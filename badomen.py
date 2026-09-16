#!/usr/bin/env python3
"""BadOmen: authorized, evidence-based web page inventory classifier.

Katana is used for broad URL discovery when available. Every discovered URL is
then independently fetched and verified by the HTTP evidence engine in
an internal HTTP evidence engine. Only observed HTML pages are included in the final inventory.

The four public labels describe observable delivery behavior, not private
server implementation details. A black-box scanner cannot prove with absolute
certainty whether an origin used a file, template, database, cache, or worker.
"""

from __future__ import annotations

import argparse
import http.cookiejar
import json
import math
import os
import re
import shutil
import subprocess
import sys
import time
from collections import Counter, deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, replace
from datetime import datetime
from pathlib import Path
from typing import Iterable
from urllib.parse import parse_qsl, urlsplit

from html import escape as _html_escape
from html.parser import HTMLParser
from urllib.error import HTTPError, URLError
from urllib.request import (
    HTTPRedirectHandler,
    Request,
    build_opener,
)
import ssl
import threading
from urllib.parse import urljoin, urlsplit, urlunsplit


HTML_CONTENT_TYPES = {
    "text/html",
    "application/xhtml+xml",
}


def escape(value: object) -> str:
    return _html_escape(str(value), quote=True)


@dataclass(frozen=True)
class ScannerConfig:
    seed_url: str
    output: Path
    max_depth: int = 5
    max_pages: int = 2000
    concurrency: int = 2
    timeout: float = 10.0
    request_delay: float = 0.1
    max_response_bytes: int = 2_000_000
    max_script_bytes: int = 250_000
    max_scripts: int = 25
    excluded_paths: tuple[str, ...] = ()
    discover_sitemaps: bool = True
    allow_invalid_tls: bool = True
    user_agent: str = "badomen/1.0.0 (authorized page inventory classifier)"


@dataclass
class ScanStats:
    started_at: str | None = None
    finished_at: str | None = None
    scripts_checked: int = 0
    sitemap_pages_discovered: int = 0
    skipped_out_of_scope: int = 0
    skipped_excluded: int = 0
    skipped_risky: int = 0
    skipped_depth: int = 0
    skipped_query_cap: int = 0


@dataclass
class PageResult:
    url: str
    final_url: str
    depth: int
    discovered_by: str
    referrer: str | None
    status: int
    content_type: str
    classification: str
    confidence: str
    reason_codes: list[str]
    limitations: list[str]
    links: list[str]
    redirect_count: int
    content_fingerprint: str


class _NoRedirectHandler(HTTPRedirectHandler):
    def http_error_301(self, req, fp, code, msg, headers):
        return fp
    def http_error_302(self, req, fp, code, msg, headers):
        return fp
    def http_error_303(self, req, fp, code, msg, headers):
        return fp
    def http_error_307(self, req, fp, code, msg, headers):
        return fp
    def http_error_308(self, req, fp, code, msg, headers):
        return fp


class _PageParser(HTMLParser):
    def __init__(self, base_url: str) -> None:
        super().__init__(convert_charrefs=True)
        self.base_url = base_url
        self.links: list[str] = []
        self.scripts: list[str] = []
        self.inline_scripts: list[str] = []
        self.forms = 0
        self.post_forms = 0
        self.submit_controls = 0
        self.password_inputs = 0
        self.text_chunks: list[str] = []
        self.hydration = False
        self._in_script = False
        self._script_external = False
        self._script_buf: list[str] = []

    def handle_starttag(self, tag: str, attrs):
        attrs_dict = {k.lower(): v for k, v in attrs if k}
        tag_l = tag.lower()
        if tag_l in {"a", "area", "link"} and attrs_dict.get("href"):
            self._add_link(attrs_dict["href"])
        elif tag_l in {"iframe", "frame", "object"} and attrs_dict.get("src"):
            self._add_link(attrs_dict["src"])
        if tag_l == "form":
            self.forms += 1
            if (attrs_dict.get("method") or "get").lower() == "post":
                self.post_forms += 1
        if tag_l in {"input", "button"} and (attrs_dict.get("type") or "").lower() in {"submit", "button", "image"}:
            self.submit_controls += 1
        if tag_l == "input" and (attrs_dict.get("type") or "").lower() == "password":
            self.password_inputs += 1
        if any(k.startswith("data-react") for k in attrs_dict) or "data-reactroot" in attrs_dict:
            self.hydration = True
        if "data-nextjs" in attrs_dict or "data-n-head" in attrs_dict:
            self.hydration = True
        if tag_l == "script":
            src = attrs_dict.get("src")
            self._in_script = True
            self._script_external = bool(src)
            self._script_buf = []
            if src:
                self._add_script(src)

    def handle_startendtag(self, tag: str, attrs):
        self.handle_starttag(tag, attrs)
        if tag.lower() == "script":
            self.handle_endtag("script")

    def handle_endtag(self, tag: str):
        if tag.lower() == "script" and self._in_script:
            text = "".join(self._script_buf)
            if text.strip():
                self.inline_scripts.append(text)
            self._in_script = False
            self._script_external = False
            self._script_buf = []

    def handle_data(self, data: str):
        if self._in_script:
            self._script_buf.append(data)
        else:
            stripped = re.sub(r"\\s+", " ", data).strip()
            if stripped:
                self.text_chunks.append(stripped)

    def handle_comment(self, data: str):
        lower = data.lower()
        if any(token in lower for token in ("reactroot", "next_data", "__next", "nuxt")):
            self.hydration = True

    def _add_link(self, value: str) -> None:
        try:
            candidate = urljoin(self.base_url, value.strip())
            parts = urlsplit(candidate)
            if parts.scheme in {"http", "https"} and parts.netloc:
                self.links.append(candidate)
        except Exception:
            pass

    def _add_script(self, value: str) -> None:
        self._add_link(value)


class WebReconScanner:
    _server_handler = re.compile(r"(?i)\\.(?:action|asp|aspx|cgi|do|jsp|jspx|php|pl)$")

    def __init__(self, config: ScannerConfig, transport=None) -> None:
        self.config = config
        self.seed_url = config.seed_url
        self.stats = ScanStats(started_at=datetime.now().astimezone().isoformat(timespec="seconds"))
        self._transport = transport
        self._delay_lock = threading.Lock()
        self._last_request = 0.0
        self._tls_retry_done: set[str] = set()

    def _build_opener(self, verify_tls: bool = True):
        if self._transport is not None:
            return self._transport
        handlers = [_NoRedirectHandler()]
        if not verify_tls:
            ctx = ssl._create_unverified_context()
            from urllib.request import HTTPSHandler
            handlers.append(HTTPSHandler(context=ctx))
        return build_opener(*handlers)

    def _rate_limit(self) -> None:
        delay = self.config.request_delay
        if delay <= 0:
            return
        with self._delay_lock:
            now = time.monotonic()
            wait = delay - (now - self._last_request)
            if wait > 0:
                time.sleep(wait)
            self._last_request = time.monotonic()

    def _fetch(self, url: str, cookie_jar: http.cookiejar.CookieJar | None = None):
        class Response:
            pass

        self._rate_limit()
        req = Request(
            url,
            headers={
                "User-Agent": self.config.user_agent,
                "Accept": "text/html,application/xhtml+xml,application/json;q=0.8,*/*;q=0.2",
                "Accept-Encoding": "identity",
                "Connection": "close",
            },
            method="GET",
        )
        result = Response()
        result.error = None
        result.out_of_scope_redirect = False
        result.status = 0
        result.content_type = ""
        result.final_url = url
        result.body = b""
        result.headers = {}
        result.redirect_count = 0
        opener = self._build_opener(True)
        if cookie_jar is not None and self._transport is None:
            from urllib.request import HTTPCookieProcessor
            opener = self._build_opener(True)
            opener.add_handler(HTTPCookieProcessor(cookie_jar))
        try:
            with opener.open(req, timeout=self.config.timeout) as resp:
                result.status = getattr(resp, "status", resp.getcode())
                result.final_url = resp.geturl()
                result.content_type = (resp.headers.get_content_type() or "").lower()
                result.headers = dict(resp.headers.items())
                result.body = resp.read(self.config.max_response_bytes + 1)
                result.redirect_count = 0 if result.final_url == url else 1
                return result
        except HTTPError as exc:
            result.status = exc.code
            result.final_url = exc.geturl() or url
            result.content_type = (exc.headers.get_content_type() if exc.headers else "") or ""
            result.content_type = result.content_type.lower()
            result.headers = dict(exc.headers.items()) if exc.headers else {}
            try:
                result.body = exc.read(self.config.max_response_bytes + 1)
            except Exception:
                result.body = b""
            if result.final_url != url and not self.in_scope(result.final_url):
                result.out_of_scope_redirect = True
            return result
        except (ssl.SSLCertVerificationError, URLError) as exc:
            if self.config.allow_invalid_tls and url.startswith("https://") and url not in self._tls_retry_done:
                self._tls_retry_done.add(url)
                self._rate_limit()
                opener = self._build_opener(False)
                try:
                    with opener.open(req, timeout=self.config.timeout) as resp:
                        result.status = getattr(resp, "status", resp.getcode())
                        result.final_url = resp.geturl()
                        result.content_type = (resp.headers.get_content_type() or "").lower()
                        result.headers = dict(resp.headers.items())
                        result.body = resp.read(self.config.max_response_bytes + 1)
                        result.redirect_count = 0 if result.final_url == url else 1
                        return result
                except Exception as retry_exc:
                    result.error = retry_exc
                    return result
            result.error = exc
            return result
        except Exception as exc:
            result.error = exc
            return result

    def normalize_url(self, candidate: str, referrer: str | None = None) -> str | None:
        try:
            base = referrer or self.seed_url
            value = urljoin(base, candidate.strip())
            parts = urlsplit(value)
            if parts.scheme not in {"http", "https"} or not parts.netloc:
                return None
            path = parts.path or "/"
            # Fragments do not affect HTTP resources.
            return urlunsplit((parts.scheme.lower(), parts.netloc.lower(), path, parts.query, ""))
        except Exception:
            return None

    def in_scope(self, url: str) -> bool:
        try:
            seed = urlsplit(self.seed_url)
            candidate = urlsplit(url)
            if candidate.scheme not in {"http", "https"} or seed.netloc.lower() != candidate.netloc.lower():
                return False
            return True
        except Exception:
            return False

    def excluded(self, url: str) -> bool:
        path = urlsplit(url).path or "/"
        from fnmatch import fnmatch
        return any(fnmatch(path, pattern) for pattern in self.config.excluded_paths)

    def risky(self, url: str) -> bool:
        return bool(re.search(KATANA_RISKY_REGEX, url))

    def discover_sitemap_pages(self) -> list[str]:
        if not self.config.discover_sitemaps:
            return []
        discovered: list[str] = []
        base = urlsplit(self.seed_url)
        candidates = [
            f"{base.scheme}://{base.netloc}/sitemap.xml",
            f"{base.scheme}://{base.netloc}/robots.txt",
        ]
        seen_sitemaps: set[str] = set()
        for source in candidates:
            response = self._fetch(source, http.cookiejar.CookieJar())
            if response.error or response.status >= 400:
                continue
            text = response.body[:self.config.max_response_bytes].decode("utf-8", "replace")
            urls: list[str] = []
            if source.endswith("robots.txt"):
                for line in text.splitlines():
                    if line.lower().startswith("sitemap:"):
                        target = line.split(":", 1)[1].strip()
                        if target:
                            urls.append(target)
            else:
                urls.extend(re.findall(r"<loc>\\s*(https?://[^<\\s]+)", text, flags=re.I))
            for candidate in urls:
                normalized = self.normalize_url(candidate)
                if not normalized or not self.in_scope(normalized) or normalized in seen_sitemaps:
                    continue
                seen_sitemaps.add(normalized)
                if "sitemap" in normalized.lower() and normalized not in discovered:
                    # A sitemap URL may itself be a sitemap. Fetch it as XML and extract loc entries.
                    nested = self._fetch(normalized, http.cookiejar.CookieJar())
                    if not nested.error and nested.status < 400:
                        body = nested.body[:self.config.max_response_bytes].decode("utf-8", "replace")
                        extracted = re.findall(r"<loc>\\s*(https?://[^<\\s]+)", body, flags=re.I)
                        for item in extracted:
                            page = self.normalize_url(item)
                            if page and self.in_scope(page) and not self.risky(page):
                                discovered.append(page)
                        continue
                if not self.risky(normalized):
                    discovered.append(normalized)
        self.stats.sitemap_pages_discovered += len(discovered)
        return list(dict.fromkeys(discovered))

    def _fingerprint(self, body: bytes) -> str:
        import hashlib
        return hashlib.sha256(body).hexdigest()[:16] if body else ""

    def analyze_page(self, url: str, depth: int, source: str, referrer: str | None) -> PageResult:
        response = self._fetch(url, http.cookiejar.CookieJar())
        if response.error:
            return PageResult(url, response.final_url, depth, source, referrer, 0, "", "inconclusive", "low", ["transport_error"], [type(response.error).__name__], [], response.redirect_count, "")
        body = response.body
        limitations: list[str] = []
        if len(body) > self.config.max_response_bytes:
            limitations.append("body_truncated")
            body = body[:self.config.max_response_bytes]
        content_type = response.content_type
        decoded = body.decode("utf-8", "replace")
        sniffed_html = bool(re.match(r"\\s*(?:<!doctype\\s+html|<html(?:\\s|>)|<head(?:\\s|>)|<body(?:\\s|>))", decoded, flags=re.I))
        if content_type not in HTML_CONTENT_TYPES and not sniffed_html:
            return PageResult(url, response.final_url, depth, source, referrer, response.status, content_type, "non-page", "high", ["non_html_content"], limitations, [], response.redirect_count, self._fingerprint(body))

        parser = _PageParser(response.final_url)
        try:
            parser.feed(decoded)
            parser.close()
        except Exception as exc:
            limitations.append(f"html_parse_{type(exc).__name__.lower()}")

        lower = decoded.lower()
        reasons: list[str] = []
        text_len = len(" ".join(parser.text_chunks))
        if text_len >= 80 or len(body) >= 1500:
            reasons.append("substantive_html")
        if parser.hydration or any(token in lower for token in ("__next_data__", "__next_f.push", "window.__nuxt__", "data-reactroot")):
            reasons.append("hydration_marker")
        if re.search(r"/(?:login|signin|sign-in|authenticate|auth)(?:[/?.#]|$)", url, re.I):
            reasons.append("authentication_route")
        if parser.password_inputs:
            reasons.append("password_input_present")
        if parser.forms:
            reasons.append("form_present")
        if parser.post_forms:
            reasons.append("post_form_present")
        if parser.submit_controls:
            reasons.append("submit_control_present")

        script_candidates = parser.scripts[: self.config.max_scripts]
        if len(parser.scripts) > self.config.max_scripts:
            limitations.append("script_limit_reached")
        script_texts = list(parser.inline_scripts)
        scripts_checked = len(script_texts)
        self.stats.scripts_checked += scripts_checked
        for script_url in script_candidates:
            script = self._fetch(script_url, http.cookiejar.CookieJar())
            if script.error:
                limitations.append("script_fetch_failed")
                continue
            payload = script.body
            if len(payload) > self.config.max_script_bytes:
                limitations.append("script_truncated")
                payload = payload[: self.config.max_script_bytes]
            script_texts.append(payload.decode("utf-8", "replace"))
            scripts_checked += 1
            self.stats.scripts_checked += 1
        joined_scripts = "\n".join(script_texts).lower()
        if re.search(r"\bfetch\s*\(", joined_scripts):
            reasons.append("fetch_call")
        if re.search(r"\bxmlhttprequest\b|\.xhr\b", joined_scripts):
            reasons.append("xhr")
        if re.search(r"graphql|/graphql(?:[/?#]|$)", joined_scripts + "\n" + lower):
            reasons.append("graphql_reference")
        if re.search(r"eventsource\b|text/event-stream", joined_scripts + "\n" + lower):
            reasons.append("event_stream")
        if re.search(r"websocket\b|new\s+websocket", joined_scripts):
            reasons.append("websocket")

        if response.redirect_count and not self.in_scope(response.final_url):
            limitations.append("out_of_scope_redirect")
        if response.redirect_count:
            reasons.append("redirect_observed")

        dynamic_signals = bool(set(reasons) & {
            "authentication_route", "password_input_present", "post_form_present", "submit_control_present",
            "fetch_call", "xhr", "graphql_reference", "event_stream", "websocket",
        })
        substantive = "substantive_html" in reasons
        hydration = "hydration_marker" in reasons
        server_handler = bool(self._server_handler.search(urlsplit(response.final_url).path))

        if "body_truncated" in limitations or "script_truncated" in limitations or "script_limit_reached" in limitations:
            classification, confidence = "inconclusive", "low"
        elif substantive and hydration:
            classification, confidence = "hybrid", "high"
        elif server_handler or dynamic_signals:
            classification, confidence = "likely-server-dynamic", "medium"
        elif substantive:
            classification, confidence = "likely-static", "high"
        else:
            classification, confidence = "inconclusive", "low"

        return PageResult(
            url=url,
            final_url=response.final_url,
            depth=depth,
            discovered_by=source,
            referrer=referrer,
            status=response.status,
            content_type=content_type,
            classification=classification,
            confidence=confidence,
            reason_codes=sorted(set(reasons)),
            limitations=sorted(set(limitations)),
            links=list(dict.fromkeys(parser.links)),
            redirect_count=response.redirect_count,
            content_fingerprint=self._fingerprint(body),
        )



VERSION = "1.0.0"
PUBLIC_LABELS = {"static", "dynamic", "hybrid", "not_sure"}
LEGACY_LABEL_MAP = {
    "likely-static": ("static", "server-delivered-stable-html"),
    "static-with-enhancements": ("static", "stable-html-with-enhancements"),
    "likely-server-dynamic": ("dynamic", "server-dynamic"),
    "likely-client-dynamic": ("dynamic", "client-dynamic"),
    "hybrid": ("hybrid", "server-rendered-and-client-hydrated"),
    "inconclusive": ("not_sure", "insufficient-or-conflicting-evidence"),
}

# Katana can still fetch filtered URLs while parsing. These exclusions reduce
# the chance of visiting common state-changing routes during its GET-only crawl.
KATANA_RISKY_REGEX = (
    r"(?i)/(?:account/(?:delete|logout)|admin/delete|cart/checkout|checkout|"
    r"delete|destroy|logout|remove|signout|upload)(?:[/?.#]|$)"
)
ASSET_EXTENSIONS = (
    "7z,avi,avif,bmp,bz2,css,csv,doc,docx,eot,epub,exe,flac,gif,gz,ico,jar,"
    "jpeg,jpg,js,json,map,m4a,m4v,mkv,mov,mp3,mp4,mpeg,mpg,ogg,otf,pdf,png,"
    "ppt,pptx,rar,rss,svg,tar,tgz,tif,tiff,ttf,txt,wav,webm,webp,woff,woff2,"
    "xls,xlsx,xml,zip"
)


@dataclass(frozen=True)
class BadOmenConfig(ScannerConfig):
    crawler: str = "katana"
    max_depth: int = 5
    max_pages: int = 2000
    query_variant_cap: int = 500
    katana_path: str | None = None
    crawl_timeout: float = 300.0
    katana_js_crawl: bool = True
    katana_headless: bool = False


@dataclass(frozen=True)
class DiscoveryOutcome:
    requested: str
    used: str
    urls: tuple[str, ...] = ()
    warning: str | None = None
    command: tuple[str, ...] = ()
    duration_seconds: float = 0.0
    time_limit_reached: bool = False


@dataclass(frozen=True)
class InventoryPage:
    url: str
    final_url: str
    status: int
    classification: str
    confidence: str
    delivery_mode: str
    test_surface: str
    evidence: tuple[str, ...]
    limitations: tuple[str, ...]
    discovered_by: str
    depth: int
    redirect_count: int
    content_fingerprint: str
    aliases: tuple[str, ...] = ()

    @classmethod
    def from_result(cls, result: PageResult) -> "InventoryPage | None":
        # A usable page must have produced HTML. Transport errors, assets, API
        # responses, and ordinary 4xx/5xx responses never enter the inventory.
        if result.classification == "non-page":
            return None
        reasons = set(result.reason_codes)
        if result.content_type not in HTML_CONTENT_TYPES and "html_body_sniffed" not in reasons:
            return None
        if result.status == 0:
            return None
        if result.status >= 400 and result.status not in {401, 403}:
            return None

        coverage_failures = {
            "body_truncated",
            "comparison_body_truncated",
            "comparison_fetch_failed",
            "script_fetch_failed",
            "script_limit_reached",
            "script_truncated",
        }
        strong_interaction_signals = {
            "authentication_route",
            "password_input_present",
        }
        server_handler = bool(
            re.search(
                r"(?i)\.(?:action|asp|aspx|cgi|do|jsp|jspx|php|pl)$",
                urlsplit(result.final_url).path,
            )
        )
        external_script_blocks_core_observation = (
            "sparse_html" in reasons
            and bool(reasons & {"external_script_uninspected", "invalid_script_url"})
        )
        if reasons & coverage_failures or external_script_blocks_core_observation:
            classification, delivery_mode = "not_sure", "incomplete-observation-coverage"
        elif "substantive_html" in reasons and "hydration_marker" in reasons:
            # Hydration plus delivered content is hybrid even if repeat probes
            # also varied; the older decision order masked this combination.
            classification, delivery_mode = "hybrid", "server-rendered-and-client-hydrated"
        elif server_handler:
            classification, delivery_mode = "dynamic", "server-handler-route"
        elif reasons & strong_interaction_signals:
            classification, delivery_mode = "dynamic", "interactive-server-surface"
        elif (mapped := LEGACY_LABEL_MAP.get(result.classification)) is None:
            classification, delivery_mode = "not_sure", "unrecognized-evidence-state"
        else:
            classification, delivery_mode = mapped
        confidence = result.confidence
        if classification == "static" and confidence == "high":
            # Stable black-box delivery cannot distinguish a file from a
            # deterministic template/cache, so never claim high certainty.
            confidence = "medium"
        if delivery_mode in {"server-handler-route", "interactive-server-surface"}:
            confidence = "medium"
        if classification == "not_sure":
            confidence = "low"

        if "authentication_route" in reasons or "password_input_present" in reasons:
            test_surface = "authenticated"
        elif reasons & {"post_form_present", "submit_control_present", "form_present"}:
            test_surface = "form_input"
        elif classification == "hybrid":
            test_surface = "mixed"
        elif classification == "dynamic" and reasons & {"fetch_call", "xhr", "graphql_reference", "event_stream", "websocket"}:
            test_surface = "api_backed"
        elif classification == "dynamic":
            test_surface = "client_application"
        else:
            test_surface = "content_only"
        return cls(
            url=result.url,
            final_url=result.final_url,
            status=result.status,
            classification=classification,
            confidence=confidence,
            delivery_mode=delivery_mode,
            test_surface=test_surface,
            evidence=tuple(result.reason_codes),
            limitations=tuple(result.limitations),
            discovered_by=result.discovered_by,
            depth=result.depth,
            redirect_count=result.redirect_count,
            content_fingerprint=result.content_fingerprint,
        )


def deduplicate_pages(pages: Iterable[InventoryPage]) -> list[InventoryPage]:
    """Collapse content-identical pages while preserving every URL as an alias."""
    surface_priority = {
        "content_only": 0,
        "client_application": 1,
        "form_input": 2,
        "api_backed": 3,
        "authenticated": 4,
        "mixed": 5,
    }
    confidence_priority = {"low": 0, "medium": 1, "high": 2}
    ordered = sorted(
        pages,
        key=lambda page: (
            page.url != page.final_url,
            bool(urlsplit(page.url).query),
            len(page.url),
            page.url,
        ),
    )
    grouped: dict[tuple[object, ...], InventoryPage] = {}
    for page in ordered:
        key = (
            ("content", page.status, page.content_fingerprint)
            if page.content_fingerprint
            else ("final_url", page.status, page.final_url)
        )
        current = grouped.get(key)
        if current is None:
            grouped[key] = page
            continue

        aliases = sorted(
            ({current.url, page.url} | set(current.aliases) | set(page.aliases))
            - {current.url}
        )
        classifications = {current.classification, page.classification}
        conflict = len(classifications) > 1
        limitations = set(current.limitations) | set(page.limitations) | {"duplicate_content_collapsed"}
        evidence = set(current.evidence) | set(page.evidence)
        if conflict:
            limitations.add("duplicate_alias_classification_conflict")
            classification = "not_sure"
            confidence = "low"
            delivery_mode = "conflicting-duplicate-alias-evidence"
        else:
            classification = current.classification
            confidence = min(
                (current.confidence, page.confidence),
                key=lambda value: confidence_priority.get(value, -1),
            )
            delivery_mode = current.delivery_mode
        test_surface = max(
            (current.test_surface, page.test_surface),
            key=lambda value: surface_priority.get(value, -1),
        )
        grouped[key] = replace(
            current,
            classification=classification,
            confidence=confidence,
            delivery_mode=delivery_mode,
            test_surface=test_surface,
            evidence=tuple(sorted(evidence)),
            limitations=tuple(sorted(limitations)),
            depth=min(current.depth, page.depth),
            aliases=tuple(aliases),
        )
    return sorted(grouped.values(), key=lambda page: page.url)


def resolve_katana(config: BadOmenConfig) -> str | None:
    candidate = config.katana_path or "katana"
    if os.path.sep in candidate:
        path = Path(candidate).expanduser()
        return str(path.resolve()) if path.is_file() and os.access(path, os.X_OK) else None
    return shutil.which(candidate)


def katana_command(config: BadOmenConfig, seed_url: str, executable: str) -> list[str]:
    origin = urlsplit(seed_url)
    origin_text = f"{origin.scheme}://{origin.netloc}"
    scope_regex = rf"^{re.escape(origin_text)}(?:/|$)"
    rate_limit = max(1, min(150, math.floor(1 / config.request_delay))) if config.request_delay else 150
    command = [
        executable,
        "-u",
        seed_url,
        "-d",
        str(config.max_depth),
        "-c",
        str(max(1, config.concurrency)),
        "-p",
        "1",
        "-rl",
        str(rate_limit),
        "-timeout",
        str(max(1, math.ceil(config.timeout))),
        "-mrs",
        str(config.max_response_bytes),
        "-retry",
        "0",
        "-ct",
        f"{max(1, math.ceil(config.crawl_timeout))}s",
        "-cs",
        scope_regex,
        "-cos",
        KATANA_RISKY_REGEX,
        "-ef",
        ASSET_EXTENSIONS,
        "-iqp",
        "-dr",
        "-duc",
        "-duf",
        "-silent",
        "-nc",
    ]
    if config.katana_js_crawl:
        command.append("-jc")
    if config.katana_headless:
        command.append("-hl")
    return command


def parse_katana_urls(output: str) -> list[str]:
    ansi = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
    url_pattern = re.compile(r"https?://[^\s\]\[<>\"']+")
    found: list[str] = []
    seen: set[str] = set()
    for line in output.splitlines():
        clean = ansi.sub("", line)
        match = url_pattern.search(clean)
        if not match:
            continue
        value = match.group(0).rstrip("),.;")
        if value not in seen:
            seen.add(value)
            found.append(value)
    return found


def discover_with_katana(config: BadOmenConfig, seed_url: str) -> DiscoveryOutcome:
    if config.crawler == "builtin":
        return DiscoveryOutcome(requested="builtin", used="builtin")

    executable = resolve_katana(config)
    if not executable:
        warning = "Katana was not found; using the built-in crawler."
        return DiscoveryOutcome(requested=config.crawler, used="builtin", warning=warning)

    command = katana_command(config, seed_url, executable)
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=config.crawl_timeout + 15,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return DiscoveryOutcome(
            requested=config.crawler,
            used="builtin",
            warning=f"Katana exceeded the {config.crawl_timeout:g}s limit; using built-in discovery.",
            command=tuple(command),
        )
    except OSError as exc:
        return DiscoveryOutcome(
            requested=config.crawler,
            used="builtin",
            warning=f"Katana could not start ({type(exc).__name__}); using built-in discovery.",
            command=tuple(command),
        )

    urls = parse_katana_urls(completed.stdout)
    duration = time.monotonic() - started
    if completed.returncode != 0 or not urls:
        detail = f"exit {completed.returncode}" if completed.returncode else "no URLs returned"
        return DiscoveryOutcome(
            requested=config.crawler,
            used="builtin",
            warning=f"Katana produced no usable discovery result ({detail}); using built-in discovery.",
            command=tuple(command),
        )
    return DiscoveryOutcome(
        requested=config.crawler,
        used="katana+builtin-verification",
        urls=tuple(urls),
        warning=(
            "Katana active discovery is enabled; Katana parsers may issue methods other than GET "
            "for constructs such as hx-post. Confirm engagement authorization and scope."
        ),
        command=tuple(command),
        duration_seconds=round(duration, 3),
        time_limit_reached=duration >= config.crawl_timeout * 0.95,
    )


class BadOmenScanner(WebReconScanner):
    """Combine Katana discovery with WebRecon's bounded evidence engine."""

    config: BadOmenConfig

    def __init__(self, config: BadOmenConfig, transport=None) -> None:  # noqa: ANN001
        super().__init__(config, transport)
        self.discovery = DiscoveryOutcome(requested=config.crawler, used="not-started")
        self.examined_results: list[PageResult] = []
        self.filtered_non_pages = 0
        self.duplicates_removed = 0
        self.discovery_seed = self.seed_url

    def resolve_discovery_seed(self) -> str:
        """Resolve a safe canonical redirect before invoking redirect-disabled Katana."""
        if self.config.crawler != "katana":
            return self.seed_url
        response = self._fetch(self.seed_url, http.cookiejar.CookieJar())
        if (
            not response.error
            and not response.out_of_scope_redirect
            and response.status
            and self.in_scope(response.final_url)
        ):
            return response.final_url
        return self.seed_url

    def scan(self) -> list[InventoryPage]:
        self.discovery_seed = self.resolve_discovery_seed()
        self.discovery = discover_with_katana(self.config, self.discovery_seed)
        queue: deque[tuple[str, int, str, str | None]] = deque()
        enqueued: set[str] = set()
        visited: set[str] = set()
        query_variants: dict[tuple[str, str], set[str]] = {}

        def enqueue(candidate: str, depth: int, source: str, referrer: str | None = None) -> None:
            url = self.normalize_url(candidate, referrer)
            if not url:
                return
            if not self.in_scope(url):
                self.stats.skipped_out_of_scope += 1
                return
            if self.excluded(url):
                self.stats.skipped_excluded += 1
                return
            if self.risky(url):
                self.stats.skipped_risky += 1
                return
            if url in visited or url in enqueued:
                return
            if depth > self.config.max_depth:
                self.stats.skipped_depth += 1
                return
            if len(visited) + len(enqueued) >= self.config.max_pages:
                return
            parsed = urlsplit(url)
            variant_key = (parsed.netloc, parsed.path)
            variants = query_variants.setdefault(variant_key, set())
            if parsed.query not in variants and len(variants) >= self.config.query_variant_cap:
                self.stats.skipped_query_cap += 1
                return
            variants.add(parsed.query)
            queue.append((url, depth, source, referrer))
            enqueued.add(url)

        enqueue(self.seed_url, 0, "seed")
        for page in self.discover_sitemap_pages():
            enqueue(page, 0, "sitemap")
        for candidate in self.discovery.urls:
            enqueue(candidate, 0, "katana")

        with ThreadPoolExecutor(max_workers=max(1, self.config.concurrency)) as executor:
            while queue and len(self.examined_results) < self.config.max_pages:
                remaining = self.config.max_pages - len(self.examined_results)
                batch_size = min(max(1, self.config.concurrency), remaining, len(queue))
                batch = [queue.popleft() for _ in range(batch_size)]
                for url, _depth, _source, _referrer in batch:
                    enqueued.discard(url)
                    visited.add(url)
                futures = [
                    executor.submit(self.analyze_page, url, depth, source, referrer)
                    for url, depth, source, referrer in batch
                ]
                for item, future in zip(batch, futures, strict=True):
                    try:
                        result = future.result()
                    except Exception as exc:  # isolate malformed/failed candidates
                        url, depth, source, referrer = item
                        result = PageResult(
                            url=url,
                            final_url=url,
                            depth=depth,
                            discovered_by=source,
                            referrer=referrer,
                            status=0,
                            content_type="",
                            classification="inconclusive",
                            confidence="low",
                            reason_codes=[f"analysis_exception_{type(exc).__name__.lower()}"],
                            limitations=["page_analysis_failed"],
                            links=[],
                            redirect_count=0,
                            content_fingerprint="",
                        )
                    self.examined_results.append(result)
                    if result.classification != "non-page":
                        for link in result.links:
                            enqueue(link, result.depth + 1, "html-link", result.final_url)

        self.stats.finished_at = self.stats.finished_at or datetime.now().astimezone().isoformat(timespec="seconds")
        inventory_candidates = [
            page
            for result in self.examined_results
            if (page := InventoryPage.from_result(result)) is not None
        ]
        self.filtered_non_pages = len(self.examined_results) - len(inventory_candidates)
        inventory = deduplicate_pages(inventory_candidates)
        self.duplicates_removed = len(inventory_candidates) - len(inventory)
        return inventory


def report_payload(scanner: BadOmenScanner, pages: list[InventoryPage]) -> dict[str, object]:
    counts = Counter(page.classification for page in pages)
    page_urls = {url for page in pages for url in (page.url, *page.aliases)}
    route_keys: set[tuple[str, str, str]] = set()
    query_shapes: set[tuple[str, str, str, tuple[str, ...]]] = set()
    for page in pages:
        for page_url in (page.url, *page.aliases):
            parsed = urlsplit(page_url)
            route_keys.add((parsed.scheme, parsed.netloc, parsed.path))
            names = tuple(sorted(key for key, _value in parse_qsl(parsed.query, keep_blank_values=True)))
            query_shapes.add((parsed.scheme, parsed.netloc, parsed.path, names))

    coverage_limitations: list[str] = []
    if len(scanner.examined_results) >= scanner.config.max_pages:
        coverage_limitations.append("candidate_limit_reached")
    if scanner.stats.skipped_query_cap:
        coverage_limitations.append("query_variant_limit_reached")
    if scanner.stats.skipped_depth:
        coverage_limitations.append("crawl_depth_boundary_reached")
    if scanner.discovery.requested == "katana" and scanner.discovery.used == "builtin":
        coverage_limitations.append("katana_unavailable_or_failed")
    if scanner.discovery.time_limit_reached:
        coverage_limitations.append("katana_crawl_time_limit_reached")
    if any("script_limit_reached" in result.reason_codes for result in scanner.examined_results):
        coverage_limitations.append("script_inspection_limit_reached")

    diagnostics = []
    for result in scanner.examined_results:
        if result.url in page_urls:
            continue
        unverified = result.classification != "non-page"
        diagnostics.append(
            {
                "url": result.url,
                "status": result.status,
                "content_type": result.content_type,
                "outcome": "unverified_candidate" if unverified else "confirmed_non_page",
                "evidence": result.reason_codes,
                "limitations": result.limitations,
                "discovered_by": result.discovered_by,
            }
        )
    return {
        "tool": "badomen",
        "version": VERSION,
        "target": scanner.seed_url,
        "started_at": scanner.stats.started_at,
        "finished_at": scanner.stats.finished_at,
        "certainty_statement": (
            "Labels describe repeatable black-box observations. Absolute knowledge of server-side "
            "implementation is impossible without source code or deployment access."
        ),
        "crawler": {
            "requested": scanner.discovery.requested,
            "used": scanner.discovery.used,
            "warning": scanner.discovery.warning,
            "katana_urls_returned": len(scanner.discovery.urls),
            "discovery_seed": scanner.discovery_seed,
            "duration_seconds": scanner.discovery.duration_seconds,
            "time_limit_reached": scanner.discovery.time_limit_reached,
        },
        "coverage": {
            "status": "bounded" if coverage_limitations else "complete_within_observed_scope",
            "limitations": coverage_limitations,
            "max_depth": scanner.config.max_depth,
            "max_candidates": scanner.config.max_pages,
            "query_variants_per_path": scanner.config.query_variant_cap,
        },
        "summary": {
            "pages": len(pages),
            "page_candidates_before_deduplication": len(pages) + scanner.duplicates_removed,
            "duplicates_removed": scanner.duplicates_removed,
            "unique_paths": len(route_keys),
            "unique_query_shapes": len(query_shapes),
            "urls_examined": len(scanner.examined_results),
            "non_pages_filtered": scanner.filtered_non_pages,
            "unverified_candidates": sum(
                diagnostic["outcome"] == "unverified_candidate" for diagnostic in diagnostics
            ),
            "classifications": {label: counts.get(label, 0) for label in sorted(PUBLIC_LABELS)},
            "discovery_sources": dict(sorted(Counter(page.discovered_by for page in pages).items())),
            "scripts_checked": scanner.stats.scripts_checked,
            "sitemap_pages_discovered": scanner.stats.sitemap_pages_discovered,
            "skipped_out_of_scope": scanner.stats.skipped_out_of_scope,
            "skipped_excluded": scanner.stats.skipped_excluded,
            "skipped_risky": scanner.stats.skipped_risky,
            "skipped_depth": scanner.stats.skipped_depth,
            "skipped_query_cap": scanner.stats.skipped_query_cap,
        },
        "pages": [asdict(page) for page in pages],
        "manual_validation": [asdict(page) for page in pages if page.classification == "not_sure"],
        "candidate_diagnostics": diagnostics,
    }


def render_html(payload: dict[str, object]) -> str:
    summary = payload["summary"]
    assert isinstance(summary, dict)
    pages = payload["pages"]
    assert isinstance(pages, list)
    counts = summary["classifications"]
    assert isinstance(counts, dict)
    cards = "".join(
        f'<div class="card {escape(label)}"><b>{escape(label)}</b><span>{count}</span></div>'
        for label, count in counts.items()
    )
    rows = "\n".join(
        "<tr>"
        f"<td><code>{escape(page['url'])}</code>"
        + (
            f"<details><summary>{len(page['aliases'])} duplicate URL alias(es)</summary>"
            + "<br>".join(f"<code>{escape(alias)}</code>" for alias in page["aliases"])
            + "</details>"
            if page["aliases"]
            else ""
        )
        + "</td>"
        f"<td>{page['status']}</td>"
        f"<td><span class=\"pill {escape(page['classification'])}\">{escape(page['classification'])}</span></td>"
        f"<td>{escape(page['confidence'])}</td>"
        f"<td>{escape(page['delivery_mode'])}</td><td>{escape(page['test_surface'])}</td>"
        f"<td>{escape(', '.join(page['evidence']))}</td>"
        f"<td>{escape(', '.join(page['limitations']))}</td>"
        "</tr>"
        for page in pages
    ) or '<tr><td colspan="8">No verified HTML pages were found.</td></tr>'
    crawler = payload["crawler"]
    assert isinstance(crawler, dict)
    coverage = payload["coverage"]
    assert isinstance(coverage, dict)
    warning = f"<p class=\"warning\">{escape(crawler['warning'])}</p>" if crawler["warning"] else ""
    coverage_text = ", ".join(coverage["limitations"]) or "no configured coverage limit was reached"
    manual_pages = payload["manual_validation"]
    assert isinstance(manual_pages, list)
    manual_rows = "".join(
        f"<li><code>{escape(page['url'])}</code> — {escape(', '.join(page['evidence']))}; "
        f"limitations: {escape(', '.join(page['limitations']))}</li>"
        for page in manual_pages
    ) or "<li>None</li>"
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>BadOmen page inventory</title><style>
:root{{font-family:system-ui,sans-serif;color-scheme:light dark}}body{{margin:2rem;max-width:1500px}}
.cards{{display:flex;gap:.7rem;flex-wrap:wrap}}.card{{border:1px solid #8886;border-radius:.5rem;padding:.7rem;min-width:9rem}}
.card span{{display:block;font-size:1.6rem}}table{{border-collapse:collapse;width:100%;font-size:.86rem}}
th,td{{border-bottom:1px solid #8885;padding:.5rem;text-align:left;vertical-align:top}}th{{position:sticky;top:0;background:Canvas}}
code{{word-break:break-all}}.pill{{border:1px solid #8888;border-radius:99px;padding:.1rem .45rem}}
.static{{background:#23863633}}.dynamic{{background:#d2992233}}.hybrid{{background:#8957e533}}.not_sure{{background:#da363333}}
.muted{{color:#777}}.warning{{border-left:4px solid #d29922;padding:.5rem}}</style></head><body>
<h1>BadOmen page inventory</h1><p>Target: <code>{escape(payload['target'])}</code></p>
<p class="muted">{escape(payload['certainty_statement'])}</p>{warning}
<p>Crawler: {escape(crawler['used'])}. Examined {summary['urls_examined']} URLs; retained {summary['pages']} unique HTML pages; collapsed {summary['duplicates_removed']} duplicates; filtered {summary['non_pages_filtered']} non-pages.</p>
<p>Coverage: <b>{escape(coverage['status'])}</b> — {escape(coverage_text)}. Exact non-page and unverified candidate diagnostics are retained in JSON.</p>
<div class="cards">{cards}</div><h2>Pages</h2><input id="q" type="search" placeholder="Filter pages" style="width:100%;padding:.6rem;box-sizing:border-box">
<table><thead><tr><th>URL</th><th>Status</th><th>Class</th><th>Confidence</th><th>Mode</th><th>Test surface</th><th>Evidence</th><th>Limitations</th></tr></thead>
<tbody id="rows">{rows}</tbody></table><h2>Manual validation queue ({len(manual_pages)})</h2>
<ul>{manual_rows}</ul><script>
const q=document.getElementById('q');q.addEventListener('input',()=>{{for(const r of document.querySelectorAll('#rows tr'))r.hidden=!r.textContent.toLowerCase().includes(q.value.toLowerCase())}});
</script></body></html>"""


def default_output_dir(seed_url: str, timestamp: str | None = None) -> Path:
    host = (urlsplit(seed_url).hostname or "website").lower()
    safe_host = re.sub(r"[^a-z0-9._-]+", "_", host).strip("._-") or "website"
    stamp = timestamp or datetime.now().strftime("%Y-%m-%d-%H-%M-%S")
    return Path.cwd() / "outputs" / f"badomen-{safe_host}-{stamp}"


def normalize_seed_input(value: str) -> str:
    candidate = value.strip()
    if not re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*://", candidate):
        candidate = f"http://{candidate}"
    return candidate


def write_report_file(path: Path, content: str) -> Path:
    """Create a non-overwriting report readable without root privileges."""
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    for attempt in range(1000):
        candidate = path if attempt == 0 else path.with_name(f"{path.stem}-{attempt}{path.suffix}")
        try:
            descriptor = os.open(candidate, flags, 0o644)
        except FileExistsError:
            continue
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="") as stream:
            stream.write(content)
        os.chmod(candidate, 0o644)
        return candidate
    raise RuntimeError(f"could not allocate a unique report filename for {path}")


def write_outputs(output_dir: Path, payload: dict[str, object], pages: list[InventoryPage]) -> dict[str, Path]:
    if output_dir.is_symlink():
        raise OSError(f"refusing symlink output directory: {output_dir}")
    output_dir.mkdir(parents=True, mode=0o755, exist_ok=True)
    if not output_dir.is_dir():
        raise OSError(f"output path is not a directory: {output_dir}")
    os.chmod(output_dir, 0o755)
    return {
        "html": write_report_file(output_dir / "report.html", render_html(payload)),
        "json": write_report_file(output_dir / "pages.json", json.dumps(payload, indent=2) + "\n"),
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="badomen",
        description="Crawl an authorized site and classify verified HTML pages as static, dynamic, hybrid, or not_sure.",
    )
    parser.add_argument("seed_url", help="authorized hostname or http:// / https:// site URL")
    parser.add_argument("-d", "--depth", type=int, default=5, help="crawl depth (default: 5)")
    parser.add_argument("--max-pages", type=int, default=2000, help="maximum candidate URLs to verify (default: 2000)")
    parser.add_argument(
        "--query-variants",
        type=int,
        default=500,
        help="maximum query-value variants per path (default: 500)",
    )
    parser.add_argument("-c", "--concurrency", type=int, default=2, help="verification workers (default: 2)")
    parser.add_argument("--timeout", type=float, default=10.0, help="per-request timeout in seconds")
    parser.add_argument("--crawl-timeout", type=float, default=300.0, help="Katana process time limit in seconds (default: 300)")
    parser.add_argument("--delay", type=float, default=0.1, help="minimum delay between verification requests")
    parser.add_argument(
        "--crawler",
        choices=("katana", "builtin"),
        default="katana",
        help="Katana plus built-in verification (default), or GET-only built-in discovery",
    )
    parser.add_argument("--katana", dest="katana_path", help="Katana executable path or command name")
    parser.add_argument("--headless", action="store_true", help="allow explicitly selected Katana to use click-capable browser crawling")
    parser.add_argument("--no-js-crawl", action="store_true", help="disable Katana JavaScript endpoint discovery")
    parser.add_argument("--no-sitemaps", action="store_true", help="disable BadOmen's sitemap discovery")
    parser.add_argument(
        "--strict-tls",
        action="store_true",
        help="do not retry certificate-invalid HTTPS targets (default: verify first, then record a fallback)",
    )
    parser.add_argument("--exclude-path", action="append", default=[], metavar="GLOB", help="same-origin path glob to skip; repeatable")
    parser.add_argument("-o", "--output-dir", type=Path, help="report directory (default: outputs/badomen-HOST-TIME)")
    parser.add_argument("--version", action="version", version=f"badomen {VERSION}")
    return parser


def config_from_args(args: argparse.Namespace) -> tuple[BadOmenConfig, Path]:
    if args.depth < 0:
        raise ValueError("--depth must be zero or greater")
    if args.max_pages < 1:
        raise ValueError("--max-pages must be at least 1")
    if args.concurrency < 1:
        raise ValueError("--concurrency must be at least 1")
    if args.query_variants < 1:
        raise ValueError("--query-variants must be at least 1")
    if args.timeout <= 0 or args.crawl_timeout <= 0:
        raise ValueError("timeouts must be greater than zero")
    if args.delay < 0:
        raise ValueError("--delay cannot be negative")
    if args.headless and args.crawler != "katana":
        raise ValueError("--headless requires --crawler katana")
    if args.katana_path and args.crawler != "katana":
        raise ValueError("--katana requires --crawler katana")
    seed_url = normalize_seed_input(args.seed_url)
    output_dir = args.output_dir or default_output_dir(seed_url)
    config = BadOmenConfig(
        seed_url=seed_url,
        output=output_dir / "report.html",
        max_depth=args.depth,
        max_pages=args.max_pages,
        concurrency=args.concurrency,
        query_variant_cap=args.query_variants,
        timeout=args.timeout,
        request_delay=args.delay,
        excluded_paths=tuple(args.exclude_path),
        discover_sitemaps=not args.no_sitemaps,
        crawler=args.crawler,
        katana_path=args.katana_path,
        crawl_timeout=args.crawl_timeout,
        katana_js_crawl=not args.no_js_crawl,
        katana_headless=args.headless,
        allow_invalid_tls=not args.strict_tls,
        user_agent=f"badomen/{VERSION} (authorized page inventory classifier)",
    )
    return config, output_dir


def print_summary(scanner: BadOmenScanner, pages: list[InventoryPage], outputs: dict[str, Path]) -> None:
    counts = Counter(page.classification for page in pages)
    print(f"[+] Crawler: {scanner.discovery.used}")
    if scanner.discovery.warning:
        print(f"[!] {scanner.discovery.warning}", file=sys.stderr)
    print(f"[+] Examined {len(scanner.examined_results)} URLs; retained {len(pages)} HTML pages")
    print("[+] " + ", ".join(f"{label}={counts.get(label, 0)}" for label in ("static", "dynamic", "hybrid", "not_sure")))
    for page in pages:
        alias_note = f" (+{len(page.aliases)} duplicate aliases)" if page.aliases else ""
        print(f"{page.classification:10} {page.confidence:6} {page.url}{alias_note}")
    print(f"[+] HTML: {outputs['html']}")
    print(f"[+] JSON: {outputs['json']}")


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        config, output_dir = config_from_args(args)
        scanner = BadOmenScanner(config)
    except ValueError as exc:
        parser.error(str(exc))
    print(f"[*] BadOmen is scanning authorized origin: {scanner.seed_url}")
    print("[*] Classifications are evidence-based observations, not claims about private server internals.")
    try:
        pages = scanner.scan()
        payload = report_payload(scanner, pages)
        outputs = write_outputs(output_dir, payload, pages)
    except KeyboardInterrupt:
        print("\n[!] Interrupted; no incomplete report was written.", file=sys.stderr)
        return 130
    except (OSError, RuntimeError) as exc:
        print(f"[!] Scan failed: {exc}", file=sys.stderr)
        return 1
    print_summary(scanner, pages, outputs)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
