#!/usr/bin/env python3
"""
Resume the 67-article NYMag/Wayback comparison from validated local artifacts.

The 1..67 row -> URL address book is reconstructed from stable metadata sources.
If any row URL is missing or contradictory, NYMag correction discovery rebuilds the
complete corpus before artifact processing begins.

Live HTML is reused only when it identifies the expected corrected article and its
article-body extraction is usable. Wayback HTML is reused only when it identifies
the expected article, has verified capture provenance at or before the requested
cutoff, and its article-body extraction is usable. Diffs are reused only when their
embedded metadata matches the hashes of both validated HTML inputs.

Wayback gaps are retried in repeated passes until all validated artifacts exist or
the user stops the process with Ctrl-C. ZIPs are created only from the 67 validated
artifacts of each type.

Dependencies:
    python -m pip install requests beautifulsoup4 lxml readability-lxml

Example:
    python nymag_wayback_diff_barkan_crawl_streamlined.py --out barkan_wayback_diff
"""

from __future__ import annotations

import argparse
import csv
import dataclasses
import difflib
import hashlib
import html as html_lib
import io
import json
import re
import sys
import time
import unicodedata
import zipfile
from pathlib import Path
from typing import Any, Iterable, Optional
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup, Comment, NavigableString, Tag

try:
    from readability import Document
except Exception:
    Document = None


DEFAULT_CUTOFF = "20260813235959"
AUTHOR_ARCHIVE_URL = "https://nymag.com/author/ross-barkan/"
EXPECTED_CORRECTION_COUNT = 67
DIFF_SCHEMA_VERSION = 2
CORRECTION_DATE = "August 14, 2026"
CORRECTION_REQUIRED_PHRASES = (
    "a previous version of this article did not meet",
    "editorial standards",
    "updated to include appropriate attribution",
)
USER_AGENT = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/127.0 Safari/537.36 BarkanResearchAudit/1.0"
)

# Blocks we want from article prose. We intentionally omit figcaption because
# image-credit/caption churn is a common source of useless diffs.
BLOCK_TAGS = {"p", "blockquote", "h2", "h3", "h4", "li"}

# Structural junk that should never contribute to an article-text diff.
REMOVE_SELECTORS = [
    "script", "style", "noscript", "template", "svg", "canvas", "iframe",
    "nav", "footer", "header", "aside", "form", "button", "input", "select",
    "textarea", "picture", "video", "audio", "figure", "figcaption",
    "[aria-hidden='true']",
    "[role='navigation']",
    "[role='complementary']",
    "[class*='newsletter']", "[id*='newsletter']",
    "[class*='recirc']", "[id*='recirc']",
    "[class*='related']", "[id*='related']",
    "[class*='recommend']", "[id*='recommend']",
    "[class*='most-popular']", "[id*='most-popular']",
    "[class*='mostPopular']", "[id*='mostPopular']",
    "[class*='comments']", "[id*='comments']",
    "[class*='commenting']", "[id*='commenting']",
    "[class*='share']", "[id*='share']",
    "[class*='social']", "[id*='social']",
    "[class*='ad-']", "[id^='ad-']", "[data-ad]",
    "[class*='advert']", "[id*='advert']",
    "[class*='subscription']", "[id*='subscription']",
    "[class*='subscribe']", "[id*='subscribe']",
    "#wm-ipp", "#wm-ipp-base", "#wm-ipp-print", ".wb-autocomplete-suggestions",
]

# If one of these appears after substantive prose, article extraction stops.
# This is deliberate: the Aug. 14 correction note itself is metadata about the
# edit, not part of the article prose whose wording we want to compare.
END_MARKERS = [
    re.compile(r"^August\s+14,\s+2026:\s+A previous version of this article", re.I),
    re.compile(r"^Sign Up for the .*Newsletter", re.I),
    re.compile(r"^Sign up for .* newsletter", re.I),
    re.compile(r"^Tags:\s*$", re.I),
    re.compile(r"^THE FEED\s*$", re.I),
    re.compile(r"^Most Popular\s*$", re.I),
    re.compile(r"^More From", re.I),
    re.compile(r"^Related(?: Stories| Articles)?\s*$", re.I),
]

# Small, high-confidence pieces of site chrome. Keep this conservative so we
# don't delete a real sentence merely because it contains a common phrase.
DROP_EXACT = {
    "save", "saved", "comment", "show comment", "menu", "search",
    "sign in", "sign out", "account", "give a gift", "subscribe",
    "save this article to read it later.",
    "find this story in your account’s ‘saved for later’ section.",
    "find this story in your account's 'saved for later' section.",
}
DROP_PREFIXES = (
    "this site is protected by recaptcha",
    "by submitting your email, you agree",
    "things you buy through our links may earn",
    "your product is saved!",
)

# Candidate containers, from specific to broad. We also run Readability as an
# independent candidate and choose the best-scoring result.
CANDIDATE_SELECTORS = [
    "[data-testid='article-body']",
    "[data-testid*='article-body']",
    "[data-testid*='articleBody']",
    "[class*='article-body']",
    "[class*='articleBody']",
    "[class*='article-content']",
    "[class*='articleContent']",
    "[class*='story-body']",
    "[class*='storyBody']",
    "[class*='post-content']",
    "article",
    "main",
]


def progress(message: str, *, enabled: bool = True) -> None:
    """Print immediately so network work never looks silently hung."""
    if enabled:
        print(message, flush=True)



@dataclasses.dataclass
class Link:
    text: str
    url: str


@dataclasses.dataclass
class Block:
    kind: str
    text: str
    links: list[Link]


@dataclasses.dataclass
class Extraction:
    blocks: list[Block]
    source: str
    chars: int
    link_density: float
    score: float
    jsonld_chars: int
    warnings: list[str]


def normalize_ws(s: str) -> str:
    """Normalize invisible/spacing noise but preserve punctuation and wording."""
    s = html_lib.unescape(s or "")
    s = unicodedata.normalize("NFC", s)
    s = s.replace("\u00a0", " ").replace("\u2009", " ").replace("\u202f", " ")
    s = s.replace("\u200b", "").replace("\ufeff", "")
    s = re.sub(r"[ \t\r\f\v]+", " ", s)
    s = re.sub(r"\n\s*\n+", "\n", s)
    return s.strip()


def norm_for_match(s: str) -> str:
    """Only for alignment, never for displayed old/new text."""
    return re.sub(r"\s+", " ", normalize_ws(s)).strip()


def slugify(s: str, max_len: int = 90) -> str:
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode("ascii")
    s = re.sub(r"[^A-Za-z0-9]+", "-", s).strip("-").lower()
    return (s[:max_len].rstrip("-") or "article")


def safe_json(obj: Any) -> str:
    return json.dumps(obj, ensure_ascii=False, sort_keys=False)


def unwrap_wayback_url(href: str) -> str:
    """Turn Wayback-rewritten links back into the original destination."""
    if not href:
        return ""
    href = href.strip()
    # //web.archive.org/web/2020.../https://example.com
    m = re.match(
        r"^(?:https?:)?//web\.archive\.org/web/\d+(?:[a-z_]+)?/(https?://.+)$",
        href,
        flags=re.I,
    )
    if m:
        return m.group(1)
    # /web/2020.../https://example.com
    m = re.match(r"^/web/\d+(?:[a-z_]+)?/(https?://.+)$", href, flags=re.I)
    if m:
        return m.group(1)
    return href


def canonicalize_link(href: str, base_url: str) -> str:
    href = unwrap_wayback_url(href)
    if not href or href.startswith(("javascript:", "mailto:", "tel:", "#")):
        return ""
    return urljoin(base_url, href)


def remove_noise_nodes(soup: BeautifulSoup) -> None:
    for comment in soup.find_all(string=lambda x: isinstance(x, Comment)):
        comment.extract()
    for selector in REMOVE_SELECTORS:
        try:
            for node in soup.select(selector):
                node.decompose()
        except Exception:
            pass


def is_end_marker(text: str) -> bool:
    return any(rx.search(text) for rx in END_MARKERS)


def is_boilerplate_text(text: str, title: str = "") -> bool:
    low = norm_for_match(text).lower()
    if not low:
        return True
    if title and low == norm_for_match(title).lower():
        return True
    if low in DROP_EXACT:
        return True
    if any(low.startswith(p) for p in DROP_PREFIXES):
        return True
    if re.match(r"^by\s+ross\s+barkan(?:\b|\s*,)", low):
        return True
    if low in {"intelligencer", "new york magazine", "nymag.com"}:
        return True
    if re.match(r"^(published|updated)\s+[a-z]+\s+\d{1,2},\s+20\d{2}", low):
        return True
    if re.match(r"^photo:\s", low):
        return True
    if low.startswith("a political columnist for intelligencer"):
        return True
    return False


def block_links(node: Tag, base_url: str) -> list[Link]:
    out: list[Link] = []
    seen: set[tuple[str, str]] = set()
    for a in node.find_all("a", href=True):
        text = normalize_ws(a.get_text(" ", strip=True))
        url = canonicalize_link(a.get("href", ""), base_url)
        if not url:
            continue
        key = (text, url)
        if key not in seen:
            out.append(Link(text=text, url=url))
            seen.add(key)
    return out


def iter_leaf_blocks(container: Tag) -> Iterable[Tag]:
    """
    Yield block-level prose nodes, avoiding duplicate text from nested blocks.
    Example: a <blockquote><p>...</p></blockquote> is one blockquote, not both.
    """
    for node in container.find_all(BLOCK_TAGS):
        if not isinstance(node, Tag):
            continue
        # Skip a node nested inside another chosen block type.
        parent = node.parent
        nested = False
        while isinstance(parent, Tag) and parent is not container:
            if parent.name in BLOCK_TAGS:
                nested = True
                break
            parent = parent.parent
        if nested:
            continue
        yield node


def blocks_from_container(container: Tag, base_url: str, title: str) -> list[Block]:
    blocks: list[Block] = []
    substantive_seen = False

    for node in iter_leaf_blocks(container):
        text = normalize_ws(node.get_text(" ", strip=True))
        if not text:
            continue

        if is_end_marker(text):
            if substantive_seen:
                break
            continue

        if is_boilerplate_text(text, title=title):
            continue

        # Before the first clear prose block, ignore tiny metadata fragments.
        if not substantive_seen:
            if node.name == "p" and len(text) >= 60:
                substantive_seen = True
            elif node.name == "blockquote" and len(text) >= 40:
                substantive_seen = True
            elif node.name in {"h2", "h3", "h4"}:
                # A subhead may precede the first paragraph, but do not let it
                # alone start an extraction; save it tentatively.
                blocks.append(Block(kind=node.name, text=text, links=block_links(node, base_url)))
                continue
            else:
                continue

        kind = node.name or "p"
        block = Block(kind=kind, text=text, links=block_links(node, base_url))
        blocks.append(block)

    # Remove any tentative leading headings if no prose followed.
    while blocks and blocks[0].kind in {"h2", "h3", "h4"} and len(blocks) == 1:
        blocks.pop(0)

    # Conservative de-duplication: only exact adjacent duplicates.
    deduped: list[Block] = []
    for b in blocks:
        if deduped and norm_for_match(deduped[-1].text) == norm_for_match(b.text):
            continue
        deduped.append(b)
    return deduped


def jsonld_article_body(soup: BeautifulSoup) -> str:
    bodies: list[str] = []
    for script in soup.find_all("script", attrs={"type": "application/ld+json"}):
        raw = script.string or script.get_text(" ", strip=False)
        if not raw:
            continue
        try:
            data = json.loads(raw)
        except Exception:
            continue

        def walk(x: Any) -> None:
            if isinstance(x, dict):
                body = x.get("articleBody")
                if isinstance(body, str) and len(normalize_ws(body)) > 200:
                    bodies.append(normalize_ws(body))
                for v in x.values():
                    walk(v)
            elif isinstance(x, list):
                for v in x:
                    walk(v)

        walk(data)
    return max(bodies, key=len) if bodies else ""


def extraction_score(blocks: list[Block], jsonld_len: int) -> tuple[float, float, int]:
    chars = sum(len(b.text) for b in blocks)
    link_chars = sum(len(link.text) for b in blocks for link in b.links)
    link_density = (link_chars / chars) if chars else 1.0
    n = len(blocks)

    # Main reward: plausible amount of prose and multiple blocks.
    score = min(chars, 30000) / 120.0 + min(n, 80) * 2.0
    # Navigation/recirculation containers have much higher anchor-text density.
    score -= min(link_density, 1.0) * 90.0

    # JSON-LD is a useful independent estimate of how long the body should be.
    if jsonld_len and chars:
        ratio = min(chars, jsonld_len) / max(chars, jsonld_len)
        score += ratio * 70.0
        if chars > jsonld_len * 1.8:
            score -= 70.0

    if chars < 500:
        score -= 150.0
    if n < 3:
        score -= 100.0
    return score, link_density, chars


def extract_article(html: str, base_url: str, title: str = "") -> Extraction:
    soup0 = BeautifulSoup(html, "lxml")
    jsonld = jsonld_article_body(soup0)
    jsonld_len = len(jsonld)

    # Work on a cleaned copy for DOM candidates.
    soup = BeautifulSoup(html, "lxml")
    remove_noise_nodes(soup)

    candidates: list[tuple[str, list[Block]]] = []
    seen_nodes: set[int] = set()

    for selector in CANDIDATE_SELECTORS:
        try:
            nodes = soup.select(selector)
        except Exception:
            continue
        for idx, node in enumerate(nodes[:8]):
            if not isinstance(node, Tag):
                continue
            ident = id(node)
            if ident in seen_nodes:
                continue
            seen_nodes.add(ident)
            blocks = blocks_from_container(node, base_url, title)
            if blocks:
                candidates.append((f"dom:{selector}[{idx}]", blocks))

    # Readability often isolates the body extremely well and preserves links.
    if Document is not None:
        try:
            summary_html = Document(html).summary(html_partial=True)
            rsoup = BeautifulSoup(summary_html, "lxml")
            remove_noise_nodes(rsoup)
            root = rsoup.body or rsoup
            blocks = blocks_from_container(root, base_url, title)
            if blocks:
                candidates.append(("readability", blocks))
        except Exception:
            pass

    if not candidates:
        # Last DOM fallback: body itself, still subjected to start/end filters.
        root = soup.body or soup
        blocks = blocks_from_container(root, base_url, title)
        if blocks:
            candidates.append(("dom:body-fallback", blocks))

    if not candidates:
        return Extraction(
            blocks=[], source="none", chars=0, link_density=1.0, score=-999.0,
            jsonld_chars=jsonld_len, warnings=["No plausible article blocks extracted."],
        )

    ranked = []
    for source, blocks in candidates:
        score, density, chars = extraction_score(blocks, jsonld_len)
        ranked.append((score, -density, chars, source, blocks))
    ranked.sort(reverse=True, key=lambda x: (x[0], x[1], x[2]))
    score, neg_density, chars, source, blocks = ranked[0]

    warnings: list[str] = []
    if chars < 800:
        warnings.append(f"Short extraction: {chars} characters.")
    if -neg_density > 0.35:
        warnings.append(f"High anchor-text density: {-neg_density:.2%}.")
    if jsonld_len and chars > jsonld_len * 1.6:
        warnings.append("Extracted body is much longer than JSON-LD articleBody; inspect for recirculation noise.")
    if jsonld_len and chars < jsonld_len * 0.55:
        warnings.append("Extracted body is much shorter than JSON-LD articleBody; inspect for truncation/paywall.")

    return Extraction(
        blocks=blocks, source=source, chars=chars, link_density=-neg_density,
        score=score, jsonld_chars=jsonld_len, warnings=warnings,
    )



def extraction_is_usable(ex: Extraction, min_chars: int) -> bool:
    if ex.chars < min_chars or len(ex.blocks) < 3 or ex.link_density >= 0.55:
        return False
    if ex.jsonld_chars:
        if ex.chars > ex.jsonld_chars * 2.25:
            return False
        if ex.chars < ex.jsonld_chars * 0.35:
            return False
    return True


def request_with_retry(
    session: requests.Session,
    url: str,
    *,
    params: Optional[list[tuple[str, str]]] = None,
    timeout: int = 45,
    max_tries: int = 2,
    label: str = "GET",
    verbose: bool = True,
    max_backoff: float = 30.0,
    give_up_after: float = 300.0,
) -> requests.Response:
    """
    GET with resilient retries and immediate progress/error reporting.

    Transient trouble (timeouts, connection errors, 429 rate-limiting, 5xx
    server errors) is retried with capped exponential backoff for up to
    `give_up_after` seconds (default 5 minutes) -- long enough to ride out a
    brief Wayback Machine or NYMag hiccup, short enough that a real outage
    doesn't hang the crawl indefinitely. When it does give up, it raises, and
    the caller records that one link as not-yet-done rather than "ok" --
    so simply re-running the same command later picks it back up. A genuine
    client error (401/403/404/...) still respects the shorter `max_tries`.
    """
    start = time.monotonic()
    attempt = 0
    while True:
        attempt += 1
        t0 = time.monotonic()
        progress(f"        {label}: attempt {attempt} ...", enabled=verbose)
        try:
            r = session.get(url, params=params, timeout=timeout, allow_redirects=True)
            elapsed = time.monotonic() - t0
            progress(
                f"        {label}: HTTP {r.status_code} in {elapsed:.1f}s",
                enabled=verbose,
            )

            if r.status_code == 429 or r.status_code >= 500:
                total_elapsed = time.monotonic() - start
                if total_elapsed >= give_up_after:
                    progress(
                        f"        {label}: giving up after {total_elapsed/60:.1f}m of "
                        f"transient HTTP {r.status_code} errors",
                        enabled=verbose,
                    )
                    r.raise_for_status()
                delay = min(1.5 * (2 ** min(attempt - 1, 6)), max_backoff)
                progress(
                    f"        {label}: transient HTTP {r.status_code}; retrying in {delay:.1f}s",
                    enabled=verbose,
                )
                time.sleep(delay)
                continue

            if r.status_code >= 400:
                if attempt < max_tries:
                    delay = min(1.5 * (2 ** (attempt - 1)), max_backoff)
                    progress(
                        f"        {label}: HTTP {r.status_code}; retrying in {delay:.1f}s "
                        f"({attempt}/{max_tries})",
                        enabled=verbose,
                    )
                    time.sleep(delay)
                    continue
                r.raise_for_status()

            return r
        except requests.exceptions.HTTPError:
            raise
        except Exception as e:
            total_elapsed = time.monotonic() - start
            if total_elapsed >= give_up_after:
                progress(
                    f"        {label}: giving up after {total_elapsed/60:.1f}m of retries: "
                    f"{type(e).__name__}: {e}",
                    enabled=verbose,
                )
                raise
            elapsed = time.monotonic() - t0
            delay = min(1.5 * (2 ** min(attempt - 1, 6)), max_backoff)
            progress(
                f"        {label}: FAILED after {elapsed:.1f}s: {type(e).__name__}: {e}; "
                f"retrying in {delay:.1f}s",
                enabled=verbose,
            )

            time.sleep(delay)


def url_variants(url: str) -> list[str]:
    p = urlparse(url)
    host = p.netloc.lower()
    path = p.path
    if p.query:
        path += "?" + p.query
    bare = host[4:] if host.startswith("www.") else host
    variants = [
        f"https://{bare}{path}", f"http://{bare}{path}",
        f"https://www.{bare}{path}", f"http://www.{bare}{path}",
    ]
    # Preserve exact input first.
    return list(dict.fromkeys([url] + variants))


def cdx_captures_for_variant(
    session: requests.Session,
    variant: str,
    cutoff: str,
    *,
    timeout: int,
    retries: int,
    verbose: bool,
    variant_label: str,
    give_up_after: float = 300.0,
) -> tuple[list[dict[str, str]], Optional[str]]:
    """Query one CDX URL variant and keep transport failure distinct from zero captures."""
    endpoint = "https://web.archive.org/cdx/search/cdx"
    params = [
        ("url", variant),
        ("output", "json"),
        ("fl", "timestamp,original,statuscode,mimetype,digest"),
        ("filter", "statuscode:200"),
        ("filter", "mimetype:text/html"),
        ("to", cutoff),
        ("collapse", "digest"),
        ("limit", "1000"),
    ]
    try:
        r = request_with_retry(
            session, endpoint, params=params, timeout=timeout, max_tries=retries,
            label=f"CDX {variant_label}", verbose=verbose, give_up_after=give_up_after,
        )
        data = r.json()
    except Exception as e:
        error = f"{type(e).__name__}: {e}"
        progress(f"        CDX variant unavailable: {error}", enabled=verbose)
        return [], error

    if not data or len(data) < 2:
        progress("        CDX answered successfully: no captures for this variant", enabled=verbose)
        return [], None
    header = data[0]
    return [dict(zip(header, row)) for row in data[1:]], None


def wayback_replay_url(timestamp: str, original: str, raw: bool = True) -> str:
    modifier = "id_/" if raw else "/"
    # Do not URL-encode original wholesale; Wayback expects a normal URL here.
    return f"https://web.archive.org/web/{timestamp}{modifier}{original}"



def parse_wayback_replay_url(url: str) -> tuple[str, str]:
    m = re.search(r"/web/(\d{14})(?:[a-z_]+)?/(https?://.+)$", url or "", flags=re.I)
    if not m:
        return "", ""
    return m.group(1), m.group(2)


def resolve_wayback_response_provenance(
    response: requests.Response,
    requested_timestamp: str,
    requested_original: str,
) -> tuple[str, str]:
    actual_timestamp, actual_original = parse_wayback_replay_url(response.url or "")
    return actual_timestamp or requested_timestamp, actual_original or requested_original


def wayback_response_is_expected(
    html: str,
    row_url: str,
    original_url: str,
    timestamp: str,
    cutoff: str,
    extraction: Extraction,
    min_chars: int,
) -> bool:
    if not timestamp or timestamp > cutoff:
        return False
    if canonical_article_url(original_url) != canonical_article_url(row_url):
        return False
    soup = BeautifulSoup(html, "lxml")
    embedded = canonical_article_url(extract_canonical_url_from_html(soup, fallback=""))
    if embedded and embedded != canonical_article_url(row_url):
        return False
    if has_target_attribution_correction(soup):
        return False
    return extraction_is_usable(extraction, min_chars)



def fetch_earliest_usable_archive(
    session: requests.Session,
    url: str,
    title: str,
    cutoff: str,
    min_chars: int,
    max_snapshots_to_try: int,
    *,
    timeout: int,
    retries: int,
    verbose: bool,
    give_up_after: float = 300.0,
) -> tuple[Optional[dict[str, Any]], list[dict[str, Any]]]:
    """Find the earliest usable pre-cutoff capture using canonical-first URL variants."""
    progress("    querying Wayback capture index...", enabled=verbose)
    variants = url_variants(url)
    merged: dict[tuple[str, str], dict[str, str]] = {}
    tried_timestamps: set[str] = set()
    attempts: list[dict[str, Any]] = []
    cdx_failures = 0
    cdx_successes = 0

    for vn, variant in enumerate(variants, 1):
        progress(f"    Wayback CDX variant {vn}/{len(variants)}: {variant}", enabled=verbose)
        rows, cdx_error = cdx_captures_for_variant(
            session, variant, cutoff, timeout=timeout, retries=retries, verbose=verbose,
            variant_label=f"{vn}/{len(variants)}", give_up_after=give_up_after,
        )
        if cdx_error is not None:
            cdx_failures += 1
            attempts.append({
                "stage": "cdx", "variant": variant, "usable": False, "error": cdx_error,
            })
            continue

        cdx_successes += 1
        added = 0
        for rec in rows:
            key = (rec.get("timestamp", ""), rec.get("digest", ""))
            if key not in merged:
                added += 1
            merged[key] = rec
        progress(f"        {len(rows)} returned; {added} new unique captures", enabled=verbose)

        captures_sorted = sorted(merged.values(), key=lambda x: x.get("timestamp", ""))
        for cap in captures_sorted:
            if len(tried_timestamps) >= max_snapshots_to_try:
                break
            requested_ts = cap.get("timestamp", "")
            if not requested_ts or requested_ts in tried_timestamps:
                continue
            tried_timestamps.add(requested_ts)
            requested_original = cap.get("original", url)
            replay = wayback_replay_url(requested_ts, requested_original, raw=True)
            progress(
                f"    snapshot {len(tried_timestamps)}/{max_snapshots_to_try}: {requested_ts}",
                enabled=verbose,
            )
            try:
                r = request_with_retry(
                    session, replay, timeout=timeout, max_tries=retries,
                    label=f"snapshot {requested_ts}", verbose=verbose, give_up_after=give_up_after,
                )
                actual_ts, actual_original = resolve_wayback_response_provenance(
                    r, requested_ts, requested_original
                )
                progress("        extracting archived article body...", enabled=verbose)
                ex = extract_article(r.text, base_url=actual_original, title=title)
                usable = wayback_response_is_expected(
                    r.text, url, actual_original, actual_ts, cutoff, ex, min_chars
                )
                progress(
                    f"        extracted {ex.chars:,} chars / {len(ex.blocks)} blocks "
                    f"via {ex.source} -> {'USABLE' if usable else 'reject'}",
                    enabled=verbose,
                )
                for warning in ex.warnings:
                    progress(f"        warning: {warning}", enabled=verbose)
                attempts.append({
                    "stage": "snapshot",
                    "timestamp": actual_ts,
                    "requested_timestamp": requested_ts,
                    "original": actual_original,
                    "replay_url": r.url or replay,
                    "chars": ex.chars,
                    "blocks": len(ex.blocks),
                    "source": ex.source,
                    "warnings": ex.warnings,
                    "usable": usable,
                })
                if usable:
                    progress(
                        f"    selected archive snapshot {actual_ts}; skipping remaining URL variants",
                        enabled=verbose,
                    )
                    return {
                        "timestamp": actual_ts,
                        "original": actual_original,
                        "archive_url": f"https://web.archive.org/web/{actual_ts}/{actual_original}",
                        "raw_replay_url": r.url or replay,
                        "html": r.text,
                        "extraction": ex,
                    }, attempts
            except Exception as e:
                attempts.append({
                    "stage": "snapshot",
                    "timestamp": requested_ts,
                    "original": requested_original,
                    "replay_url": replay,
                    "usable": False,
                    "error": f"{type(e).__name__}: {e}",
                })
                progress(f"        snapshot failed; leaving it retryable: {e}", enabled=verbose)
            time.sleep(0.10)

        if len(tried_timestamps) >= max_snapshots_to_try:
            break

    if not merged:
        if cdx_failures:
            progress(
                f"    Wayback CDX did not give a complete answer "
                f"({cdx_failures} failed variant request(s), {cdx_successes} successful); "
                "this article remains retryable.",
                enabled=verbose,
            )
        else:
            progress(
                "    Wayback: CDX answered successfully but no pre-cutoff captures were found",
                enabled=verbose,
            )
    else:
        progress("    no tested snapshot produced a usable article body", enabled=verbose)
    return None, attempts


def block_to_dict(b: Block) -> dict[str, Any]:
    return {
        "kind": b.kind,
        "text": b.text,
        "links": [dataclasses.asdict(x) for x in b.links],
    }


def ex_to_dict(ex: Extraction) -> dict[str, Any]:
    return {
        "source": ex.source,
        "chars": ex.chars,
        "link_density": round(ex.link_density, 6),
        "score": round(ex.score, 3),
        "jsonld_chars": ex.jsonld_chars,
        "warnings": ex.warnings,
        "blocks": [block_to_dict(b) for b in ex.blocks],
        "text": "\n\n".join(b.text for b in ex.blocks),
    }


def flatten_links(blocks: list[Block]) -> list[dict[str, str]]:
    seen = set()
    out = []
    for b in blocks:
        for link in b.links:
            key = (link.text, link.url)
            if key in seen:
                continue
            seen.add(key)
            out.append({"text": link.text, "url": link.url})
    return out


def tokenize_for_inline_diff(s: str) -> list[str]:
    # Preserve whitespace tokens so reconstructed diff is readable.
    return re.findall(r"\s+|[\w’'-]+|[^\w\s]", s, flags=re.UNICODE)


def inline_diff(old: str, new: str) -> str:
    a = tokenize_for_inline_diff(old)
    b = tokenize_for_inline_diff(new)
    sm = difflib.SequenceMatcher(a=a, b=b, autojunk=False)
    parts: list[str] = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        left = "".join(a[i1:i2])
        right = "".join(b[j1:j2])
        if tag == "equal":
            parts.append(left)
        elif tag == "delete":
            parts.append(f"[-{left}-]")
        elif tag == "insert":
            parts.append(f"{{+{right}+}}")
        else:
            parts.append(f"[-{left}-]{{+{right}+}}")
    return "".join(parts)


def pair_replacements(old_blocks: list[Block], new_blocks: list[Block]) -> list[dict[str, Any]]:
    """
    Greedy local pairing inside a SequenceMatcher replace region. This is only
    for readability; the raw old/new block arrays remain authoritative.
    """
    pairs: list[dict[str, Any]] = []
    used_new: set[int] = set()
    for oi, ob in enumerate(old_blocks):
        best_j = None
        best_ratio = -1.0
        for nj, nb in enumerate(new_blocks):
            if nj in used_new:
                continue
            ratio = difflib.SequenceMatcher(
                None, norm_for_match(ob.text), norm_for_match(nb.text), autojunk=False
            ).ratio()
            if ratio > best_ratio:
                best_ratio, best_j = ratio, nj
        if best_j is not None and best_ratio >= 0.18:
            used_new.add(best_j)
            nb = new_blocks[best_j]
            pairs.append({
                "old_index": oi,
                "new_index": best_j,
                "similarity": round(best_ratio, 4),
                "inline_diff": inline_diff(ob.text, nb.text),
            })
    return pairs


def compute_diff(old_blocks: list[Block], new_blocks: list[Block]) -> dict[str, Any]:
    a = [norm_for_match(b.text) for b in old_blocks]
    b = [norm_for_match(b.text) for b in new_blocks]
    sm = difflib.SequenceMatcher(a=a, b=b, autojunk=False)

    ops: list[dict[str, Any]] = []
    changed_old = changed_new = 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            continue
        old_seg = old_blocks[i1:i2]
        new_seg = new_blocks[j1:j2]
        changed_old += len(old_seg)
        changed_new += len(new_seg)
        op = {
            "op": tag,
            "old_range": [i1, i2],
            "new_range": [j1, j2],
            "old": [block_to_dict(x) for x in old_seg],
            "new": [block_to_dict(x) for x in new_seg],
        }
        if tag == "replace":
            op["paired"] = pair_replacements(old_seg, new_seg)
        ops.append(op)

    old_links = flatten_links(old_blocks)
    new_links = flatten_links(new_blocks)
    old_set = {(x["text"], x["url"]) for x in old_links}
    new_set = {(x["text"], x["url"]) for x in new_links}

    return {
        "operations": ops,
        "changed_old_blocks": changed_old,
        "changed_new_blocks": changed_new,
        "old_block_count": len(old_blocks),
        "new_block_count": len(new_blocks),
        "links_removed": [
            {"text": t, "url": u} for (t, u) in sorted(old_set - new_set)
        ],
        "links_added": [
            {"text": t, "url": u} for (t, u) in sorted(new_set - old_set)
        ],
    }


def format_links(links: list[dict[str, str]]) -> str:
    if not links:
        return ""
    return " | links: " + "; ".join(f"{x['text']!r} → {x['url']}" for x in links)



def render_diff_markdown(record: dict[str, Any]) -> str:
    meta = {
        "schema": DIFF_SCHEMA_VERSION,
        "current_url": record["current_url"],
        "live_sha256": record.get("live_sha256", ""),
        "wayback_sha256": record.get("wayback_sha256", ""),
        "archive_timestamp": record.get("archive_timestamp", ""),
        "archive_cutoff": record.get("archive_cutoff", ""),
    }
    lines = [
        f"# {record['title']}",
        f"<!-- nymag-diff-meta: {json.dumps(meta, ensure_ascii=False, sort_keys=True)} -->",
        "",
        f"- Current: {record['current_url']}",
        f"- Archive timestamp: {record.get('archive_timestamp') or 'NONE'}",
        f"- Archive: {record.get('archive_url') or 'NONE'}",
        f"- Status: {record['status']}",
        "",
    ]
    if record["status"] != "ok":
        lines.append("No valid old/current article-body comparison was produced.")
        if record.get("error"):
            lines.extend(["", f"Error: {record['error']}"])
        return "\n".join(lines) + "\n"

    diff = record["diff"]
    if not diff["operations"]:
        lines.append("## Article-body diff\n\nNo textual block changes detected after extraction/normalization.\n")
    else:
        lines.extend(["## Article-body diff", ""])
        for n, op in enumerate(diff["operations"], 1):
            lines.extend([f"### Change {n}: {op['op'].upper()}", ""])
            for item in op["old"]:
                lines.append(f"- **OLD [{item['kind']}]** {item['text']}{format_links(item['links'])}")
            for item in op["new"]:
                lines.append(f"- **NEW [{item['kind']}]** {item['text']}{format_links(item['links'])}")
            if op.get("paired"):
                lines.extend(["", "Paired inline diff(s):"])
                for pair in op["paired"]:
                    lines.append(f"- similarity {pair['similarity']:.2f}: {pair['inline_diff']}")
            lines.append("")

    if diff["links_removed"] or diff["links_added"]:
        lines.extend(["## Link delta", ""])
        for x in diff["links_removed"]:
            lines.append(f"- REMOVED: {x['text']!r} → {x['url']}")
        for x in diff["links_added"]:
            lines.append(f"- ADDED: {x['text']!r} → {x['url']}")
        lines.append("")

    old_warn = record["old_extraction"].get("warnings", [])
    new_warn = record["current_extraction"].get("warnings", [])
    if old_warn or new_warn:
        lines.extend(["## Extraction warnings", ""])
        for w in old_warn:
            lines.append(f"- OLD: {w}")
        for w in new_warn:
            lines.append(f"- CURRENT: {w}")
        lines.append("")

    return "\n".join(lines) + "\n"



def extract_canonical_url_from_html(soup: BeautifulSoup, fallback: str = "") -> str:
    """Recover an article's real URL from its own saved HTML (canonical link, then og:url)."""
    link = soup.find("link", rel="canonical")
    if link and link.get("href"):
        return link["href"].strip()
    meta = soup.find("meta", attrs={"property": "og:url"})
    if meta and meta.get("content"):
        return meta["content"].strip()
    return fallback


def canonical_article_url(href: str, base_url: str = AUTHOR_ARCHIVE_URL) -> str:
    """Normalize a NYMag Intelligencer article URL and reject non-article links."""
    if not href:
        return ""
    href = urljoin(base_url, href.strip())
    p = urlparse(href)
    host = p.netloc.lower()
    if host.startswith("www."):
        host = host[4:]
    if host != "nymag.com":
        return ""
    path = re.sub(r"/{2,}", "/", p.path or "")
    if not path.startswith("/intelligencer/") or not path.endswith(".html"):
        return ""
    # Normalize historical http/www variants and drop tracking/query fragments.
    return f"https://nymag.com{path}"


def extract_displayed_h1(soup: BeautifulSoup, fallback: str = "") -> str:
    """Read the first non-empty displayed H1; fall back conservatively."""
    for h1 in soup.find_all("h1"):
        text = normalize_ws(h1.get_text(" ", strip=True))
        if text:
            return text
    og = soup.find("meta", attrs={"property": "og:title"})
    if isinstance(og, Tag):
        content = normalize_ws(og.get("content", ""))
        if content:
            return content
    return normalize_ws(fallback)


def extract_date_published(soup: BeautifulSoup) -> str:
    """Best-effort live publication date for the summary date field."""
    candidates: list[str] = []
    for script in soup.find_all("script", attrs={"type": "application/ld+json"}):
        raw = script.string or script.get_text(" ", strip=False)
        if not raw:
            continue
        try:
            data = json.loads(raw)
        except Exception:
            continue

        def walk(x: Any) -> None:
            if isinstance(x, dict):
                val = x.get("datePublished")
                if isinstance(val, str) and val.strip():
                    candidates.append(val.strip())
                for v in x.values():
                    walk(v)
            elif isinstance(x, list):
                for v in x:
                    walk(v)

        walk(data)
    return candidates[0] if candidates else ""


def has_target_attribution_correction(soup: BeautifulSoup) -> bool:
    """Detect the specific August 14, 2026 attribution-correction notice."""
    text = normalize_ws(soup.get_text(" ", strip=True))
    low = text.lower()
    return (
        CORRECTION_DATE.lower() in low
        and all(phrase in low for phrase in CORRECTION_REQUIRED_PHRASES)
    )


def extract_author_archive_articles(html: str, page_url: str) -> tuple[list[dict[str, str]], Optional[str]]:
    """Return article entries from one author-archive page plus its next-page URL."""
    soup = BeautifulSoup(html, "lxml")
    entries: list[dict[str, str]] = []
    seen: set[str] = set()

    for a in soup.find_all("a", href=True):
        if not isinstance(a, Tag):
            continue
        url = canonical_article_url(a.get("href", ""), page_url)
        if not url or url in seen:
            continue
        title = normalize_ws(a.get_text(" ", strip=True))
        # Article-card title anchors have real text; image/chrome links do not.
        if not title:
            continue
        seen.add(url)
        entries.append({"url": url, "listing_title": title})

    next_url: Optional[str] = None
    for a in soup.find_all("a", href=True):
        if not isinstance(a, Tag):
            continue
        text = normalize_ws(a.get_text(" ", strip=True)).lower()
        if text == "more articles":
            candidate = urljoin(page_url, a.get("href", ""))
            if candidate:
                next_url = candidate
                break

    return entries, next_url


def crawl_barkan_author_archive(
    session: requests.Session,
    *,
    timeout: int,
    retries: int,
    verbose: bool,
    give_up_after: float = 300.0,
) -> tuple[list[dict[str, str]], list[dict[str, Any]]]:
    """Crawl every Ross Barkan author-archive page, preserving newest-first order."""
    progress("[DISCOVERY] Crawling Ross Barkan author archive...", enabled=True)
    page_url: Optional[str] = AUTHOR_ARCHIVE_URL
    visited_pages: set[str] = set()
    seen_articles: set[str] = set()
    articles: list[dict[str, str]] = []
    problems: list[dict[str, Any]] = []
    page_no = 0

    while page_url and page_url not in visited_pages:
        page_no += 1
        visited_pages.add(page_url)
        parsed = urlparse(page_url)
        start_match = re.search(r"(?:^|&)start=(\d+)", parsed.query)
        start_label = start_match.group(1) if start_match else "0"
        progress(
            f"[ARCHIVE page {page_no} | start={start_label}] {page_url}",
            enabled=True,
        )
        try:
            r = request_with_retry(
                session, page_url, timeout=timeout, max_tries=retries,
                label=f"author archive page {page_no}", verbose=verbose, give_up_after=give_up_after,
            )
        except Exception as e:
            problems.append({
                "archive_page": page_url,
                "reason": "author archive fetch failed",
                "error": str(e),
            })
            progress(f"    archive page FAILED: {e}", enabled=True)
            break

        page_entries, next_url = extract_author_archive_articles(r.text, r.url or page_url)
        new_count = 0
        for entry in page_entries:
            if entry["url"] in seen_articles:
                continue
            seen_articles.add(entry["url"])
            articles.append(entry)
            new_count += 1

        progress(
            f"    archive entries: {len(page_entries)} on page; "
            f"{new_count} new; {len(articles)} unique total",
            enabled=True,
        )

        if not next_url:
            progress("    no 'More Articles' link; end of author archive reached", enabled=True)
            break
        if next_url in visited_pages:
            progress("    pagination loop detected; stopping archive crawl", enabled=True)
            break
        if new_count == 0:
            progress("    no new article URLs on this page; stopping archive crawl", enabled=True)
            break

        progress(f"    next archive page -> {next_url}", enabled=verbose)
        page_url = next_url
        time.sleep(0.10)

    progress(
        f"[DISCOVERY] Author archive crawl complete: {len(articles)} unique article URLs "
        f"across {page_no} page(s).",
        enabled=True,
    )
    return articles, problems



def discover_corrected_articles(
    session: requests.Session,
    candidates: list[dict[str, str]],
    *,
    timeout: int,
    retries: int,
    verbose: bool,
    live_dir: Optional[Path] = None,
    min_chars: int = 500,
    give_up_after: float = 300.0,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Scan the full author archive and assign row numbers only after a complete scan."""
    already_saved: dict[str, dict[str, Any]] = {}
    cache_dir: Optional[Path] = None
    if live_dir is not None:
        cache_dir = live_dir / "_discovery_cache"
        cache_dir.mkdir(parents=True, exist_ok=True)
        sources = list(live_dir.glob("*.html")) + list(cache_dir.glob("*.html"))
        for f in sorted(sources):
            try:
                html = f.read_text(encoding="utf-8")
                soup = BeautifulSoup(html, "lxml")
            except Exception:
                continue
            raw_url = extract_canonical_url_from_html(soup, fallback="")
            url = canonical_article_url(raw_url)
            if not url or not has_target_attribution_correction(soup):
                continue
            ex = extract_article(html, base_url=url, title=extract_displayed_h1(soup, fallback=""))
            if not extraction_is_usable(ex, min_chars):
                continue
            already_saved[url] = {
                "title": extract_displayed_h1(soup, fallback="") or f.stem,
                "url": url,
                "date": extract_date_published(soup),
                "html": html,
            }
        if already_saved:
            progress(
                f"[DISCOVERY] Indexed {len(already_saved)} saved corrected live page(s) by canonical URL.",
                enabled=True,
            )

    progress(
        f"[DISCOVERY] Scanning {len(candidates)} author-archive articles for the "
        f"{CORRECTION_DATE} attribution notice...",
        enabled=True,
    )
    matched: list[dict[str, Any]] = []
    problems: list[dict[str, Any]] = []
    total = len(candidates)
    reused = 0

    for pos, candidate in enumerate(candidates, 1):
        url = canonical_article_url(candidate["url"]) or candidate["url"]
        listing_title = candidate.get("listing_title", "")
        label = listing_title or url

        if url in already_saved:
            saved = dict(already_saved[url])
            saved["excel_row"] = len(matched) + 1
            matched.append(saved)
            reused += 1
            continue

        progress(f"[CORRECTION SCAN {pos}/{total}] {label}", enabled=True)
        try:
            r = request_with_retry(
                session, url, timeout=timeout, max_tries=retries,
                label=f"correction scan {pos}/{total}", verbose=verbose,
                give_up_after=give_up_after,
            )
            soup = BeautifulSoup(r.text, "lxml")
            canonical_url = canonical_article_url(extract_canonical_url_from_html(soup, fallback=r.url or url))
            if canonical_url != url:
                raise ValueError(f"article identity mismatch: expected {url}, got {canonical_url or r.url}")
            if not has_target_attribution_correction(soup):
                progress(
                    f"    no target correction | matched {len(matched)}/{EXPECTED_CORRECTION_COUNT}",
                    enabled=verbose,
                )
                continue

            title = extract_displayed_h1(soup, fallback=listing_title) or listing_title or url
            ex = extract_article(r.text, base_url=canonical_url, title=title)
            if not extraction_is_usable(ex, min_chars):
                raise ValueError(
                    f"corrected live page extraction unusable: {ex.chars} chars / {len(ex.blocks)} blocks"
                )
            row = {
                "excel_row": len(matched) + 1,
                "title": title,
                "url": canonical_url,
                "date": extract_date_published(soup),
                "html": r.text,
            }
            matched.append(row)
            already_saved[canonical_url] = dict(row)
            if cache_dir is not None:
                key = hashlib.sha256(canonical_url.encode("utf-8")).hexdigest()[:20]
                _atomic_write_text(cache_dir / f"{key}-{slugify(title)}.html", r.text)
            progress(
                f"    MATCH {len(matched)}/{EXPECTED_CORRECTION_COUNT}: {title}",
                enabled=True,
            )
        except Exception as e:
            problems.append({
                "url": url,
                "title": listing_title,
                "reason": "correction scan failed",
                "error": f"{type(e).__name__}: {e}",
            })
            progress(f"    correction scan FAILED; corpus will not be frozen: {e}", enabled=True)

        time.sleep(0.05)

    matched.sort(key=lambda r: int(r["excel_row"]))
    if reused:
        progress(
            f"[DISCOVERY] Reused {reused} saved corrected article(s); network-scanned {total - reused} candidate(s).",
            enabled=True,
        )
    progress(
        f"[DISCOVERY] Correction scan complete: {len(matched)} matching articles found; "
        f"{len(problems)} unresolved candidate(s).",
        enabled=True,
    )

    complete = not problems and len(matched) == EXPECTED_CORRECTION_COUNT
    if complete:
        progress(
            f"[DISCOVERY] Corpus check PASSED: exactly {EXPECTED_CORRECTION_COUNT} corrected articles.",
            enabled=True,
        )
        if live_dir is not None:
            for row in matched:
                target = canonical_live_target(live_dir, row)
                _atomic_write_text(target, row["html"])
                quarantine_conflicting_row_files(live_dir, row, target, ".html", kind="live")
    else:
        progress(
            f"[DISCOVERY] INCOMPLETE: need exactly {EXPECTED_CORRECTION_COUNT} matches and zero "
            "unresolved candidate fetches before row numbering is frozen.",
            enabled=True,
        )
    return matched, problems




def _atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def _atomic_write_json(path: Path, obj: dict[str, Any]) -> None:
    _atomic_write_text(path, json.dumps(obj, ensure_ascii=False, indent=2) + "\n")


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def quarantine_artifact(path: Path, reason: str) -> None:
    if not path.exists():
        return
    rejected = path.parent / "_rejected"
    rejected.mkdir(parents=True, exist_ok=True)
    target = rejected / path.name
    if target.exists():
        stem, suffix = path.stem, path.suffix
        n = 2
        while (rejected / f"{stem}-{n}{suffix}").exists():
            n += 1
        target = rejected / f"{stem}-{n}{suffix}"
    path.replace(target)
    progress(f"    rejected stale/invalid artifact {path.name}: {reason}", enabled=True)


def row_files(directory: Optional[Path], row_num: int, suffix: str) -> list[Path]:
    if directory is None or not directory.exists():
        return []
    return [
        p for p in sorted(directory.glob(f"{row_num:03d}-*{suffix}"))
        if p.is_file() and p.stat().st_size > 0
    ]


def live_path_is_valid(path: Path, row: dict[str, Any], min_chars: int) -> bool:
    try:
        html = path.read_text(encoding="utf-8")
        soup = BeautifulSoup(html, "lxml")
        embedded = canonical_article_url(extract_canonical_url_from_html(soup, fallback=""))
        if embedded != canonical_article_url(row["url"]):
            return False
        if not has_target_attribution_correction(soup):
            return False
        ex = extract_article(html, base_url=row["url"], title=row["title"])
        return extraction_is_usable(ex, min_chars)
    except Exception:
        return False


def find_valid_live_artifact(
    live_dir: Path,
    row: dict[str, Any],
    min_chars: int,
    *,
    quarantine_invalid: bool = True,
) -> Optional[Path]:
    canonical = canonical_live_target(live_dir, row)
    files = row_files(live_dir, int(row["excel_row"]), ".html")
    files.sort(key=lambda p: (p != canonical, p.name))
    for p in files:
        if live_path_is_valid(p, row, min_chars):
            return p
        if quarantine_invalid:
            quarantine_artifact(p, "live HTML does not validate for this row")
    return None


def wayback_meta_path(html_path: Path) -> Path:
    return html_path.with_name(html_path.name + ".meta.json")


def load_json(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def build_wayback_meta(
    row: dict[str, Any],
    html_path: Path,
    timestamp: str,
    original: str,
    archive_url: str,
    archive_cutoff: str,
) -> dict[str, Any]:
    return {
        "schema": 1,
        "excel_row": int(row["excel_row"]),
        "current_url": canonical_article_url(row["url"]) or row["url"],
        "archive_timestamp": str(timestamp),
        "archive_url": archive_url,
        "archive_original_url": original,
        "archive_cutoff": archive_cutoff,
        "wayback_sha256": sha256_file(html_path),
    }


def write_wayback_artifact(
    wayback_dir: Path,
    row: dict[str, Any],
    html: str,
    timestamp: str,
    original: str,
    archive_url: str,
    archive_cutoff: str,
) -> tuple[Path, dict[str, Any]]:
    target = canonical_wayback_target(wayback_dir, row)
    _atomic_write_text(target, html)
    meta = build_wayback_meta(row, target, timestamp, original, archive_url, archive_cutoff)
    _atomic_write_json(wayback_meta_path(target), meta)
    quarantine_conflicting_row_files(wayback_dir, row, target, ".html", kind="wayback")
    return target, meta


def wayback_path_is_valid(
    path: Path,
    row: dict[str, Any],
    cutoff: str,
    min_chars: int,
    meta: dict[str, Any],
) -> bool:
    try:
        if int(meta.get("excel_row", -1)) != int(row["excel_row"]):
            return False
        if canonical_article_url(meta.get("current_url", "")) != canonical_article_url(row["url"]):
            return False
        ts = str(meta.get("archive_timestamp", ""))
        if not ts or ts > cutoff:
            return False
        original = str(meta.get("archive_original_url", ""))
        if canonical_article_url(original) != canonical_article_url(row["url"]):
            return False
        if meta.get("wayback_sha256") != sha256_file(path):
            return False
        html = path.read_text(encoding="utf-8")
        soup = BeautifulSoup(html, "lxml")
        embedded = canonical_article_url(extract_canonical_url_from_html(soup, fallback=""))
        if embedded and embedded != canonical_article_url(row["url"]):
            return False
        if has_target_attribution_correction(soup):
            return False
        ex = extract_article(html, base_url=original, title=row["title"])
        return extraction_is_usable(ex, min_chars)
    except Exception:
        return False


def migrate_legacy_wayback_meta(
    path: Path,
    row: dict[str, Any],
    previous: Optional[dict[str, Any]],
    cutoff: str,
    min_chars: int,
) -> Optional[dict[str, Any]]:
    previous = previous or {}
    ts = str(previous.get("archive_timestamp", ""))
    original = str(previous.get("archive_original_url", ""))
    if not ts or ts > cutoff or canonical_article_url(original) != canonical_article_url(row["url"]):
        return None
    try:
        html = path.read_text(encoding="utf-8")
        soup = BeautifulSoup(html, "lxml")
        embedded = canonical_article_url(extract_canonical_url_from_html(soup, fallback=""))
        if embedded and embedded != canonical_article_url(row["url"]):
            return None
        if has_target_attribution_correction(soup):
            return None
        ex = extract_article(html, base_url=original, title=row["title"])
        if not extraction_is_usable(ex, min_chars):
            return None
        known_hash = previous.get("wayback_sha256")
        if known_hash:
            if known_hash != sha256_file(path):
                return None
        else:
            prior_text = ((previous.get("old_extraction") or {}).get("text") or "")
            if not prior_text or norm_for_match(prior_text) != norm_for_match("\n\n".join(b.text for b in ex.blocks)):
                return None
        meta = build_wayback_meta(
            row, path, ts, original,
            previous.get("archive_url") or f"https://web.archive.org/web/{ts}/{original}",
            str(previous.get("archive_cutoff") or cutoff),
        )
        _atomic_write_json(wayback_meta_path(path), meta)
        return meta
    except Exception:
        return None


def find_valid_wayback_artifact(
    wayback_dir: Path,
    row: dict[str, Any],
    previous: Optional[dict[str, Any]],
    cutoff: str,
    min_chars: int,
    *,
    quarantine_invalid: bool = True,
) -> tuple[Optional[Path], Optional[dict[str, Any]]]:
    canonical = canonical_wayback_target(wayback_dir, row)
    files = row_files(wayback_dir, int(row["excel_row"]), ".html")
    files.sort(key=lambda p: (p != canonical, p.name))
    for p in files:
        meta_path = wayback_meta_path(p)
        meta = load_json(meta_path) if meta_path.exists() else {}
        if not meta:
            meta = migrate_legacy_wayback_meta(p, row, previous, cutoff, min_chars) or {}
        if meta and wayback_path_is_valid(p, row, cutoff, min_chars, meta):
            return p, meta
        if quarantine_invalid:
            quarantine_artifact(p, "Wayback HTML or capture provenance does not validate for this row")
            if meta_path.exists():
                quarantine_artifact(meta_path, "Wayback metadata no longer has a matching HTML artifact")
    return None, None


def diff_metadata(path: Path) -> dict[str, Any]:
    try:
        head = path.read_text(encoding="utf-8")[:16000]
    except Exception:
        return {}
    m = re.search(r"<!--\s*nymag-diff-meta:\s*(\{.*?\})\s*-->", head, flags=re.S)
    if not m:
        return {}
    try:
        data = json.loads(m.group(1))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def diff_path_is_valid(
    path: Path,
    row: dict[str, Any],
    live_path: Path,
    wayback_path: Path,
    wayback_meta: dict[str, Any],
    cutoff: str,
) -> bool:
    meta = diff_metadata(path)
    if meta.get("schema") != DIFF_SCHEMA_VERSION:
        return False
    if canonical_article_url(meta.get("current_url", "")) != canonical_article_url(row["url"]):
        return False
    if meta.get("live_sha256") != sha256_file(live_path):
        return False
    if meta.get("wayback_sha256") != sha256_file(wayback_path):
        return False
    if str(meta.get("archive_timestamp", "")) != str(wayback_meta.get("archive_timestamp", "")):
        return False
    if str(meta.get("archive_timestamp", "")) > cutoff:
        return False
    try:
        head = path.read_text(encoding="utf-8")[:16000]
    except Exception:
        return False
    return bool(re.search(r"(?m)^- Status:\s*ok\s*$", head))


def find_valid_diff_artifact(
    diffs_dir: Path,
    row: dict[str, Any],
    live_path: Optional[Path],
    wayback_path: Optional[Path],
    wayback_meta: Optional[dict[str, Any]],
    cutoff: str,
    *,
    quarantine_invalid: bool = True,
) -> Optional[Path]:
    if live_path is None or wayback_path is None or not wayback_meta:
        return None
    canonical = canonical_diff_target(diffs_dir, row)
    files = row_files(diffs_dir, int(row["excel_row"]), ".md")
    files.sort(key=lambda p: (p != canonical, p.name))
    for p in files:
        if diff_path_is_valid(p, row, live_path, wayback_path, wayback_meta, cutoff):
            return p
        if quarantine_invalid:
            quarantine_artifact(p, "diff metadata does not match the validated HTML inputs")
    return None


def quarantine_conflicting_row_files(
    directory: Path,
    row: dict[str, Any],
    keep: Path,
    suffix: str,
    *,
    kind: str,
) -> None:
    for p in row_files(directory, int(row["excel_row"]), suffix):
        if p == keep:
            continue
        quarantine_artifact(p, f"another validated {kind} artifact owns this row")
        meta = wayback_meta_path(p)
        if meta.exists():
            quarantine_artifact(meta, "metadata belongs to a rejected Wayback artifact")


def _row_metadata(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "excel_row": int(row["excel_row"]),
        "title": row["title"],
        "url": row["url"],
        "date": row.get("date", ""),
    }



def write_csv(path: Path, rows: list[dict[str, Any]], fieldnames: list[str]) -> None:
    buf = io.StringIO(newline="")
    w = csv.DictWriter(buf, fieldnames=fieldnames, extrasaction="ignore")
    w.writeheader()
    w.writerows(rows)
    _atomic_write_text(path, buf.getvalue())


# ---------------------------------------------------------------------------
# Filesystem-driven artifact helpers
# ---------------------------------------------------------------------------

def row_number_from_path(path: Path) -> Optional[int]:
    m = re.match(r"^(\d{1,3})-", path.name)
    return int(m.group(1)) if m else None



def find_row_file(directory: Optional[Path], row_num: int, suffix: str) -> Optional[Path]:
    files = row_files(directory, row_num, suffix)
    return files[0] if files else None


def canonical_live_target(live_dir: Path, row: dict[str, Any]) -> Path:
    return live_dir / f"{int(row['excel_row']):03d}-{slugify(row['title'])}.html"


def canonical_wayback_target(wayback_dir: Path, row: dict[str, Any]) -> Path:
    return wayback_dir / f"{int(row['excel_row']):03d}-{slugify(row['title'])}.html"


def canonical_diff_target(diffs_dir: Path, row: dict[str, Any]) -> Path:
    return diffs_dir / f"{int(row['excel_row']):03d}-{slugify(row['title'])}.md"


def _merge_corpus_candidate(
    candidates: dict[int, list[dict[str, Any]]],
    *,
    row_num: Any,
    url: str,
    title: str = "",
    date: str = "",
    source: str,
    priority: int,
) -> None:
    try:
        row_num = int(row_num)
    except Exception:
        return
    if not (1 <= row_num <= EXPECTED_CORRECTION_COUNT):
        return
    url = canonical_article_url(url) or (url or "").strip()
    if not url:
        return
    candidates.setdefault(row_num, []).append({
        "excel_row": row_num,
        "url": url,
        "title": normalize_ws(title),
        "date": (date or "").strip(),
        "source": source,
        "priority": priority,
    })



def reconstruct_corpus_from_existing_outputs(
    out_dir: Path,
    results_path: Path,
    summary_path: Path,
    log_path: Path,
    corpus_path: Path,
    live_dir: Optional[Path],
    wayback_dir: Optional[Path],
    diffs_dir: Path,
) -> tuple[list[dict[str, Any]], list[int]]:
    """Reconstruct the row -> URL address book from stable metadata and reject contradictions."""
    candidates: dict[int, list[dict[str, Any]]] = {}

    if corpus_path.exists():
        try:
            data = json.loads(corpus_path.read_text(encoding="utf-8"))
            for r in data.get("rows", []) if isinstance(data, dict) else []:
                _merge_corpus_candidate(
                    candidates, row_num=r.get("excel_row"), url=r.get("url", ""),
                    title=r.get("title", ""), date=r.get("date", ""),
                    source="corpus.json", priority=0,
                )
        except Exception as e:
            progress(f"[CORPUS] Ignoring unreadable {corpus_path.name}: {e}", enabled=True)

    if log_path.exists():
        try:
            log = json.loads(log_path.read_text(encoding="utf-8"))
            for r in (log.get("discovery", {}).get("rows", []) if isinstance(log, dict) else []):
                _merge_corpus_candidate(
                    candidates, row_num=r.get("excel_row"), url=r.get("url", ""),
                    title=r.get("title", ""), date=r.get("date", ""),
                    source="run_log.discovery", priority=1,
                )
            for entry in (log.get("articles", {}).values() if isinstance(log, dict) else []):
                if isinstance(entry, dict):
                    _merge_corpus_candidate(
                        candidates, row_num=entry.get("excel_row"),
                        url=entry.get("current_url", ""), title=entry.get("title", ""),
                        source="run_log.articles", priority=2,
                    )
        except Exception:
            pass

    if results_path.exists():
        for rec in latest_records_by_row(results_path).values():
            _merge_corpus_candidate(
                candidates, row_num=rec.get("excel_row"), url=rec.get("current_url", ""),
                title=rec.get("title", ""), date=rec.get("date", ""),
                source="results.jsonl", priority=3,
            )

    if summary_path.exists():
        try:
            with summary_path.open("r", encoding="utf-8", newline="") as f:
                for r in csv.DictReader(f):
                    _merge_corpus_candidate(
                        candidates, row_num=r.get("excel_row"), url=r.get("current_url", ""),
                        title=r.get("title", ""), date=r.get("date", ""),
                        source="summary.csv", priority=4,
                    )
        except Exception:
            pass

    chosen: dict[int, dict[str, Any]] = {}
    for row_num in range(1, EXPECTED_CORRECTION_COUNT + 1):
        opts = candidates.get(row_num, [])
        if not opts:
            continue
        urls = {x["url"] for x in opts}
        if len(urls) != 1:
            progress(
                f"[CORPUS] Contradictory URL evidence for row {row_num}; discovery will resolve it.",
                enabled=True,
            )
            continue
        opts.sort(key=lambda x: (x["priority"], 0 if x.get("title") else 1))
        best = dict(opts[0])
        for alt in opts[1:]:
            if not best.get("title") and alt.get("title"):
                best["title"] = alt["title"]
            if not best.get("date") and alt.get("date"):
                best["date"] = alt["date"]
        best.pop("priority", None)
        best.pop("source", None)
        if not best.get("title"):
            best["title"] = best["url"].rstrip("/").split("/")[-1].removesuffix(".html")
        chosen[row_num] = best

    url_owner: dict[str, int] = {}
    for row_num in sorted(list(chosen)):
        url = chosen[row_num]["url"]
        if url in url_owner:
            progress(
                f"[CORPUS] Duplicate URL claimed by rows {url_owner[url]} and {row_num}; "
                f"row {row_num} will be recovered by discovery.",
                enabled=True,
            )
            del chosen[row_num]
        else:
            url_owner[url] = row_num

    rows = [chosen[n] for n in sorted(chosen)]
    missing = [n for n in range(1, EXPECTED_CORRECTION_COUNT + 1) if n not in chosen]
    return rows, missing


def save_corpus_manifest(corpus_path: Path, rows: list[dict[str, Any]]) -> None:
    ordered = sorted(rows, key=lambda r: int(r["excel_row"]))
    _atomic_write_json(corpus_path, {
        "count": len(ordered),
        "rows": [_row_metadata(r) for r in ordered],
    })



def latest_records_by_row(results_path: Path) -> dict[int, dict[str, Any]]:
    latest: dict[int, dict[str, Any]] = {}
    durable = {
        "archive_timestamp", "archive_url", "archive_original_url", "archive_cutoff",
        "archive_attempts", "wayback_sha256", "old_extraction",
    }
    if not results_path.exists():
        return latest
    with results_path.open("r", encoding="utf-8") as f:
        for line in f:
            try:
                rec = json.loads(line)
                n = int(rec.get("excel_row"))
            except Exception:
                continue
            if not (1 <= n <= EXPECTED_CORRECTION_COUNT):
                continue
            previous = latest.get(n, {})
            same_url = (
                not previous.get("current_url")
                or not rec.get("current_url")
                or canonical_article_url(previous.get("current_url", ""))
                == canonical_article_url(rec.get("current_url", ""))
            )
            merged = dict(previous) if same_url else {}
            merged.update(rec)
            archive_changed = bool(
                rec.get("archive_timestamp")
                and previous.get("archive_timestamp")
                and str(rec.get("archive_timestamp")) != str(previous.get("archive_timestamp"))
            )
            for key in durable:
                if key == "old_extraction" and archive_changed:
                    merged.pop(key, None)
                    continue
                if not rec.get(key) and same_url and previous.get(key):
                    merged[key] = previous[key]
            latest[n] = merged
    return latest


def append_result_record(results_path: Path, record: dict[str, Any]) -> None:
    results_path.parent.mkdir(parents=True, exist_ok=True)
    with results_path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(record, ensure_ascii=False) + "\n")
        f.flush()


def compact_results_jsonl(results_path: Path) -> None:
    latest = latest_records_by_row(results_path)
    text = "".join(
        json.dumps(latest[n], ensure_ascii=False) + "\n" for n in sorted(latest)
    )
    _atomic_write_text(results_path, text)



def ensure_live_artifact(
    session: requests.Session,
    row: dict[str, Any],
    live_dir: Path,
    *,
    timeout: int,
    retries: int,
    verbose: bool,
    give_up_after: float,
    min_chars: int,
) -> Optional[Path]:
    existing = find_valid_live_artifact(live_dir, row, min_chars)
    if existing is not None:
        return existing
    progress(f"    LIVE missing/invalid #{row['excel_row']}; fetching {row['url']}", enabled=True)
    try:
        r = request_with_retry(
            session, row["url"], timeout=timeout, max_tries=retries,
            label=f"live #{row['excel_row']}", verbose=verbose,
            give_up_after=give_up_after,
        )
        soup = BeautifulSoup(r.text, "lxml")
        embedded = canonical_article_url(extract_canonical_url_from_html(soup, fallback=r.url or row["url"]))
        if embedded != canonical_article_url(row["url"]):
            raise ValueError(f"live article identity mismatch: {embedded or r.url}")
        if not has_target_attribution_correction(soup):
            raise ValueError("live page does not contain the target attribution correction")
        ex = extract_article(r.text, base_url=row["url"], title=row["title"])
        if not extraction_is_usable(ex, min_chars):
            raise ValueError(f"live extraction unusable: {ex.chars} chars / {len(ex.blocks)} blocks")
        target = canonical_live_target(live_dir, row)
        _atomic_write_text(target, r.text)
        quarantine_conflicting_row_files(live_dir, row, target, ".html", kind="live")
        return target
    except Exception as e:
        progress(f"    LIVE failed #{row['excel_row']}: {e}", enabled=True)
        return None



def _record_from_local_html(
    row: dict[str, Any],
    live_path: Path,
    wayback_path: Path,
    archive_meta: dict[str, Any],
    min_chars: int,
    archive_cutoff: str,
) -> dict[str, Any]:
    live_html = live_path.read_text(encoding="utf-8")
    old_html = wayback_path.read_text(encoding="utf-8")
    current_ex = extract_article(live_html, base_url=row["url"], title=row["title"])
    old_base = archive_meta.get("archive_original_url") or row["url"]
    old_ex = extract_article(old_html, base_url=old_base, title=row["title"])
    base = {
        "title": row["title"],
        "date": row.get("date", ""),
        "excel_row": row["excel_row"],
        "current_url": row["url"],
        "archive_timestamp": archive_meta.get("archive_timestamp", ""),
        "archive_url": archive_meta.get("archive_url", ""),
        "archive_original_url": old_base,
        "archive_cutoff": archive_cutoff,
        "live_sha256": sha256_file(live_path),
        "wayback_sha256": sha256_file(wayback_path),
        "diff_schema": DIFF_SCHEMA_VERSION,
    }
    if not extraction_is_usable(current_ex, min_chars):
        return {
            **base,
            "status": "current_extraction_failed",
            "error": f"Only {current_ex.chars} chars / {len(current_ex.blocks)} current blocks extracted.",
            "current_extraction": ex_to_dict(current_ex),
        }
    if not extraction_is_usable(old_ex, min_chars):
        return {
            **base,
            "status": "archive_extraction_failed",
            "error": f"Only {old_ex.chars} chars / {len(old_ex.blocks)} archived blocks extracted.",
            "current_extraction": ex_to_dict(current_ex),
            "old_extraction": ex_to_dict(old_ex),
        }
    return {
        **base,
        "status": "ok",
        "error": "",
        "old_extraction": ex_to_dict(old_ex),
        "current_extraction": ex_to_dict(current_ex),
        "diff": compute_diff(old_ex.blocks, current_ex.blocks),
        "archive_attempts": archive_meta.get("archive_attempts", []),
    }



def fetch_missing_wayback(
    session: requests.Session,
    row: dict[str, Any],
    wayback_dir: Path,
    previous: Optional[dict[str, Any]],
    args: argparse.Namespace,
) -> tuple[Optional[Path], Optional[dict[str, Any]]]:
    """Return a validated Wayback artifact, fetching it when local provenance is insufficient."""
    row_num = int(row["excel_row"])
    existing, existing_meta = find_valid_wayback_artifact(
        wayback_dir, row, previous, args.archive_cutoff, args.min_article_chars
    )
    if existing is not None and existing_meta is not None:
        return existing, {**(previous or {}), **existing_meta, "status": "archive_ready", "error": ""}

    previous = previous or {}
    ts = str(previous.get("archive_timestamp", ""))
    original = str(previous.get("archive_original_url") or row["url"])
    if ts and ts <= args.archive_cutoff and canonical_article_url(original) == canonical_article_url(row["url"]):
        replay = wayback_replay_url(ts, original, raw=True)
        progress(f"    WAYBACK missing/invalid #{row_num}; refetching known snapshot {ts}", enabled=True)
        try:
            r = request_with_retry(
                session, replay, timeout=args.timeout, max_tries=args.retries,
                label=f"Wayback exact #{row_num}", verbose=not args.quiet,
                give_up_after=args.give_up_minutes * 60,
            )
            actual_ts, actual_original = resolve_wayback_response_provenance(r, ts, original)
            ex = extract_article(r.text, base_url=actual_original, title=row["title"])
            if wayback_response_is_expected(
                r.text, row["url"], actual_original, actual_ts,
                args.archive_cutoff, ex, args.min_article_chars,
            ):
                target, meta = write_wayback_artifact(
                    wayback_dir, row, r.text, actual_ts, actual_original,
                    f"https://web.archive.org/web/{actual_ts}/{actual_original}",
                    args.archive_cutoff,
                )
                updated = {
                    **previous, **meta,
                    "title": row["title"], "date": row.get("date", ""),
                    "excel_row": row_num, "current_url": row["url"],
                    "status": "archive_ready", "error": "",
                }
                return target, updated
        except Exception as e:
            progress(f"    exact Wayback refetch failed #{row_num}: {e}", enabled=True)

    progress(f"    WAYBACK missing/invalid #{row_num}; searching IA", enabled=True)
    archive, attempts = fetch_earliest_usable_archive(
        session=session,
        url=row["url"],
        title=row["title"],
        cutoff=args.archive_cutoff,
        min_chars=args.min_article_chars,
        max_snapshots_to_try=args.max_snapshots_to_try,
        timeout=args.timeout,
        retries=args.retries,
        verbose=not args.quiet,
        give_up_after=args.give_up_minutes * 60,
    )
    if archive is None:
        return None, {
            **previous,
            "title": row["title"], "date": row.get("date", ""),
            "excel_row": row_num, "current_url": row["url"],
            "status": "archive_fetch_failed",
            "archive_attempts": attempts,
            "error": "Wayback artifact still missing; retry on the next cycle.",
        }

    target, meta = write_wayback_artifact(
        wayback_dir, row, archive["html"], archive["timestamp"], archive["original"],
        archive["archive_url"], args.archive_cutoff,
    )
    meta["archive_attempts"] = attempts
    _atomic_write_json(wayback_meta_path(target), meta)
    updated = {
        **previous, **meta,
        "title": row["title"], "date": row.get("date", ""),
        "excel_row": row_num, "current_url": row["url"],
        "status": "archive_ready", "error": "",
    }
    return target, updated


def all_expected_artifacts(rows: list[dict[str, Any]], directory: Path, suffix: str) -> list[Path]:
    files: list[Path] = []
    for row in rows:
        p = find_row_file(directory, int(row["excel_row"]), suffix)
        if p is None:
            return []
        files.append(p)
    return files


def zip_selected_files(files: list[Path], base_dir: Path, zip_path: Path) -> Path:
    if zip_path.exists():
        zip_path.unlink()
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        for p in files:
            zf.write(p, arcname=p.relative_to(base_dir))
    progress(f"[PACKAGING] wrote complete {zip_path.name} ({len(files)} files)", enabled=True)
    return zip_path


def remove_stale_zips(paths: list[Path]) -> None:
    for p in paths:
        if p.exists():
            p.unlink()
            progress(f"[PACKAGING] removed stale/incomplete {p.name}", enabled=True)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", type=Path, default=Path("nymag_wayback_diff_output"), help="Output directory")
    ap.add_argument("--archive-cutoff", default=DEFAULT_CUTOFF,
                    help="Latest Wayback timestamp allowed (default: 20260813235959)")
    ap.add_argument("--min-article-chars", type=int, default=500,
                    help="Minimum extracted prose chars for a usable page (default: 500)")
    ap.add_argument("--max-snapshots-to-try", type=int, default=12,
                    help="Try this many earliest distinct captures until one extracts cleanly (default: 12)")
    ap.add_argument("--timeout", type=int, default=45,
                    help="Per-request network timeout in seconds (default: 45)")
    ap.add_argument("--retries", type=int, default=2,
                    help="Attempts for ordinary HTTP errors (default: 2)")
    ap.add_argument("--give-up-minutes", type=float, default=0.75,
                    help="Retry window for one transiently failing request before moving to the next row")
    ap.add_argument("--cycle-wait", type=float, default=60.0,
                    help="Seconds to wait before circling over still-missing artifacts after a zero-progress pass")
    ap.add_argument("--quiet", action="store_true", help="Suppress detailed per-request logging")
    ap.add_argument("--sleep", type=float, default=0.35, help="Pause between rows")
    args = ap.parse_args()

    args.out.mkdir(parents=True, exist_ok=True)
    diffs_dir = args.out / "diffs"
    live_dir = args.out / "raw_html" / "live"
    wayback_dir = args.out / "raw_html" / "wayback"
    diffs_dir.mkdir(parents=True, exist_ok=True)
    live_dir.mkdir(parents=True, exist_ok=True)
    wayback_dir.mkdir(parents=True, exist_ok=True)

    results_path = args.out / "results.jsonl"
    summary_path = args.out / "summary.csv"
    failures_path = args.out / "failures.csv"
    log_path = args.out / "run_log.json"
    corpus_path = args.out / "corpus.json"

    zip_paths = [
        args.out / f"{args.out.name}_live_html.zip",
        args.out / f"{args.out.name}_wayback_html.zip",
        args.out / f"{args.out.name}_diffs.zip",
    ]
    remove_stale_zips(zip_paths)

    session = requests.Session()
    session.headers.update({
        "User-Agent": USER_AGENT,
        "Accept": "text/html,application/xhtml+xml,application/json;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Cache-Control": "no-cache",
    })

    rows, missing_url_rows = reconstruct_corpus_from_existing_outputs(
        args.out, results_path, summary_path, log_path, corpus_path,
        live_dir, wayback_dir, diffs_dir,
    )

    if not missing_url_rows and len(rows) == EXPECTED_CORRECTION_COUNT:
        save_corpus_manifest(corpus_path, rows)
        progress(
            f"[CORPUS] Reconstructed all {EXPECTED_CORRECTION_COUNT} row->URL mappings from stable metadata. "
            "No correction scan needed.", enabled=True,
        )
    else:
        progress(
            f"[CORPUS] URL missing or contradictory for row(s) {missing_url_rows}. "
            "Running NYMag discovery to recover a complete corpus.",
            enabled=True,
        )
        archive_candidates, archive_problems = crawl_barkan_author_archive(
            session, timeout=args.timeout, retries=args.retries,
            verbose=not args.quiet, give_up_after=args.give_up_minutes * 60,
        )
        discovered, scan_problems = discover_corrected_articles(
            session, archive_candidates, timeout=args.timeout, retries=args.retries,
            verbose=not args.quiet, live_dir=live_dir, min_chars=args.min_article_chars,
            give_up_after=args.give_up_minutes * 60,
        )
        if archive_problems or scan_problems or len(discovered) != EXPECTED_CORRECTION_COUNT:
            problems = archive_problems + scan_problems + [{
                "reason": "corpus URL recovery incomplete",
                "error": f"Need 67 URLs; discovery produced {len(discovered)} with "
                         f"{len(archive_problems) + len(scan_problems)} unresolved fetch problem(s).",
            }]
            fields = sorted({k for r in problems for k in r}) if problems else ["reason"]
            write_csv(failures_path, problems, fields)
            print(f"\nCannot continue until every row has a URL. See {failures_path}")
            return 2
        rows = sorted(discovered, key=lambda r: int(r["excel_row"]))
        save_corpus_manifest(corpus_path, rows)
        progress(f"[CORPUS] Saved recovered 1..67 address book to {corpus_path.name}.", enabled=True)

    rows = [_row_metadata(r) for r in sorted(rows, key=lambda r: int(r["excel_row"]))]
    if results_path.exists():
        compact_results_jsonl(results_path)

    pass_num = 0
    try:
        while True:
            pass_num += 1
            latest_by_row = latest_records_by_row(results_path)
            states: dict[int, tuple[Optional[Path], Optional[Path], Optional[dict[str, Any]], Optional[Path]]] = {}
            missing_live: list[int] = []
            missing_wayback: list[int] = []
            missing_diffs: list[int] = []

            for row in rows:
                n = int(row["excel_row"])
                previous = latest_by_row.get(n)
                live_path = find_valid_live_artifact(live_dir, row, args.min_article_chars)
                wb_path, wb_meta = find_valid_wayback_artifact(
                    wayback_dir, row, previous, args.archive_cutoff, args.min_article_chars
                )
                diff_path = find_valid_diff_artifact(
                    diffs_dir, row, live_path, wb_path, wb_meta, args.archive_cutoff
                )
                states[n] = (live_path, wb_path, wb_meta, diff_path)
                if live_path is None:
                    missing_live.append(n)
                if wb_path is None:
                    missing_wayback.append(n)
                if diff_path is None:
                    missing_diffs.append(n)

            if not missing_live and not missing_wayback and not missing_diffs:
                break

            progress(
                f"\n[PASS {pass_num}] missing/invalid live={missing_live or 'none'} | "
                f"Wayback={missing_wayback or 'none'} | diffs={missing_diffs or 'none'}",
                enabled=True,
            )
            progress_this_pass = 0

            for row in rows:
                n = int(row["excel_row"])
                live_path, wb_path, wb_meta, diff_path = states[n]
                previous = latest_by_row.get(n)

                if live_path is None:
                    live_path = ensure_live_artifact(
                        session, row, live_dir,
                        timeout=args.timeout, retries=args.retries,
                        verbose=not args.quiet,
                        give_up_after=args.give_up_minutes * 60,
                        min_chars=args.min_article_chars,
                    )
                    if live_path is not None:
                        progress_this_pass += 1

                if wb_path is None or wb_meta is None:
                    wb_path, previous = fetch_missing_wayback(
                        session, row, wayback_dir, previous, args,
                    )
                    if previous is not None:
                        append_result_record(results_path, previous)
                        latest_by_row[n] = previous
                    if wb_path is not None:
                        wb_meta = load_json(wayback_meta_path(wb_path))
                        progress_this_pass += 1

                if live_path is not None and wb_path is not None and wb_meta:
                    diff_path = find_valid_diff_artifact(
                        diffs_dir, row, live_path, wb_path, wb_meta, args.archive_cutoff
                    )
                    if diff_path is None:
                        try:
                            rec = _record_from_local_html(
                                row, live_path, wb_path, wb_meta,
                                args.min_article_chars, args.archive_cutoff,
                            )
                        except Exception as e:
                            rec = {
                                **(previous or {}),
                                "title": row["title"], "date": row.get("date", ""),
                                "excel_row": n, "current_url": row["url"],
                                "status": "local_diff_failed", "error": f"{type(e).__name__}: {e}",
                            }
                        append_result_record(results_path, rec)
                        latest_by_row[n] = rec
                        if rec.get("status") == "ok":
                            target = canonical_diff_target(diffs_dir, row)
                            _atomic_write_text(target, render_diff_markdown(rec))
                            quarantine_conflicting_row_files(diffs_dir, row, target, ".md", kind="diff")
                            progress(f"    DIFF built locally #{n}", enabled=True)
                            progress_this_pass += 1
                        else:
                            progress(
                                f"    DIFF not built #{n}: {rec.get('error', rec.get('status'))}",
                                enabled=True,
                            )

                time.sleep(max(0.0, args.sleep))

            compact_results_jsonl(results_path)
            if progress_this_pass:
                progress(
                    f"[PASS {pass_num}] added/repaired {progress_this_pass} validated artifact(s); circling back to row 1.",
                    enabled=True,
                )
                continue

            progress(
                f"[PASS {pass_num}] no validated artifacts were added. IA/NYMag may be unavailable; "
                f"waiting {args.cycle_wait:g}s before retrying. Ctrl-C stops safely.",
                enabled=True,
            )
            time.sleep(max(0.0, args.cycle_wait))
    except KeyboardInterrupt:
        print("\nStopped by user. Validated files are intact; rerun the same command to continue.", flush=True)

    latest_by_row = latest_records_by_row(results_path)
    summary_rows: list[dict[str, Any]] = []
    live_files: list[Path] = []
    wb_files: list[Path] = []
    diff_files: list[Path] = []

    for row in rows:
        n = int(row["excel_row"])
        rec = latest_by_row.get(n, {})
        live_path = find_valid_live_artifact(live_dir, row, args.min_article_chars)
        wb_path, wb_meta = find_valid_wayback_artifact(
            wayback_dir, row, rec, args.archive_cutoff, args.min_article_chars
        )
        diff_path = find_valid_diff_artifact(
            diffs_dir, row, live_path, wb_path, wb_meta, args.archive_cutoff
        )
        gaps: list[str] = []
        if live_path is None:
            gaps.append("live_html")
        else:
            live_files.append(live_path)
        if wb_path is None or wb_meta is None:
            gaps.append("wayback_html")
        else:
            wb_files.append(wb_path)
        if diff_path is None:
            gaps.append("diff_md")
        else:
            diff_files.append(diff_path)

        archive_source = wb_meta or rec
        summary_rows.append({
            "excel_row": n,
            "date": row.get("date", ""),
            "title": row["title"],
            "current_url": row["url"],
            "status": "ok" if not gaps else rec.get("status", "incomplete"),
            "artifact_gaps": ";".join(gaps),
            "archive_timestamp": archive_source.get("archive_timestamp", ""),
            "archive_url": archive_source.get("archive_url", ""),
            "error": "" if not gaps else rec.get("error", ""),
        })

    fields = [
        "excel_row", "date", "title", "current_url", "status", "artifact_gaps",
        "archive_timestamp", "archive_url", "error",
    ]
    write_csv(summary_path, summary_rows, fields)
    failures = [r for r in summary_rows if r["artifact_gaps"]]
    write_csv(failures_path, failures, fields if failures else ["reason"])

    if len(live_files) == EXPECTED_CORRECTION_COUNT:
        zip_selected_files(live_files, live_dir, zip_paths[0])
    if len(wb_files) == EXPECTED_CORRECTION_COUNT:
        zip_selected_files(wb_files, wayback_dir, zip_paths[1])
    if len(diff_files) == EXPECTED_CORRECTION_COUNT:
        zip_selected_files(diff_files, diffs_dir, zip_paths[2])

    incomplete = [r for r in summary_rows if r["artifact_gaps"]]
    print("\nDone." if not incomplete else "\nStopped with incomplete artifacts.")
    print(f"Corpus URL map:   {corpus_path}")
    print(f"Machine-readable: {results_path}")
    print(f"Summary:          {summary_path}")
    print(f"Human diffs:      {diffs_dir}")
    print(f"Live HTML:        {live_dir}")
    print(f"Wayback HTML:     {wayback_dir}")
    if incomplete:
        print("Still missing/invalid: " + ", ".join(
            f"#{r['excel_row']}({r['artifact_gaps']})" for r in incomplete
        ))
        return 3
    print("All 67 live HTML, 67 Wayback HTML, and 67 diffs are validated; complete ZIPs were created.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
