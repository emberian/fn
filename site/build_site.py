#!/usr/bin/env python3
"""Build fn's static website from the plain docs (Python 3.10+, stdlib only).

The site renders the repository's own markdown -- README.md, the guides under
docs/, CONTRIBUTING.md, the swarmguide -- with one shared layout.  Nothing is
copied: edit the doc and the page follows.  The landing page takes its copy
from README.md's sections; site/pages/ holds the few pages that exist only on
the site, and site/landing-paths.md the audience cards on the landing page.

    python3 site/build_site.py                 # build into build/site/
    python3 site/build_site.py --check         # build, then check every link
    python3 site/build_site.py --out DIR --base-path /

A link to a rendered doc points at its page (anchors included); a link to any
other file in the repository points at that file on GitHub; a link to a path
that does not exist fails the build by name.  --check also opens every
generated page and confirms each internal href/src resolves to a file and,
when it carries a #fragment, to an id on that page.
"""

from __future__ import annotations

import argparse
import html
import os
import posixpath
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlsplit, unquote

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "site"
REPO_URL = "https://github.com/emberian/fn"
BRANCH = "dev"
TITLE = "fuckin' news / formal news /᠁"

# Source (repo-relative) -> output path (site-relative).  Order is the order of
# the "all pages" list in the footer.
PAGES: dict[str, str] = {
    "README.md": "index.html",
    "docs/README.md": "docs/index.html",
    "docs/install.md": "docs/install.html",
    "docs/operator.md": "docs/operator.html",
    "docs/peering-with-a-friend.md": "docs/peering-with-a-friend.html",
    "docs/web.md": "docs/web.html",
    "docs/human-web-client.md": "docs/human-web-client.html",
    "docs/agents.md": "docs/agents.html",
    "docs/glossary.md": "docs/glossary.html",
    "site/pages/proofs.md": "proofs.html",
    "docs/proofs.md": "docs/proofs.html",
    "docs/architecture.md": "docs/architecture.html",
    "site/pages/how-its-built.md": "how-its-built.html",
    "swarmguide/README.md": "swarmguide/index.html",
    "swarmguide/case-notes.md": "swarmguide/case-notes.html",
    "CONTRIBUTING.md": "contributing.html",
}

# The header navigation: (label, output path).
NAV = [
    ("Guides", "docs/index.html"),
    ("Run a node", "docs/install.html"),
    ("Peer", "docs/peering-with-a-friend.html"),
    ("Read & post", "docs/web.html"),
    ("Agents", "docs/agents.html"),
    ("Proofs", "proofs.html"),
    ("How it's built", "how-its-built.html"),
]


class BuildError(Exception):
    pass


# ---------------------------------------------------------------------------
# Markdown (the subset the docs use: ATX headings, paragraphs, nested lists,
# fenced code, tables, block quotes, rules, inline code/links/emphasis).

def slugify(text: str) -> str:
    """GitHub's heading anchor: lowercase, punctuation dropped, spaces to -."""
    return re.sub(r"[^\w\- ]", "", text.lower()).replace(" ", "-")


def plain(markdown: str) -> str:
    """Inline markdown reduced to its visible text."""
    text = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", markdown)
    text = re.sub(r"`+([^`]*)`+", r"\1", text)
    return re.sub(r"(\*\*|__|\*|_)(.+?)\1", r"\2", text)


@dataclass
class Doc:
    source: str                 # repo-relative source path
    out: str                    # site-relative output path
    ids: set[str] = field(default_factory=set)
    headings: list[tuple[int, str, str]] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)


class Renderer:
    def __init__(self, doc: Doc):
        self.doc = doc

    # -- links ---------------------------------------------------------------
    def href(self, target: str) -> str:
        return resolve_link(target, self.doc, self.doc.errors)

    # -- inline --------------------------------------------------------------
    def inline(self, text: str) -> str:
        stash: list[str] = []

        def keep(fragment: str) -> str:
            stash.append(fragment)
            return f"\x00{len(stash) - 1}\x00"

        def code(m: re.Match) -> str:
            body = m.group(2).replace("\n", " ")
            return keep("<code>%s</code>" % html.escape(body.strip(" ") or body, quote=False))

        text = re.sub(r"(`+)([\s\S]+?)\1", code, text)
        text = re.sub(r"\\([\\`*_{}\[\]()#+\-.!|<>])", lambda m: keep(html.escape(m.group(1))), text)
        text = re.sub(r"<(https?://[^>\s]+)>",
                      lambda m: keep('<a href="%s">%s</a>' % (html.escape(m.group(1)),
                                                              html.escape(m.group(1)))), text)
        text = html.escape(text, quote=False)

        def image(m: re.Match) -> str:
            return keep('<img src="%s" alt="%s">' % (html.escape(self.href(html.unescape(m.group(2)))),
                                                     m.group(1)))

        def link(m: re.Match) -> str:
            label, target = m.group(1), html.unescape(m.group(2)).strip()
            url = self.href(target)
            external = url.startswith(("http://", "https://"))
            attrs = ' class="ext"' if external and REPO_URL not in url else ""
            return keep('<a href="%s"%s>%s</a>' % (html.escape(url), attrs, self.emphasis(label)))

        text = re.sub(r"!\[([^\]]*)\]\(([^)\s]+)\)", image, text)
        text = re.sub(r"\[((?:[^\[\]]|\[[^\]]*\])+)\]\(([^)\s]+)(?:\s+&quot;[^)]*&quot;)?\)", link, text)
        text = self.emphasis(text)
        text = re.sub(r"(?: {2,}|\\)\n", "<br>\n", text)
        text = text.replace(" -- ", " – ")
        while "\x00" in text:
            text = re.sub(r"\x00(\d+)\x00", lambda m: stash[int(m.group(1))], text)
        return text

    @staticmethod
    def emphasis(text: str) -> str:
        text = re.sub(r"\*\*(?=\S)([\s\S]+?)(?<=\S)\*\*", r"<strong>\1</strong>", text)
        text = re.sub(r"(?<![\w_])__(?=\S)([\s\S]+?)(?<=\S)__(?![\w_])", r"<strong>\1</strong>", text)
        text = re.sub(r"(?<![\w*])\*(?=[^\s*])([\s\S]+?)(?<=[^\s*])\*(?![\w*])", r"<em>\1</em>", text)
        text = re.sub(r"(?<![\w_])_(?=[^\s_])([\s\S]+?)(?<=[^\s_])_(?![\w_])", r"<em>\1</em>", text)
        return text

    # -- blocks --------------------------------------------------------------
    LIST_RE = re.compile(r"^( {0,3})([-*+]|\d{1,9}[.)])( +|$)(.*)$")
    FENCE_RE = re.compile(r"^( {0,3})(`{3,}|~{3,})\s*([^`\s]*)")
    HEADING_RE = re.compile(r"^ {0,3}(#{1,6})\s+(.*?)(?:\s+#+)?\s*$")
    RULE_RE = re.compile(r"^ {0,3}([-*_])(\s*\1){2,}\s*$")

    def heading(self, level: int, raw: str) -> str:
        slug = base = slugify(plain(raw))
        n = 0
        while slug in self.doc.ids:
            n += 1
            slug = f"{base}-{n}"
        self.doc.ids.add(slug)
        self.doc.headings.append((level, slug, plain(raw)))
        anchor = '' if level == 1 else ' <a class="anchor" href="#%s" aria-label="Link to this section">#</a>' % slug
        return '<h%d id="%s">%s%s</h%d>\n' % (level, slug, self.inline(raw), anchor, level)

    def starts_block(self, line: str) -> bool:
        return bool(self.FENCE_RE.match(line) or self.HEADING_RE.match(line)
                    or line.lstrip().startswith(">") or self.RULE_RE.match(line)
                    or re.match(r"^ {0,3}([-*+]|1[.)]) +\S", line))

    def blocks(self, lines: list[str], tight: bool = False) -> str:
        out: list[str] = []
        i = 0
        while i < len(lines):
            line = lines[i]
            if not line.strip():
                i += 1
                continue
            m = self.FENCE_RE.match(line)
            if m:
                indent, fence, lang = len(m.group(1)), m.group(2), m.group(3)
                body: list[str] = []
                i += 1
                while i < len(lines) and not re.match(r"^ {0,3}%s%s*\s*$" % (re.escape(fence[0]) * len(fence), re.escape(fence[0])), lines[i]):
                    body.append(lines[i][indent:] if lines[i][:indent].strip() == "" else lines[i])
                    i += 1
                i += 1
                body = [re.sub(r"\s*# docs-check:.*$", "", b) for b in body]
                cls = ' class="language-%s"' % html.escape(lang) if lang else ""
                out.append("<pre><code%s>%s</code></pre>\n" % (cls, html.escape("\n".join(body), quote=False)))
                continue
            m = self.HEADING_RE.match(line)
            if m:
                out.append(self.heading(len(m.group(1)), m.group(2)))
                i += 1
                continue
            if self.RULE_RE.match(line):
                out.append("<hr>\n")
                i += 1
                continue
            if line.lstrip().startswith(">"):
                quoted: list[str] = []
                while i < len(lines) and lines[i].strip() and (lines[i].lstrip().startswith(">") or quoted):
                    quoted.append(re.sub(r"^ {0,3}> ?", "", lines[i]))
                    i += 1
                out.append("<blockquote>\n%s</blockquote>\n" % self.blocks(quoted))
                continue
            if line.lstrip().startswith("|") and i + 1 < len(lines) and re.match(r"^\s*\|?\s*:?-+:?\s*(\|\s*:?-+:?\s*)*\|?\s*$", lines[i + 1]):
                rows = []
                while i < len(lines) and lines[i].strip().startswith("|"):
                    rows.append(lines[i])
                    i += 1
                out.append(self.table(rows))
                continue
            m = self.LIST_RE.match(line)
            if m:
                i = self.list_block(lines, i, out)
                continue
            para = [line.strip()]
            i += 1
            while i < len(lines) and lines[i].strip() and not self.starts_block(lines[i]) \
                    and not (lines[i].lstrip().startswith("|") and False):
                para.append(lines[i].strip() if not lines[i].endswith("  ") else lines[i].lstrip())
                i += 1
            body = self.inline("\n".join(para))
            out.append(body + "\n" if tight else "<p>%s</p>\n" % body)
        return "".join(out)

    def table(self, rows: list[str]) -> str:
        def cells(row: str) -> list[str]:
            row = row.strip()
            if row.startswith("|"):
                row = row[1:]
            if row.endswith("|") and not row.endswith("\\|"):
                row = row[:-1]
            parts, cur, code = [], "", False
            for ch_i, ch in enumerate(row):
                if ch == "`":
                    code = not code
                if ch == "|" and not code and (ch_i == 0 or row[ch_i - 1] != "\\"):
                    parts.append(cur)
                    cur = ""
                else:
                    cur += ch
            parts.append(cur)
            return [p.strip().replace("\\|", "|") for p in parts]

        aligns = []
        for spec in cells(rows[1]):
            aligns.append("right" if spec.endswith(":") and not spec.startswith(":")
                          else "center" if spec.startswith(":") and spec.endswith(":") else "")
        def row_html(row: str, tag: str) -> str:
            tds = []
            for n, cell in enumerate(cells(row)):
                style = ' style="text-align:%s"' % aligns[n] if n < len(aligns) and aligns[n] else ""
                tds.append("<%s%s>%s</%s>" % (tag, style, self.inline(cell), tag))
            return "<tr>%s</tr>\n" % "".join(tds)
        head = row_html(rows[0], "th")
        body = "".join(row_html(r, "td") for r in rows[2:])
        return ('<div class="table-wrap"><table>\n<thead>%s</thead>\n<tbody>\n%s</tbody>\n</table></div>\n'
                % (head, body))

    def list_block(self, lines: list[str], i: int, out: list[str]) -> int:
        first = self.LIST_RE.match(lines[i])
        ordered = first.group(2)[0].isdigit()
        items: list[list[str]] = []
        loose = False
        start = int(first.group(2)[:-1]) if ordered else 1
        while i < len(lines):
            m = self.LIST_RE.match(lines[i])
            if not m or m.group(2)[0].isdigit() != ordered:
                break
            content_indent = len(m.group(1)) + len(m.group(2)) + (len(m.group(3)) if m.group(4) else 1)
            if len(m.group(3)) > 4:
                content_indent = len(m.group(1)) + len(m.group(2)) + 1
            item = [" " * 0 + lines[i][content_indent:] if m.group(4) else ""]
            i += 1
            while i < len(lines):
                cur = lines[i]
                if not cur.strip():
                    # a blank line: the item continues only if something indented follows
                    j = i
                    while j < len(lines) and not lines[j].strip():
                        j += 1
                    if j < len(lines) and (len(lines[j]) - len(lines[j].lstrip())) >= content_indent:
                        item.extend([""] * (j - i))
                        i = j
                        continue
                    break
                indent = len(cur) - len(cur.lstrip())
                if indent >= content_indent:
                    item.append(cur[content_indent:])
                elif self.LIST_RE.match(cur) or self.starts_block(cur):
                    break
                elif item and item[-1].strip():
                    item.append(cur.strip())          # lazy continuation
                else:
                    break
                i += 1
            items.append(item)
            # a blank line before the next item makes the list loose
            j = i
            while j < len(lines) and not lines[j].strip():
                j += 1
            nxt = self.LIST_RE.match(lines[j]) if j < len(lines) else None
            if nxt and nxt.group(2)[0].isdigit() == ordered and len(nxt.group(1)) < content_indent:
                if j > i:
                    loose = True
                i = j
            else:
                break
        for item in items:
            text = "\n".join(item).strip("\n")
            if "\n\n" in text and not re.search(r"^\s*```", text, re.M):
                loose = True
        tag = "ol" if ordered else "ul"
        attr = ' start="%d"' % start if ordered and start != 1 else ""
        out.append("<%s%s>\n" % (tag, attr))
        for item in items:
            out.append("<li>%s</li>\n" % self.blocks(item, tight=not loose).rstrip("\n"))
        out.append("</%s>\n" % tag)
        return i

    def render(self, text: str) -> str:
        text = re.sub(r"(?s)<!--.*?-->\n?", "", text)
        return self.blocks(text.expandtabs(4).split("\n"))


# ---------------------------------------------------------------------------
# Links

def rel_url(from_out: str, to_out: str) -> str:
    """A relative URL from one output page to another (index.html kept
    explicit so the site also works from a file:// checkout)."""
    return posixpath.relpath(to_out, posixpath.dirname(from_out) or ".")


def resolve_link(target: str, doc: Doc, errors: list[str]) -> str:
    parts = urlsplit(target)
    if parts.scheme or target.startswith("//") or target.startswith("mailto:"):
        return target
    if not parts.path:                      # "#section" on this page
        return target
    src_dir = posixpath.dirname(doc.source)
    repo_path = posixpath.normpath(posixpath.join(src_dir, unquote(parts.path)))
    if repo_path.startswith("../") or repo_path == "..":
        errors.append(f"{doc.source}: link leaves the repository: {target}")
        return target
    fragment = "#" + parts.fragment if parts.fragment else ""
    if repo_path in PAGES:
        return rel_url(doc.out, PAGES[repo_path]) + fragment
    full = ROOT / repo_path
    if not full.exists():
        errors.append(f"{doc.source}: link to a missing file: {target}")
        return target
    kind = "tree" if full.is_dir() else "blob"
    return f"{REPO_URL}/{kind}/{BRANCH}/{repo_path}{fragment}"


# ---------------------------------------------------------------------------
# Layout

def git(*args: str) -> str:
    try:
        return subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True,
                              text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def layout(doc: Doc, title: str, body: str, *, description: str, landing: bool = False,
           toc: str = "", revision: str = "", base: str = "") -> str:
    root = rel_url(doc.out, "index.html")
    asset = lambda name: rel_url(doc.out, name)
    nav = "".join('<a href="%s"%s>%s</a>' % (
        html.escape(rel_url(doc.out, out)),
        ' aria-current="page"' if out == doc.out else "", html.escape(label)) for label, out in NAV)
    source_link = f"{REPO_URL}/blob/{BRANCH}/{doc.source}"
    footer_source = 'This page is <a href="%s">%s</a>%s, rendered.' % (
        html.escape(source_link), html.escape(doc.source),
        (" at " + html.escape(revision[:9])) if revision else "")
    page_title = TITLE if landing else f"{title} · fn"
    main_class = "landing" if landing else ("doc has-toc" if toc else "doc")
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">{('<base href="%s">' % html.escape(base)) if base else ""}
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(page_title)}</title>
<meta name="description" content="{html.escape(description)}">
<meta name="color-scheme" content="light dark">
<link rel="icon" href="{asset('favicon.svg')}" type="image/svg+xml">
<link rel="stylesheet" href="{asset('style.css')}">
</head>
<body>
<a class="skip" href="#content">Skip to the text</a>
<header class="site-header">
  <div class="bar">
    <a class="brand" href="{root}" aria-label="fn home"><span class="brand-mark">fn</span><span class="brand-dots" aria-hidden="true">/&#x1801;</span></a>
    <nav aria-label="Site">{nav}<a class="gh" href="{REPO_URL}">GitHub</a></nav>
  </div>
</header>
<main id="content" class="{main_class}">
{toc}{body}
</main>
<footer class="site-footer">
  <div class="bar">
    <p>fn is free software under the <a href="{REPO_URL}/blob/{BRANCH}/LICENSE">AGPL-3.0</a>. {footer_source}
    No cookies, no trackers, no scripts.</p>
    <p><a href="{root}">Home</a> &middot; <a href="{rel_url(doc.out, 'docs/index.html')}">All guides</a> &middot; <a href="{rel_url(doc.out, 'contributing.html')}">Contributing</a> &middot; <a href="{html.escape(source_link)}">Source of this page</a> &middot; <a href="{REPO_URL}/issues">Issues</a></p>
  </div>
</footer>
</body>
</html>
"""


def toc_html(doc: Doc) -> str:
    items = [(slug, text) for level, slug, text in doc.headings if level == 2]
    if len(items) < 3:
        return ""
    links = "".join('<li><a href="#%s">%s</a></li>' % (slug, html.escape(text)) for slug, text in items)
    return '<ol>%s</ol>' % links


def with_toc(body: str, toc: str) -> tuple[str, str]:
    """The sidebar contents (wide screens) and the body with a folded copy
    after its title (narrow screens; CSS shows one or the other)."""
    if not toc:
        return "", body
    side = '<aside class="toc" aria-label="On this page"><p class="toc-title">On this page</p>%s</aside>\n' % toc
    inline = '<details class="toc-inline"><summary>On this page</summary>%s</details>\n' % toc
    body = re.sub(r"(</h1>\n)", lambda m: m.group(1) + inline, body, count=1)
    return side, body


def first_paragraph_text(markdown: str) -> str:
    for block in re.split(r"\n\s*\n", re.sub(r"(?ms)^```.*?^```", "", markdown)):
        block = block.strip()
        if block and not block.startswith(("#", "|", "-", "*", ">", "<!--")):
            return re.sub(r"\s+", " ", plain(block))[:200]
    return ""


# ---------------------------------------------------------------------------
# Landing page: README.md's own sections, laid out.

def split_sections(markdown: str) -> tuple[str, str, list[tuple[str, str]]]:
    """(H1 text, text before the first H2, [(H2 title, body)])."""
    text = re.sub(r"(?s)<!--.*?-->\n?", "", markdown)
    m = re.match(r"\s*# (.+)\n", text)
    if not m:
        raise BuildError("README.md: no H1 title on the first line")
    h1, rest = m.group(1).strip(), text[m.end():]
    chunks = re.split(r"(?m)^## (.+)$", rest)
    intro, sections = chunks[0], []
    for n in range(1, len(chunks), 2):
        sections.append((chunks[n].strip(), chunks[n + 1]))
    return h1, intro, sections


def list_items(markdown: str) -> tuple[list[str], str, str]:
    """A section's top-level bullet items (joined lines), the text before
    them and the text after them."""
    lines = markdown.strip("\n").split("\n")
    before, items, after = [], [], []
    state = "before"
    for line in lines:
        if state in ("before", "items") and re.match(r"^- ", line):
            state = "items"
            items.append(line[2:].strip())
        elif state == "items" and line.startswith("  ") and line.strip():
            items[-1] += " " + line.strip()
        elif state == "items" and not line.strip():
            continue
        elif state == "items":
            state = "after"
            after.append(line)
        else:
            (before if state == "before" else after).append(line)
    return items, "\n".join(before), "\n".join(after)


def card(r: Renderer, item: str, cls: str = "card") -> str:
    """A bullet as a card.  "**Label:** text" or "**A sentence.** text" makes
    the bold words the title; "**Words**, more text" keeps the item whole as
    the text under a title of the bold words."""
    m = re.match(r"\*\*(.+?)\*\*\s*(.*)$", item, re.S)
    if not m:
        return '<div class="%s"><p>%s</p></div>\n' % (cls, r.inline(item))
    head, body = m.group(1), m.group(2)
    if head.endswith((":", ".")):
        head = head[:-1]
    else:
        body = head + body
    return '<div class="%s"><h3>%s</h3><p>%s</p></div>\n' % (cls, r.inline(head), r.inline(body))


def build_landing(doc: Doc, revision: str, version: str, released: bool) -> str:
    r = Renderer(doc)
    h1, intro, sections = split_sections((ROOT / doc.source).read_text(encoding="utf-8"))
    if h1 != TITLE:
        raise BuildError(f"README.md's title changed to {h1!r}; update TITLE in site/build_site.py deliberately")
    doc.ids.update({"top", "what-makes-it-odd", "where-things-stand", "where-to-start", "paths", "helping"})
    paras = [p.strip() for p in re.split(r"\n\s*\n", intro.strip()) if p.strip()]
    lead = r.inline(paras[0]) if paras else ""
    more = "".join("<p>%s</p>" % r.inline(p) for p in paras[1:])
    link = lambda path: html.escape(rel_url(doc.out, PAGES[path]))
    parts = [f"""<section class="hero" id="top">
  <h1>{html.escape(h1)}</h1>
  <p class="lead">{lead}</p>
  <div class="hero-more">{more}</div>
  <p class="cta">
    <a class="button primary" href="{link('docs/install.md')}">Run a node</a>
    <a class="button" href="{link('docs/peering-with-a-friend.md')}">Peer with a friend</a>
    <a class="button" href="{link('docs/README.md')}">All the guides</a>
  </p>
</section>
"""]
    for title, body in sections:
        slug = slugify(title)
        doc.ids.add(slug)
        if title == "What makes it odd":
            items, before, after = list_items(body)
            cards = "".join(card(r, it) for it in items)
            parts.append(f'<section id="{slug}"><h2>{r.inline(title)}</h2>{r.blocks(before.split(chr(10)))}'
                         f'<div class="cards odd">{cards}</div>'
                         f'<div class="caveat">{r.blocks(after.split(chr(10)))}</div></section>\n')
        elif title == "Where things stand":
            chip = (f"Release {html.escape(version)}" if released
                    else f"Next release: {html.escape(version)} &middot; not cut yet")
            parts.append(f'<section id="{slug}" class="status"><h2>{r.inline(title)}</h2>'
                         f'<p class="chips"><span class="chip warn">Experiment</span>'
                         f'<span class="chip">{chip}</span></p>{r.blocks(body.split(chr(10)))}</section>\n')
        elif title == "Where to start":
            items, before, after = list_items(body)
            cards = "".join(card(r, it, "card start") for it in items)
            parts.append(f'<section id="{slug}"><h2>{r.inline(title)}</h2>{r.blocks(before.split(chr(10)))}'
                         f'<div class="cards">{cards}</div>{r.blocks(after.split(chr(10)))}</section>\n')
            parts.append(paths_section(doc))
        else:
            parts.append(f'<section id="{slug}"><h2>{r.inline(title)}</h2>'
                         f'{r.blocks(body.split(chr(10)))}</section>\n')
    doc.errors.extend(r.doc.errors)
    description = re.sub(r"\s+", " ", plain(paras[0])) if paras else "fn, a news server"
    return layout(doc, h1, "".join(parts), description=description, landing=True, revision=revision)


def paths_section(landing: Doc) -> str:
    """site/landing-paths.md: one card per audience (its links are relative
    to site/, like any markdown file there)."""
    src = "site/landing-paths.md"
    pdoc = Doc(source=src, out=landing.out)
    r = Renderer(pdoc)
    text = re.sub(r"(?s)<!--.*?-->\n?", "", (ROOT / src).read_text(encoding="utf-8"))
    title_m = re.search(r"(?m)^# (.+)$", text)
    items, before, _ = list_items(text[title_m.end():] if title_m else text)
    cards = "".join(card(r, it, "card path") for it in items)
    landing.errors.extend(pdoc.errors)
    title = r.inline(title_m.group(1)) if title_m else "Paths"
    return (f'<section id="paths"><h2>{title}</h2>{r.blocks(before.split(chr(10)))}'
            f'<div class="cards paths">{cards}</div></section>\n')


# ---------------------------------------------------------------------------

def build(out_dir: Path, base_path: str) -> list[str]:
    revision = git("rev-parse", "HEAD")
    version = (ROOT / "VERSION").read_text().strip() if (ROOT / "VERSION").exists() else "?"
    released = bool(git("tag", "-l", f"v{version}", version))
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)
    errors: list[str] = []
    docs: dict[str, Doc] = {}
    for source, out in PAGES.items():
        if not (ROOT / source).exists():
            errors.append(f"site/build_site.py: page source missing: {source}")
            continue
        doc = Doc(source=source, out=out)
        docs[source] = doc
        if source == "README.md":
            page = build_landing(doc, revision, version, released)
        else:
            text = (ROOT / source).read_text(encoding="utf-8")
            r = Renderer(doc)
            body = r.render(text)
            title = next((t for level, _, t in doc.headings if level == 1), source)
            toc, body = with_toc(body, toc_html(doc))
            page = layout(doc, title, '<article class="prose">\n%s</article>' % body,
                          description=first_paragraph_text(text) or title, toc=toc, revision=revision)
        errors.extend(doc.errors)
        target = out_dir / out
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(page, encoding="utf-8")
    for asset in ("style.css", "favicon.svg"):
        shutil.copyfile(SITE / asset, out_dir / asset)
    # GitHub Pages serves 404.html for a missing path at any depth, so its
    # relative links go through <base> (the site's own path on the host).
    (out_dir / "404.html").write_text(
        layout(Doc(source="site/build_site.py", out="404.html"), "Not found",
               '<article class="prose"><h1>Not here</h1><p>That page does not exist. '
               'Try <a href="index.html">the front page</a> or <a href="docs/index.html">the guides</a>.</p></article>',
               description="Not found", revision=revision, base=base_path), encoding="utf-8")
    return errors


class LinkCollector(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links: list[str] = []
        self.ids: set[str] = set()

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if "id" in a and a["id"]:
            self.ids.add(a["id"])
        for key in ("href", "src"):
            if a.get(key):
                self.links.append(a[key])


def check(out_dir: Path) -> list[str]:
    """Every internal href/src in every generated page resolves."""
    pages: dict[Path, LinkCollector] = {}
    for path in sorted(out_dir.rglob("*.html")):
        parser = LinkCollector()
        parser.feed(path.read_text(encoding="utf-8"))
        pages[path.resolve()] = parser
    errors = []
    for path, parser in pages.items():
        rel = path.relative_to(out_dir.resolve())
        if rel.name == "404.html":
            continue
        for link in parser.links:
            parts = urlsplit(link)
            if parts.scheme or link.startswith("//"):
                if parts.scheme in ("http", "https", "mailto"):
                    continue
                errors.append(f"{rel}: unexpected link scheme: {link}")
                continue
            target = (path.parent / unquote(parts.path)).resolve() if parts.path else path
            if target.is_dir():
                target = target / "index.html"
            try:
                target.relative_to(out_dir.resolve())
            except ValueError:
                errors.append(f"{rel}: link leaves the site: {link}")
                continue
            if not target.exists():
                errors.append(f"{rel}: broken link: {link}")
                continue
            if parts.fragment and target.suffix == ".html":
                ids = pages[target].ids
                if unquote(parts.fragment) not in ids:
                    errors.append(f"{rel}: no #{parts.fragment} on {target.relative_to(out_dir.resolve())}: {link}")
    return errors


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", default=str(ROOT / "build" / "site"), help="output directory (default build/site)")
    ap.add_argument("--check", action="store_true", help="after building, check every internal link")
    ap.add_argument("--base-path", default="/fn/",
                    help="the site's path on its host, used only by 404.html (default /fn/, a GitHub project page)")
    args = ap.parse_args(argv)
    out_dir = Path(args.out)
    try:
        errors = build(out_dir, args.base_path)
    except BuildError as exc:
        print(f"site: {exc}", file=sys.stderr)
        return 1
    if args.check:
        errors += check(out_dir)
    for e in errors:
        print(f"site: {e}", file=sys.stderr)
    count = sum(1 for _ in out_dir.rglob("*.html"))
    if errors:
        print(f"site: {len(errors)} problem(s); {count} pages in {out_dir}", file=sys.stderr)
        return 1
    print(f"site: {count} pages in {out_dir}" + (", every internal link resolves" if args.check else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
