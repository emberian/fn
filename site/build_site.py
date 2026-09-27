#!/usr/bin/env python3
"""Build fn's website: a static newsreader over docs/articles (stdlib only).

The guides are Usenet articles (docs/articles/*.txt, read and checked by
tools/docs_articles.py), and the same files are posted to fn.announce and
fn.docs on a node (tools/post_docs.py).  This renders them the way a
newsreader shows a spool:

    index.html               the welcome article in fn.announce (front page)
    groups.html              the group list, with counts
    GROUP/index.html         the thread index (Subject, From, Date, Lines)
    GROUP/STEM.html          one article: headers, body, follow-ups, nav

An article's body is shown verbatim at 72 columns: prose lines, bullets and
indented command blocks keep their line breaks; on a narrow screen prose
reflows and only command blocks scroll.  A repository path in a body links
to that file on GitHub (and must exist), "part N" to that FAQ part, a
Message-ID to its article, a URL to itself.

    python3 site/build_site.py                 # build into build/site/
    python3 site/build_site.py --check         # build, check the articles and every link
    python3 site/build_site.py --out DIR --base-path /
"""

from __future__ import annotations

import argparse
import html
import re
import shutil
import subprocess
import sys
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "site"
sys.path.insert(0, str(ROOT / "tools"))
import docs_articles  # noqa: E402

REPO_URL = "https://github.com/emberian/fn"
BRANCH = "dev"
TITLE = "fuckin' news / formal news /᠁"
NODE = "fn.fg-goose.online"
READER = f"tin -T -r -A -p 563 -g {NODE}"
FRONT = "fn-welcome"

# LIST NEWSGROUPS, as a node would answer it.
DESCRIPTIONS = {
    "fn.announce": "Announcements about fn. Moderated in spirit.",
    "fn.docs": "The fn FAQ: how to read, run, peer and prove.",
}

PATH_RE = re.compile(
    r"(?<![\w./-])((?:docs|tools|books|planning|specs|swarmguide|site|packaging|host|tests)"
    r"/[\w./-]*[\w/]|AGENTS\.md|CONTRIBUTING\.md|README\.md|LICENSE)")
URL_RE = re.compile(r"https?://[^\s<>\"]+[^\s<>\".,;:)]")
PART_RE = re.compile(r"\b(parts? )(\d+)\b")
MSGID_RE = re.compile(r"&lt;([\w.-]+@" + re.escape(docs_articles.DOMAIN) + r")&gt;")
LABEL_RE = re.compile(r"^(\*[^*]+\*)")


class BuildError(Exception):
    pass


def git(*args: str) -> str:
    try:
        return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True,
                              check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


class Site:
    def __init__(self, articles: list[docs_articles.Article]):
        self.articles = articles
        self.by_id = {a.message_id: a for a in articles}
        self.groups: dict[str, list[docs_articles.Article]] = {g: [] for g in docs_articles.GROUPS}
        for a in articles:
            self.groups.setdefault(a.group, []).append(a)
        self.number = {a.message_id: n for g in self.groups.values() for n, a in enumerate(g, 1)}
        self.parts = {}
        for a in articles:
            m = re.fullmatch(r"fn-faq/part(\d+)", a.get("Archive-name"))
            if m:
                self.parts[int(m.group(1))] = a
        self.errors: list[str] = []

    # --- where things live ------------------------------------------------
    def out(self, a: docs_articles.Article) -> str:
        return "index.html" if a.stem == FRONT else f"{a.group}/{a.stem}.html"

    def href(self, from_out: str, to_out: str) -> str:
        depth = from_out.count("/")
        return "../" * depth + to_out

    def children(self, a) -> list:
        return [c for c in self.articles if c.references and c.references[-1] == a.message_id]

    def threads(self, group: str) -> list[tuple[int, docs_articles.Article]]:
        """(depth, article) in thread order: roots by number, each followed
        by its follow-ups, depth-first (tin's thread view)."""
        members = self.groups[group]
        roots = [a for a in members if not any(r in self.by_id and self.by_id[r].group == group
                                               for r in a.references)]
        order: list[tuple[int, docs_articles.Article]] = []

        def walk(a, depth):
            order.append((depth, a))
            for child in self.children(a):
                if child.group == group:
                    walk(child, depth + 1)
        for root in roots:
            walk(root, 0)
        return order

    # --- the body ---------------------------------------------------------
    def inline(self, text: str, from_out: str, rel: str) -> str:
        """Escape TEXT and link what a reader would want followed."""
        out, last = [], 0
        spans = []
        for m in URL_RE.finditer(text):
            spans.append((m.start(), m.end(), f'<a href="{html.escape(m.group(0))}">'
                          f"{html.escape(m.group(0))}</a>"))
        for m in PATH_RE.finditer(text):
            if any(s <= m.start() < e for s, e, _ in spans):
                continue
            path = m.group(1)
            if re.search(r"(?:^|/)[A-Z][A-Z-]+[A-Z](?:\.|/|$)", path) and not (ROOT / path).exists():
                continue                # a placeholder, like books/THE-BOOK.lisp
            if not (ROOT / path.rstrip("/")).exists():
                self.errors.append(f"{rel}: names {path}, which is not in the repository")
                continue
            kind = "tree" if (ROOT / path).is_dir() else "blob"
            spans.append((m.start(), m.end(), f'<a href="{REPO_URL}/{kind}/{BRANCH}/'
                          f'{path.rstrip("/")}">{html.escape(path)}</a>'))
        for m in PART_RE.finditer(text):
            n = int(m.group(2))
            if any(s <= m.start() < e for s, e, _ in spans) or n not in self.parts:
                if n not in self.parts:
                    self.errors.append(f"{rel}: names part {n}, which no article is")
                continue
            target = self.href(from_out, self.out(self.parts[n]))
            spans.append((m.start(2), m.end(2), f'<a href="{target}">{n}</a>'))
        for start, end, markup in sorted(spans):
            if start < last:
                continue
            out.append(self.msgids(html.escape(text[last:start]), from_out))
            out.append(markup)
            last = end
        out.append(self.msgids(html.escape(text[last:]), from_out))
        return "".join(out)

    def msgids(self, escaped: str, from_out: str) -> str:
        def link(m):
            mid = f"<{m.group(1)}>"
            if mid in self.by_id:
                return f'<a href="{self.href(from_out, self.out(self.by_id[mid]))}">{m.group(0)}</a>'
            return m.group(0)
        return MSGID_RE.sub(link, escaped)

    def body(self, a, from_out: str) -> str:
        """Blocks: command/art lines (4+ spaces) as <pre>, bullets and
        paragraphs as line-preserving text that reflows on a phone."""
        rel = a.path.relative_to(ROOT).as_posix()
        lines = a.body.rstrip("\n").split("\n")
        blocks: list[tuple[str, list[str]]] = []
        for line in lines:
            if not line.strip():
                blocks.append(("gap", []))
            elif line.startswith("    "):
                if blocks and blocks[-1][0] == "pre":
                    blocks[-1][1].append(line)
                else:
                    blocks.append(("pre", [line]))
            elif line.startswith("- "):
                blocks.append(("li", [line]))
            elif line.startswith("  ") and blocks and blocks[-1][0] == "li":
                blocks[-1][1].append(line)
            elif blocks and blocks[-1][0] == "p":
                blocks[-1][1].append(line)
            else:
                blocks.append(("p", [line]))
        out = []
        for kind, block in blocks:
            if kind == "gap":
                continue
            if kind == "pre":
                text = "\n".join(line[4:] for line in block)
                out.append(f'<pre class="cmd">{self.inline(text, from_out, rel)}</pre>')
                continue
            rendered = []
            for line in block:
                text = line.strip() if kind == "li" else line
                label = LABEL_RE.match(text)
                if label:
                    rest = text[label.end():]
                    rendered.append(f"<b>{html.escape(label.group(1))}</b>"
                                    + self.inline(rest, from_out, rel))
                else:
                    rendered.append(self.inline(text, from_out, rel))
            joined = "\n".join(rendered)
            if kind == "li":
                joined = joined[len("- "):] if joined.startswith("- ") else joined
                out.append(f'<p class="li">{joined}</p>')
            else:
                out.append(f'<p class="para">{joined}</p>')
        return "\n".join(out)

    # --- pages ------------------------------------------------------------
    def layout(self, out: str, title: str, main: str, *, status: str, description: str,
               base: str = "") -> str:
        up = self.href(out, "")
        css = self.href(out, "style.css")
        icon = self.href(out, "favicon.svg")
        base_tag = f'<base href="{html.escape(base)}">\n' if base else ""
        groups = " ".join(
            f'<a href="{self.href(out, g + "/index.html")}">{g}</a>'
            f"({len(self.groups[g])})" for g in self.groups)
        return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
{base_tag}<title>{html.escape(title)}</title>
<meta name="description" content="{html.escape(description)}">
<meta name="color-scheme" content="light dark">
<link rel="stylesheet" href="{css}">
<link rel="icon" href="{icon}" type="image/svg+xml">
</head>
<body>
<div class="screen">
<header class="top">
<p class="bar"><a href="{up}index.html">{html.escape(TITLE)}</a> <span>{NODE}</span></p>
<nav class="menu">[<a href="{up}groups.html">groups</a>] {groups}</nav>
</header>
<hr>
<main>
{main}
</main>
<hr>
<footer>
<p class="status">{status}</p>
<p>Read this group in your newsreader: <code>{html.escape(READER)}</code> (port 563 TLS)</p>
<p><a href="{REPO_URL}">source</a> . <a href="{REPO_URL}/tree/{BRANCH}/docs/articles">the articles as files</a> . no scripts, no trackers</p>
</footer>
</div>
</body>
</html>
"""

    def article_page(self, a) -> str:
        out = self.out(a)
        group = self.groups[a.group]
        n = self.number[a.message_id]
        heads = "\n".join(
            f'<span class="hk">{html.escape(k)}:</span> {self.msgids(html.escape(v), out)}'
            for k, v in a.headers)
        follow = self.children(a)
        followups = ""
        if follow:
            items = "\n".join(
                f'<li><a href="{self.href(out, self.out(c))}">{html.escape(c.get("Subject"))}</a>'
                f' <span class="dim">({html.escape(c.get("Summary"))})</span></li>' for c in follow)
            followups = f'<section class="followups"><p><b>Follow-ups:</b></p><ul>{items}</ul></section>'
        nav = []
        if n > 1:
            nav.append(f'<a href="{self.href(out, self.out(group[n - 2]))}" rel="prev">p)rev</a>')
        if n < len(group):
            nav.append(f'<a href="{self.href(out, self.out(group[n]))}" rel="next">n)ext</a>')
        if a.references and a.references[0] in self.by_id:
            root = self.by_id[a.references[0]]
            nav.append(f'<a href="{self.href(out, self.out(root))}">t)hread</a>')
        nav.append(f'<a href="{self.href(out, a.group + "/index.html")}">u)p to {a.group}</a>')
        main = f"""<article>
<pre class="headers">{heads}</pre>
<div class="body">
{self.body(a, out)}
</div>
</article>
{followups}
<nav class="keys">{" ".join("[" + x + "]" for x in nav)}</nav>"""
        status = (f"{html.escape(a.group)}  article {n} of {len(group)}  "
                  f"{a.lines} lines")
        return self.layout(out, f"{a.get('Subject')} ({a.group})", main,
                           status=status, description=a.get("Summary"))

    def index_page(self, group: str) -> str:
        out = f"{group}/index.html"
        rows = []
        for depth, a in self.threads(group):
            subject = html.escape(a.get("Subject"))
            tree = ('<span class="tree">' + "&nbsp;" * (2 * depth - 2) + "`-&gt; </span>"
                    if depth else "")
            name = html.escape(a.get("From").split("<")[0].strip() or a.get("From"))
            rows.append(
                f'<tr><td class="num">{self.number[a.message_id]}</td>'
                f'<td class="subj">{tree}<a href="{self.href(out, self.out(a))}">{subject}</a></td>'
                f'<td class="from">{name}</td>'
                f'<td class="date">{a.date().strftime("%d %b %Y")}</td>'
                f'<td class="num">{a.lines}</td></tr>')
        main = f"""<h1>{group}</h1>
<p class="dim">{html.escape(DESCRIPTIONS.get(group, ""))}</p>
<table class="index">
<thead><tr><th class="num">#</th><th>Subject</th><th class="from">From</th><th class="date">Date</th><th class="num">Lines</th></tr></thead>
<tbody>
{chr(10).join(rows)}
</tbody>
</table>"""
        return self.layout(out, f"{group}: thread index", main,
                           status=f"{group}  {len(self.groups[group])} articles  "
                                  f"{len(self.threads(group)) - sum(1 for d, _ in self.threads(group) if d)} threads",
                           description=DESCRIPTIONS.get(group, group))

    def groups_page(self) -> str:
        out = "groups.html"
        rows = []
        for g, members in self.groups.items():
            rows.append(f'<tr><td class="num">{len(members)}</td>'
                        f'<td class="subj"><a href="{self.href(out, g + "/index.html")}">{g}</a></td>'
                        f'<td>{html.escape(DESCRIPTIONS.get(g, ""))}</td></tr>')
        main = f"""<h1>Groups on {NODE}</h1>
<p class="dim">The groups this site mirrors. The node carries more; log in to see them.</p>
<table class="index">
<thead><tr><th class="num">Arts</th><th>Group</th><th>Description</th></tr></thead>
<tbody>
{chr(10).join(rows)}
</tbody>
</table>"""
        total = sum(len(m) for m in self.groups.values())
        return self.layout(out, "fn: groups", main,
                           status=f"{len(self.groups)} groups  {total} articles",
                           description="The newsgroups of fn's documentation.")


def build(out_dir: Path, base_path: str) -> list[str]:
    articles = docs_articles.load()
    errors = docs_articles.check(articles)
    site = Site(articles)
    if FRONT not in {a.stem for a in articles}:
        errors.append(f"no front page: docs/articles/{FRONT}.txt is missing")
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)

    def write(rel: str, text: str):
        target = out_dir / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")

    for a in articles:
        write(site.out(a), site.article_page(a))
    for g in site.groups:
        write(f"{g}/index.html", site.index_page(g))
    write("groups.html", site.groups_page())
    write("404.html", site.layout(
        "404.html", "430 no such article", '<h1>430 no such article</h1>'
        '<p>Try <a href="groups.html">the group list</a>.</p>',
        status="430 no such article", description="Not found", base=base_path))
    for asset in ("style.css", "favicon.svg"):
        shutil.copyfile(SITE / asset, out_dir / asset)
    return errors + site.errors


class LinkCollector(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links: list[str] = []
        self.ids: set[str] = set()
        self.scripts = 0

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "script":
            self.scripts += 1
        if a.get("id"):
            self.ids.add(a["id"])
        for key in ("href", "src"):
            if a.get(key):
                self.links.append(a[key])


def check(out_dir: Path) -> list[str]:
    """Every internal href/src in every generated page resolves; no page
    carries a script."""
    pages: dict[Path, LinkCollector] = {}
    for path in sorted(out_dir.rglob("*.html")):
        parser = LinkCollector()
        parser.feed(path.read_text(encoding="utf-8"))
        pages[path.resolve()] = parser
    errors = []
    root = out_dir.resolve()
    for path, parser in pages.items():
        rel = path.relative_to(root)
        if parser.scripts:
            errors.append(f"{rel}: has a script")
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
                target.relative_to(root)
            except ValueError:
                errors.append(f"{rel}: link leaves the site: {link}")
                continue
            if not target.exists():
                errors.append(f"{rel}: broken link: {link}")
            elif parts.fragment and unquote(parts.fragment) not in pages[target].ids:
                errors.append(f"{rel}: no #{parts.fragment} on {target.relative_to(root)}")
    return errors


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", default=str(ROOT / "build" / "site"),
                    help="output directory (default build/site)")
    ap.add_argument("--check", action="store_true",
                    help="after building, check every internal link")
    ap.add_argument("--base-path", default="/fn/",
                    help="the site's path on its host, used only by 404.html (default /fn/)")
    args = ap.parse_args(argv)
    out_dir = Path(args.out)
    errors = build(out_dir, args.base_path)
    if args.check:
        errors += check(out_dir)
    for e in errors:
        print(f"site: {e}", file=sys.stderr)
    count = sum(1 for _ in out_dir.rglob("*.html"))
    if errors:
        print(f"site: {len(errors)} problem(s); {count} pages in {out_dir}", file=sys.stderr)
        return 1
    print(f"site: {count} pages in {out_dir}"
          + (", every article well-formed and every internal link resolves" if args.check else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
