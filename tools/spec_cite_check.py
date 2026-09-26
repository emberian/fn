#!/usr/bin/env python3
"""Every Lisp name a specification or document cites is one the tree defines.

PKT-312: specs/bp-node-machine.md named the retired `fn-bpn-limits-compose`
four times, a theorem whose statement is false at the new widths, and no tool
noticed: `tools/ledger.py` checks the registry's theorem names and
`tools/cite_check.py` checks repository paths, while a spec's prose cites
theorems by name.  This tool reads every backquoted span of `specs/*.md` and
`docs/*.md` that is exactly one `fn...-...` symbol and asks whether any book,
test book or host file defines it (tools/ledger.py's tree: defun, defthm,
defconst, defmacro, defstobj, encapsulate signatures, and the host files'
definitions).  Case is ignored, as ACL2's reader ignores it.

Not checked, by visible rule (each counted in the summary):
  * template: the span holds `*`, `<` or `>` (`fn-bpn-*`, `fn-<rec>-shapep`);
  * short: one segment after the prefix (`fn-bpn`, `fn-host`, `fn-e`,
    `fnn-sha256`): prefixes (docs/prefixes.md), magics, record kinds, programs
    and images, which prose names without their being Lisp definitions;
  * tag: a `-vN` suffix (`fn-hybrid-v1`, `fn-peering-v1`): a versioned
    domain-separation tag or format name, octets rather than a name.
Named exemptions (tools/spec_cite_exemptions.json `exemptions`) are names a
person judged are not definitions, each with a reason.  The `stale` section
names, per packet, the citations known to be stale and not yet repaired,
each with the files that still cite it: they are reported and counted, never
silent, and `--strict` fails on any citation that is neither defined nor
listed, and on any listed entry that no longer occurs (so the list only
shrinks as the repairs land).

    python3 tools/spec_cite_check.py --summary --strict     # make check
    python3 tools/spec_cite_check.py --list                 # every unresolved citation
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
EXEMPTIONS = ROOT / "tools" / "spec_cite_exemptions.json"
SPAN = re.compile(r"`([^`\n]+)`")
SYMBOL = re.compile(r"fn[a-z0-9]*-[a-z0-9\-*+?!<>=/%.]*[a-z0-9*+?!<>=%]", re.I)
TAG = re.compile(r".*-v[0-9]+")


@dataclass
class Result:
    checked: int = 0
    resolved: int = 0
    ruled: dict = field(default_factory=lambda: {"template": 0, "short": 0, "tag": 0})
    exempted: dict = field(default_factory=dict)       # name -> count
    stale: dict = field(default_factory=dict)          # name -> [file:line]
    unlisted: dict = field(default_factory=dict)       # name -> [file:line]
    unused: list = field(default_factory=list)         # listed entries no longer cited

    @property
    def ok(self) -> bool:
        return not self.unlisted and not self.unused


def rule_for(name: str) -> str | None:
    if any(ch in name for ch in "*<>"):
        return "template"
    if name.count("-") == 1:
        return "short"
    if TAG.fullmatch(name):
        return "tag"
    return None


def citations(documents):
    """(name lowered, "file:line") for every single-symbol backquoted span."""
    for relative, text in documents:
        for number, line in enumerate(text.splitlines(), 1):
            for match in SPAN.finditer(line):
                span = match.group(1).strip()
                if SYMBOL.fullmatch(span):
                    yield span.lower(), f"{relative}:{number}"


def check(defined: set, documents, exemptions: dict) -> Result:
    named = {name.lower(): reason for name, reason in exemptions.get("exemptions", {}).items()}
    listed = {}  # name -> (packet, set of files)
    for packet, entries in exemptions.get("stale", {}).items():
        for name, files in entries.items():
            listed[name.lower()] = (packet, set(files))
    result = Result()
    seen_listed: set = set()
    seen_named: set = set()
    for name, where in citations(documents):
        result.checked += 1
        if name in defined:
            result.resolved += 1
            continue
        rule = rule_for(name)
        if rule:
            result.ruled[rule] += 1
            continue
        if name in named:
            seen_named.add(name)
            result.exempted[name] = result.exempted.get(name, 0) + 1
            continue
        file = where.rsplit(":", 1)[0]
        if name in listed and file in listed[name][1]:
            seen_listed.add((name, file))
            result.stale.setdefault(name, []).append(where)
            continue
        result.unlisted.setdefault(name, []).append(where)
    for name, reason in sorted(named.items()):
        if not isinstance(reason, str) or not reason.strip():
            result.unused.append(f"exemption {name}: no reason given")
    for name in sorted(set(named) - seen_named):
        result.unused.append(f"exemption {name}: no longer cited")
    for name, (packet, files) in sorted(listed.items()):
        for file in sorted(files):
            if (name, file) not in seen_listed:
                result.unused.append(f"{packet} {name} in {file}: no longer an unresolved citation there")
    return result


def defined_names() -> set:
    sys.path.insert(0, str(ROOT / "tools"))
    import ledger  # noqa: E402
    tree = ledger.load_tree()
    names = set(tree.functions) | set(tree.theorems) | set(tree.constrained)
    for book in tree.books.values():
        names |= book.definitions
    for host in tree.hosts.values():
        names |= host.defines | host.macros
    return {name.lower() for name in names}


def documents(root: Path = ROOT):
    for directory in ("specs", "docs"):
        for path in sorted((root / directory).glob("*.md")):
            yield path.relative_to(root).as_posix(), path.read_text(encoding="utf-8")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 on an unlisted unresolved citation or an unused entry")
    parser.add_argument("--summary", action="store_true", help="counts and failures only")
    parser.add_argument("--list", action="store_true", help="every unresolved citation")
    args = parser.parse_args(argv)
    exemptions = json.loads(EXEMPTIONS.read_text(encoding="utf-8"))
    result = check(defined_names(), list(documents()), exemptions)
    stale_count = sum(len(v) for v in result.stale.values())
    print(f"spec-cite: {result.checked} single-name citations in specs/ and docs/; "
          f"{result.resolved} defined; by rule {result.ruled['template']} template, "
          f"{result.ruled['short']} short, {result.ruled['tag']} tag; "
          f"{sum(result.exempted.values())} exempted ({len(result.exempted)} names, reasons in "
          f"{EXEMPTIONS.relative_to(ROOT)}); {stale_count} known stale "
          f"({len(result.stale)} names, listed by packet); "
          f"{sum(len(v) for v in result.unlisted.values())} unlisted")
    if args.list:
        for name, where in sorted(result.stale.items()):
            print(f"  stale {name}: {', '.join(where)}")
    for name, where in sorted(result.unlisted.items()):
        print(f"  UNDEFINED {name}: {', '.join(where)} (no book, test book or host file defines it)")
    for line in result.unused:
        print(f"  UNUSED {line}")
    return 1 if args.strict and not result.ok else 0


if __name__ == "__main__":
    raise SystemExit(main())
