#!/usr/bin/env python3
"""D64: fn ships its own OpenSSL 3.5.8 everywhere; no site may use a system libssl.

One transformation over the profiles, build scripts and prose that still
name a system libssl (the eight CRYPTO-SHIPPED-* repair items), with its rules
in one table, tools/crypto_shipped.json:

    kinds   site-kind -> profile, the files it lives in, the regex that finds it
    rules   exact text -> exact text, one per site, each tagged with its kind
    allow   sites that are correct as they are, each with its reason
    owed    sites another lane owns, each with the owner and the reason

    python3 tools/crypto_shipped.py plan    [--profile P]   every site, its rewrite, its owner
    python3 tools/crypto_shipped.py apply   [--profile P] [--dry-run]
    python3 tools/crypto_shipped.py check   [--profile P] [--strict]

`plan` lists each rule (pending, applied or drifted) and every detected site
with what covers it.  `apply --dry-run` prints the unified diff `apply` would
write; `apply` is idempotent (an applied rule is skipped; a rule whose old
text is neither found once nor already replaced is drift and stops the run,
exit 3).  `check` exits 1 while a pending rule or a detected site is neither
allowed nor owed; owed sites are listed (and fail only with --strict).
Profiles: linux, macos, openbsd, boxes, tests, docs (default: all but docs;
docs states the end state and applies only with --after-tls).
"""
from __future__ import annotations

import argparse
import difflib
import fnmatch
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
RULES = HERE / "crypto_shipped.json"
SCOPE = ("host", "packaging", "tools", "tests", "docs", "specs", "planning", "books")


def load(path: Path) -> dict:
    data = json.loads(path.read_text())
    for rule in data["rules"]:
        rule["profile"] = data["kinds"][rule["kind"]]["profile"]
        rule["old_text"] = "\n".join(rule["old"])
        rule["new_text"] = "\n".join(rule["new"])
    return data


def profiles_of(data: dict, wanted: str | None) -> list[str]:
    names = list(data["profiles"])
    if wanted is None:
        return [n for n in names if not data["profiles"][n].get("requires_flag")]
    if wanted not in names:
        raise SystemExit(f"crypto_shipped: no profile {wanted} (have {', '.join(names)})")
    return [wanted]


def files_matching(root: Path, globs: list[str]) -> list[Path]:
    found = []
    for pattern in globs:
        found += [p for p in sorted(root.glob(pattern)) if p.is_file()]
    return list(dict.fromkeys(found))


def state(rule: dict, text: str) -> str:
    """applied (new found; old absent, or only inside new), pending (old found once), drift."""
    old, new = rule["old_text"], rule["new_text"]
    if new in text and (old not in text or old in new):
        return "applied"
    if text.count(old) == 1:
        return "pending"
    return "drift"


def rewritten(root: Path, rules: list[dict]) -> tuple[dict[str, str], dict[str, str], list[tuple[dict, str]]]:
    """(before, after, per-rule states) for the files the rules name."""
    before: dict[str, str] = {}
    after: dict[str, str] = {}
    states: list[tuple[dict, str]] = []
    for rule in rules:
        path = root / rule["file"]
        if rule["file"] not in after:
            text = path.read_text() if path.is_file() else ""
            before[rule["file"]] = after[rule["file"]] = text
        st = state(rule, after[rule["file"]])
        states.append((rule, st))
        if st == "pending":
            after[rule["file"]] = after[rule["file"]].replace(rule["old_text"], rule["new_text"], 1)
    return before, after, states


def sites(root: Path, data: dict, profs: list[str]):
    """Every detected site: (kind, file, line number, line, cover) where cover is
    ('allow'|'owed', entry) or None (a violation)."""
    out = []
    seen = set()

    def cover(rel: str, line: str):
        for entry in data["allow"]:
            if fnmatch.fnmatch(rel, entry["file"]) and re.search(entry["pattern"], line):
                return ("allow", entry)
        for entry in data["owed"]:
            if entry["file"] == rel and re.search(entry["pattern"], line):
                return ("owed", entry)
        return None

    for kind, spec in data["kinds"].items():
        if spec["profile"] not in profs:
            continue
        pattern = re.compile(spec["pattern"])
        for path in files_matching(root, spec["files"]):
            rel = str(path.relative_to(root))
            for number, line in enumerate(path.read_text().splitlines(), 1):
                if pattern.search(line):
                    seen.add((rel, number))
                    out.append((kind, rel, number, line, cover(rel, line)))
    # owed sites no kind detector reaches (the ones another lane owns outright)
    for entry in data["owed"]:
        if entry["profile"] not in profs:
            continue
        path = root / entry["file"]
        if not path.is_file():
            continue
        pattern = re.compile(entry["pattern"])
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if pattern.search(line) and (entry["file"], number) not in seen:
                out.append(("owed-" + entry["profile"], entry["file"], number, line, ("owed", entry)))
    return out


def selected_rules(data: dict, profs: list[str]) -> list[dict]:
    return [r for r in data["rules"] if r["profile"] in profs]


def counts(rows, states):
    by: dict[str, dict[str, int]] = {}
    for rule, st in states:
        by.setdefault(rule["kind"], {}).setdefault("rule-" + st, 0)
        by[rule["kind"]]["rule-" + st] += 1
    for kind, _rel, _n, _line, cov in rows:
        label = "violation" if cov is None else cov[0]
        by.setdefault(kind, {}).setdefault(label, 0)
        by[kind][label] += 1
    return by


def cmd_plan(root, data, profs, out):
    rules = selected_rules(data, profs)
    _b, _a, states = rewritten(root, rules)
    for rule, st in states:
        out.write(f"rule  {st:8} {rule['kind']:28} {rule['file']}  [{rule['id']}]\n")
    rows = sites(root, data, profs)
    for kind, rel, number, line, cov in rows:
        tag = "UNHANDLED" if cov is None else f"{cov[0]}: {cov[1].get('owner') or cov[1]['reason']}"
        out.write(f"site  {kind:28} {rel}:{number}  {tag}\n")
    out.write("\nby kind:\n")
    for kind, tally in sorted(counts(rows, states).items()):
        out.write(f"  {kind:28} " + " ".join(f"{k}={v}" for k, v in sorted(tally.items())) + "\n")
    return 0


def cmd_apply(root, data, profs, dry, out, err, after_tls):
    for name in profs:
        flag = data["profiles"][name].get("requires_flag")
        if flag and not after_tls:
            err.write(f"crypto_shipped: profile {name} states the end state; pass {flag} once tls.lisp and books are converted\n")
            return 2
    before, after, states = rewritten(root, selected_rules(data, profs))
    drift = [r for r, st in states if st == "drift"]
    for rule in drift:
        err.write(f"crypto_shipped: drift: [{rule['id']}] {rule['file']}: old text is neither present once nor already replaced\n")
    if drift:
        return 3
    changed = [f for f in after if after[f] != before[f]]
    for rel in changed:
        diff = difflib.unified_diff(before[rel].splitlines(True), after[rel].splitlines(True),
                                    f"a/{rel}", f"b/{rel}")
        if dry:
            out.write("".join(diff))
        else:
            (root / rel).write_text(after[rel])
    if not dry:
        out.write(f"crypto_shipped: wrote {len(changed)} file(s): {' '.join(changed) or '(none)'}\n")
    return 0


def cmd_check(root, data, profs, strict, out):
    rules = selected_rules(data, profs)
    _b, _a, states = rewritten(root, rules)
    bad = 0
    for rule, st in states:
        if st != "applied":
            out.write(f"FAIL  rule {rule['id']} is {st} ({rule['file']})\n")
            bad += 1
    for kind, rel, number, line, cov in sites(root, data, profs):
        if cov is None:
            out.write(f"FAIL  {kind} {rel}:{number}: {line.strip()[:100]}\n")
            bad += 1
        elif cov[0] == "owed":
            entry = cov[1]
            out.write(f"owed: {entry['owner']}  {rel}:{number}  {entry['reason']}\n")
            if strict:
                bad += 1
    out.write("crypto_shipped check: " + ("FAIL" if bad else "ok") + f" (profiles {','.join(profs)})\n")
    return 1 if bad else 0


def main(argv=None, out=sys.stdout, err=sys.stderr) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=("plan", "apply", "check"))
    parser.add_argument("--profile")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--after-tls", action="store_true")
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--rules", type=Path, default=RULES)
    args = parser.parse_args(argv)
    data = load(args.rules)
    profs = profiles_of(data, args.profile)
    if args.command == "plan":
        return cmd_plan(args.root, data, profs, out)
    if args.command == "apply":
        return cmd_apply(args.root, data, profs, args.dry_run, out, err, args.after_tls)
    return cmd_check(args.root, data, profs, args.strict, out)


if __name__ == "__main__":
    sys.exit(main())
