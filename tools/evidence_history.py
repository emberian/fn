#!/usr/bin/env python3
"""Every blob the history rewrite drops is in the evidence archive, proven.

After the rewrite (build/coordinator/history-rewrite-plan.md) the archive
(hbox:/tank/fn/evidence) is the ONLY copy of what the drop list removes from
git history, so "archived" is a measurement, not a report:

  * WHICH BLOBS.  Every blob version ever at a path a drop rule matches, on
    every ref.  The walk is `git log --diff-merges=separate --root
    --no-renames --raw` with NO pathspec over a frozen ref snapshot, so no
    history simplification applies: a pathspec walk (`rev-list --objects
    REFS -- PATHS`, even `--all`) prunes a side branch whose version a merge
    discarded, and missed three real evidence blobs (Codex r61 F11).  Every
    blob of every commit's tree appears on one side of some commit's diff
    against one of its parents (the root against nothing), so the raw diffs
    of all commits against all parents list every blob version.  Refs that
    name a tree (refs/codex/*) are listed with `ls-tree -r`.
  * WHICH RULES.  The drop list is git-filter-repo's `--paths-from-file`
    syntax, matched here exactly as filter-repo matches it (r61 F7): a
    literal is the path or a leading directory of it; `glob:` is
    `fnmatch` over the whole path (`*` crosses `/`); `regex:` is `re.search`.
  * ARCHIVED.  Each blob's SHA-256 object at its CANONICAL name
    `objects/<sha[:2]>/<sha>.gz`, decompressed and re-hashed, its length
    checked, on the archive box itself (r61 F5: a name anywhere is not an
    object at its address).

    python3 tools/evidence_history.py complete --rules FILE
        [--migrate] [--write SUMMARY]

exits 0 when every blob is archived and verified, 1 when some are missing,
4 when some are present but do not verify (refused), 3 when the archive
cannot be asked (uncertain).  `--migrate` streams the missing and bad ones
in (evidence_ingest: verified, fsync'd, read back) and measures again.
`--write` records the pinned summary: the frozen ref snapshot with shas, each
rule with its path and blob counts, and "archived and verified N of N".
"""

from __future__ import annotations

import argparse
import dataclasses
import fnmatch
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import evidence_store  # noqa: E402

ZERO = "0" * 40
GIT = ["git", "-c", "log.showSignature=false", "-c", "core.quotePath=false"]


# ------------------------------------------------------------------- rules


@dataclasses.dataclass(frozen=True)
class Rule:
    text: str      # the line as written in the rules file
    kind: str      # literal | glob | regex
    pattern: str

    def matches(self, path: str) -> bool:
        if self.kind == "literal":
            # filter-repo's filename_matches: the path or a leading directory.
            n = len(self.pattern)
            return self.pattern == "" or (path.startswith(self.pattern) and (
                self.pattern.endswith("/") or len(path) == n or path[n:n + 1] == "/"))
        if self.kind == "glob":
            return fnmatch.fnmatchcase(path, self.pattern)
        return self._regex().search(path) is not None

    def _regex(self) -> re.Pattern:
        return _compiled(self.pattern)


_REGEX: dict[str, re.Pattern] = {}


def _compiled(pattern: str) -> re.Pattern:
    if pattern not in _REGEX:
        _REGEX[pattern] = re.compile(pattern)
    return _REGEX[pattern]


def parse_rules(text: str) -> list[Rule]:
    """filter-repo's --paths-from-file lines (no renames: this is a drop list)."""
    rules = []
    for line in text.splitlines():
        line = line.rstrip("\r\n")
        if not line or line.startswith("#"):
            continue
        if "==>" in line:
            raise ValueError(f"a rename rule is not a drop rule: {line!r}")
        if line.startswith("regex:"):
            _compiled(line[6:])
            rules.append(Rule(line, "regex", line[6:]))
        elif line.startswith("glob:"):
            rules.append(Rule(line, "glob", line[5:]))
        else:
            rules.append(Rule(line, "literal", line[8:] if line.startswith("literal:")
                              else line))
    return rules


def load_rules(path: Path) -> list[Rule]:
    return parse_rules(Path(path).read_text(encoding="utf-8"))


# -------------------------------------------------------------------- refs


@dataclasses.dataclass(frozen=True)
class Ref:
    name: str
    sha: str
    type: str      # commit | tag | tree | blob


def _git(root: Path, *args: str, data: bytes | None = None) -> bytes:
    done = subprocess.run([*GIT, "-C", str(root), *args], input=data,
                          capture_output=True, check=False)
    if done.returncode != 0:
        raise RuntimeError(f"git {' '.join(args[:3])} failed (exit {done.returncode}): "
                           f"{done.stderr.decode(errors='replace').strip()[-300:]}")
    return done.stdout


def snapshot_refs(root: Path) -> list[Ref]:
    """Every ref with its sha and object type, plus every worktree's HEAD
    (`--all` walks those too): the frozen set one measurement covers."""
    refs: dict[str, Ref] = {}
    rows = _git(root, "for-each-ref", "--format=%(objectname) %(objecttype) %(refname)")
    for row in rows.decode().splitlines():
        sha, kind, name = row.split(" ", 2)
        refs[name] = Ref(name, sha, kind)
    worktree = None
    for row in _git(root, "worktree", "list", "--porcelain").decode().splitlines():
        if row.startswith("worktree "):
            worktree = row[len("worktree "):]
        elif row.startswith("HEAD ") and worktree is not None:
            refs[f"HEAD {worktree}"] = Ref(f"HEAD {worktree}", row[5:].strip(), "commit")
    return sorted(refs.values(), key=lambda ref: ref.name)


def resolve_refs(root: Path, revisions: list[str]) -> list[Ref]:
    """Named revisions as a snapshot (`--all` is every ref)."""
    if revisions == ["--all"]:
        return snapshot_refs(root)
    found = []
    for revision in revisions:
        sha = _git(root, "rev-parse", "--verify", revision).decode().strip()
        kind = _git(root, "cat-file", "-t", sha).decode().strip()
        found.append(Ref(revision, sha, kind))
    return found


# -------------------------------------------------------------------- walk


def walk(root: Path, refs: list[Ref]):
    """Yield (blob id, path) for every blob version reachable from REFS:
    both sides of every raw diff of every commit against each parent (the
    root commit against the empty tree), and every blob of a tree ref."""
    commits = sorted({ref.sha for ref in refs if ref.type in ("commit", "tag")})
    if commits:
        out = _git(root, "log", "--stdin", "--diff-merges=separate", "--root",
                   "--no-renames", "--raw", "-z", "--no-abbrev", "--format=",
                   "--no-ext-diff", "--no-textconv",
                   data="".join(sha + "\n" for sha in commits).encode())
        tokens = out.split(b"\0")
        at = 0
        while at < len(tokens):
            token = tokens[at].lstrip(b"\n")
            at += 1
            if not token.startswith(b":"):
                continue
            fields = token[1:].split(b" ")
            if len(fields) != 5 or at >= len(tokens):
                raise RuntimeError(f"unexpected raw diff line {token[:120]!r}")
            path = tokens[at].decode("utf-8", "surrogateescape")
            at += 1
            old_mode, new_mode, old, new = (f.decode() for f in fields[:4])
            for mode, oid in ((old_mode, old), (new_mode, new)):
                if oid != ZERO and is_blob_mode(mode):
                    yield oid, path
    for ref in refs:
        if ref.type == "tree":
            for entry in _git(root, "ls-tree", "-r", "-z", "--full-tree", ref.sha).split(b"\0"):
                if not entry:
                    continue
                meta, _, path = entry.partition(b"\t")
                mode, kind, oid = meta.decode().split()
                if kind == "blob" and is_blob_mode(mode):
                    yield oid, path.decode("utf-8", "surrogateescape")


def is_blob_mode(mode: str) -> bool:
    """A file or a symlink (100644, 100755, the old 100664, 120000); never a
    gitlink (160000) or a tree."""
    return mode.startswith("100") or mode == "120000"


def rule_blobs(root: Path, rules: list[Rule], refs: list[Ref]) -> dict[str, dict[str, str]]:
    """{rule text: {blob id: first path}} over the whole walk."""
    found: dict[str, dict[str, str]] = {rule.text: {} for rule in rules}
    verdicts: dict[str, list[Rule]] = {}
    for oid, path in walk(root, refs):
        hits = verdicts.get(path)
        if hits is None:
            hits = verdicts[path] = [rule for rule in rules if rule.matches(path)]
        for rule in hits:
            found[rule.text].setdefault(oid, path)
    return found


def union(per_rule: dict[str, dict[str, str]]) -> dict[str, str]:
    blobs: dict[str, str] = {}
    for found in per_rule.values():
        for oid, path in found.items():
            blobs.setdefault(oid, path)
    return blobs


def digests(root: Path, blobs: dict[str, str]) -> dict[str, tuple[str, int]]:
    """{blob id: (sha256, bytes)}; raises unless git delivered every blob."""
    result = {oid: (evidence_store.sha256_bytes(data), len(data))
              for oid, data in evidence_store.cat_blobs(root, {oid: oid for oid in blobs})}
    if len(result) != len(blobs):
        raise RuntimeError(f"git delivered {len(result)} of {len(blobs)} blobs")
    return result


# ----------------------------------------------------------------- archive


CHECK_SCRIPT = r"""
import gzip, hashlib, json, os, re, sys, zlib
root = sys.argv[1]; missing = []; bad = []; n = 0; hex64 = re.compile('[0-9a-f]{64}')
for line in sys.stdin:
    parts = line.split()
    if len(parts) != 2:
        continue
    sha, size = parts[0], int(parts[1]); n += 1
    if not hex64.fullmatch(sha):
        bad.append(sha); continue
    path = os.path.join(root, 'objects', sha[:2], sha + '.gz')
    if not os.path.isfile(path):
        missing.append(sha); continue
    try:
        with open(path, 'rb') as handle:
            data = gzip.decompress(handle.read())
        ok = len(data) == size and hashlib.sha256(data).hexdigest() == sha
    except (OSError, EOFError, ValueError, zlib.error):
        ok = False
    if not ok:
        bad.append(sha)
print(json.dumps({'checked': n, 'missing': missing, 'bad': bad}))
"""


def archive_check(wanted: dict[str, int], spec: str | None = None) -> dict:
    """{sha256: bytes} -> {"checked", "missing", "bad"}, measured where the
    archive is: the canonical object, decompressed, re-hashed, length checked."""
    host, path = evidence_store.split_spec(spec or evidence_store.archive_spec())
    command = ["python3", "-c", CHECK_SCRIPT, path]
    argv = ["ssh", host, " ".join(shlex.quote(part) for part in command)] if host else command
    lines = "".join(f"{sha} {size}\n" for sha, size in sorted(wanted.items()))
    done = subprocess.run(argv, input=lines, capture_output=True, text=True, check=False)
    try:
        report = json.loads(done.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        report = None
    if done.returncode != 0 or not isinstance(report, dict) \
            or report.get("checked") != len(wanted):
        raise evidence_store.EvidenceUnavailable(
            f"the archive {spec or evidence_store.archive_spec()} could not be checked "
            f"(exit {done.returncode}): {done.stderr.strip()[-300:]}")
    return report


# --------------------------------------------------------------------- CLI


def measure(root: Path, rules: list[Rule], refs: list[Ref]):
    per_rule = rule_blobs(root, rules, refs)
    blobs = union(per_rule)
    hashed = digests(root, blobs)
    wanted = {sha: size for sha, size in hashed.values()}
    report = archive_check(wanted)
    return per_rule, blobs, hashed, report


def cmd_complete(args) -> int:
    root = evidence_store.ROOT
    rules_path = Path(args.rules)
    rules = load_rules(rules_path)
    refs = snapshot_refs(root)
    per_rule, blobs, hashed, report = measure(root, rules, refs)
    failing = set(report["missing"]) | set(report["bad"])
    if args.migrate and failing:
        todo = {oid: path for oid, path in blobs.items() if hashed[oid][0] in failing}
        print(f"migrating {len(todo)} blobs ({len(report['missing'])} missing, "
              f"{len(report['bad'])} not verifying) to {evidence_store.archive_spec()}",
              flush=True)
        rows = evidence_store.stream_objects_to_archive(root, todo, [])
        evidence_store.write_ledger(rows, "history-ledger-complete")
        report = archive_check({sha: size for sha, size in hashed.values()})
        failing = set(report["missing"]) | set(report["bad"])
    by_sha: dict[str, list[str]] = {}
    for oid, (sha, _) in hashed.items():
        by_sha.setdefault(sha, []).append(oid)
    missing_blobs = sorted(oid for sha in report["missing"] for oid in by_sha[sha])
    bad_blobs = sorted(oid for sha in report["bad"] for oid in by_sha[sha])
    rule_rows = {}
    for rule in rules:
        found = per_rule[rule.text]
        rule_rows[rule.text] = {
            "paths": len(set(found.values())), "blobs": len(found),
            "distinct_sha256": len({hashed[oid][0] for oid in found}),
            "missing": sum(1 for oid in found if hashed[oid][0] in failing)}
        print(f"  {rule.text}: {len(set(found.values()))} paths, {len(found)} blobs, "
              f"{rule_rows[rule.text]['missing']} not archived+verified")
    archived = len(blobs) - len({*missing_blobs, *bad_blobs})
    head = _git(root, "rev-parse", "HEAD").decode().strip()
    print(f"history at {head} over {len(refs)} refs, {len(rules)} rules: {len(blobs)} blobs "
          f"({len({sha for sha, _ in hashed.values()})} distinct sha256, "
          f"{sum(size for _, size in hashed.values()) / 1e6:.1f} MB raw); archived+verified "
          f"in {evidence_store.archive_spec()} at the canonical name: {archived} / "
          f"{len(blobs)}, missing {len(missing_blobs)}, refused {len(bad_blobs)}")
    for oid in missing_blobs[:20]:
        print(f"  MISSING {oid} {hashed[oid][0]} {blobs[oid]}")
    for oid in bad_blobs[:20]:
        print(f"  REFUSED {oid} {hashed[oid][0]} {blobs[oid]}")
    if args.write:
        listing = "".join(f"{ref.sha} {ref.type} {ref.name}\n" for ref in refs)
        summary = {
            "schema": 1,
            "what": "every git blob version a history-rewrite drop rule matches, on every "
                    "ref of the frozen snapshot, archived at objects/<sha256[:2]>/<sha256>.gz "
                    "and verified on the archive box (decompressed, SHA-256 and length)",
            "generated_by": "python3 tools/evidence_history.py complete --rules "
                            f"{rules_path.as_posix()}" + (" --migrate" if args.migrate else ""),
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "head": head,
            "archive": evidence_store.archive_spec(),
            "rules_file": rules_path.as_posix(),
            "rules_sha256": hashlib.sha256(rules_path.read_bytes()).hexdigest(),
            "refs_count": len(refs),
            "refs_sha256": hashlib.sha256(listing.encode()).hexdigest(),
            "rules": rule_rows,
            "blobs": len(blobs),
            "distinct_sha256": len({sha for sha, _ in hashed.values()}),
            "raw_bytes": sum(size for _, size in hashed.values()),
            "archived_verified": archived,
            "missing": len(missing_blobs),
            "bad": len(bad_blobs),
            "refs": [[ref.name, ref.type, ref.sha] for ref in refs],
        }
        out = Path(args.write)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8")
        print(f"wrote {out}")
    if bad_blobs:
        return evidence_store.EXIT_REFUSED
    return 1 if missing_blobs else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    subs = parser.add_subparsers(dest="action", required=True)
    one = subs.add_parser("complete", help="measure (and --migrate) every dropped blob")
    one.add_argument("--rules", required=True, help="the filter-repo --paths-from-file list")
    one.add_argument("--migrate", action="store_true",
                     help="stream missing or non-verifying blobs in, then measure again")
    one.add_argument("--write", help="write the pinned summary JSON here")
    one.set_defaults(func=cmd_complete)
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except evidence_store.EvidenceError as error:
        print(f"evidence_history: {evidence_store.outcome(error)}: {error}", file=sys.stderr)
        return evidence_store.exit_code(error)


if __name__ == "__main__":
    raise SystemExit(main())
