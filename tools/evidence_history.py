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
    `fnmatch` over the whole path (`*` crosses `/`), and a glob not ending in
    `*` also matches `<glob>/*` (filter-repo appends that rule, r65 F2);
    `regex:` is `re.search`.  `crosscheck` compares against what filter-repo
    itself drops in a scratch mirror, so the two cannot disagree unseen.
  * WHICH REFS.  Every ref, every worktree's HEAD and private refs, and
    every commit any reflog names (the rewrite expires reflogs, so a commit
    reachable only from one would otherwise be lost unmeasured).
  * ARCHIVED.  Each blob's SHA-256 object at its CANONICAL name
    `objects/<sha[:2]>/<sha>.gz`, decompressed and re-hashed, its length
    checked, on the archive box itself (r61 F5: a name anywhere is not an
    object at its address).

    python3 tools/evidence_history.py complete --rules FILE
        [--migrate] [--write SUMMARY | --check SUMMARY]
    python3 tools/evidence_history.py crosscheck --rules FILE --mirror DIR

exits 0 when every blob is archived and verified, 1 when some are missing,
4 when some are present but do not verify (refused), 3 when the archive
cannot be asked (uncertain).  `--migrate` streams the missing and bad ones
in (evidence_ingest: verified, fsync'd, read back) and measures again.
`--write` records the pinned summary: the frozen ref snapshot with shas, each
rule with its path and blob counts, the digest of the sorted blob set, the
committed index (rows, digest, objects verified), and "archived and verified
N of N".  `--check SUMMARY` is the rewrite-time gate: it measures again and
REFUSES (exit 1) on drift -- a dropped-blob set or index other than the
pinned one -- as well as on anything missing or refused.
"""

from __future__ import annotations

import argparse
import dataclasses
import os
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
            # filter-repo's get_paths_from_file adds `<glob>/*` (or `<glob>*`
            # after a slash) for a glob that does not end in `*`.
            if fnmatch.fnmatchcase(path, self.pattern):
                return True
            if self.pattern.endswith("*"):
                return False
            extra = self.pattern + ("*" if self.pattern.endswith("/") else "/*")
            return fnmatch.fnmatchcase(path, extra)
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
    type: str      # commit | tag | tree | blob | reflog
    peel: str = ""         # what an annotated tag finally names (else sha)
    peel_type: str = ""    # its type (else type)

    @property
    def target(self) -> tuple[str, str]:
        return (self.peel or self.sha, self.peel_type or self.type)


def _git(root: Path, *args: str, data: bytes | None = None) -> bytes:
    done = subprocess.run([*GIT, "-C", str(root), *args], input=data,
                          capture_output=True, check=False)
    if done.returncode != 0:
        raise RuntimeError(f"git {' '.join(args[:3])} failed (exit {done.returncode}): "
                           f"{done.stderr.decode(errors='replace').strip()[-300:]}")
    return done.stdout


def snapshot_refs(root: Path, reflogs: bool = True) -> list[Ref]:
    """Every ref with its sha and object type, every worktree's HEAD, and
    (type "reflog") every other commit `rev-list --all --reflog` names --
    worktree-private refs and reflog entries in every worktree: the frozen
    set one measurement covers."""
    refs: dict[str, Ref] = {}
    fmt = "--format=%(objectname) %(objecttype) %(refname)"
    for row in _git(root, "for-each-ref", fmt).decode().splitlines():
        sha, kind, name = row.split(" ", 2)
        refs[name] = Ref(name, sha, kind)
    worktree = None
    for row in _git(root, "worktree", "list", "--porcelain").decode().splitlines():
        if row.startswith("worktree "):
            worktree = row[len("worktree "):]
        elif row.startswith("HEAD ") and worktree is not None:
            refs[f"HEAD {worktree}"] = Ref(f"HEAD {worktree}", row[5:].strip(), "commit")
            # That worktree's private refs (any object type, trees included).
            # A worktree that cannot be asked is an error, never a silent
            # skip: `git worktree prune` (or restore it) and measure again.
            done = subprocess.run([*GIT, "-C", worktree, "for-each-ref", fmt, "refs/worktree",
                                   "refs/bisect", "refs/rewritten"],
                                  capture_output=True, check=False)
            if done.returncode != 0:
                raise RuntimeError(
                    f"cannot list the private refs of worktree {worktree} (git exit "
                    f"{done.returncode}: {done.stderr.decode(errors='replace').strip()[-200:]}); "
                    "prune or restore it, then measure again")
            for line in done.stdout.decode().splitlines():
                sha, kind, name = line.split(" ", 2)
                refs[f"{worktree} {name}"] = Ref(f"{worktree} {name}", sha, kind)
    tags = [ref for ref in refs.values() if ref.type == "tag"]
    if tags:
        # Peel every annotated tag to what it finally names: a tag of a tree
        # or a blob is walked as that tree or blob, never handed to git log.
        rows = _git(root, "cat-file", "--batch-check=%(objectname) %(objecttype)",
                    data="".join(f"{ref.sha}^{{}}\n" for ref in tags).encode())
        for ref, row in zip(tags, rows.decode().splitlines()):
            peel, kind = row.split()[:2]
            refs[ref.name] = Ref(ref.name, ref.sha, ref.type, peel, kind)
    if reflogs:
        named = {ref.sha for ref in refs.values()}
        tips = _git(root, "rev-list", "--no-walk", "--all", "--reflog").decode().split()
        for sha in sorted(set(tips) - named):
            refs[f"reflog {sha}"] = Ref(f"reflog {sha}", sha, "reflog")
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
    commits = sorted({ref.target[0] for ref in refs
                      if ref.target[1] in ("commit", "reflog")})
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
        sha, kind = ref.target
        if kind == "blob":
            yield sha, ""      # a ref to a bare blob: no path, matches no rule
        if kind == "tree":
            for entry in _git(root, "ls-tree", "-r", "-z", "--full-tree", sha).split(b"\0"):
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


def archive_check(wanted, spec: str | None = None) -> dict:
    """{sha256: bytes} or a set of (sha256, bytes) pairs -> {"checked",
    "missing", "bad"}, measured where the archive is: the canonical object,
    decompressed, re-hashed, length checked.  Every pair is checked, so an
    index row that names a hash with the wrong length is refused (r66 F2)."""
    if isinstance(wanted, dict):
        wanted = set(wanted.items())
    host, path = evidence_store.split_spec(spec or evidence_store.archive_spec())
    command = ["python3", "-c", CHECK_SCRIPT, path]
    argv = ["ssh", host, " ".join(shlex.quote(part) for part in command)] if host else command
    lines = "".join(f"{sha} {size}\n" for sha, size in sorted(wanted))
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


def blob_set_digest(blobs) -> str:
    return hashlib.sha256("".join(oid + "\n" for oid in sorted(blobs)).encode()).hexdigest()


def committed_index(root: Path, head: str) -> tuple[bytes, dict[str, tuple[str, int]]]:
    done = subprocess.run([*GIT, "-C", str(root), "show", f"{head}:{evidence_store.INDEX_REL}"],
                          capture_output=True, check=False)
    data = done.stdout if done.returncode == 0 else b""
    return data, evidence_store.parse_index(data.decode("utf-8"))


def cmd_complete(args) -> int:
    root = evidence_store.ROOT
    rules_path = Path(args.rules)
    rules = load_rules(rules_path)
    refs = snapshot_refs(root)
    head = _git(root, "rev-parse", "HEAD").decode().strip()
    index_bytes, index = committed_index(root, head)
    per_rule = rule_blobs(root, rules, refs)
    blobs = union(per_rule)
    hashed = digests(root, blobs)
    # Every dropped blob AND every object the committed index names.
    wanted = set(hashed.values()) | set(index.values())
    report = archive_check(wanted)
    failing = set(report["missing"]) | set(report["bad"])
    if args.migrate and failing:
        todo = {oid: path for oid, path in blobs.items() if hashed[oid][0] in failing}
        print(f"migrating {len(todo)} blobs ({len(report['missing'])} missing, "
              f"{len(report['bad'])} not verifying) to {evidence_store.archive_spec()}",
              flush=True)
        for oid, path in sorted(todo.items(), key=lambda item: item[1]):
            print(f"  migrating {oid} {hashed[oid][0]} {path}")
        if todo:
            rows = evidence_store.stream_objects_to_archive(root, todo, [])
            evidence_store.write_ledger(rows, "history-ledger-complete")
        report = archive_check(wanted)
        failing = set(report["missing"]) | set(report["bad"])
    by_sha: dict[str, list[str]] = {}
    for oid, (sha, _) in hashed.items():
        by_sha.setdefault(sha, []).append(oid)
    missing_blobs = sorted(oid for sha in report["missing"] for oid in by_sha.get(sha, []))
    bad_blobs = sorted(oid for sha in report["bad"] for oid in by_sha.get(sha, []))
    index_failing = sorted(path for path, (sha, _) in index.items() if sha in failing)
    index_refused = any(index[path][0] in set(report["bad"]) for path in index_failing)
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
    named = [ref for ref in refs if ref.type != "reflog"]
    reflog = sorted(ref.sha for ref in refs if ref.type == "reflog")
    print(f"history at {head} over {len(named)} refs + {len(reflog)} other reflog/private "
          f"commits, {len(rules)} rules: {len(blobs)} blobs "
          f"({len({sha for sha, _ in hashed.values()})} distinct sha256, "
          f"{sum(size for _, size in hashed.values()) / 1e6:.1f} MB raw); archived+verified "
          f"in {evidence_store.archive_spec()} at the canonical name: {archived} / "
          f"{len(blobs)}, missing {len(missing_blobs)}, refused {len(bad_blobs)}; "
          f"committed index {len(index)} rows, objects not archived+verified: "
          f"{len(index_failing)}")
    for oid in missing_blobs[:20]:
        print(f"  MISSING {oid} {hashed[oid][0]} {blobs[oid]}")
    for oid in bad_blobs[:20]:
        print(f"  REFUSED {oid} {hashed[oid][0]} {blobs[oid]}")
    for path in index_failing[:20]:
        print(f"  INDEX ROW NOT ARCHIVED+VERIFIED {index[path][0]} {path}")
    listing = "".join(f"{ref.sha} {ref.type} {ref.name}\n" for ref in named)
    summary = {
        "schema": 2,
        "what": "every git blob version a history-rewrite drop rule matches, on every ref, "
                "worktree HEAD and private ref and reflog-named commit of the frozen "
                "snapshot, and every object the committed index names, archived at "
                "objects/<sha256[:2]>/<sha256>.gz and verified on the archive box "
                "(decompressed, SHA-256 and length)",
        "generated_by": "python3 tools/evidence_history.py complete --rules "
                        f"{rules_path.as_posix()}" + (" --migrate" if args.migrate else ""),
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "head": head,
        "archive": evidence_store.archive_spec(),
        "rules_file": rules_path.as_posix(),
        "rules_sha256": hashlib.sha256(rules_path.read_bytes()).hexdigest(),
        "refs_count": len(named),
        "refs_sha256": hashlib.sha256(listing.encode()).hexdigest(),
        "reflog_commits": len(reflog),
        "reflog_commits_sha256": blob_set_digest(reflog),
        "rules": rule_rows,
        "blobs": len(blobs),
        "blobs_sha256": blob_set_digest(blobs),
        "distinct_sha256": len({sha for sha, _ in hashed.values()}),
        "raw_bytes": sum(size for _, size in hashed.values()),
        "archived_verified": archived,
        "missing": len(missing_blobs),
        "bad": len(bad_blobs),
        "index": {"path": evidence_store.INDEX_REL, "rows": len(index),
                  "sha256": hashlib.sha256(index_bytes).hexdigest(),
                  "objects": len({sha for sha, _ in index.values()}),
                  "rows_not_archived_verified": len(index_failing)},
        "refs": [[ref.name, ref.type, ref.sha] for ref in named],
    }
    drift = []
    if args.check:
        pinned = json.loads(Path(args.check).read_text(encoding="utf-8"))
        for key, now, then in (
                ("dropped-blob set", summary["blobs_sha256"], pinned.get("blobs_sha256")),
                ("dropped-blob count", summary["blobs"], pinned.get("blobs")),
                ("rules file", summary["rules_sha256"], pinned.get("rules_sha256")),
                ("committed index", summary["index"]["sha256"],
                 (pinned.get("index") or {}).get("sha256"))):
            if now != then:
                drift.append(key)
                print(f"  DRIFT {key}: pinned {then}, now {now}")
        moved = sorted(set(map(tuple, summary["refs"])) ^ set(map(tuple, pinned.get("refs", []))))
        print(f"  refs differing from the pin (informational): {len(moved)}")
        if drift:
            print(f"REFUSED: drift from the pinned snapshot {args.check} ({', '.join(drift)}): "
                  "re-run `complete --migrate --write` at the frozen head and commit it")
    if args.write:
        out = Path(args.write)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8")
        print(f"wrote {out}")
    if bad_blobs or index_refused:
        return evidence_store.EXIT_REFUSED
    return 1 if (missing_blobs or index_failing or drift) else 0


def cmd_crosscheck(args) -> int:
    """What filter-repo really drops, in a fresh scratch mirror, is a subset
    of what `complete` archives (r65 F2: the tool and the rewrite cannot
    disagree unseen).  Writes only under --mirror, which must not exist."""
    root = evidence_store.ROOT
    rules_path = Path(args.rules).resolve()
    mirror = Path(args.mirror)
    if mirror.exists():
        print(f"crosscheck: {mirror} exists; give a fresh path", file=sys.stderr)
        return 2
    subprocess.run(["git", "clone", "-q", "--mirror", str(root), str(mirror)], check=True)
    # Guard: every command below runs with -C the mirror, and the mirror is
    # its own repository, never the one it was cloned from (r66 F4).
    common = _git(mirror, "rev-parse", "--path-format=absolute", "--git-common-dir")
    source = _git(root, "rev-parse", "--path-format=absolute", "--git-common-dir")
    if Path(common.decode().strip()) != mirror.resolve() or common == source:
        print(f"crosscheck: {mirror} is not a separate repository; refusing", file=sys.stderr)
        return 2
    for name in _git(mirror, "for-each-ref", "--format=%(refname)", "refs/codex").decode().split():
        _git(mirror, "update-ref", "-d", name)
    refs = snapshot_refs(mirror, reflogs=False)
    ours = set(union(rule_blobs(mirror, load_rules(rules_path), refs)))
    before = blob_ids(mirror)
    # filter-repo deletes refs/remotes/* in a mirror; what only those refs
    # reach leaves for that reason, not for a path rule (checked below).
    before_kept = blob_ids(mirror, "--exclude=refs/remotes/*")
    names_before = {ref.name for ref in refs}
    home = mirror.parent / (mirror.name + ".home")
    home.mkdir()
    env = {**os.environ, "HOME": str(home), "GIT_CONFIG_NOSYSTEM": "1"}
    subprocess.run(["git", "-C", str(mirror), "-c", "user.name=x", "-c", "user.email=x@x",
                    "filter-repo", "--force", "--invert-paths", "--paths-from-file",
                    str(rules_path)], check=True, env=env, capture_output=True)
    after = blob_ids(mirror)
    names_after = {ref.name for ref in snapshot_refs(mirror, reflogs=False)}
    removed = sorted(names_before - names_after)
    unexpected = [name for name in removed if not name.startswith("refs/remotes/")]
    dropped = before_kept - after
    escaped = dropped - ours
    remote_only = (before - before_kept) - after - ours
    print(f"crosscheck in {mirror}: {len(before)} blobs before filter-repo "
          f"({len(before_kept)} reachable without refs/remotes/*), {len(after)} after; "
          f"filter-repo removed {len(removed)} refs ({len(unexpected)} outside refs/remotes/*); "
          f"dropped from the kept refs: {len(dropped)}; the walk's set {len(ours)}; dropped "
          f"and not in the walk's set: {len(escaped)}; in the walk's set and kept (also at "
          f"a kept path): {len(ours - dropped)}; reachable only from refs/remotes/*, gone "
          f"with those refs and matching no rule (not the evidence archive's): "
          f"{len(remote_only)}")
    for oid in sorted(escaped)[:20]:
        print(f"  DROPPED, NOT MEASURED {oid}")
    for name in unexpected[:20]:
        print(f"  REF REMOVED OUTSIDE refs/remotes: {name}")
    return 1 if escaped or unexpected else 0


def blob_ids(repo: Path, *exclude: str) -> set[str]:
    rows = _git(repo, "rev-list", "--objects", *exclude, "--all").decode().splitlines()
    oids = "".join(row.split(" ", 1)[0] + "\n" for row in rows)
    kinds = _git(repo, "cat-file", "--batch-check=%(objectname) %(objecttype)",
                 data=oids.encode()).decode().splitlines()
    return {row.split()[0] for row in kinds if row.endswith(" blob")}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    subs = parser.add_subparsers(dest="action", required=True)
    one = subs.add_parser("complete", help="measure (and --migrate) every dropped blob")
    one.add_argument("--rules", required=True, help="the filter-repo --paths-from-file list")
    one.add_argument("--migrate", action="store_true",
                     help="stream missing or non-verifying blobs in, then measure again")
    one.add_argument("--write", help="write the pinned summary JSON here")
    one.add_argument("--check", help="refuse unless the measurement matches this pinned summary")
    one.set_defaults(func=cmd_complete)
    one = subs.add_parser("crosscheck", help="filter-repo's real drop set is measured")
    one.add_argument("--rules", required=True)
    one.add_argument("--mirror", required=True, help="a fresh scratch path for the mirror")
    one.set_defaults(func=cmd_crosscheck)
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except evidence_store.EvidenceError as error:
        print(f"evidence_history: {evidence_store.outcome(error)}: {error}", file=sys.stderr)
        return evidence_store.exit_code(error)


if __name__ == "__main__":
    raise SystemExit(main())
