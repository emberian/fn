#!/usr/bin/env python3
"""Decide, and check, whether an image run may start from a train's certified tree.

`tools/train.py certify BOX` certifies the batch tree's affected closure on the
box, in the farm tree (tools/farm.py: the batch tree's own absolute path on the
box).  `tools/hbox_native.sh` then used to ship the same commit to a second
tree and install, certify, wire and acquire everything again (27 minutes on a
loaded hbox, 2026-10-10).  `--from-train` runs the image build in the farm tree
instead, when this module proves that tree IS the commit and holds exactly the
certificates a fresh install would give it.  Never a copy: the extraction check
compares PROJECT-DIR-ALIST, which names the build path, so the images must be
built at the path the certificates were made at.

    native_reuse.py plan   --repo R --rev FULLSHA --box HOST
        Local.  Reads the train records and the farm record; prints one JSON
        object (run, certify_id, remote_path) or exits 1 naming the refusal.
        Passes when: the box step recorded sha == ran_at == REV on this box;
        the train state's box_run is that farm run; the farm run's box_manifest
        is "passed" with the same certify_id; the run was on HOST.
    native_reuse.py expect --repo R --rev FULLSHA --out FILE
        Local.  The commit's tracked files as git blob ids.
    native_reuse.py verify --root FARMTREE --expect FILE --cache C --acl2 A
                           --profile default [--profile dtn]
        On the box.  Exits 0 only when
          (1) every tracked file of REV is in the tree with the same git blob
              id, and the tree holds no other source file (so the tree is
              `git archive REV` plus certificates), and
          (2) for every book of the profiles' include closure, the tree holds
              a certificate whose bytes are a cache entry's pair at this
              book's closure key (so: published for exactly these sources,
              this toolchain), with the entry's port and compiled file.
        Anything else prints each difference and exits 1: the caller then
        takes the ordinary install, certify and acquire path.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

# Files a certified tree holds beyond the commit: certificates and their
# companions, bytecode.  build/, .git and the like are not shipped (farm.py
# EXCLUDES) and are not source.
GENERATED_SUFFIXES = (".cert", ".port", ".fasl", ".pyc")
SKIPPED_DIRECTORIES = {"build", ".git", "__pycache__", ".venv"}
MAX_SHOWN = 12


class Refusal(Exception):
    """The reuse is not taken; the message says why."""


def _git(repo: Path, *argv: str) -> str:
    done = subprocess.run(["git", "-C", str(repo), *argv], capture_output=True, text=True)
    if done.returncode != 0:
        raise Refusal(f"git {' '.join(argv)} failed: {done.stderr.strip()}")
    return done.stdout


def _read_json(path: Path, what: str) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise Refusal(f"{what} {path} unreadable: {error}") from None
    if not isinstance(value, dict):
        raise Refusal(f"{what} {path} is not an object")
    return value


# ----------------------------------------------------------------- the plan


def plan(repo: Path, rev: str, box: str, branch: str | None = None) -> dict:
    """The farm run whose tree may be reused for REV on BOX, or a Refusal.

    Every condition reads a record the train wrote; none is assumed.  The
    tree itself is checked separately (`verify`), because the records say
    what was shipped, not what the box holds now."""
    if len(rev) != 40 or any(c not in "0123456789abcdef" for c in rev):
        raise Refusal(f"REV {rev!r} is not a full commit sha")
    branch = branch or _git(repo, "rev-parse", "--abbrev-ref", "HEAD").strip()
    stem = branch.replace("/", "__")
    train = repo / "build" / "train"
    state = _read_json(train / f"{stem}.json", "train state")
    record = _read_json(train / f"{stem}.box-step.json", "box-step record")
    if record.get("box") != box:
        raise Refusal(f"the train certified on {record.get('box')!r}, this run is on {box!r}")
    sha, ran_at = record.get("sha"), record.get("ran_at")
    if sha != rev or ran_at != rev:
        raise Refusal(f"the box step ran at {str(sha)[:12]} (ran_at {str(ran_at)[:12]}), "
                      f"REV is {rev[:12]}")
    run = record.get("run")
    if not isinstance(run, str) or not run or Path(run).name != run:
        raise Refusal("the box-step record names no farm run")
    if state.get("box_run") != run:
        raise Refusal(f"the train state's box_run is {state.get('box_run')!r}, "
                      f"the box-step record's run is {run!r}")
    if record.get("known_reds_seen"):
        raise Refusal("the train certify ran with known reds: " + ", ".join(record["known_reds_seen"]))
    farm = _read_json(repo / "build" / "farm" / f"{run}.json", "farm record")
    if farm.get("host", farm.get("box")) != box:
        raise Refusal(f"the farm run was on {farm.get('host')!r}, not {box!r}")
    if farm.get("box_manifest") != "passed":
        raise Refusal(f"the farm run's manifest is {farm.get('box_manifest')!r}, not 'passed'")
    certify_id = farm.get("certify_id")
    if not certify_id or certify_id != record.get("certify_id"):
        raise Refusal(f"the farm run's certify id {certify_id!r} is not the box-step "
                      f"record's {record.get('certify_id')!r}")
    remote = farm.get("remote_path")
    if not isinstance(remote, str) or not remote.startswith("/") or "\n" in remote \
            or any(c in remote for c in " \t'\"\\$`;&|<>*?()"):
        raise Refusal(f"the farm run's remote_path {remote!r} is not a plain absolute path")
    return {"run": run, "certify_id": certify_id, "remote_path": remote.rstrip("/"),
            "sha": rev, "box": box}


# ------------------------------------------------------------ the commit


def blob_id(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def expected_tree(repo: Path, rev: str) -> dict[str, list[str]]:
    """path -> [mode, git blob id] for every tracked file of REV."""
    out = subprocess.run(["git", "-C", str(repo), "ls-tree", "-r", "-z", rev],
                         capture_output=True)
    if out.returncode != 0:
        raise Refusal(f"git ls-tree {rev}: {out.stderr.decode().strip()}")
    found: dict[str, list[str]] = {}
    for entry in out.stdout.split(b"\0"):
        if not entry:
            continue
        meta, _, path = entry.partition(b"\t")
        mode, kind, sha = meta.decode().split()
        if kind == "blob":
            found[path.decode()] = [mode, sha]
    return found


def tree_differences(root: Path, expected: dict[str, list[str]]) -> list[str]:
    """How ROOT differs from the commit: a tracked file missing or changed, a
    source file the commit does not track.  Empty when the tree is the commit
    (certificates and the other generated files aside)."""
    diffs: list[str] = []
    for path, (mode, sha) in sorted(expected.items()):
        target = root / path
        try:
            if mode == "120000":
                actual = blob_id(os.readlink(target).encode())
            else:
                actual = blob_id(target.read_bytes())
                if (mode == "100755") != bool(target.stat().st_mode & 0o111):
                    diffs.append(f"mode differs: {path}")
        except OSError:
            diffs.append(f"missing: {path}")
            continue
        if actual != sha:
            diffs.append(f"content differs: {path}")
    for directory, names, files in os.walk(root):
        names[:] = [n for n in names if not (Path(directory) == root and n in SKIPPED_DIRECTORIES)
                    and n not in ("__pycache__", ".venv")]
        for name in files:
            relative = (Path(directory) / name).relative_to(root).as_posix()
            if relative not in expected and not name.endswith(GENERATED_SUFFIXES):
                diffs.append(f"not in the commit: {relative}")
    return diffs


# ------------------------------------------------------- the certificates


def cert_differences(root: Path, roots: list[str], toolchain_identity: str,
                     cache: Path, entries=None, content_hash=None) -> list[str]:
    """How the tree's certificates differ from what certs.py installs.

    install-partial and acquire take, for each book of the closure, a cache
    entry stored under that book's closure key (the forms of the book and of
    every book it includes, and the world) for this toolchain, and place its
    book.cert, book.port and book.fasl.  So the tree is that install when,
    for every book of the closure, one such entry's certificate, port and
    compiled file are byte-identical to the tree's.  The ACL2 certificate
    check across the pairs (that they compose) is the farm certify's, whose
    manifest `plan` required to have passed; `proof_artifacts.py validate`
    loads them again in the image's launcher."""
    import certs  # noqa: PLC0415 (the tree's own copy: tools/ is on sys.path)
    entries = entries or certs.book_entries
    content_hash = content_hash or certs.content_hash
    diffs: list[str] = []
    try:
        books = sorted(certs.required_closure(root, roots))
    except certs.UnreadableBook as error:
        return [f"closure unreadable: {error}"]

    def eligible(meta: dict) -> bool:
        return meta.get("toolchain_identity") == toolchain_identity

    for name in books:
        source = root / f"{name}.lisp"
        cert, port, fasl = (source.with_suffix(s) for s in (".cert", ".port", ".fasl"))
        if not cert.is_file():
            diffs.append(f"no certificate: {name}")
            continue
        try:
            found = entries(root, cache, name, eligible)
        except certs.UnreadableBook as error:
            diffs.append(f"{name}: {error}")
            continue
        have = content_hash(cert)
        same = [(d, m) for d, m in found if m.get("cert_sha256") == have]
        if not same:
            diffs.append(f"certificate not a cache pair for this closure and toolchain "
                         f"({len(found)} entries at the key): {name}")
            continue
        for _, meta in same:
            port_ok = (port.is_file() == bool(meta.get("has_port", port.is_file()))
                       and (not meta.get("port_sha256")
                            or (port.is_file() and content_hash(port) == meta["port_sha256"])))
            if meta.get("fasl_sha256"):
                fasl_ok = fasl.is_file() and content_hash(fasl) == meta["fasl_sha256"]
            else:  # certs.compiled_here: a loadable fasl made with these bytes
                fasl_ok = fasl.is_file() and fasl.stat().st_mtime >= cert.stat().st_mtime
            if port_ok and fasl_ok:
                break
        else:
            diffs.append(f"port or compiled file differs from the cache pair: {name}")
    return diffs


# --------------------------------------------------------------------- cli


def _say(lines: list[str]) -> None:
    for line in lines[:MAX_SHOWN]:
        print("  " + line)
    if len(lines) > MAX_SHOWN:
        print(f"  ... and {len(lines) - MAX_SHOWN} more")


def cmd_verify(arguments) -> int:
    root = Path(arguments.root).resolve()
    expected = json.loads(Path(arguments.expect).read_text(encoding="utf-8"))
    tree = tree_differences(root, expected)
    if tree:
        print(f"native_reuse: {root} is not the commit ({len(tree)} differences)")
        _say(tree)
        return 1
    import acl2_toolchain  # noqa: PLC0415
    import proof_artifacts  # noqa: PLC0415
    fingerprint = acl2_toolchain.fingerprint(Path(arguments.acl2))
    if not fingerprint.qualified or fingerprint.identity is None:
        print("native_reuse: unqualified ACL2 launcher: " + fingerprint.reason)
        return 1
    roots: list[str] = []
    for profile in arguments.profile:
        roots += [r for r in proof_artifacts.profile_roots(root, profile) if r not in roots]
    certs_diff = cert_differences(root, roots, fingerprint.identity, Path(arguments.cache))
    if certs_diff:
        print(f"native_reuse: {root}'s certificates differ from the cache's pairs "
              f"({len(certs_diff)} differences)")
        _say(certs_diff)
        return 1
    print(f"native_reuse: {root} is the commit ({len(expected)} tracked files) and holds "
          f"the cache pair of every book of {len(roots)} roots")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("action", choices=("plan", "expect", "verify"))
    parser.add_argument("--repo")
    parser.add_argument("--rev")
    parser.add_argument("--box")
    parser.add_argument("--out")
    parser.add_argument("--root")
    parser.add_argument("--expect")
    parser.add_argument("--cache")
    parser.add_argument("--acl2")
    parser.add_argument("--profile", action="append", default=[])
    arguments = parser.parse_args(argv)
    try:
        if arguments.action == "plan":
            print(json.dumps(plan(Path(arguments.repo), arguments.rev, arguments.box)))
            return 0
        if arguments.action == "expect":
            Path(arguments.out).write_text(
                json.dumps(expected_tree(Path(arguments.repo), arguments.rev)), encoding="utf-8")
            return 0
        if not (arguments.root and arguments.expect and arguments.cache and arguments.acl2
                and arguments.profile):
            parser.error("verify takes --root --expect --cache --acl2 and --profile")
        return cmd_verify(arguments)
    except Refusal as refusal:
        print(f"native_reuse: {refusal}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
