#!/usr/bin/env python3
"""Acquire and load-check one coherent ACL2 certificate artifact set.

The selected native image declaration and deployed ACL2 entry points are
the sources of the required root books. A candidate set binds their complete
local include closure to one ACL2 toolchain and compatible certificate
post-alists, possibly drawn from several origins. ACL2 then loads the roots;
an uncertified warning or ACL2 error rejects the set and the next complete
set is tried.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs  # noqa: E402
import acl2_toolchain  # noqa: E402


@dataclass(frozen=True)
class NativeProfile:
    name: str
    build: str
    image: str
    entrypoints: tuple[str, ...]


PROFILES = {
    "default": NativeProfile("default", "host/native/build.lisp", "build/fn-host",
                             ("host/owner-host.lisp",)),
    "dtn": NativeProfile("dtn", "host/native/build-dtn.lisp", "build/fn-host-dtn",
                         ("host/owner-host.lisp",)),
}

INCLUDE = re.compile(r'^\s*\(include-book\s+"([^"]+)"')
LOAD = re.compile(r'^\s*\(ld\s+"([^"]+)"')
FAILURE_MARKERS = ("ACL2 Error", "HARD ACL2 ERROR", "ABORTING from raw Lisp",
                   "Uncertified", "sub-book")
READY = "FN_ARTIFACT_SET_LOADED"


def forms(path: Path, pattern: re.Pattern[str]) -> list[str]:
    """String arguments of active top-level forms in these session scripts."""
    found = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = pattern.match(line)
        if match:
            found.append(match.group(1))
    return found


def profile_roots(root: Path, profile: str) -> list[str]:
    """Certified roots named by the native image and deployed entry points."""
    selected = PROFILES[profile]
    build = root / selected.build
    roots = set(forms(build, INCLUDE))
    pending = [(root / loaded).resolve() for loaded in forms(build, LOAD)]
    pending.extend((root / loaded).resolve() for loaded in selected.entrypoints)
    seen: set[Path] = set()
    while pending:
        host_file = pending.pop()
        if host_file in seen or not host_file.is_file():
            continue
        seen.add(host_file)
        for included in forms(host_file, INCLUDE):
            source = (host_file.parent / included).with_suffix(".lisp").resolve()
            roots.add(source.relative_to(root.resolve()).with_suffix("").as_posix())
        for loaded in forms(host_file, LOAD):
            pending.append((host_file.parent / loaded).resolve())
    return sorted(name.removesuffix(".lisp") for name in roots)


def load_driver(roots: list[str]) -> str:
    lines = ['(in-package "ACL2")']
    lines.extend('(include-book "{}")'.format(name) for name in roots)
    lines.extend(['(cw "{}~%")'.format(READY), '(good-bye)'])
    return "\n".join(lines) + "\n"


@dataclass
class LoadResult:
    ok: bool
    output: str
    returncode: int
    reason: str = ""


def validate(root: Path, acl2: Path, roots: list[str], timeout: int = 1800,
             run=subprocess.run) -> LoadResult:
    """Load the roots; ACL2 errors and uncertified-book warnings are fatal."""
    environment = dict(os.environ)
    environment.update({"ACL2_CUSTOMIZATION": "NONE", "ACL2_BOOK_HASH_ALISTP": "NIL"})
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    try:
        completed = run([str(acl2)], cwd=root, input=load_driver(roots).encode(),
                        env=environment, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT, timeout=timeout)
    except subprocess.TimeoutExpired as error:
        output = (error.stdout or b"").decode("utf-8", "replace")
        return LoadResult(False, output, 124,
                          "ACL2 load timed out after {}s".format(timeout))
    output = completed.stdout.decode("utf-8", "replace")
    markers = [marker for marker in FAILURE_MARKERS if marker in output]
    if completed.returncode != 0:
        reason = "ACL2 load exited {}".format(completed.returncode)
    elif markers:
        reason = "ACL2 load printed " + ", ".join(markers)
    elif READY not in output:
        reason = "ACL2 load did not print its ready marker"
    else:
        reason = ""
    return LoadResult(not reason, output, completed.returncode, reason)


@dataclass
class Acquisition:
    ok: bool
    profile: str
    roots: list[str]
    report: certs.Report | None = None
    rejected: list[str] = field(default_factory=list)
    attempts: list[str] = field(default_factory=list)
    reason: str = ""


def acquire(root: Path, cache: Path, acl2: Path, profile: str,
            timeout: int = 1800, run=subprocess.run) -> Acquisition:
    """Try complete current sets until ACL2 accepts one without warnings."""
    roots = profile_roots(root, profile)
    fingerprint = acl2_toolchain.fingerprint(acl2)
    if not fingerprint.qualified or fingerprint.identity is None:
        return Acquisition(
            False, profile, roots,
            reason="unqualified ACL2 launcher/core/runtime: " + fingerprint.reason)
    toolchain = fingerprint.identity
    candidates = certs.artifact_sets(root, cache, roots, toolchain, acl2=acl2)
    rejected: list[str] = []
    attempts: list[str] = []
    for candidate in candidates:
        if not candidate.complete:
            continue
        report = certs.install_artifact_set(
            root, cache, roots, toolchain_identity=toolchain, reject=rejected,
            acl2=acl2)
        if report.artifact_set is None:
            break
        loaded = validate(root, acl2, roots, timeout=timeout, run=run)
        attempts.append("{} {}: {}".format(
            report.artifact_set[:16], report.artifact_origin,
            "loaded" if loaded.ok else loaded.reason))
        if loaded.ok:
            report.rejected_sets = list(rejected)
            return Acquisition(True, profile, roots, report, rejected, attempts)
        rejected.append(report.artifact_set)

    # Do not leave the last rejected mixture looking usable to the caller.
    for name in certs.required_closure(root, roots):
        source = root / f"{name}.lisp"
        source.with_suffix(".cert").unlink(missing_ok=True)
        source.with_suffix(".port").unlink(missing_ok=True)
    reason = ("no complete current artifact set passed an ACL2 load"
              if candidates else "no current artifact set matches this ACL2 toolchain")
    return Acquisition(False, profile, roots, rejected=rejected,
                       attempts=attempts, reason=reason)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("roots", "acquire", "validate"))
    parser.add_argument("--profile", required=True, choices=sorted(PROFILES),
                        help="the actual native image declaration to cover")
    parser.add_argument("--root", default=str(ROOT))
    parser.add_argument("--cache", default=None)
    parser.add_argument("--acl2", default=os.environ.get("FN_ACL2", "acl2"))
    parser.add_argument("--timeout", type=int, default=1800)
    arguments = parser.parse_args(argv)
    root = Path(arguments.root).resolve()
    roots = profile_roots(root, arguments.profile)
    if arguments.action == "roots":
        print("\n".join(roots))
        return 0
    acl2 = Path(arguments.acl2).expanduser().resolve()
    if not acl2.is_file():
        print("proof_artifacts: ACL2 executable is absent: {}".format(acl2),
              file=sys.stderr)
        return 2
    if arguments.action == "validate":
        loaded = validate(root, acl2, roots, timeout=arguments.timeout)
        print("profile={} image={} roots={} result={}".format(
            arguments.profile, PROFILES[arguments.profile].image, len(roots),
            "loaded" if loaded.ok else loaded.reason))
        return 0 if loaded.ok else 1

    cache = (Path(arguments.cache).expanduser() if arguments.cache
             else certs.cache_directory())
    result = acquire(root, cache, acl2, arguments.profile,
                     timeout=arguments.timeout)
    for attempt in result.attempts:
        print("attempt " + attempt)
    if not result.ok or result.report is None:
        print("profile={} image={} result={} rejected={}".format(
            result.profile, PROFILES[result.profile].image, result.reason,
            len(result.rejected)))
        return 1
    report = result.report
    print("profile={} image={} artifact-set={} origin={} books={} source={} "
          "toolchain={} rejected={}".format(
              result.profile, PROFILES[result.profile].image,
              report.artifact_set, report.artifact_origin, report.books,
              report.source_identity, report.toolchain_identity,
              len(result.rejected)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
