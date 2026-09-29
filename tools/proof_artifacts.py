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
sys.path.insert(0, str(Path(__file__).resolve().parent / "extract"))
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
                   "Uncertified", "sub-book", "FN_IMAGE_WORLD_OPEN")
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
    """Certified roots named by the native image and deployed entry points,
    in the image's own load order: the build script's forms in sequence, each
    `ld` followed where it occurs, then the entry points; a root keeps its
    first place.  The order is load-bearing: an attachment book (the payload
    arena's byte array, books/payload-arena-attach) must be included before
    any book that introduces the generic it attaches (ACL2 refuses the
    attach-stobj otherwise), exactly as host/native/build.lisp orders it, so
    the artifact check loads what the image loads in the order it loads it."""
    selected = PROFILES[profile]
    base = root.resolve()
    ordered: list[str] = []
    named: set[str] = set()
    seen: set[Path] = set()

    def add(name: str) -> None:
        name = name.removesuffix(".lisp")
        if name not in named:
            named.add(name)
            ordered.append(name)

    def walk(script: Path, relative_to: Path, top: bool) -> None:
        script = script.resolve()
        if script in seen or not script.is_file():
            return
        seen.add(script)
        for line in script.read_text(encoding="utf-8").splitlines():
            included = INCLUDE.match(line)
            if included:
                if top:
                    add(included.group(1))
                else:
                    source = (relative_to / included.group(1)).with_suffix(".lisp").resolve()
                    add(source.relative_to(base).with_suffix("").as_posix())
                continue
            loaded = LOAD.match(line)
            if loaded:
                target = (root / loaded.group(1)) if top else (relative_to / loaded.group(1))
                walk(target, target.resolve().parent, False)

    walk(root / selected.build, root, True)
    for entry in selected.entrypoints:
        walk(root / entry, (root / entry).resolve().parent, False)
    return ordered


def load_driver(roots: list[str]) -> str:
    """Include the roots.  When the first is the image's umbrella book
    (tools/extract/world.py), the rest follow with the compiler off, as in
    the build script: each is then redundant and loads nothing (a top-level
    include-book reloads its closure's compiled files, and each load of a
    constrained stub takes a TLS index SBCL never frees), and the closure
    check prints FN_IMAGE_WORLD_OPEN if one of them added a book."""
    import world  # noqa: PLC0415 (tools/extract/ is on sys.path above)
    umbrella = bool(roots) and roots[0] in world.UMBRELLAS.values()
    lines = ['(in-package "ACL2")']
    for index, name in enumerate(roots):
        lines.append('(include-book "{}")'.format(name))
        if umbrella and index == 0:
            lines.extend(world.PROLOGUE)
    if umbrella:
        lines.extend(world.EPILOGUE)
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
    import acl2_slots  # noqa: PLC0415 (tools/ is on sys.path above)
    try:
        # The machine's ACL2 pool (and, on the laptop, its heap cap) (PKT-162).
        with acl2_slots.tree_slot("proof_artifacts validate"):
            completed = run([str(acl2)], cwd=root, input=load_driver(roots).encode(),
                            env=acl2_slots.acl2_environment(), stdout=subprocess.PIPE,
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
            timeout: int = 1800, run=subprocess.run,
            load_acl2: Path | None = None) -> Acquisition:
    """Try complete current sets until ACL2 accepts one without warnings.

    ACL2 (the certifying toolchain) names the artifact sets; LOAD_ACL2 (the
    launcher the image is built with, default ACL2) loads them: the served
    world is past SBCL's default --tls-limit (arena-store-7, 2026-09-28:
    "Thread local storage exhausted" loading the compiled world), and the
    image build already runs the tls64k wrapper."""
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
        loaded = validate(root, load_acl2 or acl2, roots, timeout=timeout, run=run)
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
    parser.add_argument("--load-acl2", default=None,
                        help="the launcher that LOADS the set (default --acl2); "
                             "the image build's wrapper")
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
    load_acl2 = (Path(arguments.load_acl2).expanduser().resolve()
                 if arguments.load_acl2 else None)
    if arguments.action == "validate":
        loaded = validate(root, load_acl2 or acl2, roots, timeout=arguments.timeout)
        print("profile={} image={} roots={} result={}".format(
            arguments.profile, PROFILES[arguments.profile].image, len(roots),
            "loaded" if loaded.ok else loaded.reason))
        return 0 if loaded.ok else 1

    cache = (Path(arguments.cache).expanduser() if arguments.cache
             else certs.cache_directory())
    result = acquire(root, cache, acl2, arguments.profile,
                     timeout=arguments.timeout, load_acl2=load_acl2)
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
