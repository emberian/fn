#!/usr/bin/env python3
"""A saved ACL2 image of the Python bridge's boot, built once per closure digest.

Every `Acl2Store` used to start a bare `acl2` and replay its boot: include
`books/replay` and three attachment books, then `ld` five host files, about
170 certified books in all.  On the laptop no book in that closure has a
compiled file for the local runtime (the certificate cache's `.fasl`s are
Linux SBCL's), so every boot recompiled every definition: 4.3 s on a quiet
machine, about 90 s when six unpooled bridges shared it (the python-store-f8
rerun), and every CLI invocation of `tools/run_store.py` paid it once or
twice.  The store modules spent nearly all of their 1,900 s there
(`planning/evidence/test-latency-2026-09-25.md`).

This module runs that same boot once, through the bridge's own call path
(so an ACL2 error in any boot form fails the build exactly as it failed the
boot), then `save-exec`s the session.  An image starts in about 0.1 s.

Identity.  An image is reused only when every input that could change what
the boot produces is unchanged: the boot forms themselves, and for every
book and host file the boot reaches through `include-book` and `ld`, its
source, certificate and portcullis bytes, and the ACL2 launcher chain
(launcher scripts by content, the saved core and Lisp runtime by path, size
and modification time).  The digest names the directory; a changed input is
a different directory, never a stale image.  Images live under the worktree
(`build/bridge-image/<kind>-<digest>/`) because the saved world records the
worktree's absolute book paths.

`FN_BRIDGE_IMAGE=0` disables the image and boots from the sources, which is
the path the build itself takes.  A failed build raises; it never falls back
to a slow boot silently.
"""

from __future__ import annotations

import contextlib
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
IMAGE_DIRECTORY = ROOT / "build" / "bridge-image"
SCHEMA = "fn-bridge-image-v1"
# Images kept per kind after a build: the new one and its predecessor, which a
# process started a moment ago may still be mapping.
KEEP_PER_KIND = 2
# How long a build may take.  The boot is about 6 s on the laptop; this is a
# refutation bound for a wedged ACL2, not a budget.
BUILD_TIMEOUT_SECONDS = 600.0

LD = ' :ld-error-action :return :ld-error-triples t)'

# The store bridge's boot, in order.  `run_store.Acl2Store` sends exactly
# these when no image is used; the image is these forms, saved.
STORE_FORMS = (
    '(include-book "books/replay")',
    # Every codec seam's attachment: the books call the constrained
    # encoders and decoders; this makes them evaluate.
    '(include-book "books/codec-attach")',
    # The record encoder's attachment over the concrete recognizer.
    '(include-book "books/records-attach-concrete")',
    # The store bridge's record dispatchers call the concrete twins.
    '(include-book "books/records-concrete")',
    '(ld "host/store-host.lisp"' + LD,
    '(ld "host/store-node-host.lisp"' + LD,
    '(ld "host/checkpoint-host.lisp"' + LD,
    '(ld "host/anchor-host.lisp"' + LD,
    '(ld "host/config-host.lisp"' + LD,
)

# The owner bridge (`run_owner.Acl2Owner`) loads these after the store's.
OWNER_FORMS = STORE_FORMS + (
    # books/owner-fault includes books/owner; `fn-own-fault' is what the
    # host-fault boundary in `Owner.guard' calls.
    '(include-book "books/owner-fault")',
    '(include-book "books/codec-attach")',
    '(ld "host/owner-host.lisp"' + LD,
    '(ld "host/feed-filename-host.lisp"' + LD,
)

# The BP ingress bridge (`run_bp_ingress.Acl2BpIngress`) loads these after
# the store's; the native BP tests author their requests through it.
BP_INGRESS_FORMS = STORE_FORMS + (
    '(include-book "books/bp-ingress")',
    '(include-book "books/codec-attach")',
    '(ld "host/bp-ingress-host.lisp"' + LD,
)

KINDS = {"store": STORE_FORMS, "owner": OWNER_FORMS, "bp-ingress": BP_INGRESS_FORMS}

_INCLUDE = re.compile(r'\(\s*include-book\s+"([^"]+)"([^()]*)\)', re.IGNORECASE)
_LD = re.compile(r'\(\s*ld\s+"([^"]+)"', re.IGNORECASE)
_COMMENT = re.compile(r";[^\n]*")
_BLOCK_COMMENT = re.compile(r"#\|.*?\|#", re.DOTALL)
_ABSOLUTE_PATH = re.compile(r"/[A-Za-z0-9_./+@%-]+")
_MAX_LAUNCHER_BYTES = 64 * 1024


def enabled() -> bool:
    return os.environ.get("FN_BRIDGE_IMAGE", "1") not in ("0", "", "no", "off")


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def _references(path: Path) -> list[Path]:
    """The books and files one source reaches: `include-book` and `ld`.

    A `:dir` include names a system book, which the toolchain identity
    covers.  `ld` resolves against the loading file's directory, as ACL2's
    connected book directory does during the `ld`.
    """
    text = path.read_text(encoding="utf-8", errors="replace")
    text = _COMMENT.sub("", _BLOCK_COMMENT.sub("", text))
    found = []
    for match in _INCLUDE.finditer(text):
        if ":dir" in match.group(2).lower():
            continue
        found.append((path.parent / (match.group(1) + ".lisp")).resolve())
    for match in _LD.finditer(text):
        found.append((path.parent / match.group(1)).resolve())
    return found


def _form_roots(forms) -> list[Path]:
    roots = []
    for form in forms:
        match = _INCLUDE.match(form)
        if match:
            roots.append((ROOT / (match.group(1) + ".lisp")).resolve())
            continue
        match = _LD.match(form)
        if match:
            roots.append((ROOT / match.group(1)).resolve())
    return roots


def closure(forms) -> list[Path]:
    """Every repository source the boot forms reach, sorted."""
    seen: set[Path] = set()
    stack = _form_roots(forms)
    while stack:
        path = stack.pop()
        if path in seen:
            continue
        seen.add(path)
        if path.is_file():
            stack.extend(_references(path))
    return sorted(seen)


def _launcher_identity(executable: Path) -> list:
    """The launcher chain: small scripts by content, large files by stat.

    Follows absolute paths named in a launcher script two levels deep
    (Homebrew's `acl2` wrapper names `saved_acl2`, which names the Lisp
    runtime and the saved core).  A core is hundreds of megabytes; its path,
    size and modification time identify it for a local cache.
    """
    identity = []
    seen: set[str] = set()
    frontier = [executable]
    for _depth in range(3):
        following = []
        for path in frontier:
            key = str(path)
            if key in seen or not path.exists() or path.is_dir():
                continue
            seen.add(key)
            status = path.stat()
            if status.st_size <= _MAX_LAUNCHER_BYTES:
                data = path.read_bytes()
                identity.append([key, "sha256", hashlib.sha256(data).hexdigest()])
                if data[:2] == b"#!":
                    for word in _ABSOLUTE_PATH.findall(data.decode("utf-8", "replace")):
                        following.append(Path(word))
            else:
                identity.append([key, "stat", status.st_size, status.st_mtime_ns])
        frontier = following
    return identity


def resolve_acl2(environment: dict) -> Path:
    configured = environment.get("FN_ACL2", "acl2")
    if os.sep in configured:
        return Path(configured).expanduser().resolve()
    found = shutil.which(configured, path=environment.get("PATH"))
    if found is None:
        raise FileNotFoundError(f"no ACL2 executable {configured!r} on PATH")
    return Path(found).resolve()


def digest(kind: str, environment: dict) -> str:
    forms = KINDS[kind]
    files = []
    for path in closure(forms):
        entry = [str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)]
        if not path.is_file():
            entry.append("absent")
        else:
            entry.append(_sha256(path))
            if path.suffix == ".lisp":
                for suffix in (".cert", ".port"):
                    companion = path.with_suffix(suffix)
                    entry.append(_sha256(companion) if companion.is_file() else "absent")
        files.append(entry)
    material = {
        "schema": SCHEMA,
        "kind": kind,
        "forms": list(forms),
        "files": files,
        "acl2": _launcher_identity(resolve_acl2(environment)),
        "environment": {name: environment.get(name) for name in
                        ("ACL2_CUSTOMIZATION", "ACL2_BOOK_HASH_ALISTP")},
    }
    encoded = json.dumps(material, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def image_path(kind: str, image_digest: str) -> Path:
    return IMAGE_DIRECTORY / f"{kind}-{image_digest[:24]}" / "fn-bridge"


def _complete(path: Path) -> bool:
    return path.is_file() and path.with_name("fn-bridge.core").is_file() \
        and path.with_name("DONE").is_file()


@contextlib.contextmanager
def _build_lock():
    IMAGE_DIRECTORY.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(IMAGE_DIRECTORY / ".lock", os.O_RDWR | os.O_CREAT, 0o644)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _prune(kind: str, keep: Path) -> None:
    """Remove this kind's older images, keeping `keep` and its newest peers.

    Called under the build lock, so an incomplete directory here is a crashed
    build's.  An unlinked core stays mapped by any process still using it."""
    others = sorted(
        (entry for entry in IMAGE_DIRECTORY.glob(f"{kind}-*")
         if entry.is_dir() and entry != keep),
        key=lambda entry: entry.stat().st_mtime, reverse=True)
    kept = 0
    for entry in others:
        if kept < KEEP_PER_KIND - 1 and _complete(entry / "fn-bridge"):
            kept += 1
            continue
        shutil.rmtree(entry, ignore_errors=True)


def error_summary(transcript: str, limit: int = 2000) -> str:
    """The ACL2 error paragraphs of a failed boot form, bounded.

    The refused form's reply is the whole `ld` transcript (81 KiB for the
    owner boot); a caller that prints it into a pipe can fill the pipe, and
    a reader needs the error, not the transcript.
    """
    lines = transcript.splitlines()
    kept: list[str] = []
    for index, line in enumerate(lines):
        if "ACL2 Error" in line or "HARD ACL2 ERROR" in line.upper():
            kept.extend(lines[index:index + 6])
    text = " ".join(" ".join(kept).split()) or " ".join(transcript.split())[-limit:]
    return text[:limit]


def build(kind: str, image_digest: str, environment: dict) -> Path:
    """Boot from the sources through the bridge's checks, then save-exec."""
    from tools import run_store

    target = image_path(kind, image_digest)
    # The launcher save-exec writes names its core by absolute path, so the
    # image is written where it will be used; `DONE`, written last, is what
    # makes it complete (`_complete`), and the build lock excludes a reader
    # of a half-written one in this worktree.
    staging = target.parent
    shutil.rmtree(staging, ignore_errors=True)
    staging.mkdir(parents=True)
    started = time.monotonic()
    try:
        session = run_store.Acl2Store(_forms=KINDS[kind], _use_image=False, _reset=False)
    except run_store.StoreError as error:
        shutil.rmtree(staging, ignore_errors=True)
        raise RuntimeError(f"bridge image build for {kind} failed: "
                           f"{error_summary(str(error))}") from None
    try:
        # save-exec refuses inside the read-eval-print loop.
        session.proc.stdin.write(
            b':q\n(save-exec "' + str(staging / "fn-bridge").encode() + b'" "fn bridge '
            + kind.encode() + b' ' + image_digest[:24].encode() + b'")\n')
        session.proc.stdin.close()
        try:
            session.proc.wait(timeout=BUILD_TIMEOUT_SECONDS)
        except subprocess.TimeoutExpired:
            session.proc.kill()
            session.proc.wait()
            raise
        if session.proc.stdout is not None:
            session.proc.stdout.close()
    finally:
        session.closed = True
        session.release_slot()
    if not (staging / "fn-bridge").is_file() or not (staging / "fn-bridge.core").is_file():
        shutil.rmtree(staging, ignore_errors=True)
        raise RuntimeError(f"bridge image build for {kind} wrote no image "
                           f"(ACL2 exit {session.proc.returncode})")
    (staging / "DONE").write_text(json.dumps({
        "kind": kind, "digest": image_digest,
        "seconds": round(time.monotonic() - started, 3)}) + "\n")
    _prune(kind, target.parent)
    return target


def ensure(kind: str, environment: dict) -> Path:
    """The image for this closure, building it under the lock if absent."""
    image_digest = digest(kind, environment)
    target = image_path(kind, image_digest)
    if _complete(target):
        return target
    with _build_lock():
        if _complete(target):
            return target
        print(f"fn: building the {kind} bridge image {image_digest[:12]} "
              f"(once per closure digest)", file=sys.stderr, flush=True)
        return build(kind, image_digest, environment)


def main(argv: list[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("command", choices=("digest", "ensure", "closure"))
    parser.add_argument("--kind", choices=sorted(KINDS), default="store")
    arguments = parser.parse_args(argv)
    sys.path.insert(0, str(ROOT))
    from tools import run_store

    environment = run_store.acl2_environment()
    if arguments.command == "digest":
        print(digest(arguments.kind, environment))
    elif arguments.command == "closure":
        for path in closure(KINDS[arguments.kind]):
            print(path.relative_to(ROOT) if path.is_relative_to(ROOT) else path)
    else:
        started = time.monotonic()
        path = ensure(arguments.kind, environment)
        print(f"{path} ({time.monotonic() - started:.2f} s)")
    return 0


if __name__ == "__main__":
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))
    sys.exit(main())
