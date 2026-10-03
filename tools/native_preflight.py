#!/usr/bin/env python3
"""Reuse successful static native gates over identical source and Python inputs.

Only these three source scanners are eligible. ACL2 admission, certificates,
host loading, image identity and runtime tests never use these receipts.
All repository source is hashed, including untracked files, except generated
build products and evidence payloads (the evidence index is included). The
scanners read source, not those excluded products. External/directory symlinks
or a concurrent source change prevent filing a reusable result. Keep this input
contract in sync when changing a scanner to consume new external inputs.
Use a fixed Python installation; its executable/version identify its standard
library, which is not separately archived here. User/site hooks are disabled.
Place receipts outside the source tree or under its excluded build directory.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

GATES = {
    "world-check": ("tools/extract/world.py", "--check"),
    "interfaces-check": ("tools/interface_emit.py", "--check"),
    "host-books": ("tools/host_check.py", "--books"),
}
SCHEMA = 1
PYTHON_FLAGS = ("-I", "-S")  # No user/site startup hooks or external import paths.
IGNORED_DIRS = {".git", "__pycache__", ".pytest_cache"}
IGNORED_SUFFIXES = {".cert", ".fasl", ".port", ".acl2x", ".pyc"}


class Uncacheable(Exception):
    pass


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def identity(root: Path, gate: str) -> str:
    """Path-independent source identity; no caller-supplied revision is trusted."""
    root = root.resolve()
    h = hashlib.sha256()
    def walk_error(exc):
        raise Uncacheable("source directory unavailable") from exc

    for directory, dirs, files in os.walk(root, followlinks=False, onerror=walk_error):
        relative = Path(directory).relative_to(root)
        dirs[:] = sorted(d for d in dirs if d not in IGNORED_DIRS
                         and relative / d != Path("build")
                         and relative / d != Path("planning/evidence"))
        for name in dirs + sorted(files):
            path = Path(directory) / name
            if path.is_symlink():
                try:
                    target = path.resolve(strict=True)
                except (OSError, RuntimeError) as exc:
                    raise Uncacheable(f"unavailable source symlink: {path.relative_to(root)}") from exc
                if name in dirs or not target.is_relative_to(root):
                    raise Uncacheable(f"external/directory source symlink: {path.relative_to(root)}")
        for name in sorted(files):
            path = Path(directory) / name
            if path.name == ".git" or path.suffix in IGNORED_SUFFIXES:
                continue
            rel = path.relative_to(root).as_posix().encode()
            try:
                data = (b"link\0" + os.readlink(path).encode() + b"\0" + path.read_bytes()
                        if path.is_symlink() else b"file\0" + path.read_bytes())
            except OSError as exc:
                raise Uncacheable(f"source unavailable: {path.relative_to(root)}") from exc
            h.update(len(rel).to_bytes(8, "big") + rel)
            h.update(len(data).to_bytes(8, "big") + hashlib.sha256(data).digest())
    # The source scanners use the standard library. Interpreter identity and
    # Python import/locale configuration are inputs; per-run scratch locations,
    # test-image variables and unrelated authentication variables are not.
    env = {k: v for k, v in os.environ.items()
           if k.startswith(("PYTHON", "LC_")) or k in {"LANG", "PATH"}}
    runtime = {"schema": SCHEMA, "gate": gate, "command": GATES[gate],
               "python_flags": PYTHON_FLAGS,
               "python": str(Path(sys.executable).resolve()), "version": sys.version,
               "executable_sha256": digest(Path(sys.executable).read_bytes()),
               "environment": env}
    h.update(json.dumps(runtime, sort_keys=True).encode())
    return h.hexdigest()


def atomic_write(path: Path, data: bytes) -> None:
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as out:
        tmp = Path(out.name)
        out.write(data)
        out.flush()
        os.fsync(out.fileno())
    os.replace(tmp, path)


def cached_output(cache: Path, key: str, gate: str) -> bytes | None:
    try:
        receipt = json.loads((cache / f"{key}.json").read_bytes())
        output = (cache / f"{key}.log").read_bytes()
        if (receipt.get("schema") == SCHEMA and receipt.get("key") == key
                and receipt.get("gate") == gate and receipt.get("exit_code") == 0
                and receipt.get("output_sha256") == digest(output)):
            return output
    except (OSError, ValueError, AttributeError):
        pass
    return None


def run_gate(root: Path, cache: Path, gate: str, *, force: bool = False,
             runner=subprocess.run, output=None) -> int:
    output = output or sys.stdout.buffer
    command = [sys.executable, *PYTHON_FLAGS, *GATES[gate]]
    try:
        key = identity(root, gate)
    except Uncacheable as exc:
        output.write(f"preflight: no reusable receipt ({exc})\n".encode())
        result = runner(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output.write(result.stdout)
        return result.returncode
    cache.mkdir(parents=True, exist_ok=True)
    with (cache / f"{key}.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            stable = identity(root, gate) == key
        except Uncacheable:
            stable = False
        if not stable:
            output.write(b"preflight: source changed while acquiring receipt lock\n")
            return 2
        # Another invocation may have filed this exact gate while we waited.
        saved = None if force else cached_output(cache, key, gate)
        if saved is not None:
            output.write(f"preflight: REUSED {gate} {key}\n".encode())
            output.write(saved)
            return 0
        started = time.monotonic()
        result = runner(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output.write(result.stdout)
        if result.returncode:
            return result.returncode
        try:
            stable = identity(root, gate) == key
        except Uncacheable:
            stable = False
        if not stable:
            output.write(b"preflight: source changed during check; result not reusable\n")
            return 2
        receipt = {"schema": SCHEMA, "key": key, "gate": gate, "exit_code": 0,
                   "output_sha256": digest(result.stdout), "source_root": str(root),
                   "elapsed_seconds": round(time.monotonic() - started, 3)}
        atomic_write(cache / f"{key}.log", result.stdout)
        atomic_write(cache / f"{key}.json", json.dumps(receipt, sort_keys=True).encode())
        output.write(f"preflight: FILED {gate} {key}\n".encode())
        return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gate", choices=GATES, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--force", action="store_true", help="run even with a matching receipt")
    args = parser.parse_args()
    return run_gate(Path(__file__).resolve().parents[1], args.cache.resolve(),
                    args.gate, force=args.force)


if __name__ == "__main__":
    raise SystemExit(main())
