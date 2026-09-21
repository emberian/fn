#!/usr/bin/env python3
"""Fingerprint the ACL2 launcher, saved core, Lisp runtime, and proof environment.

ACL2's generated ``saved_acl2`` is a shell launcher.  Hashing that small script
alone does not identify the hundreds-of-megabytes core it loads or the Lisp
runtime which interprets it.  This module recognizes the generated launcher
shape without executing it, follows at most one outer package-manager wrapper,
and binds all three content digests into the cache compatibility identity.

Unknown launcher shapes are reported as unqualified.  Callers may still run an
unqualified ACL2 for local evidence, but they must not publish or acquire a
reusable certificate set under a guessed identity.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys


SCHEMA = "fn-acl2-toolchain-v1"
PROOF_ENVIRONMENT = {
    "ACL2_CUSTOMIZATION": "NONE",
    "ACL2_BOOK_HASH_ALISTP": "NIL",
    "ACL2_SYSTEM_BOOKS": None,
}
EXEC = re.compile(r"\bexec\s+(['\"])(/[^'\"]+)\1(?P<args>[^\n]*)")
CORE = re.compile(r"(?:^|\s)--core\s+(['\"])(/[^'\"]+)\1(?:\s|$)")


def content_hash(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def stable_identity(value: object) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


@dataclass(frozen=True)
class Fingerprint:
    qualified: bool
    identity: str | None
    compatibility: dict[str, object] | None
    provenance: dict[str, object]
    reason: str = ""


def _file(path: Path, role: str) -> dict[str, object]:
    resolved = path.expanduser().resolve()
    if not resolved.is_file():
        raise ValueError(f"{role} is absent: {resolved}")
    return {
        "path": str(resolved),
        "sha256": content_hash(resolved),
        "size": resolved.stat().st_size,
    }


def fingerprint(launcher: Path, max_wrappers: int = 2) -> Fingerprint:
    """Recognize a generated saved-image launcher and hash its actual inputs."""
    try:
        current = launcher.expanduser().resolve()
        launchers: list[dict[str, object]] = []
        seen: set[Path] = set()
        runtime: dict[str, object] | None = None
        core: dict[str, object] | None = None
        for _ in range(max_wrappers + 1):
            if current in seen:
                raise ValueError(f"launcher recursion at {current}")
            seen.add(current)
            info = _file(current, "ACL2 launcher")
            try:
                text = current.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as error:
                raise ValueError(f"unknown non-text ACL2 launcher {current}: {error}")
            first = text.splitlines()[0] if text.splitlines() else ""
            if not first.startswith("#!") or not any(
                    shell in first for shell in ("/sh", "/bash")):
                raise ValueError(f"unknown ACL2 launcher interpreter: {first!r}")
            match = EXEC.search(text)
            if match is None:
                raise ValueError(f"unknown ACL2 launcher shape: no absolute exec in {current}")
            launchers.append(info)
            executed = Path(match.group(2)).resolve()
            core_match = CORE.search(match.group("args"))
            if core_match is not None:
                runtime = _file(executed, "Lisp runtime")
                core = _file(Path(core_match.group(2)), "ACL2 saved core")
                break
            current = executed
        if runtime is None or core is None:
            raise ValueError(
                f"unknown ACL2 launcher shape: no literal absolute --core after "
                f"{len(launchers)} wrapper(s)")
        compatibility: dict[str, object] = {
            "schema": SCHEMA,
            "launcher_chain_sha256": [one["sha256"] for one in launchers],
            "core_sha256": core["sha256"],
            "runtime_sha256": runtime["sha256"],
            "proof_environment": PROOF_ENVIRONMENT,
        }
        provenance = {
            "status": "qualified",
            "schema": SCHEMA,
            "launchers": launchers,
            "core": core,
            "runtime": runtime,
            "compatibility": compatibility,
        }
        return Fingerprint(True, stable_identity(compatibility), compatibility,
                           provenance)
    except (OSError, ValueError) as error:
        path = launcher.expanduser().resolve()
        provenance: dict[str, object] = {
            "status": "unqualified",
            "schema": SCHEMA,
            "launcher": str(path),
            "reason": str(error),
        }
        if path.is_file():
            provenance["launcher_sha256"] = content_hash(path)
            provenance["launcher_size"] = path.stat().st_size
        return Fingerprint(False, None, None, provenance, str(error))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=("identity", "describe"))
    parser.add_argument("launcher")
    arguments = parser.parse_args(argv)
    found = fingerprint(Path(arguments.launcher))
    if arguments.action == "describe":
        print(json.dumps(found.provenance, indent=2, sort_keys=True))
    elif found.identity:
        print(found.identity)
    if not found.qualified:
        print(f"acl2_toolchain: unqualified launcher: {found.reason}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
