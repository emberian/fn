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
import shlex
import sys


SCHEMA = "fn-acl2-toolchain-v1"
PROOF_ENVIRONMENT = {
    "ACL2_CUSTOMIZATION": "NONE",
    "ACL2_BOOK_HASH_ALISTP": "NIL",
    "ACL2_SYSTEM_BOOKS": None,
}
MAX_LAUNCHER_BYTES = 64 * 1024
ASSIGNMENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*=.*", re.DOTALL)


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


def _shell_words(line: str) -> list[str]:
    lexer = shlex.shlex(line, posix=True, punctuation_chars=";&|<>")
    lexer.commenters = "#"
    lexer.whitespace_split = True
    return list(lexer)


def _launcher_exec(path: Path, expected_sha256: str) -> tuple[Path, list[str]]:
    """Parse the deliberately small launcher subset without running a shell.

    Accepted files contain a shell shebang, blank/comment lines, literal
    ``export NAME=value`` lines, and one final ``exec`` command.  Assignments
    may prefix that command, as in Homebrew's ACL2 wrapper.  Anything more
    expressive remains unqualified instead of being evaluated to discover an
    identity.
    """
    with path.open("rb") as source:
        raw = source.read(MAX_LAUNCHER_BYTES + 1)
    if len(raw) > MAX_LAUNCHER_BYTES:
        raise ValueError(
            f"ACL2 launcher exceeds {MAX_LAUNCHER_BYTES} byte parse bound: {path}")
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise ValueError(f"ACL2 launcher changed while it was fingerprinted: {path}")
    try:
        text = raw.decode("utf-8")
    except UnicodeError as error:
        raise ValueError(f"unknown non-text ACL2 launcher {path}: {error}")
    lines = text.splitlines()
    first = lines[0] if lines else ""
    if not first.startswith("#!") or not any(
            shell in first for shell in ("/sh", "/bash")):
        raise ValueError(f"unknown ACL2 launcher interpreter: {first!r}")

    found: tuple[Path, list[str]] | None = None
    for number, line in enumerate(lines[1:], 2):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        try:
            words = _shell_words(stripped)
        except ValueError as error:
            raise ValueError(f"unknown ACL2 launcher syntax at {path}:{number}: {error}")
        if not words:
            continue
        if any(set(word) <= set(";&|<>") for word in words):
            raise ValueError(
                f"shell control operator is outside the recognized launcher "
                f"subset at {path}:{number}")
        if words[0] == "export" and len(words) == 2 and ASSIGNMENT.fullmatch(words[1]):
            if found is not None:
                raise ValueError(f"command follows exec at {path}:{number}")
            continue
        index = 0
        while index < len(words) and ASSIGNMENT.fullmatch(words[index]):
            index += 1
        if index >= len(words) or words[index] != "exec" or index + 1 >= len(words):
            raise ValueError(f"unknown ACL2 launcher command at {path}:{number}")
        if found is not None:
            raise ValueError(f"multiple exec commands in ACL2 launcher {path}")
        executable = Path(words[index + 1])
        if not executable.is_absolute():
            raise ValueError(f"ACL2 launcher exec is not an absolute path: {executable}")
        found = (executable.resolve(), words[index + 2:])
    if found is None:
        raise ValueError(f"unknown ACL2 launcher shape: no literal absolute exec in {path}")
    return found


def fingerprint(launcher: Path, max_wrappers: int = 1) -> Fingerprint:
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
            launchers.append(info)
            executed, arguments = _launcher_exec(current, str(info["sha256"]))
            if "--core" in arguments:
                core_index = arguments.index("--core")
                if core_index + 1 >= len(arguments):
                    raise ValueError(f"ACL2 launcher has --core without a path: {current}")
                core_path = Path(arguments[core_index + 1])
                if not core_path.is_absolute():
                    raise ValueError(
                        f"ACL2 saved core is not an absolute path: {core_path}")
                runtime = _file(executed, "Lisp runtime")
                core = _file(core_path, "ACL2 saved core")
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
