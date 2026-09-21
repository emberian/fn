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


def _launcher_exec(path: Path, expected_sha256: str) -> tuple[Path, list[str], dict[str, str]]:
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
    environment: dict[str, str] = {}
    for number, line in enumerate(lines[1:], 2):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        # Quoted forwarding is the only expansion in the recognized subset.
        # Reject conservatively before shlex discards the quote information.
        without_forwarding = stripped.replace('"$@"', "").replace("'$@'", "")
        if "$" in without_forwarding or "`" in without_forwarding:
            raise ValueError(
                f"shell expansion is outside the recognized launcher subset "
                f"at {path}:{number}")
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
            name, value = words[1].split("=", 1)
            environment[name] = value
            continue
        index = 0
        while index < len(words) and ASSIGNMENT.fullmatch(words[index]):
            name, value = words[index].split("=", 1)
            environment[name] = value
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
    return found[0], found[1], environment


def _saved_core(arguments: list[str], launcher: Path) -> Path:
    """Recognize the bounded SBCL saved-image argument profile."""
    if not arguments or arguments[-1] != "$@":
        raise ValueError(f"ACL2 launcher must end with quoted argument forwarding: {launcher}")
    arguments = arguments[:-1]
    value_options = {
        "--tls-limit": lambda value: value.isdecimal(),
        "--dynamic-space-size": lambda value: value.isdecimal(),
        "--control-stack-size": lambda value: value.isdecimal(),
        "--userinit": lambda value: value == "/dev/null",
        "--sysinit": lambda value: value == "/dev/null",
        "--eval": lambda value: value == "(acl2::sbcl-restart)",
    }
    flag_options = {
        "--disable-ldb", "--disable-debugger", "--lose-on-corruption",
        "--end-runtime-options", "--noinform", "--no-sysinit", "--no-userinit",
    }
    core: Path | None = None
    evals = 0
    index = 0
    while index < len(arguments):
        option = arguments[index]
        if option == "--core":
            if core is not None or index + 1 >= len(arguments):
                raise ValueError(f"ACL2 launcher must name exactly one saved core: {launcher}")
            core = Path(arguments[index + 1])
            if not core.is_absolute():
                raise ValueError(f"ACL2 saved core is not an absolute path: {core}")
            index += 2
            continue
        if option in flag_options:
            index += 1
            continue
        check = value_options.get(option)
        if check is None or index + 1 >= len(arguments) or not check(arguments[index + 1]):
            raise ValueError(f"unrecognized ACL2 runtime argument {option!r}: {launcher}")
        if option == "--eval":
            evals += 1
            if evals > 1:
                raise ValueError(f"multiple ACL2 runtime evaluations: {launcher}")
        index += 2
    if core is None:
        raise ValueError(f"ACL2 launcher does not name a literal saved core: {launcher}")
    return core


def fingerprint(launcher: Path, max_wrappers: int = 1) -> Fingerprint:
    """Recognize a generated saved-image launcher and hash its actual inputs."""
    try:
        current = launcher.expanduser().resolve()
        launchers: list[dict[str, object]] = []
        seen: set[Path] = set()
        runtime: dict[str, object] | None = None
        core: dict[str, object] | None = None
        launcher_environment: list[dict[str, str]] = []
        for _ in range(max_wrappers + 1):
            if current in seen:
                raise ValueError(f"launcher recursion at {current}")
            seen.add(current)
            info = _file(current, "ACL2 launcher")
            launchers.append(info)
            executed, arguments, assignments = _launcher_exec(
                current, str(info["sha256"]))
            launcher_environment.append(assignments)
            if "--core" in arguments:
                core_path = _saved_core(arguments, current)
                runtime = _file(executed, "Lisp runtime")
                core = _file(core_path, "ACL2 saved core")
                break
            if arguments != ["$@"]:
                raise ValueError(
                    f"outer ACL2 wrapper has arguments other than quoted forwarding: "
                    f"{current}")
            current = executed
        if runtime is None or core is None:
            raise ValueError(
                f"unknown ACL2 launcher shape: no literal absolute --core after "
                f"{len(launchers)} wrapper(s)")
        effective_proof_environment = dict(PROOF_ENVIRONMENT)
        for assignments in launcher_environment:
            for name in effective_proof_environment:
                if name in assignments:
                    effective_proof_environment[name] = assignments[name]
        compatibility: dict[str, object] = {
            "schema": SCHEMA,
            "launcher_chain_sha256": [one["sha256"] for one in launchers],
            "core_sha256": core["sha256"],
            "runtime_sha256": runtime["sha256"],
            "proof_environment": effective_proof_environment,
            "launcher_environment": launcher_environment,
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
