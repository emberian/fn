#!/usr/bin/env python3
"""Check an externally pinned product binding before starting its runtime.

This checks artifact identity and exact launch geometry, never qualification.
The installer must supply a digest-pinned binding and a capsule export from the
SAME build as the saved core. The core still owns unit admission. Files must be
in an immutable installation for the check-to-exec interval; this is not a
defence against a concurrent privileged writer or a proof of compilation.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import stat
import sys


class BindingError(ValueError):
    pass


ROLES = {"launcher", "runtime", "core", "source_manifest", "profile", "capsule"}
OPTIONS = {"--tls-limit": "tls_limit", "--dynamic-space-size": "dynamic_space_bytes",
           "--control-stack-size": "control_stack_bytes"}


def digest(path):
    """Bound-memory hash; reject a file that changes during this read."""
    with path.open("rb") as stream:
        before = os.fstat(stream.fileno())
        if not stat.S_ISREG(before.st_mode):
            raise BindingError("artifact is not a regular file: " + str(path))
        result = hashlib.sha256()
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
        after = os.fstat(stream.fileno())
    fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
    if any(getattr(before, f) != getattr(after, f) for f in fields):
        raise BindingError("artifact changed while hashing: " + str(path))
    return result.hexdigest()


def checked_bytes(path, expected):
    if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
        raise BindingError("missing or malformed expected SHA256")
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise BindingError("artifact digest mismatch: " + str(path))
    return data


def number(flag, value):
    match = re.fullmatch(r"([0-9]+)(KB|MB|GB)?", value)
    if not match or int(match[1]) <= 0:
        raise BindingError("invalid runtime option: " + flag)
    if flag == "--tls-limit":
        if match[2]:
            raise BindingError("TLS limit is a count, not a byte size")
        return int(match[1])
    # SBCL's unsuffixed dynamic-space and control-stack sizes are MiB.
    return int(match[1]) * {None: 2**20, "KB": 2**10, "MB": 2**20, "GB": 2**30}[match[2]]


def parse_launcher(text):
    """Accept only core_launcher.py's literal shell form, without evaluating it."""
    lines = [line.strip() for line in text.splitlines()
             if line.strip() and not line.lstrip().startswith("#")]
    if len(lines) != 2 or not lines[0].startswith("export SBCL_HOME="):
        raise BindingError("unsupported product launcher form")
    home_words = shlex.split(lines[0])
    if len(home_words) != 2 or not home_words[1].startswith("SBCL_HOME="):
        raise BindingError("unsupported SBCL_HOME assignment")
    home = home_words[1].split("=", 1)[1]
    words = shlex.split(lines[1])
    if len(words) < 2 or words[0] != "exec":
        raise BindingError("launcher has no literal exec")
    runtime, rest = words[1], words[2:]
    geometry = {}
    while len(rest) >= 2 and rest[0] in OPTIONS:
        flag, value = rest[:2]
        if OPTIONS[flag] in geometry:
            raise BindingError("duplicate runtime option: " + flag)
        geometry[OPTIONS[flag]] = number(flag, value)
        rest = rest[2:]
    if set(geometry) != set(OPTIONS.values()):
        raise BindingError("all three runtime geometry options must be explicit")
    if len(rest) < 3 or rest[:2] != ["--disable-ldb", "--core"]:
        raise BindingError("unsupported runtime flags")
    core, tail = rest[2], rest[3:]
    expected = ["--noinform", "${SBCL_USER_ARGS}", "--end-runtime-options",
                "--no-userinit", "--no-sysinit", "--eval", "(cl-user::xl-toplevel)",
                "--disable-debugger", "--end-toplevel-options", "$@"]
    if tail != expected:
        raise BindingError("unsupported product entrypoint or flags")
    for path in (runtime, core, home):
        if not re.fullmatch(r"/[A-Za-z0-9_./+:-]+", path):
            raise BindingError("launcher paths must be literal absolute paths")
    # Construct an argv, never execute the shell or interpolate its environment.
    argv = words[1:]
    argv.remove("${SBCL_USER_ARGS}")
    argv.pop()  # literal $@ becomes only the separately supplied app arguments
    return runtime, core, home, geometry, argv


def resolve(binding_path, expected_sha256, user_runtime_args="", app_args=()):
    binding_path = Path(binding_path).resolve()
    binding = json.loads(checked_bytes(binding_path, expected_sha256))
    if (not isinstance(binding, dict) or type(binding.get("schema")) is not int
            or binding["schema"] != 1 or not isinstance(binding.get("artifacts"), dict)
            or set(binding["artifacts"]) != ROLES):
        raise BindingError("incomplete launch binding")
    paths = {}
    for role, record in binding["artifacts"].items():
        if not isinstance(record, dict):
            raise BindingError("invalid artifact record: " + role)
        path = Path(record["path"])
        path = (binding_path.parent / path).resolve() if not path.is_absolute() else path.resolve()
        expected = record.get("sha256")
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise BindingError("missing artifact digest: " + role)
        if digest(path) != expected:
            raise BindingError("artifact digest mismatch: " + role)
        paths[role] = path
    launcher = checked_bytes(paths["launcher"], binding["artifacts"]["launcher"]["sha256"]).decode()
    runtime, core, home, geometry, argv = parse_launcher(launcher)
    if Path(runtime).resolve() != paths["runtime"] or Path(core).resolve() != paths["core"]:
        raise BindingError("launcher selects different runtime or core")
    expected_options = binding.get("options")
    if (not isinstance(expected_options, dict) or set(expected_options) != set(OPTIONS.values())
            or any(type(v) is not int or v <= 0 for v in expected_options.values())
            or geometry != expected_options):
        raise BindingError("launch geometry differs from binding")
    capsule = json.loads(checked_bytes(paths["capsule"], binding["artifacts"]["capsule"]["sha256"]))
    expected_coordinate = {role + "_sha256": binding["artifacts"][role]["sha256"]
                           for role in ("runtime", "source_manifest", "profile")}
    expected_coordinate["options"] = geometry
    if (not isinstance(capsule, dict) or type(capsule.get("schema")) is not int
            or capsule["schema"] != 1 or capsule.get("coordinate") != expected_coordinate):
        raise BindingError("capsule export belongs to a different runtime/source/profile/options")
    # Neither a status string nor a caller-supplied boolean establishes admission.
    # Unit evidence is deliberately left to the saved core's actual installer.
    overrides = shlex.split(user_runtime_args)
    seen = set()
    while overrides:
        if len(overrides) < 2 or overrides[0] not in OPTIONS or overrides[0] in seen:
            raise BindingError("unsupported or duplicate SBCL_USER_ARGS option")
        flag, value = overrides[:2]
        if number(flag, value) != geometry[OPTIONS[flag]]:
            raise BindingError("SBCL_USER_ARGS changes bound geometry: " + flag)
        seen.add(flag)
        overrides = overrides[2:]
    argv[0] = str(paths["runtime"])
    argv[argv.index("--core") + 1] = str(paths["core"])
    return argv + list(app_args), home


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binding", required=True, type=Path)
    parser.add_argument("--expected-sha256", required=True)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("app_args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    try:
        app_args = args.app_args[1:] if args.app_args[:1] == ["--"] else args.app_args
        argv, home = resolve(args.binding, args.expected_sha256,
                             os.environ.get("SBCL_USER_ARGS", ""), app_args)
        if args.check:
            print(json.dumps({"identity": "matched", "qualification": "not-established",
                              "argv": argv, "SBCL_HOME": home}))
            return 0
        env = dict(os.environ, SBCL_HOME=home)
        env.pop("SBCL_USER_ARGS", None)
        os.execve(argv[0], argv, env)
    except (BindingError, OSError, ValueError, KeyError, TypeError) as error:
        print("bound launch refused: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
