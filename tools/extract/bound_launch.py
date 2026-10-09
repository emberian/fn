#!/usr/bin/env python3
"""Check an externally pinned product binding before starting its runtime.

This checks artifact identity and the launch's bounds, never qualification.
The heap is decided per command, as the image's launcher decides it (ruling
2026-10-09, ADMISSION-RESERVES-NOT-REOPEN): `--fn ARGV' with no caller figure
first runs the core's own `--fn heap -- ARGV' probe and starts at the heap and
control stack ACL2 prints, under the binding's heap ceiling (the preset's
configured memory); a decided figure above it is a named refusal, exit 1.
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
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import core_launcher  # noqa: E402  the one rendering of the decision prelude


class BindingError(ValueError):
    pass


class Refusal(Exception):
    """The launch is refused by name (the heap probe's refusal, or a decided
    heap above the binding's ceiling): STATUS is the exit status, WORDS the
    line printed after `fn: '."""
    def __init__(self, status, words):
        super().__init__(words)
        self.status, self.words = status, words


ROLES = {"launcher", "runtime", "core", "source_manifest", "profile", "capsule"}
OPTIONS = {"--tls-limit": "tls_limit", "--dynamic-space-size": "dynamic_space_bytes",
           "--control-stack-size": "control_stack_bytes"}
# What a binding pins: the TLS limit (a build constant) and the heap ceiling,
# the preset's configured memory.  The heap and control stack themselves are
# decided per command by the core (heap_decision).
BOUND_OPTIONS = ("tls_limit", "dynamic_space_ceiling_bytes")
PROBE_TIMEOUT_SECONDS = 300
MIB = 2**20


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


def _code(text):
    return [line.strip() for line in text.splitlines()
            if line.strip() and not line.lstrip().startswith("#")]


def parse_launcher(text):
    """Accept only core_launcher.py's literal shell form, without evaluating it:
    the decision prelude, verbatim, then the SBCL_HOME and exec lines.  This
    process never runs the prelude (it decides the heap itself, below); a
    launcher without it would start at a fixed heap when run directly."""
    code = _code(text)
    prelude = _code(core_launcher.decision_prelude())
    if code[:len(prelude)] != prelude:
        raise BindingError("launcher does not carry the heap decision prelude")
    lines = code[len(prelude):]
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


def resolve_plan(binding_path, expected_sha256, user_runtime_args="", app_args=(), environment=None):
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
    if (not isinstance(expected_options, dict) or set(expected_options) != set(BOUND_OPTIONS)
            or any(type(v) is not int or v <= 0 for v in expected_options.values())):
        raise BindingError("binding options must be the TLS limit and the heap ceiling")
    if geometry["tls_limit"] != expected_options["tls_limit"]:
        raise BindingError("launch geometry differs from binding: TLS limit")
    if geometry["dynamic_space_bytes"] > expected_options["dynamic_space_ceiling_bytes"]:
        raise BindingError("launch geometry differs from binding: the default heap is above the ceiling")
    capsule = json.loads(checked_bytes(paths["capsule"], binding["artifacts"]["capsule"]["sha256"]))
    expected_coordinate = {role + "_sha256": binding["artifacts"][role]["sha256"]
                           for role in ("runtime", "source_manifest", "profile")}
    expected_coordinate["options"] = expected_options
    selected = binding.get("environment", {})
    libraries = binding.get("foreign_libraries", {})
    if not isinstance(selected, dict) or not isinstance(libraries, dict):
        raise BindingError("invalid bound environment")
    if set(selected) & set(libraries):
        raise BindingError("duplicate bound environment selector")
    for key, value in selected.items():
        if (not isinstance(key, str) or not re.fullmatch(r"FN_[A-Z0-9_]+", key)
                or key.endswith("_LIBRARY") or not isinstance(value, str) or "\0" in value):
            raise BindingError("invalid bound FN selector")
    library_paths = {}
    library_hashes = {}
    for key, record in libraries.items():
        if (not isinstance(key, str) or not re.fullmatch(r"FN_[A-Z0-9_]+_LIBRARY", key)
                or not isinstance(record, dict)):
            raise BindingError("invalid foreign-library binding")
        path = Path(record["path"])
        path = (binding_path.parent / path).resolve() if not path.is_absolute() else path.resolve()
        expected = record.get("sha256")
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise BindingError("missing foreign-library digest")
        if digest(path) != expected:
            raise BindingError("foreign-library digest mismatch: " + key)
        library_paths[key] = str(path)
        library_hashes[key] = expected
    if selected:
        expected_coordinate["environment"] = selected
    if libraries:
        expected_coordinate["foreign_libraries"] = library_hashes
    if (not isinstance(capsule, dict) or type(capsule.get("schema")) is not int
            or capsule["schema"] != 1 or capsule.get("coordinate") != expected_coordinate):
        raise BindingError("capsule export belongs to a different runtime/source/profile/options/environment")
    env = dict(os.environ if environment is None else environment)
    for key, value in env.items():
        if (key.startswith(("LD_", "DYLD_", "MALLOC_", "Malloc"))
                or key in {"GLIBC_TUNABLES", "ASAN_OPTIONS", "LSAN_OPTIONS", "TSAN_OPTIONS"}
                or (key.startswith("SBCL_") and key not in {"SBCL_HOME", "SBCL_USER_ARGS"})):
            raise BindingError("unbound runtime environment selector: " + key)
        if key.startswith("FN_"):
            if key in library_paths:
                if not value or str(Path(value).resolve()) != library_paths[key]:
                    raise BindingError("foreign-library selector mismatch: " + key)
            elif key not in selected or value != selected[key]:
                raise BindingError("unbound or mismatched FN selector: " + key)
    env.update(selected)
    env.update(library_paths)
    env["SBCL_HOME"] = home
    env.pop("SBCL_USER_ARGS", None)
    # Neither a status string nor a caller-supplied boolean establishes admission.
    # Unit evidence is deliberately left to the saved core's actual installer.
    # A caller's figure is its own (as at the image's launcher), within the
    # bounds: the TLS limit is the binding's, the heap at most its ceiling.
    overrides = shlex.split(user_runtime_args)
    seen = set()
    while overrides:
        if len(overrides) < 2 or overrides[0] not in OPTIONS or overrides[0] in seen:
            raise BindingError("unsupported or duplicate SBCL_USER_ARGS option")
        flag, value = overrides[:2]
        size = number(flag, value)
        if flag == "--tls-limit" and size != expected_options["tls_limit"]:
            raise BindingError("SBCL_USER_ARGS changes the bound TLS limit")
        if flag == "--dynamic-space-size" and size > expected_options["dynamic_space_ceiling_bytes"]:
            raise BindingError("SBCL_USER_ARGS heap is above the binding's ceiling")
        argv[argv.index(flag) + 1] = value
        seen.add(flag)
        overrides = overrides[2:]
    argv[0] = str(paths["runtime"])
    argv[argv.index("--core") + 1] = str(paths["core"])
    return argv + list(app_args), home, env


def heap_decision(argv, env, app_args, ceiling):
    """ARGV with the heap and control stack the core decides for APP_ARGS:
    `--fn heap -- ARGV' run at the core's size plus two 64 MiB nurseries (as
    packaging/fn's fn_decide_heap runs it), its `heap=MB MB ... stack=KB KB'
    applied; Refusal on its refusal, on a probe that never decided, and on a
    decided heap above CEILING (octets)."""
    core = Path(argv[argv.index("--core") + 1])
    boot = (core.stat().st_size + MIB - 1) // MIB + 128
    probe = list(argv)
    probe[probe.index("--dynamic-space-size") + 1] = str(boot)
    probe += ["--fn", "heap", "--", *app_args[1:]]
    done = subprocess.run(probe, env=env, capture_output=True, text=True,
                          timeout=PROBE_TIMEOUT_SECONDS)
    figure = next((line for line in done.stdout.splitlines()
                   if line.startswith(("heap=", "refused "))), "")
    if figure.startswith("refused "):
        raise Refusal(done.returncode or 1, figure)
    if done.returncode == 5:
        raise Refusal(5, done.stderr.strip() or "usage refused before the heap probe ran")
    heap = re.match(r"heap=([0-9]+) MB\b", figure)
    stack = re.search(r"\bstack=([0-9]+) KB\b", figure)
    if done.returncode != 0 or not heap or not stack:
        raise Refusal(4, "fault heap-probe-did-not-run exit=%d: the core stopped before it decided "
                         "its memory: %s" % (done.returncode, (done.stderr or figure).strip()[-300:]))
    if int(heap[1]) * MIB > ceiling:
        raise Refusal(1, "refused heap-above-ceiling decided=%s MB ceiling=%d MB: the store this "
                         "command opens needs more memory than the binding's preset is configured "
                         "for" % (heap[1], ceiling // MIB))
    argv = list(argv)
    argv[argv.index("--dynamic-space-size") + 1] = heap[1]
    argv[argv.index("--control-stack-size") + 1] = stack[1] + "KB"
    return argv


def plan_launch(binding_path, expected_sha256, user_runtime_args="", app_args=(), environment=None):
    """resolve_plan, then the per-command heap: a caller's heap figure is its
    own; otherwise a `--fn' command other than `heap' is decided by the core."""
    argv, home, env = resolve_plan(binding_path, expected_sha256, user_runtime_args, app_args,
                                   environment)
    app_args = list(app_args)
    caller_heap = "--dynamic-space-size" in shlex.split(user_runtime_args)
    if not caller_heap and app_args[:1] == ["--fn"] and app_args[1:2] != ["heap"]:
        binding = json.loads(checked_bytes(Path(binding_path).resolve(), expected_sha256))
        head = argv[:len(argv) - len(app_args)]
        argv = heap_decision(head, env, app_args,
                             binding["options"]["dynamic_space_ceiling_bytes"]) + app_args
    return argv, home, env


def resolve(binding_path, expected_sha256, user_runtime_args="", app_args=(), environment=None):
    """Compatibility identity resolver; process launch uses the bound environment."""
    argv, home, _ = resolve_plan(binding_path, expected_sha256, user_runtime_args, app_args, environment)
    return argv, home


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binding", required=True, type=Path)
    parser.add_argument("--expected-sha256", required=True)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("app_args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    try:
        app_args = args.app_args[1:] if args.app_args[:1] == ["--"] else args.app_args
        argv, home, env = plan_launch(args.binding, args.expected_sha256,
                                      os.environ.get("SBCL_USER_ARGS", ""), app_args)
        if args.check:
            print(json.dumps({"identity": "matched", "qualification": "not-established",
                              "argv": argv, "SBCL_HOME": home}))
            return 0
        os.execve(argv[0], argv, env)
    except Refusal as refusal:
        print("fn: " + refusal.words, file=sys.stderr)
        return refusal.status
    except (BindingError, OSError, ValueError, KeyError, TypeError,
            subprocess.SubprocessError) as error:
        print("bound launch refused: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
