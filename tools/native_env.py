#!/usr/bin/env python3
"""Which environment a native test module reads, and what tools/hbox_native.sh sets.

    python3 tools/native_env.py plan --images developer,production \\
        [--env NAME=VALUE ...] tests.test_native_hybrid_author ...
    python3 tools/native_env.py table            # the variable table, Markdown

Seven lanes ran a module through hbox_native.sh, had every test skip for an
environment variable the script never set, and read the summary's "OK"
(PKT-437 (2), PKT-374).  This is the one table of what the native modules
read and what each variable means, and the check hbox_native.sh makes before
any test step.

A module *reads* a variable when its source calls `os.environ.get("NAME"`,
`os.environ["NAME"]`, `os.getenv("NAME"` or tests/native_harness.py's
`native_image("NAME"`; `plan` scans the module's own file
(tests/test_x.py for tests.test_x or tests.test_x.Class) and every tests/
module it imports, transitively, for image variables (PKT-490 (2)); opt-ins
and fixed paths count from the module's own file.  An image variable read only
through an imported helper is set when its image is built and noted, never
refused, when it is not: a helper may read it at import without the module
ever starting that image.  For each requested module `plan` prints one line,

    MODULE NAME=VALUE ...

the assignments hbox_native.sh gives that module's process: every image
variable it reads whose image this run builds, the opt-in flags that mean
"run against the image this run built", and the OpenSSL and tree paths.
Values are box-shell words ($T is the tree, $FN_TEST_OPENSSL_BIN the test
tool OpenSSL 3.5 that makes independent ML-DSA-65 keys; the node itself uses
the system libssl and its own ML-DSA-65 library, HST-016).
A module that reads an image variable whose image is not in --images (and
not given by --env) is refused by name, exit 2:

    tests.test_native_hybrid_author reads FN_NATIVE_HOST: build the production
    image with --images developer,production

One rule for which image a variable names: FN_NATIVE_HOST is always the
production image (build/fn-host), never the developer launcher
(operator-daily-2's n1 set it to the developer image and the production-only
selector case started owners that never exit).  A module that falls back to
another image when a variable is unset lists that read in FALLBACK: it is
neither refused nor set, so the module keeps its own default (pass --env to
point it elsewhere).

The production image's identity (lane tooling-leftovers, 2026-09-27; wire-bounds
hand-computed it): tests.test_native_peering and tests.test_native_admin
check the running process against FN_NATIVE_LAUNCHER_SHA256,
FN_NATIVE_CORE_SHA256, FN_NATIVE_RUNTIME_SHA256 and
FN_NATIVE_IMAGE_SOURCE_SHA.  `identity` computes all four from an image,
anywhere:

    eval "$(python3 tools/native_env.py identity --image build/fn-host \
        --source "$(git rev-parse HEAD)" --export)"

hbox_native.sh runs it on the box after the image steps (on the image
FN_NATIVE_HOST names when --env gives one); `plan` refuses a module that
reads one when no production image is built and none is given.

Harness stores (lane membership-budget): `init` refuses a profile whose
full store the machine's budget cannot hold unless FN_INIT_BUDGET_MB names a
target.  The fixtures, the power-loss and service-envelope harnesses and the
pack-chain module make stores for hbox and run them directly; they take the
target from `harness_store_env` here, HARNESS_INIT_BUDGET_MB (hbox's 96
GiB), so it is written once.

The toolchain SBCL (obstructions-5 item 41; tooling-truth-2 found a whole
KNOWN_RED list caused by it): hbox's system sbcl 2.2.9 (/usr/bin/sbcl) sits
on PATH ahead of the toolchain's /tank/fn/sbcl/bin/sbcl 2.6.8, so a tool or
test running `sbcl` by name got the wrong runtime.  tools/farm.py HOSTS names
each box's `sbcl`; on a box (that file exists here)

    python3 tools/native_env.py sbcl            # its absolute path ('' off a box)
    python3 tools/native_env.py sbcl --export   # export FN_SBCL=... PATH=<its dir>:$PATH
    python3 tools/native_env.py sbcl-check      # exit 2 when `sbcl` or FN_SBCL is another

hbox_native.sh, remote_check.sh and the Makefile put it first on PATH and
set FN_SBCL; farm.py's box command does the same; hbox_native and
remote_check run `sbcl-check` before any step, so a bare `sbcl` that is not
the toolchain's is refused by name instead of silently running.
"""

from __future__ import annotations

import argparse
import ast
import os
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ORDER = ("developer", "production", "dtn", "dtn-developer", "reference",
         "developer-stripped", "prof")
IMAGE_PATH = {
    "production": "$T/build/fn-host",
    "developer": "$T/build/fn-host-developer",
    # The production image with its full world (the release's reference
    # twin) and the developer image stripped (gpt-6's wave-5 review s.4).
    "reference": "$T/build/fn-host-reference",
    "developer-stripped": "$T/build/fn-host-developer-stripped",
    "dtn": "$T/build/fn-host-dtn",
    "dtn-developer": "$T/build/fn-host-dtn-developer",
    # The profiling developer image (tools/profile/build_native_profile.sh),
    # a measurement tool, never a test subject: no variable names it.
    "prof": "$T/build/fn-host-prof",
}
OPENSSL = "$FN_TEST_OPENSSL_BIN"

# Image variables: the images that satisfy each, first built wins.
IMAGES = {
    "FN_NATIVE_HOST": ("production",),
    "FN_NATIVE_DEVELOPER_HOST": ("developer",),
    "FN_NATIVE_REFERENCE_HOST": ("reference",),
    "FN_NATIVE_DEVELOPER_STRIPPED_HOST": ("developer-stripped",),
    "FN_NATIVE_CRASH_HOST": ("developer",),
    "FN_NATIVE_BP_HOST": ("dtn", "dtn-developer"),
    "FN_NATIVE_CONTACT_SENDER": ("dtn", "dtn-developer"),
    "FN_NATIVE_CONTACT_RECEIVER": ("dtn", "dtn-developer"),
    "FN_NATIVE_DTN_HOST": ("dtn",),
    "FN_NATIVE_DTN_DEVELOPER_HOST": ("dtn-developer",),
}
# A module that needs a different first choice for a variable (module stem,
# variable) -> images in order: 7 of test_bp_service_native's 17 cases need
# fault-injection switches the non-developer DTN image refuses (image-strip,
# 2026-09-28), so it takes the dtn-developer image when that is built; 2 of
# test_bp_receive_integrity_native's 4 likewise (FN_BP_TEST_DELIVER_FAULT,
# FN_IMMUTABLE_PUBLISH_TEST_FAIL; red on the dtn image, lane native-reds).
PREFER = {
    ("test_bp_service_native", "FN_NATIVE_BP_HOST"): ("dtn-developer", "dtn"),
    ("test_bp_receive_integrity_native", "FN_NATIVE_BP_HOST"): ("dtn-developer", "dtn"),
}
# The modules reading these default to exactly the first image's path in
# their own tree ($T), so when that image is built nothing is exported and
# the module keeps its default; a fallback image is exported.
DEFAULTS_TO_FIRST = {"FN_NATIVE_BP_HOST", "FN_NATIVE_CONTACT_SENDER",
                     "FN_NATIVE_CONTACT_RECEIVER", "FN_NATIVE_DTN_DEVELOPER_HOST"}
# Reads that fall back to another image when unset: never refused, never set
# (the module keeps its own default).  (module stem, variable).
FALLBACK = {
    ("test_native_public_exposure", "FN_NATIVE_HOST"): "falls back to FN_NATIVE_DEVELOPER_HOST",
    ("test_native_profile", "FN_NATIVE_HOST"): "falls back to FN_NATIVE_DEVELOPER_HOST",
    ("test_native_key_statements", "FN_NATIVE_HOST"): "defaults to build/fn-host-developer",
}
# Set for every module that reads them: they mean "the image this run built".
FIXED = {
    "FN_RUN_HYBRID_E2E": ("1", "opt-in: the hybrid-signature saved-image gate"),
    "FN_RUN_CONSUMER_EXCHANGE": ("1", "opt-in: the consumer exchange against this run's image"),
    "FN_TEST_OPENSSL": (OPENSSL, "the test tool OpenSSL 3.5 (independent ML-DSA-65 keys)"),
    "FN_OPENSSL": (OPENSSL, "the test tool OpenSSL 3.5"),
    "FN_NATIVE_TEST_ROOT": ("$T", "the shipped tree"),
}
# Of FIXED, the names that locate a test tool and gate nothing: set for a
# module that reads one only through a helper too, since a module that
# subclasses the helper's tests runs the helper's reads
# (tests/test_native_operator_verdicts runs test_native_control_filing's
# signed withdrawal, which needs FN_TEST_OPENSSL's ML-DSA-65; dev-health
# 2026-09-27).  The opt-ins stay the helper's own modules'.
TOOLS = ("FN_TEST_OPENSSL", "FN_OPENSSL", "FN_NATIVE_TEST_ROOT")
# Read but never set by the script: each needs something this run does not
# build or means a different image.  A module reading one gets a note, and
# the cases it gates skip (reported, never counted as passing).
MANUAL = {
    "FN_RUN_NATIVE_CLONE": "opt-in for a combined E2/checkpoint developer image",
    "FN_RUN_RELOCATION_E2E": "opt-in; also needs FN_BUILD_OPENSSL_PREFIX (a second OpenSSL build)",
    "FN_BUILD_OPENSSL_PREFIX": "the build-time OpenSSL for the relocation case",
    "FN_RUN_CONSUMER_E2E": "opt-in for the consumer E2 gate",
    "FN_RUN_CONSUMER_POLL_E2E": "opt-in; requires the ACL2-owned consumer poll command",
    "FN_RUN_CONSUMER_INSPECT": "opt-in for consumer inspect",
    "FN_RUN_CONSUMER_PROJECT_BOUNDS": "opt-in for consumer project bounds",
    "FN_RUN_NATIVE_READER_INDEX": "opt-in for the integrated reader-index gate",
    "FN_RUN_TOPIC_LOCAL_E2E": "opt-in for a source-matched topic image",
    "FN_RUN_TOPIC_METADATA_E2E": "opt-in for the source-matched topic-metadata gate",
    "FN_NATIVE_BP_NODE_HOST": "falls back to FN_NATIVE_DEVELOPER_HOST (the DTN developer image by --env)",
    "FN_NATIVE_READER_HOST": "falls back to FN_NATIVE_DEVELOPER_HOST",
    "FN_NATIVE_SOURCE_ROOT": "defaults to the tree the module runs from",
    "FN_SPAN_REFERENCE_HOST": "the base image of the ingress-span differential (SCN-110; built from the lane base, by --env)",
    "FN_RUN_SLOW": "opt-in for tests marked slow (tests/native_harness.py `slow'): batches and qualification",
    "FN_INN_SRC": "an installed INN 2.7 tree",
    "FN_DTN7_REPO": "a dtn7-rs checkout",
}
# The production image's identity: computed by `identity` from the image
# on the box after the image steps, never typed.  A module reading one needs
# the production image (or FN_NATIVE_HOST and the value by --env).
IDENTITY = {
    "FN_NATIVE_LAUNCHER_SHA256": "SHA-256 of the image's launcher (build/fn-host)",
    "FN_NATIVE_CORE_SHA256": "SHA-256 of the image's core (build/fn-host.core)",
    "FN_NATIVE_RUNTIME_SHA256": "SHA-256 of the SBCL runtime the launcher execs",
    "FN_NATIVE_IMAGE_SOURCE_SHA": "the source revision the image was built from "
                                  "(a commit, or HEAD+dirty for a worktree run)",
}
# The developer image's identity, computed the same way from
# build/fn-host-developer when that image is built (`identity --prefix
# FN_NATIVE_DEVELOPER_`): a case that pins the developer core
# (tests/test_native_protected_peering's durable-sent cut) skipped wholly
# without it.
DEVELOPER_IDENTITY = {
    "FN_NATIVE_DEVELOPER_LAUNCHER_SHA256": "SHA-256 of the developer image's launcher",
    "FN_NATIVE_DEVELOPER_CORE_SHA256": "SHA-256 of the developer image's core",
}
# The FN_INIT_BUDGET_MB a harness names for the stores it makes for hbox and
# runs directly (hbox's 96 GiB): the one place it is written.
HARNESS_INIT_BUDGET_MB = "98304"


def harness_store_env(env: dict[str, str] | None = None) -> dict[str, str]:
    """ENV (default os.environ) with the harness stores' init budget, unless set."""
    import os
    out = dict(os.environ if env is None else env)
    out.setdefault("FN_INIT_BUDGET_MB", HARNESS_INIT_BUDGET_MB)
    return out


LAUNCHER_EXEC = re.compile(r'^exec "([^"]+)" ', re.M)


def sha256_file(path: Path) -> str:
    import hashlib
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def image_identity(image: Path, source: str | None = None) -> dict[str, str]:
    """The four identity variables of IMAGE (a save-exec launcher beside IMAGE.core).

    The runtime is the file the launcher's `exec "..."` line names.  A
    variable whose file is missing is left out, never guessed.
    """
    found: dict[str, str] = {}
    core = Path(str(image) + ".core")
    if image.is_file():
        found["FN_NATIVE_LAUNCHER_SHA256"] = sha256_file(image)
        match = LAUNCHER_EXEC.search(image.read_text(encoding="utf-8", errors="replace"))
        runtime = Path(match.group(1)) if match else None
        if runtime is not None and runtime.is_file():
            found["FN_NATIVE_RUNTIME_SHA256"] = sha256_file(runtime)
    if core.is_file():
        found["FN_NATIVE_CORE_SHA256"] = sha256_file(core)
    if source:
        found["FN_NATIVE_IMAGE_SOURCE_SHA"] = source
    return found


READ = re.compile(r'(?:environ\.get\(|environ\[|getenv\(|native_image\()\s*"(FN_[A-Z0-9_]+)"')


def module_file(module: str) -> Path:
    parts = module.split(".")
    for end in range(len(parts), 0, -1):
        path = ROOT.joinpath(*parts[:end]).with_suffix(".py")
        if path.is_file():
            return path
    raise SystemExit(f"native_env: no source for {module}")


# `from tests.X import ...`, `import tests.X` and `from tests import X, Y as Z`:
# the local helpers a module takes its images from (tests/test_native_bounds_join
# reads FN_NATIVE_HOST only through test_native_operator_verbs' IMAGE).
IMPORT_FROM = re.compile(r"^\s*(?:from\s+tests\.([\w.]+)\s+import|import\s+tests\.([\w.]+))", re.M)
IMPORT_NAMES = re.compile(r"^\s*from\s+tests\s+import\s+(\([^)]*\)|[^\n]+)", re.M)


def local_imports(text: str) -> list[str]:
    found = [f"tests.{a or b}" for a, b in IMPORT_FROM.findall(text)]
    for names in IMPORT_NAMES.findall(text):
        for word in names.strip("()").replace("\\", " ").split(","):
            name = word.split(" as ")[0].strip()
            if name:
                found.append(f"tests.{name}")
    return found


def own_reads(module: str) -> list[str]:
    """The variables MODULE's own file reads."""
    return sorted(set(READ.findall(module_file(module).read_text())))


def reads(module: str) -> list[str]:
    """The variables MODULE reads, in its own file or a tests/ helper it imports."""
    top = module_file(module)
    seen: set[Path] = set()
    names: set[str] = set()
    pending = [top]
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        text = path.read_text()
        names.update(READ.findall(text))
        for helper in local_imports(text):
            try:
                pending.append(module_file(helper))
            except SystemExit:
                continue  # a package or a name that is not a module file
    return sorted(names)


def join_images(built: list[str], *extra: str) -> str:
    wanted = set(built) | set(extra)
    return ",".join(image for image in ORDER if image in wanted)


def needed_images(images: list[str], given: dict[str, str], modules: list[str]
                  ) -> tuple[str, list[str]]:
    """The images these modules read, over IMAGES: (the list, why each was added).

    `hbox_native` without --images builds this list instead of refusing a
    module that reads an unbuilt image (FN_NATIVE_HOST -> production): three
    lanes lost a launch each to that refusal (2026-09-29).
    """
    built, why = list(images), []
    while True:
        missing = plan_missing(built, given, modules)
        new = [(module, name, image) for module, name, image in missing if image not in built]
        if not new:
            return join_images(built), why
        for module, name, image in new:
            if image not in built:
                built.append(image)
            why.append(f"{image} ({module} reads {name})")


def plan_missing(images, given, modules) -> list[tuple[str, str, str]]:
    return _plan(images, given, modules)[3]


def plan(images: list[str], given: dict[str, str], modules: list[str],
         allow_skips: bool = False) -> tuple[list[str], list[str], list[str]]:
    """(lines, refusals, notes) for these modules and this run's images.

    A module whose own source reads a MANUAL gate (FN_RUN_*_E2E, FN_INN_SRC,
    ...) that this run leaves unset is REFUSED, naming the variable, unless
    ALLOW_SKIPS (hbox_native --allow-skips): operability-4 built 25 minutes
    of images twice for a module that then skipped (obstructions-5 item 45).
    """
    lines, refusals, notes, _ = _plan(images, given, modules, allow_skips)
    return lines, refusals, notes


def _plan(images: list[str], given: dict[str, str], modules: list[str],
          allow_skips: bool = True):
    lines, notes = [], []
    gated: list[str] = []
    missing: list[tuple[str, str, str]] = []
    for module in modules:
        stem = module_file(module).stem
        assignments = []
        own = set(own_reads(module))
        for name in reads(module):
            if name in given or (name not in own and name not in IMAGES
                                 and name not in TOOLS):
                continue  # a helper's opt-ins stay the helper's own modules'
            if name in IMAGES:
                choices = PREFER.get((stem, name), IMAGES[name])
                image = next((i for i in choices if i in images), None)
                if (stem, name) in FALLBACK:
                    continue
                if image is not None:
                    if not (name in DEFAULTS_TO_FIRST and image == IMAGES[name][0]):
                        assignments.append(f"{name}={IMAGE_PATH[image]}")
                elif name in own:
                    missing.append((module, name, IMAGES[name][0]))
                else:
                    # Read only by an imported helper, which may read it at
                    # import and never start that image: set when built,
                    # noted (never refused) when not.
                    notes.append(f"{module} reads {name} through a tests/ helper it "
                                 f"imports (not set: the {IMAGES[name][0]} image is not "
                                 f"built; add it to --images if the module starts it)")
            elif name in IDENTITY:
                # Exported for every module by the identity step, from the
                # production image (or the one FN_NATIVE_HOST names).
                if (name in own and "production" not in images
                        and "FN_NATIVE_HOST" not in given):
                    missing.append((module, name, "production"))
            elif name in DEVELOPER_IDENTITY:
                if name in own and "developer" not in images:
                    missing.append((module, name, "developer"))
            elif name in FIXED:
                assignments.append(f"{name}={FIXED[name][0]}")
            elif name in MANUAL and not MANUAL[name].startswith(("falls back", "defaults")):
                if allow_skips or name not in own:
                    notes.append(f"{module} reads {name} (not set: {MANUAL[name]}; "
                                 f"pass --env {name}=... to run what it gates)")
                else:
                    gated.append(f"{module} is gated by {name}, which this run leaves unset "
                                 f"({MANUAL[name]}): its gated tests would build the images "
                                 f"and then skip. Pass --env {name}=..., or --allow-skips")
        lines.append(" ".join([module, *assignments]))
    wanted = join_images(images, *(image for _, _, image in missing))
    refusals = [f"{module} reads {name}: build the {image} image with --images {wanted}"
                for module, name, image in missing] + gated
    return lines, refusals, notes, missing


def readers() -> dict[str, list[str]]:
    table: dict[str, list[str]] = {}
    paths = sorted({*(ROOT / "tests").glob("test_native_*.py"),
                    *(ROOT / "tests").glob("test_*_native.py")})
    for path in paths:
        for name in set(READ.findall(path.read_text())):
            table.setdefault(name, []).append(path.stem)
    return table


def meaning(name: str) -> str:
    if name in IDENTITY:
        return ("identity: " + IDENTITY[name] + "; `native_env.py identity` computes it "
                "after the image steps (refused when no production image is built)")
    if name in DEVELOPER_IDENTITY:
        return ("identity: " + DEVELOPER_IDENTITY[name] + "; `native_env.py identity "
                "--prefix FN_NATIVE_DEVELOPER_` computes it when the developer image is built")
    if name in IMAGES:
        fallback = sorted(stem for stem, var in FALLBACK if var == name)
        return ("image: " + " or ".join(IMAGES[name]) + " (set when built; refused when not)"
                + (f"; not set for {', '.join(fallback)} (own fallback)" if fallback else ""))
    if name in FIXED:
        return f"set to {FIXED[name][0]}: {FIXED[name][1]}"
    if name in MANUAL:
        return "not set: " + MANUAL[name]
    return "test-internal (fault injection or evidence path; the test sets it)"


def table() -> str:
    rows = ["| variable | modules reading it | what hbox_native.sh gives it |",
            "|---|---|---|"]
    known = set(IMAGES) | set(FIXED) | set(MANUAL) | set(IDENTITY) | set(DEVELOPER_IDENTITY)
    for name, modules in sorted(readers().items()):
        if name not in known:
            continue
        rows.append(f"| {name} | {', '.join(sorted(modules))} | {meaning(name)} |")
    return "\n".join(rows)


def host_sbcls(farm: Path | None = None) -> list[str]:
    """Every box's toolchain SBCL, from tools/farm.py HOSTS (read, not imported)."""
    tree = ast.parse((farm or ROOT / "tools" / "farm.py").read_text(encoding="utf-8"))
    for node in tree.body:
        if isinstance(node, ast.Assign) and getattr(node.targets[0], "id", None) == "HOSTS":
            hosts = ast.literal_eval(node.value)
            return sorted({h["sbcl"] for h in hosts.values() if h.get("sbcl")})
    return []


def toolchain_sbcl(candidates: list[str] | None = None, exists=os.path.isfile) -> str | None:
    """The toolchain SBCL when this machine is a box (its HOSTS path is here), else None."""
    for path in host_sbcls() if candidates is None else candidates:
        if exists(path):
            return path
    return None


def sbcl_refusal(toolchain: str | None, on_path: str | None, fn_sbcl: str | None,
                 real=os.path.realpath) -> str | None:
    """Why a box's `sbcl` is not the toolchain's, or None.  Off a box: None."""
    if toolchain is None:
        return None
    want = real(toolchain)
    if fn_sbcl and real(fn_sbcl) != want:
        return (f"FN_SBCL is {fn_sbcl}, not the toolchain's {toolchain} (tools/farm.py HOSTS)")
    if on_path is None:
        return (f"no `sbcl` on PATH; put {os.path.dirname(toolchain)} first "
                "(eval \"$(python3 tools/native_env.py sbcl --export)\")")
    if real(on_path) != want:
        return (f"`sbcl` on PATH is {on_path}, not the toolchain's {toolchain} "
                "(hbox's system sbcl is 2.2.9, the toolchain's 2.6.8): put "
                f"{os.path.dirname(toolchain)} first on PATH "
                "(eval \"$(python3 tools/native_env.py sbcl --export)\")")
    return None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("plan", help="per-module assignments, or a refusal by name")
    p.add_argument("--images", default="developer")
    p.add_argument("--env", action="append", default=[], help="NAME=VALUE the caller set")
    p.add_argument("--allow-skips", action="store_true",
                   help="note, do not refuse, a module whose opt-in gate is unset")
    p.add_argument("modules", nargs="+")
    p = sub.add_parser("images", help="the image list these modules read, over --images")
    p.add_argument("--images", default="developer")
    p.add_argument("--env", action="append", default=[], help="NAME=VALUE the caller set")
    p.add_argument("modules", nargs="+")
    sub.add_parser("table", help="the variable table (Markdown)")
    p = sub.add_parser("identity", help="the production image's four identity variables")
    p.add_argument("--image", default="build/fn-host",
                   help="the launcher (its core is IMAGE.core); default build/fn-host")
    p.add_argument("--source", default=None, help="the source revision it was built from")
    p.add_argument("--export", action="store_true", help="as `export NAME=VALUE` lines")
    p.add_argument("--prefix", default=None,
                   help="FN_NATIVE_DEVELOPER_: print the launcher and core digests "
                        "under that prefix (DEVELOPER_IDENTITY) and nothing else")
    p = sub.add_parser("sbcl", help="this box's toolchain SBCL (nothing off a box)")
    p.add_argument("--export", action="store_true",
                   help="as `export FN_SBCL=... PATH=<its dir>:$PATH`")
    sub.add_parser("sbcl-check", help="exit 2 when `sbcl`/FN_SBCL here is not the toolchain's")
    arguments = parser.parse_args(argv)
    if arguments.command == "sbcl":
        found = toolchain_sbcl()
        if found and arguments.export:
            print(f"export FN_SBCL={found} PATH={os.path.dirname(found)}:$PATH")
        elif found:
            print(found)
        return 0
    if arguments.command == "sbcl-check":
        found = toolchain_sbcl()
        why = sbcl_refusal(found, shutil.which("sbcl"), os.environ.get("FN_SBCL"))
        if why:
            print(f"native_env: REFUSED: {why}", file=sys.stderr)
            return 2
        print(f"native_env: sbcl is the toolchain's {found}" if found
              else "native_env: not a box (no HOSTS sbcl here); sbcl not checked")
        return 0
    if arguments.command == "table":
        print(table())
        return 0
    if arguments.command == "identity":
        image = Path(arguments.image)
        found = image_identity(image, arguments.source)
        if arguments.prefix:
            renamed = {arguments.prefix + name[len("FN_NATIVE_"):]: value
                       for name, value in found.items()
                       if name in ("FN_NATIVE_LAUNCHER_SHA256", "FN_NATIVE_CORE_SHA256")}
            for name in DEVELOPER_IDENTITY if arguments.prefix == "FN_NATIVE_DEVELOPER_" else renamed:
                if name in renamed:
                    print(("export " if arguments.export else "") + f"{name}={renamed[name]}")
            return 0 if renamed else 1
        absent = [name for name in IDENTITY if name not in found]
        for name in IDENTITY:
            if name in found:
                print(("export " if arguments.export else "") + f"{name}={found[name]}")
        if absent:
            print(f"native_env: identity of {image}: not set (no file, or no --source): "
                  + ", ".join(absent), file=sys.stderr)
        return 0 if found else 1
    images = [image for image in arguments.images.split(",") if image]
    given = dict(item.split("=", 1) for item in arguments.env)
    if arguments.command == "images":
        wanted, why = needed_images(images, given, arguments.modules)
        if why:
            print("hbox_native: images derived from what the modules read: "
                  f"--images {wanted}; added " + "; ".join(why), file=sys.stderr)
        print(wanted)
        return 0
    lines, refusals, notes = plan(images, given, arguments.modules,
                                  allow_skips=getattr(arguments, "allow_skips", False))
    for note in notes:
        print(f"hbox_native: note: {note}", file=sys.stderr)
    if refusals:
        for refusal in refusals:
            print(f"hbox_native: {refusal}", file=sys.stderr)
        return 2
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main())
