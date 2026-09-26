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
`os.environ["NAME"]` or `os.getenv("NAME"`; `plan` scans the module's own file
(tests/test_x.py for tests.test_x or tests.test_x.Class), not the helpers it
imports.  For each requested module `plan` prints one line,

    MODULE NAME=VALUE ...

the assignments hbox_native.sh gives that module's process: every image
variable it reads whose image this run builds, the opt-in flags that mean
"run against the image this run built", and the OpenSSL and tree paths.
Values are box-shell words ($T is the tree, $FN_OPENSSL_PREFIX the toolchain).
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
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ORDER = ("developer", "production", "dtn", "dtn-developer")
IMAGE_PATH = {
    "production": "$T/build/fn-host",
    "developer": "$T/build/fn-host-developer",
    "dtn": "$T/build/fn-host-dtn",
    "dtn-developer": "$T/build/fn-host-dtn-developer",
}
OPENSSL = "$FN_OPENSSL_PREFIX/bin/openssl"

# Image variables: the images that satisfy each, first built wins.
IMAGES = {
    "FN_NATIVE_HOST": ("production",),
    "FN_NATIVE_DEVELOPER_HOST": ("developer",),
    "FN_NATIVE_CRASH_HOST": ("developer",),
    "FN_NATIVE_BP_HOST": ("dtn", "dtn-developer"),
    "FN_NATIVE_CONTACT_SENDER": ("dtn", "dtn-developer"),
    "FN_NATIVE_CONTACT_RECEIVER": ("dtn", "dtn-developer"),
    "FN_NATIVE_DTN_HOST": ("dtn",),
    "FN_NATIVE_DTN_DEVELOPER_HOST": ("dtn-developer",),
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
    "FN_RUN_HYBRID_E2E": ("1", "opt-in: the OpenSSL 3.5 saved-image gate"),
    "FN_RUN_CONSUMER_EXCHANGE": ("1", "opt-in: the consumer exchange against this run's image"),
    "FN_TEST_OPENSSL": (OPENSSL, "the toolchain's OpenSSL 3.5 (ML-DSA-65)"),
    "FN_OPENSSL": (OPENSSL, "the toolchain's OpenSSL 3.5"),
    "FN_NATIVE_TEST_ROOT": ("$T", "the shipped tree"),
}
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
    "FN_OLD_NATIVE_HOST": "an older image (upgrade cases)",
    "FN_OLD_IMAGE": "an older image (upgrade cases)",
    "FN_PRE_T2_NATIVE_DEVELOPER_HOST": "a pre-T2 developer image (migration)",
    "FN_T2_NATIVE_DEVELOPER_HOST": "a T2 developer image (migration)",
    "FN_T2B_NATIVE_DEVELOPER_HOST": "a T2b developer image (migration)",
    "FN_NATIVE_TOPIC_V1_HOST": "a topic-v1 image (legacy topic cases)",
    "FN_INN_SRC": "an installed INN 2.7 tree",
    "FN_DTN7_REPO": "a dtn7-rs checkout",
}
READ = re.compile(r'(?:environ\.get\(|environ\[|getenv\()\s*"(FN_[A-Z0-9_]+)"')


def module_file(module: str) -> Path:
    parts = module.split(".")
    for end in range(len(parts), 0, -1):
        path = ROOT.joinpath(*parts[:end]).with_suffix(".py")
        if path.is_file():
            return path
    raise SystemExit(f"native_env: no source for {module}")


def reads(module: str) -> list[str]:
    return sorted(set(READ.findall(module_file(module).read_text())))


def join_images(built: list[str], *extra: str) -> str:
    wanted = set(built) | set(extra)
    return ",".join(image for image in ORDER if image in wanted)


def plan(images: list[str], given: dict[str, str], modules: list[str]
         ) -> tuple[list[str], list[str], list[str]]:
    """(lines, refusals, notes) for these modules and this run's images."""
    lines, notes = [], []
    missing: list[tuple[str, str, str]] = []
    for module in modules:
        stem = module_file(module).stem
        assignments = []
        for name in reads(module):
            if name in given:
                continue
            if name in IMAGES:
                image = next((i for i in IMAGES[name] if i in images), None)
                if (stem, name) in FALLBACK:
                    continue
                if image is not None:
                    if not (name in DEFAULTS_TO_FIRST and image == IMAGES[name][0]):
                        assignments.append(f"{name}={IMAGE_PATH[image]}")
                else:
                    missing.append((module, name, IMAGES[name][0]))
            elif name in FIXED:
                assignments.append(f"{name}={FIXED[name][0]}")
            elif name in MANUAL and not MANUAL[name].startswith(("falls back", "defaults")):
                notes.append(f"{module} reads {name} (not set: {MANUAL[name]}; "
                             f"pass --env {name}=... to run what it gates)")
        lines.append(" ".join([module, *assignments]))
    wanted = join_images(images, *(image for _, _, image in missing))
    refusals = [f"{module} reads {name}: build the {image} image with --images {wanted}"
                for module, name, image in missing]
    return lines, refusals, notes


def readers() -> dict[str, list[str]]:
    table: dict[str, list[str]] = {}
    paths = sorted({*(ROOT / "tests").glob("test_native_*.py"),
                    *(ROOT / "tests").glob("test_*_native.py")})
    for path in paths:
        for name in set(READ.findall(path.read_text())):
            table.setdefault(name, []).append(path.stem)
    return table


def meaning(name: str) -> str:
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
    known = set(IMAGES) | set(FIXED) | set(MANUAL)
    for name, modules in sorted(readers().items()):
        if name not in known:
            continue
        rows.append(f"| {name} | {', '.join(sorted(modules))} | {meaning(name)} |")
    return "\n".join(rows)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("plan", help="per-module assignments, or a refusal by name")
    p.add_argument("--images", default="developer")
    p.add_argument("--env", action="append", default=[], help="NAME=VALUE the caller set")
    p.add_argument("modules", nargs="+")
    sub.add_parser("table", help="the variable table (Markdown)")
    arguments = parser.parse_args(argv)
    if arguments.command == "table":
        print(table())
        return 0
    images = [image for image in arguments.images.split(",") if image]
    given = dict(item.split("=", 1) for item in arguments.env)
    lines, refusals, notes = plan(images, given, arguments.modules)
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
