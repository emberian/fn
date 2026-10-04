#!/usr/bin/env python3
"""Run a scenario tier against a published image set (lane scenarios, 2026-10-04).

    python3 tools/scenario_suite.py list [TIER]
    python3 tools/scenario_suite.py modules TIER
    python3 tools/scenario_suite.py run TIER --image-set SHA [--rev REV]
        [--label LABEL] [--jobs 4] [--dry-run] [-- HBOX_NATIVE_OPTION ...]
    python3 tools/scenario_suite.py check
    python3 tools/scenario_suite.py heap-optouts

The tiers are data, tests/scenarios/tiers.tsv: peer (can a stranger's
server peer with us safely and usefully: transit both ways, catch-up,
cursor quanta, misbehaving peers, credentials, real INN), smoke (one short module per
question, minutes), core (the integrator's twelve, the release image bar),
e2e (one whole module per user-visible surface), resilience (crash-cut,
fault and hostile campaigns) and scale (fixture stores and measurements).
planning/scenarios-2026-10-04.md is the coverage map they were cut from:
which question each entry answers and the gaps no entry answers.

`run` hands the tier's modules and opt-in variables to tools/hbox_native.sh
with `--box BOX --image-set SHA` and the four published images, so nothing
is certified or built: the modules run against the images the integrator
published for dev commit SHA (hbox:/tank/fn/images/SHA).  The tests come from
REV (default SHA itself, so the tests match the image; `.` runs this
worktree's tests, uncommitted edits included, against the published images).
It returns once the box run has started; `tools/hbox_native.sh attach LABEL`
waits for it and prints run.log.  A tier's `tool` entries are kits
hbox_native.sh cannot launch (it runs unittest modules only); `run` prints
them with $IMAGES filled in, to run by hand on hbox under swarm-build.

`modules TIER` prints the tier's modules one per line, for any other runner:
with an overlay image (tools/fn_dev.py overlay, lane loops) the modules read
the images from FN_NATIVE_DEVELOPER_HOST and the other image variables, as
every native module does, e.g.
`python3 tools/test_budget.py $(python3 tools/scenario_suite.py modules smoke)`.

`check` (make check) holds the file to its shape: every module exists (and
its class, when one is named), every question code is known, every opt-in
variable is one a module reads, no module appears twice in a tier, every
tier is non-empty, and no -mock or source-only module is listed (they answer
none of these questions).  Exit 0 or 1.
"""
from __future__ import annotations

import argparse
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TIERS_FILE = "tests/scenarios/tiers.tsv"
TIERS = ("peer", "smoke", "core", "e2e", "resilience", "scale")
KINDS = ("module", "env", "tool")
QUESTIONS = {"DUR", "ARU", "IDEM", "BND", "MEM", "LAT", "FSYNC", "OPEN", "PEER", "BP",
             "WEB", "AUTH", "CUR", "RCON", "IDN", "RDR", "CKPT", "OPS", "INTEROP"}
IMAGES = "developer,production,dtn,dtn-developer"
IMAGE_BASE = "/tank/fn/images"


def entries(root: pathlib.Path = ROOT) -> list[tuple[int, str, str, str, str, str]]:
    """(line number, tier, kind, entry, questions, why) for each line."""
    out = []
    for number, line in enumerate((root / TIERS_FILE).read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        fields += [""] * (5 - len(fields))
        out.append((number, *fields[:5]))
    return out


def tier(name: str, root: pathlib.Path = ROOT) -> dict[str, list[str]]:
    got: dict[str, list[str]] = {kind: [] for kind in KINDS}
    for _, t, kind, entry, _, _ in entries(root):
        if t == name and kind in got:
            got[kind].append(entry)
    return got


def image_reads(root: pathlib.Path, module: str, text: str) -> list[str]:
    """The variables MODULE reads, through its tests/ helpers too (tools/native_env.py)."""
    if root == ROOT:
        sys.path.insert(0, str(ROOT / "tools"))
        import native_env  # noqa: E402
        return native_env.reads("tests." + module)
    return re.findall(r'"(FN_[A-Z0-9_]+)"', text)


HEAP_OPTOUT = re.compile(r"image_heap=|[\"']SBCL_USER_ARGS[\"']|[\"']FN_TEST_HEAP_MB[\"']")


def heap_optouts(root: pathlib.Path = ROOT) -> list[str]:
    """Native test lines that run an owner at a heap of their own choosing
    instead of the installed launcher's decided figure (tests/native_harness.py
    Node.launch): Node(image_heap=REASON), or SBCL_USER_ARGS / FN_TEST_HEAP_MB
    set by the test.  The decided-launch ruling (2026-10-04) has them counted."""
    out = []
    for path in sorted((root / "tests").glob("test_*.py")):
        if "native" not in path.name and not path.name.startswith("test_bp_"):
            continue
        for number, line in enumerate(path.read_text(encoding="utf-8", errors="replace")
                                      .splitlines(), 1):
            if HEAP_OPTOUT.search(line) and not line.lstrip().startswith("#"):
                out.append(f"{path.relative_to(root)}:{number}: {line.strip()[:120]}")
    return out


def findings(root: pathlib.Path = ROOT) -> list[str]:
    out: list[str] = []
    seen: dict[tuple[str, str], int] = {}
    tests_text = "\n".join(p.read_text(encoding="utf-8", errors="replace")
                           for p in sorted((root / "tests").glob("test_*.py")))
    for number, t, kind, entry, questions, why in entries(root):
        where = f"{TIERS_FILE}:{number}"
        if t not in TIERS:
            out.append(f"{where}: unknown tier {t!r} (one of {', '.join(TIERS)})")
        if kind not in KINDS:
            out.append(f"{where}: unknown kind {kind!r} (one of {', '.join(KINDS)})")
            continue
        unknown = [q for q in questions.split(",") if q not in QUESTIONS]
        if unknown or not questions:
            out.append(f"{where}: unknown question code(s) {unknown or [questions]}")
        if not why.strip():
            out.append(f"{where}: no reason given")
        if (t, entry) in seen:
            out.append(f"{where}: {entry} is already in tier {t} at line {seen[(t, entry)]}")
        seen[(t, entry)] = number
        if kind == "module":
            parts = entry.split(".")
            path = root / "tests" / (parts[1] + ".py") if len(parts) >= 2 else None
            if len(parts) not in (2, 3) or parts[0] != "tests" or not path.is_file():
                out.append(f"{where}: {entry}: no such test module")
                continue
            text = path.read_text(encoding="utf-8", errors="replace")
            if len(parts) == 3 and not re.search(rf"^class {re.escape(parts[2])}\b", text, re.M):
                out.append(f"{where}: {entry}: no class {parts[2]} in {path.relative_to(root)}")
            if "-mock" in parts[1] or "mock" in parts[1].split("_"):
                out.append(f"{where}: {entry}: a -mock module answers no scenario question")
            if not any(re.fullmatch(r"FN_NATIVE_[A-Z_]*HOST", name)
                       for name in image_reads(root, parts[1], text)):
                out.append(f"{where}: {entry}: reads no image variable, so it drives no image")
        elif kind == "env":
            name = entry.split("=", 1)[0]
            if "=" not in entry or not re.fullmatch(r"[A-Z][A-Z0-9_]*", name):
                out.append(f"{where}: {entry}: not NAME=VALUE")
            elif name not in tests_text:
                out.append(f"{where}: {name}: no test module reads it")
    for t in TIERS:
        if not tier(t, root)["module"]:
            out.append(f"{TIERS_FILE}: tier {t} lists no module")
    return out


def run(args: argparse.Namespace) -> int:
    got = tier(args.tier)
    if not got["module"]:
        print(f"scenario_suite: tier {args.tier} lists no module", file=sys.stderr)
        return 2
    if not re.fullmatch(r"[0-9a-f]{7,40}", args.image_set):
        print("scenario_suite: --image-set takes a commit sha", file=sys.stderr)
        return 2
    sha = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--verify", "--quiet",
                          args.image_set + "^{commit}"],
                         capture_output=True, text=True).stdout.strip() or args.image_set
    rev = args.rev or sha
    label = args.label or f"{args.tier}-{sha[:9]}"
    argv = ["sh", str(ROOT / "tools/hbox_native.sh"), "--box", args.box, "--image-set", sha,
            "--images", IMAGES, "--jobs", str(args.jobs), "--label", label]
    for env in got["env"]:
        argv += ["--env", env]
    argv += list(args.extra) + [rev] + got["module"]
    print("scenario_suite: " + " ".join(argv), flush=True)
    for tool in got["tool"]:
        words = [f"{IMAGE_BASE}/{sha}" + w[len("$IMAGES"):] if w.startswith("$IMAGES")
                 else sha if w == "SHA" else w for w in tool.split(" ")]
        print("scenario_suite: by hand on hbox: " + " ".join(words), flush=True)
    if args.dry_run:
        return 0
    return subprocess.call(argv, cwd=ROOT)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("list")
    p.add_argument("tier", nargs="?", choices=TIERS)
    p = sub.add_parser("modules")
    p.add_argument("tier", choices=TIERS)
    sub.add_parser("check")
    sub.add_parser("heap-optouts")
    p = sub.add_parser("run")
    p.add_argument("tier", choices=TIERS)
    p.add_argument("--image-set", required=True, help="the dev commit whose published images to use")
    p.add_argument("--rev", help="the tests' revision (default: the image set's; `.` = this worktree)")
    p.add_argument("--label")
    p.add_argument("--jobs", type=int, default=4)
    p.add_argument("--box", default="hbox",
                   help="hbox (default: the INN tree, docker and the fixtures live there) or a "
                        "rented box from ~/.config/fn/boxes.json (lat1, cloud1, cloud2: they "
                        "mirror the published image sets)")
    p.add_argument("--dry-run", action="store_true")
    p.add_argument("extra", nargs="*", help="further tools/hbox_native.sh options, after --")
    args = parser.parse_args(argv)
    if args.command == "check":
        found = findings()
        for line in found:
            print("scenario_suite: " + line)
        if not found:
            counts = ", ".join(f"{t} {len(tier(t)['module'])}" for t in TIERS)
            print(f"scenario_suite: {TIERS_FILE} well formed ({counts} modules); "
                  f"{len(heap_optouts())} native test lines choose their own heap "
                  "(heap-optouts lists them)")
        return 1 if found else 0
    if args.command == "heap-optouts":
        found = heap_optouts()
        print("\n".join(found))
        print(f"scenario_suite: {len(found)} native test lines choose their own heap")
        return 0
    if args.command == "modules":
        print("\n".join(tier(args.tier)["module"]))
        return 0
    if args.command == "list":
        for _, t, kind, entry, questions, why in entries():
            if args.tier in (None, t):
                print(f"{t}\t{kind}\t{entry}\t{questions}\t{why}")
        return 0
    return run(args)


if __name__ == "__main__":
    sys.exit(main())
