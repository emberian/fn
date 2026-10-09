#!/usr/bin/env python3
"""Run a scenario tier against a published image set (lane scenarios, 2026-10-04).

    python3 tools/scenario_suite.py list [TIER]
    python3 tools/scenario_suite.py modules TIER
    python3 tools/scenario_suite.py run TIER --image-set SHA [--rev REV]
        [--label LABEL] [--jobs 4] [--dry-run] [-- HBOX_NATIVE_OPTION ...]
    python3 tools/scenario_suite.py check
    python3 tools/scenario_suite.py heap-optouts
    python3 tools/scenario_suite.py affected [--since REV] [--explain] [FILE ...]

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

`affected` answers which native modules a change can affect: the files
named, or those changed since REV (`git diff --name-only REV`), through
tests/scenarios/affects.tsv (path rules to the coverage map's question
codes) and planning/scenarios-2026-10-04-modules.tsv (each module's codes).
It prints the smoke tier's modules first (they always run: the
batch gate's floor), then every image-driving module the change selects, one
per line; `--explain` adds the rule that selected each.  An unclassified file
under host/, books/, packaging/ or tests/ selects every native.

`check` (make check) holds the file to its shape: every module exists (and
its class, when one is named), every question code is known, every opt-in
variable is one a module reads, no module appears twice in a tier, every
tier is non-empty, and no -mock or source-only module is listed (they answer
none of these questions).  Exit 0 or 1.
"""
from __future__ import annotations

import argparse
import json
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
AFFECTS_FILE = "tests/scenarios/affects.tsv"
MODULE_MAP = "planning/scenarios-2026-10-04-modules.tsv"
# The module map's qualities whose modules drive an image (MOCK and SRC
# modules run under make check, not as natives).
IMAGE_QUALITIES = {"REAL", "OPTIN", "PINNED", "WEAK"}
FLOOR_TIERS = ("smoke",)
ESCAPES = ("host/", "books/", "packaging/", "tests/")


def entries(root: pathlib.Path = ROOT) -> list[tuple[int, str, str, str, str, str]]:
    """(line number, tier, kind, entry, questions, why) for each line."""
    out = []
    for number, line in enumerate((root / TIERS_FILE).read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        fields += [""] * (5 - len(fields))
        if "{scaling_ratio_target}" in fields[4]:
            fields[4] = fields[4].replace("{scaling_ratio_target}", scaling_target(root))
        out.append((number, *fields[:5]))
    return out


def scaling_target(root: pathlib.Path = ROOT) -> str:
    """The declared ARTICLE 8N/N ratio target: tools/scaling_baseline.json, the
    one source tests/test_native_scaling.py reads too (tools/ratchet.py
    scaling_limit says when a ceiling above it is allowed)."""
    data = json.loads((root / "tools/scaling_baseline.json").read_text(encoding="ascii"))
    return f"{data['article_ratio_target']:g}"


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
# A line whose SBCL_USER_ARGS names only the control stack keeps the decided
# heap (packaging/launcher-decide.sh composes it after the decision), so it
# chooses no heap of its own.
STACK_ONLY = re.compile(r"[\"']SBCL_USER_ARGS[\"']\s*:\s*[\"']--control-stack-size [^\"']*[\"']")


def heap_optouts(root: pathlib.Path = ROOT) -> list[str]:
    """Native test lines that run an owner at a heap of their own choosing
    instead of the installed launcher's decided figure (tests/native_harness.py
    Node.launch): Node(image_heap=REASON), or SBCL_USER_ARGS naming a heap /
    FN_TEST_HEAP_MB set by the test (a stack-only SBCL_USER_ARGS keeps the
    decided heap).  The decided-launch ruling (2026-10-04) has them counted."""
    out = []
    for path in sorted((root / "tests").glob("test_*.py")):
        if "native" not in path.name and not path.name.startswith("test_bp_"):
            continue
        for number, line in enumerate(path.read_text(encoding="utf-8", errors="replace")
                                      .splitlines(), 1):
            if (HEAP_OPTOUT.search(line) and not line.lstrip().startswith("#")
                    and not STACK_ONLY.search(line)):
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


def affect_rules(root: pathlib.Path = ROOT) -> list[tuple[int, str, str, str]]:
    """(line number, glob, codes, why) for each rule, in file order."""
    out = []
    for number, line in enumerate((root / AFFECTS_FILE).read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t") + ["", ""]
        out.append((number, fields[0], fields[1], fields[2]))
    return out


def module_codes(root: pathlib.Path = ROOT) -> dict[str, set[str]]:
    """tests.MODULE -> its question codes, for the image-driving modules: a
    REAL/OPTIN/PINNED/WEAK row, or a mixed SRC row that a tier lists (its
    image half is why the tier names it)."""
    tiered = {".".join(e.split(".")[:2]) for _, _, kind, e, _, _ in entries(root) if kind == "module"}
    out: dict[str, set[str]] = {}
    for line in (root / MODULE_MAP).read_text(encoding="utf-8").splitlines()[1:]:
        fields = line.split("\t")
        if not (root / "tests" / (fields[0] + ".py")).is_file():
            continue
        if len(fields) >= 3 and (fields[1] in IMAGE_QUALITIES or "tests." + fields[0] in tiered):
            out["tests." + fields[0]] = {c for c in fields[2].split(",") if c in QUESTIONS}
    return out


def affect_findings(root: pathlib.Path = ROOT) -> list[str]:
    out = []
    for number, glob, codes, why in affect_rules(root):
        where = f"{AFFECTS_FILE}:{number}"
        if not glob or not why.strip():
            out.append(f"{where}: a rule needs GLOB, CODES and a reason")
        words = codes.split(",")
        if codes not in ("ALL", "NONE", "SELF") and not all(w in QUESTIONS for w in words):
            out.append(f"{where}: unknown code(s) in {codes!r}")
    known = set(module_codes(root))
    for _, _, kind, entry, _, _ in entries(root):
        name = ".".join(entry.split(".")[:2])
        if kind == "module" and name not in known:
            out.append(f"{MODULE_MAP}: {name} (a tier module) has no image-driving row")
    return out


def _first_rule(rules, path):
    import fnmatch
    return next(((n, g, c) for n, g, c, _ in rules if fnmatch.fnmatchcase(path, g)), None)


_GRAPH = None


def book_hosts(path: str) -> "set[str] | None":
    """The loaded host files whose definitions reach a definition of book
    PATH through the call graph (tools/callgraph.py: books and host files,
    an edge per mention), the image build scripts left out (they name book
    symbols to build the world, not to run them).  None when PATH defines
    nothing the graph knows (a new or deleted book: the caller takes ALL)."""
    global _GRAPH
    import collections
    if _GRAPH is None:
        sys.path.insert(0, str(ROOT / "tools"))
        import callgraph  # noqa: E402
        graph = callgraph.build(callgraph.tree_files())
        back: dict[str, set[str]] = collections.defaultdict(set)
        for source, targets in graph.edges.items():
            for one in targets:
                back[one].add(source)
        bypath: dict[str, set[str]] = collections.defaultdict(set)
        for name, definitions in graph.definitions.items():
            for definition in definitions:
                bypath[definition.path].add(name)
        _GRAPH = (graph, back, bypath)
    graph, back, bypath = _GRAPH
    seen = set(bypath.get(path, ()))
    if not seen:
        return None
    frontier = list(seen)
    while frontier:
        following = []
        for name in frontier:
            for caller in back.get(name, ()):
                if caller not in seen:
                    seen.add(caller)
                    following.append(caller)
        frontier = following
    return {d.path for name in seen for d in graph.definitions.get(name, ())
            if d.path.startswith("host/") and not d.path.startswith("host/native/build")}


def _python_defs(source: str):
    """(key -> ast dump, key -> names it mentions, module-level dumps) of a
    Python file: top-level functions and classes' members by key
    (`f', `Class.m', `Class.<body>'); imports are left out of the module
    level (make check's native_source_check imports every module)."""
    import ast
    tree = ast.parse(source)
    dumps, refs, rest = {}, {}, []

    def names(node):
        found = set()
        for sub in ast.walk(node):
            if isinstance(sub, ast.Name):
                found.add(sub.id)
            elif isinstance(sub, ast.Attribute):
                found.add(sub.attr)
        return found

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            dumps[node.name], refs[node.name] = ast.dump(node), names(node)
        elif isinstance(node, ast.ClassDef):
            other = []
            for member in node.body:
                if isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    key = node.name + "." + member.name
                    dumps[key], refs[key] = ast.dump(member), names(member)
                else:
                    other.append(member)
            key = node.name + ".<body>"
            dumps[key] = ast.dump(ast.Module(body=other, type_ignores=[])) + repr(
                [ast.dump(b) for b in node.bases])
            refs[key] = set().union(*(names(m) for m in other)) if other else set()
        elif not isinstance(node, (ast.Import, ast.ImportFrom)):
            rest.append(ast.dump(node))
    return dumps, refs, rest


def helper_names(path: str, since: str, root: pathlib.Path = ROOT) -> "set[str] | None":
    """The names whose behaviour a change to the Python test helper PATH
    since SINCE can alter: the changed functions and class members, and every
    member of the file that mentions one of those names, to a fixed point.
    None when the file is new or deleted, or a module-level statement other
    than an import changed (the caller takes the file's rule, ALL)."""
    old = subprocess.run(["git", "-C", str(root), "show", f"{since}:{path}"],
                         capture_output=True, text=True)
    if old.returncode != 0 or not (root / path).is_file():
        return None
    try:
        before = _python_defs(old.stdout)
        after = _python_defs((root / path).read_text(encoding="utf-8"))
    except SyntaxError:
        return None
    if before[2] != after[2]:
        return None
    changed = {k for k in set(before[0]) | set(after[0]) if before[0].get(k) != after[0].get(k)}
    hit = {k.split(".")[-1] for k in changed if not k.endswith(".<body>")}
    hit |= {k.split(".")[0] for k in changed if k.endswith(".<body>")}
    while True:
        more = {k.split(".")[-1] if not k.endswith(".<body>") else k.split(".")[0]
                for k, mentioned in after[1].items() if mentioned & hit} - hit
        if not more:
            return hit
        hit |= more


def _module_text(name: str, root: pathlib.Path, seen: set) -> str:
    """tests/NAME.py and, transitively, the tests modules it imports."""
    if name in seen:
        return ""
    seen.add(name)
    path = root / "tests" / (name + ".py")
    if not path.is_file():
        return ""
    text = path.read_text(encoding="utf-8", errors="replace")
    imported = set(re.findall(r"^\s*from tests(?:\.(\w+))? import ([\w, ()]+)", text, re.M))
    more = []
    for module, names in imported:
        if module:
            more.append(module)
        else:
            more += [n.strip() for n in names.strip("()").split(",") if n.strip()]
    more += re.findall(r"^\s*import tests\.(\w+)", text, re.M)
    return text + "".join(_module_text(m, root, seen) for m in more if m != "native_harness")


def affected(paths: list[str], root: pathlib.Path = ROOT, since: "str | None" = None) -> dict[str, str]:
    """tests.MODULE -> why, for every native module PATHS can affect,
    the floor tier (smoke) first.  With SINCE, a changed Python test helper
    selects only the modules that mention a name its change can alter."""
    codes = module_codes(root)
    chosen: dict[str, str] = {}
    for t in FLOOR_TIERS:
        for entry in tier(t, root)["module"]:
            chosen.setdefault(".".join(entry.split(".")[:2]), f"tier {t} (always)")
    rules = affect_rules(root)

    def select(word: str, why: str) -> None:
        if word == "NONE":
            return
        wanted = None if word == "ALL" else set(word.split(","))
        for name, have in sorted(codes.items()):
            if wanted is None or have & wanted:
                chosen.setdefault(name, why)

    for path in paths:
        rule = _first_rule(rules, path)
        if (since and path.startswith("tests/") and path.endswith(".py")
                and not pathlib.PurePath(path).name.startswith("test_")):
            names = helper_names(path, since, root)
            if names is not None:
                pattern = re.compile(r"\b(" + "|".join(map(re.escape, sorted(names))) + r")\b") if names else None
                for name in sorted(codes):
                    if pattern and pattern.search(_module_text(name[len("tests."):], root, set())):
                        chosen.setdefault(name, f"{path} changes {', '.join(sorted(names))[:120]}")
                continue
        if rule is None and path.startswith("books/") and path.endswith(".lisp") and root == ROOT:
            hosts = book_hosts(path)
            if hosts is None:
                select("ALL", f"{path}: a book the call graph does not know: ALL")
                continue
            words = set()
            for host in sorted(hosts):
                hr = _first_rule(rules, host)
                words.add(hr[2] if hr else "ALL")
            if "ALL" in words:
                culprits = sorted(h for h in hosts if (_first_rule(rules, h) or (0, 0, "ALL"))[2] == "ALL")
                select("ALL", f"{path} reached from {', '.join(culprits[:3])}: ALL")
            elif words - {"NONE"}:
                merged = ",".join(sorted(set().union(*(w.split(",") for w in words - {"NONE"}))))
                select(merged, f"{path} reached from {len(hosts)} host file(s): {merged}")
            continue
        if rule is None:
            if not path.startswith(ESCAPES):
                continue
            rule = (0, "(unclassified)", "ALL")
        number, glob, word = rule
        why = f"{path} ({AFFECTS_FILE}:{number} {glob} {word})" if number else f"{path} unclassified: ALL"
        if word == "SELF":
            name = "tests." + pathlib.PurePath(path).stem
            if name in codes:
                chosen.setdefault(name, why)
            continue
        select(word, why)
    return chosen


def changed_since(rev: str, root: pathlib.Path = ROOT) -> list[str]:
    result = subprocess.run(["git", "-C", str(root), "diff", "--name-only", rev],
                            capture_output=True, text=True, check=True)
    return [line for line in result.stdout.splitlines() if line]


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
    envs = [word for env in got["env"] for word in ("--env", env)]
    if args.box in (None, "auto"):
        # boxq places the job (lane cloud): it shards the modules over the
        # boxes that hold the set and records the verdicts; no second scheduler
        # here.  The tier's opt-in variables name hbox's trees (INN, docker), so
        # on a rented box their gated cases skip by name (--allow-skips).
        if not (ROOT / "tools/boxq.py").is_file():
            print("scenario_suite: tools/boxq.py is not in this tree; name --box hbox "
                  "(or another box)", file=sys.stderr)
            return 2
        argv = ["python3", str(ROOT / "tools/boxq.py"), "submit", "--kind", "native",
                "--priority", args.priority, "--image-set", sha, "--rev", rev,
                "--images", IMAGES, "--note", label]
        argv += (["--wait"] if args.wait else []) + got["module"]
        argv += ["--", "--allow-skips"] + envs + list(args.extra)
    else:
        argv = ["sh", str(ROOT / "tools/hbox_native.sh"), "--box", args.box, "--image-set", sha,
                "--images", IMAGES, "--jobs", str(args.jobs), "--label", label]
        argv += envs + list(args.extra) + [rev] + got["module"]
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
    p = sub.add_parser("affected")
    p.add_argument("--since", help="every file changed since REV (git diff --name-only REV)")
    p.add_argument("--explain", action="store_true", help="name the rule that selected each module")
    p.add_argument("files", nargs="*")
    p = sub.add_parser("run")
    p.add_argument("tier", choices=TIERS)
    p.add_argument("--image-set", required=True, help="the dev commit whose published images to use")
    p.add_argument("--rev", help="the tests' revision (default: the image set's; `.` = this worktree)")
    p.add_argument("--label")
    p.add_argument("--jobs", type=int, default=4)
    p.add_argument("--box", default="auto",
                   help="auto (default): tools/boxq.py places and shards the job on the boxes "
                        "that hold the set; hbox (the INN tree, docker and the fixtures live "
                        "there) or another box: tools/hbox_native.sh there, as named")
    p.add_argument("--priority", default="lane", choices=("lane", "fill"),
                   help="boxq priority (with --box auto)")
    p.add_argument("--wait", action="store_true", help="boxq: wait for the verdict")
    p.add_argument("--dry-run", action="store_true")
    p.add_argument("extra", nargs="*", help="further tools/hbox_native.sh options, after --")
    args = parser.parse_args(argv)
    if args.command == "check":
        found = findings() + affect_findings()
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
    if args.command == "affected":
        paths = list(args.files) + (changed_since(args.since) if args.since else [])
        for name, why in affected(paths, since=args.since).items():
            print(f"{name}\t{why}" if args.explain else name)
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
