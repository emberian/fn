#!/usr/bin/env python3
"""Every tracked Python file: size, category, callers, last touch, reach.

    git ls-files > DUMP/files.txt
    git log --format='@@%h|%cs|%s' --name-only -- '*.py' > DUMP/log.txt
    cp build/lanes/*/LANEDUMP.md DUMP/lanedumps/<lane>.md     (optional)
    python3 tools/py_inventory.py --dump DUMP --csv OUT.csv --md OUT.md

Run where Python is allowed (hbox, persvati); the dump is what lets a tree
without `.git` (an rsync) answer the history columns.  Without --dump it
asks git itself.

A caller is a file that names the subject: an import, a path, a unittest
module name (`tests.test_x`) or, for a basename that is unique in the tree,
the bare `name.py`.  Comments are dropped from Python callers first, so a
file that only mentions another in a comment does not call it; strings are
kept, because subprocess calls are strings.  Reach is the closure of those
edges from four root sets: `make check`'s recipe, the image-gated native
modules (cut_release.sh's rule: tests/test_*native*.py, tests/test_bp_*.py),
`make test`'s discovery (every tests/test_*.py) and the release scripts.
It is deliberately generous: a reached file may not be executed, but an
unreached file with no caller is executed by nothing in the tree.

The last-touching lane is the commit subject's prefix before its colon
(`Batch AY`, `owner-time-model-tests`), which is how commits are titled here.
"""

from __future__ import annotations

import argparse
import ast
import csv
import fnmatch
import io
import json
import re
import subprocess
import sys
import tokenize
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

CLIENTS = {"fn_reader", "fn_web", "fn_client", "fn_agent", "fn_consumer", "fn_verify", "nntp_session"}
STORE = {"run_store", "run_owner", "checkpoint", "synth_log_store"}
BUILD = {"proof_repl", "farm", "certs", "certify_books", "acl2_slots", "acl2_toolchain", "proof_artifacts",
         "test_budget", "check_steps", "labs", "cert_cache_sync", "cert_alists", "bridge_image",
         "native_env", "gate_reap", "acl2_cost", "proof_profile", "repl_census", "lift_stobj_tests"}
LINTS = {"ledger", "current_view", "merge_registry", "next_id", "teeth_check", "harness_check",
         "certified_claims", "evidence_manifests", "green_check", "proof_cost", "check_scaffold",
         "docs_check", "docs_articles", "session_depth", "changelog", "release_sequence"}
CALLER_KINDS = ("make", "sh", "packaging", "ci", "py_import", "py_path", "tests", "lisp",
                "dir_ref", "docs", "planning", "evidence", "lanedump")
CODE_KINDS = ("make", "sh", "packaging", "ci", "py_import", "py_path", "tests", "lisp", "dir_ref")


def category(path: str, stem: str) -> str:
    if path.startswith("planning/evidence/"):
        return "evidence"
    if path.startswith("site/"):
        return "docs"
    if path.startswith("tests/"):
        return "tests" if re.match(r"tests/test_[^/]*\.py$", path) else "instruments"
    if stem in CLIENTS:
        return "clients"
    if stem in STORE:
        return "store"
    if stem in BUILD:
        return "build"
    if stem in LINTS or stem.endswith("_check"):
        return "lints"
    return "other"


def caller_kind(path: str) -> str:
    if path == "Makefile":
        return "make"
    if path.startswith(".github/"):
        return "ci"
    if path.startswith("packaging/"):
        return "packaging"
    if path.startswith("planning/evidence/"):
        return "evidence"
    if path.endswith(".sh"):
        return "sh"
    if path.endswith(".py"):
        return "tests" if path.startswith("tests/") else "py"
    if path.endswith(".lisp") or path.endswith(".lsp"):
        return "lisp"
    if path.startswith(("docs/", "specs/", "site/")) or path in ("README.md", "CONTRIBUTING.md", "AGENTS.md"):
        return "docs"
    if path.startswith("planning/"):
        return "planning"
    return "other"


def strip_comments(text: str) -> str:
    try:
        tokens = [t for t in tokenize.generate_tokens(io.StringIO(text).readline) if t.type != tokenize.COMMENT]
        return tokenize.untokenize(tokens)
    except (tokenize.TokenError, IndentationError, SyntaxError):
        return text


def load(args) -> tuple[list[str], dict[str, tuple[str, str, str, str]], dict[str, str]]:
    if args.dump:
        dump = Path(args.dump)
        files = dump.joinpath("files.txt").read_text().split("\n")
        log = dump.joinpath("log.txt").read_text()
        lanedumps = {p.stem: p.read_text(errors="replace") for p in sorted(dump.glob("lanedumps/*.md"))}
    else:
        files = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=True).stdout.split("\n")
        log = subprocess.run(["git", "log", "--format=@@%h|%cs|%s", "--name-only", "--", "*.py"],
                             cwd=ROOT, capture_output=True, text=True, check=True).stdout
        lanedumps = {p.parent.name: p.read_text(errors="replace") for p in sorted(ROOT.glob("build/lanes/*/LANEDUMP.md"))}
    files = [f for f in files if f]
    last: dict[str, tuple[str, str, str, str]] = {}
    first: dict[str, str] = {}
    commit = None
    for line in log.split("\n"):
        if line.startswith("@@"):
            commit = line[2:].split("|", 2)
        elif line and commit:
            last.setdefault(line, (commit[0], commit[1], commit[2], lane_of(commit[2])))
            first[line] = commit[1]
    return files, {k: v + (first.get(k, ""),) for k, v in last.items()}, lanedumps


def lane_of(subject: str) -> str:
    match = re.match(r"(?:Merge (?:branch )?'?(?:lane/)?)?([A-Za-z0-9][\w./ -]{0,40}?)(?:'|:| into )", subject)
    return match.group(1).strip() if match else ""


IMPORT = re.compile(r"^\s*(?:from\s+([\w.]+)\s+import\s+([\w., ()]+)|import\s+([\w., ]+))", re.M)
DYNAMIC = re.compile(r"import_module\(\s*['\"]([\w.]+)['\"]")


def imported_names(text: str) -> set[str]:
    """Every dotted segment a Python file imports, statically or by name."""
    names: set[str] = set()
    for source, members, plain in IMPORT.findall(text):
        for dotted in [source] + re.split(r"[\s,()]+", members or "") + re.split(r"[\s,]+", plain or ""):
            names.update(part for part in dotted.split(".") if part and part != "as")
    for dotted in DYNAMIC.findall(text):
        names.update(dotted.split("."))
    return names


def names_target(text: str, path: str, stem: str, unique_base: bool) -> bool:
    if path in text or re.search(re.escape(path[:-3].replace("/", ".")) + r"\b", text):
        return True
    return unique_base and re.search(r"(?<![\w.-])" + re.escape(stem) + r"\.py\b", text) is not None


def check_roots(makefile: str) -> set[str]:
    match = re.search(r"^check:\n((?:\t.*\n|#.*\n)+)", makefile, re.M)
    recipe = match.group(1) if match else ""
    roots = set(re.findall(r"((?:tools|site|tests)/[\w/]+\.py)", recipe))
    roots |= {m.replace(".", "/") + ".py" for m in re.findall(r"unittest -q (tests\.test_\w+)", recipe)}
    return roots


HARNESS = re.compile(r"^_?(start|stop|launch|spawn|boot|serve|run_node|kill|terminate|wait_for|wait_until|connect|client|"
                     r"nntp|send|command|read_reply|reply|expect|free_port|pick_port|port|image|env|node_env|fresh_store|"
                     r"make_store|init_store|store_init|new_store|temp|announce|control|owner|socket|recv|readline|talk|"
                     r"session|post|login|auth|shutdown|cleanup|teardown|setup)", re.I)


def harness_lines(text: str) -> tuple[int, int]:
    """Lines in definitions shaped like node/client harness code, and Popen sites.

    The T2 estimate: what a shared tests/native_harness.py could absorb.  A
    name heuristic, over-inclusive for `send`/`command` and blind to inline
    setup, so it is an estimate by function, not a measurement of duplication."""
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return 0, 0
    spans = [n.end_lineno - n.lineno + 1 for n in ast.walk(tree)
             if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
             and HARNESS.match(n.name) and not n.name.startswith("test")]
    return sum(spans), text.count("subprocess.Popen")


def classify(rows: list[dict], spec: dict) -> None:
    """First matching rule wins; a tests/ file importing a host tool and
    naming no native image is `python-host-test` (T5) unless a rule
    before the catch-alls names it."""
    host = set(spec["host_tools"])
    markers = spec["native_markers"]
    catch_all = {"*", "planning/evidence/*"}
    for r in rows:
        path, stem = r["path"], Path(r["path"]).stem
        text = (ROOT / path).read_text(errors="replace")
        rule = next(x for x in spec["rules"] if fnmatch.fnmatch(path, x["glob"]))
        if rule["glob"] in catch_all:
            if path.startswith("tools/") and stem in host:
                rule = {"class": "RETIRE-WITH-DEPENDENCY", "tranche": "T5", "saving": 1,
                        "reason": "the Python host (retired 2026-09-19): the ACL2 model is the model, the native store makes fixtures"}
            elif path.startswith("tests/") and imported_names(text) & host and not any(m in text for m in markers):
                rule = {"class": "RETIRE-WITH-DEPENDENCY", "tranche": "T5", "saving": 1,
                        "reason": "python-host-test: drives the Python host and names no native image"}
        r["class"], r["tranche"], r["reason"] = rule["class"], rule["tranche"], rule["reason"]
        r["removed"] = round(r["lines"] * rule["saving"])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--dump", help="directory with files.txt, log.txt, lanedumps/*.md")
    parser.add_argument("--csv", required=True)
    parser.add_argument("--md")
    parser.add_argument("--classes", help="rules JSON: class, tranche and saving per glob (first match wins)")
    args = parser.parse_args()
    files, history, lanedumps = load(args)
    pys = sorted(f for f in files if f.endswith(".py") and (ROOT / f).is_file())
    texts: dict[str, str] = {}
    for f in files:
        p = ROOT / f
        if not p.is_file() or p.stat().st_size > 1_000_000:
            continue
        if f.startswith("planning/evidence/") and not f.endswith((".py", ".md", ".sh")):
            continue
        try:
            raw = p.read_text()
        except (UnicodeDecodeError, OSError):
            continue
        texts[f] = strip_comments(raw) if f.endswith(".py") else raw
    tokens = {f: set(re.findall(r"\w+", t)) for f, t in texts.items()}
    imports = {f: imported_names(t) for f, t in texts.items() if f.endswith(".py")}
    base_count = defaultdict(int)
    for f in pys:
        base_count[Path(f).name] += 1

    callers: dict[str, dict[str, list[str]]] = {}
    edges: dict[str, set[str]] = defaultdict(set)
    for target in pys:
        stem = Path(target).stem
        unique = base_count[Path(target).name] == 1
        found: dict[str, list[str]] = defaultdict(list)
        for f, text in texts.items():
            if f == target or stem not in tokens[f]:
                continue
            imported = stem in imports.get(f, ())
            if not imported and not names_target(text, target, stem, unique):
                continue
            kind = caller_kind(f)
            if kind in ("py", "tests"):
                if kind == "py":
                    kind = "py_import" if imported else "py_path"
                found[kind].append(f)
                edges[f].add(target)
            else:
                found[kind].append(f)
                if kind in ("make", "sh", "packaging", "ci"):
                    edges[f].add(target)
        # An overlay or lab directory named as a whole (`tests/tcpcl_lab_fake`)
        # reaches every file under it.
        parents = [str(q) for q in Path(target).parents if len(q.parts) >= 2]
        for f, text in texts.items():
            if f != target and not f.startswith(tuple(q + "/" for q in parents)) and caller_kind(f) not in (
                    "docs", "planning", "evidence", "other") and any(q in text for q in parents):
                found["dir_ref"].append(f)
                edges[f].add(target)
        for lane, text in lanedumps.items():
            if re.search(r"(?<![\w-])" + re.escape(stem) + r"(?:\.py)?\b", text):
                found["lanedump"].append(lane)
        callers[target] = found

    def closure(roots: set[str]) -> set[str]:
        seen, stack = set(), list(roots)
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node)
            stack.extend(edges.get(node, ()))
        return seen

    makefile = texts.get("Makefile", "")
    reach = {
        "check": closure(check_roots(makefile)),
        "native": closure({f for f in pys if re.match(r"tests/test_(.*native.*|bp_.*)\.py$", f)}),
        "test": closure({f for f in pys if re.match(r"tests/test_[^/]*\.py$", f)}),
        "release": closure({f for f in files if f in ("tools/cut_release.sh", "packaging/release-tarball.sh",
                                                        "packaging/install-clients.sh", "tools/hbox_native.sh")}),
        "make": closure({"Makefile"}),
    }

    rows = []
    for target in pys:
        stem = Path(target).stem
        found = callers[target]
        lines = (ROOT / target).read_text(errors="replace").count("\n")
        h = history.get(target, ("", "", "", "", ""))
        row = {"path": target, "lines": lines, "category": category(target, stem)}
        for kind in CALLER_KINDS:
            row[kind] = " ".join(sorted(found.get(kind, [])))
        row["n_code_callers"] = sum(len(found.get(k, [])) for k in CODE_KINDS)
        code = {f for k in CODE_KINDS for f in found.get(k, [])}
        row["self_test_only"] = bool(code) and code <= {f"tests/test_{stem}.py", f"tests/test_{stem}s.py"}
        row["reach"] = " ".join(k for k in ("check", "native", "test", "release", "make") if target in reach[k])
        row["harness_def_lines"], row["popen_sites"] = harness_lines((ROOT / target).read_text(errors="replace"))
        row.update(last_commit=h[0], last_date=h[1], last_lane=h[3], first_date=h[4], last_subject=h[2][:120])
        rows.append(row)

    if args.classes:
        classify(rows, json.loads(Path(args.classes).read_text()))
    with open(args.csv, "w", newline="") as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    if args.md:
        totals: dict[str, list[int]] = defaultdict(lambda: [0, 0])
        for r in rows:
            totals[r["category"]][0] += 1
            totals[r["category"]][1] += r["lines"]
        md = ["| category | files | lines |", "|---|---:|---:|"]
        md += [f"| {c} | {n} | {l:,} |" for c, (n, l) in sorted(totals.items(), key=lambda kv: -kv[1][1])]
        md += [f"| total | {len(rows)} | {sum(r['lines'] for r in rows):,} |", "",
               "| path | lines | cat | code callers | reach | last | lane |", "|---|---:|---|---:|---|---|---|"]
        for r in sorted(rows, key=lambda r: -r["lines"]):
            md.append(f"| {r['path']} | {r['lines']} | {r['category']} | {r['n_code_callers']} | {r['reach'] or '-'} | {r['last_date']} | {r['last_lane']} |")
        if args.classes:
            md += ["", "| tranche | class | files | lines | removed |", "|---|---|---:|---:|---:|"]
            groups: dict[tuple[str, str], list[int]] = defaultdict(lambda: [0, 0, 0])
            for r in rows:
                g = groups[(r["tranche"] or "-", r["class"])]
                g[0] += 1
                g[1] += r["lines"]
                g[2] += r["removed"]
            md += [f"| {t} | {c} | {n} | {l:,} | {x:,} |" for (t, c), (n, l, x) in sorted(groups.items())]
        Path(args.md).write_text("\n".join(md) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
