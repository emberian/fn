"""Identify the current checkout and source bytes used by simulator drivers."""
import hashlib
import json
from pathlib import Path
import os
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
# FN2_SCENARIO_HEAD names the commit when the tree is a copy without .git (a box tree).
head = os.environ.get("FN2_SCENARIO_HEAD") or subprocess.check_output(
    ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()


def digest(paths):
    h = hashlib.sha256()
    for path in sorted(paths):
        h.update(str(path.relative_to(root)).encode() + b"\0")
        h.update(hashlib.sha256(path.read_bytes()).digest())
    return h.hexdigest()


runtime = [p for directory in ("books", "sim")
           for p in (root / directory).glob("*.lisp")]
tests = [p for p in (root / "tests").iterdir()
         if p.suffix in (".lisp", ".lsp", ".py")]
revision = (f"HEAD={head};fn2-runtime-sha256={digest(runtime)};"
            f"fn2-tests-sha256={digest(tests)}")
sys.stdout.write("(defconst *fn2-scenario-revision* " + json.dumps(revision) + ")\n")
