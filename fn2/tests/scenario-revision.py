"""Identify the current checkout and source bytes used by simulator drivers."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()


def digest(paths):
    h = hashlib.sha256()
    for path in sorted(paths):
        h.update(str(path.relative_to(root)).encode() + b"\0")
        h.update(hashlib.sha256(path.read_bytes()).digest())
    return h.hexdigest()


runtime = [p for directory in ("books", "sim")
           for p in (root / "fn2" / directory).glob("*.lisp")]
tests = [p for p in (root / "fn2/tests").iterdir()
         if p.suffix in (".lisp", ".lsp", ".py")]
revision = (f"HEAD={head};fn2-runtime-sha256={digest(runtime)};"
            f"fn2-tests-sha256={digest(tests)}")
sys.stdout.write("(defconst *fn2-scenario-revision* " + json.dumps(revision) + ")\n")
