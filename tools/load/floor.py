"""Compile and run the C floors on the cell's actual work filesystem."""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import tempfile
from pathlib import Path


def run(work, reps=300):
    work = Path(work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    # A private subdirectory avoids overwriting or removing anyone else's files.
    with tempfile.TemporaryDirectory(prefix="floor-", dir=work) as scratch:
        binary = Path(scratch) / "floor"
        compiler = shutil.which("gcc") or shutil.which("cc")
        if not compiler:
            return {"not_measured": {"floor": "gcc/cc unavailable"}}
        try:
            subprocess.run([compiler, "-O2", "-pthread", str(Path(__file__).with_suffix(".c")),
                            "-o", str(binary)], capture_output=True, text=True, check=True, timeout=60)
            completed = subprocess.run([str(binary), scratch, str(reps)],
                                       capture_output=True, text=True, check=True, timeout=600)
            data = json.loads(completed.stdout)
            data["work_path"] = str(work)
            data["compiler"] = compiler
            return data
        except (subprocess.SubprocessError, ValueError, OSError) as exc:
            reason = str(exc)
            if isinstance(exc, subprocess.CalledProcessError):
                reason += ": " + exc.stderr[-1000:]
            return {"not_measured": {"floor": reason}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True)
    parser.add_argument("--reps", type=int, default=300)
    args = parser.parse_args()
    print(json.dumps(run(args.work, args.reps), indent=1))


if __name__ == "__main__":
    main()
