#!/usr/bin/env python3
"""tools/extract/bench.py -- the per-command cost of extracted programs
against the SBCL developer image, on the same transcripts (lane
extract-writable, E2).

    bench.py IMAGE OUT.json LABEL=SERVED [LABEL=SERVED ...]
             [--store STORE] [--cpu N] [--runs N]

Each transcript (tools/extract/transcripts.py's timing sessions, a 2,001-
command read session, and with --store the store transcripts over a copy of
STORE) runs as one process per invocation, pinned to CPU N (taskset), RUNS
times per program, the programs INTERLEAVED run by run so a change in the
box's load lands on every program alike.  The per-command cost of a program
on a transcript is (median wall of the transcript - median wall of its
baseline) / its command count: the baseline is `bare-lf' (one command) for
the seeded archive and `store-quit' (QUIT alone) for the store, so start-up
and the store's open are subtracted.  The ratio is program / image.  Every
reply is also compared with the image's (a program whose reply differs is
reported, not timed as if it were right).
"""
import json
import os
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

X = Path(__file__).resolve().parent
sys.path.insert(0, str(X))
import transcripts  # noqa: E402

READ_2000 = (b"GROUP fn.letters\r\nSTAT\r\nARTICLE 1\r\nHEAD 1\r\n" * 500) + b"QUIT\r\n"
STORE_READ = (b"CAPABILITIES\r\nMODE READER\r\nLIST\r\nGROUP fn.test\r\nSTAT\r\nHEAD\r\nBODY\r\n"
              b"ARTICLE 1\r\nARTICLE 2\r\nNEXT\r\nLAST\r\nOVER 1-3\r\nHDR Subject 1-3\r\n")
STORE_SESSION = STORE_READ * 40 + b"QUIT\r\n"


def commands(chunks):
    return max(1, b"".join(chunks).count(b"\n"))


def main(argv):
    args, progs, store, cpu, runs = [], [], None, "20", 7
    it = iter(argv[1:])
    for a in it:
        if a == "--store":
            store = next(it)
        elif a == "--cpu":
            cpu = next(it)
        elif a == "--runs":
            runs = int(next(it))
        elif "=" in a and not a.startswith("/"):
            label, path = a.split("=", 1)
            progs.append((label, path))
        else:
            args.append(a)
    image, out = args
    tmp = Path(tempfile.mkdtemp(prefix="fn-bench-"))
    cases = {}
    for name in ("bare-lf", "reader-commands", "session-200"):
        cases[name] = (transcripts.CASES[name], None, "bare-lf")
    cases["read-2000"] = ([READ_2000], None, "bare-lf")
    if store:
        dst = tmp / "store"
        shutil.copytree(store, dst, symlinks=True)
        lock = dst / "writer.lock"
        lock.touch()
        lock.chmod(0o600)
        subprocess.run([image, "--fn", "store", str(dst), "rebind-filesystem"], check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       env=dict(os.environ, ACL2_CUSTOMIZATION="NONE"))
        cases["store-quit"] = ([b"QUIT\r\n"], str(dst), "store-quit")
        cases["store-session"] = ([STORE_SESSION], str(dst), "store-quit")
    files = {}
    for name, (chunks, _, _) in cases.items():
        f = tmp / (name + ".chunks")
        transcripts.write(f, chunks)
        files[name] = f
    everyone = [("image", None)] + progs
    walls = {(p, c): [] for p, _ in everyone for c in cases}
    replies = {}
    env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")

    def argv_of(label, path, case):
        chunks, st, _ = cases[case]
        if path is None:
            return [image, "--fn", "model", str(files[case]), st or "-"]
        return [path, "model", str(files[case])] + ([st] if st else [])

    for r in range(runs):
        for case in cases:
            for label, path in everyone:
                cmd = ["taskset", "-c", cpu] + argv_of(label, path, case)
                t0 = time.perf_counter()
                p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
                walls[(label, case)].append(time.perf_counter() - t0)
                if p.returncode != 0:
                    sys.exit("bench: %s on %s exited %d: %s" % (label, case, p.returncode,
                                                                p.stderr.decode(errors="replace")[-300:]))
                if r == 0:
                    replies[(label, case)] = p.stdout
    report = {"image": image, "cpu": cpu, "runs": runs, "programs": dict(progs), "cases": {}}
    for case, (chunks, st, base) in cases.items():
        n = commands(chunks)
        row = {"commands": n, "baseline": base}
        for label, _ in everyone:
            med = statistics.median(walls[(label, case)])
            row[label] = {"median_s": round(med, 5),
                          "identical": replies[(label, case)] == replies[("image", case)]}
        if case != base:
            for label, _ in everyone:
                per = (row[label]["median_s"] - statistics.median(walls[(label, base)])) / n
                row[label]["per_command_us"] = round(per * 1e6, 2)
            for label, _ in progs:
                im = row["image"]["per_command_us"]
                row[label]["ratio"] = round(row[label]["per_command_us"] / im, 2) if im > 0 else None
        report["cases"][case] = row
    Path(out).write_text(json.dumps(report, indent=1) + "\n")
    labels = [l for l, _ in everyone]
    print("%-16s %6s  " % ("case", "cmds") + "  ".join("%22s" % l for l in labels))
    for case, row in report["cases"].items():
        cells = []
        for l in labels:
            c = row[l]
            if "per_command_us" in c:
                cells.append("%8.1f us%s%s" % (c["per_command_us"],
                                               (" x%.2f" % c["ratio"]) if c.get("ratio") else "      ",
                                               "" if c["identical"] else " DIFFER"))
            else:
                cells.append("%10.3f s start%s" % (c["median_s"], "" if c["identical"] else " DIFFER"))
        print("%-16s %6d  " % (case, row["commands"]) + "  ".join("%22s" % x for x in cells))
    shutil.rmtree(tmp, ignore_errors=True)
    return 0 if all(row[l]["identical"] for row in report["cases"].values() for l in labels) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
