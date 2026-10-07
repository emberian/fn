#!/usr/bin/env python3
"""L-FRESH: does a fresh node start under a whole-process memory limit?

For each LIMIT (MB) this makes a work directory, runs the production image's
`--fn operator CONFIG init` with the small preset (tests/test_native_image_heap.py's
INIT_FLAGS), then starts the node the way an installed node starts
(tests.native_harness.installed_launcher: packaging/fn, which runs the image's
heap probe and may refuse the profile on this machine) inside
`systemd-run --user --scope -p MemoryMax=<limit>M -p MemorySwapMax=0`, waits for
LISTENING, POSTs one 2048-octet article, reads it back with ARTICLE, records
VmRSS/VmHWM at LISTENING and after, and stops the owner by its own recorded PID
(SIGTERM, then SIGKILL to that PID only).  A refused start is the result: its
stderr (and the heap probe's line) is recorded verbatim.  One JSON document on stdout; Linux only.

  tools/load_fresh_start.py --image IMAGE --work DIR [--limit-mb 256 --limit-mb 1024]
                            [--tree DIR_WITH_tests_AND_packaging]
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

INIT_FLAGS = ("--profile", "development", "--max-transactions", "16384",
              "--max-history-octets", "8388608", "--max-record-octets", "196608",
              "--max-groups-per-article", "16", "--max-open-suffix", "128")
LINE = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdef\r\n"


def article(i, octets=2048):
    head = ("From: fresh@example.invalid\r\nNewsgroups: fn.test\r\nSubject: fresh %d\r\n"
            "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\n"
            "Message-ID: <fresh-%06d@example.invalid>\r\n\r\n" % (i, i)).encode("ascii")
    need = octets - len(head)
    body = LINE * (need // len(LINE))
    rest = need - len(body)
    if rest >= 2:
        body += LINE[:rest - 2] + b"\r\n"
    return head + body


def status_kib(pid):
    try:
        text = Path("/proc/%d/status" % pid).read_text()
    except OSError:
        return None
    return {k: int(m.group(1)) for k in ("VmRSS", "VmHWM", "RssAnon", "RssFile")
            if (m := re.search(k + r":\s+(\d+) kB", text))}


def tail(path, n=2000):
    try:
        return Path(path).read_bytes()[-n:].decode("utf-8", "replace")
    except OSError:
        return ""


def one(limit_mb, image, work, harness, timeout=120):
    d = Path(work) / ("fresh-%d" % limit_mb)
    if d.exists():  # a fresh store every time: an earlier run's directory is left alone
        d = Path(work) / ("fresh-%d-%d" % (limit_mb, int(time.time())))
    d.mkdir(parents=True)
    port = harness.free_port()
    config = d / "fn.toml"
    config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                      '[control]\npath = "{}"\n'.format(d / "store", port, d / "control.sock"))
    env = harness.environment({"FN_NATIVE_HOST": None})
    out = {"limit_mb": limit_mb, "image": str(image), "dir": str(d), "port": port,
           "load": os.getloadavg(), "preset": "small (INIT_FLAGS)"}
    init = subprocess.run([str(image), "--fn", "operator", str(config), "init", *INIT_FLAGS,
                           "fn.letters", "fn.test"], env=env, capture_output=True, timeout=600)
    out["init_exit"] = init.returncode
    out["init_stderr_tail"] = init.stderr[-600:].decode("utf-8", "replace")
    if init.returncode != 0:
        out["verdict"] = "init-failed"
        return out
    launcher = harness.installed_launcher(image)
    # The decided heap, recorded: the same probe packaging/fn runs first
    # (`IMAGE --fn heap -- operator CONFIG run`), under the same limit.
    core = Path(str(image) + ".core")
    boot = (core.stat().st_size + 1048575) // 1048576 + 128 if core.exists() else 256
    probe = subprocess.run(
        ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=%dM" % limit_mb,
         "-p", "MemorySwapMax=0", str(image), "--fn", "heap", "--", "operator", str(config), "run"],
        env=dict(env, SBCL_USER_ARGS="--dynamic-space-size %d" % boot),
        capture_output=True, timeout=300)
    out["heap_probe"] = {"exit": probe.returncode,
                         "stdout": probe.stdout.decode("utf-8", "replace").strip(),
                         "stderr_tail": probe.stderr[-400:].decode("utf-8", "replace")}
    errp, outp = d / "run.stderr", d / "run.stdout"
    argv = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=%dM" % limit_mb,
            "-p", "MemorySwapMax=0", str(launcher), "operator", str(config), "run"]
    out["argv"] = argv
    with open(errp, "wb") as err, open(outp, "wb") as so:
        proc = subprocess.Popen(argv, env=env, stdout=so, stderr=err, cwd=str(harness.ROOT))
    out["pid"] = proc.pid
    t0, listening = time.monotonic(), False
    while time.monotonic() - t0 < timeout:
        if b"LISTENING " in outp.read_bytes():
            listening = True
            break
        if proc.poll() is not None:
            break
        time.sleep(0.2)
    out["seconds_to_listening_or_exit"] = round(time.monotonic() - t0, 2)
    out["listening"] = listening
    try:
        if listening:
            out["at_listening_kib"] = status_kib(proc.pid)
            try:
                with harness.Client(port, timeout=120) as c:
                    first, final = c.post(article(1))
                    out["post"] = [first.decode("latin1"), (final or b"").decode("latin1")]
                    body = c.article("<fresh-000001@example.invalid>")
                    out["article_octets"] = None if body is None else len(body)
                out["served"] = (out["post"][0].startswith("340") and out["post"][1].startswith("240")
                                 and out["article_octets"] is not None)
            except Exception as e:  # noqa: BLE001 - the failure is the result
                out["client_error"] = repr(e)
                out["served"] = False
            out["after_kib"] = status_kib(proc.pid)
    finally:
        if proc.poll() is None:
            proc.terminate()  # SIGTERM to the PID this script started
            try:
                proc.wait(timeout=90)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
                out["needed_sigkill"] = True
        out["exit_code"] = proc.returncode
    out["stdout_tail"] = tail(outp)
    out["stderr_tail"] = tail(errp)
    out["verdict"] = ("serves" if out.get("served") else
                      "refused-or-exited" if not listening else "listening-but-no-service")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--image", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--limit-mb", type=int, action="append")
    ap.add_argument("--tree", default=str(Path(__file__).resolve().parents[1]))
    a = ap.parse_args()
    sys.path.insert(0, a.tree)
    from tests import native_harness as harness  # noqa: PLC0415
    results = [one(m, Path(a.image).resolve(), a.work, harness) for m in (a.limit_mb or [256, 1024])]
    print(json.dumps(results, indent=1))
    return 0 if all(r.get("verdict") == "serves" for r in results) else 1


if __name__ == "__main__":
    sys.exit(main())
