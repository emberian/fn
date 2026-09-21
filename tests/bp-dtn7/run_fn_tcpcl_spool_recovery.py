#!/usr/bin/env python3
"""Native TCPCL spool ownership, fail-closed recovery, and fence checks."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


LISTENING = re.compile(r"TCPCL LISTENING (\d+)")


def invoke(image: Path, spool: Path, env=None, timeout=20):
    return subprocess.run(
        [str(image), "--fn", "tcpcl", "listen", "0", "1", str(spool),
         "dtn://fn-b/", "-", "4", "1024", "1048576", "-", "-"],
        text=True, capture_output=True, env=env, timeout=timeout)


def spawn(image: Path, spool: Path):
    return subprocess.Popen(
        [str(image), "--fn", "tcpcl", "listen", "0", "1", str(spool),
         "dtn://fn-b/", "-", "4", "1024", "1048576", "-", "-"],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def wait_listening(process, timeout=20):
    lines = []
    deadline = time.time() + timeout
    while time.time() < deadline:
        line = process.stdout.readline()
        if line:
            lines.append(line)
            if LISTENING.search(line):
                return "".join(lines)
        elif process.poll() is not None:
            break
    raise RuntimeError("listener did not start: " + "".join(lines))


def stage(spool: Path, pid: int, digit: str) -> Path:
    path = spool / (".incoming-{}-{}".format(pid, digit * 24))
    path.write_bytes(("staged-" + digit).encode())
    return path


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--image", required=True)
    parser.add_argument("--work")
    parser.add_argument("--source-revision", default="unknown")
    parser.add_argument("--artifact-set", default="unknown")
    args = parser.parse_args(argv)
    image = Path(args.image).resolve()
    if not image.is_file():
        raise SystemExit("missing native image: {}".format(image))
    root = Path(args.work).resolve() if args.work else Path(
        tempfile.mkdtemp(prefix="fn-tcpcl-spool-"))
    if root.exists():
        shutil.rmtree(root)
    spool = root / "spool"
    spool.mkdir(parents=True)
    completed = spool / "passive-0.bundle"
    completed.write_bytes(b"authoritative completed payload\n")
    external = root / "external"
    external.write_bytes(b"must not be followed\n")

    regular = stage(spool, 123, "a")
    malicious = spool / (".incoming-124-" + "b" * 24)
    malicious.symlink_to(external)
    bad = invoke(image, spool)
    bad_output = bad.stdout + bad.stderr
    fail_closed = (bad.returncode == 4 and regular.exists() and malicious.is_symlink()
                   and external.read_bytes() == b"must not be followed\n"
                   and completed.read_bytes() == b"authoritative completed payload\n")

    malicious.unlink()
    base_env = dict(os.environ)
    unlink_env = dict(base_env)
    unlink_env["FN_TCPCL_TEST_FAIL_STAGING_UNLINK"] = "1"
    unlink_failed = invoke(image, spool, unlink_env)
    unlink_fenced = (unlink_failed.returncode == 3 and regular.exists()
                     and "injected staging cleanup unlink failure" in
                     (unlink_failed.stdout + unlink_failed.stderr))

    barrier_env = dict(base_env)
    barrier_env["FN_TCPCL_TEST_FAIL_STAGING_BARRIER"] = "1"
    barrier_failed = invoke(image, spool, barrier_env)
    barrier_fenced = (barrier_failed.returncode == 3 and not regular.exists()
                      and "injected staging cleanup barrier failure" in
                      (barrier_failed.stdout + barrier_failed.stderr))

    # A normal restart establishes the lock, completes recovery, and listens.
    process = spawn(image, spool)
    try:
        started = wait_listening(process)
        contender = invoke(image, spool)
        contention_refused = (contender.returncode == 1 and
                              "spool is already owned" in
                              (contender.stdout + contender.stderr))
        owner_alive = process.poll() is None
        recovered = (not list(spool.glob(".incoming-*")) and
                     completed.read_bytes() == b"authoritative completed payload\n")
    finally:
        process.kill()
        process.wait(timeout=10)

    report = {
        "scenario": "tcpcl-spool-recovery",
        "source_revision": args.source_revision,
        "artifact_set": args.artifact_set,
        "image": str(image),
        "image_sha256": hashlib.sha256(image.read_bytes()).hexdigest(),
        "fail_closed_symlink": fail_closed,
        "unlink_failure_fenced": unlink_fenced,
        "barrier_failure_fenced": barrier_fenced,
        "contention_refused": contention_refused,
        "owner_alive": owner_alive,
        "recovered": recovered,
        "listener_output": started.splitlines(),
        "exit_codes": {"symlink": bad.returncode,
                       "unlink": unlink_failed.returncode,
                       "barrier": barrier_failed.returncode,
                       "contender": contender.returncode},
    }
    report["ok"] = all((fail_closed, unlink_fenced, barrier_fenced,
                        contention_refused, owner_alive, recovered))
    (root / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
