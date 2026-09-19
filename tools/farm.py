#!/usr/bin/env python3
"""Run fn's certification on a farm box and bring the evidence home.

The laptop is the wrong machine for a wide certification: it has four ACL2
slots and other work on it.  persvati and hbox are the farm.  Because every
tool sets ``ACL2_BOOK_HASH_ALISTP=NIL``, certificates produced there are valid
here, so a farm run is not a separate world: it is the same certification with
the evidence and the certificate pairs rsynced back and published to the local
cache.

    python3 tools/farm.py submit persvati --jobs 12 --affected-by books/wire.lisp
    python3 tools/farm.py wait persvati run-20260919T101500Z-4f2a
    python3 tools/farm.py status hbox

``submit`` mirrors this worktree to the *same absolute path* on the host,
starts the runner detached with its own log and status file, and returns a run
id.  ``wait`` blocks on that id, printing progress every poll and never
spinning; it returns the runner's own exit code.  hbox is co-tenant, so its
runner is wrapped in ``swarm-build``, which enforces the memory cap there.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import secrets
import shlex
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs  # noqa: E402

HOSTS = {
    "persvati": {
        "acl2": "$HOME/fn-tools/acl2-8.7/saved_acl2",
        "cache": "~/fn-certcache",
        "wrap": "",
    },
    "hbox": {
        "acl2": "/tank/fn/acl2-8.7/saved_acl2",
        "cache": "/tank/fn/certcache",
        # hbox is shared with another project's build; swarm-build is the
        # cgroup with the enforced memory cap.
        "wrap": "swarm-build",
    },
}
EXCLUDES = ("build/", ".git/", "__pycache__/", ".venv/", "*.pyc")
POLL_SECONDS = 30
DEFAULT_WAIT_SECONDS = 6 * 60 * 60
EVIDENCE = re.compile(r"Certification evidence: (build/acl2/[A-Za-z0-9._-]+)")

# Seams: the tests drive the real command construction through these.
RUN = subprocess.run
SLEEP = time.sleep


def host_settings(host: str) -> dict:
    return HOSTS.get(host, {"acl2": "acl2", "cache": "~/fn-certcache", "wrap": ""})


def run(command: list[str], check: bool = True) -> subprocess.CompletedProcess:
    return RUN(command, check=check, stdout=subprocess.PIPE,
               stderr=subprocess.STDOUT, text=True)


def ssh(host: str, script: str, check: bool = True) -> subprocess.CompletedProcess:
    return run(["ssh", "-n", host, script], check=check)


def run_id() -> str:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return f"run-{stamp}-{secrets.token_hex(2)}"


def record_path(root: Path, identifier: str) -> Path:
    return root / "build" / "farm" / f"{identifier}.json"


def remote_root(root: Path, identifier: str, override: str | None = None) -> Path:
    """Where the run lives on the box: the recorded path, or this one.

    Certificates name their sub-books by absolute path, so the path the run
    used on the box is what `certs.py` records as their origin.  When it is
    not a path on this machine, the pairs install into any worktree here.
    """
    if override:
        return Path(override)
    try:
        record = json.loads(record_path(root, identifier).read_text())
    except (OSError, ValueError):
        return root
    return Path(record.get("remote_path", str(root)))


def push(host: str, root: Path, remote: Path) -> None:
    command = ["rsync", "-a", "--delete"]
    for pattern in EXCLUDES:
        command.append(f"--exclude={pattern}")
    command.extend([f"{root}/", f"{host}:{remote}/"])
    run(command)


def remote_script(host: str, root: Path, identifier: str, books: list[str],
                  jobs: int, timeout_seconds: int, affected_by: list[str]) -> str:
    settings = host_settings(host)
    runner = ["python3", "tools/certify_books.py", "--jobs", str(jobs)]
    for path in affected_by:
        runner.extend(["--affected-by", path])
    runner.extend(books)
    if settings["wrap"]:
        runner = [settings["wrap"]] + runner
    log = f"build/farm/{identifier}.log"
    status_file = f"build/farm/{identifier}.status"
    inner = (
        f"FN_ACL2={settings['acl2']} "
        f"FN_ACL2_TIMEOUT_SECONDS={timeout_seconds} "
        f"FN_CERT_CACHE={settings['cache']} "
        + " ".join(shlex.quote(word) for word in runner)
        + f" > {log} 2>&1; echo $? > {status_file}"
    )
    return (f"cd {shlex.quote(str(root))} && mkdir -p build/farm && "
            f"nohup sh -c {shlex.quote(inner)} >/dev/null 2>&1 &")


def submit(host: str, root: Path, books: list[str], jobs: int,
           timeout_seconds: int, affected_by: list[str],
           remote: Path | None = None) -> str:
    identifier = run_id()
    remote = remote or root
    push(host, root, remote)
    ssh(host, remote_script(host, remote, identifier, books, jobs,
                            timeout_seconds, affected_by))
    record = {
        "run_id": identifier,
        "host": host,
        "path": str(root),
        "remote_path": str(remote),
        "books": books,
        "affected_by": affected_by,
        "jobs": jobs,
        "timeout_seconds": timeout_seconds,
        "submitted_at": dt.datetime.now(dt.timezone.utc).isoformat(),
    }
    path = record_path(root, identifier)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8")
    return identifier


def progress_script(root: Path, identifier: str) -> str:
    log = f"build/farm/{identifier}.log"
    return (
        f"cd {shlex.quote(str(root))} 2>/dev/null || exit 9; "
        f"printf 'STATUS %s\\n' \"$(cat build/farm/{identifier}.status "
        f"2>/dev/null || echo running)\"; "
        f"printf 'MARKERS %s\\n' \"$(grep -c FN_CERTIFY_SUCCESS {log} 2>/dev/null "
        f"|| echo 0)\"; "
        f"printf 'TAIL %s\\n' \"$(tail -c 300 {log} 2>/dev/null | tr '\\n' ' ')\""
    )


def parse_progress(output: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for line in output.splitlines():
        for key in ("STATUS", "MARKERS", "TAIL"):
            if line.startswith(key + " "):
                fields[key] = line[len(key) + 1:].strip()
    return fields


def wait(host: str, identifier: str, root: Path, poll: int = POLL_SECONDS,
         timeout_seconds: int = DEFAULT_WAIT_SECONDS) -> int:
    """Block until the remote run writes its status file, then fetch evidence."""
    started = time.monotonic()
    remote = remote_root(root, identifier)
    while True:
        progress = parse_progress(ssh(host, progress_script(remote, identifier),
                                      check=False).stdout)
        state = progress.get("STATUS", "running")
        if state != "running":
            break
        elapsed = int(time.monotonic() - started)
        print(f"{identifier} on {host}: running, {progress.get('MARKERS', '0')} "
              f"books certified, {elapsed}s elapsed", flush=True)
        if time.monotonic() - started >= timeout_seconds:
            print(f"{identifier} on {host}: still running after "
                  f"{timeout_seconds}s; not waiting further", file=sys.stderr)
            return 3
        SLEEP(poll)
    try:
        code = int(state)
    except ValueError:
        code = 1
    fetch(host, identifier, root, remote)
    print(f"{identifier} on {host}: finished with exit code {code}")
    return code


def fetch(host: str, identifier: str, root: Path,
          remote: Path | None = None) -> None:
    """Bring back the evidence directory, the new pairs, and cache the pairs."""
    remote = remote or remote_root(root, identifier)
    log = ssh(host, f"cat {shlex.quote(str(remote))}/build/farm/{identifier}.log",
              check=False).stdout
    (root / "build" / "farm").mkdir(parents=True, exist_ok=True)
    (root / "build" / "farm" / f"{identifier}.log").write_text(log, encoding="utf-8")
    for directory in sorted(set(EVIDENCE.findall(log))):
        local = root / directory
        local.mkdir(parents=True, exist_ok=True)
        run(["rsync", "-a", f"{host}:{remote}/{directory}/", f"{local}/"], check=False)
    for directory in certs.BOOK_DIRECTORIES:
        run(["rsync", "-a", "--update", "--include=*/", "--include=*.cert",
             "--include=*.port", "--exclude=*",
             f"{host}:{remote}/{directory}/", f"{root}/{directory}/"], check=False)
    # The pairs were produced under the *remote* path, which is what their
    # sub-book entries name; record that as their origin.
    report = certs.publish(root, certs.cache_directory(),
                           origin=str(remote), origin_host=host)
    for line in report.lines():
        print(line)


def status(host: str, root: Path) -> int:
    script = (
        f"cd {shlex.quote(str(root))}/build/farm 2>/dev/null || "
        f"{{ echo 'no runs'; exit 0; }}; "
        "for log in *.log; do [ -e \"$log\" ] || continue; id=${log%.log}; "
        "state=$(cat \"$id.status\" 2>/dev/null || echo running); "
        "printf '%s %s %s\\n' \"$id\" \"$state\" "
        "\"$(grep -c FN_CERTIFY_SUCCESS \"$log\" 2>/dev/null || echo 0)\"; done"
    )
    result = ssh(host, script, check=False)
    print(f"{host}:{root}")
    print("run-id status books-certified")
    print(result.stdout.rstrip())
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=("submit", "wait", "status"))
    parser.add_argument("host")
    parser.add_argument("rest", nargs="*",
                        help="submit: book roots; wait: the run id")
    parser.add_argument("--jobs", type=int,
                        default=int(os.environ.get("FN_CERTIFY_JOBS", "8")))
    parser.add_argument("--affected-by", action="append", default=[],
                        help="certify only roots whose closure contains this book")
    parser.add_argument("--timeout-seconds", type=int, default=1800,
                        help="per-ACL2-invocation timeout on the host")
    parser.add_argument("--wait-seconds", type=int, default=DEFAULT_WAIT_SECONDS,
                        help="how long `wait` blocks before giving up")
    parser.add_argument("--poll-seconds", type=int, default=POLL_SECONDS)
    parser.add_argument("--root", default=str(ROOT))
    parser.add_argument("--remote-root", default=None,
                        help="the path to use on the host (default: --root); a "
                             "path that does not exist here makes the resulting "
                             "certificates installable in any local worktree")
    arguments = parser.parse_args(argv)
    root = Path(arguments.root).resolve()
    if arguments.action == "submit":
        identifier = submit(arguments.host, root, list(arguments.rest),
                            arguments.jobs, arguments.timeout_seconds,
                            list(arguments.affected_by),
                            Path(arguments.remote_root) if arguments.remote_root
                            else None)
        print(identifier)
        return 0
    if arguments.action == "wait":
        if len(arguments.rest) != 1:
            parser.error("wait takes exactly one run id")
        return wait(arguments.host, arguments.rest[0], root,
                    arguments.poll_seconds, arguments.wait_seconds)
    return status(arguments.host,
                  Path(arguments.remote_root) if arguments.remote_root else root)


if __name__ == "__main__":
    raise SystemExit(main())
