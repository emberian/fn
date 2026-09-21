#!/usr/bin/env python3
"""Measure the operator's live-owner post path and native direct paths.

This intentionally does not call ``post_article``.  Each measured owner post
is ``bin/fn post`` while ``bin/fn run`` owns the store, so the command probes
the Unix control socket and the owner performs the one durable acceptance
decision.  Setup and the optional native measurements are named separately in
the JSON; neither is presented as served-owner throughput.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import resource
from pathlib import Path
import signal
import socket
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tests.bench.generate import article_octets, message_id  # noqa: E402
from tools.run_store import MAX_TRANSACTION_COUNT  # noqa: E402

GROUPS = ("fn.letters", "fn.test")
OUTCOMES = {0: "accepted", 1: "refused", 3: "uncertain", 4: "fault", 5: "usage"}


def summary(values):
    if not values:
        return None
    ordered = sorted(values)
    return {"runs": len(values), "min_seconds": ordered[0],
            "median_seconds": statistics.median(ordered),
            "p90_seconds": ordered[min(len(ordered) - 1, int(0.9 * len(ordered)))],
            "max_seconds": ordered[-1], "total_seconds": sum(ordered)}




def host_facts():
    facts = {"hostname": socket.gethostname(), "platform": platform.platform(),
             "machine": platform.machine(), "cpu_count": os.cpu_count(),
             "kernel": platform.release()}
    try:
        for line in Path("/proc/cpuinfo").read_text(errors="replace").splitlines():
            if line.startswith("model name"):
                facts["cpu_model"] = line.split(":", 1)[1].strip()
                break
        for line in Path("/proc/meminfo").read_text(errors="replace").splitlines():
            if line.startswith("MemTotal:"):
                facts["memory_kib"] = int(line.split()[1])
                break
    except OSError:
        pass
    return facts

def file_sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()

def tree_rss_kib(pid):
    """Resident KiB of the owner and children, Linux only."""
    pending, seen, total = [pid], set(), 0
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        try:
            status = Path("/proc/{}/status".format(current)).read_text()
            for line in status.splitlines():
                if line.startswith("VmRSS:"):
                    total += int(line.split()[1])
                    break
            children = Path("/proc/{}/task/{}/children".format(current, current))
            pending.extend(int(one) for one in children.read_text().split() if one.isdigit())
        except OSError:
            continue
    return total or None


def command(argv, *, cwd, environment, timeout=1800):
    before = time.monotonic()
    try:
        done = subprocess.run(argv, cwd=cwd, env=environment, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=timeout, check=False)
        return {"argv": argv, "seconds": time.monotonic() - before,
                "returncode": done.returncode,
                "children_maxrss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                "stdout": done.stdout[-1000:], "stderr": done.stderr[-1000:]}
    except subprocess.TimeoutExpired as error:
        return {"argv": argv, "seconds": time.monotonic() - before,
                "returncode": 124, "stdout": (error.stdout or "")[-1000:],
                "stderr": (error.stderr or "")[-1000:], "timeout": True}


def wait_listening(process, log, seconds=120):
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        text = log.read_text(errors="replace") if log.exists() else ""
        for line in text.splitlines():
            if line.startswith("LISTENING "):
                try:
                    return int(line.split()[1]), text
                except (IndexError, ValueError):
                    return None, text
        if process.poll() is not None:
            return None, text
        time.sleep(0.1)
    return None, log.read_text(errors="replace") if log.exists() else ""


def stop(process, control):
    try:
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
            sock.settimeout(10)
            sock.connect(str(control))
            sock.sendall(b"QUIT\n")
            sock.recv(256)
    except OSError:
        pass
    try:
        process.wait(timeout=20)
    except subprocess.TimeoutExpired:
        process.send_signal(signal.SIGTERM)
        try:
            process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait(timeout=10)


def write_source(directory, seed, index, size, folded=False):
    msgid = message_id(seed, index)
    source = article_octets(seed, index, size, msgid, GROUPS,
                            "folded" if folded else "random")
    path = directory / "article-{:05d}.eml".format(index)
    path.write_bytes(source)
    return msgid.decode("ascii"), path, {
        "bytes": len(source), "sha256": hashlib.sha256(source).hexdigest(),
        "ends_crlf": source.endswith(b"\r\n"),
        "bare_lf": b"\n" in source.replace(b"\r\n", b""),
        "folded": folded,
    }


def current_owner(work, counts, payload, folded_bytes, seed, acl2):
    """One owner and one growing dev-profile store, through CLI→control POST."""
    result = {"path": "bin/fn post -> live bin/fn run control socket",
              "scope": "development oracle only; the Python bridge is not a production endpoint",
              "profile": "development", "counts_requested": counts,
              "payload_bytes": payload, "groups": list(GROUPS), "points": [],
              "quota": None, "folded_stress": None, "stopped_by": None}
    node, store, sources = work / "owner", work / "owner-store", work / "sources"
    node.mkdir(parents=True, exist_ok=True)
    sources.mkdir(parents=True, exist_ok=True)
    config, control, log = node / "fn.toml", node / "control.sock", node / "owner.log"
    env = dict(os.environ)
    if acl2:
        env["FN_ACL2"] = acl2
    init = command([sys.executable, "bin/fn", "--config", str(config), "init",
                    "--store", str(store), "--group", GROUPS[0], "--group", GROUPS[1],
                    "--listen", "127.0.0.1:0", "--control", str(control),
                    "--log", str(log), *( ["--acl2", acl2] if acl2 else [])],
                   cwd=ROOT, environment=env)
    result["init"] = init
    if init["returncode"] != 0:
        result["stopped_by"] = "init returned {}".format(init["returncode"])
        return result
    owner_argv = [sys.executable, "bin/fn", "--config", str(config), "run",
                  "--control", str(control), "--max-connections", "32"]
    before_owner = time.monotonic()
    with log.open("w") as output:
        owner = subprocess.Popen(owner_argv, cwd=ROOT, env=env, stdout=output,
                                 stderr=subprocess.STDOUT, text=True)
    port, listening = wait_listening(owner, log)
    result["owner"] = {"argv": owner_argv, "pid": owner.pid, "listen_port": port,
                       "environment": {"FN_ACL2": env.get("FN_ACL2", "default")},
                       "log_before_posts": listening[-1000:]}
    if port is None:
        result["stopped_by"] = "owner did not reach LISTENING"
        stop(owner, control)
        return result
    committed = 0
    quota_taken = False
    folded_at = MAX_TRANSACTION_COUNT - 1 if folded_bytes > 0 else None
    result["owner"]["startup_seconds"] = time.monotonic() - before_owner
    try:
        for target in counts:
            if target > MAX_TRANSACTION_COUNT:
                result["points"].append({
                    "target_articles": target, "at_open": committed,
                    "not_measured": "development profile max_transactions={}".format(
                        MAX_TRANSACTION_COUNT),
                })
                result["stopped_by"] = "development profile transaction bound at {} accepted articles".format(
                    MAX_TRANSACTION_COUNT)
                break
            point, latencies = {"target_articles": target, "at_open": committed,
                                "loadavg": os.getloadavg()}, []
            while committed < target:
                folded = committed == folded_at
                size = folded_bytes if folded else payload
                msgid, source, shape = write_source(sources, seed, committed, size, folded)
                invocation = [sys.executable, "bin/fn", "--config", str(config), "post",
                              "--message-id", msgid, "--payload", str(source),
                              "--group", GROUPS[0], "--group", GROUPS[1],
                              "--control", str(control)]
                one = command(invocation, cwd=ROOT, environment=env)
                one["outcome"] = OUTCOMES.get(one["returncode"], "fault")
                one["source"] = shape
                one["control_path_reported"] = "path=control" in (one["stdout"] + one["stderr"])
                if one["outcome"] != "accepted" or not one["control_path_reported"]:
                    point["stopped_post"] = one
                    result["stopped_by"] = "post {} {}".format(committed, one["outcome"])
                    break
                if folded:
                    result["folded_stress"] = one
                else:
                    latencies.append(one["seconds"])
                committed += 1
            point["committed_after"] = committed
            point["control_post_seconds"] = summary(latencies)
            point["owner_tree_rss_kib"] = tree_rss_kib(owner.pid)
            result["points"].append(point)
            if result["stopped_by"]:
                break
            if committed == MAX_TRANSACTION_COUNT:
                # A single fresh ID past the configured capacity is a refusal
                # observation.  Its latency never enters a throughput summary.
                msgid, source, shape = write_source(sources, seed, committed, payload)
                quota = command([sys.executable, "bin/fn", "--config", str(config), "post",
                                 "--message-id", msgid, "--payload", str(source),
                                 "--group", GROUPS[0], "--group", GROUPS[1],
                                 "--control", str(control)], cwd=ROOT, environment=env)
                quota["outcome"] = OUTCOMES.get(quota["returncode"], "fault")
                quota["source"] = shape
                quota["control_path_reported"] = "path=control" in (quota["stdout"] + quota["stderr"])
                result["quota"] = quota
                quota_taken = True
                if quota["outcome"] != "refused":
                    result["stopped_by"] = "configured quota post returned {}".format(quota["outcome"])
                    break
        if not result["stopped_by"] and not quota_taken:
            result["stopped_by"] = "completed requested targets within development transaction bound"
    finally:
        result["owner_log"] = log.read_text(errors="replace")[-4000:] if log.exists() else ""
        stop(owner, control)
    recover = command([sys.executable, "bin/fn", "--config", str(config), "recover"],
                      cwd=ROOT, environment=env)
    recover["path"] = "operator recovery after owner shutdown"
    result["recover"] = recover
    return result


def native_direct(work, payload, seed, native_image, native_source_revision, native_image_digest):
    """Developer-image store/reader diagnostics, explicitly not owner POST."""
    result = {"path": "developer native image --fn store/reader diagnostics; no Python child in command tree and no served owner/control claim",
              "image": native_image, "source_revision": native_source_revision or "unspecified",
              "image_sha256": native_image_digest or (file_sha256(native_image) if native_image and Path(native_image).is_file() else "unavailable")}
    if not native_image or not Path(native_image).is_file():
        result["not_measured"] = "no executable --native-image was supplied"
        return result
    root, source = work / "native-store", work / "native.eml"
    image = str(Path(native_image).resolve())
    env = dict(os.environ)
    env.pop("FN_HOST", None)
    env.pop("FN_NATIVE_HOST", None)
    init = command([image, "--fn", "store", str(root), "init", *GROUPS],
                   cwd=ROOT, environment=env)
    result["store_init"] = init
    if init["returncode"] != 0:
        return result
    msgid, source, shape = write_source(work, seed, 900001, payload)
    post = command([image, "--fn", "store", str(root), "post", msgid, str(source),
                    "-", "-", *GROUPS], cwd=ROOT, environment=env)
    post["source"] = shape
    result["store_post"] = post
    result["store_recover"] = command([image, "--fn", "store", str(root), "recover"],
                                        cwd=ROOT, environment=env)
    log = work / "native-reader.log"
    before_reader = time.monotonic()
    reader_argv = [image, "--fn", "reader", "0", "1", str(root)]
    with log.open("w") as output:
        reader = subprocess.Popen(reader_argv, cwd=ROOT, env=env, stdout=output,
                                  stderr=subprocess.STDOUT, text=True)
    port, _ = wait_listening(reader, log)
    reader_result = {"argv": reader_argv, "environment": {"python_child": False},
                     "startup_seconds": time.monotonic() - before_reader, "port": port}
    if port is not None:
        before = time.monotonic()
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=20) as sock:
                reader_result["greeting"] = sock.recv(512).decode("ascii", "replace")
        except OSError as error:
            reader_result["error"] = "{}: {}".format(type(error).__name__, error)
        reader_result["first_connection_seconds"] = time.monotonic() - before
    stop(reader, work / "no-control.sock")
    reader_result["returncode"] = reader.returncode
    reader_result["log"] = log.read_text(errors="replace")[-1000:] if log.exists() else ""
    result["reader"] = reader_result
    return result



def revision():
    done = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, check=False)
    return done.stdout.strip() if done.returncode == 0 else "unknown"


def report_text(result):
    owner = result["owner_control"]
    lines = ["# Current-path performance measurement", "",
             "- Owner source: `{}`".format(result["owner_source_revision"]),
             "- Harness revision: `{}`; harness SHA-256 `{}`.".format(result["harness_revision"], result["harness_sha256"]),
             "- Host: `{}`; load at start `{}`.".format(result["host"]["platform"], result["loadavg_at_start"]),
             "- Owner scope: development-oracle evidence only: `bin/fn post` through the live `bin/fn run` control socket; each accepted post reports `path=control`. This Python bridge path is not a production endpoint.",
             "- Native scope: explicit developer-image `--fn store` / `--fn reader` diagnostics with no Python child; it does not measure the production operator/owner path.", "",
             "## Owner results", ""]
    if owner.get("not_measured"):
        lines.append("- Owner path: {}.".format(owner["not_measured"]))
    for point in owner.get("points", []):
        if "not_measured" in point:
            lines.append("- {} articles: {}.".format(point["target_articles"], point["not_measured"]))
            continue
        stat = point.get("control_post_seconds")
        if stat:
            lines.append("- {} accepted articles: {} timed posts, median {:.6f}s, worst {:.6f}s, owner-tree RSS {} KiB.".format(
                point["committed_after"], stat["runs"], stat["median_seconds"], stat["max_seconds"], point["owner_tree_rss_kib"]))
        else:
            lines.append("- {} articles: no ordinary latency samples.".format(point["target_articles"]))
    quota = owner.get("quota")
    if quota:
        lines.append("- Quota boundary: {} (exit {}).".format(quota["outcome"], quota["returncode"]))
    if owner.get("folded_stress"):
        lines.append("- Folded-header stress: {} in {:.6f}s, separate from ordinary samples.".format(
            owner["folded_stress"]["outcome"], owner["folded_stress"]["seconds"]))
    native = result["native_direct"]
    lines.extend(["", "## Recovery and native direct", "",
                  "- Owner recovery: {} (exit {}).".format(owner.get("recover", {}).get("outcome", OUTCOMES.get(owner.get("recover", {}).get("returncode"), "not-run")), owner.get("recover", {}).get("returncode", "not-run")),
                  "- Native direct: {}.".format(native.get("not_measured", "source {} image-sha256 {}".format(native.get("source_revision", "unspecified"), native.get("image_sha256", "unavailable"))))])
    if native.get("store_post"):
        lines.append("- Native direct init {:.6f}s, one accepted 1024-byte post {:.6f}s, recovery {:.6f}s; cumulative child peak RSS {} KiB.".format(
            native["store_init"]["seconds"], native["store_post"]["seconds"], native["store_recover"]["seconds"], native["store_recover"].get("children_maxrss_kib", "unavailable")))
    if native.get("reader"):
        lines.append("- Native reader startup {:.6f}s; first greeting {:.6f}s.".format(
            native["reader"].get("startup_seconds", 0), native["reader"].get("first_connection_seconds", 0)))
    lines.extend(["", "Commands and full per-invocation outcomes, source hashes, exact input sizes, RSS, tool versions, and logs are in the adjacent JSON artifact."])
    return "\n".join(lines) + "\n"

def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--work", required=True)
    parser.add_argument("--counts", default="16,128,512")
    parser.add_argument("--payload", type=int, default=1024)
    parser.add_argument("--folded-bytes", type=int, default=12000)
    parser.add_argument("--seed", type=int, default=13)
    parser.add_argument("--acl2", default=os.environ.get("FN_ACL2", ""))
    parser.add_argument("--native-image", default="",
                        help="explicit developer-profile image for raw store/reader diagnostics")
    parser.add_argument("--native-source-revision", default="")
    parser.add_argument("--native-image-digest", default="")
    parser.add_argument("--harness-revision", default="")
    parser.add_argument("--json", default=None)
    parser.add_argument("--report", default=None)
    parser.add_argument("--skip-owner", action="store_true")
    parser.add_argument("--owner-source-revision", default="")
    args = parser.parse_args(argv)
    counts = [int(one) for one in args.counts.split(",") if one]
    if not counts or counts != sorted(set(counts)) or counts[0] < 1:
        parser.error("--counts must be strictly increasing positive integers")
    work = Path(args.work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    result = {"tool": "tests/bench/current_path.py", "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
              "cwd": str(ROOT), "harness_revision": args.harness_revision or revision(),
              "harness_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "owner_source_revision": args.owner_source_revision or revision(),
              "counts_requested": counts, "python": sys.version,
              "host": host_facts(),
              "tool_versions": {"python": sys.version, "acl2_path": args.acl2 or "default"},
              "loadavg_at_start": os.getloadavg(),
              "owner_control": ({"not_measured": "skipped by --skip-owner; no owner/control claim"}
                                if args.skip_owner else current_owner(work, counts, args.payload,
                                                                       args.folded_bytes, args.seed, args.acl2)),
              "native_direct": native_direct(work, args.payload, args.seed, args.native_image,
                                               args.native_source_revision, args.native_image_digest)}
    result["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    text = json.dumps(result, sort_keys=True)
    if args.json:
        Path(args.json).write_text(text + "\n")
    if args.report:
        Path(args.report).write_text(report_text(result))
    print("CURRENT-PATH " + text)
    return 0 if args.skip_owner or result["owner_control"].get("recover", {}).get("returncode") == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
