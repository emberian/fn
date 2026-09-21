#!/usr/bin/env python3
"""Bounded benchmark of the production native shared-owner post/read path."""
import argparse, hashlib, json, os, platform, select, signal, socket
import statistics, subprocess, tempfile, time
from pathlib import Path


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def percentile(xs, fraction):
    ys = sorted(xs)
    return ys[max(0, min(len(ys) - 1, int((len(ys) * fraction + .999999)) - 1))]


def stats(xs):
    return {"samples": len(xs), "p50_seconds": statistics.median(xs),
            "p95_seconds": percentile(xs, .95), "max_seconds": max(xs)}


def rss_kib(pid):
    for line in Path("/proc/{}/status".format(pid)).read_text().splitlines():
        if line.startswith("VmRSS:"):
            return int(line.split()[1])
    return None


def article(index, body_bytes):
    mid = "<native-shared-{:04d}@example.invalid>".format(index)
    head = ("From: bench@example.invalid\r\nNewsgroups: fn.test\r\n"
            "Subject: native shared owner {:04d}\r\n"
            "Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n"
            "Message-ID: {}\r\n\r\n".format(index, mid)).encode("ascii")
    return mid, head + (b"x" * body_bytes) + b"\r\n"


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    env.pop("FN_NATIVE_HOST", None)
    return env


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def command(argv, cwd, timeout=180):
    start = time.monotonic_ns()
    done = subprocess.run(argv, cwd=cwd, env=environment(), stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=timeout, check=False)
    return done, (time.monotonic_ns() - start) / 1e9


def start_owner(image, config, cwd):
    started = time.monotonic_ns()
    proc = subprocess.Popen([image, "--fn", "operator", str(config), "run"], cwd=cwd,
                            env=environment(), stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, bufsize=0)
    observed = b""
    deadline = time.monotonic() + 180
    port = None
    while time.monotonic() < deadline and len(observed) < 8192:
        if not select.select([proc.stdout], [], [], deadline - time.monotonic())[0]:
            break
        chunk = os.read(proc.stdout.fileno(), 4096)
        if not chunk:
            break
        observed += chunk
        for line in observed.splitlines():
            if line.startswith(b"LISTENING "):
                port = int(line.split()[1])
                return proc, port, (time.monotonic_ns() - started) / 1e9, observed.decode("ascii", "replace")
    proc.terminate()
    _, error = proc.communicate(timeout=10)
    raise RuntimeError("owner startup failed: {!r} {}".format(observed, error.decode("utf-8", "replace")))


def stop_owner(proc):
    proc.send_signal(signal.SIGTERM)
    try:
        _, error = proc.communicate(timeout=30)
    except subprocess.TimeoutExpired:
        proc.kill(); _, error = proc.communicate(timeout=10)
    if proc.returncode != 0:
        raise RuntimeError("owner stop {}: {}".format(proc.returncode, error.decode("utf-8", "replace")[-2000:]))


def recv_line(stream):
    line = stream.readline(4096)
    if not line:
        raise RuntimeError("NNTP connection ended")
    return line


def read_article(port, message_id):
    started = time.monotonic_ns()
    with socket.create_connection(("127.0.0.1", port), timeout=30) as sock:
        stream = sock.makefile("rb")
        greeting = recv_line(stream)
        sock.sendall(("ARTICLE {}\r\n".format(message_id)).encode("ascii"))
        status = recv_line(stream)
        received = 0
        if status.startswith(b"220 "):
            while True:
                line = recv_line(stream)
                if line == b".\r\n": break
                received += len(line)
        sock.sendall(b"QUIT\r\n")
    return ((time.monotonic_ns() - started) / 1e9, greeting.decode("ascii", "replace").strip(),
            status.decode("ascii", "replace").strip(), received)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--image", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--json", required=True)
    ap.add_argument("--counts", default="1,16,64,128")
    ap.add_argument("--body-bytes", type=int, default=1024)
    ap.add_argument("--reads", type=int, default=20)
    ap.add_argument("--source-revision", required=True)
    args = ap.parse_args()
    counts = [int(x) for x in args.counts.split(",")]
    if counts != sorted(set(counts)) or not counts or counts[-1] > 128 or counts[0] < 1:
        ap.error("counts must be unique increasing integers in 1..128")
    if not (1 <= args.reads <= 100) or not (0 <= args.body_bytes <= 65536):
        ap.error("bounded reads/body profile exceeded")
    image, work = str(Path(args.image).resolve()), Path(args.work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    store, control, config, sources = work/"store", work/"control.sock", work/"fn.toml", work/"sources"
    sources.mkdir()
    init, init_seconds = command([image, "--fn", "store", str(store), "init", "fn.test"], work)
    if init.returncode: raise RuntimeError(init.stderr.decode("utf-8", "replace"))
    config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n[control]\npath = "{}"\n'.format(store, free_port(), control))
    owner, port, startup, announcement = start_owner(image, config, work)
    points, post_samples, shapes = [], [], []
    try:
        for index in range(1, counts[-1] + 1):
            mid, payload = article(index, args.body_bytes)
            source = sources/"{:04d}.eml".format(index); source.write_bytes(payload)
            done, elapsed = command([image, "--fn", "operator", str(config), "post", "--message-id", mid,
                                     "--payload", str(source), "--group", "fn.test"], work)
            if done.returncode != 0 or b"accepted operator post" not in done.stderr + done.stdout:
                raise RuntimeError("post {} failed {} {!r} {!r}".format(index, done.returncode, done.stdout, done.stderr))
            post_samples.append(elapsed)
            shapes.append({"index": index, "message_id": mid, "bytes": len(payload),
                           "sha256": hashlib.sha256(payload).hexdigest()})
            if index in counts:
                ids = [shapes[(j * index) // args.reads]["message_id"] for j in range(args.reads)]
                reads, byte_counts = [], []
                for selected in ids:
                    elapsed, greeting, status, received = read_article(port, selected)
                    if not status.startswith("220 "): raise RuntimeError(status)
                    reads.append(elapsed); byte_counts.append(received)
                points.append({"articles": index, "posts_since_previous_point": len(post_samples),
                               "post_latency": stats(post_samples), "read_latency": stats(reads),
                               "read_response_bytes": {"min": min(byte_counts), "max": max(byte_counts)},
                               "owner_rss_kib": rss_kib(owner.pid)})
                post_samples = []
    finally:
        stop_owner(owner)
    reopened, reopen_port, reopen_seconds, reopen_announcement = start_owner(image, config, work)
    try:
        reopen_read = read_article(reopen_port, shapes[-1]["message_id"])
        reopen_rss = rss_kib(reopened.pid)
    finally:
        stop_owner(reopened)
    result = {"schema": "fn-native-shared-owner-benchmark-v1", "source_revision": args.source_revision,
              "image": image, "image_sha256": sha256(image), "harness_sha256": sha256(__file__),
              "host": {"hostname": platform.node(), "platform": platform.platform(), "cpu_count": os.cpu_count()},
              "profile": {"counts": counts, "body_bytes": args.body_bytes, "reads_per_point": args.reads,
                          "article_count": len(shapes), "article_bytes": sorted(set(x["bytes"] for x in shapes)),
                          "total_source_bytes": sum(x["bytes"] for x in shapes)},
              "store_init_seconds": init_seconds, "first_startup_seconds": startup,
              "first_announcement": announcement.strip(), "points": points,
              "reopen": {"startup_seconds": reopen_seconds, "rss_kib": reopen_rss,
                         "announcement": reopen_announcement.strip(), "read_seconds": reopen_read[0],
                         "read_status": reopen_read[2], "read_response_bytes": reopen_read[3]},
              "articles": shapes, "finished_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    Path(args.json).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"image_sha256": result["image_sha256"], "points": points, "reopen": result["reopen"]}, sort_keys=True))


if __name__ == "__main__": main()
