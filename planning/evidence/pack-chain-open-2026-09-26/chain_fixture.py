"""Build the 20,000-record chain fixture once, and time opens over copies of it.

    python3 chain_fixture.py build WORK FIXTURE [N]
    python3 chain_fixture.py time FIXTURE SCRATCH [DEADLINE]

Run from the tree root (it imports tests.test_native_pack_chain and uses
FN_NATIVE_DEVELOPER_HOST or build/fn-host-developer).  `build` makes the
scale store in WORK (a tmpfs directory), takes the served BEFORE view and the
retention listing, runs `operator CONFIG store compact`, and copies the
compacted store into FIXTURE/store with before-view.json, retention.txt,
compact.txt, origin.json and SHA256SUMS.  `time` copies FIXTURE/store into
SCRATCH, times `store recover` (peak RSS from /usr/bin/time -v) and
`operator CONFIG run` to its LISTENING line (peak RSS from VmHWM at the
announcement), and prints one JSON line.  The fixture is never opened in
place: every open writes an open-time checkpoint.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import select
import shutil
import socket
import subprocess
import sys
import time

sys.path.insert(0, os.getcwd())
from tests.test_native_checkpoint import IMAGE, ROOT  # noqa: E402
from tests.test_native_pack_chain import NativePackChainTests, PROFILE_FLAGS  # noqa: E402

ENV = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
ENV.pop("ACL2_SYSTEM_BOOKS", None)


def native(*args):
    result = subprocess.run([str(IMAGE), "--fn", *map(str, args)], cwd=ROOT, env=ENV,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode != 0:
        raise SystemExit("native {} exited {}: {}".format(
            args, result.returncode, result.stderr.decode("utf-8", "replace")[-4000:]))
    return result.stdout.decode("utf-8", "replace"), result.stderr.decode("utf-8", "replace")


def write_config(base, store, name):
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        port = probe.getsockname()[1]
    config = base / (name + ".toml")
    config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
                      'port = {}\n[control]\npath = "{}"\n'.format(
                          store, port, base / (name + "-control.sock")), encoding="ascii")
    return config, port


def vm_hwm_kib(pid):
    for line in Path("/proc/{}/status".format(pid)).read_text().splitlines():
        if line.startswith("VmHWM:"):
            return int(line.split()[1])
    return None


def start_owner(config, deadline):
    """Start the owner; return (process, seconds to LISTENING, VmHWM KiB then)."""
    started = time.monotonic()
    process = subprocess.Popen([str(IMAGE), "--fn", "operator", str(config), "run"],
                               cwd=ROOT, env=ENV, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)
    buffered = b""
    while True:
        while b"\n" in buffered:
            line, buffered = buffered.split(b"\n", 1)
            if line.startswith(b"LISTENING "):
                return process, time.monotonic() - started, vm_hwm_kib(process.pid)
        remaining = started + deadline - time.monotonic()
        if remaining <= 0 or not select.select([process.stdout], [], [], remaining)[0]:
            process.kill()
            raise SystemExit("owner did not announce within {} s".format(deadline))
        chunk = os.read(process.stdout.fileno(), 4096)
        if not chunk:
            raise SystemExit("owner ended before LISTENING: {}".format(
                process.stderr.read()[-4000:]))
        buffered += chunk


def stop_owner(process):
    process.terminate()
    _, stderr = process.communicate(timeout=1800)
    if process.returncode != 0:
        raise SystemExit("owner stop exited {}: {}".format(process.returncode, stderr[-4000:]))


def encode_view(view):
    def enc(value):
        if isinstance(value, bytes):
            return base64.b64encode(value).decode("ascii")
        return [enc(v) for v in value]
    return {str(key): enc(value) for key, value in view.items()}


def sha256sums(root):
    lines = []
    for path in sorted(p for p in root.rglob("*") if p.is_file() and p.name != "SHA256SUMS"):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append("{}  {}\n".format(digest, path.relative_to(root)))
    (root / "SHA256SUMS").write_text("".join(lines), encoding="ascii")


def build(work, fixture, n):
    work.mkdir(parents=True)
    store = work / "scale-chain"
    config, port = write_config(work, store, "scale-chain")
    timings = {}
    t = time.monotonic()
    out, err = native("operator", config, "init", *PROFILE_FLAGS, "fn.letters", "fn.test")
    assert "accepted operator init" in err, err
    t = time.monotonic()
    native("store", store, "probe", str(n), "article")
    timings["probe_s"] = round(time.monotonic() - t, 1)
    sample = ["<capacity-{}@example.invalid>".format(k)
              for k in (0, 1, 4095, 4096, 4097, n // 2, n - 2, n - 1)]
    # served_view with this module's timed owner start.
    case = NativePackChainTests("test_scale_store_compacts_into_a_chain")
    case.base, case.env = work, ENV
    starts = []

    def run_owner(cfg):
        process, seconds, hwm = start_owner(cfg, 3600)
        starts.append({"listening_s": round(seconds, 1), "vmhwm_kib": hwm})
        return process
    case.run_owner = run_owner
    case.stop_owner = stop_owner
    t = time.monotonic()
    before = case.served_view(config, port, sample)
    timings["before_view_s"] = round(time.monotonic() - t, 1)
    timings["before_owner"] = starts[-1]
    retention, _ = native("store", store, "retention")
    t = time.monotonic()
    compacted, _ = native("operator", config, "store", "compact")
    timings["compact_s"] = round(time.monotonic() - t, 1)
    match = re.search(r"records=(\d+) generation=(\d+) links=(\d+)", compacted)
    assert match and int(match.group(1)) == n, compacted
    status, _ = native("store", store, "status")
    fixture.mkdir(parents=True)
    shutil.copytree(store, fixture / "store", symlinks=True)
    (fixture / "before-view.json").write_text(json.dumps(
        {"sample": sample, "view": encode_view(before)}), encoding="ascii")
    (fixture / "retention.txt").write_text(retention, encoding="utf-8")
    (fixture / "compact.txt").write_text(compacted, encoding="utf-8")
    (fixture / "status.txt").write_text(status, encoding="utf-8")
    image_sha = hashlib.sha256(Path(str(IMAGE) + ".core").read_bytes()).hexdigest() \
        if Path(str(IMAGE) + ".core").exists() else None
    origin = {"n": n, "profile_flags": list(PROFILE_FLAGS), "image": str(IMAGE),
              "image_core_sha256": image_sha, "source_rev": os.environ.get("FN_FIXTURE_REV"),
              "built_in": str(work), "timings": timings,
              "built_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (fixture / "origin.json").write_text(json.dumps(origin, indent=1), encoding="ascii")
    sha256sums(fixture)
    print(json.dumps(origin))


def time_open(fixture, scratch, deadline):
    scratch.mkdir(parents=True)
    store = scratch / "store"
    shutil.copytree(fixture / "store", store, symlinks=True)
    result = {"fixture": str(fixture)}
    t = time.monotonic()
    run = subprocess.run(["/usr/bin/time", "-v", str(IMAGE), "--fn", "store", str(store),
                          "recover"], cwd=ROOT, env=ENV, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    result["recover_s"] = round(time.monotonic() - t, 1)
    result["recover_exit"] = run.returncode
    result["recover_stdout"] = run.stdout.decode("utf-8", "replace")[-400:]
    peak = re.search(rb"Maximum resident set size \(kbytes\): (\d+)", run.stderr)
    result["recover_peak_kib"] = int(peak.group(1)) if peak else None
    config, _ = write_config(scratch, store, "time")
    process, seconds, hwm = start_owner(config, deadline)
    result["listening_s"] = round(seconds, 1)
    result["listening_vmhwm_kib"] = hwm
    t = time.monotonic()
    stop_owner(process)
    result["stop_s"] = round(time.monotonic() - t, 1)
    print(json.dumps(result))


if __name__ == "__main__":
    verb = sys.argv[1]
    if verb == "build":
        build(Path(sys.argv[2]), Path(sys.argv[3]),
              int(sys.argv[4]) if len(sys.argv) > 4 else 20000)
    elif verb == "time":
        time_open(Path(sys.argv[2]), Path(sys.argv[3]),
                  int(sys.argv[4]) if len(sys.argv) > 4 else 3600)
    else:
        raise SystemExit(__doc__)
