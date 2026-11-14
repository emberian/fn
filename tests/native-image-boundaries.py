#!/usr/bin/env python3
"""Injected native boundaries preserve accepted articles across image recovery.

Each case starts from the same accepted baseline image, interrupts a second
POST, and checks exact recovered public bytes. This is a bounded campaign;
the JSON report records its specific cuts and whether POST returned 240.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import socket
import subprocess
import time

SPEC = importlib.util.spec_from_file_location(
    "native_restart", Path(__file__).with_name("native-image-restart.py"))
restart = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(restart)
ROOT = restart.ROOT


def environment(cut=None):
    env = dict(os.environ)
    env.pop("FN2_KILL_AT", None)
    if cut is not None:
        env["FN2_KILL_AT"] = str(cut)
    return env


def post(sock, stream, whole):
    sock.sendall(b"POST\r\n")
    reply = stream.readline()
    if not reply:
        raise EOFError("process exited before POST invitation")
    assert reply == b"340 send article to be posted\r\n", reply
    sock.sendall(restart.wire(restart.stuffed(whole) + [b"."]))
    return stream.readline()


def connect_interrupted(port):
    sock = socket.create_connection(("127.0.0.1", port), timeout=30)
    stream = sock.makefile("rb")
    try:
        greeting = stream.readline()
        if not greeting:
            raise EOFError("process exited before greeting")
        assert greeting == b"200 fn-nntp experimental server ready\r\n", greeting
        return sock, stream
    except BaseException:
        stream.close()
        sock.close()
        raise


def verify(port, articles, acknowledged):
    sock, stream = restart.connect(port)
    try:
        sock.sendall(b"GROUP local.test\r\n")
        group = stream.readline()
        assert group in (b"211 1 1 1 local.test\r\n", b"211 2 1 2 local.test\r\n"), group
        transcript = bytearray(group)
        present = False
        for number, (mid, _, whole) in enumerate(articles, 1):
            sock.sendall(f"ARTICLE {number}\r\n".encode())
            status = stream.readline()
            transcript.extend(status)
            if number == 2 and status == b"423 no article with that number\r\n":
                assert not acknowledged, "acknowledged candidate lost after recovery"
                assert group == b"211 1 1 1 local.test\r\n"
                continue
            expected_status = b"220 " + str(number).encode() + b" " + mid + b" article follows\r\n"
            assert status == expected_status, (number, status)
            actual = restart.multiline(stream)
            expected = restart.wire(
                [f"Xref: fn2.invalid local.test:{number}".encode()]
                + restart.stuffed(whole) + [b"."])
            assert actual == expected, (number, len(actual), len(expected))
            transcript.extend(actual)
            if number == 2:
                present = True
                assert group == b"211 2 1 2 local.test\r\n"
        return present, bytes(transcript)
    finally:
        stream.close()
        sock.close()


def ready_boundary(directory, baseline, articles):
    """Observe the recovery prefix once; this calibration is not a death case."""
    image = directory / "calibration.img"
    shutil.copyfile(baseline, image)
    node = restart.Node(directory, image, "serve", "calibration",
                        env=environment((1 << 60) - 1))
    try:
        ready = int(node.marker(b"BOUNDARY-READY ").split()[1])
        port = int(node.marker(b"LISTENING ").split()[1])
        present, transcript = verify(port, articles, False)
        assert not present, "baseline already contains the candidate"
        (directory / "calibration.wire").write_bytes(transcript)
        node.kill()
        (directory / "calibration.json").write_text(
            json.dumps(dict(ready_boundary=ready, source_image=str(baseline))) + "\n")
        print(f"CALIBRATED ready boundary {ready}", flush=True)
        return ready
    finally:
        node.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path)
    selected = parser.add_mutually_exclusive_group(required=True)
    selected.add_argument("--cuts", help="comma-separated positive boundary indexes")
    selected.add_argument("--relative-cuts",
                          help="positive offsets from an observed ready boundary")
    parser.add_argument("--baseline", type=Path,
                        help="reuse a prior campaign's accepted baseline image")
    args = parser.parse_args()
    cuts = [int(value) for value in (args.cuts or args.relative_cuts).split(",")]
    assert cuts and all(cut > 0 for cut in cuts) and len(set(cuts)) == len(cuts)
    directory = (args.directory or ROOT / "build" / f"image-boundaries-{time.time_ns()}").resolve()
    directory.mkdir(parents=True, exist_ok=False)
    baseline = directory / "baseline.img"
    articles = []
    for mid, length in ((b"<prior@example.invalid>", 100),
                        (b"<candidate@example.invalid>", 250)):
        head, whole = restart.article(mid, length)
        articles.append((mid, head, whole))
    if args.baseline:
        shutil.copyfile(args.baseline.resolve(), baseline)
    else:
        node = restart.Node(directory, baseline, "init", "init", env=environment())
        try:
            node.marker(b"INITIALIZED")
            assert node.proc.wait(timeout=30) == 0
        finally:
            node.close()
        ctl = Path(f"/tmp/fn2-boundaries-{os.getpid()}.sock")
        node = restart.Node(directory, baseline, "serve", "baseline", control_sock=ctl,
                            env=environment())
        try:
            port = int(node.marker(b"LISTENING ").split()[1])
            node.marker(b"LISTENING-LOCAL ")
            subprocess.run([str(ROOT / "fn"), "grant", "set", "anonymous", "append",
                            "local.test", "--control-sock", str(ctl)],
                           cwd=ROOT, check=True, timeout=60, env=environment())
            sock, stream = restart.connect(port)
            try:
                assert post(sock, stream, articles[0][2]) == b"240 article received OK\r\n"
                node.kill()
            finally:
                stream.close()
                sock.close()
        finally:
            node.close()
            for path in (ctl, Path(f"{ctl}.groups")):
                if path.exists():
                    path.unlink()
    if args.relative_cuts:
        ready = ready_boundary(directory, baseline, articles)
        cuts = [ready + offset for offset in cuts]
    results = []
    for cut in cuts:
        image = directory / f"cut-{cut}.img"
        shutil.copyfile(baseline, image)
        node = restart.Node(directory, image, "serve", f"cut-{cut}", env=environment(cut))
        acknowledged = False
        phase = "startup"
        try:
            try:
                try:
                    port = int(node.marker(b"LISTENING ").split()[1])
                except AssertionError as error:
                    if str(error).startswith("no b'LISTENING '"):
                        raise EOFError(str(error)) from error
                    raise
                phase = "connect"
                sock, stream = connect_interrupted(port)
                try:
                    phase = "candidate-post"
                    reply = post(sock, stream, articles[1][2])
                    if reply:
                        assert reply == b"240 article received OK\r\n", reply
                        acknowledged = True
                        phase = "after-240"
                        # Keep the connection active so a configured later cut is
                        # reached; these requests cannot alter article contents.
                        for _ in range(cut):
                            sock.sendall(b"DATE\r\n")
                            if not stream.readline():
                                break
                finally:
                    stream.close()
                    sock.close()
            except (OSError, EOFError) as error:
                # A transport interruption is expected only with the exact
                # injected exit below. Retain diagnostics even in that case.
                diagnostic = str(error)
            else:
                diagnostic = ""
            assert node.proc.wait(timeout=30) == 86, "configured cut was not the process exit"
        finally:
            node.close()
        log = (directory / f"cut-{cut}.log").read_text(errors="replace")
        matches = re.findall(r"FN2 KILL boundary=(\d+) label=([^\s]+)", log)
        assert len(matches) == 1 and int(matches[0][0]) == cut, matches
        node = restart.Node(directory, image, "serve", f"recover-{cut}", env=environment())
        try:
            port = int(node.marker(b"LISTENING ").split()[1])
            present, transcript = verify(port, articles, acknowledged)
            (directory / f"recover-{cut}.wire").write_bytes(transcript)
            node.kill()
        finally:
            node.close()
        results.append(dict(cut=cut, label=matches[0][1], phase=phase,
                            acknowledged=acknowledged, candidate_recovered=present,
                            diagnostic=diagnostic))
        (directory / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results[-1]), flush=True)
    assert any(row["phase"] == "candidate-post" and not row["acknowledged"]
               for row in results), "chosen cuts did not interrupt a candidate POST; inspect results and extend the campaign"
    print(f"NATIVE IMAGE BOUNDARIES PASS: {len(results)} cuts; {directory}")


if __name__ == "__main__":
    main()
