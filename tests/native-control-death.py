#!/usr/bin/env python3
"""Selected-host accepted POST, SIGKILL, fresh restart and control trace replay.

Requires current qualified node-profile, merkle and native-control-replay.
Run inside a reserved, timed build job. No persisted-effect refinement claim:
replayed disk Read octets remain observations, never a declared durable prefix.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("boundaries", ROOT / "tests/native-image-boundaries.py")
boundary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)
restart = boundary.restart


def captured_env(path, target, device_effects=False):
    env = boundary.environment()
    env.pop("FN2_TEST_DEVICE_EFFECTS", None)
    if device_effects:
        env["FN2_TEST_DEVICE_EFFECTS"] = str(path.with_suffix(".effects"))
    env.update(FN2_TEST_CAPTURE=str(path), FN2_ENVELOPE_TRACE="262144")
    env["FN2_TEST_CAPTURE_TARGET"] = target.hex()
    return env


def image_observation(source, destination):
    """Copy only after our node is reaped; no fsync or storage-prefix inference."""
    with source.open("rb") as original, destination.open("xb") as snapshot:
        shutil.copyfileobj(original, snapshot, length=1024 * 1024)
    digest = hashlib.sha256()
    with destination.open("rb") as snapshot:
        for chunk in iter(lambda: snapshot.read(1024 * 1024), b""):
            digest.update(chunk)
    return dict(path=str(destination), bytes=destination.stat().st_size,
                sha256=digest.hexdigest(), scope="post-process-death visible image; persistence not established")


def await_recorded(node, received):
    recorded = bytearray()
    while len(recorded) < len(received):
        marker = node.marker(b"CAPTURE-SEND ")
        fields = marker.split(maxsplit=2)
        _, event = fields[:2]
        chunk = fields[2] if len(fields) == 3 else b""
        recorded.extend(bytes.fromhex(chunk.decode("ascii")))
    assert recorded == received, (len(recorded), len(received))
    cut = node.marker(b"CAPTURE-CUT ")
    assert cut.split() == [b"CAPTURE-CUT", event, b"post-recorded-before-post-boundary"], cut
    return int(event)


def replay(directory, name):
    selected = (ROOT / "tools/image-node.lsp").read_text()
    include = '(include-book "books/merkle" :uncertified-okp nil)'
    main = '(sb-ext:exit :code (fn2-nserve-main))'
    assert selected.count(include) == selected.count(main) == 1
    selected = selected.replace(include, include + '\n(include-book "tests/native-control-replay" :uncertified-okp nil)')
    selected = selected.replace(main, '(load "tests/native-control-replay-raw.lsp")\n(sb-ext:exit :code 0)')
    script = directory / f"{name}-replay.lsp"
    script.write_text(selected)
    env = dict(os.environ, FN2_TEST_CAPTURE=str(directory / f"{name}.trace"),
               FN2_TEST_PEER=str(directory / f"{name}.peer"))
    with script.open("rb") as source, (directory / f"{name}-replay.log").open("wb") as log:
        result = subprocess.run([str(ROOT / "tools/acl2"), "--timeout", "300"],
                                stdin=source, stdout=log, stderr=subprocess.STDOUT,
                                cwd=ROOT, env=env, timeout=330)
    assert result.returncode == 0, f"see {name}-replay.log"
    assert "NATIVE CONTROL REPLAY PASS" in (directory / f"{name}-replay.log").read_text()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--device-effects", action="store_true",
                        help="capture test-only raw device effects and pre/restart image observations")
    args = parser.parse_args()
    directory = args.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    image = directory / "node.img"
    # Explicit caller-provided origin configuration is inherited unchanged.
    subprocess.run([str(ROOT / "fn"), "init", str(image), "--size-mb", "32", "--group", "local.test"],
                   env=boundary.environment(), cwd=ROOT, check=True, timeout=600)
    control = Path(f"/tmp/fn2-control-death-{os.getpid()}-{time.time_ns()}.sock")
    seed = restart.Node(directory, image, "serve", "grant", control_sock=control,
                        env=boundary.environment())
    try:
        seed.marker(b"LISTENING-LOCAL ")
        subprocess.run([str(ROOT / "fn"), "grant", "set", "anonymous", "append", "local.test",
                        "--control-sock", str(control)], cwd=ROOT, check=True, timeout=60,
                       env=boundary.environment())
        seed.kill()
    finally:
        seed.close()
    observations = []
    if args.device_effects:
        observations.append(image_observation(image, directory / "before-accepted.img"))
        (directory / "image-observations.json").write_text(json.dumps(observations, indent=2) + "\n")
    mid = b"<control-death@example.invalid>"
    _, article = restart.article(mid, 100)
    receipts = []
    for name in ("accepted", "restarted"):
        target = b"200 fn-nntp experimental server ready\r\n"
        if name == "accepted":
            target += b"340 send article to be posted\r\n240 article received OK\r\n"
        else:
            target += b"211 1 1 1 local.test\r\n220 1 " + mid + b" article follows\r\n"
            target += restart.wire([b"Xref: fn2.invalid local.test:1"] + restart.stuffed(article) + [b"."])
        node = restart.Node(directory, image, "serve", name,
                            env=captured_env(directory / f"{name}.trace", target, args.device_effects),
                            launcher=[sys.executable, str(ROOT / "tests/native-control-launcher.py")])
        try:
            port = int(node.marker(b"LISTENING ").split()[1])
            sock = boundary.socket.create_connection(("127.0.0.1", port), timeout=30)
            peer_port = sock.getsockname()[1]
            stream = sock.makefile("rb")
            try:
                received = bytearray(stream.readline())
                assert received == b"200 fn-nntp experimental server ready\r\n"
                sent = bytearray()
                if name == "accepted":
                    sock.sendall(b"POST\r\n")
                    sent.extend(b"POST\r\n")
                    invitation = stream.readline()
                    assert invitation == b"340 send article to be posted\r\n"
                    received.extend(invitation)
                    body = restart.wire(restart.stuffed(article) + [b"."])
                    sock.sendall(body)
                    sent.extend(body)
                    accepted = stream.readline()
                    assert accepted == b"240 article received OK\r\n"
                    received.extend(accepted)
                else:
                    sock.sendall(b"GROUP local.test\r\n")
                    sent.extend(b"GROUP local.test\r\n")
                    group = stream.readline()
                    assert group == b"211 1 1 1 local.test\r\n"
                    received.extend(group)
                    sock.sendall(b"ARTICLE 1\r\n")
                    sent.extend(b"ARTICLE 1\r\n")
                    status = stream.readline()
                    assert status == b"220 1 " + mid + b" article follows\r\n"
                    body = restart.multiline(stream)
                    assert body == restart.wire([b"Xref: fn2.invalid local.test:1"] + restart.stuffed(article) + [b"."])
                    received.extend(status + body)
                event = await_recorded(node, received)
                (directory / f"{name}.wire").write_bytes(received)
                (directory / f"{name}.peer").write_text(
                    f"({peer_port} (" + " ".join(map(str, sent)) + ") (" +
                    " ".join(map(str, received)) + "))\n")
                # The separate evidence stream is flushed; no storage fence is
                # inserted by the fixture. Reap only our recorded runtime PID.
                node.kill()
                if args.device_effects:
                    observations.append(image_observation(image, directory / f"after-{name}-kill.img"))
                    (directory / "image-observations.json").write_text(json.dumps(observations, indent=2) + "\n")
                receipts.append(dict(phase=name, accepted_post=name == "accepted", capture_event=event,
                                     cut="SIGKILL after parent observed peer bytes and post-recorded pause",
                                     node_pid=node.node_pid, exit=node.proc.returncode))
            finally:
                stream.close()
                sock.close()
        finally:
            node.close()
        (directory / "processes.json").write_text(json.dumps(receipts, indent=2) + "\n")
        replay(directory, name)
    print("CONTROL DEATH PASS: accepted POST and fresh ARTICLE match independent control replays; persisted-effect mapping remains owed")


if __name__ == "__main__":
    main()
