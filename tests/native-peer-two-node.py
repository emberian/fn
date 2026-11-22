#!/usr/bin/env python3
"""Drive independent fn2 nodes over verified TLS.

The article-only control uses ordinary POST, ARTICLE and IHAVE. The pull
control drives B's actual actor and checks its durable position after restart.
"""
import argparse
import json
import os
from contextlib import contextmanager, ExitStack
from pathlib import Path
import secrets
import stat
import struct
import subprocess
import tempfile
import time
from typing import NamedTuple

from harness.launcher import require_launcher_sigkill
from test_fn2_starttls_surface import Peer
from test_fn2_user_surface import FN, LiveNode, ROOT, run_fn

from fn_admin import build_cns_request, cursor_consumer_and_position_width, decode_cns_reply, fnct_open, leb_decode

SENDER_ORIGIN = 811
CONSUMER = 7
GROUP = "local.test"
MID = b"<two-node-peer@example.invalid>"
BODY = b"two-node peer wire control"


class BoundaryBlocked(Exception):
    pass


def accepted(*args):
    result = run_fn(*args, as_json=True)
    assert result["outcome"] == "accepted", result
    return result


class RunningNode(NamedTuple):
    port: int
    cert: Path
    image: Path
    process: LiveNode
    serve: list[str]


@contextmanager
def listen(directory, image, control, serve, label, *, env=None):
    running = LiveNode(directory, image, label, serve, env=env)
    try:
        port = int(running.wait_marker(b"LISTENING ").split()[1])
        assert running.wait_marker(b"LISTENING-LOCAL ") == f"LISTENING-LOCAL {control}".encode()
        assert stat.S_IMODE(control.stat().st_mode) == 0o600
        yield port, running
    finally:
        running.close()


@contextmanager
def node(directory, control, identity, *, counted=False, pull_ca=None, cut_env=None):
    directory.mkdir()
    cert, key = directory / "cert.pem", directory / "key.pem"
    subprocess.run(
        ["openssl", "req", "-x509", "-newkey", "ec", "-pkeyopt", "ec_paramgen_curve:prime256v1",
         "-nodes", "-days", "1", "-subj", "/CN=localhost", "-addext", "subjectAltName=DNS:localhost",
         "-keyout", str(key), "-out", str(cert)],
        check=True, capture_output=True, timeout=15,
    )
    origin = (
        "--origin-lineage", str(identity),
        "--origin-domain", str(identity + 1),
        "--origin-incarnation", "1",
        "--history-id", str(identity + 2),
        "--history-incarnation", "1",
        "--history-revision", str(identity + 3),
    )
    image = directory / "node.img"
    fault_model = ("--storage-fault-model", "crash-only") if cut_env is not None else ()
    run_fn("init", str(image), "--size-mb", "8", "--group", GROUP, *origin, *fault_model)
    serve = [
        "--host", "127.0.0.1", "--port", "0", "--control-sock", str(control),
        "--tls-certificate", str(cert), "--tls-key", str(key), "--peering", *origin, *fault_model,
    ]
    if counted:
        serve.extend([
            "--max-consumer-request-octets", "512", "--max-consumer-discard-octets", "1024",
            "--consumer-body-timeout-ms", "5000",
        ])
    if pull_ca is not None:
        serve.extend(["--peer-pull-slots", "1", "--peer-pull-ca-file", str(pull_ca),
                      "--peer-pull-tls-name", "localhost"])
    with listen(directory, image, control, serve, "peer", env=cut_env) as (port, running):
        yield RunningNode(port, cert, image, running, serve)


def provision(control, principal, rights):
    transport = ("--control-sock", str(control))
    accepted("principal", "create", principal, *transport)
    password = secrets.token_hex(24).encode("ascii")
    result = subprocess.run(
        [FN, "principal", "set-password", principal, *transport],
        input=password + b"\n" + password + b"\n", cwd=ROOT, capture_output=True, timeout=90,
    )
    assert result.returncode == 0, ("set-password", result.returncode)
    for right, group in rights:
        accepted("grant", "set", principal, right, *([group] if group else []), *transport)
    return principal.encode("ascii"), password


@contextmanager
def logged_in(port, cert, auth, peer_role=False):
    peer = Peer(port)
    try:
        peer.sock.settimeout(30)
        peer.upgrade(cert, False)
        principal, password = auth
        assert peer.command(b"AUTHINFO USER " + principal).startswith(b"381 ")
        assert peer.command(b"AUTHINFO PASS " + password).startswith(b"281 ")
        if peer_role:
            assert peer.command(b"MODE STREAM").startswith(b"203 ")
        yield peer
    finally:
        peer.close()


def post_one(peer):
    assert peer.command(b"POST").startswith(b"340 ")
    article = [
        b"Path: source.invalid!not-for-mail", b"From: fixture@example.invalid",
        b"Date: Fri, 30 Oct 2026 12:00:00 +0000", b"Subject: Two-node wire control",
        b"Newsgroups: " + GROUP.encode("ascii"), b"Message-ID: " + MID, b"", BODY, b".",
    ]
    answer = peer.command(b"\r\n".join(article))
    assert answer.startswith(b"240 "), answer


def article_transit(source, target, directory):
    assert target.command(b"ARTICLE " + MID).startswith(b"430 ")
    assert target.command(b"BODY " + MID).startswith(b"430 ")
    assert target.command(b"CHECK " + MID) == b"238 " + MID
    assert source.command(b"ARTICLE " + MID).startswith(b"220 ")
    article = []
    while (line := source.line()) != b".":
        # The serving node's generated Xref is local numbering metadata.
        if not line.lower().startswith(b"xref:"):
            article.append(line)
    assert b"Message-ID: " + MID in article
    assert BODY in article
    transfer = b"\r\n".join(article + [b"."])
    (directory / "ordinary-article.nntp").write_bytes(transfer + b"\r\n")
    assert target.command(b"IHAVE " + MID).startswith(b"335 ")
    assert target.command(transfer).startswith(b"235 ")
    assert target.command(b"CHECK " + MID) == b"438 " + MID
    assert target.command(b"IHAVE " + MID) == b"435 duplicate"
    assert target.command(b"BODY " + MID).startswith(b"222 ")
    assert [target.line(), target.line()] == [BODY, b"."]
    print("PASS ordinary ARTICLE body transit and same-ID retry on B", flush=True)


def register_at_sender(source, directory):
    registered = source.xfnc("register", consumer=bytes([CONSUMER]), start="history",
                             streams=[GROUP.encode("ascii")])
    if registered.get("outcome") != "accepted":
        raise BoundaryBlocked(f"A REGISTER returned {registered!r}")
    assert registered["position"] == 0, registered
    cursor = bytes.fromhex(registered["cursor"])
    consumer, width = cursor_consumer_and_position_width(cursor)
    assert consumer == bytes([CONSUMER])
    indices = []
    off = 5
    for _ in range(2):
        size, off = leb_decode(cursor, off)
        indices.append(int.from_bytes(cursor[off:off + size], "big"))
        off += size
    assert indices == [SENDER_ORIGIN + 2, 1], indices
    view = int.from_bytes(cursor[-3 * width:-2 * width], "big")
    assert view > 0
    (directory / "initial.fncu").write_bytes(cursor)
    return cursor, view


# kind 28 holds the generated peer batch layout, including its digest tag.
PEER_BATCH_HEADER = struct.Struct(">BQQQB32sQQHQQBI")
PEER_BATCH_PAIR = struct.Struct(">QHH")


def read_sender_page(source, cursor, directory):
    query = build_cns_request("read", cursor=cursor, max_items=1, max_octets=1024)
    request = f"XFNC {len(query)}\r\n".encode("ascii") + query
    assert source.tls.write(request) == len(request)
    source.flush()
    line = source.line()
    code, separator, extent = line.partition(b" ")
    assert separator and extent.isdigit() and 0 < int(extent) <= 4096, line
    reply = source.take(int(extent))
    kind, payload = fnct_open(reply)
    (directory / "read-line").write_bytes(line + b"\r\n")
    (directory / "read.fnct").write_bytes(reply)
    if code != b"290":
        result = decode_cns_reply("read", reply)
        assert code == {"refused": b"490", "uncertain": b"491"}[result["outcome"]], result
        raise BoundaryBlocked(f"A counted READ returned {result!r}")
    assert kind == 28 and payload[:3] == bytes(3), "unexpected accepted peer READ envelope"
    count = int.from_bytes(payload[3:7], "big")
    result = payload[7:]
    assert count == len(result) and len(result) >= PEER_BATCH_HEADER.size + 2
    (version, history, incarnation, revision, algorithm, chain, view, view_version, interpretation,
     next_position, end, stop, pairs) = PEER_BATCH_HEADER.unpack_from(result)
    assert (version, algorithm, pairs) == (1, 1, 1)
    assert 0 < next_position <= end and stop in (0, 1, 2, 3)
    pos = PEER_BATCH_HEADER.size
    cursor_size = int.from_bytes(result[pos:pos + 2], "big")
    pos += 2 + cursor_size
    assert 0 < cursor_size <= 366 and pos + PEER_BATCH_PAIR.size <= len(result)
    item_position, history_size, evidence_size = PEER_BATCH_PAIR.unpack_from(result, pos)
    pos += PEER_BATCH_PAIR.size
    assert item_position == next_position and history_size > 0 and evidence_size > 0
    assert pos + history_size + evidence_size == len(result)
    assert MID in result[pos + history_size:]
    return dict(source_domain=history, source_incarnation=incarnation, source_revision=revision,
                source_view=view, source_view_version=view_version, interpretation=interpretation,
                position=next_position, chain=chain.hex())


def catch_up(source, target, directory):
    assert target.command(b"ARTICLE " + MID).startswith(b"430 ")
    cursor, _ = register_at_sender(source, directory)
    read_sender_page(source, cursor, directory)
    print("PASS A counted READ carried the posted article's evidence", flush=True)


def activate_receiver(control, target, remote_port, sender_auth, view, directory, *,
                      allow_interrupted=False, marker="pull-activation.json"):
    assert target.command(b"ARTICLE " + MID).startswith(b"430 ")
    username, secret = sender_auth
    result = subprocess.run(
        [FN, "peer", "pull", "--control-sock", str(control), "--json",
         "--local-principal", "from-a", "--local-group", GROUP, "--consumer", str(CONSUMER),
         "--expected-history", str(SENDER_ORIGIN + 2), "--expected-incarnation", "1",
         "--expected-view", str(view), "--remote-stream", GROUP, "--remote-address", "127.0.0.1",
         "--remote-port", str(remote_port), "--timeout-ms", "30000", "--remote-user", username.decode("ascii")],
        input=secret + b"\n", cwd=ROOT, capture_output=True, timeout=90,
    )
    assert secret not in result.stdout + result.stderr
    if allow_interrupted and result.returncode == 3:
        activation = json.loads(result.stdout)
        assert activation["outcome"] == "uncertain"
        (directory / marker).write_text(json.dumps({"outcome": "uncertain"}) + "\n")
        return None
    if result.returncode:
        raise BoundaryBlocked(f"B owner pull activation exited {result.returncode}")
    activation = json.loads(result.stdout)
    assert set(activation) == {"outcome", "reason", "attempt", "generation"}, activation
    assert activation["outcome"] == "accepted", activation
    assert 0 <= activation["attempt"] < 1 << 32 and 0 < activation["generation"] < 1 << 60, activation
    (directory / marker).write_text(json.dumps(activation, sort_keys=True) + "\n")
    print("PASS B owner pull activation", flush=True)
    return activation


def peer_position(control, timeout=10):
    return run_fn("peer", "position", "--control-sock", str(control), "--local-principal", "from-a",
                  "--consumer", str(CONSUMER), as_json=True, timeout=timeout)


def wait_for_progress(control):
    deadline = time.monotonic() + 40
    while (remaining := deadline - time.monotonic()) > 0:
        state = peer_position(control, timeout=min(10, remaining))
        assert state["outcome"] == "accepted", state
        if state["found"] and state["position"] > 0:
            return state
        time.sleep(min(0.25, max(0, deadline - time.monotonic())))
    raise BoundaryBlocked("B accepted the pull but exposed no positive durable position within 40 seconds")


def pull_and_reopen(directory, a, b, a_socket, b_socket, a_auth, b_auth):
    with logged_in(a.port, a.cert, a_auth, peer_role=True) as source:
        cursor, view = register_at_sender(source, directory)
        sender_page = read_sender_page(source, cursor, directory)
    before = peer_position(b_socket)
    assert before == {"outcome": "accepted", "reason": "none", "found": False}, before
    with logged_in(b.port, b.cert, b_auth, peer_role=True) as target:
        activate_receiver(b_socket, target, a.port, a_auth, view, directory)
    position = wait_for_progress(b_socket)
    a_scope = accepted("grant", "get", "from-b", "peer-feed", GROUP,
                       "--control-sock", str(a_socket))
    b_scope = accepted("grant", "get", "from-a", "peer-accept", GROUP,
                       "--control-sock", str(b_socket))
    assert position["target_stream"] == b_scope["target"], position
    assert position["source_domain"] == SENDER_ORIGIN + 2 and position["source_incarnation"] == 1, position
    assert position["source_view"] == a_scope["target"] and position["source_view_version"] == view, position
    assert position["source_revision"] == SENDER_ORIGIN + 3 and any(bytes.fromhex(position["chain"])), position
    assert {field: position[field] for field in sender_page} == sender_page, position
    (directory / "durable-position.json").write_text(json.dumps(position, sort_keys=True) + "\n")
    b.process.sigkill()
    with listen(b.image.parent, b.image, b_socket, b.serve, "after-import") as (port, _):
        assert peer_position(b_socket) == position, "B recovered a different peer checkpoint"
        print("PASS B durable peer position after process death", flush=True)
        with logged_in(a.port, a.cert, a_auth, peer_role=True) as source:
            with logged_in(port, b.cert, b_auth, peer_role=True) as target:
                article_transit(source, target, directory)
        assert peer_position(b_socket) == position, "ordinary transit changed the peer checkpoint"


def observer_environment(mode):
    real = Path(os.environ["FN_ACL2"]).resolve(strict=True)
    observer = ROOT / "tests/native-peer-cut-launcher.py"
    if real.resolve() == observer.resolve() or not os.access(real, os.X_OK):
        raise ValueError("FN_ACL2 must select a qualified real launcher")
    return dict(os.environ, FN_ACL2=str(observer), FN2_TEST_REAL_ACL2=str(real),
                FN2_TEST_PEER_CUT_MODE=mode)


def observe_cut(process, activation, expected):
    marker = process.wait_marker(b"PEER-POSITION-CUT ", seconds=40)
    keys = ("attempt", "generation", "baseline", "published", "consumer",
            "history", "incarnation", "view", "prior", "next")
    fields = marker.split()[1:]
    assert len(fields) == len(keys), marker
    cut = dict(zip(keys, map(int, fields)))
    if activation is not None:
        assert (cut["attempt"], cut["generation"]) == (activation["attempt"], activation["generation"]), cut
    assert cut["consumer"] == CONSUMER and cut["prior"] == 0, cut
    assert (cut["history"], cut["incarnation"], cut["view"], cut["next"]) == (
        expected["source_domain"], expected["source_incarnation"],
        expected["source_view_version"], expected["position"],
    ), cut
    return cut


def pull_with_death_cut(directory, a, b, b_socket, a_auth, b_auth, replay_env):
    with logged_in(a.port, a.cert, a_auth, peer_role=True) as source:
        cursor, view = register_at_sender(source, directory)
        sender_page = read_sender_page(source, cursor, directory)
    before = peer_position(b_socket)
    assert before == {"outcome": "accepted", "reason": "none", "found": False}, before
    with logged_in(b.port, b.cert, b_auth, peer_role=True) as target:
        activation = activate_receiver(b_socket, target, a.port, a_auth, view, directory,
                                       allow_interrupted=True, marker="cut-activation.json")
    cut = observe_cut(b.process, activation, sender_page)
    require_launcher_sigkill(b.process.proc)
    assert cut["published"] > cut["baseline"], cut
    (directory / "receipt-before-checkpoint-cut.json").write_text(json.dumps(cut, sort_keys=True) + "\n")

    with listen(b.image.parent, b.image, b_socket, b.serve, "receipt-cut-replay", env=replay_env) as (port, running):
        assert peer_position(b_socket) == before, "B recovered a checkpoint that had never been published"
        with logged_in(port, b.cert, b_auth, peer_role=True) as target:
            activation = activate_receiver(b_socket, target, a.port, a_auth, view, directory,
                                           marker="replay-activation.json")
        replay = observe_cut(running, activation, sender_page)
        assert replay["baseline"] == replay["published"] == cut["published"], (cut, replay)
        (directory / "receipt-retry-cut.json").write_text(json.dumps(replay, sort_keys=True) + "\n")

        position = wait_for_progress(b_socket)
        assert {field: position[field] for field in sender_page} == sender_page, position
        (directory / "replayed-position.json").write_text(json.dumps(position, sort_keys=True) + "\n")
        with logged_in(a.port, a.cert, a_auth, peer_role=True) as source:
            with logged_in(port, b.cert, b_auth, peer_role=True) as target:
                article_transit(source, target, directory)
        assert peer_position(b_socket) == position, "ordinary transit changed the peer checkpoint"
    print("PASS receipt-only process death, exact idempotent retry and checkpoint advance", flush=True)


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("--directory", type=Path, required=True)
    modes = args.add_mutually_exclusive_group()
    modes.add_argument("--article-only", action="store_true", help="run the ordinary transit control")
    modes.add_argument("--activate-pull", action="store_true", help="run B's actor and verify its durable position")
    modes.add_argument("--cut-before-checkpoint", action="store_true",
                       help="kill B after one item settles and before its checkpoint arm")
    options = args.parse_args()
    cut_env = observer_environment("kill") if options.cut_before_checkpoint else None
    replay_env = observer_environment("observe") if options.cut_before_checkpoint else None
    pull = options.activate_pull or options.cut_before_checkpoint
    directory = options.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    try:
        with ExitStack() as cleanup:
            sockets = Path(cleanup.enter_context(tempfile.TemporaryDirectory(prefix="fn2-peer-", dir="/tmp")))
            a_socket, b_socket = sockets / "a.sock", sockets / "b.sock"
            a = cleanup.enter_context(node(directory / "a", a_socket, SENDER_ORIGIN,
                                           counted=not options.article_only))
            b = cleanup.enter_context(node(directory / "b", b_socket, 821,
                                           pull_ca=a.cert if pull else None, cut_env=cut_env))
            assert a.port != b.port, (a.port, b.port)
            a_poster = provision(a_socket, "local-poster", [("append", GROUP)])
            a_reader = provision(a_socket, "from-b", [
                ("peer", None), ("consume", None), ("peer-feed", GROUP), ("read", GROUP),
            ])
            b_target = provision(b_socket, "from-a", [
                ("peer", None), ("peer-accept", GROUP), ("append", GROUP), ("read", GROUP),
            ])
            with logged_in(a.port, a.cert, a_poster) as poster:
                post_one(poster)
            print("PASS durable NNTP POST on A", flush=True)
            if options.cut_before_checkpoint:
                pull_with_death_cut(directory, a, b, b_socket, a_reader, b_target, replay_env)
            elif options.activate_pull:
                pull_and_reopen(directory, a, b, a_socket, b_socket, a_reader, b_target)
            else:
                with logged_in(b.port, b.cert, b_target, peer_role=True) as target:
                    with logged_in(a.port, a.cert, a_reader, peer_role=True) as source:
                        if options.article_only:
                            article_transit(source, target, directory)
                        else:
                            catch_up(source, target, directory)
    except BoundaryBlocked as exc:
        raise SystemExit(f"BLOCKED {exc}") from exc


if __name__ == "__main__":
    main()
