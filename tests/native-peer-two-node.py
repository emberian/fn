#!/usr/bin/env python3
"""Drive independent fn2 nodes over verified TLS.

The article-only control uses ordinary POST, ARTICLE and IHAVE. The catch-up
run requires an accepted counted READ and a served B-side peer-pull import.
"""
import argparse
import json
from contextlib import contextmanager, ExitStack
from pathlib import Path
import secrets
import stat
import subprocess
import tempfile

from test_fn2_starttls_surface import Peer
from test_fn2_user_surface import FN, LiveNode, ROOT, run_fn

from fn_admin import build_cns_request, decode_cns_reply, fnct_open

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


@contextmanager
def node(directory, control, identity, *, counted=False, pull_ca=None):
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
    )
    image = directory / "node.img"
    run_fn("init", str(image), "--size-mb", "8", "--group", GROUP, *origin)
    serve = [
        "--host", "127.0.0.1", "--port", "0", "--control-sock", str(control),
        "--tls-certificate", str(cert), "--tls-key", str(key), "--peering", *origin,
    ]
    if counted:
        serve.extend([
            "--max-consumer-request-octets", "512", "--max-consumer-discard-octets", "1024",
            "--consumer-body-timeout-ms", "5000",
        ])
    if pull_ca is not None:
        serve.extend(["--peer-pull-slots", "1", "--peer-pull-ca-file", str(pull_ca),
                      "--peer-pull-tls-name", "localhost"])
    running = LiveNode(directory, image, "peer", serve)
    try:
        port = int(running.wait_marker(b"LISTENING ").split()[1])
        assert running.wait_marker(b"LISTENING-LOCAL ") == f"LISTENING-LOCAL {control}".encode()
        assert stat.S_IMODE(control.stat().st_mode) == 0o600
        yield port, cert
    finally:
        running.close()


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
    assert target.command(b"IHAVE " + MID) == b"435 duplicate"
    assert target.command(b"BODY " + MID).startswith(b"222 ")
    assert [target.line(), target.line()] == [BODY, b"."]
    print("PASS ordinary ARTICLE body transit and same-ID retry on B", flush=True)


def catch_up(source, target, directory):
    assert target.command(b"ARTICLE " + MID).startswith(b"430 ")
    registered = source.xfnc("register", consumer=bytes([CONSUMER]), start="history", streams=[GROUP.encode("ascii")])
    if registered.get("outcome") != "accepted":
        raise BoundaryBlocked(f"A REGISTER returned {registered!r}")
    assert registered["position"] == 0, registered
    cursor = bytes.fromhex(registered["cursor"])
    (directory / "initial.fncu").write_bytes(cursor)
    query = build_cns_request("read", cursor=cursor, max_items=1, max_octets=1024)
    request = f"XFNC {len(query)}\r\n".encode("ascii") + query
    assert source.tls.write(request) == len(request)
    source.flush()
    line = source.line()
    code, separator, extent = line.partition(b" ")
    assert separator and extent.isdigit() and 0 < int(extent) <= 4096, line
    reply = source.take(int(extent))
    fnct_open(reply)
    (directory / "read-line").write_bytes(line + b"\r\n")
    (directory / "read.fnct").write_bytes(reply)
    if code != b"290":
        result = decode_cns_reply("read", reply)
        assert code == {"refused": b"490", "uncertain": b"491"}[result["outcome"]], result
        raise BoundaryBlocked(f"A counted READ returned {result!r}")
    raise BoundaryBlocked("B has no served peer-pull import handoff or settled receipt to compare after restart")


def activate_receiver(control, target, remote_port, sender_auth, view, directory):
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
    if result.returncode:
        raise BoundaryBlocked(f"B owner pull activation exited {result.returncode}")
    activation = json.loads(result.stdout)
    assert set(activation) == {"outcome", "reason", "attempt", "generation"}, activation
    assert activation["outcome"] == "accepted", activation
    assert 0 <= activation["attempt"] < 1 << 32 and 0 < activation["generation"] < 1 << 60, activation
    (directory / "pull-activation.json").write_text(json.dumps(activation, sort_keys=True) + "\n")
    print("PASS B owner pull activation", flush=True)


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("--directory", type=Path, required=True)
    modes = args.add_mutually_exclusive_group()
    modes.add_argument("--article-only", action="store_true", help="run the ordinary transit control")
    modes.add_argument("--activate-pull", action="store_true", help="check the owner's pull activation on B")
    args.add_argument("--expected-view", type=int, help="expected A view version for --activate-pull")
    options = args.parse_args()
    if options.activate_pull and options.expected_view is None:
        args.error("--activate-pull requires --expected-view")
    directory = options.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    try:
        with ExitStack() as cleanup:
            sockets = Path(cleanup.enter_context(tempfile.TemporaryDirectory(prefix="fn2-peer-", dir="/tmp")))
            a_socket, b_socket = sockets / "a.sock", sockets / "b.sock"
            a = cleanup.enter_context(node(directory / "a", a_socket, SENDER_ORIGIN,
                                           counted=not options.article_only))
            b = cleanup.enter_context(node(directory / "b", b_socket, 821,
                                           pull_ca=a[1] if options.activate_pull else None))
            assert a[0] != b[0], (a[0], b[0])
            a_poster = provision(a_socket, "local-poster", [("append", GROUP)])
            a_reader = provision(a_socket, "from-b", [
                ("peer", None), ("consume", None), ("peer-feed", GROUP), ("read", GROUP),
            ])
            b_target = provision(b_socket, "from-a", [
                ("peer", None), ("peer-accept", GROUP), ("append", GROUP), ("read", GROUP),
            ])
            with logged_in(*a, a_poster) as poster:
                post_one(poster)
            print("PASS durable NNTP POST on A", flush=True)
            with logged_in(*b, b_target, peer_role=True) as target:
                if options.activate_pull:
                    activate_receiver(b_socket, target, a[0], a_reader, options.expected_view, directory)
                else:
                    with logged_in(*a, a_reader, peer_role=True) as source:
                        if options.article_only:
                            article_transit(source, target, directory)
                        else:
                            catch_up(source, target, directory)
    except BoundaryBlocked as exc:
        raise SystemExit(f"BLOCKED {exc}") from exc


if __name__ == "__main__":
    main()
