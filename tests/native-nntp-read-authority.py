#!/usr/bin/env python3
"""Native STARTTLS and AUTHINFO control for group-granted NNTP reads.

Requires the qualified composed image with the shared group-read decision
and owner-local password provisioning. Uses an isolated image and fresh logins.
"""
import argparse
from contextlib import contextmanager
import importlib.util
import os
from pathlib import Path
import secrets
import subprocess
import time

from test_fn2_starttls_surface import Peer

SPEC = importlib.util.spec_from_file_location(
    "append_restart", Path(__file__).with_name("native-append-fetch-restart.py"))
fixture = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(fixture)

VISIBLE = b"local.ninth"
PRIMARY = b"local.test"
CROSSPOST = b"<read-crosspost@example.invalid>"
NINTH_ONLY = b"<read-ninth@example.invalid>"


def lines(peer, command, status):
    reply = peer.command(command)
    assert reply.startswith(status + b" "), (command, reply)
    result = []
    while (line := peer.line()) != b".":
        result.append(line)
    return result


def overview(peer, message_id, number):
    result = lines(peer, b"OVER " + message_id, b"224")
    assert len(result) == 1, result
    fields = result[0].split(b"\t")
    assert len(fields) >= 8 and (fields[0], fields[4]) == (number, message_id), result


@contextmanager
def login_attempt(port, cert, principal, password, expected=b"281"):
    peer = Peer(port)
    try:
        peer.sock.settimeout(30)
        peer.upgrade(cert, False)
        assert peer.command(b"AUTHINFO USER " + principal.encode("ascii")).startswith(b"381 ")
        answer = peer.command(b"AUTHINFO PASS " + password.encode("ascii"))
        assert answer.startswith(expected + b" "), ("AUTHINFO PASS", answer[:3])
        yield peer
    finally:
        peer.close()


def readable(peer):
    assert peer.command(b"GROUP " + PRIMARY).startswith(b"411 ")
    assert peer.command(b"LISTGROUP " + PRIMARY).startswith(b"411 ")
    assert [line.split()[0] for line in lines(peer, b"LIST ACTIVE", b"215")] == [VISIBLE]
    overview(peer, CROSSPOST, b"0")
    overview(peer, NINTH_ONLY, b"0")
    assert peer.command(b"STAT " + CROSSPOST) == b"223 0 " + CROSSPOST + b" retrieved"
    headers = lines(peer, b"HEAD " + NINTH_ONLY, b"221")
    assert b"Message-ID: " + NINTH_ONLY in headers, headers
    assert peer.command(b"GROUP " + VISIBLE) == b"211 2 1 2 " + VISIBLE
    overview(peer, CROSSPOST, b"1")
    overview(peer, NINTH_ONLY, b"2")
    assert lines(peer, b"LISTGROUP", b"211") == [b"1", b"2"]
    numbered = lines(peer, b"OVER 1-2", b"224")
    fields = [line.split(b"\t") for line in numbered]
    assert [(row[0], row[4]) for row in fields] == [(b"1", CROSSPOST), (b"2", NINTH_ONLY)], numbered
    assert peer.command(b"STAT") == b"223 1 " + CROSSPOST + b" retrieved"


def denied(peer):
    for name in (PRIMARY, VISIBLE):
        assert peer.command(b"GROUP " + name).startswith(b"411 ")
        assert peer.command(b"LISTGROUP " + name).startswith(b"411 ")
    assert lines(peer, b"LIST ACTIVE", b"215") == []
    for message_id in (CROSSPOST, NINTH_ONLY):
        for verb in (b"OVER ", b"STAT ", b"HEAD ", b"HDR Subject "):
            reply = peer.command(verb + message_id)
            assert reply == b"430 no article with that message-id", (verb, message_id, reply)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
    directory = parser.parse_args().directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    cert, key = directory / "cert.pem", directory / "key.pem"
    subprocess.run(["openssl", "req", "-x509", "-newkey", "ec", "-pkeyopt",
                    "ec_paramgen_curve:prime256v1", "-nodes", "-days", "1",
                    "-subj", "/CN=localhost", "-addext", "subjectAltName=DNS:localhost",
                    "-keyout", str(key), "-out", str(cert)],
                   check=True, capture_output=True, timeout=15)
    image = directory / "node.img"
    groups = [PRIMARY.decode("ascii"), *(f"local.pad{n}" for n in range(2, 9)), VISIBLE.decode("ascii")]
    fixture.initialize(directory, image, startup_args=tuple(
        option for group in groups for option in ("--group", group)))
    control = Path(f"/tmp/fn2-nntp-read-{os.getpid()}-{time.time_ns()}.sock")
    def start(label):
        return fixture.restart.Node(directory, image, "serve", label, control_sock=control,
                                    env=fixture.environment(), startup_args=(
                                        "--tls-certificate", str(cert), "--tls-key", str(key)))

    def admin(label, *args):
        reply = fixture.run_fn(directory, label, *args, "--control-sock", control)
        assert reply["outcome"] == "accepted", reply

    credentials = {}
    node = start("provision")
    try:
        node.marker(b"LISTENING ")
        node.marker(b"LISTENING-LOCAL ")
        admin("poster", "principal", "create", "fixture-poster")
        for group in (PRIMARY, VISIBLE):
            admin(f"append-{group.decode('ascii')}", "grant", "set", "fixture-poster",
                  "append", group.decode("ascii"))
        for index, (message_id, groups) in enumerate((
                (CROSSPOST, PRIMARY + b"," + VISIBLE), (NINTH_ONLY, VISIBLE)), 1):
            article = fixture.crossing_article(message_id.decode("ascii")).replace(
                b"Newsgroups: local.test\r\n", b"Newsgroups: " + groups + b"\r\n", 1)
            path = directory / f"article-{index}"
            path.write_bytes(article)
            reply = fixture.append_file(directory, f"append-{index}", control, "fixture-poster",
                                        100 + index, path)
            assert reply["outcome"] == "accepted" and reply["evidence"] == "committed", reply
        for principal in ("fixture-reader", "fixture-denied"):
            admin(principal, "principal", "create", principal)
            password = secrets.token_hex(16)
            password_reply = subprocess.run(
                [str(fixture.ROOT / "fn"), "principal", "set-password", principal,
                 "--control-sock", str(control)],
                cwd=fixture.ROOT, env=fixture.environment(), capture_output=True,
                input=f"{password}\n{password}\n".encode("ascii"), timeout=90)
            assert password_reply.returncode == 0, ("set-password", password_reply.returncode)
            credentials[principal] = password
        admin("secondary-only", "grant", "set", "fixture-reader", "read", VISIBLE.decode("ascii"))
        node.kill()
    finally:
        node.close()

    node = start("recovered")
    try:
        port = int(node.marker(b"LISTENING ").split()[1])
        node.marker(b"LISTENING-LOCAL ")
        # Change one byte of the recovered reader's password. The principal,
        # TLS state, stored group grants and password length are identical.
        issued = credentials["fixture-reader"]
        wrong = ("0" if issued[0] != "0" else "1") + issued[1:]
        with login_attempt(port, cert, "fixture-reader", wrong, expected=b"481") as peer:
            denied(peer)
        with login_attempt(port, cert, "fixture-denied", credentials["fixture-denied"]) as peer:
            denied(peer)
        with login_attempt(port, cert, "fixture-reader", credentials["fixture-reader"]) as peer:
            readable(peer)
            admin("revoke-secondary", "grant", "set", "fixture-reader", "read",
                  VISIBLE.decode("ascii"), "--revoke")
            for command in (b"STAT", b"ARTICLE 1", b"OVER 1-2", b"LISTGROUP"):
                reply = peer.command(command)
                assert reply.startswith(b"412 "), (command, reply)
            denied(peer)
    finally:
        node.close()
        for path in (control, Path(f"{control}.groups")):
            path.unlink(missing_ok=True)
    print("PASS recovered NNTP login, ninth-group crosspost and same-session grant revocation")


if __name__ == "__main__":
    main()
