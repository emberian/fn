#!/usr/bin/env python3
"""Exercise delivered cancellation through protected POST and owner APPEND.

Requires a qualified image with delivered withdrawal and scoped peer
admission. The fresh isolated image is retained for inspection.
"""
import argparse
import importlib.util
import os
from pathlib import Path
import secrets
import subprocess
import time

SPEC = importlib.util.spec_from_file_location(
    "nntp_authority", Path(__file__).with_name("native-nntp-read-authority.py"))
authority = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(authority)
fixture = authority.fixture

GROUPS = (b"local.test", b"local.other")
CONTROL = b"control.cancel"
ALICE_TARGET = b"<withdraw-author@example.invalid>"
ADMIN_TARGET = b"<withdraw-owner@example.invalid>"


def article(mid, groups, target=None, transit=False):
    source = fixture.crossing_article(mid.decode("ascii")).replace(
        b"Newsgroups: local.test\r\n", b"Newsgroups: " + b",".join(groups) + b"\r\n", 1)
    headers = b"Path: peer.invalid!not-for-mail\r\n" if transit else b""
    if target:
        headers += b"Control: cancel " + target + b"\r\n"
    return headers + source


def nntp_article(peer, verb, source, ready, done):
    prompt = peer.command(verb)
    assert prompt.startswith(ready + b" "), (verb, prompt)
    lines = source.split(b"\r\n")
    assert lines[-1] == b""
    wire = b"\r\n".join(b"." + line if line.startswith(b".") else line for line in lines)
    reply = peer.command(wire + b".")
    assert reply.startswith(done + b" "), (verb, reply)


def projection(peer, count, high, absent=()):
    for group in GROUPS:
        reply = peer.command(b"GROUP " + group)
        fields = reply.split()
        assert fields[0] == b"211" and fields[-1] == group, reply
        assert int(fields[1]) == count and int(fields[3]) == high, reply
    for target in absent:
        assert peer.command(b"STAT " + target).startswith(b"430 ")


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
    fixture.initialize(directory, image, startup_args=tuple(
        word for group in (*GROUPS, CONTROL) for word in ("--group", group.decode("ascii"))))
    control = Path(f"/tmp/fn2-withdrawal-{os.getpid()}-{time.time_ns()}.sock")

    def start(label):
        env = fixture.environment()
        env.pop("FN2_ENVELOPE_TRACE", None)
        return fixture.restart.Node(directory, image, "serve", label, control_sock=control,
                                    env=env, startup_args=(
                                        "--tls-certificate", str(cert), "--tls-key", str(key), "--peering"))

    def admin(label, *args, expected=0):
        return fixture.run_fn(directory, label, *args, "--control-sock", control, expected=expected)

    def account(name):
        assert admin(name, "principal", "create", name)["outcome"] == "accepted"
        phrase = secrets.token_hex(16)
        reply = subprocess.run([str(fixture.ROOT / "fn"), "principal", "set-password", name,
                                "--control-sock", str(control)], cwd=fixture.ROOT,
                               input=f"{phrase}\n{phrase}\n".encode("ascii"), env=fixture.environment(),
                               capture_output=True, timeout=90)
        assert reply.returncode == 0, ("set-password", reply.returncode)
        return phrase

    def grant(principal, right, group=None):
        suffix = () if group is None else (group.decode("ascii"),)
        label = "-".join((principal, right, *suffix))
        assert admin(label, "grant", "set", principal, right, *suffix)["outcome"] == "accepted"

    def login(port, name, phrase):
        return authority.login_attempt(port, cert, name, phrase)

    cancel_file = directory / "owner-cancel.article"
    cancel_file.write_bytes(article(b"<owner-cancel@example.invalid>", (CONTROL,), ADMIN_TARGET))

    def owner_append(label, path, expected=0):
        return admin(label, "stream", "append", "--file", path, "--op", "91", expected=expected)

    node = start("initial")
    try:
        port = int(node.marker(b"LISTENING ").split()[1])
        node.marker(b"LISTENING-LOCAL ")
        alice = account("withdraw-author")
        bob = account("withdraw-foreign")
        relay = account("withdraw-peer")
        for group in GROUPS:
            grant("withdraw-author", "read", group)
            grant("withdraw-author", "append", group)
        grant("withdraw-author", "append", CONTROL)
        grant("withdraw-foreign", "append", CONTROL)
        grant("withdraw-peer", "peer")
        grant("withdraw-peer", "peer-accept", CONTROL)
        grant("withdraw-peer", "append", CONTROL)

        with login(port, "withdraw-author", alice) as reader:
            for target in (ALICE_TARGET, ADMIN_TARGET):
                nntp_article(reader, b"POST", article(target, GROUPS), b"340", b"240")
            projection(reader, 2, 2)

        with login(port, "withdraw-foreign", bob) as other:
            nntp_article(other, b"POST",
                         article(b"<foreign-cancel@example.invalid>", (CONTROL,), ALICE_TARGET),
                         b"340", b"441")
        with login(port, "withdraw-peer", relay) as other:
            mid = b"<peer-cancel@example.invalid>"
            # fixture.crossing_article supplies the same From for both the
            # target and this forwarded cancel. Only the login differs.
            nntp_article(other, b"IHAVE " + mid, article(mid, (CONTROL,), ALICE_TARGET, transit=True),
                         b"335", b"437")

        with login(port, "withdraw-author", alice) as reader:
            projection(reader, 2, 2)
            nntp_article(reader, b"POST",
                         article(b"<author-cancel@example.invalid>", (CONTROL,), ALICE_TARGET),
                         b"340", b"240")
            projection(reader, 1, 2, (ALICE_TARGET,))

        receipt = owner_append("owner-cancel", cancel_file)
        assert receipt["outcome"] == "accepted" and receipt["evidence"] == "committed", receipt
        with login(port, "withdraw-author", alice) as reader:
            projection(reader, 0, 2, (ALICE_TARGET, ADMIN_TARGET))
        node.kill()
    finally:
        node.close()

    node = start("reopen")
    try:
        port = int(node.marker(b"LISTENING ").split()[1])
        node.marker(b"LISTENING-LOCAL ")
        assert owner_append("owner-cancel-retry", cancel_file) == receipt
        conflicting = directory / "owner-cancel-conflict.article"
        conflicting.write_bytes(article(b"<owner-other@example.invalid>", (CONTROL,), ALICE_TARGET))
        assert owner_append("owner-cancel-conflict", conflicting, expected=1)["reason"] == "operation-reused"
        with login(port, "withdraw-author", alice) as reader:
            projection(reader, 0, 2, (ALICE_TARGET, ADMIN_TARGET))
    finally:
        node.close()


if __name__ == "__main__":
    main()
