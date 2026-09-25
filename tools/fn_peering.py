#!/usr/bin/env python3
"""Peering with strangers: invitations, key statements and pull feeds (SPIKE).

SPIKE (spike/peering, D28).  Everything in this file is a host-side
orchestration the dev version must move under ACL2 ownership; every such
decision is marked `SPIKE: defers ...` and listed in
planning/evidence/spike-peering-2026-09-25.md.  The file computes no value
ACL2 computes for acceptance: signatures are made and checked by the native
image (`hybrid-sign-carrier`, `hybrid-verify-source`), enrollment and
revocation go through the node's control socket (`hybrid-enroll`,
`hybrid-revoke`), peer records through the ACL2-planned operator `peer add`
(the assured reconfiguration path, live over the control socket), and
verdicts are the node's own `HDR :fn-verified` answers.

    fn_peering.py keygen DIR
    fn_peering.py invite   --node CONFIG --keys DIR --name PEER --groups W \\
                           --host H --port P [--author DIR ...] --out FILE
    fn_peering.py accept   --node CONFIG --keys DIR FILE --out FILE \\
                           [--enrol-author HEX ...] [--inbound-source ADDR] \\
                           [--reachable HOST:PORT] [--expect-principal HEX]
    fn_peering.py confirm  --node CONFIG --keys DIR FILE [--inbound-source ADDR]
    fn_peering.py succession --old DIR --new DIR --out FILE
    fn_peering.py revocation --keys DIR --out FILE
    fn_peering.py keys-process --node CONFIG [--group fn.keys] [--state FILE]
    fn_peering.py pull --from H:P --into H:P [--bind ADDR] --groups W \\
                       --state FILE [--rounds N --interval S]

Outcomes keep D13's three words and exit codes: accepted 0, refused 1,
uncertain 3 (usage 5).  A statement or invitation that does not verify is
refused, never "unverified-but-applied".
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import secrets
import socket
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, EXIT_USAGE = 0, 1, 3, 5
WORD = {EXIT_OK: "accepted", EXIT_REFUSED: "refused", EXIT_UNCERTAIN: "uncertain",
        EXIT_USAGE: "usage"}
PROTOCOL = "fn-peering-spike-v1"


class Outcome(Exception):
    def __init__(self, code, message):
        super().__init__(message)
        self.code = code


def refuse(message):
    raise Outcome(EXIT_REFUSED, message)


def log(line):
    print(line, flush=True)


# ---------------------------------------------------------------------------
# the node: its configuration file, image, control socket and reader port

def parse_toml(path):
    try:
        import tomllib
        return tomllib.loads(Path(path).read_text())
    except ModuleNotFoundError:  # pragma: no cover - hbox has 3.12
        raise Outcome(EXIT_USAGE, "python 3.11+ is required for tomllib")


class Node:
    def __init__(self, config):
        self.config = Path(config).resolve()
        data = parse_toml(self.config)
        self.store = Path(data["store"]["path"])
        self.control = Path(data.get("control", {}).get("path",
                                                          str(self.store / "control.sock")))
        listener = data.get("listener", {})
        self.host = listener.get("host", "127.0.0.1")
        self.port = int(listener.get("port", 1119))
        self.state = self.config.parent / "peering"
        self.state.mkdir(exist_ok=True)

    def operator(self, *words, check=True):
        result = image("operator", str(self.config), *words, check=False)
        if check and result.returncode != 0:
            raise Outcome(EXIT_UNCERTAIN if result.returncode == 3 else EXIT_REFUSED,
                          "operator {} -> {} {}".format(" ".join(words), result.returncode,
                                                        result.stderr.strip()))
        return result

    def enroll(self, keys):
        # SPIKE: defers an ACL2-owned "next generation" request; 0 = next
        # (host/native/hybrid-control.lisp).
        result = image("hybrid-enroll", str(self.control), "0", str(keys.principal_path),
                       str(keys.ed_public_path), str(keys.ml_public_path), check=False)
        return result.returncode

    def revoke(self, principal_path):
        return image("hybrid-revoke", str(self.control), "0", str(principal_path),
                     check=False).returncode

    def reader(self):
        return Nntp(self.host, self.port)


def image_path():
    return os.environ.get("FN_NATIVE_HOST", str(ROOT / "build" / "fn-host"))


def image(*args, check=True, timeout=120):
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    result = subprocess.run([image_path(), "--fn", *args], stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, env=env, timeout=timeout,
                            check=False)
    if check and result.returncode != 0:
        raise Outcome(EXIT_REFUSED, "{} -> {}: {}".format(args[0], result.returncode,
                                                          result.stderr.strip()[-400:]))
    return result


def openssl(*args):
    subprocess.run([os.environ.get("FN_OPENSSL", "openssl"), *args], check=True,
                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)


# ---------------------------------------------------------------------------
# key directories: principal.bin, ed-public.bin, ed-secret.bin (seed||public),
# ml-private.pem, ml-public.pem.  The principal is 32 random octets.
# SPIKE: defers the genesis binding (books/principal.lisp
# fn-prin-genesis-bindsp) of a principal id to its first key.

class Keys:
    def __init__(self, directory):
        self.dir = Path(directory)
        self.principal_path = self.dir / "principal.bin"
        self.ed_public_path = self.dir / "ed-public.bin"
        self.ed_secret_path = self.dir / "ed-secret.bin"
        self.ml_private_path = self.dir / "ml-private.pem"
        self.ml_public_path = self.dir / "ml-public.pem"

    @property
    def principal(self):
        return self.principal_path.read_bytes().hex()

    @property
    def ed_public(self):
        return self.ed_public_path.read_bytes().hex()

    @property
    def ml_pem(self):
        return self.ml_public_path.read_text()

    def sign(self, source: bytes, stem: str) -> bytes:
        work = self.dir / "work"
        work.mkdir(exist_ok=True)
        src, out = work / (stem + ".src"), work / (stem + ".signed")
        src.write_bytes(source)
        if out.exists():
            out.unlink()
        image("hybrid-sign-carrier", str(self.principal_path), str(self.ed_public_path),
              str(self.ed_secret_path), str(self.ml_public_path), str(self.ml_private_path),
              str(src), str(out))
        return out.read_bytes()


def keygen(directory, principal=None):
    keys = Keys(directory)
    keys.dir.mkdir(parents=True, exist_ok=True)
    if principal is not None:
        keys.principal_path.write_bytes(bytes.fromhex(principal))
    elif not keys.principal_path.exists():
        keys.principal_path.write_bytes(secrets.token_bytes(32))
    der = keys.dir / "ed-private.der"
    openssl("genpkey", "-algorithm", "ED25519", "-outform", "DER", "-out", str(der))
    pub = keys.dir / "ed-public.der"
    openssl("pkey", "-inform", "DER", "-in", str(der), "-pubout", "-outform", "DER",
            "-out", str(pub))
    seed, public = der.read_bytes()[-32:], pub.read_bytes()[-32:]
    keys.ed_public_path.write_bytes(public)
    keys.ed_secret_path.write_bytes(seed + public)
    os.chmod(keys.ed_secret_path, 0o600)
    der.unlink()
    pub.unlink()
    openssl("genpkey", "-algorithm", "ML-DSA-65", "-out", str(keys.ml_private_path))
    os.chmod(keys.ml_private_path, 0o600)
    openssl("pkey", "-in", str(keys.ml_private_path), "-pubout", "-out",
            str(keys.ml_public_path))
    return keys


def pem_line(pem: str) -> str:
    return "".join(line for line in pem.splitlines() if not line.startswith("-----"))


def pem_of_line(body: str) -> str:
    lines = [body[i:i + 64] for i in range(0, len(body), 64)]
    return "-----BEGIN PUBLIC KEY-----\n" + "\n".join(lines) + "\n-----END PUBLIC KEY-----\n"


# ---------------------------------------------------------------------------
# signed documents: an article whose body is `Key: value` lines, carried by
# FN-Authorship (books/hybrid-carrier.lisp).  Verification is the native
# `hybrid-verify-source` over the claimed ML key; the verified line gives the
# principal, the authored-source identity, the Ed25519 key and the exact
# authored source, and the body's claims must equal the verified keys.

def rfc5322_date():
    return dt.datetime.now(dt.timezone.utc).strftime("%a, %d %b %Y %H:%M:%S +0000")


def document(kind, group, msgid, fields, author="fn-peering@invalid"):
    head = ("From: {}\r\nDate: {}\r\nNewsgroups: {}\r\nSubject: {}\r\n"
            "Message-ID: {}\r\n\r\n").format(author, rfc5322_date(), group, kind, msgid)
    body = "".join("{}: {}\r\n".format(k, v) for k, v in fields)
    return (head + body).encode("ascii")


def body_fields(source: bytes):
    text = source.decode("ascii", "replace")
    _, _, body = text.partition("\r\n\r\n")
    fields = {}
    for line in body.split("\r\n"):
        if ": " in line:
            key, value = line.split(": ", 1)
            fields.setdefault(key, value)
    return fields


def verify_document(signed: bytes, ml_pem_line: str, work: Path, stem: str):
    """Returns (principal-hex, source-id-hex, ed-hex, source-bytes) or refuses."""
    work.mkdir(parents=True, exist_ok=True)
    article, pem = work / (stem + ".eml"), work / (stem + "-ml.pem")
    article.write_bytes(signed)
    pem.write_text(pem_of_line(ml_pem_line))
    result = image("hybrid-verify-source", str(article), str(pem), check=False)
    if result.returncode != 0:
        refuse("{} does not verify: {}".format(stem, (result.stdout + result.stderr).strip()[-300:]))
    words = result.stdout.split()
    if len(words) != 6 or words[0] != "fn-portable-v1":
        refuse("{}: unexpected verifier line".format(stem))
    principal, source_id, ed, _ml, source = words[1:]
    return principal, source_id, ed, bytes.fromhex(source)


def peek_fields(signed: bytes):
    """Read the claimed ML key from the carried source before verifying it.

    The claim is only a key to try: verification checks the carrier's key
    set against it and the body's claims against the verified line."""
    text = signed.decode("ascii", "replace")
    marker = "\r\n\r\n"
    parts = text.split(marker)
    for index in range(len(parts) - 1, 0, -1):
        fields = body_fields((marker.join(parts[index - 1:])).encode("ascii", "replace"))
        if "ML-DSA-65" in fields or "New-ML-DSA-65" in fields:
            return fields
    return body_fields(signed)


# ---------------------------------------------------------------------------
# invite / accept / confirm

def pending_path(node):
    return node.state / "invitations.json"


def load_json(path, default):
    try:
        return json.loads(Path(path).read_text())
    except FileNotFoundError:
        return default


def save_json(path, value):
    tmp = Path(str(path) + ".tmp")
    tmp.write_text(json.dumps(value, indent=1, sort_keys=True))
    os.replace(tmp, path)


def path_identity(node):
    listing = node.operator("peer", "list", check=False)
    return None if listing.returncode else listing.stdout


def command_invite(args):
    node, keys = Node(args.node), Keys(args.keys)
    nonce = secrets.token_hex(16)
    authors = [Keys(d) for d in args.author or ()]
    fields = [("FN-Peering", "invitation " + PROTOCOL), ("Invitee", args.name),
              ("Inviter-Path", args.path_id), ("Principal", keys.principal),
              ("Ed25519", keys.ed_public), ("ML-DSA-65", pem_line(keys.ml_pem)),
              ("Groups", args.groups), ("Host", args.host), ("Port", str(args.port)),
              ("Nonce", nonce),
              ("Carries", ",".join([keys.principal] + [a.principal for a in authors]))]
    for index, author in enumerate(authors):
        fields += [("Author-{}".format(index), author.principal),
                   ("Author-{}-Ed25519".format(index), author.ed_public),
                   ("Author-{}-ML-DSA-65".format(index), pem_line(author.ml_pem))]
    source = document("fn-invitation", "fn.peering", "<invite-{}@{}>".format(nonce, args.path_id),
                      fields)
    signed = keys.sign(source, "invite-" + nonce)
    Path(args.out).write_bytes(signed)
    pending = load_json(pending_path(node), {})
    # SPIKE: defers the durable invitation record to a Store record kind with
    # its once-only consumption theorem; here it is a JSON file beside the
    # configuration, consumed by `confirm`.
    pending[nonce] = {"name": args.name, "groups": args.groups, "state": "pending",
                      "sha256": hashlib.sha256(signed).hexdigest(),
                      "source_sha256": hashlib.sha256(source).hexdigest()}
    save_json(pending_path(node), pending)
    log("accepted invite {} nonce={} out={} sha256={}".format(
        args.name, nonce, args.out, hashlib.sha256(signed).hexdigest()))
    return EXIT_OK


def enroll_claimed(node, directory, principal, ed_hex, ml_line):
    work = Keys(directory)
    work.dir.mkdir(parents=True, exist_ok=True)
    work.principal_path.write_bytes(bytes.fromhex(principal))
    work.ed_public_path.write_bytes(bytes.fromhex(ed_hex))
    work.ml_public_path.write_text(pem_of_line(ml_line))
    return node.enroll(work)


def peer_add(node, name, path_id, host, port, inbound, outbound, source, carries):
    words = ["peer", "add", name, path_id, host, str(port), inbound, outbound,
             "source-address", source, "false"]
    if carries:
        words += ["carries", *carries]
    return node.operator(*words)


def command_accept(args):
    node, keys = Node(args.node), Keys(args.keys)
    signed = Path(args.file).read_bytes()
    claimed = peek_fields(signed)
    if "ML-DSA-65" not in claimed:
        refuse("invitation names no ML-DSA-65 key")
    work = node.state / "work"
    principal, source_id, ed, source = verify_document(signed, claimed["ML-DSA-65"], work,
                                                       "invitation")
    fields = body_fields(source)
    # The binding: what the invitation claims is what signed it.
    if fields.get("FN-Peering") != "invitation " + PROTOCOL:
        refuse("not an invitation")
    if fields.get("Principal") != principal or fields.get("Ed25519") != ed:
        refuse("invitation's claimed keys are not the keys that signed it")
    if args.expect_principal and args.expect_principal != principal:
        refuse("invitation principal {} is not the expected {}".format(
            principal, args.expect_principal))
    seen = load_json(node.state / "accepted.json", {})
    if fields["Nonce"] in seen:
        refuse("invitation nonce {} already accepted".format(fields["Nonce"]))
    inviter = fields["Inviter-Path"]
    # 1. Enrol the inviting node's principal (its statements verify here).
    code = enroll_claimed(node, node.state / "keys" / principal, principal, ed,
                          fields["ML-DSA-65"])
    if code != 0:
        raise Outcome(code if code in (1, 3) else 1, "enrolling {} -> {}".format(principal, code))
    log("accepted enrol inviter principal={}".format(principal))
    # 2. Authors the operator chose to enrol on the inviter's introduction.
    #    Carrying is not authority: the rest are carried, never verified.
    index = 0
    while "Author-{}".format(index) in fields:
        author = fields["Author-{}".format(index)]
        if author in (args.enrol_author or ()):
            code = enroll_claimed(node, node.state / "keys" / author, author,
                                  fields["Author-{}-Ed25519".format(index)],
                                  fields["Author-{}-ML-DSA-65".format(index)])
            log("{} enrol introduced author={}".format(WORD.get(code, "fault"), author))
        index += 1
    # 3. The peer record, with carries-principal rows for the offered groups,
    #    through the ACL2-planned administrative path (live: control socket).
    carries = [c for c in fields.get("Carries", "").split(",") if c]
    peer_add(node, args.as_name or inviter, inviter, fields["Host"], fields["Port"],
             fields["Groups"], fields["Groups"] if args.feed else "-",
             args.inbound_source, carries)
    log("accepted peer add {} inbound={} carries={}".format(inviter, fields["Groups"],
                                                            len(carries)))
    # 4. The signed acceptance: it names the invitation it answers by nonce,
    #    by the inviter's principal and by the ACL2 authored-source identity.
    reach = args.reachable or "-"
    reply = [("FN-Peering", "acceptance " + PROTOCOL), ("Nonce", fields["Nonce"]),
             ("Invitation-Source-Id", source_id), ("Inviter-Principal", principal),
             ("Acceptor-Path", args.path_id), ("Principal", keys.principal),
             ("Ed25519", keys.ed_public), ("ML-DSA-65", pem_line(keys.ml_pem)),
             ("Reachable", reach), ("Source-Address", args.connects_from),
             ("Groups", fields["Groups"]), ("Carries", keys.principal)]
    source = document("fn-acceptance", "fn.peering",
                      "<accept-{}@{}>".format(fields["Nonce"], args.path_id), reply)
    signed_reply = keys.sign(source, "accept-" + fields["Nonce"])
    Path(args.out).write_bytes(signed_reply)
    seen[fields["Nonce"]] = {"inviter": principal, "source_id": source_id}
    save_json(node.state / "accepted.json", seen)
    log("accepted accept nonce={} out={} sha256={}".format(
        fields["Nonce"], args.out, hashlib.sha256(signed_reply).hexdigest()))
    return EXIT_OK


def command_confirm(args):
    node, keys = Node(args.node), Keys(args.keys)
    signed = Path(args.file).read_bytes()
    claimed = peek_fields(signed)
    principal, _sid, ed, source = verify_document(signed, claimed.get("ML-DSA-65", ""),
                                                  node.state / "work", "acceptance")
    fields = body_fields(source)
    if fields.get("FN-Peering") != "acceptance " + PROTOCOL:
        refuse("not an acceptance")
    if fields.get("Principal") != principal or fields.get("Ed25519") != ed:
        refuse("acceptance's claimed keys are not the keys that signed it")
    pending = load_json(pending_path(node), {})
    record = pending.get(fields.get("Nonce", ""))
    if record is None:
        refuse("acceptance answers no invitation of this node")
    if record["state"] != "pending":
        refuse("invitation {} already {}".format(fields["Nonce"], record["state"]))
    if fields.get("Inviter-Principal") != keys.principal:
        refuse("acceptance names another inviter")
    # The invitation's ACL2 authored-source identity: recompute from our copy.
    ours = Path(args.invitation).read_bytes() if args.invitation else None
    if ours is not None:
        _p, our_sid, _e, _s = verify_document(ours, pem_line(keys.ml_pem), node.state / "work",
                                              "our-invitation")
        if our_sid != fields.get("Invitation-Source-Id"):
            refuse("acceptance binds another invitation source")
    code = enroll_claimed(node, node.state / "keys" / principal, principal, ed,
                          fields["ML-DSA-65"])
    if code != 0:
        raise Outcome(code if code in (1, 3) else 1, "enrolling {} -> {}".format(principal, code))
    log("accepted enrol acceptor principal={}".format(principal))
    reach = fields.get("Reachable", "-")
    host, port = (reach.rsplit(":", 1) if reach != "-" else ("127.0.0.1", "119"))
    peer_add(node, record["name"], fields["Acceptor-Path"], host, port, record["groups"],
             record["groups"] if reach != "-" else "-",
             args.inbound_source or fields.get("Source-Address", "127.0.0.1"),
             [c for c in fields.get("Carries", "").split(",") if c])
    record["state"] = "confirmed"
    record["peer_principal"] = principal
    save_json(pending_path(node), pending)
    log("accepted confirm {} nonce={} outbound={}".format(record["name"], fields["Nonce"],
                                                          "none (unreachable: pulls)"
                                                          if reach == "-" else reach))
    return EXIT_OK


# ---------------------------------------------------------------------------
# key statements: succession and revocation, posted as ordinary signed
# articles in a control-like group (fn.keys).  A node acts on a statement
# only when ITS OWN verdict is `verified P` for the statement's principal P:
# the old key is this node's current enrollment of P (so a replayed or
# superseded statement is refused at acceptance and never acted on), and a
# `carried` or `revoked` verdict is never authority.

def command_succession(args):
    old, new = Keys(args.old), Keys(args.new)
    if old.principal != new.principal:
        refuse("succession keeps the principal: old and new key directories differ")
    nonce = secrets.token_hex(8)
    msgid = "<succession-{}@fn-keys.invalid>".format(nonce)
    pop_source = document("fn-key-pop", args.group, "<pop-{}@fn-keys.invalid>".format(nonce),
                          [("FN-Key-PoP", PROTOCOL), ("Principal", old.principal),
                           ("Old-Ed25519", old.ed_public), ("New-Ed25519", new.ed_public),
                           ("Statement", msgid)])
    pop = new.sign(pop_source, "pop-" + nonce)
    source = document("fn-key-succession " + old.principal, args.group, msgid,
                      [("FN-Key-Statement", "succession " + PROTOCOL),
                       ("Principal", old.principal), ("Old-Ed25519", old.ed_public),
                       ("New-Ed25519", new.ed_public),
                       ("New-ML-DSA-65", pem_line(new.ml_pem)),
                       ("Proof-Of-Possession", base64.b64encode(pop).decode())],
                      author="{}@fn-keys.invalid".format(old.principal[:16]))
    Path(args.out).write_bytes(old.sign(source, "succession-" + nonce))
    log("accepted succession principal={} msgid={} out={}".format(old.principal, msgid, args.out))
    return EXIT_OK


def command_revocation(args):
    keys = Keys(args.keys)
    nonce = secrets.token_hex(8)
    msgid = "<revocation-{}@fn-keys.invalid>".format(nonce)
    source = document("fn-key-revocation " + keys.principal, args.group, msgid,
                      [("FN-Key-Statement", "revocation " + PROTOCOL),
                       ("Principal", keys.principal), ("Reason", args.reason)],
                      author="{}@fn-keys.invalid".format(keys.principal[:16]))
    Path(args.out).write_bytes(keys.sign(source, "revocation-" + nonce))
    log("accepted revocation principal={} msgid={} out={}".format(keys.principal, msgid,
                                                                  args.out))
    return EXIT_OK


def command_keys_process(args):
    """SPIKE: defers the statement executor to ACL2 (C2's fn-ctl-authorize
    shape: a verified verdict and a grant covering the namespace), run by the
    owner at acceptance rather than by a reader-side poller."""
    node = Node(args.node)
    state_path = Path(args.state) if args.state else node.state / "keys-process.json"
    state = load_json(state_path, {"done": {}})
    acted = 0
    with node.reader() as nntp:
        for msgid, article in nntp.group_articles(args.group):
            if msgid in state["done"]:
                continue
            verdict = nntp.verdict(msgid)
            fields = body_fields(strip_carrier_head(article))
            kind = fields.get("FN-Key-Statement", "")
            principal = fields.get("Principal", "")
            words = verdict.split()
            outcome = decide_statement(node, kind, principal, words, fields, msgid)
            state["done"][msgid] = outcome
            log("{} key-statement {} kind={} principal={} verdict={!r}".format(
                outcome.split()[0], msgid, kind.split(" ")[0] or "-", principal or "-", verdict))
            acted += outcome.startswith("accepted")
    save_json(state_path, state)
    log("accepted keys-process acted={}".format(acted))
    return EXIT_OK


def strip_carrier_head(article: bytes) -> bytes:
    return article


def decide_statement(node, kind, principal, words, fields, msgid):
    if not kind:
        return "refused not-a-statement"
    if len(words) < 2 or words[0] != "verified":
        return "refused verdict-not-verified ({}): carrying is not authority".format(
            words[0] if words else "none")
    if words[1] != principal:
        return "refused verdict-names-another-principal"
    if kind == "succession " + PROTOCOL:
        pop = base64.b64decode(fields.get("Proof-Of-Possession", ""))
        p, _sid, ed, pop_source = verify_document(pop, fields.get("New-ML-DSA-65", ""),
                                                  node.state / "work", "pop")
        pop_fields = body_fields(pop_source)
        if not (p == principal and ed == fields.get("New-Ed25519")
                and pop_fields.get("Principal") == principal
                and pop_fields.get("Old-Ed25519") == fields.get("Old-Ed25519")
                and pop_fields.get("New-Ed25519") == ed
                and pop_fields.get("Statement") == msgid):
            return "refused proof-of-possession"
        code = enroll_claimed(node, node.state / "keys" / (principal + "-" + ed[:8]),
                              principal, ed, fields["New-ML-DSA-65"])
        return "{} enrol-successor ed={} (old key superseded from the next generation)".format(
            WORD.get(code, "fault"), ed[:16])
    if kind == "revocation " + PROTOCOL:
        path = node.state / "work" / ("revoke-" + principal + ".bin")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(bytes.fromhex(principal))
        code = node.revoke(path)
        return "{} revoke".format(WORD.get(code, "fault"))
    return "refused unknown-statement"


# ---------------------------------------------------------------------------
# NNTP client pieces

class Nntp:
    def __init__(self, host, port, bind=None, timeout=30):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.settimeout(timeout)
        if bind:
            self.sock.bind((bind, 0))
        self.sock.connect((host, int(port)))
        self.file = self.sock.makefile("rwb", buffering=0)
        self.greeting = self.line()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        try:
            self.command("QUIT")
        except OSError:
            pass
        self.sock.close()

    def line(self):
        data = self.file.readline()
        if not data:
            raise OSError("connection closed")
        return data.decode("latin-1").rstrip("\r\n")

    def command(self, text):
        self.file.write(text.encode("latin-1") + b"\r\n")
        return self.line()

    def block(self):
        lines = []
        while True:
            raw = self.file.readline()
            if not raw:
                raise OSError("connection closed in a block")
            if raw == b".\r\n":
                return lines
            if raw.startswith(b".."):
                raw = raw[1:]
            lines.append(raw)

    def article(self, spec):
        status = self.command("ARTICLE " + spec)
        if not status.startswith("220"):
            return status, None
        return status, b"".join(self.block())

    def verdict(self, msgid):
        status = self.command("HDR :fn-verified " + msgid)
        if not status.startswith("225"):
            return "none " + status
        lines = self.block()
        if not lines:
            return "none"
        text = lines[0].decode("latin-1").strip()
        return text.split(" ", 1)[1] if " " in text else text

    def group_articles(self, group):
        status = self.command("GROUP " + group)
        if not status.startswith("211"):
            return
        _, count, low, high = status.split()[:4]
        for number in range(int(low), int(high) + 1):
            status, octets = self.article(str(number))
            if octets is None:
                continue
            parts = status.split()
            yield (parts[2] if len(parts) > 2 else ""), octets

    def ihave(self, msgid, octets):
        status = self.command("IHAVE " + msgid)
        if not status.startswith("335"):
            return status
        body = b"".join((b"." + l if l.startswith(b".") else l)
                        for l in octets.splitlines(keepends=True))
        if not body.endswith(b"\r\n"):
            body += b"\r\n"
        self.file.write(body + b".\r\n")
        return self.line()


# ---------------------------------------------------------------------------
# NEWNEWS-driven pull feed (RFC 3977 section 7.4).  SPIKE: defers the pull
# schedule and cursor to the owner (books/scheduler-peers.lisp) with an ACL2
# cursor record; here the cursor lives in a JSON file.
#
# An ack means what it names: the cursor advances past a run only when every
# article NEWNEWS listed drew a terminal answer from the local node -- 235
# (accepted), 435 (already held) or 437 (refused, recorded) -- and a 436 or a
# broken connection keeps the article pending for the next round.

def remote_date(nntp):
    status = nntp.command("DATE")
    if status.startswith("111 ") and len(status.split()[1]) == 14:
        return dt.datetime.strptime(status.split()[1], "%Y%m%d%H%M%S").replace(
            tzinfo=dt.timezone.utc)
    return dt.datetime.now(dt.timezone.utc)


def pull_round(args, state):
    fh, fp = args.source.rsplit(":", 1)
    ih, ip = args.into.rsplit(":", 1)
    counts = {"listed": 0, "235": 0, "435": 0, "437": 0, "pending": 0}
    with Nntp(fh, fp) as remote:
        started = remote_date(remote)
        since = dt.datetime.fromtimestamp(state.get("cursor", 0), dt.timezone.utc)
        status = remote.command("NEWNEWS {} {} GMT".format(args.groups,
                                                            since.strftime("%Y%m%d %H%M%S")))
        if not status.startswith("230"):
            raise Outcome(EXIT_UNCERTAIN, "NEWNEWS -> " + status)
        listed = [l.decode("latin-1").strip() for l in remote.block()]
        wanted = list(dict.fromkeys(state.get("pending", []) + listed))
        counts["listed"] = len(listed)
        pending = []
        with Nntp(ih, ip, bind=args.bind) as local:
            for msgid in wanted:
                astatus, octets = remote.article(msgid)
                if octets is None:
                    log("pull {} remote {}".format(msgid, astatus))
                    continue
                answer = local.ihave(msgid, octets)
                code = answer[:3]
                log("pull {} -> {}".format(msgid, answer))
                if code in ("235", "435", "437"):
                    counts[code] += 1
                else:
                    pending.append(msgid)
                    counts["pending"] += 1
    state["pending"] = pending
    # One second of overlap: an article arriving in the same second as DATE is
    # listed again next round and answered 435, never missed.
    state["cursor"] = int(started.timestamp()) - 1 if not pending else state.get("cursor", 0)
    return counts


def command_pull(args):
    state_path = Path(args.state)
    state = load_json(state_path, {"cursor": 0, "pending": []})
    for round_index in range(args.rounds):
        try:
            counts = pull_round(args, state)
            save_json(state_path, state)
            log("accepted pull round={} {} cursor={}".format(
                round_index, " ".join("{}={}".format(k, v) for k, v in counts.items()),
                state["cursor"]))
        except (OSError, Outcome) as error:
            log("uncertain pull round={} {}".format(round_index, error))
        if round_index + 1 < args.rounds:
            time.sleep(args.interval)
    return EXIT_OK


# ---------------------------------------------------------------------------

def build_parser():
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="command", required=True)
    k = sub.add_parser("keygen")
    k.add_argument("dir")
    k.add_argument("--principal")
    i = sub.add_parser("invite")
    i.add_argument("--node", required=True)
    i.add_argument("--keys", required=True)
    i.add_argument("--name", required=True)
    i.add_argument("--path-id", required=True)
    i.add_argument("--groups", required=True)
    i.add_argument("--host", required=True)
    i.add_argument("--port", type=int, required=True)
    i.add_argument("--author", action="append")
    i.add_argument("--out", required=True)
    a = sub.add_parser("accept")
    a.add_argument("file")
    a.add_argument("--node", required=True)
    a.add_argument("--keys", required=True)
    a.add_argument("--path-id", required=True)
    a.add_argument("--as-name")
    a.add_argument("--out", required=True)
    a.add_argument("--enrol-author", action="append")
    a.add_argument("--inbound-source", default="127.0.0.1",
                   help="the address the inviter's articles arrive from here")
    a.add_argument("--connects-from", default="127.0.0.1",
                   help="the address this node's feed connects to the inviter from")
    a.add_argument("--reachable", help="HOST:PORT the inviter may feed; omit behind NAT")
    a.add_argument("--feed", action="store_true", help="feed the inviter (outbound)")
    a.add_argument("--expect-principal")
    c = sub.add_parser("confirm")
    c.add_argument("file")
    c.add_argument("--node", required=True)
    c.add_argument("--keys", required=True)
    c.add_argument("--invitation")
    c.add_argument("--inbound-source")
    s = sub.add_parser("succession")
    s.add_argument("--old", required=True)
    s.add_argument("--new", required=True)
    s.add_argument("--group", default="fn.keys")
    s.add_argument("--out", required=True)
    r = sub.add_parser("revocation")
    r.add_argument("--keys", required=True)
    r.add_argument("--group", default="fn.keys")
    r.add_argument("--reason", default="key-compromise")
    r.add_argument("--out", required=True)
    kp = sub.add_parser("keys-process")
    kp.add_argument("--node", required=True)
    kp.add_argument("--group", default="fn.keys")
    kp.add_argument("--state")
    pl = sub.add_parser("pull")
    pl.add_argument("--from", dest="source", required=True)
    pl.add_argument("--into", required=True)
    pl.add_argument("--bind")
    pl.add_argument("--groups", required=True)
    pl.add_argument("--state", required=True)
    pl.add_argument("--rounds", type=int, default=1)
    pl.add_argument("--interval", type=float, default=30.0)
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)
    try:
        if args.command == "keygen":
            keys = keygen(args.dir, args.principal)
            log("accepted keygen principal={} ed={}".format(keys.principal, keys.ed_public))
            return EXIT_OK
        return {"invite": command_invite, "accept": command_accept,
                "confirm": command_confirm, "succession": command_succession,
                "revocation": command_revocation, "keys-process": command_keys_process,
                "pull": command_pull}[args.command](args)
    except Outcome as outcome:
        log("{} {} {}".format(WORD.get(outcome.code, "fault"), args.command, outcome))
        return outcome.code


if __name__ == "__main__":
    sys.exit(main())
