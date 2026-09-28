#!/usr/bin/env python3
"""Synthesize a large format-10 store by writing its record log directly.

    tools/synth_log_store.py SEED OUT N [--batch B] [--check-only]

SEED is a real format-10 store with no checkpoint whose journal/000001.log holds
article records written by the owner (a POSTed fixture: tools/fixtures.py's
n1k-2k).  OUT (must not exist) gets SEED's files except journal/, and a
journal/000001.log of N article records made from SEED's records by
renumbering: record i is template i mod |SEED| with sequence i, txid and
generation i + 1, a fresh Message-ID of the template's length (in the record
and in the payload's Message-ID header, so the payload's length and charge are
the template's), and the subject and obligation identities recomputed from the
new payload and Message-ID exactly as books/identity.lisp defines them
(fn-id-subject-of-payload, fn-id-obligation-of; checked on every template
first: the recomputation must reproduce each template's own identities, or the
tool refuses).  Entries are the log's frames (books/store-log.lisp fn-lg-entry:
FNLG, version 1, kind 1 for one record or kind 2 for B records packed, the
previous trailer first in the payload, SHA-256 trailer, zero padding to the
4096-octet unit), chained from the trailer of the seed's genesis
(journal/000000.log, books/store-genesis.lisp: position 0 of the log, one
kind-3 frame; copied unchanged, so OUT is the seed's node: its identity,
history salt and profile digest -- the profile is copied too).  The digest is
the store's frame digest, BLAKE3 (digest below).

The seed's profile and configuration must hold N: a 2 KiB article is charged
2 units of the store's capacity (fn-charge-for-payload), and the default
capacity (1,048,576) refuses the replay past ~524k articles.  For 1M: import
the seed's export with --max-transactions 4000000 --max-history-octets
8000000000, run it once and set `capacity 4000000` (a configuration record at
the txid after the seed's; the renumbered history ties it, configuration
first, as the replay orders a tie).  The record's
planning/evidence/snapshot-open-2-2026-09-27.md section 5 has the commands.

This is a TEST FIXTURE writer: it decides nothing the node relies on.  The
node's own open verifies every frame, chain link and record (a fixture it
refuses is refused by name), so a wrong byte here is a refused fixture, never
an accepted wrong history.  Streams: memory is one batch, whatever N is.
"""
import argparse, os, shutil, struct, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import blake3_ref  # noqa: E402  fn's digest (books/blake3.lisp), store format 10

UNIT = 4096
MAGIC = b"FNLG"
SUBJECT_LABEL = b"fn/subject/v1"
OBLIGATION_LABEL = b"fn/obligation/v1"
# The store's digest and the content identities' algorithm octet
# (books/identity.lisp): BLAKE3 (books/crypto-attach.lisp, through
# tools/blake3_ref.py) and 2 in format 10.
IDENTITY_ALGORITHM = 2


def digest(octets):
    return blake3_ref.blake3(octets)


def cbor_head(major, n):
    if n < 24:
        return bytes([(major << 5) | n])
    if n < 256:
        return bytes([(major << 5) | 24, n])
    if n < 65536:
        return bytes([(major << 5) | 25]) + struct.pack(">H", n)
    if n < 2 ** 32:
        return bytes([(major << 5) | 26]) + struct.pack(">I", n)
    return bytes([(major << 5) | 27]) + struct.pack(">Q", n)


def cbor_items(b):
    """The record's top-level items: ('u', n) or ('b', bytes), in order."""
    out, p = [], 0
    while p < len(b):
        ib = b[p]; major, info = ib >> 5, ib & 31; p += 1
        if info < 24:
            n = info
        elif info == 24:
            n = b[p]; p += 1
        elif info == 25:
            n = struct.unpack(">H", b[p:p + 2])[0]; p += 2
        elif info == 26:
            n = struct.unpack(">I", b[p:p + 4])[0]; p += 4
        elif info == 27:
            n = struct.unpack(">Q", b[p:p + 8])[0]; p += 8
        else:
            raise ValueError("indefinite item")
        if major == 0:
            out.append(("u", n))
        elif major == 2:
            out.append(("b", b[p:p + n])); p += n
        else:
            raise ValueError("major type %d" % major)
    return out


def encode(items):
    return b"".join(cbor_head(0, v) if t == "u" else cbor_head(2, len(v)) + v for t, v in items)


def subject_of(payload):
    d = digest(SUBJECT_LABEL + b"\x00" + struct.pack(">I", len(payload)) + payload)
    return SUBJECT_LABEL + b"\x00\x01" + bytes([IDENTITY_ALGORITHM]) + d


def obligation_of(msgid, subject):
    d = digest(OBLIGATION_LABEL + b"\x00" + struct.pack(">I", len(msgid)) + msgid
                       + struct.pack(">I", len(subject)) + subject)
    return OBLIGATION_LABEL + b"\x00\x01" + bytes([IDENTITY_ALGORITHM]) + d


def genesis_trailer(path):
    """The chain value segment 1 starts from: the genesis frame's trailer,
    after checking it is one kind-3 FNLG frame from the zero chain."""
    d = open(path, "rb").read()
    if d[:4] != MAGIC or d[4] != 1 or d[5] != 3:
        raise SystemExit("seed genesis: not a kind-3 FNLG frame")
    n = struct.unpack(">I", d[6:10])[0]
    if len(d) != 10 + n + 32 or d[10:42] != bytes(32):
        raise SystemExit("seed genesis: not one frame from the zero chain")
    if digest(d[:10 + n]) != d[10 + n:]:
        raise SystemExit("seed genesis: the trailer does not verify")
    return d[10 + n:]


def read_entries(path, genesis):
    d = open(path, "rb").read()
    pos, prev, records = 0, genesis, []
    while pos + 10 <= len(d) and d[pos:pos + 4] == MAGIC:
        kind = d[pos + 5]
        n = struct.unpack(">I", d[pos + 6:pos + 10])[0]
        prot = d[pos:pos + 10 + n]
        trailer = d[pos + 10 + n:pos + 42 + n]
        if digest(prot) != trailer or prot[10:42] != prev:
            raise SystemExit("seed log: entry at %d does not verify" % pos)
        body = prot[42:]
        if kind == 1:
            records.append(body)
        elif kind == 2:
            q = 0
            while q < len(body):
                m = struct.unpack(">I", body[q:q + 4])[0]
                records.append(body[q + 4:q + 4 + m]); q += 4 + m
        else:
            raise SystemExit("seed log: kind %d" % kind)
        prev = trailer
        end = pos + 42 + n
        pos = end + ((-end) % UNIT)
    return records


class Template:
    """An article record: its items and where the fields sit."""
    def __init__(self, raw):
        it = cbor_items(raw)
        if not (it[0] == ("b", b"fn-r") and it[1] == ("u", 1)):
            raise ValueError("not a version-1 article record")
        self.items = it
        self.seq, self.txid, self.gen = it[2][1], it[3][1], it[4][1]
        self.msgid = it[5][1]
        self.payload = it[6][1]
        ng = it[7][1]
        self.groups_end = 8 + ng
        self.obligation = it[self.groups_end][1]
        self.subject = it[self.groups_end + 1][1]
        if encode(it) != raw:
            raise ValueError("record is not in the shortest encoding")
        if self.payload.count(self.msgid) != 1:
            raise ValueError("payload does not name its Message-ID once")

    def check(self):
        s = subject_of(self.payload)
        o = obligation_of(self.msgid, s)
        return s.hex().encode() == self.subject and o.hex().encode() == self.obligation

    def make(self, i):
        body = self.msgid[1:-1]
        at = body.index(b"@")
        local = ("s%d" % i).encode()
        width = at
        if len(local) > width:
            raise SystemExit("record %d: Message-ID local part wider than the template's" % i)
        msgid = b"<" + local.rjust(width, b"0") + body[at:] + b">"
        payload = self.payload.replace(self.msgid, msgid)
        s = subject_of(payload)
        o = obligation_of(msgid, s)
        it = list(self.items)
        it[2], it[3], it[4] = ("u", i), ("u", i + 1), ("u", i + 1)
        it[5], it[6] = ("b", msgid), ("b", payload)
        it[self.groups_end] = ("b", o.hex().encode())
        it[self.groups_end + 1] = ("b", s.hex().encode())
        return encode(it)


def frame(prev, chunk):
    kind = 1 if len(chunk) == 1 else 2
    body = chunk[0] if kind == 1 else b"".join(struct.pack(">I", len(r)) + r for r in chunk)
    payload = prev + body
    prot = MAGIC + bytes([1, kind]) + struct.pack(">I", len(payload)) + payload
    trailer = digest(prot)
    f = prot + trailer
    return f + bytes((-len(f)) % UNIT), trailer


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("seed"); ap.add_argument("out"); ap.add_argument("n", type=int)
    ap.add_argument("--batch", type=int, default=1)
    ap.add_argument("--check-only", action="store_true")
    a = ap.parse_args()
    seg = os.path.join(a.seed, "journal", "000001.log")
    gen = os.path.join(a.seed, "journal", "000000.log")
    if os.path.exists(os.path.join(a.seed, "store-checkpoint.fnsc")) or \
       sorted(os.listdir(os.path.join(a.seed, "journal"))) != ["000000.log", "000001.log"]:
        raise SystemExit("seed: expected the genesis and one segment (journal/000000.log, "
                         "000001.log; format 10) and no checkpoint; found journal/ %s%s (a seed "
                         "whose owner checkpointed has rotated its log: initialize it with "
                         "--max-open-suffix above its record count)"
                         % (sorted(os.listdir(os.path.join(a.seed, "journal"))),
                            " and store-checkpoint.fnsc" if os.path.exists(
                                os.path.join(a.seed, "store-checkpoint.fnsc")) else ""))
    genesis = genesis_trailer(gen)
    raws = read_entries(seg, genesis)
    temps = [Template(r) for r in raws]
    for k, t in enumerate(temps):
        if (t.seq, t.txid, t.gen) != (k, k + 1, k + 1):
            raise SystemExit("seed record %d: sequence/txid %s not the renumbering's" % (k, (t.seq, t.txid, t.gen)))
        if not t.check():
            raise SystemExit("seed record %d: identities do not recompute" % k)
        if t.make(k) == raws[k]:
            pass
    print("seed: %d records verified, identities recompute" % len(temps))
    if a.check_only:
        return
    if os.path.exists(a.out):
        raise SystemExit("out exists")
    shutil.copytree(a.seed, a.out, ignore=shutil.ignore_patterns("journal", "writer.lock"))
    os.mkdir(os.path.join(a.out, "journal"), 0o700)
    shutil.copy2(gen, os.path.join(a.out, "journal", "000000.log"))
    prev, written = genesis, 0
    path = os.path.join(a.out, "journal", "000001.log")
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as f:
        i = 0
        while i < a.n:
            chunk = [temps[j % len(temps)].make(j) for j in range(i, min(a.n, i + a.batch))]
            e, prev = frame(prev, chunk)
            f.write(e); written += len(e); i += len(chunk)
        tail = max(4 * 1024 * 1024, written + UNIT) - written
        f.write(bytes(tail + ((-(written + tail)) % (1024 * 1024))))
        f.flush(); os.fsync(f.fileno())
    print("wrote %d records, %d octets of entries" % (a.n, written))


if __name__ == "__main__":
    main()
