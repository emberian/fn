"""F for bp, the TCPCL half: seeded RFC 9174 session mutation against the DTN image's `bp receive` (H7e).

    python3 -m fn2.tests.surface.tcpcl_fuzz --target fn1|fn2|fake --seeds A..B --out DIR [--seconds S] [--plant P]

RELEASE-PLAN §2.2's F row for BP/TCPCL: "TCPCL segment and BPv7 CBOR fuzz" (bp_fuzz is the CBOR half). Each case
starts one `bp receive PORT 1 JOURNAL dtn://fn-b/ ...` (host/native/bp.lisp: one session, then exit), and
plays one TCPCL v4 session at it carrying the captured dtn7-rs bundle (tests/bp-dtn7/golden), with at most
one mutation whose outcome RFC 9174 decides. The encoding is the carried peer's (tests/test_bp_node_native.py
TcpclPeer): contact header `dtn!` 04 00; SESS_INIT 07, keepalive u16, segment MRU u64, transfer MRU u64,
node-ID length u16, node ID, extension length u32; XFER_SEGMENT 01, flags (START 2, END 1), transfer ID u64,
on START an extension length u32, data length u64, data; SESS_TERM 05.

  none            one START|END segment: the receiver accepts the bundle, and its journalled ADU is the
                  payload dtn7-rs sent
  split           the bundle in 2-4 segments (START, ..., END), one transfer: accepted, same ADU (5.2.2)
  magic, version  another contact magic, or version 3 or 5: no bundle accepted (4.2, 4.3)
  no-start        the first segment without START: no bundle accepted (5.2.2, a protocol violation)
  short-segment   a segment whose declared length exceeds the octets sent before the client closes: none
  bundle-flip     the segment carries the bundle with its first octet changed: none (bp decode refuses)
  huge-length     a data length of 2**62: none, and the receiver neither waits for it nor allocates it

Every case: the receiver exits within its deadline, with no signal and no backtrace. A disagreement is a row
in DIR/findings.jsonl (exit 1). `--target fake` runs a small independent RFC 9174 receiver over
bp_fuzz.fake_decode (mutation controls: `--plant accept-bad-magic`, `accept-no-start`).
"""
import argparse
import json
import os
from pathlib import Path
import random
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time

from fn2.tests.surface.bp_fuzz import BUNDLES, GOLDEN, fake_decode

PLANTS = ('accept-bad-magic', 'accept-no-start')
CASES = ('none', 'split', 'magic', 'version', 'no-start', 'short-segment', 'bundle-flip', 'huge-length')
BUNDLE = (GOLDEN / BUNDLES['dtn7'][0]).read_bytes()
PAYLOAD = BUNDLES['dtn7'][3]
WALL = BUNDLES['dtn7'][2] + 100
DEADLINE = 30.0


PEER = 'dtn://dtn7x/'      # the captured bundle's source and previous node


def sess_init(node_id=PEER.encode()):
    return (b'\x07\x00\x01' + (1 << 16).to_bytes(8, 'big') + (1 << 20).to_bytes(8, 'big')
            + len(node_id).to_bytes(2, 'big') + node_id + b'\x00\x00\x00\x00')


def segment(xfer, data, *, start, end, declared=None):
    flags = (2 if start else 0) | (1 if end else 0)
    return (b'\x01' + bytes([flags]) + xfer.to_bytes(8, 'big') + (b'\x00\x00\x00\x00' if start else b'')
            + (len(data) if declared is None else declared).to_bytes(8, 'big') + data)


def plan(rng):
    """(mutation, accepted?, contact, segments octets, close early?)."""
    kind = rng.choice(CASES)
    contact, bundle, segments = b'dtn!\x04\x00', BUNDLE, None
    if kind == 'magic':
        contact = rng.choice([b'dtn?\x04\x00', b'DTN!\x04\x00', b'dtn\x00\x04\x00'])
    elif kind == 'version':
        contact = b'dtn!' + bytes([rng.choice([3, 5])]) + b'\x00'
    elif kind == 'bundle-flip':
        bundle = bytes([bundle[0] ^ 0x01]) + bundle[1:]
    if kind == 'split':
        cuts = sorted(rng.sample(range(1, len(bundle)), rng.randrange(1, 4)))
        parts = [bundle[a:b] for a, b in zip([0] + cuts, cuts + [len(bundle)])]
        segments = b''.join(segment(1, part, start=i == 0, end=i == len(parts) - 1) for i, part in enumerate(parts))
    elif kind == 'no-start':
        segments = segment(1, bundle, start=False, end=True)
    elif kind == 'short-segment':
        segments = segment(1, bundle[:len(bundle) // 2], start=True, end=True, declared=len(bundle))
    elif kind == 'huge-length':
        segments = segment(1, bundle[:16], start=True, end=True, declared=1 << 62)
    else:
        segments = segment(1, bundle, start=True, end=True)
    return kind, kind in ('none', 'split'), contact, segments


def play(port, contact, segments, timeout=DEADLINE):
    """Run the client side; the receiver's own messages are drained and ignored."""
    with socket.create_connection(('127.0.0.1', port), timeout=timeout) as s:
        s.settimeout(timeout)
        drained = []

        def drain():
            try:
                while True:
                    chunk = s.recv(65536)
                    if not chunk:
                        return
                    drained.append(chunk)
            except OSError:
                return
        reader = threading.Thread(target=drain, daemon=True)
        try:
            s.sendall(contact)
            reader.start()
            time.sleep(0.2)
            s.sendall(sess_init())
            time.sleep(0.2)
            s.sendall(segments)
            time.sleep(1.0)
            s.sendall(b'\x05\x00\x00')
            s.shutdown(socket.SHUT_WR)
        except OSError:
            pass
        reader.join(timeout)


class FakeReceiver:
    """An independent RFC 9174 receiver over bp_fuzz.fake_decode, for the mutation controls."""

    def __init__(self, plant):
        self.plant = plant

    def run(self, contact, segments):
        if contact[:4] != b'dtn!' and self.plant != 'accept-bad-magic':
            return None
        if contact[4] != 4:
            return None
        data, at, transfer, started = segments, 0, b'', False
        while at < len(data):
            if data[at] != 1:
                return None
            flags = data[at + 1]
            at += 10
            if flags & 2:
                started = True
                at += 4 + int.from_bytes(data[at:at + 4], 'big')
            elif not started and self.plant != 'accept-no-start':
                return None
            length = int.from_bytes(data[at:at + 8], 'big')
            at += 8
            if at + length > len(data):
                return None
            transfer += data[at:at + length]
            at += length
            if flags & 1:
                break
        outcome, _, adu = fake_decode(transfer, WALL)
        return adu if outcome == 'accepted' else None


def free_port():
    with socket.socket() as s:
        s.bind(('127.0.0.1', 0))
        return s.getsockname()[1]


def live_case(image, work, contact, segments):
    """(accepted ADU or None, exit code, receiver output).

    `bp receive` admits a TCPCL principal only against a Store's enrolled BP boundary (host/native/bp.lisp
    fnn-command-bp-receive: "Without it no ingress is admitted and ACL2 refuses every inbound bundle at the
    receive boundary"), so each case makes a Store whose boundary names the captured bundle's peer at the
    receive port, as tests/test_bp_node_native.py does for its nodes."""
    journal, port, store = work / 'journal', free_port(), work / 'store'
    log = work / 'receive.log'
    config = work / 'fn.toml'
    run = lambda *words: subprocess.run([str(image), '--fn', *map(str, words)], capture_output=True, timeout=120)
    steps = [run('store', store, 'init', 'fn.test')]
    config.write_text(f'[store]\npath = "{store}"\n')
    steps.append(run('operator', config, 'policy', 'set', 'path-identity', 'receiver.bp.gate.invalid'))
    steps.append(run('operator', config, 'bp-boundary', 'add', 'sender-boundary', 'sender.bp.gate.invalid', PEER,
                     port, 'fn.test', '32768', '16', 'contact', free_port()))
    for step in steps:
        if step.returncode != 0:
            raise RuntimeError('fixture: ' + (step.stdout + step.stderr)[-300:].decode('latin-1'))
    with log.open('wb') as out:
        receiver = subprocess.Popen([str(image), '--fn', 'bp', 'receive', str(port), '1', str(journal), 'dtn://fn-b/',
                                     '-', '3600000', '2', '32', '1048576', '-', '-', str(WALL), '60000', str(store)],
                                    stdout=out, stderr=subprocess.STDOUT)
    try:
        deadline = time.monotonic() + 30
        while not re.search(rb'BP LISTENING \d+', log.read_bytes()):
            if receiver.poll() is not None or time.monotonic() > deadline:
                raise RuntimeError('bp receive did not listen: ' + log.read_bytes()[-300:].decode('latin-1'))
            time.sleep(0.05)
        play(port, contact, segments)
        try:
            code = receiver.wait(timeout=DEADLINE)
        except subprocess.TimeoutExpired:
            code = None
    finally:
        if receiver.poll() is None:
            receiver.kill()             # this case's own child, by its Popen handle
            receiver.wait(timeout=10)
    text = log.read_bytes().decode('latin-1')
    # `BP accepted xfer=N adu=M path=P`: the accepted bundle journalled at P; its ADU is the payload when the
    # journal record holds the payload's octets and M is their length.
    found = re.search(r'^BP accepted xfer=\d+ adu=(\d+) path=(\S+)$', text, re.M)
    adu = None
    if found:
        record = Path(found.group(2)).read_bytes() if Path(found.group(2)).exists() else b''
        adu = PAYLOAD if int(found.group(1)) == len(PAYLOAD) and PAYLOAD in record else record[:64] or b'?'
    return adu, code, text


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--target', choices=('fn1', 'fn2', 'fake'), required=True)
    p.add_argument('--seeds', default='0..199')
    p.add_argument('--seconds', type=float, default=float('inf'))
    p.add_argument('--plant', choices=PLANTS)
    p.add_argument('--image', type=Path)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args(argv)
    if args.plant and args.target != 'fake':
        p.error('plants require --target fake')
    root = Path(__file__).resolve().parents[3]
    image = args.image or Path(os.environ.get('FN_NATIVE_DTN_HOST', str(root / 'build' / 'fn-host-dtn')))
    if args.target != 'fake' and not image.is_file():
        p.error('a live target needs --image or FN_NATIVE_DTN_HOST (bp receive)')
    start, end = map(int, args.seeds.split('..'))
    args.out.mkdir(parents=True, exist_ok=True)
    findings, counts, run, deadline = [], {}, 0, time.monotonic() + args.seconds
    fake = FakeReceiver(args.plant)
    for seed in range(start, end + 1):
        if time.monotonic() >= deadline:
            break
        kind, accepted, contact, segments = plan(random.Random(seed))
        counts[kind] = counts.get(kind, 0) + 1
        problem, detail = None, ''
        if args.target == 'fake':
            adu = fake.run(contact, segments)
        else:
            work = Path(tempfile.mkdtemp(prefix='fn2-tcpcl-'))
            try:
                adu, code, detail = live_case(image, work, contact, segments)
            finally:
                shutil.rmtree(work, ignore_errors=True)      # this case's own scratch directory
            if code is None:
                problem = f'the receiver did not exit within {DEADLINE} s'
            elif code < 0 or re.search(r'debugger invoked|Unhandled [A-Z-]+|Backtrace for', detail):
                problem = f'receiver crashed (exit {code})'
        run += 1
        if problem is None:
            if accepted and adu != PAYLOAD:
                problem = f'expected the bundle accepted with its payload, got {adu!r}'
            elif not accepted and adu is not None:
                problem = 'a mutated session delivered a bundle'
        if problem:
            findings.append(dict(seed=seed, mutation=kind, problem=problem, output=detail[-600:]))
    (args.out / 'findings.jsonl').write_text(''.join(json.dumps(f) + '\n' for f in findings))
    summary = dict(target=args.target, plant=args.plant, seeds=args.seeds, cases=run, by_mutation=counts,
                   findings=len(findings))
    (args.out / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    print(json.dumps(summary))
    return 1 if findings else 0


if __name__ == '__main__':
    sys.exit(main())
