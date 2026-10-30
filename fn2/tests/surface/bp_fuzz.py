"""F for bp: seeded BPv7 bundle mutation through the DTN image's `bp decode` (H7g).

    python3 -m fn2.tests.surface.bp_fuzz --target fn1|fn2|fake --seeds A..B --out DIR [--seconds S] [--plant P]

RELEASE-PLAN §2.2's F row for BP/TCPCL: "TCPCL segment and BPv7 CBOR fuzz". This driver covers the BPv7
half (the TCPCL segment half needs a TCPCL peer and is still owed). The subject is `fn --fn bp decode FILE
NODE-ID LIFETIME CRC HOP MRU WALL WALL-ERROR ADU-OUT` (host/native/bp.lisp): one line `BP decode
outcome=accepted|refused|uncertain reason=WORD adu=N`, exit 0 exactly when accepted, and the ADU written
when accepted. The seeds start from the two captured bundles of tests/bp-dtn7/golden (the dtn7-rs bundle
carries no CRC; fn's carries CRC32C on every block) at their own DTN time, and apply one mutation whose
outcome RFC 9171 decides:

  none            accepted; the ADU is the captured payload
  payload-flip    dtn7-rs bundle, octets of the payload's data changed in place: accepted, and the ADU is
                  exactly the changed octets (no CRC: 4.2.1 leaves integrity to the CRC, which is absent)
  crc-flip        fn's bundle, one bit changed inside any block: refused (CRC32C, 4.2.1, detects every
                  single-bit error; a change that breaks the CBOR first is refused as well)
  truncated       octets cut from the end: refused        trailing   octets after the bundle: refused
  expired         dtn7-rs bundle (no age block), the clock past creation + lifetime: refused,
                  reason `lifetime-expired`
  age-expired     fn's bundle with its Bundle Age block re-encoded past the lifetime (CRC recomputed):
                  refused, `lifetime-expired`. A bundle with an age block is judged by its age, not the
                  clock (RFC 9171 5.5; fn prefers the age path whenever the block is present,
                  books/clock.lisp fn-clock-expiry-decision), so the clock alone never expires fn's bundle
  garbage         random octets: refused

Every reply must be one such line, never a fault, signal or backtrace. A disagreement is a row in
DIR/findings.jsonl (exit 1). `--target fake` runs a small independent BPv7 reader (a CBOR item walker,
CRC32C, the lifetime check; mutation controls `--plant accept-crc-flip`, `adu-unflipped`, `accept-expired`).
"""
import argparse
import json
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[3]
GOLDEN = ROOT / 'tests' / 'bp-dtn7' / 'golden'
PLANTS = ('accept-crc-flip', 'adu-unflipped', 'accept-expired')
BUNDLES = {
    # name: (file, node id, creation DTN ms, payload)
    'dtn7': ('dtn7-rs-0.21.0-authored.bundle', 'dtn://fn-b/', 843272141627, b'dtn7 -> fn, decoded as a bundle\n'),
    'fn': ('fn-authored-accepted-by-dtn7-rs-0.21.0.bundle', 'dtn://dtn7x/', 843272138572,
           b'fn -> dtn7, a bundle fn authored\n'),
}
LIFETIME = 3600000
CASES = ('none', 'payload-flip', 'payload-flip', 'crc-flip', 'crc-flip', 'truncated', 'trailing', 'expired',
         'age-expired', 'garbage')
# fn's bundle-age block (RFC 9171 4.4.2), age 0, CRC32C: 86 07 03 00 02 41 00 44 CRC.
AGE_BLOCK_HEAD = bytes.fromhex('8607030002')


def case(rng):
    """(mutation, bundle name, expected: ('accepted', adu) or ('refused', reason or None), octets, wall)."""
    kind = rng.choice(CASES)
    name = {'payload-flip': 'dtn7', 'crc-flip': 'fn', 'expired': 'dtn7', 'age-expired': 'fn'}.get(kind) or \
        rng.choice(sorted(BUNDLES))
    file, node, created, payload = BUNDLES[name]
    data = bytearray((GOLDEN / file).read_bytes())
    wall = created + rng.randrange(1, 60000)
    if kind == 'none':
        return kind, name, ('accepted', payload), bytes(data), wall
    if kind == 'payload-flip':
        at = data.find(payload)
        adu = bytearray(payload)
        for _ in range(rng.randrange(1, 4)):
            i = rng.randrange(len(adu))
            adu[i] ^= 1 << rng.randrange(8)
        data[at:at + len(adu)] = adu
        return kind, name, ('accepted', bytes(adu)), bytes(data), wall
    if kind == 'crc-flip':
        i = rng.randrange(1, len(data) - 1)
        data[i] ^= 1 << rng.randrange(8)
        return kind, name, ('refused', None), bytes(data), wall
    if kind == 'truncated':
        return kind, name, ('refused', None), bytes(data[:-rng.randrange(1, len(data))]), wall
    if kind == 'trailing':
        return kind, name, ('refused', None), bytes(data) + bytes(rng.randrange(256) for _ in range(rng.randrange(1, 5))), wall
    if kind == 'expired':
        return kind, name, ('refused', 'lifetime-expired'), bytes(data), created + LIFETIME + rng.randrange(1, 10 ** 6)
    if kind == 'age-expired':
        # The age block re-encoded with an age past the lifetime, its CRC32C recomputed (fn decides expiry by
        # the age whenever the block is present: books/clock.lisp fn-clock-expiry-decision, RFC 9171 5.5).
        at = data.find(AGE_BLOCK_HEAD)
        end = at + len(AGE_BLOCK_HEAD) + 2 + 5
        age = LIFETIME + rng.randrange(1, 10 ** 6)
        body = AGE_BLOCK_HEAD + b'\x45' + b'\x1a' + age.to_bytes(4, 'big') + b'\x44'
        block = body + _crc32c(body + b'\x00' * 4).to_bytes(4, 'big')
        return kind, name, ('refused', 'lifetime-expired'), bytes(data[:at]) + block + bytes(data[end:]), wall
    if kind == 'garbage':
        return kind, name, ('refused', None), bytes(rng.randrange(256) for _ in range(rng.randrange(0, 200))), wall
    raise ValueError(kind)


# -- the fake's independent reader ---------------------------------------------------------------------

def _crc32c(data):
    crc = 0xFFFFFFFF
    for b in data:
        crc ^= b
        for _ in range(8):
            crc = (crc >> 1) ^ (0x82F63B78 if crc & 1 else 0)
    return crc ^ 0xFFFFFFFF


def _crc16_x25(data):
    crc = 0xFFFF
    for b in data:
        crc ^= b
        for _ in range(8):
            crc = (crc >> 1) ^ (0x8408 if crc & 1 else 0)
    return crc ^ 0xFFFF


def _head(data, at):
    """(major, value, start of content) of the CBOR item head at AT; value None for indefinite."""
    if at >= len(data):
        raise ValueError('truncated')
    major, info = data[at] >> 5, data[at] & 31
    if info < 24:
        return major, info, at + 1
    if info == 31:
        return major, None, at + 1
    width = {24: 1, 25: 2, 26: 4, 27: 8}.get(info)
    if width is None or at + 1 + width > len(data):
        raise ValueError('truncated')
    return major, int.from_bytes(data[at + 1:at + 1 + width], 'big'), at + 1 + width


def _skip(data, at):
    major, value, at = _head(data, at)
    if major in (0, 1, 7):
        return at
    if major in (2, 3):
        if value is None or at + value > len(data):
            raise ValueError('truncated')
        return at + value
    if major in (4, 5):
        if value is None:
            raise ValueError('indefinite item inside a block')
        for _ in range(value * (2 if major == 5 else 1)):
            at = _skip(data, at)
        return at
    if major == 6:
        return _skip(data, at)
    raise ValueError('major')


def fake_decode(data, wall, plant=None):
    """(outcome, reason, adu) of an independent small BPv7 reader."""
    try:
        if not data or data[0] != 0x9F:
            return 'refused', 'not-a-bundle', b''
        at, blocks = 1, []
        while True:
            if at >= len(data):
                return 'refused', 'truncated', b''
            if data[at] == 0xFF:
                at += 1
                break
            end = _skip(data, at)
            blocks.append((at, end))
            at = end
        if at != len(data):
            return 'refused', 'trailing-octets', b''
        adu, created, lifetime, age = None, None, None, None
        for index, (start, end) in enumerate(blocks):
            block = data[start:end]
            major, count, pos = _head(block, 0)
            items = []
            for _ in range(count or 0):
                nxt = _skip(block, pos)
                items.append((pos, nxt))
                pos = nxt
            # RFC 9171 4.3.1: primary [version, flags, CRC type, destination, source, report-to,
            # [creation time, sequence], lifetime, ...]; 4.3.2: canonical [type, number, flags, CRC type, data, ...].
            crc_type = _head(block, items[2 if index == 0 else 3][0])[1] if items else 0
            base = 5 if index else (10 if _head(block, items[1][0])[1] & 1 else 8)   # 4.3.1: fragment fields
            if crc_type not in (0, 1, 2) or len(items) != base + (crc_type != 0):
                return 'refused', 'crc-type', b''
            if crc_type and plant != 'accept-crc-flip':
                cs, ce = items[-1]
                _, length, vstart = _head(block, cs)
                stored = block[vstart:vstart + length]
                zeroed = block[:vstart] + b'\x00' * length + block[vstart + length:]
                value = _crc32c(zeroed).to_bytes(4, 'big') if crc_type == 2 else _crc16_x25(zeroed).to_bytes(2, 'big')
                if value != stored:
                    return 'refused', 'crc', b''
            if index == 0:
                _, _, first = _head(block, items[6][0])       # the creation timestamp array's first element
                _, created, _ = _head(block, first)
                _, lifetime, _ = _head(block, items[7][0])
            else:
                _, kind, _ = _head(block, items[0][0])
                _, length, vstart = _head(block, items[4][0])
                if kind == 1:
                    adu = bytes(block[vstart:vstart + length])
                elif kind == 7:
                    _, age, _ = _head(block[vstart:vstart + length], 0)
        if created is None or adu is None:
            return 'refused', 'grammar', b''
        expired = age > lifetime if age is not None else wall > created + lifetime    # RFC 9171 5.5
        if expired and plant != 'accept-expired':
            return 'refused', 'lifetime-expired', b''
        return 'accepted', 'nil', adu
    except (ValueError, IndexError):
        return 'refused', 'grammar', b''


def judge(expected, reply, adu):
    code, text = reply['exit'], reply['text']
    if code < 0 or re.search(r'debugger invoked|Unhandled [A-Z-]+|Backtrace for', text):
        return f'crash (exit {code})'
    lines = re.findall(r'^BP decode outcome=(\S+) reason=(\S+) adu=(\d+)$', text, re.M)
    if len(lines) != 1:
        return 'not exactly one `BP decode` line: ' + text[-200:]
    outcome, reason, length = lines[0]
    if (code == 0) != (outcome == 'accepted'):
        return f'exit {code} with outcome {outcome}'
    if outcome != expected[0]:
        return f'expected {expected[0]}, got {outcome} reason={reason}'
    if outcome == 'accepted':
        if adu != expected[1] or int(length) != len(expected[1]):
            return f'ADU differs: {adu!r}'
    elif expected[1] and reason != expected[1]:
        return f'expected reason {expected[1]}, got {reason}'
    return None


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--target', choices=('fn1', 'fn2', 'fake'), required=True)
    p.add_argument('--seeds', default='0..999')
    p.add_argument('--seconds', type=float, default=float('inf'))
    p.add_argument('--plant', choices=PLANTS)
    p.add_argument('--image', type=Path)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--with-tcpcl', action='store_true',
                   help='then the TCPCL session half (tcpcl_fuzz) on the remaining time, into OUT/tcpcl')
    args = p.parse_args(argv)
    if args.plant and args.target != 'fake':
        p.error('plants require --target fake')
    if args.with_tcpcl:
        began, seconds = time.monotonic(), args.seconds
        rest = [a for a in (argv if argv is not None else sys.argv[1:]) if a != '--with-tcpcl']
        if seconds != float('inf'):
            rest[rest.index('--seconds') + 1] = str(seconds / 2)
        code = main(rest)
        left = seconds - (time.monotonic() - began) if seconds != float('inf') else seconds
        from fn2.tests.surface import tcpcl_fuzz
        session = ['--target', args.target, '--out', str(args.out / 'tcpcl')] + \
            (['--seconds', str(max(1.0, left))] if left != float('inf') else []) + \
            (['--image', str(args.image)] if args.image else [])
        return max(code, tcpcl_fuzz.main(session))
    image = args.image or Path(os.environ.get('FN_NATIVE_DTN_HOST', str(ROOT / 'build' / 'fn-host-dtn')))
    if args.target != 'fake' and not image.is_file():
        p.error('a live target needs --image or FN_NATIVE_DTN_HOST (bp decode)')
    start, end = map(int, args.seeds.split('..'))
    args.out.mkdir(parents=True, exist_ok=True)
    findings, counts, run, deadline = [], {}, 0, time.monotonic() + args.seconds
    with tempfile.TemporaryDirectory(prefix='fn2-bp-fuzz-') as directory:
        path, adu_path = Path(directory) / 'bundle', Path(directory) / 'adu'
        for seed in range(start, end + 1):
            if time.monotonic() >= deadline:
                break
            kind, name, expected, data, wall = case(random.Random(seed))
            counts[kind] = counts.get(kind, 0) + 1
            if adu_path.exists():
                adu_path.unlink()
            if args.target == 'fake':
                outcome, reason, adu = fake_decode(data, wall, args.plant)
                if args.plant == 'adu-unflipped' and outcome == 'accepted':
                    adu = BUNDLES[name][3]
                reply = dict(exit=0 if outcome == 'accepted' else 1,
                             text=f'BP decode outcome={outcome} reason={reason} adu={len(adu)}\n')
            else:
                path.write_bytes(data)
                result = subprocess.run([str(image), '--fn', 'bp', 'decode', str(path), BUNDLES[name][1],
                                         str(LIFETIME), '2', '32', '1048576', str(wall), '0', str(adu_path)],
                                        capture_output=True, timeout=60)
                reply = dict(exit=result.returncode, text=(result.stdout + result.stderr).decode('utf-8', 'replace'))
                adu = adu_path.read_bytes() if adu_path.exists() else b''
            run += 1
            problem = judge(expected, reply, adu)
            if problem:
                findings.append(dict(seed=seed, mutation=kind, bundle=name, problem=problem, reply=reply,
                                     octets=data.hex(), wall=wall))
    (args.out / 'findings.jsonl').write_text(''.join(json.dumps(f) + '\n' for f in findings))
    summary = dict(target=args.target, plant=args.plant, seeds=args.seeds, cases=run, by_mutation=counts,
                   findings=len(findings))
    (args.out / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    print(json.dumps(summary))
    return 1 if findings else 0


if __name__ == '__main__':
    sys.exit(main())
