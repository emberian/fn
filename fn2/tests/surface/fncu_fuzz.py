"""F for consumer: seeded `fncu` v1 cursor mutation through the image's `consumer-inspect` (H7g).

    python3 -m fn2.tests.surface.fncu_fuzz --target fn1|fn2|fake --seeds A..B --out DIR [--seconds S]
        [--plant P]

RELEASE-PLAN §2.2's F row for the consumer: "FNCT frame and `fncu` fuzz (magic, kind, payload limit,
BLAKE3 trailer)". This driver covers the `fncu` half; the FNCT frame half needs a control-socket client and
is still owed. The oracle is specs/consumer-progress.md:45-50 and 730-740: `fncu` (4 octets), version 1
(1 octet), five length-prefixed IDs (history, incarnation, consumer, principal, query; 1..64 octets each),
then four big-endian u32 (query version, view version, registration epoch, scanned position); at most 346
octets, checked before decoding. The image's developer verb `consumer-inspect FILE` prints
`fn-consumer-inspect-v1 history=HEX ... position=N ...` (exit 0) or
`fn-consumer-inspect-refused-v1 WORD` (exit 1), where WORD is `limit` for an overbound file, `version` for
another version, `grammar` for any other malformed encoding (the carried tests.test_native_consumer_inspect
names those three). Two pins the spec leaves open, read from fn1's decoder (books/consumer-position.lisp
fn-cp-cursor-decode, fn-cp-cursorp) and recorded in fn2/docs/h-harness.md "Spec pins": P-FNCU-HEADER, any
first five octets other than `fncu` 01 (an empty or short file included) is `version`; P-FNCU-EPOCH, the
registration epoch is positive, so an epoch of 0 is `grammar`.

Each case is a random well-formed cursor with at most one mutation: none (every field is compared
exactly); truncated; trailing octets; an empty ID; an ID length past 64 (limit when the file then
exceeds 346 octets, else grammar); a length prefix past the end; another magic; another version; an
overbound file of any octets; an empty file. A disagreement is a row in DIR/findings.jsonl (exit 1).
`--target fake` runs an independent decoder (mutation controls: `--plant accept-trailing`,
`version-as-grammar`, `swap-epoch-position`).
"""
import argparse
import json
import os
from pathlib import Path
import random
import re
import struct
import subprocess
import sys
import tempfile
import time

PLANTS = ('accept-trailing', 'version-as-grammar', 'swap-epoch-position')
IDS = ('history', 'incarnation', 'consumer', 'principal', 'query')
NUMBERS = ('query-version', 'view-version', 'registration-epoch', 'position')
MAX = 346
CASES = ('none', 'none', 'none', 'truncated', 'trailing', 'empty-id', 'long-id', 'length-past-end', 'magic',
         'version', 'overbound', 'empty', 'epoch-zero')


def encode(fields, version=1, magic=b'fncu'):
    out = magic + bytes([version])
    for name in IDS:
        out += bytes([len(fields[name])]) + fields[name]
    return out + b''.join(struct.pack('>I', fields[n]) for n in NUMBERS)


def cursor(rng):
    fields = {n: bytes(rng.randrange(256) for _ in range(rng.choice([1, 2, 8, 32, 64, rng.randrange(1, 65)])))
              for n in IDS}
    fields.update({n: rng.choice([0, 1, 4294967295, rng.randrange(1 << 32)]) for n in NUMBERS})
    fields['registration-epoch'] = fields['registration-epoch'] or 1     # positive (P-FNCU-EPOCH)
    return fields


def case(rng):
    """(mutation, expected: dict of fields or a refusal word, octets)."""
    fields = cursor(rng)
    data = encode(fields)
    kind = rng.choice(CASES)
    if kind == 'none':
        return kind, fields, data
    if kind == 'truncated':
        return kind, 'grammar', data[:-rng.randrange(1, len(data) - 5)]
    if kind == 'trailing':
        extra = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 4)))
        return kind, ('limit' if len(data) + len(extra) > MAX else 'grammar'), data + extra
    if kind == 'empty-id':
        name = rng.choice(IDS)
        fields[name] = b''
        return kind, 'grammar', encode(fields)
    if kind == 'long-id':
        name = rng.choice(IDS)
        fields[name] = bytes(rng.randrange(256) for _ in range(rng.randrange(65, 256)))
        data = encode(fields)
        return kind, ('limit' if len(data) > MAX else 'grammar'), data
    if kind == 'length-past-end':
        # The query ID's prefix claims one octet more than its ID and the 16 number octets hold.
        fields['query'] = fields['query'][:rng.randrange(1, 48)]
        data = encode(fields)
        prefix_at = len(data) - 16 - len(fields['query']) - 1
        return kind, 'grammar', data[:prefix_at] + bytes([len(fields['query']) + 17]) + data[prefix_at + 1:]
    if kind == 'magic':
        magic = rng.choice([b'fncv', b'FNCU', b'\x00ncu', b'fnc'])
        return kind, 'version', encode(fields, magic=magic)      # P-FNCU-HEADER
    if kind == 'epoch-zero':
        fields['registration-epoch'] = 0
        return kind, 'grammar', encode(fields)                  # P-FNCU-EPOCH
    if kind == 'version':
        return kind, 'version', encode(fields, version=rng.choice([0, 2, 3, 255]))
    if kind == 'overbound':
        return kind, 'limit', bytes(rng.randrange(256) for _ in range(rng.randrange(MAX + 1, 600)))
    if kind == 'empty':
        return kind, 'version', b''                             # P-FNCU-HEADER
    raise ValueError(kind)


def fake_inspect(data, plant=None):
    if len(data) > MAX:
        return 1, 'fn-consumer-inspect-refused-v1 limit'
    if data[:4] != b'fncu' or len(data) < 5 or data[4] != 1:
        return 1, 'fn-consumer-inspect-refused-v1 ' + ('grammar' if plant == 'version-as-grammar' else 'version')
    at, ids = 5, []
    for _ in IDS:
        if at >= len(data) or not 1 <= data[at] <= 64 or at + 1 + data[at] > len(data):
            return 1, 'fn-consumer-inspect-refused-v1 grammar'
        ids.append(data[at + 1:at + 1 + data[at]])
        at += 1 + data[at]
    if len(data) - at != 16 and not (plant == 'accept-trailing' and len(data) - at > 16):
        return 1, 'fn-consumer-inspect-refused-v1 grammar'
    numbers = list(struct.unpack('>4I', data[at:at + 16]))
    if numbers[2] == 0:
        return 1, 'fn-consumer-inspect-refused-v1 grammar'
    if plant == 'swap-epoch-position':
        numbers[2], numbers[3] = numbers[3], numbers[2]
    return 0, render(dict(zip(IDS, ids)) | dict(zip(NUMBERS, numbers)))


def render(fields):
    return ('fn-consumer-inspect-v1 ' + ' '.join(f'{n}={fields[n].hex()}' for n in IDS) + ' ' +
            ' '.join(f'{n}={fields[n]}' for n in NUMBERS) +
            ' currentness=unverified acceptance=unverified processing=unverified')


def judge(expected, code, text):
    text = text.strip()
    if code < 0 or re.search(r'debugger invoked|Unhandled [A-Z-]+|Backtrace for', text):
        return f'crash (exit {code})'
    if isinstance(expected, dict):
        if code != 0:
            return f'expected the cursor decoded, got exit {code}: {text[:120]}'
        lines = [l for l in text.splitlines() if l.startswith('fn-consumer-inspect-v1 ')]
        if lines != [render(expected)]:
            return 'decoded fields differ: ' + (lines[0][:300] if lines else text[:300])
        return None
    want = 'fn-consumer-inspect-refused-v1 ' + expected
    if code != 1 or want not in text.splitlines():
        return f'expected exit 1 and `{want}`, got exit {code}: {text[:160]}'
    return None


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--target', choices=('fn1', 'fn2', 'fake'), required=True)
    p.add_argument('--seeds', default='0..999')
    p.add_argument('--seconds', type=float, default=float('inf'))
    p.add_argument('--plant', choices=PLANTS)
    p.add_argument('--image', type=Path)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--with-fnct', action='store_true',
                   help='then the FNCT frame half (fnct_fuzz) on the remaining time, into OUT/fnct')
    args = p.parse_args(argv)
    if args.plant and args.target != 'fake':
        p.error('plants require --target fake')
    if args.with_fnct:
        began, seconds = time.monotonic(), args.seconds
        rest = [a for a in (argv if argv is not None else sys.argv[1:]) if a != '--with-fnct']
        if seconds != float('inf'):
            i = rest.index('--seconds')
            rest[i + 1] = str(seconds / 2)
        code = main(rest)
        left = seconds - (time.monotonic() - began) if seconds != float('inf') else seconds
        from fn2.tests.surface import fnct_fuzz
        fnct = ['--target', args.target, '--out', str(args.out / 'fnct')] + \
            (['--seconds', str(max(1.0, left))] if left != float('inf') else [])
        return max(code, fnct_fuzz.main(fnct))
    image = args.image or Path(os.environ.get('FN_NATIVE_DEVELOPER_HOST', '/nonexistent'))
    if args.target != 'fake' and not image.is_file():
        p.error('a live target needs --image or FN_NATIVE_DEVELOPER_HOST (consumer-inspect is a developer verb)')
    start, end = map(int, args.seeds.split('..'))
    args.out.mkdir(parents=True, exist_ok=True)
    findings, counts, run, deadline = [], {}, 0, time.monotonic() + args.seconds
    with tempfile.TemporaryDirectory(prefix='fn2-fncu-fuzz-') as directory:
        path = Path(directory) / 'cursor.fncu'
        for seed in range(start, end + 1):
            if time.monotonic() >= deadline:
                break
            kind, expected, data = case(random.Random(seed))
            counts[kind] = counts.get(kind, 0) + 1
            if args.target == 'fake':
                code, text = fake_inspect(data, args.plant)
            else:
                path.write_bytes(data)
                result = subprocess.run([str(image), '--fn', 'consumer-inspect', str(path)], capture_output=True,
                                        timeout=60, env=dict(os.environ, ACL2_CUSTOMIZATION='NONE'))
                code, text = result.returncode, (result.stdout + result.stderr).decode('utf-8', 'replace')
            run += 1
            problem = judge(expected, code, text)
            if problem:
                findings.append(dict(seed=seed, mutation=kind, problem=problem, octets=data.hex(),
                                     expected=expected if isinstance(expected, str) else 'decoded'))
    (args.out / 'findings.jsonl').write_text(''.join(json.dumps(f) + '\n' for f in findings))
    summary = dict(target=args.target, plant=args.plant, seeds=args.seeds, cases=run, by_mutation=counts,
                   findings=len(findings))
    (args.out / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    print(json.dumps(summary))
    return 1 if findings else 0


if __name__ == '__main__':
    sys.exit(main())
