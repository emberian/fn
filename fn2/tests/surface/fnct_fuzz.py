"""F for consumer, the FNCT half: seeded mutation of captured control frames against a live owner (H7e).

    python3 -m fn2.tests.surface.fnct_fuzz --target fn1|fn2|fake --seeds A..B --out DIR [--seconds S] [--plant P]

RELEASE-PLAN §2.2's F row for the consumer: "FNCT frame and `fncu` fuzz (magic, kind, payload limit, BLAKE3
trailer)". specs/owner.md:58-70: one bounded sealed FNCT request and one bounded sealed reply per AF_UNIX
connection; ACL2 owns the grammar; one ten-second deadline covers a complete incoming frame. A frame is
sealed by a 32-octet digest trailer over its protected prefix (books/frame-trailer.lisp).

The driver starts one owner, then captures the request frames its own operator CLI sends (`operator CONFIG
status`, through a recording proxy on a second control path) and their replies. It never builds a frame: every
case is a captured frame, or one with a single mutation. The oracle needs no decoder:

  none        the captured request again: the same reply octets as captured (identity and TLS-status
              requests, whose replies are stable; the live-status FNLS reply carries counters and is
              compared by its first ten octets: magic, version, kind and length class)
  flip        one bit anywhere, header, payload or trailer: never the captured success reply (the trailer
              covers the whole protected prefix, so no single flip survives a check)
  truncated, extended, garbage, oversized (a megabyte)
              never the captured success reply; the reply or the close comes within the frame deadline

After every case the owner must still answer the captured identity request with its captured reply (the
owner lives, and a refused frame changed nothing). A disagreement is a row in DIR/findings.jsonl (exit 1).
`--target fake` runs a fake owner (mutation controls: `--plant accept-trailer-flip`, `die-on-oversize`).
"""
import argparse
from contextlib import ExitStack
import json
import os
from pathlib import Path
import random
import socket
import subprocess
import sys
import threading
import time
import unittest

PLANTS = ('accept-trailer-flip', 'die-on-oversize')
DEADLINE = 10.0
CASES = ('none', 'flip', 'flip', 'flip', 'truncated', 'extended', 'garbage', 'oversized')


def exchange(path, request, timeout=DEADLINE + 5):
    """(reply octets, seconds) of one request on its own connection; b'' when the owner closes or refuses."""
    start = time.monotonic()
    with socket.socket(socket.AF_UNIX) as s:
        s.settimeout(timeout)
        try:
            s.connect(str(path))
            s.sendall(request)
            s.shutdown(socket.SHUT_WR)
        except OSError:
            pass
        reply = b''
        try:
            while True:
                chunk = s.recv(65536)
                if not chunk:
                    break
                reply += chunk
        except OSError:
            pass
    return reply, time.monotonic() - start


class Owner:
    """One live owner and its captured frames, or the fake."""

    def __init__(self, target, plant):
        self.target, self.plant, self.stack = target, plant, ExitStack()
        self.dead = False
        if target == 'fake':
            self.frames = {b'FNCT\x01\x1a' + bytes(4) + b'T' * 32: b'FNCT\x01\x1b' + bytes([0, 0, 0, 2]) + b'ok' + b'R' * 32}
            return
        case = unittest.TestCase()
        case.addCleanup = self.stack.callback
        from tests.native_harness import Node, native_image
        from fn2.tests.surface import owned_ports
        node = owned_ports(lambda c: Node(c, native_image('FN_NATIVE_HOST')))(case)
        node.init('fn.test')
        node.start()
        self.node, self.control = node, node.control
        self.frames = self.capture(node)

    def capture(self, node):
        proxy = node.root / 'capture.sock'
        server = socket.socket(socket.AF_UNIX)
        server.bind(str(proxy))
        server.listen(4)
        self.stack.callback(server.close)
        frames = {}

        def serve():
            while True:
                try:
                    conn, _ = server.accept()
                except OSError:
                    return
                with conn:
                    conn.settimeout(DEADLINE)
                    request = b''
                    try:
                        while True:
                            chunk = conn.recv(65536)
                            if not chunk:
                                break
                            request += chunk
                    except OSError:
                        pass
                    reply, _ = exchange(self.control, request)
                    frames.setdefault(request, reply)
                    try:
                        conn.sendall(reply)
                    except OSError:
                        pass
        threading.Thread(target=serve, daemon=True).start()
        client = node.root / 'capture.toml'
        client.write_text(node.config.read_text().replace(f'path = "{node.control}"', f'path = "{proxy}"'))
        from tests.native_harness import native_image
        subprocess.run([str(native_image('FN_NATIVE_HOST')), '--fn', 'operator', str(client), 'status'],
                       capture_output=True, timeout=120)
        if not frames:
            raise RuntimeError('no control frame captured from `operator CONFIG status`')
        return frames

    def send(self, request):
        if self.target != 'fake':
            return exchange(self.control, request)
        if self.dead:
            return b'', 0.0
        if self.plant == 'die-on-oversize' and len(request) > 65536:
            self.dead = True
            return b'', 0.0
        for frame, reply in self.frames.items():
            if request == frame or (self.plant == 'accept-trailer-flip' and len(request) == len(frame)
                                    and request[:-32] == frame[:-32]):
                return reply, 0.0
        return b'FNCT\x01\x02' + bytes([0, 0, 0, 1]) + b'\x02' + b'R' * 32, 0.0

    def close(self):
        self.stack.close()


def stable(frame):
    return frame[:4] == b'FNCT'      # the FNLS live-status reply carries counters


def same_reply(frame, expected, reply):
    return reply == expected if stable(frame) else reply[:10] == expected[:10]


def case(rng, frames):
    frame = rng.choice(sorted(frames))
    kind = rng.choice(CASES)
    data = bytearray(frame)
    if kind == 'none':
        return kind, frame, bytes(data)
    if kind == 'flip':
        i = rng.randrange(len(data))
        data[i] ^= 1 << rng.randrange(8)
    elif kind == 'truncated':
        data = data[:rng.randrange(0, len(data))]
    elif kind == 'extended':
        data += bytes(rng.randrange(256) for _ in range(rng.randrange(1, 64)))
    elif kind == 'garbage':
        data = bytearray(rng.randrange(256) for _ in range(rng.randrange(0, 256)))
    elif kind == 'oversized':
        data = data[:10] + bytes(1 << 20)
    return kind, frame, bytes(data)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--target', choices=('fn1', 'fn2', 'fake'), required=True)
    p.add_argument('--seeds', default='0..499')
    p.add_argument('--seconds', type=float, default=float('inf'))
    p.add_argument('--plant', choices=PLANTS)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args(argv)
    if args.plant and args.target != 'fake':
        p.error('plants require --target fake')
    if args.target != 'fake':
        os.environ['FN2_SURFACE_TARGET'] = args.target
        from fn2.tests.harness import shim
        shim.install(args.target)
    start, end = map(int, args.seeds.split('..'))
    args.out.mkdir(parents=True, exist_ok=True)
    owner = Owner(args.target, args.plant)
    findings, counts, run, deadline = [], {}, 0, time.monotonic() + args.seconds
    identity = next((f for f in sorted(owner.frames) if stable(f)), None)
    try:
        for seed in range(start, end + 1):
            if time.monotonic() >= deadline:
                break
            kind, frame, request = case(random.Random(seed), owner.frames)
            counts[kind] = counts.get(kind, 0) + 1
            reply, seconds = owner.send(request)
            run += 1
            expected = owner.frames[frame]
            problem = None
            if kind == 'none' and not same_reply(frame, expected, reply):
                problem = 'the captured request no longer gets its captured reply'
            elif kind != 'none' and request != frame and reply == expected:
                problem = 'a mutated frame got the captured success reply'
            elif seconds > DEADLINE + 2:
                problem = f'reply or close after {seconds:.1f} s (deadline {DEADLINE} s)'
            if problem is None and identity is not None:
                after, _ = owner.send(identity)
                if after != owner.frames[identity]:
                    problem = 'after this case the owner no longer answers the identity request as captured'
            if problem:
                findings.append(dict(seed=seed, mutation=kind, problem=problem, request=request[:200].hex(),
                                     reply=reply[:200].hex()))
                if 'no longer answers' in problem:
                    break
    finally:
        owner.close()
    (args.out / 'findings.jsonl').write_text(''.join(json.dumps(f) + '\n' for f in findings))
    summary = dict(target=args.target, plant=args.plant, seeds=args.seeds, cases=run, by_mutation=counts,
                   captured=len(owner.frames), findings=len(findings))
    (args.out / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    print(json.dumps(summary))
    return 1 if findings else 0


if __name__ == '__main__':
    sys.exit(main())
