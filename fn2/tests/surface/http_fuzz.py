"""F for web: seeded HTTP/1.1 request-head mutation against the node's own web face (H7f).

    python3 -m fn2.tests.surface.http_fuzz --target fn1|fn2|fake --seeds A..B --out DIR [--seconds S]
        [--plant P]

RELEASE-PLAN §2.2's F row for the web reader: "`defgrammar http` fuzz (request line, headers, chunking,
form bodies)". Each case is one well-formed request (GET or HEAD /health, GET of an absent path, POST to a
GET path) with at most one deviation whose answer RFC 9112 / RFC 9110 and the face's stated local policy
decide (books/web-request.lisp's header, the parser's contract: method, request-target, version, field
lines, Host, Content-Length, Transfer-Encoding, line ends, the head limit):

  200 GET/HEAD /health; absolute-form target (9112 3.2.2); HTTP/1.0 without Host; equal duplicate
      Content-Length (9112 6.3)
  404 an absent path          405 POST to a GET-only path
  400 a malformed request line (double space, a tab, no version); a target neither origin- nor
      absolute-form; a version that is not HTTP/x.y; HTTP/1.1 without Host or with two; whitespace before
      a field colon (9112 5.1); obs-fold (5.2); NUL in a field value (9110 5.5); a bare LF line end;
      a non-digit or two unequal Content-Length values (6.3); a bare LF ending one field line (2.2: this face
      accepts only CRLF)
  411 POST without Content-Length    413 Content-Length over the body limit    431 a head past its limit
  no reply, close   a head whose every line ends in a bare LF: no CRLF CRLF frames it, so at the client's
      EOF the face closes (RFC 9112 8: an incomplete message); a single bare LF inside a framed head is 400
  501 a method other than GET, HEAD, POST (9110 9.1); any Transfer-Encoding (the face's stated policy)
  505 HTTP/2.0, HTTP/1.2, HTTP/3.0

Every case is one connection; the reply's status line must be `HTTP/1.1 NNN reason` (or 1.0) with the
expected NNN. After every 25 cases and at the end, GET /health must still answer 200 `ready` (the face
lives). A disagreement is a row in DIR/findings.jsonl (exit 1). `--target fake` judges an independent
reading of the same rules (mutation controls: `--plant accept-transfer-encoding`, `accept-bare-lf`,
`505-as-400`).
"""
import argparse
from contextlib import ExitStack
import json
import os
from pathlib import Path
import random
import re
import socket
import sys
import time
import unittest

PLANTS = ('accept-transfer-encoding', 'accept-bare-lf', '505-as-400')
HEAD_LIMIT_OCTETS = 1 << 20     # past any profile's head limit (the 431 case)
BODY_LIMIT_OCTETS = 1 << 40     # past any profile's body limit (the 413 case)
CASES = ('get-health', 'head-health', 'absent', 'post-get-path', 'absolute-form', 'http10-no-host',
         'equal-cl', 'method', 'double-space', 'tab', 'no-version', 'bad-target', 'version-syntax',
         'no-host', 'two-hosts', 'space-before-colon', 'obs-fold', 'nul-in-value', 'bare-lf', 'unframed-lf', 'cl-nondigit',
         'cl-unequal', 'post-no-cl', 'cl-too-big', 'head-too-big', 'transfer-encoding', 'version-unsupported')


def request(rng, host):
    """(case, expected status, request octets)."""
    kind = rng.choice(CASES)
    method, target, version = 'GET', '/health', 'HTTP/1.1'
    fields = [('Host', host)]
    expected = 200
    sep, eol, extra = ' ', '\r\n', ''
    if kind == 'head-health':
        method = 'HEAD'
    elif kind == 'absent':
        target, expected = '/zz-absent-' + str(rng.randrange(100)), 404
    elif kind == 'post-get-path':
        method, expected = 'POST', 405
        fields.append(('Content-Length', '0'))
    elif kind == 'absolute-form':
        target = 'http://' + host + '/health'
    elif kind == 'http10-no-host':
        version, fields = 'HTTP/1.0', []
    elif kind == 'equal-cl':
        fields += [('Content-Length', '0'), ('Content-Length', '0')]
    elif kind == 'method':
        method, expected = rng.choice(['PUT', 'DELETE', 'PATCH', 'OPTIONS', 'TRACE', 'BREW', 'get', 'Post']), 501
    elif kind == 'double-space':
        sep, expected = '  ', 400
    elif kind == 'tab':
        sep, expected = '\t', 400
    elif kind == 'no-version':
        version, expected = '', 400
    elif kind == 'bad-target':
        target, expected = rng.choice(['health', '*', 'h:ealth', '//', '%zz']), 400
        if target == '//':
            expected = 404      # an origin-form path no route has
    elif kind == 'version-syntax':
        version, expected = rng.choice(['HTTP/1', 'http/1.1', 'HTTP/1.1x', 'HTTP 1.1', 'HTTPS/1.1']), 400
    elif kind == 'version-unsupported':
        version, expected = rng.choice(['HTTP/2.0', 'HTTP/1.2', 'HTTP/3.0']), 505
    elif kind == 'no-host':
        fields, expected = [], 400
    elif kind == 'two-hosts':
        fields, expected = fields + [('Host', host)], 400
    elif kind == 'space-before-colon':
        fields, expected = [('Host ', host)], 400
    elif kind == 'obs-fold':
        fields, expected = fields + [('X-Fuzz', 'a')], 400
        extra = ' folded'
    elif kind == 'nul-in-value':
        fields, expected = fields + [('X-Fuzz', 'a\x00b')], 400
    elif kind == 'bare-lf':
        fields, expected = [('X-Fuzz', 'lf')] + fields, 400
        extra = None            # this one field line ends in a bare LF inside a CRLF-framed head
    elif kind == 'unframed-lf':
        eol, expected = '\n', None     # no CRLF CRLF: the head is never framed; at EOF, close without a reply
    elif kind == 'cl-nondigit':
        method, target = 'POST', '/signin'
        fields, expected = fields + [('Content-Length', rng.choice(['abc', '-1', '1.5', '0x10', '+3']))], 400
    elif kind == 'cl-unequal':
        method, target = 'POST', '/signin'
        fields, expected = fields + [('Content-Length', '0'), ('Content-Length', '1')], 400
    elif kind == 'post-no-cl':
        method, target, expected = 'POST', '/signin', 411
    elif kind == 'cl-too-big':
        method, target = 'POST', '/signin'
        fields, expected = fields + [('Content-Length', str(BODY_LIMIT_OCTETS))], 413
    elif kind == 'head-too-big':
        fields, expected = fields + [('X-Fuzz', 'h' * HEAD_LIMIT_OCTETS)], 431
    elif kind == 'transfer-encoding':
        method, target = 'POST', '/signin'
        fields, expected = fields + [('Transfer-Encoding', rng.choice(['chunked', 'gzip, chunked', 'identity']))], 501
    line = method + sep + target + ((sep + version) if version else '')
    head = line + eol + ''.join(f'{k}: {v}' + ('\n' if k == 'X-Fuzz' and extra is None else eol) +
                                (extra + eol if k == 'X-Fuzz' and extra else '') for k, v in fields)
    return kind, expected, (head + eol).encode('latin-1')


def fake_status(octets, plant=None):
    """An independent reading of the same rules, for the mutation controls."""
    text = octets.decode('latin-1')
    if '\r\n\r\n' not in text and plant != 'accept-bare-lf':
        return None
    if '\n' in text.replace('\r\n', '') and plant != 'accept-bare-lf':
        return 400
    head = text.replace('\r\n', '\n') if plant == 'accept-bare-lf' else text
    lines = head.split('\n' if plant == 'accept-bare-lf' else '\r\n')
    if len(octets) > 65536:
        return 431
    m = re.fullmatch(r'([!#$%&\'*+.^_`|~0-9A-Za-z-]+) (\S+) (\S+)', lines[0])
    if not m:
        return 400
    method, target, version = m.groups()
    vm = re.fullmatch(r'HTTP/([0-9])\.([0-9])', version)
    if not vm:
        return 400
    if version not in ('HTTP/1.1', 'HTTP/1.0'):
        return 400 if plant == '505-as-400' else 505
    if method not in ('GET', 'HEAD', 'POST'):
        return 501
    if target.startswith('http://'):
        target = '/' + target.split('/', 3)[3] if target.count('/') >= 3 else '/'
    if not target.startswith('/'):
        return 400
    fields = []
    for line in lines[1:]:
        if not line:
            break
        if line[0] in ' \t':
            return 400
        name, colon, value = line.partition(':')
        if not colon or name != name.rstrip() or '\x00' in value:
            return 400
        fields.append((name.lower(), value.strip()))
    hosts = [v for k, v in fields if k == 'host']
    if version == 'HTTP/1.1' and len(hosts) != 1:
        return 400
    if any(k == 'transfer-encoding' for k, _ in fields) and plant != 'accept-transfer-encoding':
        return 501
    lengths = {v for k, v in fields if k == 'content-length'}
    if any(not v.isdigit() for v in lengths) or len(lengths) > 1:
        return 400
    if method == 'POST' and not lengths and not any(k == 'transfer-encoding' for k, _ in fields):
        return 411
    if lengths and int(next(iter(lengths))) > 1 << 30:
        return 413
    path = target.split('?')[0]
    if path == '/health':
        return 405 if method == 'POST' else 200
    if path == '/signin':
        return 200
    return 404


class Face:
    """The web face of one developer-image node (the web S target), or the fake."""

    def __init__(self, target, plant):
        self.target, self.plant, self.stack = target, plant, ExitStack()
        if target == 'fake':
            self.host = '127.0.0.1:1'
            return
        case = unittest.TestCase()
        case.addCleanup = self.stack.callback
        from fn2.tests.surface.web.test_model_web import WebTarget
        self.web = WebTarget(case)
        self.host = '127.0.0.1:%d' % self.web.port

    def send(self, octets):
        """(status code or None, status line) for one request on its own connection."""
        if self.target == 'fake':
            code = fake_status(octets, self.plant)
            return code, (f'HTTP/1.1 {code} fake' if code else '')
        with socket.create_connection(('127.0.0.1', self.web.port), timeout=10) as sock:
            try:
                sock.sendall(octets)
                sock.shutdown(socket.SHUT_WR)
            except OSError:
                pass        # the face may answer and close before it has a long head
            data = b''
            try:
                while b'\r\n' not in data and len(data) < 4096:
                    chunk = sock.recv(4096)
                    if not chunk:
                        break
                    data += chunk
            except (socket.timeout, ConnectionResetError):
                pass
        line = data.split(b'\r\n', 1)[0].decode('latin-1')
        m = re.fullmatch(r'HTTP/1\.[01] ([1-5][0-9][0-9])( .*)?', line)
        return (int(m.group(1)) if m else None), line

    def alive(self):
        code, line = self.send(f'GET /health HTTP/1.1\r\nHost: {self.host}\r\n\r\n'.encode())
        return code == 200, line

    def close(self):
        self.stack.close()


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--target', choices=('fn1', 'fn2', 'fake'), required=True)
    p.add_argument('--seeds', default='0..999')
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
    face = Face(args.target, args.plant)
    findings, counts, run, deadline = [], {}, 0, time.monotonic() + args.seconds
    try:
        for seed in range(start, end + 1):
            if time.monotonic() >= deadline:
                break
            kind, expected, octets = request(random.Random(seed), face.host)
            counts[kind] = counts.get(kind, 0) + 1
            code, line = face.send(octets)
            run += 1
            if code != expected:
                findings.append(dict(seed=seed, case=kind, expected=expected, status=line,
                                     problem='no status line' if code is None else f'expected {expected}',
                                     request=octets[:600].decode('latin-1')))
            if run % 25 == 0:
                ok, line = face.alive()
                if not ok:
                    findings.append(dict(seed=seed, case='liveness', expected=200, status=line,
                                         problem='GET /health no longer 200 after the cases'))
                    break
        ok, line = face.alive()
        if not ok:
            findings.append(dict(seed=None, case='liveness', expected=200, status=line, problem='GET /health at the end'))
    finally:
        face.close()
    (args.out / 'findings.jsonl').write_text(''.join(json.dumps(f) + '\n' for f in findings))
    summary = dict(target=args.target, plant=args.plant, seeds=args.seeds, cases=run, by_case=counts,
                   findings=len(findings))
    (args.out / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    print(json.dumps(summary))
    return 1 if findings else 0


if __name__ == '__main__':
    sys.exit(main())
