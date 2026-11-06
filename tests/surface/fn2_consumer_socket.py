"""M2's sentence on the laptop: a consumer registers, reads, waits and acks over the owner-only Unix
socket of the served node, an NNTP client posts over its TCP listener, the waiter wakes, and an NNTP
reader fetches the same article.

    python3 -m tests.surface.fn2_consumer_socket --out build/consumer-socket

(from the repository root, the books tests/native-consumer.lsp includes certified on this machine).
Starts `tools/acl2 < tests/native-consumer.lsp` in its own session (the leader's PID in
<out>/node.pid; stopped by that PID's group, never by pattern) with FN2_LISTENER_PORT,
FN2_LISTENER_PATH=<out>/node.sock and FN2_OWNER_UID=os.getuid(), runs the scenario, writes
<out>/report.json (every exchange, its octets and the verdict of each judgment) and exits 0 when
every judgment holds, 1 otherwise, 2 when the node does not start.

The frames on the socket are the port's FNCT (e-surface.md 4.2; books/consumer-codec.lisp, served by
books/fnct-pool.lisp and books/cns.lisp): "FNCT", version 1, kind, a four-octet length, the payload and
BLAKE3-256 of everything before it. A control command is kind 1 (one octet: 1 status .. 5 stop),
answered by kind 2 (the posture octet; stop closes without one); a consumer request is kind 4, a code
octet and its fields (14 register-query, 15 read, 16 wait-cursor, 1 ack, 2 position, 18 status-wide),
answered by kind 28: the class (accepted refused uncertain fault), the reason word and the verb's
result (a cursor; a page's more, next cursor, count and items; ack's position; status's position,
frontier and gap). Each judgment is a sentence of the consumer port's statement (e-surface.md 3, 3.2;
books/consumer-port.lisp) over the node's own answers: the client computes no value the port
computes; it re-sends the cursor the node issued, proposes what the node answered as an ack's
position, and probes one below and one past the frontier the node reported.
"""
import argparse
import json
import os
import queue
import re
import select
import signal
import socket
import subprocess
import sys
import threading
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
DRIVER = os.path.join('tests', 'native-consumer.lsp')

from tests.surface.blake3_pure import blake3

CLASSES = ('accepted', 'refused', 'uncertain', 'fault')
CMD_STATUS, CMD_STOP = 1, 5
CONSUMER = 1
MAGIC = b'FNCT'
KIND_CONTROL, KIND_POSTURE, KIND_REQUEST, KIND_PORT_REPLY = 1, 2, 4, 28
CODES = {'register': 14, 'read': 15, 'wait': 16, 'ack': 1, 'position': 2, 'status': 18, 'fetch': 13}


def seal(kind, payload):
    prefix = MAGIC + bytes([1, kind]) + len(payload).to_bytes(4, 'big') + payload
    return prefix + blake3(prefix)


def be(n):
    return n.to_bytes(max(1, (n.bit_length() + 7) // 8), 'big')


def octets(b):
    """A (:octets 64) field: one length octet (below 128), then the octets."""
    assert len(b) < 128
    return bytes([len(b)]) + b


def u16(b):
    return len(b).to_bytes(2, 'big') + b


def cursor_fields(c):
    """fncu v1: magic, version, five length-prefixed IDs, four u32 counters."""
    assert c[:5] == b'fncu\x01', c
    i, ids = 5, []
    for _ in range(5):
        n = c[i]
        ids.append(c[i + 1:i + 1 + n])
        i += 1 + n
    words = [int.from_bytes(c[i + 4 * k:i + 4 * k + 4], 'big') for k in range(4)]
    assert i + 16 == len(c), c
    return ids, words


def cursor_position(c):
    return cursor_fields(c)[1][3]


def cursor_at(c, position):
    """The issued cursor C proposing POSITION (an ack's payload)."""
    return c[:-4] + position.to_bytes(4, 'big')


def request(verb, cursor=None, position=None, items=8, seconds=30, mid=b''):
    code = CODES[verb]
    if verb == 'register':      # consumer, the empty stream list (the inbox), start :history
        fields = octets(be(CONSUMER)) + u16(b'') + bytes([1])
    elif verb in ('position', 'status'):
        fields = octets(be(CONSUMER))
    elif verb == 'read':
        fields = u16(cursor) + items.to_bytes(4, 'big') + (65536).to_bytes(4, 'big')
    elif verb == 'wait':
        fields = u16(cursor) + items.to_bytes(4, 'big') + (65536).to_bytes(4, 'big') + seconds.to_bytes(4, 'big')
    elif verb == 'ack':
        fields = cursor_at(cursor, position)
    elif verb == 'fetch':       # Message-ID, domain 0, the occurrence's position
        fields = u16(mid) + (0).to_bytes(4, 'big') + position.to_bytes(8, 'big')
    return seal(KIND_REQUEST, bytes([code]) + fields)


def open_frame(f):
    """(kind, payload) of one whole frame; raises when the frame is not FNCT or its trailer is wrong."""
    if len(f) < 42 or f[:5] != MAGIC + b'\x01':
        raise ValueError(f'not an FNCT frame: {f.hex()}')
    n = int.from_bytes(f[6:10], 'big')
    if len(f) != 42 + n or blake3(f[:10 + n]) != f[10 + n:]:
        raise ValueError(f'FNCT extent or trailer wrong: {f.hex()}')
    return f[5], f[10:10 + n]


def decode(verb, frame):
    """A kind 28 reply as the judgments read it."""
    kind, p = open_frame(frame)
    if kind != KIND_PORT_REPLY:
        raise ValueError(f'{verb}: reply kind {kind}')
    cls = CLASSES[p[0]]
    wl = int.from_bytes(p[1:3], 'big')
    word = p[3:3 + wl].decode('ascii')
    rl = int.from_bytes(p[3 + wl:7 + wl], 'big')
    q = p[7 + wl:7 + wl + rl]
    if 7 + wl + rl != len(p):
        raise ValueError(f'{verb}: kind 28 payload {p.hex()}')
    r = dict(outcome=cls, reason=word or 'none', result=q.hex())
    if cls != 'accepted':
        if q:
            raise ValueError(f'{verb}: a {cls} reply carries a result {q.hex()}')
        return r
    if verb in ('register', 'position'):
        r.update(cursor=q, position=cursor_position(q))
    elif verb == 'ack':
        r.update(position=int.from_bytes(q[4:12], 'big'))
    elif verb == 'status':
        r.update(position=int.from_bytes(q[4:12], 'big'), frontier=int.from_bytes(q[12:20], 'big'),
                 gap=int.from_bytes(q[20:28], 'big'))
    elif verb == 'fetch':
        al = int.from_bytes(q[0:4], 'big')
        if 4 + al != len(q):
            raise ValueError(f'fetch: result {q.hex()}')
        r.update(article=q[4:])
    elif verb in ('read', 'wait'):
        nl = int.from_bytes(q[1:3], 'big')
        nxt = q[3:3 + nl]
        count = int.from_bytes(q[3 + nl:7 + nl], 'big')
        il = int.from_bytes(q[7 + nl:11 + nl], 'big')
        items = parse_items(q[11 + nl:11 + nl + il])
        if len(items) != count:
            raise ValueError(f'{verb}: count {count} but {len(items)} items')
        r.update(more=q[0], cursor=nxt, next=cursor_position(nxt), count=count, items=items)
    return r


ITEM_TYPES = ('record', 'withdrawn', 'reference', 'gap')


def parse_items(b):
    """A page's items (e-surface.md 4.2; consumer-codec.lisp *fn2-fnct-item-layout*): type, domain, position,
    reasons, streams, Message-ID and body (a reference's body is its octet count and content identity)."""
    items, i = [], 0
    while i < len(b):
        t, dom, pos, reasons = b[i], int.from_bytes(b[i + 1:i + 5], 'big'), int.from_bytes(b[i + 5:i + 13], 'big'), b[i + 13]
        i += 14
        sl = int.from_bytes(b[i:i + 2], 'big'); streams = b[i + 2:i + 2 + sl]; i += 2 + sl
        ml = int.from_bytes(b[i:i + 2], 'big'); mid = b[i + 2:i + 2 + ml]; i += 2 + ml
        bl = int.from_bytes(b[i:i + 4], 'big'); body = b[i + 4:i + 4 + bl]; i += 4 + bl
        if i > len(b) or t >= len(ITEM_TYPES):
            raise ValueError(f'items: malformed at {i}: {b.hex()}')
        item = dict(type=ITEM_TYPES[t], domain=dom, position=pos, reasons=reasons, streams=streams.hex(),
                    message_id=mid.decode('latin-1'), body=body)
        if item['type'] == 'reference':
            if bl != 41:
                raise ValueError(f'items: a reference body of {bl} octets')
            item.update(octets=int.from_bytes(body[:8], 'big'), content=body[9:].hex())
        items.append(item)
    return items


class Report:
    def __init__(self):
        self.exchanges, self.judgments = [], []

    def exchange(self, carrier, sent, received, note=''):
        self.exchanges.append(dict(carrier=carrier, sent=sent.hex(), received=received.hex(), note=note))

    def judge(self, sentence, holds, evidence):
        self.judgments.append(dict(sentence=sentence, holds=bool(holds),
                                   evidence=evidence if isinstance(evidence, (dict, int, str)) else repr(evidence)))
        print(f"{'ok  ' if holds else 'FAIL'} {sentence}: {evidence}", flush=True)
        return holds


class Consumer:
    """The local carrier's client: one request in flight, its reply one FNCT frame."""

    def __init__(self, path, report):
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.sock.settimeout(30)
        self.sock.connect(path)
        self.report = report

    def send(self, verb, **fields):
        frame = request(verb, **fields)
        self.sock.sendall(frame)
        return frame

    def _read(self, n):
        got = b''
        while len(got) < n:
            chunk = self.sock.recv(n - len(got))
            if not chunk:
                break
            got += chunk
        return got

    def receive(self, frame, verb, seconds=30):
        self.sock.settimeout(seconds)
        got = self._read(10)
        if len(got) == 10:
            got += self._read(int.from_bytes(got[6:10], 'big') + 32)
        self.report.exchange('L', frame, got, verb)
        if len(got) < 42:
            raise RuntimeError(f'{verb}: the node answered {got!r} and closed')
        return decode(verb, got)

    def call(self, verb, **fields):
        return self.receive(self.send(verb, **fields), verb)

    def quiet(self, seconds):
        """True when no octet arrives within SECONDS (a parked request)."""
        ready, _, _ = select.select([self.sock], [], [], seconds)
        return not ready

    def stop(self):
        frame = seal(KIND_CONTROL, bytes([CMD_STOP]))
        self.sock.sendall(frame)
        self.sock.settimeout(30)
        rest = b''
        while True:
            chunk = self.sock.recv(4096)
            if not chunk:
                break
            rest += chunk
        self.report.exchange('L', frame, rest, 'stop')
        self.sock.close()
        return rest


class Nntp:
    def __init__(self, port, report, name):
        self.sock = socket.create_connection(('127.0.0.1', port), timeout=30)
        self.file = self.sock.makefile('rb')
        self.report, self.name = report, name
        self.greeting = self.file.readline()
        report.exchange(name, b'', self.greeting, 'greeting')

    def line(self, command):
        self.sock.sendall(command)
        reply = self.file.readline()
        self.report.exchange(self.name, command, reply)
        return reply

    def block(self):
        lines = []
        while True:
            line = self.file.readline()
            if line in (b'.\r\n', b''):
                break
            lines.append(line)
        self.report.exchange(self.name, b'', b''.join(lines) + b'.\r\n', 'multi-line block')
        return lines

    def post(self, article):
        first = self.line(b'POST\r\n')
        if not first.startswith(b'340'):
            return first, None
        stuffed = b''.join((b'.' + l if l.startswith(b'.') else l) + b'\r\n' for l in article.split(b'\r\n'))
        self.sock.sendall(stuffed + b'.\r\n')
        final = self.file.readline()
        self.report.exchange(self.name, stuffed + b'.\r\n', final, 'article')
        return first, final

    def quit(self):
        self.line(b'QUIT\r\n')
        self.sock.close()


def start_node(out, port, path):
    env = dict(os.environ, FN2_LISTENER_PORT=str(port), FN2_LISTENER_PATH=path, FN2_OWNER_UID=str(os.getuid()))
    log = open(os.path.join(out, 'node.log'), 'wb')
    proc = subprocess.Popen([os.path.join(ROOT, 'tools', 'acl2')], cwd=ROOT, stdin=open(os.path.join(ROOT, DRIVER), 'rb'),
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env, start_new_session=True)
    with open(os.path.join(out, 'node.pid'), 'w') as f:
        f.write(f'{proc.pid}\n')
    return proc, log


class Lines:
    """The node's stdout, one line at a time, read by a thread (a select on a buffered pipe misses lines)."""

    def __init__(self, proc, log):
        self.queue, self.log = queue.Queue(), log
        threading.Thread(target=self._pump, args=(proc.stdout,), daemon=True).start()

    def _pump(self, stream):
        for line in iter(stream.readline, b''):
            self.log.write(line)
            self.log.flush()
            self.queue.put(line)
        self.queue.put(None)

    def wait(self, prefix, seconds):
        deadline = time.monotonic() + seconds
        while True:
            try:
                line = self.queue.get(timeout=max(0.01, deadline - time.monotonic()))
            except queue.Empty:
                break
            if line is None:
                raise RuntimeError(f'the node ended before {prefix!r} (see node.log)')
            if line.startswith(prefix):
                return line
            if line.startswith(b'REFUSED '):
                raise RuntimeError(line.decode().strip())
        raise RuntimeError(f'no {prefix!r} within {seconds} s (see node.log)')


def stop_node(proc, log):
    """SIGTERM to the session the PID file names, then its STOPPED line."""
    if proc.poll() is None:
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    try:
        proc.wait(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait()
    time.sleep(0.5)   # the reader thread drains the pipe to EOF
    log.close()
    return proc.returncode


def scenario(port, path, report, mid):
    j = report.judge
    mode = os.stat(path).st_mode & 0o777
    j('L is the owner\'s 0600 socket', mode == 0o600, oct(mode))
    j('the owner is the test\'s own uid, not root', os.getuid() != 0, os.getuid())
    c = Consumer(path, report)

    # register: accepted with the recorded cursor (e-surface 3).
    r = c.call('register')
    j('register(c1, the inbox, from history) is accepted', r['outcome'] == 'accepted' and r['reason'] == 'none', r)
    cur = r.get('cursor', b'')
    again = c.call('register')
    j('the same registration again answers the recorded cursor', again['outcome'] == 'accepted'
      and again.get('cursor') == cur, again)
    s0 = c.call('status')
    j('status answers accepted with position <= frontier', s0['outcome'] == 'accepted'
      and s0['position'] <= s0['frontier'] and s0['gap'] == s0['frontier'] - s0['position'], s0)
    p0 = c.call('position')
    j('position answers the recorded cursor (status\'s position)', p0['outcome'] == 'accepted'
      and p0['position'] == s0['position'] and p0.get('cursor') == cursor_at(cur, s0['position']), p0)

    # read: a page in commit-position order from the recorded position to the frontier (3, 4.1).
    page = c.call('read', cursor=cur)
    j('read is accepted and its next proposal is the frontier status answered', page['outcome'] == 'accepted'
      and page['next'] >= s0['frontier'], page)
    j('the page is complete within the client\'s limit (more 0), so its next cursor is its next proposal',
      page['more'] == 0, page)
    if page['count'] > 0:
        a = c.call('ack', cursor=cur, position=page['next'])
        j('ack of the page\'s next is accepted and recorded', a['outcome'] == 'accepted'
          and a['position'] == page['next'], a)
    caught = c.call('status')
    frontier = caught['frontier']
    j('after the ack, the recorded position is the frontier (nothing unread)', caught['outcome'] == 'accepted'
      and caught['position'] == caught['frontier'] and caught['gap'] == 0, caught)

    # wait: parks while nothing past the cursor is published (3, 5; K4).
    w = c.send('wait', cursor=cur)
    j('wait with nothing unread parks (no reply within 2 s)', c.quiet(2), 'quiet')

    # append on carrier N: an NNTP POST (consumer-port.lisp: append is POST).
    poster = Nntp(port, report, 'N-post')
    j('the NNTP listener greets with posting allowed (200)', poster.greeting.startswith(b'200'), poster.greeting)
    article = (b'From: m2@example.invalid\r\nNewsgroups: local.test\r\nSubject: m2 sentence\r\n'
               b'Message-ID: ' + mid + b'\r\n\r\nthe consumer sees this\r\n.dotted line\r\nend')
    first, final = poster.post(article)
    j('POST is accepted (340 then 240)', first.startswith(b'340') and final is not None and final.startswith(b'240'),
      [first, final])
    poster.quit()

    # a second owner connection sees the post's commit in the frontier while the first waits
    second = Consumer(path, report)
    seen = second.call('status')
    j('status on a second connection answers the frontier past the waiter\'s position', seen['outcome'] == 'accepted'
      and seen['position'] == frontier and seen['frontier'] == frontier + 1, seen)
    second.stop()

    # the waiter wakes with the post's position (K4: woken by the publish, never a scan).
    item = {}
    try:
        woke = c.receive(w, 'wait', seconds=60)
    except socket.timeout:
        woke = None
    j('the parked wait answers after the publish (within 60 s)', woke is not None, woke)
    if woke is None:
        # the parked connection stays parked; the ack contract runs on a fresh one
        c = Consumer(path, report)
        new = seen['frontier']
    else:
        j('the woken wait is accepted', woke['outcome'] == 'accepted', woke)
        j('the woken page holds exactly the one new commit, its next the post\'s position', woke['count'] == 1
          and woke['next'] == frontier + 1 and woke['more'] == 0, woke)
        new = woke['next']
        item = woke['items'][0] if woke['items'] else {}
        j('the woken page\'s item is the post\'s record: its position, its Message-ID',
          item.get('type') == 'record' and item.get('position') == new
          and item.get('message_id') == mid.decode(), {k: v for k, v in item.items() if k != 'body'})
        f = c.call('fetch', mid=mid, position=new)
        j('fetch of the occurrence (its Message-ID, its position) answers the item\'s octets (3.4)',
          f['outcome'] == 'accepted' and f.get('article') == item.get('body') and len(f.get('article', b'')) > 0,
          {k: v for k, v in f.items() if k != 'article'})
        f = c.call('fetch', mid=b'<not-' + mid[1:], position=new)
        j('fetch naming another Message-ID at that position is unavailable, never another selection',
          f['outcome'] == 'refused' and f['reason'] == 'unavailable', f)

    # ack contract (3.2): forward only; equal accepted, lower behind, past the frontier refused.
    a = c.call('ack', cursor=cur, position=new)
    j('ack of the woken page\'s next is accepted, recorded at it', a['outcome'] == 'accepted'
      and a['position'] == new, a)
    p = c.call('position')
    j('position answers the acknowledged position', p['outcome'] == 'accepted' and p['position'] == new, p)
    s = c.call('status')
    j('status answers position and frontier, nothing unread', s['outcome'] == 'accepted' and s['position'] == new
      and s['frontier'] == new, s)
    a = c.call('ack', cursor=cur, position=new)
    j('an equal ack is accepted with no change', a['outcome'] == 'accepted' and a['position'] == new, a)
    a = c.call('ack', cursor=cur, position=new - 1)
    p = c.call('position')
    j('a lower ack is refused behind, without rewind', a['outcome'] == 'refused' and a['reason'] == 'behind'
      and p.get('position') == new, [a, p])
    a = c.call('ack', cursor=cur, position=new + 1)
    p = c.call('position')
    j('an ack past the committed frontier is refused beyond-frontier', a['outcome'] == 'refused'
      and a['reason'] == 'beyond-frontier' and p.get('position') == new, [a, p])
    after = c.call('read', cursor=cur)
    j('a read after the ack starts at the acknowledged position: an empty page', after['outcome'] == 'accepted'
      and after['next'] == new and after['count'] == 0, after)
    rest = c.stop()
    j('the stop command closes the control connection', rest == b'', rest.hex())

    # an NNTP reader sees the same article (3.3: no second write path).
    reader = Nntp(port, report, 'N-read')
    g = reader.line(b'GROUP local.test\r\n')
    j('GROUP local.test counts the posted article', g.startswith(b'211 '), g)
    head = reader.line(b'ARTICLE ' + mid + b'\r\n')
    lines = reader.block() if head.startswith(b'220') else []
    body = b''.join(lines)
    j('ARTICLE <mid> answers 220 with the posted Message-ID', head.startswith(b'220') and mid in head, head)
    unstuffed = b''.join(l[1:] if l.startswith(b'..') else l for l in lines)
    # N renders the node's group projection as the article's first line
    # (Xref from the overview row, cursor.lisp fn2-cursor-put-xref); a
    # RECORD item is the exact stored octets, the projection not among them
    # (e-surface.md 4.1), so L's octets are N's after that one line, and the
    # line is exactly the projection of the posted article's group number.
    num = g.split()[3] if g.startswith(b'211 ') else b''
    xref = re.match(rb'Xref: [^ \r\n]+ local\.test:' + re.escape(num) + rb'\r\n', unstuffed) if num else None
    stored = unstuffed[xref.end():] if xref else b''
    j('the same article on L and N: the woken item\'s octets are ARTICLE <mid>\'s after N\'s Xref projection line',
      woke is not None and xref is not None and item.get('body') == stored and len(stored) > 0,
      [len(unstuffed), len(stored), len(item.get('body', b'') if woke else b'')])
    j('the article\'s octets are the posted header lines and body', all(
        piece in body for piece in (b'Subject: m2 sentence\r\n', b'Message-ID: ' + mid + b'\r\n',
                                    b'the consumer sees this\r\n', b'..dotted line\r\n', b'end\r\n')), body.decode('latin-1'))
    reader.quit()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--out', default=os.path.join('build', 'consumer-socket'))
    parser.add_argument('--start-seconds', type=int, default=900)
    args = parser.parse_args(argv)
    out = os.path.abspath(args.out)
    os.makedirs(out, exist_ok=True)
    path = os.path.join(out, 'node.sock')
    if os.path.exists(path):
        print(f'{path} exists (a previous node is live, or its stop failed): not removed', file=sys.stderr)
        return 2
    probe = socket.socket()
    probe.bind(('127.0.0.1', 0))
    port = probe.getsockname()[1]
    probe.close()
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    report = Report()
    mid = f'<m2-{os.getpid()}-{int(time.time())}@example.invalid>'.encode()
    proc, log = start_node(out, port, path)
    started, error = False, None
    try:
        lines = Lines(proc, log)
        lines.wait(b'LISTENING ', args.start_seconds)
        lines.wait(b'LISTENING-LOCAL ', 60)
        started = True
        scenario(port, path, report, mid)
    except Exception as e:   # the report names it; the node is stopped either way
        error = f'{type(e).__name__}: {e}'
        print('ERROR', error, file=sys.stderr)
    finally:
        code = stop_node(proc, log)
    with open(os.path.join(out, 'node.log'), 'rb') as f:
        stopped = [l.decode().strip() for l in f if l.startswith(b'STOPPED')]
    held = all(x['holds'] for x in report.judgments)
    result = dict(
        command='python3 -m tests.surface.fn2_consumer_socket --out ' + args.out,
        driver=DRIVER, started=started, error=error, node_exit=code, stopped=stopped,
        socket_removed=not os.path.exists(path),
        judgments=report.judgments, exchanges=report.exchanges,
        judged=len(report.judgments), held=sum(x['holds'] for x in report.judgments),
        owed=['an item\'s streams and reasons (4.1): the one served query is the principal\'s inbox, so items carry '
              'none',
              'the fncu cursor\'s history and incarnation (one 0 octet each until B serves the store\'s) and a '
              'durable principal id (the principal\'s slot until then): e-surface.md 14 item 8'],
        verdict='pass' if started and error is None and held and code == 0 else 'fail')
    text = json.dumps(result, indent=1, default=lambda o: o.hex() if isinstance(o, (bytes, bytearray)) else repr(o))
    with open(os.path.join(out, 'report.json'), 'w') as f:
        f.write(text)
    print(f"consumer-socket: {result['verdict']} ({result['held']}/{result['judged']} judgments hold; "
          f"node exit {code}; {os.path.join(out, 'report.json')})")
    if not started:
        return 2
    return 0 if result['verdict'] == 'pass' else 1


if __name__ == '__main__':
    sys.exit(main())
