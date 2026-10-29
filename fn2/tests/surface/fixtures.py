"""E fixture drivers: each fixture row replayed against the live target (README "Provisioning and driver hooks").

One hook for every family: `FN2_SURFACE_FIXTURE_<FAMILY>=fn2.tests.surface.fixtures:fixture`. The row's
`path` selects the driver. Each driver builds the setup the fixture presupposes on a fresh node, replays it,
asserts the contract with `case`, and writes every compared row to `OUT/fixtures/<name>.json`. A fixture that
does not exist in this tree is a named skip, never a pass.

- `fn2/tests/model/fixtures/rfc3977`: the RFC 3977 transcripts on a live node. Setup the transcripts
  presuppose is built (groups, the example articles); numbers the setup cannot reproduce are compared by the
  rule that produced them (an empty group's `211 0 L L-1`), and every other octet the transcript fixes is
  compared exactly (status code, Message-ID echo, header values, body).
- `tests/fixtures/consumer-position`: the CNS cursor vectors through the image's `consumer-inspect`, whose
  expected decodings are the carried `tests.test_native_consumer_inspect` assertions (the developer image).
- `tests/bp-dtn7/golden`: the dtn7-rs-authored bundle through `bp decode` (accepted, ADU equal to what
  dtn7-rs sent) and fn's own captured bundle re-authored by `bp send` with the capture's inputs (octet-equal).
- `fn2/tests/fixtures/scram`: RFC 7677 section 3's SCRAM-SHA-256 vector through the tests' independent
  client (tests/sasl_client.py, the one the tls_auth S form uses against the server), then a live SCRAM
  exchange whose server signature that client verifies.
"""
from datetime import datetime, timedelta, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

from fn2.tests.surface import ROOT, owned_ports


def fixture(*, case, target, family, out, path, contract):
    path = Path(path)
    name = path.relative_to(ROOT).as_posix() if path.is_absolute() else path.as_posix()
    if name not in DRIVERS:
        raise ValueError(f'no fixture driver for {name} ({family}: {contract})')
    if not path.exists():
        raise unittest.SkipTest(f'fixture absent in this tree: {name} ({contract})')
    driver = DRIVERS[name]
    if driver is None:
        raise ValueError(f'fixture {name} now exists; its driver is owed ({contract})')
    directory = Path(out) / 'fixtures'
    directory.mkdir(parents=True, exist_ok=True)
    rows = driver(case, path)
    (directory / (path.name + '.json')).write_text(json.dumps(rows, indent=1, sort_keys=True, default=repr))
    bad = [r for r in rows if not r['ok']]
    case.assertTrue(rows, f'{name}: no fixture row compared')
    case.assertFalse(bad, f'{name}: {len(bad)} of {len(rows)} rows differ: ' + json.dumps(bad[:3], default=repr))
    return rows


# -- RFC 3977 transcripts -----------------------------------------------------------------------------

EXAMPLE_ID = '<45223423@example.com>'
EXAMPLE_GROUP = 'misc.test'
# RFC 5536 section 3.1.4 reserves example.* ("MUST NOT be used for the names of normal newsgroups"), and
# fn refuses to create one (RESERVED-GROUP-NAME); the transcript's empty group is created under this name
# and the name is rewritten in the replayed command and the expected reply alike. The unknown-group
# transcript keeps its example.* name: it is never created, so 411 is still the answer.
RENAMES = {b'example.currently.empty.newsgroup': b'fixture.currently.empty.newsgroup'}
EMPTY_GROUP = 'fixture.currently.empty.newsgroup'
NEW_ARTICLES = {'<i.am.a.new.article@example.com>': 'news.test',
                '<i.am.another.new.article@example.com>': 'sci.test'}
SETUP_GROUPS = (EXAMPLE_GROUP, EMPTY_GROUP, *sorted(set(NEW_ARTICLES.values())))


def transcript(path):
    """[(direction, octets)] of one fixture, comments dropped; '[S]' alone is the empty line."""
    rows = []
    for line in path.read_text().splitlines():
        if line.startswith('#') or not line.strip():
            continue
        tag, _, rest = line.partition(' ')
        if tag not in ('[C]', '[S]'):
            raise ValueError(f'{path.name}: not a transcript line: {line!r}')
        rows.append((tag[1], (rest if line != tag else '').encode('utf-8')))
    return rows


def exchanges(rows):
    """(greeting lines, [(command, [reply lines])]) from a transcript."""
    greeting, steps = [], []
    for direction, text in rows:
        if direction == 'C':
            steps.append((text, []))
        elif steps:
            steps[-1][1].append(text)
        else:
            greeting.append(text)
    return greeting, steps


def example_article(rows):
    """The example article's octets from article-msgid.txt's 220 block, without Path (the node writes its own)."""
    _, steps = exchanges(rows)
    block = steps[0][1][1:-1]
    head = [l for l in block[:block.index(b'')] if not l.lower().startswith(b'path:')]
    body = block[block.index(b'') + 1:]
    return b'\r\n'.join(head + [b''] + body) + b'\r\n'


def new_article(message_id, group):
    return ('From: rfc3977-fixture@example.invalid\r\nNewsgroups: {}\r\nSubject: new article {}\r\n'
            'Message-ID: {}\r\n\r\nnew article body\r\n').format(group, message_id, message_id).encode()


@owned_ports
def _node(case, groups, extra=''):
    from tests.native_harness import Node, native_image
    node = Node(case, native_image('FN_NATIVE_HOST'), extra=extra)
    node.init(*groups)
    node.start()
    return node


def _headers(block):
    head = block.split(b'\r\n\r\n', 1)[0].split(b'\r\n')
    fields = {}
    for line in head:
        name, _, value = line.partition(b':')
        fields.setdefault(name.strip().lower(), []).append(value.strip())
    return fields


def _compare(expected, status, block, setup):
    """(ok, rule) for one reply against the transcript's lines."""
    want = expected[0]
    code = want[:3]
    if status[:3] != code:
        return False, f'status {status[:3]!r}, transcript {code!r}'
    words, got = want.split(), status.split()
    if code in (b'220', b'221', b'222', b'223'):
        if got[1:3] != words[1:3]:
            return False, 'article number and Message-ID echo (RFC 3977 6.2.1.2: 0 by Message-ID)'
        if code == b'223':
            return True, 'n and Message-ID'
        lines = expected[1:-1]
        if code in (b'220', b'221'):
            split = lines.index(b'') if b'' in lines else len(lines)
            served = _headers(block)
            for line in lines[:split]:
                name, _, value = line.partition(b':')
                if name.lower() == b'path':
                    continue        # the node's own path, by design (RFC 5537 3.2.1)
                if value.strip() not in served.get(name.strip().lower(), []):
                    return False, f'header {name!r} {value.strip()!r} not served'
            lines = lines[split + 1:] if code == b'220' else []
        if code in (b'220', b'222'):
            body = block.split(b'\r\n\r\n', 1)[1] if code == b'220' else block
            if body != b''.join(l + b'\r\n' for l in lines):
                return False, 'body octets'
        return True, 'echo, every transcript header but Path, body'
    if code == b'211':
        count, low, high = (int(x) for x in got[1:4])
        if words[1] == b'0' and got[4:5] == words[4:5] and count == 0 and high == low - 1 and low >= 1:
            return True, 'empty group: 211 0 L L-1 NAME (RFC 3977 6.1.1.2); L is the node\'s'
        return False, 'empty-group rule'
    if code == b'111':
        stamp = datetime.strptime(got[1].decode(), '%Y%m%d%H%M%S').replace(tzinfo=timezone.utc)
        if abs(stamp - datetime.now(timezone.utc)) < timedelta(hours=1):
            return True, 'yyyymmddhhmmss within an hour of the harness clock (the transcript\'s is 1999)'
        return False, 'DATE clock'
    if code in (b'230', b'231'):
        rows = [l.split()[0] for l in block.split(b'\r\n') if l]
        if code == b'231':
            wanted = sorted(g.encode() for g in setup['groups'])
            rule = 'every setup group is newer than the 1999 date (the setup; the transcript has none)'
        else:
            wanted = sorted(l for l in expected[1:-1])
            rule = 'exactly the transcript\'s Message-IDs'
        return sorted(rows) == wanted, rule
    return True, 'status code'


def rfc3977(case, directory):
    files = sorted(directory.glob('*.txt'))
    parsed = {p.name: transcript(p) for p in files}
    node = _node(case, SETUP_GROUPS)
    reader = None
    poster = node.session()
    setup = {'groups': SETUP_GROUPS, 'posts': {}}
    for message_id, payload in [(EXAMPLE_ID, example_article(parsed['article-msgid.txt']))] + [
            (m, new_article(m, g)) for m, g in sorted(NEW_ARTICLES.items())]:
        first, final = poster.post(payload)
        setup['posts'][message_id] = [first.decode('latin-1'), final and final.decode('latin-1')]
        case.assertTrue(final is not None and final.startswith(b'240'), (message_id, first, final))
    poster.close()
    rows = []
    for name, steps in parsed.items():
        greeting, script = exchanges(steps)
        if greeting and greeting[0].startswith(b'201'):
            if reader is None:
                reader = _node(case, ('fn.test',), extra='\n[posting]\nenabled = false\n')
            client = reader.session()
        else:
            client = node.session()
        if greeting:
            ok, rule = (client.greeting[:3] == greeting[0][:3], 'greeting code')
            rows.append(dict(fixture=name, command=None, expected=greeting[0], got=client.greeting, ok=ok, rule=rule))
        for command, expected in script:
            for old, new in RENAMES.items():
                command = command.replace(old, new)
                expected = [line.replace(old, new) for line in expected]
            status = client.command(command)
            block = b''
            if status[:3] in (b'220', b'221', b'222', b'230', b'231'):
                block = client.block()
            ok, rule = _compare(expected, status, block, setup)
            if status[:3] == b'205':
                try:
                    tail = client.line()
                    ok, rule = False, f'octets after 205: {tail!r}'
                except EOFError:
                    rule = '205 then the node closes (RFC 3977 5.4)'
            rows.append(dict(fixture=name, command=command, expected=expected[0], got=status,
                             block=block[:400], ok=ok, rule=rule))
        client.close(quit=False)
    return rows


# -- consumer position vectors ------------------------------------------------------------------------

def consumer_position(case, directory):
    from tests.native_harness import native_image
    image = native_image('FN_NATIVE_DEVELOPER_HOST')
    if not (image.is_file() and os.access(image, os.X_OK)):
        raise unittest.SkipTest('consumer-position needs FN_NATIVE_DEVELOPER_HOST (consumer-inspect is a developer verb)')
    env = dict(os.environ, FN_RUN_CONSUMER_INSPECT='1', FN_NATIVE_DEVELOPER_HOST=str(image))
    result = subprocess.run([sys.executable, '-c', INSPECT_RUNNER], cwd=ROOT, env=env, capture_output=True, timeout=600)
    text = result.stderr.decode('utf-8', 'replace')
    outcomes = json.loads(result.stdout.decode().strip().splitlines()[-1]) if result.stdout.strip() else {}
    rows = [dict(fixture=test, ok=outcome == 'ok', rule='tests.test_native_consumer_inspect', got=outcome)
            for test, outcome in sorted(outcomes.items())]
    vectors = sorted(p.name for p in directory.glob('*.fncu'))
    read = [v for v in vectors if v in Path(ROOT / 'tests/test_native_consumer_inspect.py').read_text()]
    rows.append(dict(fixture='every vector is asserted', ok=read == vectors, got=read, expected=vectors,
                     rule='each .fncu named by an assertion'))
    rows.append(dict(fixture='module exit', ok=result.returncode == 0, got=result.returncode, rule=text[-600:]))
    return rows


INSPECT_RUNNER = """
import json, unittest
suite = unittest.defaultTestLoader.loadTestsFromName('tests.test_native_consumer_inspect')
class R(unittest.TextTestResult):
    outcomes = {}
    def addSuccess(self, t): super().addSuccess(t); self.outcomes[t.id()] = 'ok'
    def addFailure(self, t, e): super().addFailure(t, e); self.outcomes[t.id()] = 'fail'
    def addError(self, t, e): super().addError(t, e); self.outcomes[t.id()] = 'error'
    def addSkip(self, t, r): super().addSkip(t, r); self.outcomes[t.id()] = 'skip: ' + r
unittest.TextTestRunner(resultclass=R, verbosity=2).run(suite)
print(json.dumps(R.outcomes))
"""


# -- BP golden bundles ---------------------------------------------------------------------------------

DTN7_AUTHORED = 'dtn7-rs-0.21.0-authored.bundle'
FN_AUTHORED = 'fn-authored-accepted-by-dtn7-rs-0.21.0.bundle'
DTN7_PAYLOAD = b'dtn7 -> fn, decoded as a bundle\n'
FN_PAYLOAD = b'fn -> dtn7, a bundle fn authored\n'
# The capture's inputs (golden/README.md "What each one is"): creation time, endpoints, lifetime, CRC32C,
# hop limit 32; sequence 1 is the second bundle a fresh journal authors.
DTN7_CREATION_MS = 843272141627
FN_CREATION_MS = 843272138572


def bp_golden(case, directory):
    import tempfile
    from tests.native_harness import native_image
    image = native_image('FN_NATIVE_DTN_HOST', 'build/fn-host-dtn')
    if not (image.is_file() and os.access(image, os.X_OK)):
        raise unittest.SkipTest('bp golden needs FN_NATIVE_DTN_HOST (bp decode / bp send)')
    work = Path(tempfile.mkdtemp(prefix='fn2-bp-golden-'))
    case.addCleanup(lambda: subprocess.run(['rm', '-rf', str(work)], check=False))
    rows = []
    adu = work / 'adu.out'
    decoded = subprocess.run([str(image), '--fn', 'bp', 'decode', str(directory / DTN7_AUTHORED), 'dtn://fn-b/',
                              '3600000', '2', '32', '1048576', str(DTN7_CREATION_MS + 100), '0', str(adu)],
                             capture_output=True, timeout=120)
    line = decoded.stdout.decode('latin-1').strip()
    rows.append(dict(fixture=DTN7_AUTHORED, ok=decoded.returncode == 0 and 'outcome=accepted' in line
                     and adu.exists() and adu.read_bytes() == DTN7_PAYLOAD, got=line,
                     rule='bp decode at the bundle\'s own DTN time: accepted, ADU = dtn7-rs payload'))
    payload = work / 'adu.txt'
    payload.write_bytes(FN_PAYLOAD)
    journal = work / 'journal'
    sent = []
    for _ in range(2):
        out = subprocess.run([str(image), '--fn', 'bp', 'send', '127.0.0.1', '1', str(payload), str(journal),
                              'dtn://fn-b/', 'dtn://dtn7x/incoming', '3600000', '2', '32', '1048576', '0',
                              str(FN_CREATION_MS), '60000'], capture_output=True, timeout=120)
        sent.append(out.stdout.decode('latin-1'))
    authored = journal / 'authored-1.wire'
    golden = (directory / FN_AUTHORED).read_bytes()
    rows.append(dict(fixture=FN_AUTHORED, ok=authored.exists() and authored.read_bytes() == golden,
                     got=authored.read_bytes().hex() if authored.exists() else sent[-1][-400:], expected=golden.hex(),
                     rule='bp send with the capture\'s inputs re-authors the captured octets (journalled before the socket)'))
    return rows


# -- SCRAM (RFC 7677) ---------------------------------------------------------------------------------

def scram_vectors(directory):
    from tests.sasl_client import ScramSha256
    rows = []
    for vector in sorted(directory.glob('*.json')):
        v = json.loads(vector.read_text())
        client = ScramSha256(v['user'], v['password'], cnonce=v['client_nonce'].encode())
        first = client.client_first()
        final = client.client_final(v['server_first'].encode())
        rows.append(dict(fixture=vector.name + ' client-first', ok=first == v['client_first'].encode(), got=first))
        rows.append(dict(fixture=vector.name + ' client-final', ok=final == v['client_final'].encode(), got=final))
        rows.append(dict(fixture=vector.name + ' server-final', ok=client.server_final_ok(v['server_final'].encode()),
                         got=v['server_final']))
    return rows


def scram(case, directory):
    from tests.sasl_client import ScramSha256, b64, status_data
    rows = scram_vectors(directory)
    # Live: the same client against the node (TLS: SCRAM is offered on any listener with accounts).
    from tests.native_harness import Client, client_context
    node = _scram_node(case)
    client = Client(node.tls_port, implicit_tls=client_context(), timeout=30)
    scram = ScramSha256('hu-scram', 'pencil')
    first = client.command('AUTHINFO SASL SCRAM-SHA-256 ' + b64(scram.client_first()))
    status, server_first = status_data(first)
    final = client.command(b64(scram.client_final(server_first))) if status == '383' else first
    status, server_final = status_data(final)
    rows.append(dict(fixture='live SCRAM-SHA-256', got=[first, final],
                     ok=status == '283' and server_final is not None and scram.server_final_ok(server_final),
                     rule='283 with a server signature the RFC 7677-checked client verifies'))
    client.close()
    return rows


@owned_ports
def _scram_node(case):
    from tests.native_harness import Node, native_image
    node = Node(case, native_image('FN_NATIVE_HOST'))
    node.init('fn.test')
    node.use_tls(protected_only=True)
    # As the tls_auth S target writes it (fn2/tests/surface/tls_auth/test_model_tls_auth.py TlsAuthTarget).
    node.write_config(extra=('tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n'
                             '\n[auth]\nrequired = false\nprotected_only = true\npath = "{}"\n').format(
                                 node.tls_port, node.cert, node.root / 'key.pem', node.root / 'credentials.toml'))
    secret = b'pencil'
    node.operator('principal', 'set-password', 'hu-scram', input=secret + b'\n' + secret + b'\n', expect=0, timeout=30)
    node.start()
    return node


DRIVERS = {
    'fn2/tests/model/fixtures/rfc3977': rfc3977,
    'tests/fixtures/consumer-position': consumer_position,
    'tests/bp-dtn7/golden': bp_golden,
    'fn2/tests/fixtures/scram': scram,
    'share/fn/wire-grammar.json': None,
    'fn2/tests/fixtures/web': None,
}
