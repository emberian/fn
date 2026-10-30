"""F for config_limits: seeded fn.toml mutation through the image's `config check` (H7e).

    python3 -m fn2.tests.surface.config_fuzz --target fn1|fn2|fake --seeds A..B --out DIR [--seconds S]
        [--plant P]

RELEASE-PLAN §2.2's F row for config: "`fn.toml` fuzz (every key with bad values -> a named refusal to
start)". The subject is `fn-native-config-load`, reached the way every verb reaches it: `fn --fn operator
PATH show` loads the profile as `run` does and prints it, exit 0, or refuses it as usage, exit 5
(specs/native-config.md: "maps a refused configuration load to :usage and CLI exit 5"). The diagnostic
`config check` is not the subject: it reads through the generic bounded reader, which answers an
oversized profile with a fault (exit 4), where every operator verb names the bound as usage (H7e probe).

Each case is a well-formed profile drawn from specs/native-config.md's documented table (store.path
required; listener host/port/tls_cert/tls_key; auth required/protected_only/path; posting enabled/agent;
anchor server; acl2 path/slots; log path; control path), with at most one mutation whose verdict the spec
decides. The expectation is the generator's, from the spec's sentences; the image must agree:

  accepted   the unmutated profile; a comment line or blank line added; keys reordered within a table
  refused    a non-ASCII octet (in a comment, a key or a value); more than 128 lines; more than 16,384
             octets; a duplicate table; a duplicate key; an unknown key in a known table; an unknown table;
             a value of the wrong type (a quoted string for a Boolean or a number, a number for a Boolean or a
             path, `yes` for a Boolean); a backslash or an inline comment in a quoted value; a TOML feature
             outside the profile (an array, an inline table, a float, a single-quoted string, a multi-line
             string, a dotted key); store.path absent or empty; listener port 0 or above 65535; the wildcard
             host 0.0.0.0; tls_cert without tls_key; a path over 512 octets; an anchor name over 128

Every reply is also judged universally: exit 0, or exit 5 with a usage line naming the refusal; never a
fault, a signal or a backtrace. A disagreement is a row in DIR/findings.jsonl (exit 1). `--target fake`
checks a small independent reading of the same sentences (mutation controls: `--plant accept-non-ascii`,
`accept-duplicate-key`, `refuse-comment`).
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

PLANTS = ('accept-non-ascii', 'accept-duplicate-key', 'refuse-comment')
CRASH = re.compile(r'debugger invoked|Unhandled [A-Z-]+|Backtrace for|fatal error|Heap exhausted')
# The documented surface (specs/native-config.md's table) with a well-formed value maker per key.
KEYS = {
    'store': {'path': lambda r: q('/tmp/fz-store-' + str(r.randrange(1000)))},
    'listener': {'host': lambda r: q(r.choice(['127.0.0.1', 'localhost', '::1', '10.1.2.3'])),
                 'port': lambda r: str(r.choice([1, 119, 1119, 65535, r.randrange(1, 65536)]))},
    'auth': {'required': lambda r: r.choice(['true', 'false']), 'protected_only': lambda r: 'false',
             'path': lambda r: q('/tmp/fz-auth.toml')},
    'posting': {'enabled': lambda r: r.choice(['true', 'false'])},
    'anchor': {'server': lambda r: q('news.example.invalid')},
    'acl2': {'path': lambda r: q('/opt/acl2/saved_acl2'), 'slots': lambda r: str(r.randrange(1, 65))},
    'log': {'path': lambda r: q('/tmp/fz.log')},
    'control': {'path': lambda r: q('/tmp/fz-control.sock')},
}
TYPES = {('listener', 'port'): 'nat', ('acl2', 'slots'): 'nat', ('auth', 'required'): 'bool',
         ('auth', 'protected_only'): 'bool', ('posting', 'enabled'): 'bool'}
ACCEPTED = ('none', 'comment', 'blank', 'reorder')
REFUSED = ('non-ascii', 'lines-129', 'octets-16385', 'duplicate-table', 'duplicate-key', 'unknown-key',
           'unknown-table', 'wrong-type', 'backslash', 'inline-comment', 'toml-feature', 'no-store',
           'empty-store', 'port-0', 'port-65536', 'wildcard-host', 'unpaired-tls', 'long-path', 'long-anchor')


def q(text):
    return '"' + text + '"'


def profile(rng):
    """[(table, [(key, value)])], store first, every documented table equally likely."""
    tables = [('store', [('path', KEYS['store']['path'](rng))])]
    for table in rng.sample([t for t in KEYS if t != 'store'], rng.randrange(0, 4)):
        keys = rng.sample(sorted(KEYS[table]), rng.randrange(1, len(KEYS[table]) + 1))
        tables.append((table, [(k, KEYS[table][k](rng)) for k in keys]))
    return tables


def render(tables, extra_lines=()):
    lines = []
    for table, pairs in tables:
        lines.append(f'[{table}]')
        lines += [f'{k} = {v}' for k, v in pairs]
    return '\n'.join(lines + list(extra_lines)) + '\n'


def case(rng):
    """(mutation, expected 'accepted'|'refused', profile octets)."""
    tables = profile(rng)
    kind = rng.choice(ACCEPTED + REFUSED + REFUSED)
    pick = lambda: rng.randrange(len(tables))
    if kind == 'comment':
        return kind, 'accepted', render(tables, ['# a comment: ' + 'c' * rng.randrange(60)]).encode()
    if kind == 'blank':
        return kind, 'accepted', render(tables, ['', '   ']).encode()
    if kind == 'reorder':
        for _, pairs in tables:
            rng.shuffle(pairs)
        rng.shuffle(tables)
        return kind, 'accepted', render(tables).encode()
    if kind == 'none':
        return kind, 'accepted', render(tables).encode()
    if kind == 'non-ascii':
        where = rng.choice(('comment', 'value', 'key'))
        if where == 'comment':
            text = render(tables, ['# café'])
        elif where == 'value':
            tables[0] = ('store', [('path', q('/tmp/café'))])
            text = render(tables)
        else:
            text = render(tables, ['päth = "x"'])
        return kind, 'refused', text.encode('utf-8')
    if kind == 'lines-129':
        return kind, 'refused', render(tables, ['# filler'] * 130).encode()
    if kind == 'octets-16385':
        return kind, 'refused', render(tables, ['# ' + 'x' * 200] * 90).encode()
    if kind == 'duplicate-table':
        table, pairs = tables[pick()]
        return kind, 'refused', (render(tables) + render([(table, pairs)])).encode()
    if kind == 'duplicate-key':
        i = pick()
        table, pairs = tables[i]
        tables[i] = (table, pairs + [pairs[0]])
        return kind, 'refused', render(tables).encode()
    if kind == 'unknown-key':
        i = pick()
        tables[i] = (tables[i][0], tables[i][1] + [('zz_fuzz_key', '"x"')])
        return kind, 'refused', render(tables).encode()
    if kind == 'unknown-table':
        return kind, 'refused', render(tables + [('zz_fuzz', [('key', '"x"')])]).encode()
    if kind == 'wrong-type':
        (table, key), typ = rng.choice(sorted(TYPES.items()))
        bad = rng.choice({'nat': ['"7"', 'true', '-1', '123456'], 'bool': ['"true"', '1', 'yes', 'TRUE']}[typ])
        others = [(t, pairs) for t, pairs in tables if t != table]
        mine = [(k, v) for t, pairs in tables if t == table for k, v in pairs if k != key]
        return kind, 'refused', render(others + [(table, mine + [(key, bad)])]).encode()
    if kind == 'backslash':
        tables[0] = ('store', [('path', q('/tmp/a\\\\b'))])
        return kind, 'refused', render(tables).encode()
    if kind == 'inline-comment':
        tables[0] = ('store', [('path', q('/tmp/x') + ' # here')])
        return kind, 'refused', render(tables).encode()
    if kind == 'toml-feature':
        value = rng.choice(['["a", "b"]', '{ a = 1 }', '1.5', "'/tmp/x'", '"""/tmp/x"""', '1979-05-27'])
        if rng.random() < 0.2:
            return kind, 'refused', (render(tables) + 'store.path = "/tmp/y"\n').encode()
        return kind, 'refused', render([('store', [('path', value)])] + tables[1:]).encode()
    if kind == 'no-store':
        return kind, 'refused', render(tables[1:] or [('posting', [('enabled', 'true')])]).encode()
    if kind == 'empty-store':
        return kind, 'refused', render([('store', [('path', '""')])] + tables[1:]).encode()
    listener = lambda pairs: [(t, p) for t, p in tables if t != 'listener'] + [('listener', pairs)]
    if kind == 'port-0':
        return kind, 'refused', render(listener([('port', '0')])).encode()
    if kind == 'port-65536':
        return kind, 'refused', render(listener([('port', '65536')])).encode()
    if kind == 'wildcard-host':
        return kind, 'refused', render(listener([('host', '"0.0.0.0"')])).encode()
    if kind == 'unpaired-tls':
        return kind, 'refused', render(listener([('tls_cert', '"/tmp/cert.pem"')])).encode()
    if kind == 'long-path':
        return kind, 'refused', render([('store', [('path', q('/' + 'p' * 512))])] + tables[1:]).encode()
    if kind == 'long-anchor':
        return kind, 'refused', render([(t, p) for t, p in tables if t != 'anchor'] +
                                       [('anchor', [('server', q('a' * 129))])]).encode()
    raise ValueError(kind)


def fake_check(octets, plant=None):
    """An independent small reading of specs/native-config.md for the mutation controls."""
    try:
        text = octets.decode('ascii')
    except UnicodeDecodeError:
        return (0, 'accepted config\n') if plant == 'accept-non-ascii' else (1, 'refused config: INVALID\n')
    lines = text.split('\n')[:-1]
    if len(octets) > 16384 or len(lines) > 128:
        return 1, 'refused config: INVALID\n'
    seen, table, values = set(), None, {}
    for line in lines:
        s = line.strip()
        if not s:
            continue
        if s.startswith('#'):
            if plant == 'refuse-comment':
                return 1, 'refused config: INVALID\n'
            continue
        m = re.fullmatch(r'\[([a-z0-9_]+)\]', s)
        if m:
            table = m.group(1)
            if table not in KEYS or (table, None) in seen:
                return 1, 'refused config: INVALID\n'
            seen.add((table, None))
            continue
        m = re.fullmatch(r'([a-z_]+) = (true|false|[0-9]{1,5}|"[ !#-\[\]-~]*")', s)
        if not m or table is None or m.group(1) not in KEYS[table]:
            return 1, 'refused config: INVALID\n'
        if (table, m.group(1)) in seen and plant != 'accept-duplicate-key':
            return 1, 'refused config: INVALID\n'
        seen.add((table, m.group(1)))
        values[(table, m.group(1))] = m.group(2)
    for (table, key), typ in TYPES.items():
        v = values.get((table, key))
        if v is not None and (typ == 'nat') != bool(re.fullmatch(r'[0-9]+', v)) or (
                v is not None and typ == 'bool' and v not in ('true', 'false')):
            return 1, 'refused config: INVALID\n'
    strings = {k: v[1:-1] for k, v in values.items() if v.startswith('"')}
    for k, v in values.items():
        if k not in TYPES and not v.startswith('"'):
            return 1, 'refused config: INVALID\n'
    if not strings.get(('store', 'path')) or any(len(v) > 512 for v in strings.values()):
        return 1, 'refused config: INVALID\n'
    if len(strings.get(('anchor', 'server'), '')) > 128:
        return 1, 'refused config: INVALID\n'
    port = int(values.get(('listener', 'port'), '1119'))
    if not 1 <= port <= 65535 or strings.get(('listener', 'host')) == '0.0.0.0':
        return 1, 'refused config: INVALID\n'
    if (('listener', 'tls_cert') in values) != (('listener', 'tls_key') in values):
        return 1, 'refused config: INVALID\n'
    return 0, 'accepted config\n'


def check(target, image, octets, directory, plant):
    if target == 'fake':
        code, text = fake_check(octets, plant)
        return dict(exit=5 if code else 0, text=text if not code else 'usage operator show (CONFIGURATION INVALID)\n'), 0.0
    path = Path(directory) / 'fn.toml'
    path.write_bytes(octets)
    start = time.monotonic()
    result = subprocess.run([str(image), '--fn', 'operator', str(path), 'show'], capture_output=True, timeout=60)
    return dict(exit=result.returncode, text=(result.stdout + result.stderr).decode('utf-8', 'replace')), \
        time.monotonic() - start


def judge(expected, reply):
    code, text = reply['exit'], reply['text']
    if code < 0:
        return f'killed by signal {-code}'
    if CRASH.search(text):
        return 'debugger or backtrace: ' + CRASH.search(text).group()
    if code not in (0, 5):
        return f'exit {code} (a profile is shown, exit 0, or refused as usage, exit 5)'
    if code == 5 and not re.search(r'^(usage operator \S+|\S+: error: )', text, re.M):
        return 'exit 5 without a usage line naming the refusal'
    if (code == 0) != (expected == 'accepted'):
        return f'expected {expected}'
    return None


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--target', choices=('fn1', 'fn2', 'fake'), required=True)
    p.add_argument('--seeds', default='0..999')
    p.add_argument('--seconds', type=float, default=float('inf'))
    p.add_argument('--plant', choices=PLANTS)
    p.add_argument('--image', type=Path)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args(argv)
    if args.plant and args.target != 'fake':
        p.error('plants require --target fake')
    image = args.image or Path(os.environ.get('FN_NATIVE_HOST', '/nonexistent'))
    if args.target != 'fake' and not image.is_file():
        p.error('a live target needs --image or FN_NATIVE_HOST')
    start, end = map(int, args.seeds.split('..'))
    args.out.mkdir(parents=True, exist_ok=True)
    findings, counts, deadline, run = [], {}, time.monotonic() + args.seconds, 0
    with tempfile.TemporaryDirectory(prefix='fn2-config-fuzz-') as directory:
        for seed in range(start, end + 1):
            if time.monotonic() >= deadline:
                break
            kind, expected, octets = case(random.Random(seed))
            counts[kind] = counts.get(kind, 0) + 1
            reply, _ = check(args.target, image, octets, directory, args.plant)
            run += 1
            problem = judge(expected, reply)
            if problem:
                findings.append(dict(seed=seed, mutation=kind, expected=expected, reply=reply, problem=problem,
                                     profile=octets.decode('utf-8', 'replace')[:2000]))
    (args.out / 'findings.jsonl').write_text(''.join(json.dumps(f) + '\n' for f in findings))
    summary = dict(target=args.target, plant=args.plant, seeds=args.seeds, cases=run, by_mutation=counts,
                   findings=len(findings))
    (args.out / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    print(json.dumps(summary))
    return 1 if findings else 0


if __name__ == '__main__':
    sys.exit(main())
