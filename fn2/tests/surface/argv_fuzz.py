"""F for operator and store_ops: seeded argv mutation against a live node, judged by the families' models (H7d).

    python3 -m fn2.tests.surface.argv_fuzz --family operator|store_ops --target fn1|fake --seeds A..B
        --out DIR [--seconds S] [--steps N] [--plant P]

RELEASE-PLAN §2.2 F row: "argv fuzz (every verb with malformed arguments -> usage exit, never a crash)".
Each seed starts one node (the families' S targets, STORE_INIT), then sends N argv calls, each a mutation of
a well-formed call of a modelled verb. Every reply is judged twice:

  universal (every call): the exit is a class of the exit table (tools/outcome_codes.py), never `fault`
    and never a signal; no Lisp debugger or backtrace on any stream; the tagged result line, when the verb
    prints one, carries the exit's word (operator_model.result_problem); the call returns within its bound.
  by mutation:
    empty-token, non-ascii   exit 5 `ARGV-MALFORMED` (specs/native-admin.md:8-15, every verb)
    unknown-verb, verb-alone exit 5 usage (the verb table, docs/operator.md:1232-1242)
    value                    the family model's verdict (OperatorModel.verdict / StoreOpsModel.classify),
                             with its recorded fn1 adjudications; the model's state follows every reply
    extra-argument           store_ops: StoreOpsModel's malformed class (usage, the sub-verb's tag)
    overlong                 a 600-octet token: universal only (refusal or usage, never a crash)

A finding is a row in DIR/findings.jsonl; the exit status is 1 when there is one, else 0. DIR/summary.json
counts calls by mutation and verb. `--target fake` runs the families' fake targets (fn2/tests/model
test_operator_model.FakeTarget; for store_ops a model-rendered fake), and `--plant` gives the mutation
controls: crash-on-overlong (a backtrace and signal on a long token), fault-on-empty (an empty token answered
`fault`), accept-bad-capacity / store-accept-extra (a malformed call accepted).
"""
import argparse
from contextlib import ExitStack
import json
import os
from pathlib import Path
import random
import re
import signal
import sys
import time
import unittest

from fn2.tests.model.operator_model import OperatorModel, Request as OperatorRequest, WORDS, result_line, result_problem
from tools.outcome_codes import EXIT

PLANTS = ('crash-on-overlong', 'fault-on-empty', 'accept-bad-capacity', 'store-accept-extra')
CRASH = re.compile(r'debugger invoked|Unhandled [A-Z-]+|Backtrace for|fatal error|Heap exhausted|INFO: Control stack')
OPERATOR_BASES = (
    ('group create', ('fz.new',)), ('group retire', ('hz.test',)), ('group describe', ('hz.test', 'a', 'description')),
    ('group policy', ('hz.test', 'y')), ('group moderate', ('hz.mod', '--moderators', 'hz-mod', '--queue', 'hz.mod.moderation')),
    ('moderation list', ('hz.mod',)), ('motd set', ('hello',)), ('motd clear', ()), ('capacity', ('4096',)),
    ('retention set', ('keep-forever',)), ('retention expire', ('hz.test', 'keep', '10')),
    ('account invite', ()), ('account list', ()), ('account access', ('show',)), ('principal list', ()),
    ('account delete', ('nobody',)), ('principal delete', ('nobody',)))
REQUIRES_ARGS = {v for v, a in OPERATOR_BASES if a}
VALUES = ('', '0', '-1', '007', '4294967295', '4294967296', '1e3', 'y', 'n', 'x', 'hz.test', 'hz.mod',
          'example.test', 'poster', 'a..b', 'UPPER.Case', '*', '[', 'release-after', 'keep-forever',
          'clear', 'purge', 'octets', 'z' * 64)
# Flag names are not values here: a value position given `--queue` or `--off` asks how the verb's flag
# parser reads a flag-shaped value, which no spec line decides (out of this driver's scope).
# Recorded target replies (fn1 only), each backed by an observed reply and a spec line.
ADJUDICATIONS = (
    dict(group='A01', kind='non-ascii', target='fn1', exit=5, text='fn-host: error: operator argument is not ASCII',
         spec='specs/native-admin.md:12-15 (a malformed word, empty or not ASCII, is refused by name, ARGV-MALFORMED)',
         observed='the host refuses a non-ASCII word before ACL2 judges the argv: exit 5 with its own error line and '
                  'no tagged `usage operator ... ARGV-MALFORMED` line (host/native/operator.lisp '
                  'fnn-operator-argv-octets); an empty word is ARGV-MALFORMED as specified',
         **{'class': 'fn1-bug'}),
)
# Words no operator verb is (`help` and `policy` are verbs; H7d's first run sent them as noise).
NOISE_VERBS = ('frobnicate', 'grup', 'group-create', 'status!', 'xyzzy', 'Group', '--version')


class Session:
    """One node (or fake) for one seed: raw argv calls plus the model-judged ones."""

    def __init__(self, family, target, plant):
        self.family, self.target_name, self.plant = family, target, plant
        self.stack = ExitStack()
        self.case = unittest.TestCase()
        self.case.addCleanup = self.stack.callback
        if family == 'operator':
            self.model = OperatorModel()
            if target == 'fake':
                from fn2.tests.model.test_operator_model import FakeTarget
                self.target = TotalFake(FakeTarget(self.case), OperatorModel())
            else:
                from fn2.tests.surface.operator.test_model_operator import OperatorTarget
                self.target = OperatorTarget(self.case)
        else:
            from fn2.tests.model.store_ops_model import StoreOpsModel
            self.model = StoreOpsModel()
            if target == 'fake':
                self.target = StoreFake(self.model)
            else:
                from fn2.tests.surface.store_ops.test_model_store_ops import StoreTarget
                self.target = StoreTarget(self.case)

    def close(self):
        self.stack.close()

    def raw(self, words, timeout=5):
        """(reply, elapsed) of argv WORDS as `operator CONFIG WORDS...`."""
        start = time.monotonic()
        if self.target_name == 'fake':
            reply = self.fake_raw(words)
        else:
            result = self.target.node.operator(*words, timeout=timeout)
            reply = dict(exit=result.returncode, text=(result.stdout + result.stderr).decode('utf-8', 'replace'))
        return self.planted(words, reply), time.monotonic() - start

    def fake_raw(self, words):
        if any(not w or not w.isascii() for w in words):
            return dict(exit=5, text='usage operator request ARGV-MALFORMED\n')
        if self.family == 'store_ops':
            return self.target.raw(words)
        for verb, _ in OPERATOR_BASES:
            n = len(verb.split())
            if tuple(words[:n]) == tuple(verb.split()):
                if not words[n:] and verb in REQUIRES_ARGS:
                    break
                try:
                    return self.target.call(OperatorRequest(verb, tuple(words[n:])))
                except (IndexError, ValueError, KeyError):
                    return dict(exit=5, text=f'usage operator {verb.split()[0]} SYNTAX\n')
        return dict(exit=5, text='usage operator request UNKNOWN-VERB\n')

    def planted(self, words, reply):
        if self.plant == 'crash-on-overlong' and any(len(w) > 500 for w in words):
            return dict(exit=-signal.SIGABRT, text='Unhandled SIMPLE-ERROR in thread "main thread"\nBacktrace for: x\n')
        if self.plant == 'fault-on-empty' and '' in words:
            return dict(exit=int(EXIT.FAULT), text='fault operator request INTERNAL\n')
        if self.plant == 'accept-bad-capacity' and words[:1] == ('capacity',) and reply['exit'] == 5:
            return dict(exit=0, text='accepted operator capacity\n')
        if self.plant == 'store-accept-extra' and 'hz-extra-argument' in words and reply['exit'] == 5:
            return dict(exit=0, text='accepted operator store\n')
        return reply


class TotalFake:
    """The operator S fake (reports and state) with refusals rendered from a shadow OperatorModel, so the
    unmutated control agrees with the oracle; a call shape neither models is usage, as a broken shape is.
    Mutation controls only: the live oracle is the model against the node."""

    def __init__(self, fake, shadow):
        self.fake, self.shadow = fake, shadow

    def call(self, r):
        try:
            code, reason, _ = self.shadow.verdict(r)
        except (IndexError, ValueError, KeyError):
            return dict(exit=5, text=f'usage operator {r.verb.split()[0]} SYNTAX\n')
        if code:
            return dict(exit=code, text=f'{WORDS[code]} operator {r.verb.split()[0]} (ADMINISTRATION {reason.upper()})\n')
        reply = self.fake.call(r)
        self.shadow.apply(r, reply)
        return reply


class StoreFake:
    """A model-rendered store_ops fake (mutation controls only; the live oracle is StoreOpsModel)."""

    def __init__(self, model):
        self.model = model

    def call(self, r):
        code, reason, _ = self.model.classify(r)
        if code:
            return dict(exit=code, text=f'{WORDS[code]} operator store {reason.upper()}\n')
        text = ''
        if r.verb == 'inspect':
            text = f'inspect {r.argument}\n'
        return dict(exit=0, text=text + 'accepted operator store\n')

    def raw(self, words):
        if words[:1] == ('store',) and (len(words) < 2 or words[1] not in STORE_VERBS):
            return dict(exit=5, text='usage operator store INVALID-STORE-COMMAND\n')
        if words[:1] not in (('store',), ('status',), ('recover',)):
            return dict(exit=5, text='usage operator request UNKNOWN-VERB\n')
        return dict(exit=0, text='accepted operator store\n')


STORE_VERBS = ('inspect', 'export', 'import', 'compact', 'checkpoint', 'bless-snapshot', 'reclaim')


def universal(reply, elapsed, bound, *, tagged):
    code = reply['exit']
    if code < 0:
        return f'killed by signal {-code}'
    if code not in {int(e) for e in EXIT}:
        return f'exit {code} is not a class of the exit table'
    if code == EXIT.FAULT:
        return 'fault on an argv mutation (a malformed call is usage or a refusal, never a fault)'
    if CRASH.search(reply['text']):
        return 'debugger or backtrace on the CLI streams: ' + CRASH.search(reply['text']).group()
    if elapsed > bound:
        return f'took {elapsed:.1f} s (bound {bound} s)'
    line = result_line(reply['text'])
    if line is None and tagged:
        return 'no tagged result line'
    if line is not None and line[0] != WORDS.get(code):
        return f'tagged line word {line[0]!r} for exit {code}'
    return None


def operator_calls(rng, steps):
    for _ in range(steps):
        verb, args = rng.choice(OPERATOR_BASES)
        kind = rng.choice(('value', 'value', 'value', 'empty-token', 'non-ascii', 'unknown-verb', 'verb-alone', 'overlong'))
        args = list(args)
        if kind in ('value', 'empty-token', 'non-ascii', 'overlong') and not args:
            kind = 'unknown-verb' if kind != 'value' else 'value'
        values = [i for i, a in enumerate(args) if not a.startswith('--')]   # never a flag's own name
        if kind == 'value' and values:
            args[rng.choice(values)] = rng.choice(VALUES[1:])
        elif kind == 'empty-token':
            args[rng.randrange(len(args))] = ''
        elif kind == 'non-ascii':
            i = rng.randrange(len(args))
            args[i] = 'é' + args[i]
        elif kind == 'overlong':
            args[rng.randrange(len(args))] = 'o' * 600
        if kind == 'unknown-verb':
            yield kind, None, (rng.choice(NOISE_VERBS),) + tuple(args)
        elif kind == 'verb-alone':
            yield (kind, None, tuple(verb.split())) if verb in REQUIRES_ARGS else ('value', verb, ())
        elif kind == 'value':
            yield kind, verb, tuple(args)
        else:
            yield kind, verb, tuple(verb.split()) + tuple(args)     # a raw call carries its verb words


def store_calls(rng, steps):
    for _ in range(steps):
        kind = rng.choice(('inspect', 'inspect-group', 'extra-argument', 'empty-token', 'non-ascii', 'unknown-verb', 'overlong'))
        if kind == 'inspect':
            yield kind, None, dict(verb='inspect', argument=rng.choice(('<absent@hz.invalid>', '<a@b>', 'x', '<' + 'q' * 40 + '@x>')))
        elif kind == 'inspect-group':
            yield kind, None, dict(verb='inspect-group', argument=rng.choice(('hz.test', 'hz.none', 'x.y', 'fz.new')))
        elif kind == 'extra-argument':
            yield kind, None, dict(verb=rng.choice(('status', 'recover', 'compact', 'checkpoint')), malformed=True)
        elif kind == 'unknown-verb':
            yield kind, None, ('store', rng.choice(('frob', 'inspekt', 'EXPORT', '-')))
        else:
            word = {'empty-token': '', 'non-ascii': 'éx', 'overlong': '<' + 'o' * 600 + '@x>'}[kind]
            yield kind, None, ('store', 'inspect', word)


def run_seed(args, seed, findings, counts):
    rng = random.Random(seed)
    session = Session(args.family, args.target, args.plant)
    try:
        calls = operator_calls(rng, args.steps) if args.family == 'operator' else store_calls(rng, args.steps)
        for kind, verb, spec in calls:
            counts[kind] = counts.get(kind, 0) + 1
            row = dict(seed=seed, kind=kind)
            expected = None
            if args.family == 'operator' and kind == 'value':
                try:
                    expected = session.model.rule(verb, *spec)
                except (IndexError, ValueError, KeyError):
                    # A shape outside the model's grammar (a flag's value moved): universal judgement only.
                    counts['model-silent'] = counts.get('model-silent', 0) + 1
            if expected is not None and args.family == 'operator':
                words = expected.request.words
                reply, elapsed = timed(session.target.call, expected.request)
                reply = session.planted(words, reply)
                problem = universal(reply, elapsed, 5, tagged=True)
                if problem is None:
                    target = args.target if args.target != 'fake' else 'fake'
                    if expected.recorded_difference(reply, target) is None:
                        problem = expected.check(reply)
                    if problem is None:
                        expected.update(reply, target)
            elif args.family == 'store_ops' and isinstance(spec, dict):
                expected = session.model.rule(**spec)
                reply, elapsed = timed(session.target.call, expected.request)
                words = ('store', spec['verb']) + (('hz-extra-argument',) if spec.get('malformed') else ())
                reply = session.planted(words, reply)
                problem = universal(reply, elapsed, 10, tagged=False) or expected.check(reply)
            else:
                words = spec
                reply, elapsed = session.raw(words)
                problem = universal(reply, elapsed, 5, tagged=args.family == 'operator')
                if problem is None and kind in ('empty-token', 'non-ascii'):
                    problem = result_problem(reply, 5, 'argv-malformed', tagged=args.family == 'operator')
                elif problem is None and kind in ('unknown-verb', 'verb-alone'):
                    problem = result_problem(reply, 5, None, tagged=args.family == 'operator')
                # (a model-silent value mutation keeps the universal judgement only)
            if problem:
                row.update(words=list(words), reply=reply, problem=problem)
                recorded = next((a['group'] for a in ADJUDICATIONS if a['kind'] == kind and a['target'] == args.target
                                 and reply['exit'] == a['exit'] and reply['text'].strip() == a['text']), None)
                if recorded:
                    counts['recorded ' + recorded] = counts.get('recorded ' + recorded, 0) + 1
                else:
                    findings.append(row)
    finally:
        session.close()


def timed(call, request):
    start = time.monotonic()
    reply = call(request)
    return reply, time.monotonic() - start


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--family', choices=('operator', 'store_ops'), required=True)
    p.add_argument('--target', choices=('fn1', 'fn2', 'fake'), required=True)
    p.add_argument('--seeds', default='0..19')
    p.add_argument('--steps', type=int, default=20)
    p.add_argument('--seconds', type=float, default=float('inf'))
    p.add_argument('--plant', choices=PLANTS)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args(argv)
    if args.plant and args.target != 'fake':
        p.error('plants require --target fake')
    start, end = map(int, args.seeds.split('..'))
    args.out.mkdir(parents=True, exist_ok=True)
    if args.target != 'fake':
        os.environ['FN2_SURFACE_TARGET'] = args.target
        from fn2.tests.harness import shim
        shim.install(args.target)
    findings, counts, seeds_run = [], {}, 0
    deadline = time.monotonic() + args.seconds
    for seed in range(start, end + 1):
        if time.monotonic() >= deadline:
            break
        run_seed(args, seed, findings, counts)
        seeds_run += 1
    (args.out / 'findings.jsonl').write_text(''.join(json.dumps(f, default=repr) + '\n' for f in findings))
    summary = dict(family=args.family, target=args.target, plant=args.plant, seeds=args.seeds, seeds_run=seeds_run,
                   steps=args.steps, calls=sum(counts.values()), by_mutation=counts, findings=len(findings))
    (args.out / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    print(json.dumps(summary))
    return 1 if findings else 0


if __name__ == '__main__':
    sys.exit(main())
