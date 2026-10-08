"""One-shot structural call-site migration; fixtures protect comments/theorems."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "tools"))
import lisp_rewrite as rw


def migrate(text, names, calls):
    parsed = rw.parse(text)
    edits = []
    for form in parsed.forms:
        if not isinstance(form, rw.Lst) or len(form.items) < 4:
            continue
        if form.items[0].low != "defun" or form.items[1].low not in names:
            continue
        for old, new in calls.items():
            for hit in rw.match("_", form.items[3:], head=old):
                atom = hit.node.items[0]
                edits.append((atom.start, atom.end, new))
    return rw.write(text, edits), len(edits)


fixture = '; old\n(defun chosen (x) (old x))\n(defun kept (x) (old x))\n(defthm old-rule (old x))\n'
expected = fixture.replace('(defun chosen (x) (old x))', '(defun chosen (x) (new x))')
assert migrate(fixture, {'chosen'}, {'old': 'new'}) == (expected, 1)
assert migrate(expected, {'chosen'}, {'old': 'new'}) == (expected, 0)

plans = {
    'books/store-log-pipeline.lisp': (
        {'fn-lgk-behind-write', 'fn-lgk-behind-admitsp', 'fn-lgk-pipe-fence',
         'fn-lgk-pipe-fail', 'fn-lgk-pipe-take'},
        {'fn-lgk-fence': 'fn-lgk-pipe-kernel-fence',
         'fn-lgk-fence-failed': 'fn-lgk-pipe-kernel-fail',
         'fn-lgk-fitsp': 'fn-lgk-pipe-kernel-fitsp',
         'fn-lgk-append-octets': 'fn-lgk-pipe-kernel-octets',
         'fn-olr-take': 'fn-lgk-pipe-kernel-take'}),
    'books/owner-commit-durability.lisp': (
        {'fn-ocp-gc-start', 'fn-ocp-gc-advance'},
        {'fn-lgk-append': 'fn-lgk-pipe-kernel-append',
         'fn-lgc-of': 'fn-lgk-pipe-kernel-view'}),
}

def entry_forms(name, arguments, tag):
    args = ' '.join(arguments)
    body = f'(fn-ocp-gc-host-step x (list {tag} {" ".join(arguments[1:])}))'
    forms = (f'(defun {name} ({args})\n  {body})\n'
             f'(defthm {name}-by-definition\n'
             f'  (equal ({name} {args})\n         {body}))\n')
    assert len(rw.parse(forms).forms) == 2
    return forms

assert '(equal (sample x which)' in entry_forms('sample', ['x', 'which'], ':begin')
assert entry_forms('sample', ['x', 'which'], ':begin').count('(fn-ocp-gc-host-step x (list :begin which))') == 2

if __name__ == '__main__':
    for name, (selected, calls) in plans.items():
        path = ROOT / name
        text, count = migrate(path.read_text(), selected, calls)
        path.write_text(text)
        print(f'{name}: {count} call operators changed')
    path = ROOT / 'books/owner-commit-durability.lisp'
    parsed = rw.parse(path)
    entries = {
        'begin': ['x', 'which'], 'reserve': ['x', 'which', 'txid'],
        'take': ['x', 'which', 'record', 'txid'],
        'member': ['x', 'which', 'outcome'], 'seal': ['x', 'which'],
        'abort': ['x', 'which'],
        'pick': ['x', 'waiting'],
        'observe': ['x', 'class', 'hold', 'wait'],
        'disk': ['x', 'kind', 'reading', 'arg'],
        'note': ['x', 'a', 'b'],
    }
    text = ''
    for tag, args in entries.items():
        name = 'fn-ocp-gc-entry-' + tag
        if not rw.match('_', parsed.forms, deep=False, head='defun', name=name):
            text += entry_forms(name, args, ':' + tag)
    if text:
        before = rw.match('_', parsed.forms, deep=False, head='defun', name='fn-ocp-gc-run')[0].start
        path.write_text(rw.write(parsed.text, [(before, before, text + '\n')]))
        print('books/owner-commit-durability.lisp: derived micro-entry definitions/equations inserted')
