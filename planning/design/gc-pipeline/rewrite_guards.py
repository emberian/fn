"""Add explicit shape guards structurally; proofs remain ordinary ACL2 events."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "tools"))
import lisp_rewrite as rw


def guarded(text, guards):
    edits = []
    for hit in rw.match('_', rw.parse(text).forms, deep=False, head='defun'):
        form = hit.node
        guard = guards.get(form.items[1].low)
        if guard is None:
            continue
        decl = form.items[3]
        if isinstance(decl, rw.Lst) and decl.items[0].low == 'declare':
            xargs = next(x for x in decl.items[1:] if x.items[0].low == 'xargs')
            if any(getattr(x, 'low', '') == ':guard' for x in xargs.items):
                continue
            edits.append((xargs.items[0].end, xargs.items[0].end,
                          f' :guard {guard} :verify-guards nil'))
        else:
            edits.append((form.items[2].end, form.items[2].end,
                          f'\n  (declare (xargs :guard {guard} :verify-guards nil))'))
    return rw.write(text, edits)


fixture = '; untouched\n(defun a (x) (nth 0 x))\n(defun b (x) (declare (xargs :measure (len x))) x)\n'
fixed = guarded(fixture, {'a': '(true-listp x)', 'b': 't'})
assert '; untouched' in fixed and ':measure (len x)' in fixed
assert fixed.count(':verify-guards nil') == 2
assert guarded(fixed, {'a': '(true-listp x)', 'b': 't'}) == fixed


def verify_form(name):
    return f'''(verify-guards {name}
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
'''


assert len(rw.parse(verify_form('example')).forms) == 1

kernel = {
    'fn-lgk-pipe-make': 't',
    'fn-lgk-pipe-ks': '(true-listp p)',
    'fn-lgk-pipe-behind': '(true-listp p)',
    'fn-olr-gc-profile-fitp': '(true-listp ks)',
    'fn-olr-gc-prepare': '(and (fn-lgk-pipe-shapedp p) (true-listp records))',
}
for suffix in ('d', 'acked', 'fence', 'fail', 'ack', 'consume', 'take'):
    kernel['fn-lgk-pipe-' + suffix] = '(fn-lgk-pipe-shapedp p)'
for name in ('fn-lgk-behind-write', 'fn-lgk-behind-admitsp',
             'fn-lgk-append-behind', 'fn-lgk-behind-state', 'fn-lgk-behind-effect'):
    kernel[name] = '(fn-lgk-pipe-shapedp p)'

if __name__ == '__main__':
    p = ROOT / 'books/store-log-pipeline.lisp'
    p.write_text(guarded(p.read_text(), kernel))
    p = ROOT / 'books/owner-commit-durability.lisp'
    names = ('stop start io append-issue collect advance begin reserve take '
             'member seal-extent seal').split()
    owner = {'fn-ocp-gc-' + name: '(fn-ocp-gc-shapedp x)' for name in names}
    owner['fn-ocp-gc-host-step'] = '(and (fn-ocp-gc-shapedp x) (true-listp event))'
    for hit in rw.match('_', rw.parse(p).forms, deep=False, head='defun'):
        name = hit.node.items[1].low
        if name.startswith('fn-ocp-gc-entry-'):
            owner[name] = '(fn-ocp-gc-shapedp x)'
    for name in ('profilep', 'init', 'event-action', 'event-state', 'pick'):
        owner['fn-ocp-gc-' + name] = 't'
    p.write_text(guarded(p.read_text(), owner))
    parsed = rw.parse(p)
    verified = {h.node.items[1].low for h in
                rw.match('_', parsed.forms, deep=False, head='verify-guards')}
    order = ('io append-issue collect advance begin reserve take member '
             'seal-extent seal host-step').split()
    order = ['fn-ocp-gc-' + name for name in order]
    order += [h.node.items[1].low for h in
              rw.match('_', parsed.forms, deep=False, head='defun')
              if h.node.items[1].low.startswith('fn-ocp-gc-entry-')]
    added = ''.join(verify_form(name) for name in order if name not in verified)
    if added:
        p.write_text(rw.write(parsed.text, [(len(parsed.text), len(parsed.text), added)]))
