"""Register derived entries from their actual book guards; no copied guard table."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as rw


def entry(text, form, kinds):
    name = form.items[1].text
    args = [a.text for a in form.items[2].items]
    checks = []
    for hit in rw.match('(xargs ?*xs)', [form]):
        xs = hit.node.items
        for i, node in enumerate(xs[:-1]):
            if getattr(node, 'text', '').lower() == ':guard':
                guard = xs[i + 1]
                for check in rw.match('(?pred ?arg)', [guard]):
                    pred, arg = check.node.items
                    if getattr(pred, 'text', '') in kinds and getattr(arg, 'text', '') in args:
                        checks.append((arg.text, pred.text))
    checks.sort(key=lambda c: args.index(c[0]))
    k = ' '.join(f'({a} {p})' for a, p in checks)
    thm = 'fn-ocp-gc-open-linked' if name == 'fn-ocp-gc-open' else name + '-by-definition'
    return f'(definterface {name}\n  :class :common-lisp-compliant\n  :kinds ({k})\n  :keystones ({thm}))'


fixture = '(defun fn-ocp-gc-entry-test (x n) (declare (xargs :guard (and (true-listp x) (natp n)))) x)'
assert ':kinds ((x true-listp) (n natp))' in entry(fixture, rw.parse(fixture).forms[0], {'true-listp', 'natp'})
assert ':kinds ()' in entry(fixture, rw.parse(fixture).forms[0], set())

if __name__ == '__main__':
    # The registry derives only recognizers named by *fn-entry-guard-kinds*.
    # The private SHAPEDP guard is carried from OPEN and preserved steps;
    # it is not registered as a per-call whole-state validation.
    catalog = rw.parse((ROOT / 'books/payload-kinds.lisp').read_text())
    hit = rw.match('_', catalog.forms, head='defconst', name='*fn-entry-guard-kinds*', deep=False)[0]
    kinds = {n.items[0].text for n in hit.node.items[2].node.items}
    target = ROOT / 'host/interfaces.lisp'
    original = target.read_text()
    present = {h.node.items[1].text for h in rw.match('_', rw.parse(original).forms, head='definterface', deep=False)}
    additions = []
    for filename in ['owner-commit-durability-steps.lisp', 'owner-commit-durability-open.lisp']:
        text = (ROOT / 'books' / filename).read_text()
        for h in rw.match('_', rw.parse(text).forms, head='defun', deep=False):
            name = h.node.items[1].text
            if (name.startswith('fn-ocp-gc-entry-') or name == 'fn-ocp-gc-open') and name not in present:
                additions.append(entry(text, h.node, kinds))
    if additions:
        target.write_text(rw.write(original, [(len(original), len(original), '\n; Derived pipeline entries, guard kinds extracted by register_entries.py.\n' + '\n\n'.join(additions) + '\n')]))
