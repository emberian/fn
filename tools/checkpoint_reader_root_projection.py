#!/usr/bin/env python3
"""Project named reader proof interfaces, retaining the current root runtime.

No checkpoint table, allocator, codec, BOOT or evidence-provider file is copied.
The qualified donor supplies proof statements; the new closure needs its own gate.
"""
from pathlib import Path
import subprocess
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]
BASE = 'fa9451c27'
DONOR = '6347c86a91f239b055f20af39f15cead69ecf8af'


def source(revision, path):
    return subprocess.check_output(['git', 'show', revision+':'+path], cwd=ROOT, text=True)


def unique(text, pattern):
    nodes = lr.match(pattern, lr.parse(text).forms)
    assert len(nodes) == 1, (pattern, len(nodes))
    return nodes[0].node


def raw(text, node):
    return text[node.start:node.end]


def norm(node):
    if isinstance(node, lr.Lst):
        items = node.items
        if items and getattr(items[0], 'low', None) == 'xargs':
            out = [norm(items[0])]
            i = 1
            while i < len(items):
                if getattr(items[i], 'low', None) in (':hints', ':guard-hints'):
                    i += 2
                    continue
                out.append(norm(items[i])); i += 1
            return tuple(out)
        return tuple(map(norm, items))
    if isinstance(node, lr.Pre):
        return node.prefix, norm(node.node)
    return node.text if isinstance(node, lr.Str) else node.low


def export_local(text, pattern):
    node = unique(text, '(local '+pattern+')')
    return raw(text, node.items[1])


def interfaces(donor):
    # A distinct narrow name leaves the root's original decoder contracts intact.
    node = unique(donor, '(fn2-fields-preserves fn2-checkpoint-decode ?*body)')
    text = raw(donor, node)
    at = next(n.start-node.start for n in node.items if getattr(n, 'low', None) == ':raw-rows')
    text = text[:at]+':prefix "-FIELDS-ONLY" '+text[at:]
    # The root already exports the same public ROWS equation under its old
    # name. Keep it from rewriting the generated :USE premise to T before
    # RAW-ROWS opens the getter. Every generated statement stays identical.
    forms = ['(encapsulate ()\n (local (in-theory (disable fn2-checkpoint-decode-preserves-rows)))\n'
             +text+'\n)']
    for name in ('fn2-checkpoint-decode-fields-domain-value-type',
                 'fn2-checkpoint-decode-fields-domain-value-integer'):
        forms.append(export_local(donor, '(defthm '+name+' ?*body)'))
    forms.append(export_local(donor, '(fn2-fields-preserves fn2-format-run ?*body)'))
    for name in ('fc-byte', 'fc-advance', 'fc-run-bytes', 'fc-step', 'format-run'):
        forms.append(export_local(donor, '(defthm fn2-checkpoint-'+name+'-read-pool-frame ?*body)'))
    return '''; Named interfaces over the current checkpoint/format implementation.
; Matching donor bodies do not transfer certification to this closure.
(in-package "ACL2")
(include-book "checkpoint")
(include-book "columns-guard-hints")
(fn2-book-layer :b)

'''+ '\n\n'.join(forms)+'\n'


def reader(before, donor):
    old = unique(before, '(defun fn2-checkpoint-check-step ?*body)')
    new = unique(donor, '(defun fn2-checkpoint-check-step ?*body)')
    assert norm(old) == norm(new), 'actual reader body/guard changed'
    original = unique(before, '(fn2-checkpoints-preserves fn2-checkpoint-check-step ?*body)')
    helper = unique(donor, '(local (defun fn2-checkpoint-reader-partition-contracts ?*body))')
    events = [n for n in lr.parse(donor).forms if isinstance(n, lr.Lst) and n.items
              and getattr(n.items[0], 'low', None) == 'make-event'
              and 'fn2-checkpoint-reader-partition-contracts args specs facts' in raw(donor, n)]
    assert len(events) == 1
    guarded = unique(donor, '(defcolumns-guarded-contracts fn2-checkpoint-check-step ?*body)')
    tail = '\n\n'.join(raw(donor, n) for n in (helper, events[0], guarded))
    result = lr.write(before, [(old.start, old.end, raw(donor, new)),
                               (original.start, original.end, tail)])
    result = result.replace('(include-book "checkpoint")',
        '(include-book "checkpoint-reader-interfaces")\n(include-book "columns-carrier-contracts")\n(include-book "owed")', 1)
    return result


def project():
    donor = source(DONOR, 'books/checkpoint.lisp')
    before = source(BASE, 'books/checkpoint-descriptor-read.lisp')
    # Validate expansion-critical guard and actual format worker subjects too.
    for path, names in [
        ('books/format-check.lisp', ('fn2-fc-guard', 'fn2-format-run', 'fn2-fc-byte',
          'fn2-fc-advance', 'fn2-fc-run-bytes', 'fn2-fc-step', 'fn2-fc-reset')),
        ('books/blake3.lisp', ('fn2-b3-ready',))]:
        a, b = source(BASE, path), source(DONOR, path)
        for name in names:
            head = 'defmacro' if name == 'fn2-fc-guard' else 'defun'
            pattern = '('+head+' '+name+' ?*body)'
            assert norm(unique(a, pattern)) == norm(unique(b, pattern)), (path, name)
    outputs = {'books/checkpoint-reader-interfaces.lisp': interfaces(donor),
               'books/checkpoint-descriptor-read.lisp': reader(before, donor)}
    for name in ('checkpoint-reader-scalar-domain-unit', 'checkpoint-reader-refutation-unit'):
        text = source(DONOR, 'tests/'+name+'.lisp')
        if name.endswith('scalar-domain-unit'):
            assert text.count('(include-book "../books/checkpoint")') == 1
            text = text.replace('(include-book "../books/checkpoint")',
                                '(include-book "../books/checkpoint-descriptor-read")')
        outputs['tests/'+name+'.lisp'] = text
    for path, text in outputs.items():
        actual = ROOT/path
        if actual.exists() and path.endswith('checkpoint-descriptor-read.lisp'):
            assert actual.read_text() in (before, text), path
        elif actual.exists():
            assert actual.read_text() == text, path
        actual.write_text(text)


if __name__ == '__main__':
    project()
