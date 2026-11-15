"""Wire only named cold event seams in the concrete boot machine using Lisp ASTs."""
from pathlib import Path
import argparse
import lisp_rewrite as lr

PHASES = tuple(':checkpoint-events-' + x for x in (
    'begin', 'journal-bind', 'journal-load', 'journal-received', 'journal-check',
    'frontier-begin', 'frontier-check', 'frontier-peaks', 'frontier-padding', 'frontier-finish', 'finish'))


def kind(text):
    edits = []
    for m in lr.match('(defmachine fn2-boot ?*body)', lr.parse(text).forms, deep=False):
        items = m.captures['body']
        for i, item in enumerate(items[:-1]):
            key = getattr(item, 'low', '')
            if key not in (':states', ':holds', ':arms'):
                continue
            seq = items[i + 1]
            names = {getattr(x, 'low', '') if isinstance(x, lr.Atom) else getattr(x.items[0], 'low', '') for x in seq.items}
            if all(x in names for x in PHASES):
                continue
            if any(x in names for x in PHASES):
                raise ValueError('partial event phase class')
            added = ' '.join(PHASES) if key == ':states' else '\n         '.join('(' + x + (' :storage-window)' if key == ':holds' else ')') for x in PHASES)
            edits.append((seq.end - 1, seq.end - 1, '\n         ' + added))
    return lr.write(text, edits), len(edits)


ARMS = '''
  (:checkpoint-events-begin :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-boot-checkpoint-events-begin id row-generation) :accept (:ok))
   (:set (root-role 3) (root-cursor 0)) (:next :checkpoint-root-load)
   (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
  (:checkpoint-events-journal-bind :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-boot-checkpoint-events-journal-bind) :accept ()
    :case (((:journal) (:next :checkpoint-events-journal-load) (:charge :bytes 64 :steps *fn2-work-stage* :runnable t))
           ((:frontier) (:next :checkpoint-events-frontier-begin) (:charge :steps *fn2-work-small* :runnable t))
           (:otherwise (:stop :checkpoint)))))
  (:checkpoint-events-journal-load :on-refusal ((:stop :checkpoint))
   (:do (code offset) (fn2-boot-checkpoint-events-journal-target) :accept (:read))
   (:do (reset) (fn2-core-reset row-rx-slot row-rx-gen))
   (:set (offset offset) (stage 11)) (:next :read)
   (:charge :steps *fn2-work-small* :runnable t))
  (:checkpoint-events-journal-received :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-boot-checkpoint-events-loaded id row-generation) :accept (:more))
   (:next :checkpoint-events-journal-check) (:charge :steps *fn2-work-small* :runnable t))
  (:checkpoint-events-journal-check
   (:do (code) (fn2-boot-checkpoint-events-journal-step 4096) :accept ()
    :case (((:more) (:next :checkpoint-events-journal-check) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
           ((:need-read) (:next :checkpoint-events-journal-load) (:charge :steps *fn2-work-small* :runnable t))
           ((:next) (:next :checkpoint-events-journal-bind) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
           ((:frontier) (:next :checkpoint-events-frontier-begin) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
           ((:yield) (:yield)) (:otherwise (:stop :checkpoint)))))
  (:checkpoint-events-frontier-begin :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-boot-checkpoint-events-frontier-begin) :accept (:ok))
   (:set (root-role 4) (root-cursor 0)) (:next :checkpoint-root-load)
   (:charge :bytes 128 :steps *fn2-work-stage* :runnable t))
  (:checkpoint-events-frontier-check
   (:do (code) (fn2-boot-checkpoint-events-frontier-step 4096) :accept ()
    :case (((:more) (:next :checkpoint-events-frontier-check) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
           ((:peaks) (:next :checkpoint-events-frontier-peaks) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
           (:otherwise (:stop :checkpoint)))))
  (:checkpoint-events-frontier-peaks
   (:do (code) (fn2-boot-checkpoint-events-peak-step 32) :accept ()
    :case (((:more) (:next :checkpoint-events-frontier-peaks) (:charge :bytes 32 :steps *fn2-work-stage* :runnable t))
           ((:padding) (:next :checkpoint-events-frontier-padding) (:charge :bytes 32 :steps *fn2-work-stage* :runnable t))
           (:otherwise (:stop :checkpoint)))))
  (:checkpoint-events-frontier-padding
   (:do (code) (fn2-boot-checkpoint-root-padding) :accept ()
    :case (((:more) (:next :checkpoint-events-frontier-padding) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
           ((:page-end) (:next :checkpoint-events-frontier-finish) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
           (:otherwise (:stop :checkpoint)))))
  (:checkpoint-events-frontier-finish :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-boot-checkpoint-events-frontier-finish) :accept (:events-complete))
   (:next :checkpoint-events-finish) (:charge :steps *fn2-work-stage* :runnable t))
  (:checkpoint-events-finish :on-refusal ((:stop :checkpoint))
   (:do (code candidate) (fn2-boot-checkpoint-investigation-finish id row-generation) :accept ()
    :case (((:next-candidate) (:set (checkpoint-index candidate)) (:next :checkpoint-root-candidate)
                             (:charge :steps *fn2-work-stage* :runnable t))
           ((:census) (:next :checkpoint-census) (:charge :steps *fn2-work-stage* :runnable t))
           ((:validated) (:stop :checkpoint))
           (:otherwise (:stop :checkpoint)))))
'''


def boot(text):
    edits = []
    owners = {':checkpoint-root-copy', ':checkpoint-root-dispatch', ':checkpoint-root-finish', ':checkpoint-summary-close', ':read-result'}
    # Only actual arm nodes containing an operation/transition qualify: declarations
    # in the machine kind and comments/strings cannot match this syntax.
    for phase in owners:
        for m in lr.match('(' + phase + ' ?*body)', lr.parse(text).forms, deep=True):
            node = m.node
            src = text[node.start:node.end]
            if len(m.captures['body']) < 1:
                continue
            out = src
            if phase == ':checkpoint-root-copy' and ':checkpoint-events-frontier-check' not in src:
                out = out.replace('((:next :checkpoint-root-verify))', '((:if (equal row-root-role 4)\n      ((:next :checkpoint-events-frontier-check)) ((:next :checkpoint-root-verify))))')
            elif phase == ':checkpoint-root-dispatch' and 'fn2-boot-checkpoint-events-directory-entry' not in src:
                out = out.replace('((:do (consumed) (fn2-boot-checkpoint-arena-consume) :accept (:entry))))', '((:if (equal row-root-role 3)\n                          ((:do (consumed) (fn2-boot-checkpoint-events-directory-entry) :accept (:entry)))\n                          ((:do (consumed) (fn2-boot-checkpoint-arena-consume) :accept (:entry))))))')
                out = out.replace('*fn2-checkpoint-map-entry-width* *fn2-checkpoint-arena-entry-width*)', '*fn2-checkpoint-map-entry-width* (if (equal row-root-role 3) *fn2-event-proof-entry-width* *fn2-checkpoint-arena-entry-width*))')
            elif phase == ':checkpoint-root-finish' and 'fn2-boot-checkpoint-events-directory-finish' not in src:
                old = '((:do (code) (fn2-boot-checkpoint-arena-finish) :accept (:arena-ready))'
                if old in out:
                    out = out.replace(old, '((:if (equal row-root-role 3)\n      ((:do (code) (fn2-boot-checkpoint-events-directory-finish) :accept (:directory-complete))\n       (:next :checkpoint-events-journal-bind) (:charge :steps *fn2-work-stage* :runnable t))\n      ' + old)
                    out += '))'
            elif phase == ':checkpoint-summary-close':
                if '(:next :checkpoint-events-begin)' not in out:
                    out = '''(:checkpoint-summary-close :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-boot-checkpoint-summary-close) :accept (:captured))
   (:next :checkpoint-events-begin) (:charge :steps *fn2-work-stage* :runnable t))'''
            elif phase == ':read-result':
                seam = '((equal row-stage 10) (:next :checkpoint-payload-copy))'
                if '(equal row-stage 11)' not in out:
                    out = out.replace(seam, seam + '\n                    ((equal row-stage 11) (:next :checkpoint-events-journal-received))')
            if out != src:
                edits.append((node.start, node.end, out))
    if '(fn2-boot-checkpoint-events-operations)' not in text:
        for m in lr.match('(fn2-boot-checkpoint-payload-operations)', lr.parse(text).forms, deep=True):
            edits.append((m.node.end, m.node.end, '\n (fn2-boot-checkpoint-events-operations)'))
    if '(include-book "checkpoint-restore-events-boot")' not in text:
        for m in lr.match('(include-book "checkpoint-restore-payload-boot")', lr.parse(text).forms, deep=False):
            edits.append((m.node.end, m.node.end, '\n(include-book "checkpoint-restore-events-boot")'))
    if '(:checkpoint-events-begin :on-refusal' not in text:
        for m in lr.match('(:checkpoint-payload-begin :on-refusal ?*body)', lr.parse(text).forms, deep=True):
            edits.append((m.node.start, m.node.start, ARMS + '\n  '))
    out = lr.write(text, edits)
    lr.parse(out)
    return out, len(edits)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--write', action='store_true')
    args = p.parse_args()
    root = Path(__file__).resolve().parents[1]
    for filename, transform in [('boot-kind', kind), ('boot', boot)]:
        path = root / f'books/{filename}.lisp'
        out, count = transform(path.read_text())
        print(filename, count)
        if args.write:
            path.write_text(out)
