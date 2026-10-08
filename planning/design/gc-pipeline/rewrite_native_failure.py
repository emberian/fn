"""Pipeline receipts own kernel failure; standalone routes retain the old call."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as rw
from proof_repl import spans


def transform(text):
    # The raw file has platform reader conditionals. Rewrite only the six
    # ordinary top-level forms in this class; never parse those conditionals.
    edits = []
    for a, b in spans(text):
        form = text[a:b]
        if "'fn-lgc-fence-failed" not in form:
            continue
        if form.startswith('(defun fnn-log-unowned-failed-kernel '):
            continue
        parsed = rw.parse(form)
        for hit in rw.match("(fnn-core 'fn-lgc-fence-failed (fnn-log-kernel ?log))", parsed.forms):
            arg = hit.captures['log']
            edits.append((a + hit.start, a + hit.end,
                          '(fnn-log-unowned-failed-kernel ' + form[arg.start:arg.end] + ')'))
    return rw.write(text, edits)


fixture = "(setf (fnn-log-kernel log) (fnn-core 'fn-lgc-fence-failed (fnn-log-kernel log)))"
assert transform(fixture) == '(setf (fnn-log-kernel log) (fnn-log-unowned-failed-kernel log))'
assert transform(transform(fixture)) == transform(fixture)

if __name__ == '__main__':
    p = ROOT / 'host/native/io.lisp'
    p.write_text(transform(p.read_text()))
