"""Exact canonical park mutation extraction; source projection, not a loader."""
from pathlib import Path
import lisp_rewrite as lr
FIXTURE = Path(__file__).resolve().parent / 'fixtures/run-physical-park/mutations-before.lisp'
NAME = 'fn2-run-load-park-source-mutations'

def project(source):
    parsed = lr.parse(source)
    if lr.match('(defmacro '+NAME+' ?*body)', parsed.forms):
        raise ValueError('park recipe already extracted')
    found = lr.match('(defun fn2-run-load-park-source ?*body)', parsed.forms)
    if len(found) != 1:
        raise ValueError('expected sole canonical park operation')
    f = found[0].node
    if source[f.start:f.end] != FIXTURE.read_text().rstrip('\n'):
        raise ValueError('park operation differs outside exact extraction')
    body = f.items[-1]
    bindings = body.items[1]
    if len(bindings.items) != 5:
        raise ValueError('unexpected park mutation recipe')
    tail = source[bindings.items[1].start:bindings.items[-1].end]
    result = source[body.items[-1].start:body.items[-1].end]
    macro = ('; Shared static mutations, after each actual owner proves its own\n'
             '; terminal source-view/pending/workspace boundary. No pool lease is freed.\n'
             '(defmacro '+NAME+' ()\n `(b* ('+tail+')\n  '+result+'))\n\n')
    guard = source[bindings.items[0].start:bindings.items[0].end]
    replacement = '(b* ('+guard+')\n  ('+NAME+'))'
    return lr.write(source, [(f.start, f.start, macro), (body.start, body.end, replacement)])


def expanded_function(source):
    """Expand only the named static recipe, preserving every actual guard."""
    from lisp_source import forms, read_sexp
    trees = [read_sexp(s) for s in forms(source)]
    f = next(t for t in trees if isinstance(t, list) and t[:2] == ['defun', 'fn2-run-load-park-source'])
    macro = next((t for t in trees if isinstance(t, list) and t[:2] == ['defmacro', NAME]), None)
    if macro is None:
        return f
    template = macro[-1]
    if template[0] != 'quasiquote' or template[1][0] != 'b*' or f[-1][-1] != [NAME]:
        raise ValueError('nonstatic or unexpected park recipe')
    inner = template[1]
    if f[-1][0] != 'b*' or len(f[-1][1]) != 1:
        raise ValueError('canonical owner guard changed')
    import copy
    result = copy.deepcopy(f)
    result[-1] = ['b*', result[-1][1] + copy.deepcopy(inner[1]), *copy.deepcopy(inner[2:])]
    return result


def require_recipe(source):
    from lisp_source import forms, read_sexp
    expected = project(FIXTURE.read_text())
    def macro(text):
        return next(read_sexp(s) for s in forms(text)
                    if read_sexp(s)[:2] == ['defmacro', NAME])
    if macro(source) != macro(expected) or expanded_function(source) != read_sexp(FIXTURE.read_text()):
        raise ValueError('park guard or mutation differs outside exact static extraction')
