"""Project archive schema metadata/admission without replacing newer fold proofs.

Each splice is confined to a named declaration or admission function.  The
before fixture is actual ad7229772 source, rather than a second schema model.
"""
import lisp_rewrite as lr


def change(source, name, recipe, head='defun'):
    matches = lr.match(f'({head} {name} ?*body)', lr.parse(source).forms, deep=False)
    if len(matches) != 1:
        raise ValueError(f'expected one {name}')
    n = matches[0].node
    return lr.write(source, [(n.start, n.end, recipe(source[n.start:n.end]))])


def once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f'declaration drift: {old}')
    return text.replace(old, new, 1)


SCALAR = '''(defun fn2-rs-scalar-value-kindp (kind)
 (declare (xargs :verify-guards nil))
 (or (member-eq kind '(:u8 :u16 :u32 :u60 :u64 :bool :varint))
     (and (consp kind) (member-eq (car kind) '(:id :enum)))))
'''
INTEGER_VALUES = '''(defun fn2-rs-int-valuesp (value)
 (declare (xargs :verify-guards nil))
 (if (atom value) (null value)
  (and (consp (car value)) (fn2-rs-scalar-value-kindp (cadar value))
       (fn2-rs-int-valuesp (cdr value)))))'''


def schema(source):
    if not lr.match('(defun fn2-rs-scalar-value-kindp ?*body)', lr.parse(source).forms,
                    deep=False):
        source = change(source, 'fn2-rs-int-valuesp', lambda _: SCALAR + INTEGER_VALUES)

    def declaration(s):
        if '(name id key value merge page-kind fold internal)' in s:
            return s
        s = once(s, '(name id key value merge page-kind fold)',
                 '(name id key value merge page-kind fold internal)')
        s = once(s, '(or (null fold) (fn2-rf-okp fold key value merge))))',
                 '(or (null fold) (fn2-rf-okp fold key value merge))\n'
                 '                   (booleanp internal) (or (not internal) (null fold))))')
        return once(s, ':compare cmp :fold fold)', ':compare cmp :fold fold :internal internal)')

    source = change(source, 'fn2-defrunschema', declaration)

    def macro(s):
        if 'fold internal)' in s:
            return s
        s = once(s, "(page-kind ':run-data) fold)", "(page-kind ':run-data) fold internal)")
        return once(s, 'name id key value merge page-kind fold)',
                    'name id key value merge page-kind fold internal)')
    return change(source, 'defrunschema', macro, 'defmacro')


def put(source):
    def recipe(s):
        if '(fn2-run-layout-internal-p sid)' in s:
            return s
        return once(s, '((unless (< 0 (fn2-run-layout-fields sid 0)))',
                    '((unless (and (< 0 (fn2-run-layout-fields sid 0)) '
                    '(not (fn2-run-layout-internal-p sid))))')
    return change(source, 'fn2-succ-put', recipe)


def replay(source):
    def recipe(s):
        if '(fn2-run-layout-internal-p sid)' in s:
            return s
        anchor='(sid (- kind *fn2-commit-txn-schema-record-kind-base*))'
        return once(s, anchor, anchor + '\n      ((when (fn2-run-layout-internal-p sid)) '
                    '(mv :schema fn2-succ-slots fn2-fields))')
    return change(source, 'fn2-succ-replay-records', recipe)
