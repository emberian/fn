"""Emit the arm reader's internal expression alphabet, not ACL2 data values.

These are proof proposals. The independent Lean Syntax projection must succeed
and agree with each generated ArmDecl before a whole-arm proof can validate.
Literal QUOTE payloads, CASE keys and phase case codes use the data encoder.
"""
import re
from emit_lean import Atom, Str, List, val, lean_str, as_list, die


def _symbol(x):
    return '(Val.sym ' + lean_str(str(x)) + ')'


def _list(xs):
    return '(Val.ofList [' + ', '.join(xs) + '])'


def expr_val(x):
    if isinstance(x, List):
        xs = list(x)
        if not xs:
            return 'Val.nil'
        head = str(xs[0])
        if head == 'QUOTE':
            if len(xs) != 2:
                die('internal QUOTE requires one value')
            return _list([_symbol(xs[0]), val(xs[1])])
        if head == 'CASE':
            if len(xs) < 2:
                die('internal CASE requires a key')
            clauses = []
            for c in xs[2:]:
                cs = as_list(c)
                if len(cs) != 2:
                    die('internal CASE requires keys/form clauses')
                keys = cs[0]
                otherwise = (isinstance(keys, Atom)
                    and getattr(keys, 'symbol_package', None) == 'COMMON-LISP'
                    and getattr(keys, 'symbol_name', None) == 'OTHERWISE')
                clauses.append(_list([_symbol(Atom('OTHERWISE')) if otherwise else val(keys), expr_val(cs[1])]))
            return _list([_symbol(xs[0]), expr_val(xs[1]), *clauses])
        if head == 'COND':
            return _list([_symbol(xs[0]), *(_list([expr_val(v) for v in as_list(c)]) for c in xs[1:])])
        return _list([_symbol(xs[0]), *(expr_val(v) for v in xs[1:])])
    if isinstance(x, Str):
        return val(x)
    if isinstance(x, Atom) and hasattr(x, 'symbol_package'):
        if x.symbol_package == 'KEYWORD' or (x.symbol_package == 'COMMON-LISP' and x.symbol_name in ('NIL', 'T')):
            return val(x)
        return _symbol(x)
    if re.fullmatch(r'[+-]?\d+', str(x)) or str(x).startswith('#\\') or str(x).startswith(':') or str(x) in ('NIL', 'T'):
        return val(x)
    return _symbol(x)


def phase_val(x):
    if not isinstance(x, List):
        return expr_val(x)
    xs = as_list(x)
    if xs and str(xs[0]) == ':IF' and len(xs) == 4:
        return _list([_symbol(xs[0]), expr_val(xs[1]), phase_val(xs[2]), phase_val(xs[3])])
    if xs and str(xs[0]) == ':CASE' and len(xs) >= 2:
        clauses = []
        for c in xs[2:]:
            cs = as_list(c)
            if len(cs) != 2:
                die('internal phase CASE requires keys/form clauses')
            clauses.append(_list([val(cs[0]), phase_val(cs[1])]))
        return _list([_symbol(xs[0]), expr_val(xs[1]), *clauses])
    die('unsupported internal phase syntax')
