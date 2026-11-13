"""Conservative shape proposals for core adapters; Lean must check every proposal.

A summary says that one result projection is an n-element proper list whenever
one argument is an n-element proper list. Unknown calls, recursive cycles and
out-of-range whole-list writes are refused, never treated as assumptions.
"""
from emit_lean import Atom, List, as_list, is_lambda, is_nil


def literal_index(t):
    if isinstance(t, List) and len(t) == 2 and str(t[0]) == 'QUOTE':
        s = str(t[1])
        if s.isdigit():
            return int(s)
    return None


class CoreShapeAnalyzer:
    def __init__(self, definitions):
        self.definitions = definitions
        self.bodies = {}
        self.summaries = {}
        self.active = set()
        self.order = []

    def abstract(self, t, env):
        if not isinstance(t, List):
            return env.get(str(t), ('nil',) if is_nil(t) else ('unknown',))
        if not t:
            return ('nil',)
        if is_lambda(t[0]):
            fs = list(as_list(t[0][1]))
            if len(fs) != len(t)-1:
                return ('unknown',)
            actuals = [self.abstract(a, env) for a in t[1:]]
            return self.abstract(t[0][2], dict(zip(map(str, fs), actuals)))
        op = str(t[0]); args = list(t[1:])
        if op == 'QUOTE' and len(args) == 1:
            if is_nil(args[0]):
                return ('nil',)
            return ('unknown',)
        if op == 'IF' and len(args) == 3:
            return ('if', self.abstract(args[1], env), self.abstract(args[2], env))
        if op == 'RETURN-LAST' and len(args) == 3:
            return self.abstract(args[2], env)
        if op == 'CONS' and len(args) == 2:
            return ('cons', *(self.abstract(a, env) for a in args))
        if op in ('NTH','MV-NTH') and len(args) == 2:
            i = literal_index(args[0])
            if i is not None:
                return ('nth', i, self.abstract(args[1], env))
        if op == 'UPDATE-NTH' and len(args) == 3:
            i = literal_index(args[0])
            if i is not None:
                return ('update', i, self.abstract(args[1], env), self.abstract(args[2], env))
        if op in self.definitions:
            return ('call', op, tuple(self.abstract(a, env) for a in args))
        return ('unknown',)

    def shape(self, node, n, path, input_index, input_size):
        tag = node[0]
        if tag == 'arg':
            return set() if node[1] == input_index and n == input_size and not path else None
        if tag == 'nil':
            return set() if n == 0 else None
        if tag == 'nth':
            return self.shape(node[2], n, (node[1],)+path, input_index, input_size)
        if tag == 'cons':
            if path:
                target = node[1] if path[0] == 0 else node[2]
                rest = path[1:] if path[0] == 0 else (path[0]-1,)+path[1:]
                return self.shape(target, n, rest, input_index, input_size)
            return self.shape(node[2], n-1, (), input_index, input_size) if n else None
        if tag == 'update':
            i = node[1]
            if path:
                return self.shape(node[2] if path[0] == i else node[3], n,
                                  path[1:] if path[0] == i else path, input_index, input_size)
            if i < n:
                return self.shape(node[3], n, (), input_index, input_size)
            return None
        if tag == 'if':
            a = self.shape(node[1], n, path, input_index, input_size)
            b = self.shape(node[2], n, path, input_index, input_size)
            return a | b if a is not None and b is not None else None
        if tag == 'call':
            name, actuals = node[1:]
            if len(actuals) != len(self.definitions[name][0]):
                return None
            for i, actual in enumerate(actuals):
                deps = self.shape(actual, n, (), input_index, input_size)
                key = (name, n, path, i)
                if deps is not None and self.ensure(*key):
                    return deps | {key}
        return None

    def ensure(self, name, n, path, input_index):
        key = (name, n, tuple(path), input_index)
        if key in self.summaries:
            return self.summaries[key] is not None
        if key in self.active or name not in self.definitions or n < 0:
            return False
        formals, body, *_ = self.definitions[name]
        if not 0 <= input_index < len(formals):
            return False
        if name not in self.bodies:
            self.bodies[name] = self.abstract(body, {f: ('arg', i) for i,f in enumerate(formals)})
        self.active.add(key)
        deps = self.shape(self.bodies[name], n, tuple(path), input_index, n)
        self.active.remove(key)
        self.summaries[key] = deps
        if deps is not None:
            self.order.append(key)
        return deps is not None


def shape_theorem_name(key):
    name, n, path, arg = key
    projection = '_'.join(map(str,path)) if path else 'whole'
    return f'{name}_core_shape_{n}_{projection}_arg{arg}'


def emit_shape_candidates(analyzer, destination, widx, fill_world_bodies, targets=None):
    """Emit conditional statements and proofs; success here is only a proposal.

    Single-step unfolding plus dependency lemmas shares proofs across callers.
    The compiler, not this analyzer, establishes every proposed statement.
    """
    from emit_lean import ident, as_module, CORE_STRING_BODIES
    lines = [
        'import Fn2.Instances.ServedCertificates.ServedCommon',
        'import Fn2.ACL2.Pres',
        'namespace Fn2.Instances.ServedCertificates.ServedCoreShapes',
        'open Fn2.ACL2 Fn2.Arms Fn2.Instances.LayerAWorld',
        'open Fn2.Instances.ServedCertificates.ServedCommon',
        'set_option maxHeartbeats 800000',
        'set_option linter.unusedSimpArgs false',
    ]
    selected = set(analyzer.order) if targets is None else set()
    def select(key):
        if key in selected:
            return
        if analyzer.summaries.get(key) is None:
            raise ValueError(f'no shape proposal for {key}')
        selected.add(key)
        for dep in analyzer.summaries[key]:
            select(dep)
    for key in targets or ():
        select(key)
    for key in analyzer.order:
        if key not in selected:
            continue
        name,n,path,arg = key
        formals,body,*_ = analyzer.definitions[name]
        binders = ' '.join(f'({ident(f)} : Val)' for f in formals)
        args = ' '.join(ident(f) for f in formals)
        expr = f'({ident(name)} {args})'
        for i in path:
            expr = f'(Native.nth (.int {i}) {expr})'
        # Supply only concrete in-range update facts; never weaken the input
        # shape hypothesis to make UPDATE-NTH's padding appear preserving.
        indices = set()
        def collect(t):
            if not isinstance(t,List) or not t: return
            if str(t[0]) == 'QUOTE': return
            if str(t[0]) == 'UPDATE-NTH' and len(t)==4:
                i=literal_index(t[1])
                if i is not None and i<n: indices.add(i)
            for x in t: collect(x)
        collect(body)
        lines += [f'theorem {ident(shape_theorem_name(key))} {binders}',
                  f'    (hcore : isListB {n} {ident(formals[arg])} = true) :',
                  f'    isListB {n} {expr} = true := by']
        for i in sorted(indices):
            lines.append(f'  have hi_{i} : 0 ≤ ({i} : Int) ∧ ({i} : Int) < {n} := by decide')
        deps=[ident(shape_theorem_name(k)) for k in sorted(analyzer.summaries[key])]
        simps=[ident(name),'isListB_ite','isListB_succ_cons','isListB_zero_nil',
               'isListB_upd','Pres.nth_ite','Pres.nth_cons_zero','Pres.nth_cons_succ',
               'Pres.nth_upd_same','Pres.nth_upd_ne','hcore','ite_self',
               *(f'hi_{i}' for i in sorted(indices)),*deps]
        lines.append('  simp (disch := first | assumption | decide) only ['+', '.join(simps)+']')
        lines.append(f'#print axioms {ident(shape_theorem_name(key))}')
        # Specialize the input shape to a tuple image, so callers can rewrite
        # reconstruction without unfolding the operation's implementation.
        ibinders = ' '.join(f'({ident(f)} : '+(f'Fin {n} → Val' if i==arg else 'Val')+')'
                            for i,f in enumerate(formals))
        iargs = ' '.join(f'(Combinators.tupleImage {ident(f)})' if i==arg else ident(f)
                         for i,f in enumerate(formals))
        iexpr = f'({ident(name)} {iargs})'
        for i in path:
            iexpr = f'(Native.nth (.int {i}) {iexpr})'
        lines += [f'theorem {ident(shape_theorem_name(key)+"_reassembled")} {ibinders} :',
                  f'    Combinators.tupleImage (Combinators.kidsOfVal {n} {iexpr}) = {iexpr} := by',
                  f'  exact Combinators.tupleImage_kidsOfVal _ (isListN_of_isListB',
                  f'    ({ident(shape_theorem_name(key))} {iargs} (isListB_tupleImage _)))']

    lines += ['end Fn2.Instances.ServedCertificates.ServedCoreShapes','']
    text=fill_world_bodies(as_module('\n'.join(lines),expose=True,
                          import_all=CORE_STRING_BODIES,bodies='scan'),widx)
    destination.write_text(text)
