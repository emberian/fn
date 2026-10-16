#!/usr/bin/env python3
"""PIN-VALUE plan (main ruling B, 10-16): which theorem formulas change.

The pin value of fn-ocfg-pins widens from CFG to (CFG . PROFILE), and the
opens gain a PROFILE argument.  This script is the plan of record: the READY's
counts are its output, and a later revision shows as a diff of plan.txt.

  WIDENED   a formula that states the pin value's shape: names the pin table
            and (a) asserts fn-cfgp, (b) projects (cdr (fn-ocfg-pin-find ..)),
            (c) builds (cons ID TERM) with a compound TERM, or (d) passes a
            compound value to fn-ocfg-pin-add / fn-ocfg-pin-set.
  ARGUMENT  a formula that names a function in the ARITY SET: the transitive
            STATE-free callers of the three opens, not through fn-ocfg-step
            (whose :open / :open-peer arms read PROFILE from the event).
Usage: python3 build/pin-value/plan.py [ROOT]  (default: the lane root)
"""
import os, re, sys, collections

ROOT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), '..', '..')
SEED = {'fn-ocfg-open', 'fn-ocfg-open-peer', 'fn-ocar-ocfg-open'}
STOP = {'fn-ocfg-step'}
PIN = {'fn-ocfg-pin-add', 'fn-ocfg-pin-set', 'fn-ocfg-pin-find', 'fn-ocfg-pins-okp',
       'fn-ocfg-pins', 'fn-ocfg-pin-remove', 'fn-ocfg-conns-pinnedp', 'fn-ocfg-pins-pin-conns-only'}

def strip(t):
    out = []; i = 0; n = len(t)
    while i < n:
        c = t[i]
        if c == ';':
            j = t.find('\n', i); i = n if j < 0 else j; continue
        if c == '#' and i + 1 < n and t[i + 1] == '|':
            j = t.find('|#', i); i = n if j < 0 else j + 2; continue
        if c == '"':
            j = i + 1
            while j < n and t[j] != '"':
                j += 2 if t[j] == '\\' else 1
            out.append('""'); i = j + 1; continue
        out.append(c); i += 1
    return ''.join(out)

def forms(t):
    i = 0; n = len(t)
    while i < n:
        if t[i] == '(':
            d = 0; j = i
            while j < n:
                if t[j] == '(':
                    d += 1
                elif t[j] == ')':
                    d -= 1
                    if d == 0:
                        break
                j += 1
            yield t[i:j + 1]; i = j + 1
        else:
            i += 1

def parse(tk, i=0):
    if tk[i] == '(':
        l = []; i += 1
        while tk[i] != ')':
            x, i = parse(tk, i); l.append(x)
        return l, i + 1
    return tk[i].lower(), i + 1

def events(f):
    if isinstance(f, list) and f and isinstance(f[0], str):
        h = f[0]
        if h in ('local', 'encapsulate', 'progn', 'with-output', 'defsection'):
            for x in f[1:]:
                yield from events(x)
        elif h in ('defun', 'defund', 'def-loop', 'define', 'defun-inline') and len(f) > 2 and isinstance(f[1], str):
            yield 'def', f[1], f[2], f[3:]
        elif h in ('defthm', 'defthmd') and len(f) > 2 and isinstance(f[1], str):
            yield 'thm', f[1], None, f[2]

def syms(x):
    if isinstance(x, list):
        for y in x:
            yield from syms(y)
    else:
        yield x

def subterms(x):
    if isinstance(x, list):
        yield x
        for y in x:
            yield from subterms(y)

def widened(formula):
    s = set(syms(formula))
    if not s & PIN:
        return None
    if 'fn-cfgp' in s:
        return 'cfgp'
    for t in subterms(formula):
        if not t or not isinstance(t[0], str):
            continue
        if t[0] == 'cdr' and len(t) == 2 and isinstance(t[1], list) and t[1] and t[1][0] == 'fn-ocfg-pin-find':
            return 'projection'
        if t[0] == 'cons' and len(t) == 3 and isinstance(t[2], list) and s & {'fn-ocfg-pin-find'}:
            return 'built value'
        if t[0] in ('fn-ocfg-pin-add', 'fn-ocfg-pin-set') and len(t) == 4 and isinstance(t[2], list):
            return 'compound value'
    return None

defs, thms, others, bodies = {}, [], [], {}
for d in ('books', 'host', 'tests'):
    for dp, _, fs in os.walk(os.path.join(ROOT, d)):
        for fn in sorted(fs):
            if not fn.endswith('.lisp'):
                continue
            p = os.path.join(dp, fn); rel = os.path.relpath(p, ROOT)
            t = strip(open(p, errors='replace').read())
            for fr in forms(t):
                try:
                    f, _ = parse(re.findall(r'\(|\)|[^\s()]+', fr))
                except Exception:
                    continue
                evs = list(events(f))
                if not evs and isinstance(f, list) and f and isinstance(f[0], str) and f[0] not in ('in-package', 'include-book'):
                    others.append((rel, f[0], f))
                for kind, name, formals, body in evs:
                    if kind == 'def':
                        fm = [x for x in formals if isinstance(x, str)] if isinstance(formals, list) else []
                        defs[name] = (rel, fm, set(syms(body)))
                        bodies[name] = body
                    else:
                        thms.append((rel, name, body))

arity = set(SEED); ch = True
while ch:
    ch = False
    for n, (rel, fm, b) in defs.items():
        if n in arity or n in STOP or 'state' in fm:
            continue
        if b & arity:
            arity.add(n); ch = True

W = [(r, n, widened(f)) for r, n, f in thms if widened(f)]
A = [(r, n) for r, n, f in thms if set(syms(f)) & arity]
wn = {(r, n) for r, n, _ in W}
A_only = [x for x in A if x not in wn]
print('ARITY SET (%d): %s' % (len(arity), ' '.join(sorted(arity))))
print('WIDENED %d' % len(W))
for r, n, why in sorted(W):
    print('  W  %-50s %-60s %s' % (r, n, why))
print('ARGUMENT %d (also widened: %d)' % (len(A_only), len(A) - len(A_only)))
for r, n in sorted(A_only):
    print('  A  %-50s %s' % (r, n))
c = collections.Counter(r for r, _ in A_only)
print('ARGUMENT by book:')
for k in sorted(c):
    print('  %3d %s' % (c[k], k))
print('TOTAL %d' % (len(W) + len(A_only)))
# Call sites: every definition whose body calls a member of the arity set
# (the members themselves gain PROFILE; STATE callers pass
# (fn-owner-store-profile state); test helpers pass their fixture's profile).
C = sorted((defs[n][0], n, 'state' in defs[n][1]) for n in defs
           if defs[n][2] & arity)
print('CALL SITES %d' % len(C))
for r, n, st in C:
    print('  C  %-50s %-50s %s' % (r, n, 'state' if st else 'pure'))

O = [(r, h) for r, h, f in others if set(syms(f)) & arity]
print('OTHER FORMS %d (asserts, defteeth, tables naming the arity set)' % len(O))
for (r, h), k in sorted(collections.Counter(O).items()):
    print('  O  %-60s %-20s x%d' % (r, h, k))

# Pin-table producers: what reaches fn-ocfg-make's PINS slot (argument 3).
# Every producer other than the pin primitives and an existing table builds
# pin VALUES itself and must build (CFG . PROFILE).
KNOWN = {'fn-ocfg-pin-add', 'fn-ocfg-pin-set', 'fn-ocfg-pin-remove', 'fn-ocfg-pins'}
def heads(x):
    if isinstance(x, list) and x and isinstance(x[0], str):
        if x[0] == 'if':
            for y in x[2:]:
                yield from heads(y)
        else:
            yield x[0]
    elif isinstance(x, str):
        yield '<var>'
P = set()
for n, b in bodies.items():
    for tm in subterms(b):
        if tm and tm[0] == 'fn-ocfg-make' and len(tm) == 5:
            for h in heads(tm[3]):
                if h not in KNOWN and h != '<var>':
                    P.add((defs[n][0], n, h))
print('PIN PRODUCERS %d (definitions whose pins slot is built by something other than the pin primitives)' % len(P))
for r, n, h in sorted(P):
    print('  P  %-50s %-40s via %s' % (r, n, h))

# A producer that builds pin values from a configuration alone also gains the
# old table, so each surviving connection keeps its own pinned profile:
# (fn-orcp-pins-at conns cfg pins).  Formulas naming it change by that
# argument (and fn-orcn-pin-find-of-pins-at is also WIDENED above).
PRODUCER_ARITY = {h for _, _, h in P}
PA = [(r, n) for r, n, f in thms if set(syms(f)) & PRODUCER_ARITY and (r, n) not in wn]
print('PRODUCER ARGUMENT %d (formulas naming %s, not already widened)' % (len(PA), ' '.join(sorted(PRODUCER_ARITY))))
for r, n in sorted(PA):
    print('  PA %-50s %s' % (r, n))
print('GRAND TOTAL formulas %d' % (len(W) + len(A_only) + len([x for x in PA if x not in set(A_only)])))
