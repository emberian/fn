#!/usr/bin/env python3
"""lift_stobj_tests.py PAYLOADS FILE... (lane served-readers, 2026-09-27; companion of
thread_stobj.py).  Known gaps: a theorem under must-fail is lifted (undo it),
macros expanding to arena calls are not lifted.: in every top-level form that is not a definition or
a theorem (inside local too), replace each innermost call (F a1 .. an fn-arena)
by (in-arena-F PAYLOADS a1 .. an), and insert the arena-lift include and
(bpr-lift F n) for each lifted F before the first rewritten form."""
import sys, re
SYM = re.compile(r"[^\s()'`,\";]+")
SKIP = {'defun', 'defund', 'defthm', 'defthmd', 'thm', 'defmacro', 'include-book', 'in-package',
        'defstobj', 'encapsulate', 'in-theory', 'deftheory', 'verify-guards', 'defabsstobj',
        'defthm-flag', 'mutual-recursion', 'table', 'bpr-lift', 'set-default-hints', 'defrule'}
BINDERS = {'with-local-stobj', 'mv-let', 'let', 'let*', 'declare', 'defun', 'defthm', 'thm', 'mv',
           'lambda', 'b*', 'list', 'cons', 'quote'}

def forms(text):
    out = []; i = 0; n = len(text)
    while i < n:
        c = text[i]
        if c.isspace(): i += 1; continue
        if c == ';':
            while i < n and text[i] != '\n': i += 1
            continue
        if text.startswith('#|', i):
            j = text.find('|#', i + 2); i = (j + 2) if j >= 0 else n; continue
        start = i; depth = 0
        while i < n:
            c = text[i]
            if c == ';':
                while i < n and text[i] != '\n': i += 1
                continue
            if c == '"':
                i += 1
                while i < n and text[i] != '"':
                    if text[i] == '\\': i += 1
                    i += 1
                i += 1; continue
            if text.startswith('#\\', i): i += 3; continue
            if c == '(': depth += 1
            elif c == ')':
                depth -= 1
                if depth == 0: i += 1; break
            elif depth == 0 and c.isspace(): break
            i += 1
        out.append((start, i))
    return out

def match_end(t, j):
    depth = 0; p = j
    while True:
        c = t[p]
        if c == '"':
            p += 1
            while t[p] != '"':
                if t[p] == '\\': p += 1
                p += 1
        elif c == ';':
            while t[p] != '\n': p += 1
            continue
        elif c == '#' and t[p + 1] == '\\': p += 3; continue
        elif c == '(': depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0: return p
        p += 1

def split_args(t):
    out = []; i = 0; n = len(t)
    while i < n:
        if t[i] in ' \t\n': i += 1; continue
        if t[i] == ';':
            while i < n and t[i] != '\n': i += 1
            continue
        j = i
        while j < n and t[j] in "'`,@": j += 1
        if j < n and t[j] == '(':
            e = match_end(t, j) + 1; out.append(t[i:e]); i = e; continue
        if j < n and t[j] == '"':
            k = j + 1
            while t[k] != '"':
                if t[k] == '\\': k += 1
                k += 1
            out.append(t[i:k + 1]); i = k + 1; continue
        while j < n and t[j] not in ' \t\n()': j += 1
        out.append(t[i:j]); i = j
    return out

def toks(x): return set(SYM.findall(x.lower()))

def xform(f, payloads, lifted):
    changed = True
    while changed:
        changed = False
        for m in re.finditer(r"\(([^\s()'`,\";]+)\s", f):
            j = m.start()
            if j > 0 and f[j - 1] in "'": continue
            e = match_end(f, j)
            args = split_args(f[j + 1:e])
            if len(args) >= 2 and args[-1].lower() == 'fn-arena' and args[0].lower() not in BINDERS:
                if any('fn-arena' in toks(a) for a in args[1:-1]): continue
                fn = args[0]; n = len(args) - 2
                lifted[fn] = n
                new = '(in-arena-' + fn + ' ' + payloads + (' ' if n else '') + ' '.join(args[1:-1]) + ')'
                f = f[:j] + new + f[e + 1:]; changed = True; break
    return f

payloads = sys.argv[1]
for path in sys.argv[2:]:
    s = open(path).read()
    res = []; last = 0; first = None; lifted = {}
    for (a, b) in forms(s):
        f = s[a:b]
        inner = f
        m = re.match(r'\(local\s+', f)
        if m: inner = f[m.end():]
        hm = re.match(r"\(([^\s()'`,\";]+)", inner)
        head = hm.group(1).lower() if hm else ''
        if head in SKIP or 'fn-arena' not in toks(f): continue
        g = xform(f, payloads, lifted)
        if g != f:
            if first is None: first = a
            res.append(s[last:a]); res.append(g); last = b
    res.append(s[last:]); s2 = ''.join(res)
    if first is not None:
        pre = ''
        if not re.search(r'\(include-book "arena-lift"', s2): pre += '(include-book "arena-lift")\n'
        if payloads.startswith('*') and not re.search(r'\(defconst ' + re.escape(payloads) + r'\s', s2):
            pre += ';; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).\n(defconst %s nil)\n' % payloads
        have = set(re.findall(r'\(bpr-lift (\S+) \d+\)', s2))
        pre += ''.join('(bpr-lift %s %d)\n' % (k, v) for k, v in sorted(lifted.items()) if k not in have)
        s2 = s2[:first] + pre + s2[first:]
        open(path, 'w').write(s2)
    print(path, sorted(lifted.items()))
