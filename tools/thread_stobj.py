#!/usr/bin/env python3
"""thread_stobj.py [--dry] NAMESFILE FILE... : thread the fn-arena stobj.

Written by lane served-readers (2026-09-27) to make the served readers take
the payload arena; reusable for any interface change that adds a stobj
formal to a call tree.  Host entries whose formals end in STATE get fn-arena
just before state.

NAMESFILE lists functions whose last formal is (or becomes) fn-arena.  Every
unquoted call (F ...) of a listed F, not inside a theory expression, gains a
final ` fn-arena` unless its last argument already is fn-arena.  Every
defun/defund whose body (formals excluded) calls a listed function gains a
trailing fn-arena formal and :stobjs fn-arena (merged into its xargs; a defun
that had no :guard/:stobjs/:verify-guards also gets :verify-guards nil, so no
eager guard verification appears where there was none) and joins the list;
to a global fixpoint across FILEs.  Prints changed defuns and suspicious
sites (defun-sk, defconst, encapsulate signatures)."""
import sys, re
dry = '--dry' in sys.argv
args = [a for a in sys.argv[1:] if a != '--dry']
namesf, files = args[0], args[1:]
names = set(l.strip() for l in open(namesf) if l.strip() and not l.startswith('#'))
arity = {}
statelast = set()
SYM = re.compile(r"[^\s()'`,\";]+")
THEORY = {'e/d', 'e/d*', 'enable', 'disable', 'enable*', 'disable*', 'theory',
          'union-theories', 'set-difference-theories', 'intersection-theories',
          'universal-theory', 'function-theory', 'executable-counterpart-theory',
          ':functional-instance', 'deftheory-static'}

def parse(s):
    """list of nodes: dict(start,end,head,parent,quoted,hstart,hend)"""
    nodes = []; stack = []; i = 0; n = len(s)
    while i < n:
        c = s[i]
        if c == ';':
            while i < n and s[i] != '\n': i += 1
            continue
        if s.startswith('#|', i):
            j = s.find('|#', i + 2); i = n if j < 0 else j + 2; continue
        if s.startswith('#\\', i):
            i += 3
            while i < n and SYM.match(s[i]) and s[i] not in '()': i += 1
            continue
        if c == '"':
            i += 1
            while i < n and s[i] != '"':
                if s[i] == '\\': i += 1
                i += 1
            i += 1; continue
        if c == '(':
            k = i - 1
            q = k >= 0 and s[k] == "'"
            parent = stack[-1] if stack else None
            if parent is not None and nodes[parent]['quoted']: q = True
            m = SYM.match(s, i + 1)
            head = m.group(0).lower() if m else None
            nodes.append(dict(start=i, end=None, head=head, parent=parent, quoted=q,
                              hend=(m.end() if m else i + 1)))
            stack.append(len(nodes) - 1)
        elif c == ')':
            if stack:
                nodes[stack.pop()]['end'] = i
        i += 1
    return nodes

def count_args(s, node):
    i = node['hend']; e = node['end']; n = 0
    while i < e:
        c = s[i]
        if c in ' \t\n': i += 1; continue
        if c == ';':
            while i < e and s[i] != '\n': i += 1
            continue
        n += 1
        while i < e and s[i] in "'`,@#": i += 1
        if s[i] == '(':
            d = 0
            while True:
                if s[i] == '"':
                    i += 1
                    while s[i] != '"':
                        if s[i] == '\\': i += 1
                        i += 1
                elif s[i] == ';':
                    while s[i] != '\n': i += 1
                    continue
                elif s[i] == '(': d += 1
                elif s[i] == ')':
                    d -= 1
                    if d == 0: i += 1; break
                i += 1
        elif s[i] == '"':
            i += 1
            while s[i] != '"':
                if s[i] == '\\': i += 1
                i += 1
            i += 1
        else:
            while i < e and s[i] not in ' \t\n();': i += 1
    return n

def last_token(s, node):
    """the last top-level token of node's list (a symbol) or None"""
    j = node['end'] - 1
    while j > node['start'] and s[j] in ' \t\n': j -= 1
    if s[j] == ')': return None
    k = j
    while k > node['start'] and s[k - 1] not in ' \t\n(': k -= 1
    return s[k:j + 1].lower()

def is_call(s, nodes, idx):
    nd = nodes[idx]
    if nd['head'] not in names or nd['quoted'] or nd['end'] is None: return False
    p = nd['parent']
    if p is not None:
        ph = nodes[p]['head']
        if ph in THEORY: return False
        # the formals list of a defun
        if ph in ('defun', 'defund', 'defun-nx', 'defun-sk', 'defmacro', 'defabbrev'):
            # formals is the 2nd element
            kids = [q for q in range(p + 1, len(nodes)) if nodes[q]['parent'] == p]
            if kids and kids[0] == idx: return False
        if ph in ('declare',): return False
    return True

report = []
def process(path, s):
    changed_any = False
    while True:
        nodes = parse(s)
        edits = []  # (pos, text)
        newly = []
        # defuns first
        for i, nd in enumerate(nodes):
            if nd['head'] in ('defun', 'defund') and not nd['quoted'] and nd['end']:
                m = re.match(r"\((?:defun|defund)\s+(" + SYM.pattern + r")\s*", s[nd['start']:])
                if not m: continue
                name = m.group(1).lower()
                kids = [q for q in range(i + 1, len(nodes)) if nodes[q]['parent'] == i]
                if not kids: continue
                formals = nodes[kids[0]]
                fl = s[formals['start'] + 1:formals['end']].lower().split()
                if 'fn-arena' in fl:
                    if name in names: arity[name] = len(fl)
                    continue
                calls = any(is_call(s, nodes, q) for q in range(kids[0] + 1, len(nodes))
                            if nodes[q]['start'] < nd['end'] and nodes[q]['start'] > formals['end'])
                if not calls: continue
                if fl and fl[-1] == 'state':
                    k = s.rfind('state', formals['start'], formals['end'])
                    edits.append((k, 'fn-arena '))
                    statelast.add(name)
                else:
                    edits.append((formals['end'], ' fn-arena'))
                arity[name] = len(fl) + 1
                # xargs
                xa = None
                for q in kids[1:]:
                    if nodes[q]['head'] == 'declare':
                        for r in range(q + 1, len(nodes)):
                            if nodes[r]['parent'] == q and nodes[r]['head'] == 'xargs':
                                xa = nodes[r]
                    elif nodes[q]['head'] is not None and nodes[q]['head'] != 'declare':
                        break
                if xa is None:
                    edits.append((formals['end'] + 1, '\n  (declare (xargs :stobjs fn-arena :verify-guards nil))'))
                else:
                    body = s[xa['start']:xa['end']]
                    sm = re.search(r":stobjs\s+", body)
                    extra = ''
                    if not re.search(r":guard\b|:stobjs\b|:verify-guards\b", body):
                        extra = ' :verify-guards nil'
                    if sm:
                        p0 = xa['start'] + sm.end()
                        if s[p0] == '(':
                            e = next(nodes[r]['end'] for r in range(len(nodes)) if nodes[r]['start'] == p0)
                            edits.append((e, ' fn-arena'))
                        else:
                            e = p0
                            while s[e] not in ' \t\n)': e += 1
                            edits.append((p0, '('))
                            edits.append((e, ' fn-arena)'))
                    else:
                        edits.append((xa['hend'], ' :stobjs fn-arena' + extra))
                newly.append(name)
        if newly:
            for pos, t in sorted(edits, key=lambda x: -x[0]):
                s = s[:pos] + t + s[pos:]
            for nm in newly:
                names.add(nm); report.append('defun %s %s' % (path, nm))
            changed_any = True
            continue
        # calls
        for i, nd in enumerate(nodes):
            if is_call(s, nodes, i):
                if last_token(s, nd) == 'fn-arena': continue
                if nd['head'] in statelast and re.search(r'fn-arena\s+state\s*$', s[nd['start']:nd['end']]): continue
                a = arity.get(nd['head'])
                if a is not None and count_args(s, nd) >= a: continue
                if a is None: report.append('NOARITY %s %s' % (path, nd['head']))
                if nd['head'] in statelast:
                    if last_token(s, nd) != 'state':
                        report.append('STATELAST-ODD %s %s' % (path, nd['head'])); continue
                    k = s.rfind('state', nd['start'], nd['end'])
                    if s[k-1] not in ' \t\n' : report.append('STATELAST-ODD %s' % path); continue
                    if s[max(0,k-9):k].strip().endswith('fn-arena'): continue
                    edits.append((k, 'fn-arena '))
                else:
                    edits.append((nd['end'], ' fn-arena'))
        if edits:
            for pos, t in sorted(edits, key=lambda x: -x[0]):
                s = s[:pos] + t + s[pos:]
            changed_any = True
        # suspicious
        for i, nd in enumerate(nodes):
            if nd['head'] in ('defun-sk', 'defconst', 'encapsulate', 'defun-nx', 'define', 'defabbrev', 'defmacro') and not nd['quoted'] and nd['end']:
                body = s[nd['start']:nd['end']]
                toks = set(t.lower() for t in SYM.findall(body))
                if toks & names and nd['head'] != 'defmacro':
                    report.append('SUSPICIOUS %s %s at %d: %s' % (nd['head'], path, s.count('\n', 0, nd['start']) + 1, body[:80].replace('\n', ' ')))
        return s, changed_any

texts = {f: open(f).read() for f in files}
for f in files:
    for m in re.finditer(r"\((?:defun|defund)\s+(" + SYM.pattern + r")\s*\(([^()]*)\)", texts[f]):
        nm = m.group(1).lower(); fl = m.group(2).lower().split()
        if nm in names and 'fn-arena' in fl: arity[nm] = len(fl)
        if nm in names and fl and fl[-1] == 'state':
            statelast.add(nm)
            if 'fn-arena' not in fl: arity[nm] = len(fl) + 1
orig = dict(texts)
while True:
    before = len(names)
    for f in files:
        texts[f], _ = process(f, texts[f])
    if len(names) == before: break
# final pass for calls with the full name set
for f in files: texts[f], _ = process(f, texts[f])
seen = set()
for r in report:
    if r not in seen: seen.add(r); print(r)
ch = [f for f in files if texts[f] != orig[f]]
print('CHANGED', len(ch)); print('\n'.join(ch))
if not dry:
    for f in ch: open(f, 'w').write(texts[f])
    open(namesf, 'w').write('\n'.join(sorted(names)) + '\n')
