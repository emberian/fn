"""Structural owner-family funnel migration, preserving untouched source bytes.

Only executable calls are rewritten; quotes, comments and strings stay intact.
The fixed publication layout is shared by the transformation and its fixtures.
"""
from tools import lisp_rewrite as lr

FIELDS = ('attempted', 'base', 'base-payloads', 'deferred', 'durable',
          'inflight', 'pending', 'requested', 'serial', 'pass')
GLOBALS = {'fn-owner-' + ('orc-pass' if f == 'pass' else 'sco-' + f): ':' + f
           for f in FIELDS}


def publication(source):
    parsed = lr.parse(source)

    def visit(n):
        if not isinstance(n, lr.Lst):
            return source[n.start:n.end]
        items = n.items
        if (len(items) >= 3 and isinstance(items[0], lr.Atom)
                and isinstance(items[1], lr.Pre) and items[1].prefix == "'"
                and isinstance(items[1].node, lr.Atom)):
            field = GLOBALS.get(items[1].node.low)
            head = items[0].low
            if field and head in ('f-get-global', 'fn-owner-sco-global') and len(items) == 3:
                return f'(fn-opub-get {field} (fn-ost-publication {visit(items[2])}))'
            if field and head == 'f-put-global' and len(items) == 4:
                if not isinstance(items[3], lr.Atom) or items[3].low != "state":
                    raise ValueError("family migration requires a threaded state binding")
                value, state = visit(items[2]), visit(items[3])
                return (f'(fn-ost-install-publication\n'
                        f' (fn-opub-put {field} {value} (fn-ost-publication {state})) {state})')
        return lr.write(source[n.start:n.end],
                        [(c.start-n.start, c.end-n.start, visit(c)) for c in items
                         if isinstance(c, lr.Lst)])

    return lr.write(source, [(n.start, n.end, visit(n)) for n in parsed.forms
                             if isinstance(n, lr.Lst)])


def composition_events():
    """All ten observable post-fields, expressed as the old compositions.

    Emitted assertions use the independent tuple layout, not fn-opub-put;
    fields not assigned by the old host composition must remain unchanged.
    """
    old = {f: f'(fn-opub-get :{f} r)' for f in FIELDS}
    def row(changes):
        return '(list ' + ' '.join(changes.get(f, old[f]) for f in FIELDS) + ')'
    observe = row({})
    events = [f'(defun fn-opub-observe (r)\n  (declare (xargs :guard t))\n  {observe})']
    due = '''(fn-ock-requested-next
        (fn-opub-get :durable r) count suffix
        (fn-opl-attempted (fn-opub-get :deferred r) (fn-opub-get :attempted r) count now)
        (fn-opub-get :inflight r)
        (fn-opl-blockedp (fn-opub-get :deferred r) budget space count now)
        (fn-opub-get :requested r))'''
    request = '''(fn-ock-request-word
        (fn-opub-get :durable r) count
        (fn-opl-attempted (fn-opub-get :deferred r) (fn-opub-get :attempted r) count now)
        (fn-opub-get :inflight r)
        (fn-opl-blockedp (fn-opub-get :deferred r) budget space count now))'''
    specs = [
        ('due', 'r profile count suffix budget space now', f'((word {due}))',
         '(if profile (if (equal word :coalesce) :inflight word) :idle)',
         f'''(if (not profile) (fn-opub-observe r)
          (cond ((equal word :coalesce) {row({'pending':'t'})})
                ((equal word :inflight) (fn-opub-observe r))
                ((equal word :due) {row({'pending':'nil'})})
                (t {row({'pending':'nil','requested':'nil'})})))'''),
        ('request', 'r profile count budget space now', f'((word {request}))',
         '(if profile word :nothing-to-compact)',
         f"(if profile {row({'requested': '''(and (member-eq word '(:requested :coalesced)) t)'''})} (fn-opub-observe r))"),
        ('capture', 'r count', '((serial (fn-opl-next-serial (fn-opub-get :serial r))))',
         'serial', row({'attempted':'count','inflight':'count','serial':'serial','requested':'nil'})),
        ('done', 'r next payloads durablep verdict',
         '''((released (fn-orc-release-slot (list :publication (fn-sco-sequence next))
                    (fn-opub-get :pass r) (fn-opub-get :inflight r))))''',
         '(if durablep (fn-sco-sequence next) :none)',
         row({'base':'(fn-scka-strip-base next)', 'base-payloads':'(and (natp payloads) payloads)',
              'inflight':'(cadr released)', 'durable':'(if durablep (fn-sco-sequence next) (fn-opub-get :durable r))',
              'deferred':'''(cond ((and (consp verdict) (eq (car verdict) :deferred)) verdict)
                                 (durablep nil) (t (fn-opub-get :deferred r)))'''})),
        ('abandoned', 'r count serial outcome now',
         '''((settled (fn-opl-settle count serial outcome now (fn-opub-get :pass r)
                         (fn-opub-get :inflight r) (fn-opub-get :serial r) (fn-opub-get :deferred r))))''',
         '''(if (fn-opl-holdsp count serial (fn-opub-get :pass r) (fn-opub-get :inflight r)
                             (fn-opub-get :serial r)) (caddr settled) :stale)''',
         row({'inflight':'(cadr settled)','deferred':'(caddr settled)'}))]
    for name, args, bindings, answer, fields in specs:
        events.append(f'''(defthm fn-opub-{name}-composition-by-definition
  (let {bindings}
    (and (equal (mv-nth 0 (fn-opub-{name} {args})) {answer})
         (equal (fn-opub-observe (mv-nth 1 (fn-opub-{name} {args})))
                {fields})))
  :hints (("Goal" :in-theory
           (e/d (fn-opub-{name} fn-opub-observe)
                (fn-opub-get fn-opub-put fn-opl-settle fn-opl-holdsp
                 fn-orc-release-slot fn-ock-requested-next fn-ock-request-word
                 fn-opl-attempted fn-opl-blockedp fn-scka-strip-base fn-sco-sequence)))))''')
    for name, args, fields in [
        ('install','r base',row({f: ('base' if f=='base' else 'nil') for f in FIELDS if f!='serial'})),
        ('reclaim-install','r base count',row({'base':'base','base-payloads':'nil','durable':'count','attempted':'count','deferred':'nil','inflight':'nil','pass':'nil'}))]:
        events.append(f'''(defthm fn-opub-{name}-composition-by-definition
  (equal (fn-opub-observe (fn-opub-{name} {args})) {fields})
  :hints (("Goal" :in-theory (enable fn-opub-{name} fn-opub-observe))))''')
    return '\n\n'.join(events) + '\n'
