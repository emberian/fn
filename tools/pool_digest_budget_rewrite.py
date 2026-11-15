"""Grow the shared digest loader; retain the entire original fetch definition."""
import lisp_rewrite as lr

SUPPORT = '''; A partial little-endian word is continuation state, not a digest receipt.
; Its width is exactly the number of bytes already consumed in this word.
(defun fn2-rec-fetch-state-p (next acc)
 (declare (xargs :guard t))
 (and (natp next) (<= next 32) (unsigned-byte-p 32 acc)
      (case (mod next 4)
       (0 (equal acc 0)) (1 (unsigned-byte-p 8 acc))
       (2 (unsigned-byte-p 16 acc)) (otherwise (unsigned-byte-p 24 acc)))))

(defun fn2-rec-fetch-bytes (left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-pool fn2-digests) :verify-guards nil :measure (nfix left)
  :guard (and (fn2-pool-wfp fn2-pool) (fn2-digest-rowp dst fn2-digests)
              (natp left) (fn2-rec-fetch-state-p next acc) (natp off))))
 (b* (((when (= next 32)) (mv :ok next acc fn2-digests))
      ((when (zp left)) (mv :more next acc fn2-digests))
      ((mv code byte) (fn2-rec-byte-at slot gen (+ off next) okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code next acc fn2-digests))
      (pos (mod next 4))
      ; Use the existing canonical U32 byte transition, not another word codec.
      ((mv status word & & &) (fn2-layout-byte :u32 pos acc 0 0 0 byte))
      ((unless (and (member-eq status '(:part :done)) (unsigned-byte-p 32 word)))
       (mv :invariant next acc fn2-digests))
      (after (+ 1 next)) (complete (eq status :done))
      (partial (if complete 0 word))
      ((unless (fn2-rec-fetch-state-p after partial)) (mv :invariant next acc fn2-digests))
      ; No partially read word is written to the destination row.
      (fn2-digests (if complete (fn2-digest-set-word dst (floor next 4) word fn2-digests) fn2-digests)))
  (fn2-rec-fetch-bytes (- left 1) after partial dst slot gen off okind oslot ogen fn2-pool fn2-digests)))

(defun fn2-rec-fetch-step (budget next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-pool fn2-digests) :verify-guards nil
  :guard (and (fn2-pool-wfp fn2-pool) (fn2-digest-rowp dst fn2-digests))))
 (if (not (and (natp budget) (natp off) (fn2-rec-fetch-state-p next acc)))
     (mv :bounds next acc fn2-digests)
  (fn2-rec-fetch-bytes (min budget (- 32 next)) next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)))

(defthm fn2-rec-fetch-step-progress-bound
 (implies (and (natp budget) (natp off) (fn2-rec-fetch-state-p next acc))
  (and (<= next (mv-nth 1 (fn2-rec-fetch-step budget next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
       (<= (mv-nth 1 (fn2-rec-fetch-step budget next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)) 32)
       (<= (- (mv-nth 1 (fn2-rec-fetch-step budget next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)) next) budget)))
 :rule-classes nil)
(defthm fn2-rec-fetch-step-result-state
 (implies (and (natp budget) (natp off) (fn2-rec-fetch-state-p next acc))
  (fn2-rec-fetch-state-p
   (mv-nth 1 (fn2-rec-fetch-step budget next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests))
   (mv-nth 2 (fn2-rec-fetch-step budget next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests))))
 :rule-classes nil)
(defthm fn2-rec-fetch-step-zero
 (implies (and (natp off) (fn2-rec-fetch-state-p next acc))
  (equal (mv-list 4 (fn2-rec-fetch-step 0 next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests))
         (list (if (= next 32) :ok :more) next acc fn2-digests)))
 :rule-classes nil)
(defthm fn2-rec-fetch-step-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digest-rowp dst fn2-digests))
  (and (fn2-digestsp (mv-nth 3 (fn2-rec-fetch-step budget next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
       (fn2-digests-wfp (mv-nth 3 (fn2-rec-fetch-step budget next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
       (equal (fn2-digests-rows (mv-nth 3 (fn2-rec-fetch-step budget next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
              (fn2-digests-rows fn2-digests))))
 :rule-classes nil)
(verify-guards fn2-rec-fetch-bytes)
(verify-guards fn2-rec-fetch-step)
(in-theory (disable fn2-rec-fetch-state-p fn2-rec-fetch-bytes fn2-rec-fetch-step))

'''

EXEC = '''(if (or (not (natp k)) (>= k 8)) (mv :ok fn2-digests)
   (mv-let (code next acc fn2-digests)
    (fn2-rec-fetch-step (- 32 (* 4 k)) (* 4 k) 0 dst slot gen off okind oslot ogen fn2-pool fn2-digests)
    (declare (ignore next acc))
    (mv code fn2-digests)))'''

REFINEMENT = '''; Exact original API code and COMPLETE digest carrier effects.
(defthm fn2-rec-fetch-exec-refines
 (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
               (fn2-digestsp fn2-digests) (fn2-digest-rowp dst fn2-digests)
               (natp k) (<= k 8) (natp off))
  (equal (mv-list 2 (fn2-rec-fetch k dst slot gen off okind oslot ogen fn2-pool fn2-digests))
         (mv-list 2 '''+EXEC+''')))
 :rule-classes nil)
'''


def rewrite(source):
    if '(defun fn2-rec-fetch-step ' in source:return source
    matches=lr.match('(defun fn2-rec-fetch ?*body)',lr.parse(source).forms,deep=False)
    if len(matches)!=1:raise ValueError('expected canonical digest fetch')
    n=matches[0].node
    source=lr.write(source,[(n.start,n.start,SUPPORT)])
    anchor='(in-theory (disable fn2-rec-fetch))'
    if source.count(anchor)!=1:raise ValueError('fetch proof anchor drift')
    source=source.replace(anchor,REFINEMENT+anchor,1)
    anchor='(include-book "pool")'
    if source.count(anchor)!=1:raise ValueError('pool dependency drift')
    return source.replace(anchor,anchor+'\n(include-book "layout")',1)


def fixture_totalize(source):
    """Apply the authentic fixed-index recipe; keep natural controls unchanged."""
    from checkpoint_summary_recursion_rewrite import rewrite as fixed
    source, _ = fixed(source, {'fn2-rdb-seed': 8, 'fn2-rdb-words': 8})
    if '(defconst *fn2-rdb-boundary-words* ' not in source:
        seed = lr.match('(fn2-fields-set-value i (+ 12345 (* 101 i)) fn2-fields)',lr.parse(source).forms)
        if len(seed) != 1:
            raise ValueError('fixture input-word class drift')
        n = seed[0].node
        source = lr.write(source, [(n.start,n.end,'(fn2-fields-set-value i (nth (nfix i) *fn2-rdb-boundary-words*) fn2-fields)')])
        n = lr.match('(defun fn2-rdb-seed ?*body)',lr.parse(source).forms,deep=False)[0].node
        source = lr.write(source, [(n.start,n.start,'; Independent U32 boundaries exercise all four byte positions.\n(defconst *fn2-rdb-boundary-words* \'(0 255 256 65535 65536 2147483647 2147483648 4294967295))\n')])
    forms = lr.parse(source).forms
    fn = lr.match('(defun fn2-rdb-full ?*body)', forms, deep=False)[0].node
    calls = lr.match('(fn2-rdb-full ?k ?*rest)', [fn.items[-1]])
    if len(calls) != 1:
        raise ValueError('full fixture recursion drift')
    arg = calls[0].captures['k']
    if not lr.match('(+ 1 (nfix k))', [arg], deep=False) and not lr.match('(+ 1 k)', [arg], deep=False):
        raise ValueError('full fixture successor drift')
    source=lr.write(source, [(arg.start, arg.end, '(+ 1 (nfix k))')])
    if '(legacy (fn2-digests-copy fn2-digests))' not in source:
        target='(good (and (eq code :ok) (fn2-rdb-words 0 k (- 8 k) fn2-fields fn2-digests)))'
        if source.count(target)!=1:raise ValueError('full carrier witness anchor drift')
        source=source.replace(target,'''(legacy (fn2-digests-copy fn2-digests))
       ((mv fn2-fields fn2-digests) (fn2-rdb-seed 0 fn2-fields fn2-digests))
       (whole (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                   (fn2-digestsp fn2-digests) (fn2-digest-rowp 0 fn2-digests)
                   (natp k) (<= k 8) (natp 0)))
       ((mv new-code next acc fn2-digests)
        (fn2-rec-fetch-step (- 32 (* 4 k)) (* 4 k) 0 0 slot gen 0 1 0 1 fn2-pool fn2-digests))
       (good (and whole (eq code :ok) (eq code new-code) (= next 32) (= acc 0)
                  (equal legacy (fn2-digests-copy fn2-digests))
                  (fn2-rdb-words 0 k (- 8 k) fn2-fields fn2-digests)))''',1)
    if '(short-legacy (fn2-digests-copy fn2-digests))' not in source:
        target='(short-same (and (eq short :bounds) (fn2-rdb-words 0 0 2 fn2-fields fn2-digests)))'
        if source.count(target)!=1:raise ValueError('partial carrier witness anchor drift')
        source=source.replace(target,'''(short-legacy (fn2-digests-copy fn2-digests))
      ((mv fn2-fields fn2-digests) (fn2-rdb-seed 0 fn2-fields fn2-digests))
      ((mv short-new short-next short-acc fn2-digests)
       (fn2-rec-fetch-step 32 0 0 0 slot gen 0 1 0 1 fn2-pool fn2-digests))
      (short-same (and (eq short :bounds) (eq short short-new) (= short-next 10)
                       (fn2-rec-fetch-state-p short-next short-acc)
                       (equal short-legacy (fn2-digests-copy fn2-digests))
                       (fn2-rdb-words 0 0 2 fn2-fields fn2-digests)))''',1)
    if '(partial-before (fn2-digests-copy fn2-digests))' not in source:
        target='      ((mv incremental fn2-digests) (fn2-rdb-drive 32 0 0 slot gen fn2-fields fn2-pool fn2-digests))'
        if source.count(target)!=1:raise ValueError('stale partial witness anchor drift')
        source=source.replace(target,'''      ((mv prefix pn pa fn2-digests) (fn2-rec-fetch-step 5 0 0 0 slot gen 0 1 0 1 fn2-pool fn2-digests))
      (partial-before (fn2-digests-copy fn2-digests))
      ((mv stale-partial spn spa fn2-digests)
       (fn2-rec-fetch-step 1 pn pa 0 slot (+ 1 gen) 0 1 0 1 fn2-pool fn2-digests))
      (partial-same (and (eq prefix :more) (= pn 5) (= pa 255)
                         (eq stale-partial :stale) (= spn pn) (= spa pa)
                         (equal partial-before (fn2-digests-copy fn2-digests))))
      ((mv fn2-fields fn2-digests) (fn2-rdb-seed 0 fn2-fields fn2-digests))
'''+target,1)
        source=source.replace('wrong-same stale-same incremental full','wrong-same stale-same partial-same incremental full',1)
        source=source.replace("'(t t t t t t t t t)","'(t t t t t t t t t t)",1)
    if '; Complete test-only reference faces from each actual schema.' not in source:
        events='; Complete test-only reference faces from each actual schema.\n'
        for name in ['fn2-digests','fn2-pool']:
            events+=f"""(make-event
 (let* ((name '{name})
        (schema (cdr (assoc-eq name (fn2-decl-rows :columns (w state)))))
        (fields (append (fn2-columns-fields name (fn2-decl-get :columns schema))
                        (list (list (fn2-columns-sym name "-ROWS") :type
                                    (list 'integer 0 (- (fn2-decl-get :rows-bound schema) 1)) :initially 0))
                        (fn2-decl-get :extra-fields schema))))
   (cons 'progn (fn2-columns-reference-events name (fn2-columns-sym name "-REF") fields))))
"""
        n=lr.match('(deflayout fn2-rec-budget-words ?*body)',lr.parse(source).forms,deep=False)[0].node
        source=lr.write(source,[(n.start,n.start,events+'\n')])
    return source
