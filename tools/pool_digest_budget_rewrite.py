"""Grow the shared digest loader; retain the exact original logical fetch."""
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
(verify-guards fn2-rec-fetch
 :hints (("Goal" :use ((:instance fn2-rec-fetch-exec-refines))
                 :expand ((fn2-rec-fetch k dst slot gen off okind oslot ogen fn2-pool fn2-digests)))))
'''


def rewrite(source):
    if '(defun fn2-rec-fetch-step ' in source:return source
    matches=lr.match('(defun fn2-rec-fetch ?*body)',lr.parse(source).forms,deep=False)
    if len(matches)!=1:raise ValueError('expected canonical digest fetch')
    n=matches[0].node;body=n.items[-1]
    original=source[body.start:body.end]
    function=source[n.start:n.end]
    function=function.replace(':measure (nfix (- 8 (nfix k)))',
                              ':verify-guards nil :measure (nfix (- 8 (nfix k)))',1)
    function=function[:function.rfind(original)]+'(mbe :logic '+original+'\n       :exec '+EXEC+')'+function[function.rfind(original)+len(original):]
    source=lr.write(source,[(n.start,n.end,SUPPORT+function)])
    anchor='(in-theory (disable fn2-rec-fetch))'
    if source.count(anchor)!=1:raise ValueError('fetch proof anchor drift')
    source=source.replace(anchor,REFINEMENT+anchor,1)
    anchor='(include-book "pool")'
    if source.count(anchor)!=1:raise ValueError('pool dependency drift')
    return source.replace(anchor,anchor+'\n(include-book "layout")',1)
