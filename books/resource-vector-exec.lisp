; fn: the resource ledger as a typed stobj (lane resource-ledger,
; 2026-10-01; deputy-1 after Codex review r06; planning/design-store-
; representation-2026-10-01.md section 2: "one ledger in one stobj,
; typed").  The served path holds no list (D27): the budget and the drawn
; vector are (unsigned-byte 64) arrays of *fn-rv-k* words, the slots are
; direct-index typed columns -- a phase column, a generation column (the
; completion token, books/resource-vector.lisp) and one u64 column a
; coordinate for the demands -- and the ownership row Codex's pool kept
; per read (the token (id cid file eoff elen trailer),
; books/page-read-ledger.lisp fn-prl-token) is six more u64 columns indexed
; by the same slot.  Codex's five-element pool list (ledger bookkeeping
; native-octets fd-bookkeeping file-limit; books/page-read-pool-state.lisp
; fn-prp-data) becomes the typed scalars below.
;
; GEN: def-representation.  This is the hand-written smallest version of
; what `def-representation' generates once it lands (MODE 2026-10-01
; section 4): the concrete stobj, its abstraction FN-RL-BANK to the logical
; bank, the representation invariant FN-RL-WFP and, per export, a
; correspondence theorem.  STATUS, honestly (r06 F3): the exports' guards
; are declared and NOT verified, and NO correspondence theorem is proved in
; this book; PRF-1211 stays planned until they are, and the ledger is wired
; into nothing.  The next version is the TREE of books/resource-vector-tree
; (one table, a row's owner a slot, per-row drawn columns for the sub-bank
; rows), which is the layout the host needs; this flat twin is kept as the
; measured shape of the columns, not as a claim.
;
; THE REPRESENTATION DOMAIN (r06 F4, D27): a budget word is a u64.  A
; profile whose budget does not fit is REFUSED by fn-rl-install
; (:unrepresentable-profile), never saturated; a slot whose generation has
; reached the last u64 refuses its next charge (:slot-exhausted), never
; wraps.  No arithmetic here can exceed a word: a charge is admitted only
; when drawn + demand <= budget coordinate-wise and the budget is a u64
; array, so every stored sum is below 2^64; a demand coordinate past 2^64
; fails the fit, never the store.

(in-package "ACL2")
(include-book "resource-vector")

(assert-event (equal *fn-rv-k* 9))

(defconst *fn-rl-word-max* (1- (expt 2 64)))

(defstobj fn-resource-ledger
  (fn-rl-budget :type (array (unsigned-byte 64) (9)) :initially 0)
  (fn-rl-drawn :type (array (unsigned-byte 64) (9)) :initially 0)
  (fn-rl-count :type (unsigned-byte 32) :initially 0)
  (fn-rl-phases :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (fn-rl-gens :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  ;; the demand columns, one a coordinate
  (fn-rl-c0 :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-c1 :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-c2 :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-c3 :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-c4 :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-c5 :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-c6 :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-c7 :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-c8 :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  ;; the pool's ownership row: Codex's read token, typed, by slot
  (fn-rl-ids :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-cids :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-files :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-eoffs :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-elens :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-rl-trailers :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  ;; Codex's pool scalars, typed: the identity counter and the four figures
  (fn-rl-next :type (unsigned-byte 64) :initially 0)
  (fn-rl-bookkeeping :type (unsigned-byte 64) :initially 0)
  (fn-rl-native-octets :type (unsigned-byte 64) :initially 0)
  (fn-rl-fd-bookkeeping :type (unsigned-byte 64) :initially 0)
  (fn-rl-file-limit :type (unsigned-byte 64) :initially 0)
  (fn-rl-mode :type (unsigned-byte 8) :initially 0)
  :inline t)

; -----------------------------------------------------------------------------
; The representation invariant: every column holds COUNT slots.

(defun fn-rl-wfp (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger))
  (let ((n (fn-rl-count fn-resource-ledger)))
    (and (<= n (fn-rl-phases-length fn-resource-ledger))
         (<= n (fn-rl-gens-length fn-resource-ledger))
         (<= n (fn-rl-c0-length fn-resource-ledger))
         (<= n (fn-rl-c1-length fn-resource-ledger))
         (<= n (fn-rl-c2-length fn-resource-ledger))
         (<= n (fn-rl-c3-length fn-resource-ledger))
         (<= n (fn-rl-c4-length fn-resource-ledger))
         (<= n (fn-rl-c5-length fn-resource-ledger))
         (<= n (fn-rl-c6-length fn-resource-ledger))
         (<= n (fn-rl-c7-length fn-resource-ledger))
         (<= n (fn-rl-c8-length fn-resource-ledger))
         (<= n (fn-rl-ids-length fn-resource-ledger))
         (<= n (fn-rl-cids-length fn-resource-ledger))
         (<= n (fn-rl-files-length fn-resource-ledger))
         (<= n (fn-rl-eoffs-length fn-resource-ledger))
         (<= n (fn-rl-elens-length fn-resource-ledger))
         (<= n (fn-rl-trailers-length fn-resource-ledger)))))

(defun fn-rl-slotp (slot fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard (fn-rl-wfp fn-resource-ledger)))
  (and (natp slot) (< slot (fn-rl-count fn-resource-ledger))))

; -----------------------------------------------------------------------------
; The columns, by coordinate.

(defun fn-rl-ci (i slot fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger
                  :guard (and (natp i) (< i 9) (fn-rl-wfp fn-resource-ledger)
                              (fn-rl-slotp slot fn-resource-ledger))))
  (case i
    (0 (fn-rl-c0i slot fn-resource-ledger))
    (1 (fn-rl-c1i slot fn-resource-ledger))
    (2 (fn-rl-c2i slot fn-resource-ledger))
    (3 (fn-rl-c3i slot fn-resource-ledger))
    (4 (fn-rl-c4i slot fn-resource-ledger))
    (5 (fn-rl-c5i slot fn-resource-ledger))
    (6 (fn-rl-c6i slot fn-resource-ledger))
    (7 (fn-rl-c7i slot fn-resource-ledger))
    (otherwise (fn-rl-c8i slot fn-resource-ledger))))

(defun fn-rl-update-ci (i slot v fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger
                  :guard (and (natp i) (< i 9) (fn-rl-wfp fn-resource-ledger)
                              (fn-rl-slotp slot fn-resource-ledger)
                              (unsigned-byte-p 64 v))))
  (case i
    (0 (update-fn-rl-c0i slot v fn-resource-ledger))
    (1 (update-fn-rl-c1i slot v fn-resource-ledger))
    (2 (update-fn-rl-c2i slot v fn-resource-ledger))
    (3 (update-fn-rl-c3i slot v fn-resource-ledger))
    (4 (update-fn-rl-c4i slot v fn-resource-ledger))
    (5 (update-fn-rl-c5i slot v fn-resource-ledger))
    (6 (update-fn-rl-c6i slot v fn-resource-ledger))
    (7 (update-fn-rl-c7i slot v fn-resource-ledger))
    (otherwise (update-fn-rl-c8i slot v fn-resource-ledger))))

; -----------------------------------------------------------------------------
; The abstraction: the typed ledger as the logical bank.

(defun fn-rl-budget-list (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger))
  (list (fn-rl-budgeti 0 fn-resource-ledger) (fn-rl-budgeti 1 fn-resource-ledger)
        (fn-rl-budgeti 2 fn-resource-ledger) (fn-rl-budgeti 3 fn-resource-ledger)
        (fn-rl-budgeti 4 fn-resource-ledger) (fn-rl-budgeti 5 fn-resource-ledger)
        (fn-rl-budgeti 6 fn-resource-ledger) (fn-rl-budgeti 7 fn-resource-ledger)
        (fn-rl-budgeti 8 fn-resource-ledger)))

(defun fn-rl-drawn-list (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger))
  (list (fn-rl-drawni 0 fn-resource-ledger) (fn-rl-drawni 1 fn-resource-ledger)
        (fn-rl-drawni 2 fn-resource-ledger) (fn-rl-drawni 3 fn-resource-ledger)
        (fn-rl-drawni 4 fn-resource-ledger) (fn-rl-drawni 5 fn-resource-ledger)
        (fn-rl-drawni 6 fn-resource-ledger) (fn-rl-drawni 7 fn-resource-ledger)
        (fn-rl-drawni 8 fn-resource-ledger)))

(defun fn-rl-demand-list (slot fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger
                  :guard (and (fn-rl-wfp fn-resource-ledger) (fn-rl-slotp slot fn-resource-ledger))))
  (list (fn-rl-c0i slot fn-resource-ledger) (fn-rl-c1i slot fn-resource-ledger)
        (fn-rl-c2i slot fn-resource-ledger) (fn-rl-c3i slot fn-resource-ledger)
        (fn-rl-c4i slot fn-resource-ledger) (fn-rl-c5i slot fn-resource-ledger)
        (fn-rl-c6i slot fn-resource-ledger) (fn-rl-c7i slot fn-resource-ledger)
        (fn-rl-c8i slot fn-resource-ledger)))

; A row of the logical bank: (PHASE GEN . DEMAND).
(defun fn-rl-rows-from (i fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger
                  :guard (and (natp i) (fn-rl-wfp fn-resource-ledger))
                  :measure (nfix (- (nfix (fn-rl-count fn-resource-ledger)) (nfix i)))))
  (if (or (not (natp i)) (>= i (nfix (fn-rl-count fn-resource-ledger))))
      nil
    (cons (list* (fn-rl-phasesi i fn-resource-ledger) (fn-rl-gensi i fn-resource-ledger)
                 (fn-rl-demand-list i fn-resource-ledger))
          (fn-rl-rows-from (+ 1 i) fn-resource-ledger))))

(defun fn-rl-bank (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard (fn-rl-wfp fn-resource-ledger)))
  (fn-rv-make (fn-rl-budget-list fn-resource-ledger)
              (fn-rl-drawn-list fn-resource-ledger)
              (fn-rl-rows-from 0 fn-resource-ledger)))

; -----------------------------------------------------------------------------
; The exports.

; Does DEMAND fit beside what is drawn, coordinate by coordinate?  (A word
; is checked before any store: the sum is below the budget word.)
(defun fn-rl-fits-from (i demand fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (natp i) (true-listp demand) (<= (+ i (len demand)) 9))
                  :measure (len demand)))
  (if (endp demand)
      t
    (and (<= (+ (fn-rl-drawni i fn-resource-ledger) (nfix (car demand)))
             (fn-rl-budgeti i fn-resource-ledger))
         (fn-rl-fits-from (+ 1 i) (cdr demand) fn-resource-ledger))))

(defun fn-rl-charge-from (i slot demand fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (natp i) (true-listp demand) (<= (+ i (len demand)) 9)
                              (fn-rl-wfp fn-resource-ledger)
                              (fn-rl-slotp slot fn-resource-ledger)
                              (fn-rl-fits-from i demand fn-resource-ledger))
                  :measure (len demand)))
  (if (endp demand)
      fn-resource-ledger
    (let* ((d (nfix (car demand)))
           (fn-resource-ledger
            (update-fn-rl-drawni i (+ (fn-rl-drawni i fn-resource-ledger) d) fn-resource-ledger))
           (fn-resource-ledger (fn-rl-update-ci i slot d fn-resource-ledger)))
      (fn-rl-charge-from (+ 1 i) slot (cdr demand) fn-resource-ledger))))

; A charge (fn-rv-charge): the slot's new generation is the token.
(defun fn-rl-charge (slot demand phase fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (fn-rl-wfp fn-resource-ledger) (true-listp demand)
                              (or (eql phase 1) (eql phase 2)))))
  (cond ((not (and (fn-rl-slotp slot fn-resource-ledger) (fn-rv-vectorp demand)))
         (mv :invalid-draw 0 fn-resource-ledger))
        ((not (eql (fn-rl-phasesi slot fn-resource-ledger) 0))
         (mv :slot-busy 0 fn-resource-ledger))
        ((not (fn-rl-fits-from 0 demand fn-resource-ledger))
         (mv :resources-unavailable 0 fn-resource-ledger))
        ((>= (fn-rl-gensi slot fn-resource-ledger) *fn-rl-word-max*)
         (mv :slot-exhausted 0 fn-resource-ledger))
        (t (let* ((gen (+ 1 (fn-rl-gensi slot fn-resource-ledger)))
                  (fn-resource-ledger (fn-rl-charge-from 0 slot demand fn-resource-ledger))
                  (fn-resource-ledger (update-fn-rl-phasesi slot phase fn-resource-ledger))
                  (fn-resource-ledger (update-fn-rl-gensi slot gen fn-resource-ledger)))
             (mv (if (eql phase 2) :opened :drawn) gen fn-resource-ledger)))))

(defun fn-rl-draw (slot demand fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (fn-rl-wfp fn-resource-ledger) (true-listp demand))))
  (fn-rl-charge slot demand 1 fn-resource-ledger))

(defun fn-rl-open (slot budget fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (fn-rl-wfp fn-resource-ledger) (true-listp budget))))
  (fn-rl-charge slot budget 2 fn-resource-ledger))

; Settle: the reusable coordinates (the mask's) return; the slot idles and
; keeps its generation; the token must name the slot's current draw.
(defun fn-rl-release-from (i slot mask fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (natp i) (true-listp mask) (<= (+ i (len mask)) 9)
                              (fn-rl-wfp fn-resource-ledger)
                              (fn-rl-slotp slot fn-resource-ledger))))
  (if (endp mask)
      fn-resource-ledger
    (let* ((d (if (eql (car mask) 1) (fn-rl-ci i slot fn-resource-ledger) 0))
           (fn-resource-ledger
            (update-fn-rl-drawni i (nfix (- (fn-rl-drawni i fn-resource-ledger) d))
                                 fn-resource-ledger))
           (fn-resource-ledger (fn-rl-update-ci i slot 0 fn-resource-ledger)))
      (fn-rl-release-from (+ 1 i) slot (cdr mask) fn-resource-ledger))))

(defun fn-rl-settle (slot gen fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil :guard (fn-rl-wfp fn-resource-ledger)))
  (cond ((not (fn-rl-slotp slot fn-resource-ledger)) (mv :invalid-slot fn-resource-ledger))
        ((not (and (eql (fn-rl-phasesi slot fn-resource-ledger) 1)
                   (equal (fn-rl-gensi slot fn-resource-ledger) gen)))
         (mv :stale fn-resource-ledger))
        (t (let* ((fn-resource-ledger
                   (fn-rl-release-from 0 slot *fn-rv-reusable-mask* fn-resource-ledger))
                  (fn-resource-ledger (update-fn-rl-phasesi slot 0 fn-resource-ledger)))
             (mv :settled fn-resource-ledger)))))

; -----------------------------------------------------------------------------
; Install: the profile's budget words must be representable (every word a
; u64) or the install is refused before any store (D27: refuse, never
; saturate); then NSLOTS idle slots, the baseline drawn at slot 0 and the
; reserve opened at slot 1 (books/resource-vector.lisp fn-rv-install).

(defun fn-rl-words-representable-p (words)
  (declare (xargs :guard t))
  (if (consp words)
      (and (natp (car words)) (<= (car words) *fn-rl-word-max*)
           (fn-rl-words-representable-p (cdr words)))
    (null words)))

(defun fn-rl-store-words-from (i words fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger
                  :guard (and (natp i) (<= (+ i (len words)) 9)
                              (fn-rl-words-representable-p words))
                  :verify-guards nil))
  (if (endp words)
      fn-resource-ledger
    (let ((fn-resource-ledger (update-fn-rl-budgeti i (car words) fn-resource-ledger)))
      (fn-rl-store-words-from (+ 1 i) (cdr words) fn-resource-ledger))))

(defun fn-rl-resize-all (n fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard (unsigned-byte-p 32 n)))
  (let* ((fn-resource-ledger (resize-fn-rl-phases n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-gens n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-c0 n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-c1 n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-c2 n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-c3 n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-c4 n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-c5 n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-c6 n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-c7 n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-c8 n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-ids n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-cids n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-files n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-eoffs n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-elens n fn-resource-ledger))
         (fn-resource-ledger (resize-fn-rl-trailers n fn-resource-ledger))
         (fn-resource-ledger (update-fn-rl-count n fn-resource-ledger)))
    fn-resource-ledger))

; A ledger installs ONCE (Codex r18 F2: a reinstall that shrank and regrew
; the columns would zero the generations, and an old completion token would
; settle a new draw -- the ABA back through the representation); and every
; check precedes every store (r18 F1): the budget's representability, the
; shapes, and that the baseline and the reserve fit the budget together,
; which is exactly what fn-rv-install's two charges decide, so neither can
; refuse after the columns exist.
(defun fn-rl-install (budget baseline reserve nslots fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (true-listp budget) (true-listp baseline) (true-listp reserve)
                              (natp nslots))))
  (cond ((not (eql (fn-rl-count fn-resource-ledger) 0))
         (mv :already-installed fn-resource-ledger))
        ((not (and (fn-rv-vectorp budget) (fn-rv-vectorp baseline) (fn-rv-vectorp reserve)
                   (<= 2 nslots) (unsigned-byte-p 32 nslots)))
         (mv :invalid-install fn-resource-ledger))
        ((not (fn-rl-words-representable-p budget))
         (mv :unrepresentable-profile fn-resource-ledger))
        ((not (fn-rv-below (fn-rv-plus baseline reserve) budget))
         (mv :resources-unavailable fn-resource-ledger))
        (t (let* ((fn-resource-ledger (fn-rl-resize-all nslots fn-resource-ledger))
                  (fn-resource-ledger (fn-rl-store-words-from 0 budget fn-resource-ledger)))
             (mv-let (w1 g1 fn-resource-ledger)
               (fn-rl-draw 0 baseline fn-resource-ledger)
               (declare (ignore g1))
               (if (not (eq w1 :drawn))
                   (mv w1 fn-resource-ledger)   ; unreachable: checked above
                 (mv-let (w2 g2 fn-resource-ledger)
                   (fn-rl-open 1 reserve fn-resource-ledger)
                   (declare (ignore g2))
                   (if (not (eq w2 :opened))
                       (mv w2 fn-resource-ledger)   ; unreachable: checked above
                     (mv :installed fn-resource-ledger)))))))))
