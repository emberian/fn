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
; correspondence theorem. Draw, open and settle and their mutable loops
; now have verified guards and representation preservation. Fresh install
; has fn-rl-install-correspondence; install/store-words guards and the
; general draw/settle bank correspondence remain separate obligations. PRF-1211 stays planned, and the ledger is wired
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
  ;; Owner syncer custody: physical join and consumed operation outcome are
  ;; independent receipts.  These scalar fields do not change FN-RL-BANK.
  (fn-rl-worker-resident :type (unsigned-byte 64) :initially 0)
  (fn-rl-worker-operation :type (unsigned-byte 64) :initially 0)
  (fn-rl-worker-physical :type bit :initially 0)
  (fn-rl-worker-outcome :type bit :initially 0)
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

; The concrete profile has u64 budget words and a u32 slot count.
; These are representation limits, not logical admission limits (D27).
(defun fn-rl-profile-representable-p (budget nslots)
  (declare (xargs :guard t))
  (and (fn-rl-words-representable-p budget)
       (unsigned-byte-p 32 nslots)))

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
; refusal is decided before any store (r18 F1): representability and the
; logical decision on a two-slot table are checked before mutation. The theorem
; fn-rl-install-preflight-charges-succeed proves that, on a fresh ledger,
; neither charge can refuse after the columns exist.
(defun fn-rl-install (budget baseline reserve nslots fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (true-listp budget) (true-listp baseline) (true-listp reserve)
                              (natp nslots))))
  (cond ((not (eql (fn-rl-count fn-resource-ledger) 0))
         (mv :already-installed fn-resource-ledger))
        ((not (fn-rl-profile-representable-p budget nslots))
         (mv :unrepresentable-profile fn-resource-ledger))
        ((not (and (fn-rv-vectorp budget) (<= 2 nslots)))
         (mv (car (fn-rv-install budget baseline reserve nslots))
             fn-resource-ledger))
        ;; Only slots 0 and 1 determine installation's verdict.  Ask the
        ;; logical specification on that bounded table before any store.
        ((not (eq (car (fn-rv-install budget baseline reserve 2)) :installed))
         (mv (car (fn-rv-install budget baseline reserve 2)) fn-resource-ledger))
        (t (let* ((fn-resource-ledger (fn-rl-resize-all nslots fn-resource-ledger))
                  (fn-resource-ledger (fn-rl-store-words-from 0 budget fn-resource-ledger)))
             (mv-let (w1 g1 fn-resource-ledger)
               (fn-rl-draw 0 baseline fn-resource-ledger)
               (declare (ignore g1))
               (if (not (eq w1 :drawn))
                   ; fn-rl-install-preflight-charges-succeed proves this unreachable.
                   (mv w1 fn-resource-ledger)
                 (mv-let (w2 g2 fn-resource-ledger)
                   (fn-rl-open 1 reserve fn-resource-ledger)
                   (declare (ignore g2))
                   (if (not (eq w2 :opened))
                       ; fn-rl-install-preflight-charges-succeed covers both branches.
                       (mv w2 fn-resource-ledger)
                     (mv :installed fn-resource-ledger)))))))))

; -----------------------------------------------------------------------------
; Fresh installation correspondence.  FN-RL-INSTALL has no served host caller
; yet; this is the concrete export's model boundary, not a deployment claim.
; Freshness constrains only the bank's initial charge and slot columns, plus
; the stobj type and zero count. Budget, ownership columns, and pool scalars
; need not be zero: installation overwrites the budget and the abstraction
; does not inspect the other fields. Thus the whole created stobj need not be
; an equality hypothesis. Empty bank columns are precisely their created shape.
(defun fn-rl-freshp (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger))
  (and (fn-resource-ledgerp fn-resource-ledger)
       (equal (fn-rl-count fn-resource-ledger) 0)
       (equal (fn-rl-drawn-list fn-resource-ledger) *fn-rv-zero*)
       (equal (fn-rl-phases-length fn-resource-ledger) 0)
       (equal (fn-rl-gens-length fn-resource-ledger) 0)
       (equal (fn-rl-c0-length fn-resource-ledger) 0)
       (equal (fn-rl-c1-length fn-resource-ledger) 0)
       (equal (fn-rl-c2-length fn-resource-ledger) 0)
       (equal (fn-rl-c3-length fn-resource-ledger) 0)
       (equal (fn-rl-c4-length fn-resource-ledger) 0)
       (equal (fn-rl-c5-length fn-resource-ledger) 0)
       (equal (fn-rl-c6-length fn-resource-ledger) 0)
       (equal (fn-rl-c7-length fn-resource-ledger) 0)
       (equal (fn-rl-c8-length fn-resource-ledger) 0)))

(defthm fn-rl-created-ledger-is-fresh
  (fn-rl-freshp (create-fn-resource-ledger))
  :rule-classes nil)

(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 ; The decision needs two logical rows, independently of the installed size.
(local
 (progn
(defthm fn-rl-logical-install-word-uses-two-slots
  (implies (and (natp nslots) (<= 2 nslots))
           (equal (car (fn-rv-install budget baseline reserve nslots))
                  (car (fn-rv-install budget baseline reserve 2))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-rv-install fn-rv-draw fn-rv-open fn-rv-charge
                 fn-rv-slotp fn-rv-slot-count fn-rv-phase fn-rv-gen fn-rv-row)
                (fn-rv-idle-rows nth update-nth fn-rv-make
                 fn-rv-budget fn-rv-drawn fn-rv-slots)))))
 ))
 (local (in-theory (disable fn-rl-logical-install-word-uses-two-slots)))
 ; Array reads and the two live rows followed by the untouched idle tail.
(local
 (progn
(defthm fn-rl-nth-member
  (implies (and (natp i) (< i (len xs)))
           (member-equal (nth i xs) xs))
  :hints (("Goal" :induct (nth i xs))))
(defthm fn-rl-resize-zero-members
  (implies (member-equal x (resize-list nil n 0))
           (equal x 0))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (resize-list nil n 0))))
(defthm fn-rl-len-resize
  (equal (len (resize-list xs n d)) (nfix n)))
(defthm fn-rl-nth-resize-zero
  (implies (and (natp i) (< i (nfix n)))
           (equal (nth i (resize-list nil n 0)) 0))
  :hints (("Goal" :use (:instance fn-rl-nth-member
                                  (xs (resize-list nil n 0)))
           :in-theory (disable fn-rl-nth-member resize-list nth))))
(defthm fn-rl-resize-empty
  (implies (and (equal (len xs) 0) (syntaxp (not (equal xs ''nil))))
           (equal (resize-list xs n 0) (resize-list nil n 0)))
  :hints (("Goal" :induct (resize-list xs n 0))))
(defthm fn-rl-vector-nine-fields
  (implies (fn-rv-vectorp v)
    (equal (list (nth 0 v) (nth 1 v) (nth 2 v) (nth 3 v)
                 (nth 4 v) (nth 5 v) (nth 6 v) (nth 7 v) (nth 8 v))
           v))
  :hints (("Goal" :in-theory (e/d (fn-rv-vectorp fn-rv-nats-p) (nth-add1))
           :expand ((len v)
                    (len (cdr v))
                    (len (cdr (cdr v)))
                    (len (cdr (cdr (cdr v))))
                    (len (cdr (cdr (cdr (cdr v)))))
                    (len (cdr (cdr (cdr (cdr (cdr v))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr v)))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr v))))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr v)))))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr v))))))))))
                    (:free (xs) (nth 0 xs))
                    (:free (xs) (nth 1 xs))
                    (:free (xs) (nth 2 xs))
                    (:free (xs) (nth 3 xs))
                    (:free (xs) (nth 4 xs))
                    (:free (xs) (nth 5 xs))
                    (:free (xs) (nth 6 xs))
                    (:free (xs) (nth 7 xs))
                    (:free (xs) (nth 8 xs))))))
 ))
(local
 (progn
(defthm fn-rl-installed-column-read
  (implies (and (equal col (update-nth 1 b (update-nth 0 a (resize-list nil n 0))))
                (natp i) (< i (nfix n)))
           (equal (nth i col) (cond ((equal i 0) a) ((equal i 1) b) (t 0))))
  :hints (("Goal" :in-theory (disable nth update-nth resize-list))))
 ))
(local
 (progn
(defthm fn-rl-installed-tail-fields
  (implies (and (natp i) (<= 2 i) (<= i (fn-rl-count ledger))
                (natp (fn-rl-count ledger))
                (<= 2 (fn-rl-count ledger))
                (equal (nth 3 ledger)
                       (update-nth 1 2 (update-nth 0 1 (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 4 ledger)
                       (update-nth 1 1 (update-nth 0 1 (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 5 ledger)
                       (update-nth 1 (nth 0 reserve)
                                   (update-nth 0 (nth 0 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 6 ledger)
                       (update-nth 1 (nth 1 reserve)
                                   (update-nth 0 (nth 1 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 7 ledger)
                       (update-nth 1 (nth 2 reserve)
                                   (update-nth 0 (nth 2 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 8 ledger)
                       (update-nth 1 (nth 3 reserve)
                                   (update-nth 0 (nth 3 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 9 ledger)
                       (update-nth 1 (nth 4 reserve)
                                   (update-nth 0 (nth 4 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 10 ledger)
                       (update-nth 1 (nth 5 reserve)
                                   (update-nth 0 (nth 5 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 11 ledger)
                       (update-nth 1 (nth 6 reserve)
                                   (update-nth 0 (nth 6 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 12 ledger)
                       (update-nth 1 (nth 7 reserve)
                                   (update-nth 0 (nth 7 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 13 ledger)
                       (update-nth 1 (nth 8 reserve)
                                   (update-nth 0 (nth 8 baseline) (resize-list nil (fn-rl-count ledger) 0)))))
           (equal (fn-rl-rows-from i ledger)
                  (fn-rv-idle-rows (- (fn-rl-count ledger) i))))
  :hints (("Goal" :induct (fn-rl-rows-from i ledger)
           :expand ((fn-rl-rows-from i ledger) (fn-rv-idle-rows (+ (- i) (fn-rl-count ledger))))
           :in-theory (e/d ((:induction fn-rl-rows-from))
                           ((:definition fn-rl-rows-from) fn-rv-idle-rows
                            resize-list nth update-nth fn-rl-count)))))

(defthm fn-rl-installed-row-fields
  (implies (and (fn-rv-vectorp baseline) (fn-rv-vectorp reserve)
                (natp (fn-rl-count ledger))
                (<= 2 (fn-rl-count ledger))
                (equal (nth 3 ledger)
                       (update-nth 1 2 (update-nth 0 1 (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 4 ledger)
                       (update-nth 1 1 (update-nth 0 1 (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 5 ledger)
                       (update-nth 1 (nth 0 reserve)
                                   (update-nth 0 (nth 0 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 6 ledger)
                       (update-nth 1 (nth 1 reserve)
                                   (update-nth 0 (nth 1 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 7 ledger)
                       (update-nth 1 (nth 2 reserve)
                                   (update-nth 0 (nth 2 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 8 ledger)
                       (update-nth 1 (nth 3 reserve)
                                   (update-nth 0 (nth 3 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 9 ledger)
                       (update-nth 1 (nth 4 reserve)
                                   (update-nth 0 (nth 4 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 10 ledger)
                       (update-nth 1 (nth 5 reserve)
                                   (update-nth 0 (nth 5 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 11 ledger)
                       (update-nth 1 (nth 6 reserve)
                                   (update-nth 0 (nth 6 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 12 ledger)
                       (update-nth 1 (nth 7 reserve)
                                   (update-nth 0 (nth 7 baseline) (resize-list nil (fn-rl-count ledger) 0))))
                (equal (nth 13 ledger)
                       (update-nth 1 (nth 8 reserve)
                                   (update-nth 0 (nth 8 baseline) (resize-list nil (fn-rl-count ledger) 0)))))
           (equal (fn-rl-rows-from 0 ledger)
                  (cons (list* 1 1 baseline)
                        (cons (list* 2 1 reserve)
                              (fn-rv-idle-rows (- (fn-rl-count ledger) 2))))))
  :hints (("Goal" :use (:instance fn-rl-installed-tail-fields (i 2))
 :expand ((fn-rl-rows-from 0 ledger)
                           (fn-rl-rows-from 1 ledger))
           :in-theory (disable fn-rl-rows-from resize-list nth update-nth fn-rl-count))))
 ))

 ; Expand the fixed nine coordinates once, then recover arbitrary vectors
 ; through fn-rl-vector-nine-fields. These are local implementation lemmas.
(local
 (progn
(defthm fn-rl-install-nine-fields
  (let ((budget (list b0 b1 b2 b3 b4 b5 b6 b7 b8))
        (baseline (list u0 u1 u2 u3 u4 u5 u6 u7 u8))
        (reserve (list r0 r1 r2 r3 r4 r5 r6 r7 r8)))
    (implies (and (fn-rl-freshp ledger)
                  (natp nslots) (<= 2 nslots)
                  (fn-rv-vectorp budget) (fn-rv-vectorp baseline)
                  (fn-rv-vectorp reserve)
                  (fn-rl-profile-representable-p budget nslots)
                  (fn-rv-below (fn-rv-plus baseline reserve) budget))
           (let* ((result (fn-rl-install budget baseline reserve nslots ledger))
                  (after (mv-nth 1 result)))
             (and (equal (mv-nth 0 result) :installed)
                  (equal (fn-rl-count after) nslots)
                  (equal (fn-rl-budget-list after) budget)
                  (equal (fn-rl-drawn-list after) (fn-rv-plus baseline reserve))
                  (equal (nth 3 after)
                       (update-nth 1 2
                                   (update-nth 0 1 (resize-list nil nslots 0))))
                  (equal (nth 4 after)
                       (update-nth 1 1
                                   (update-nth 0 1 (resize-list nil nslots 0))))
                  (equal (nth 5 after)
                       (update-nth 1 r0
                                   (update-nth 0 u0 (resize-list nil nslots 0))))
                  (equal (nth 6 after)
                       (update-nth 1 r1
                                   (update-nth 0 u1 (resize-list nil nslots 0))))
                  (equal (nth 7 after)
                       (update-nth 1 r2
                                   (update-nth 0 u2 (resize-list nil nslots 0))))
                  (equal (nth 8 after)
                       (update-nth 1 r3
                                   (update-nth 0 u3 (resize-list nil nslots 0))))
                  (equal (nth 9 after)
                       (update-nth 1 r4
                                   (update-nth 0 u4 (resize-list nil nslots 0))))
                  (equal (nth 10 after)
                       (update-nth 1 r5
                                   (update-nth 0 u5 (resize-list nil nslots 0))))
                  (equal (nth 11 after)
                       (update-nth 1 r6
                                   (update-nth 0 u6 (resize-list nil nslots 0))))
                  (equal (nth 12 after)
                       (update-nth 1 r7
                                   (update-nth 0 u7 (resize-list nil nslots 0))))
                  (equal (nth 13 after)
                       (update-nth 1 r8
                                   (update-nth 0 u8 (resize-list nil nslots 0))))))))
  :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-rv-install fn-rv-draw fn-rv-open fn-rv-charge
                fn-rv-slotp fn-rv-slot-count fn-rv-phase fn-rv-gen fn-rv-row
                fn-rv-vectorp fn-rv-nats-p fn-rv-below fn-rv-plus)
               (fn-resource-ledgerp fn-rv-idle-rows
                nth update-nth resize-list fn-rl-rows-from
                fn-rl-logical-install-word-uses-two-slots)))))
 ))
(local
 (progn
(defthm fn-rl-install-fields
  (implies (and (fn-rl-freshp ledger)
                  (natp nslots) (<= 2 nslots)
                  (fn-rv-vectorp budget) (fn-rv-vectorp baseline)
                  (fn-rv-vectorp reserve)
                  (fn-rl-profile-representable-p budget nslots)
                  (fn-rv-below (fn-rv-plus baseline reserve) budget))
           (let* ((result (fn-rl-install budget baseline reserve nslots ledger))
                  (after (mv-nth 1 result)))
             (and (equal (mv-nth 0 result) :installed)
                  (equal (fn-rl-count after) nslots)
                  (equal (fn-rl-budget-list after) budget)
                  (equal (fn-rl-drawn-list after) (fn-rv-plus baseline reserve))
                  (equal (nth 3 after)
                       (update-nth 1 2
                                   (update-nth 0 1 (resize-list nil nslots 0))))
                  (equal (nth 4 after)
                       (update-nth 1 1
                                   (update-nth 0 1 (resize-list nil nslots 0))))
                  (equal (nth 5 after)
                       (update-nth 1 (nth 0 reserve)
                                   (update-nth 0 (nth 0 baseline) (resize-list nil nslots 0))))
                  (equal (nth 6 after)
                       (update-nth 1 (nth 1 reserve)
                                   (update-nth 0 (nth 1 baseline) (resize-list nil nslots 0))))
                  (equal (nth 7 after)
                       (update-nth 1 (nth 2 reserve)
                                   (update-nth 0 (nth 2 baseline) (resize-list nil nslots 0))))
                  (equal (nth 8 after)
                       (update-nth 1 (nth 3 reserve)
                                   (update-nth 0 (nth 3 baseline) (resize-list nil nslots 0))))
                  (equal (nth 9 after)
                       (update-nth 1 (nth 4 reserve)
                                   (update-nth 0 (nth 4 baseline) (resize-list nil nslots 0))))
                  (equal (nth 10 after)
                       (update-nth 1 (nth 5 reserve)
                                   (update-nth 0 (nth 5 baseline) (resize-list nil nslots 0))))
                  (equal (nth 11 after)
                       (update-nth 1 (nth 6 reserve)
                                   (update-nth 0 (nth 6 baseline) (resize-list nil nslots 0))))
                  (equal (nth 12 after)
                       (update-nth 1 (nth 7 reserve)
                                   (update-nth 0 (nth 7 baseline) (resize-list nil nslots 0))))
                  (equal (nth 13 after)
                       (update-nth 1 (nth 8 reserve)
                                   (update-nth 0 (nth 8 baseline) (resize-list nil nslots 0)))))))
  :rule-classes nil
 :hints (("Goal" :use (:instance fn-rl-install-nine-fields (b0 (nth 0 budget))
                    (b1 (nth 1 budget))
                    (b2 (nth 2 budget))
                    (b3 (nth 3 budget))
                    (b4 (nth 4 budget))
                    (b5 (nth 5 budget))
                    (b6 (nth 6 budget))
                    (b7 (nth 7 budget))
                    (b8 (nth 8 budget))
                    (u0 (nth 0 baseline))
                    (u1 (nth 1 baseline))
                    (u2 (nth 2 baseline))
                    (u3 (nth 3 baseline))
                    (u4 (nth 4 baseline))
                    (u5 (nth 5 baseline))
                    (u6 (nth 6 baseline))
                    (u7 (nth 7 baseline))
                    (u8 (nth 8 baseline))
                    (r0 (nth 0 reserve))
                    (r1 (nth 1 reserve))
                    (r2 (nth 2 reserve))
                    (r3 (nth 3 reserve))
                    (r4 (nth 4 reserve))
                    (r5 (nth 5 reserve))
                    (r6 (nth 6 reserve))
                    (r7 (nth 7 reserve))
                    (r8 (nth 8 reserve)))
 :in-theory (disable fn-rl-install fn-rl-freshp fn-rl-profile-representable-p
                     fn-rl-count fn-rl-budget-list fn-rl-drawn-list
                     fn-rv-plus fn-rv-below fn-rv-vectorp nth update-nth))))
 ))
(local
 (progn
(defthm fn-rl-install-success-bank
  (implies (and (fn-rl-freshp ledger)
                (natp nslots) (<= 2 nslots)
                (fn-rv-vectorp budget) (fn-rv-vectorp baseline)
                (fn-rv-vectorp reserve)
                (fn-rl-profile-representable-p budget nslots)
                (fn-rv-below (fn-rv-plus baseline reserve) budget))
           (and
            (equal (mv-nth 0 (fn-rl-install budget baseline reserve nslots ledger))
                   :installed)
            (equal (fn-rl-bank (mv-nth 1 (fn-rl-install budget baseline reserve nslots ledger)))
                   (fn-rv-make budget (fn-rv-plus baseline reserve)
                               (cons (list* 1 1 baseline)
                                     (cons (list* 2 1 reserve)
                                           (fn-rv-idle-rows (- nslots 2))))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-rl-install-fields
                 (:instance fn-rl-installed-row-fields
                            (ledger (mv-nth 1 (fn-rl-install budget baseline reserve nslots ledger)))))
           :in-theory (e/d (fn-rl-bank)
                           (fn-rl-install fn-rl-freshp fn-rl-profile-representable-p
                            fn-rl-count fn-rl-budget-list fn-rl-drawn-list fn-rl-rows-from
                            fn-rv-make fn-rv-idle-rows fn-rv-plus fn-rv-below
                            fn-rv-vectorp nth update-nth)))))

(defthm fn-rl-logical-install-success-shape
  (implies (and (natp nslots) (<= 2 nslots)
                (fn-rv-vectorp budget) (fn-rv-vectorp baseline)
                (fn-rv-vectorp reserve)
                (fn-rv-below (fn-rv-plus baseline reserve) budget))
           (equal (fn-rv-install budget baseline reserve nslots)
                  (list :installed
                        (fn-rv-make budget (fn-rv-plus baseline reserve)
                                    (cons (list* 1 1 baseline)
                                          (cons (list* 2 1 reserve)
                                                (fn-rv-idle-rows (- nslots 2))))))))
  :hints (("Goal" :expand ((fn-rv-idle-rows nslots)
                            (fn-rv-idle-rows (+ -1 nslots)))
           :in-theory
           (e/d (fn-rv-install fn-rv-draw fn-rv-open fn-rv-charge
                 fn-rv-slotp fn-rv-slot-count fn-rv-phase fn-rv-gen fn-rv-row)
                (fn-rv-idle-rows nth fn-rv-make
                 fn-rv-budget fn-rv-drawn fn-rv-slots)))))
 ))
(local
 (progn
(defthm fn-rl-logical-install-admits-iff
  (implies (natp nslots)
           (equal (equal (car (fn-rv-install budget baseline reserve nslots)) :installed)
                  (and (fn-rv-vectorp budget) (<= 2 nslots)
                       (fn-rv-vectorp baseline) (fn-rv-vectorp reserve)
                       (fn-rv-below (fn-rv-plus baseline reserve) budget))))
  :hints (("Goal" :in-theory
           (e/d (fn-rv-install fn-rv-draw fn-rv-open fn-rv-charge
                 fn-rv-slotp fn-rv-slot-count fn-rv-phase fn-rv-gen fn-rv-row)
                (fn-rv-idle-rows nth update-nth fn-rv-make
                 fn-rv-budget fn-rv-drawn fn-rv-slots
                 fn-rl-logical-install-success-shape
                 fn-rl-logical-install-word-uses-two-slots)))))

(defthm fn-rl-fresh-count
  (implies (fn-rl-freshp ledger) (equal (fn-rl-count ledger) 0))
  :hints (("Goal" :in-theory (disable fn-resource-ledgerp))))

(defthm fn-rl-install-refused-before-store
  (implies
   (and (fn-rl-freshp ledger) (natp nslots)
        (or (not (fn-rl-profile-representable-p budget nslots))
            (not (equal (car (fn-rv-install budget baseline reserve nslots)) :installed))))
   (equal (fn-rl-install budget baseline reserve nslots ledger)
          (list (if (fn-rl-profile-representable-p budget nslots)
                    (car (fn-rv-install budget baseline reserve nslots))
                  :unrepresentable-profile)
                ledger)))
  :hints (("Goal" :use fn-rl-logical-install-word-uses-two-slots
 :in-theory
           (e/d (fn-rl-install)
                (fn-rl-freshp fn-rl-count fn-rl-profile-representable-p
                 fn-rl-draw fn-rl-open fn-rl-resize-all fn-rl-store-words-from
                 fn-rv-install fn-rl-logical-install-admits-iff
 fn-rl-logical-install-word-uses-two-slots)))))
 ))

 ; (a) exact word, with ONE named representation exception; (b) complete bank
 ; abstraction on success; (c) exact input ledger on every refusal.
(defthm fn-rl-install-correspondence
  (implies
   (and (fn-rl-freshp fn-resource-ledger)
        (true-listp budget) (true-listp baseline) (true-listp reserve)
        (natp nslots))
   (let* ((result (fn-rl-install budget baseline reserve nslots fn-resource-ledger))
          (word (mv-nth 0 result))
          (after (mv-nth 1 result))
          (logical (fn-rv-install budget baseline reserve nslots)))
     (and (equal word
                 (if (fn-rl-profile-representable-p budget nslots)
                     (car logical)
                   :unrepresentable-profile))
          (implies (equal word :installed)
                   (equal (fn-rl-bank after) (cadr logical)))
          (implies (not (equal word :installed))
                   (equal after fn-resource-ledger)))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((fn-rl-profile-representable-p budget nslots)
                   (equal (car (fn-rv-install budget baseline reserve nslots)) :installed))
           :use ((:instance fn-rl-install-success-bank (ledger fn-resource-ledger))
                 (:instance fn-rl-install-refused-before-store (ledger fn-resource-ledger)))
           :in-theory (disable fn-rl-install fn-rl-bank fn-rl-freshp
                               fn-rl-profile-representable-p
                               fn-rl-logical-install-word-uses-two-slots
                               fn-rv-install fn-rv-make fn-rv-idle-rows
                               fn-rv-vectorp fn-rv-plus fn-rv-below))))
(local
 (progn
(defthm fn-rl-charge-never-answers-installed
  (not (equal (mv-nth 0 (fn-rl-charge slot demand phase ledger)) :installed))
  :hints (("Goal" :in-theory
           (e/d (fn-rl-charge)
                (fn-rl-slotp fn-rl-fits-from fn-rl-charge-from
                 fn-rv-vectorp update-fn-rl-phasesi update-fn-rl-gensi)))))


(defthm fn-rl-charge-word-not-installed
  (not (equal (car (fn-rl-charge slot demand phase ledger)) :installed))
  :hints (("Goal" :use fn-rl-charge-never-answers-installed
           :in-theory (disable fn-rl-charge fn-rl-charge-never-answers-installed))))
 ))

 ; (d) Both post-mutation error branches are unreachable under the complete
 ; fresh, representable, logically admitted preflight antecedent.
(defthm fn-rl-install-preflight-charges-succeed
  (implies
   (and (fn-rl-freshp fn-resource-ledger)
        (true-listp budget) (true-listp baseline) (true-listp reserve)
        (natp nslots)
        (fn-rl-profile-representable-p budget nslots)
        (equal (car (fn-rv-install budget baseline reserve nslots)) :installed))
   (let* ((resized (fn-rl-resize-all nslots fn-resource-ledger))
          (stored (fn-rl-store-words-from 0 budget resized))
          (first (fn-rl-draw 0 baseline stored))
          (second (fn-rl-open 1 reserve (mv-nth 2 first))))
     (and (equal (mv-nth 0 first) :drawn)
          (equal (mv-nth 0 second) :opened))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-rl-logical-install-admits-iff
                 fn-rl-install-correspondence
                 fn-rl-logical-install-word-uses-two-slots)
           :in-theory
           (e/d (fn-rl-install fn-rl-draw fn-rl-open)
                (fn-rl-freshp fn-rl-count fn-rl-profile-representable-p
                 fn-rl-charge fn-rl-resize-all fn-rl-store-words-from
                 fn-rl-bank fn-rv-install
                 fn-rl-logical-install-admits-iff
                 fn-rl-logical-install-success-shape
                 fn-rl-logical-install-word-uses-two-slots
                 fn-rl-install-refused-before-store)))))
)

; -----------------------------------------------------------------------------
; The consumed flat ledger: guarded draw/settle, representation preservation,
; and receipt custody. These proofs use one shared family of array facts;
; no served call reconstructs or validates the complete logical bank.
(encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defmacro fn-rl-array-proof-facts (field bits)
  (let* ((base (symbol-name field))
         (pred (intern-in-package-of-symbol (concatenate 'string base "P") field))
         (read (intern-in-package-of-symbol (concatenate 'string base "I") field))
         (length (intern-in-package-of-symbol (concatenate 'string base "-LENGTH") field))
         (update (intern-in-package-of-symbol (concatenate 'string "UPDATE-" base "I") field))
         (nth-type (intern-in-package-of-symbol (concatenate 'string base "P-NTH-TYPE") field))
         (pred-update (intern-in-package-of-symbol (concatenate 'string base "P-UPDATE") field))
         (read-type (intern-in-package-of-symbol (concatenate 'string base "I-TYPE") field))
         (read-nat (intern-in-package-of-symbol (concatenate 'string base "I-NAT") field))
         (update-type (intern-in-package-of-symbol (concatenate 'string "FN-RL-UPDATE-" (subseq base 6 nil) "I-KEEPS-TYPE") field))
         (update-wfp (intern-in-package-of-symbol (concatenate 'string "FN-RL-UPDATE-" (subseq base 6 nil) "I-KEEPS-WFP") field)))
    `(progn
(defthm ,nth-type
 (implies (and (,pred xs) (natp i) (< i (len xs)))
          (unsigned-byte-p ,bits (nth i xs)))
 :hints (("Goal" :induct (nth i xs) :in-theory (enable ,pred))))
(defthm ,pred-update
 (implies (and (,pred xs) (natp i) (< i (len xs)) (unsigned-byte-p ,bits v))
          (,pred (update-nth i v xs)))
 :hints (("Goal" :induct (update-nth i v xs) :in-theory (enable ,pred))))
(defthm ,read-type
 (implies (and (fn-resource-ledgerp ledger) (natp i)
               (< i (,length ledger)))
          (unsigned-byte-p ,bits (,read i ledger)))
 :hints (("Goal" :in-theory (e/d (fn-resource-ledgerp ,read ,length)
                                (,pred unsigned-byte-p integer-range-p)))))
(defthm ,read-nat
 (implies (and (fn-resource-ledgerp ledger) (natp i)
               (< i (,length ledger)))
          (natp (,read i ledger)))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :use ,read-type :in-theory (e/d (unsigned-byte-p integer-range-p)
                     (fn-resource-ledgerp ,read ,length ,read-type)))))
(defthm ,update-type
 (implies (and (fn-resource-ledgerp ledger) (natp i) (< i (,length ledger))
               (unsigned-byte-p ,bits v))
          (fn-resource-ledgerp (,update i v ledger)))
 :hints (("Goal" :in-theory (e/d (fn-resource-ledgerp ,update ,length)
                                (fn-rl-budgetp fn-rl-drawnp fn-rl-phasesp fn-rl-gensp fn-rl-c0p fn-rl-c1p fn-rl-c2p fn-rl-c3p fn-rl-c4p fn-rl-c5p fn-rl-c6p fn-rl-c7p fn-rl-c8p unsigned-byte-p integer-range-p)))))
(defthm ,update-wfp
 (implies (and (fn-rl-wfp ledger) (natp i) (< i (,length ledger)))
          (fn-rl-wfp (,update i v ledger)))
 :hints (("Goal" :in-theory (enable fn-rl-wfp ,update ,length))))))))

(local (fn-rl-array-proof-facts fn-rl-budget 64))

(local (fn-rl-array-proof-facts fn-rl-drawn 64))

(local (fn-rl-array-proof-facts fn-rl-phases 8))

(local (fn-rl-array-proof-facts fn-rl-gens 64))

(local (fn-rl-array-proof-facts fn-rl-c0 64))

(local (fn-rl-array-proof-facts fn-rl-c1 64))

(local (fn-rl-array-proof-facts fn-rl-c2 64))

(local (fn-rl-array-proof-facts fn-rl-c3 64))

(local (fn-rl-array-proof-facts fn-rl-c4 64))

(local (fn-rl-array-proof-facts fn-rl-c5 64))

(local (fn-rl-array-proof-facts fn-rl-c6 64))

(local (fn-rl-array-proof-facts fn-rl-c7 64))

(local (fn-rl-array-proof-facts fn-rl-c8 64))

(local (defthm fn-rl-fixed-array-lengths
 (implies (fn-resource-ledgerp ledger)
          (and (equal (fn-rl-budget-length ledger) 9)
               (equal (fn-rl-drawn-length ledger) 9)))
 :hints (("Goal" :in-theory (e/d (fn-resource-ledgerp fn-rl-budget-length fn-rl-drawn-length)
            (fn-rl-budgetp fn-rl-drawnp))))))

(local (in-theory (disable fn-resource-ledgerp)))

(local (defthm fn-rl-nonempty-positive-len (implies (consp x) (< 0 (len x))) :rule-classes :linear))

(verify-guards fn-rl-fits-from
 :hints (("Goal" :in-theory (disable fn-rl-budgeti fn-rl-drawni fn-rl-budget-length fn-rl-drawn-length)
  :use ((:instance fn-rl-drawni-nat (i i) (ledger fn-resource-ledger))
        (:instance fn-rl-budgeti-nat (i i) (ledger fn-resource-ledger))))))

(local (defthm fn-rl-update-ci-keeps-type-and-wfp
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (fn-rl-slotp slot ledger) (natp i) (< i 9) (unsigned-byte-p 64 v))
          (and (fn-resource-ledgerp (fn-rl-update-ci i slot v ledger))
               (fn-rl-wfp (fn-rl-update-ci i slot v ledger))))
 :hints (("Goal" :in-theory (e/d (fn-rl-update-ci fn-rl-wfp fn-rl-slotp)
  (fn-resource-ledgerp update-fn-rl-c0i update-fn-rl-c1i update-fn-rl-c2i
   update-fn-rl-c3i update-fn-rl-c4i update-fn-rl-c5i update-fn-rl-c6i
   update-fn-rl-c7i update-fn-rl-c8i))))))

(local (defthm fn-rl-fits-from-update-drawn-before
 (implies (and (natp i) (natp j) (< j i))
  (equal (fn-rl-fits-from i demand (update-fn-rl-drawni j v ledger))
         (fn-rl-fits-from i demand ledger)))
 :hints (("Goal" :induct (fn-rl-fits-from i demand ledger)
          :in-theory (enable fn-rl-fits-from)))))

(local (defthm fn-rl-fits-from-update-ci
 (equal (fn-rl-fits-from i demand (fn-rl-update-ci j slot v ledger))
        (fn-rl-fits-from i demand ledger))
 :hints (("Goal" :induct (fn-rl-fits-from i demand ledger)
          :in-theory (enable fn-rl-fits-from fn-rl-update-ci)))))

(local (defthm fn-rl-update-ci-keeps-slotp
 (equal (fn-rl-slotp s (fn-rl-update-ci i slot v ledger)) (fn-rl-slotp s ledger))
 :hints (("Goal" :in-theory (enable fn-rl-slotp fn-rl-update-ci)))))

(local (defthm fn-rl-update-ci-keeps-count
 (equal (fn-rl-count (fn-rl-update-ci i slot v ledger)) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-update-ci) (nth update-nth))))))

(local (defthm fn-rl-update-ci-keeps-budgeti
 (equal (fn-rl-budgeti j (fn-rl-update-ci i slot v ledger)) (fn-rl-budgeti j ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-update-ci) (nth update-nth))))))

(local (defthm fn-rl-update-ci-keeps-drawni
 (equal (fn-rl-drawni j (fn-rl-update-ci i slot v ledger)) (fn-rl-drawni j ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-update-ci) (nth update-nth))))))

(local (defthm fn-rl-drawn-update-keeps-slotp
 (equal (fn-rl-slotp slot (update-fn-rl-drawni i v ledger)) (fn-rl-slotp slot ledger))
 :hints (("Goal" :in-theory (enable fn-rl-slotp)))))

(local (defthm fn-rl-fits-from-tail
 (implies (and (consp demand) (fn-rl-fits-from i demand ledger))
          (fn-rl-fits-from (+ 1 i) (cdr demand) ledger))
 :hints (("Goal" :expand ((fn-rl-fits-from i demand ledger))
  :in-theory (disable fn-rl-fits-from fn-rl-drawni fn-rl-budgeti)))))

(local (defthm fn-rl-fit-head-types
 (implies (and (fn-resource-ledgerp ledger) (natp i) (< i 9)
               (consp demand) (fn-rl-fits-from i demand ledger))
  (and (unsigned-byte-p 64 (+ (fn-rl-drawni i ledger) (nfix (car demand))))
       (unsigned-byte-p 64 (nfix (car demand)))))
 :hints (("Goal" :expand ((fn-rl-fits-from i demand ledger))
   :use ((:instance fn-rl-budgeti-type) (:instance fn-rl-drawni-type))
   :in-theory (e/d (unsigned-byte-p integer-range-p)
                   (fn-rl-fits-from fn-rl-budgeti fn-rl-drawni fn-rl-budget-length
                    fn-rl-drawn-length fn-resource-ledgerp fn-rl-budgeti-type fn-rl-drawni-type))))))

(local (defthm fn-rl-charge-one-preserves
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (fn-rl-slotp slot ledger) (natp i) (< i 9)
               (consp demand) (fn-rl-fits-from i demand ledger))
  (let ((after (fn-rl-update-ci i slot (nfix (car demand))
    (update-fn-rl-drawni i (+ (fn-rl-drawni i ledger) (nfix (car demand))) ledger))))
   (and (fn-resource-ledgerp after) (fn-rl-wfp after) (fn-rl-slotp slot after)
        (fn-rl-fits-from (+ 1 i) (cdr demand) after))))
 :hints (("Goal" :use (fn-rl-fit-head-types)
  :expand ((fn-rl-fits-from i demand ledger))
  :in-theory (e/d () (fn-rl-update-ci fn-rl-wfp fn-rl-slotp fn-resource-ledgerp
        update-fn-rl-drawni fn-rl-drawni fn-rl-budgeti fn-rl-fits-from fn-rl-fit-head-types nfix unsigned-byte-p integer-range-p))))))

(local (defthm fn-rl-charge-from-keeps-type-and-wfp
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (fn-rl-slotp slot ledger) (natp i) (true-listp demand)
               (<= (+ i (len demand)) 9) (fn-rl-fits-from i demand ledger))
          (and (fn-resource-ledgerp (fn-rl-charge-from i slot demand ledger))
               (fn-rl-wfp (fn-rl-charge-from i slot demand ledger))))
 :hints (("Goal" :induct (fn-rl-charge-from i slot demand ledger)
          :in-theory (e/d (fn-rl-charge-from)
            (fn-rl-update-ci fn-rl-wfp fn-resource-ledgerp fn-rl-drawni fn-rl-budgeti
             update-fn-rl-drawni fn-rl-fits-from fn-rl-slotp nfix unsigned-byte-p integer-range-p default-plus-1 default-plus-2)))
         ("Subgoal *1/2" :use fn-rl-charge-one-preserves
          :in-theory (e/d (fn-rl-charge-from) (fn-rl-charge-one-preserves fn-rl-update-ci fn-rl-wfp fn-resource-ledgerp fn-rl-drawni fn-rl-budgeti update-fn-rl-drawni fn-rl-fits-from fn-rl-slotp nfix unsigned-byte-p integer-range-p default-plus-1 default-plus-2))))))

(verify-guards fn-rl-charge-from
 :hints (("Goal" :use ((:instance fn-rl-fit-head-types (ledger fn-resource-ledger))
                      (:instance fn-rl-drawni-nat (ledger fn-resource-ledger)))
 :in-theory (disable fn-rl-fit-head-types fn-rl-drawni-nat fn-rl-update-ci fn-rl-wfp fn-resource-ledgerp
 fn-rl-drawni fn-rl-budgeti update-fn-rl-drawni fn-rl-fits-from fn-rl-slotp nfix unsigned-byte-p
 integer-range-p default-plus-1 default-plus-2))))

(local (defthm fn-rl-charge-from-frame
 (implies (and (natp f) (not (member-equal f '(1 5 6 7 8 9 10 11 12 13))))
  (equal (nth f (fn-rl-charge-from i slot demand ledger)) (nth f ledger)))
 :hints (("Goal" :induct (fn-rl-charge-from i slot demand ledger)
          :in-theory (e/d (fn-rl-charge-from fn-rl-update-ci) (nth update-nth))))))

(local (defthm fn-rl-charge-from-keeps-slotp
 (equal (fn-rl-slotp s (fn-rl-charge-from i slot demand ledger)) (fn-rl-slotp s ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-slotp fn-rl-count) (fn-rl-charge-from nth))))))

(local (defthm fn-rl-charge-from-keeps-gens-length
 (equal (fn-rl-gens-length (fn-rl-charge-from i slot demand ledger)) (fn-rl-gens-length ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-gens-length) (fn-rl-charge-from nth))))))

(local (defthm fn-rl-charge-from-keeps-phases-length
 (equal (fn-rl-phases-length (fn-rl-charge-from i slot demand ledger)) (fn-rl-phases-length ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-phases-length) (fn-rl-charge-from nth))))))

(local (defthm fn-rl-charge-from-keeps-gensi
 (equal (fn-rl-gensi s (fn-rl-charge-from i slot demand ledger)) (fn-rl-gensi s ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-gensi) (fn-rl-charge-from nth))))))

(local (defthm fn-rl-slot-bounds
 (implies (and (fn-rl-wfp ledger) (fn-rl-slotp slot ledger))
  (and (natp slot) (< slot (fn-rl-phases-length ledger))
                  (< slot (fn-rl-gens-length ledger))))
 :hints (("Goal" :in-theory (enable fn-rl-wfp fn-rl-slotp)))))

(local (defthm fn-rl-generation-increment-type
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (fn-rl-slotp slot ledger) (< (fn-rl-gensi slot ledger) *fn-rl-word-max*))
  (unsigned-byte-p 64 (+ 1 (fn-rl-gensi slot ledger))))
 :hints (("Goal" :use (:instance fn-rl-gensi-type (i slot))
   :in-theory (e/d (unsigned-byte-p integer-range-p)
                  (fn-rl-gensi fn-rl-gensi-type fn-rl-wfp fn-rl-slotp
                   fn-resource-ledgerp fn-rl-gens-length))))))

(local (defthm fn-rl-phase-update-keeps-gens-length
 (equal (fn-rl-gens-length (update-fn-rl-phasesi slot phase ledger)) (fn-rl-gens-length ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-gens-length update-fn-rl-phasesi) (nth update-nth))))))

(verify-guards fn-rl-charge
 :hints (("Goal" :use ((:instance fn-rl-gensi-nat (i slot) (ledger fn-resource-ledger))
                      (:instance fn-rl-generation-increment-type (ledger fn-resource-ledger))
                      (:instance fn-rl-slot-bounds (ledger fn-resource-ledger)))
 :in-theory (disable fn-rl-gensi-nat fn-rl-generation-increment-type
  fn-rl-slot-bounds fn-rl-gens-length fn-rl-phases-length fn-rl-wfp fn-rl-slotp fn-resource-ledgerp fn-rl-charge-from fn-rl-fits-from fn-rl-update-ci
  fn-rl-gensi fn-rl-phasesi update-fn-rl-phasesi update-fn-rl-gensi
  fn-rv-vectorp unsigned-byte-p integer-range-p default-plus-1 default-plus-2))))

(verify-guards fn-rl-draw)

(verify-guards fn-rl-open)

(local (defthm fn-rl-ci-type
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (fn-rl-slotp slot ledger)
               (natp i) (< i 9))
          (unsigned-byte-p 64 (fn-rl-ci i slot ledger)))
 :hints (("Goal" :use ((:instance fn-rl-c0i-type (i slot)) (:instance fn-rl-c1i-type (i slot)) (:instance fn-rl-c2i-type (i slot)) (:instance fn-rl-c3i-type (i slot)) (:instance fn-rl-c4i-type (i slot)) (:instance fn-rl-c5i-type (i slot)) (:instance fn-rl-c6i-type (i slot)) (:instance fn-rl-c7i-type (i slot)) (:instance fn-rl-c8i-type (i slot))) :in-theory (e/d (fn-rl-ci fn-rl-wfp fn-rl-slotp)
              (fn-rl-c0i fn-rl-c0i-type fn-rl-c1i fn-rl-c1i-type fn-rl-c2i fn-rl-c2i-type fn-rl-c3i fn-rl-c3i-type fn-rl-c4i fn-rl-c4i-type fn-rl-c5i fn-rl-c5i-type fn-rl-c6i fn-rl-c6i-type fn-rl-c7i fn-rl-c7i-type fn-rl-c8i fn-rl-c8i-type unsigned-byte-p integer-range-p))))))

(local (defthm fn-rl-ci-nat
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (fn-rl-slotp slot ledger) (natp i) (< i 9))
  (natp (fn-rl-ci i slot ledger)))
 :hints (("Goal" :use fn-rl-ci-type :in-theory (e/d (unsigned-byte-p integer-range-p)
  (fn-rl-ci-type fn-rl-ci fn-rl-wfp fn-rl-slotp))))))

(local (defthm fn-rl-release-head-type
 (implies (and (fn-resource-ledgerp ledger) (natp i) (< i 9) (natp d))
   (unsigned-byte-p 64 (nfix (- (fn-rl-drawni i ledger) d))))
 :hints (("Goal" :use fn-rl-drawni-type
   :in-theory (e/d (unsigned-byte-p integer-range-p)
       (fn-rl-drawni fn-rl-drawn-length fn-rl-drawni-type))))))

(local (defthm fn-rl-release-one-preserves
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (fn-rl-slotp slot ledger) (natp i) (< i 9))
  (let ((after (fn-rl-update-ci i slot 0
    (update-fn-rl-drawni i (nfix (- (fn-rl-drawni i ledger)
      (if (eql m 1) (fn-rl-ci i slot ledger) 0))) ledger))))
   (and (fn-resource-ledgerp after) (fn-rl-wfp after) (fn-rl-slotp slot after))))
 :hints (("Goal" :use (fn-rl-ci-nat
   (:instance fn-rl-release-head-type (d (if (eql m 1) (fn-rl-ci i slot ledger) 0))))
   :in-theory (disable fn-rl-ci-nat fn-rl-release-head-type fn-rl-ci fn-rl-update-ci
      fn-rl-wfp fn-rl-slotp fn-resource-ledgerp fn-rl-drawni update-fn-rl-drawni
      nfix unsigned-byte-p integer-range-p default-plus-1 default-plus-2 default-minus)))))

(local (defthm fn-rl-release-from-keeps-type-and-wfp
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (fn-rl-slotp slot ledger) (natp i) (true-listp mask)
               (<= (+ i (len mask)) 9))
          (and (fn-resource-ledgerp (fn-rl-release-from i slot mask ledger))
               (fn-rl-wfp (fn-rl-release-from i slot mask ledger))))
 :hints (("Goal" :induct (fn-rl-release-from i slot mask ledger)
  :in-theory (e/d (fn-rl-release-from)
    (fn-rl-ci fn-rl-update-ci fn-rl-wfp fn-rl-slotp fn-resource-ledgerp
     fn-rl-drawni fn-rl-budgeti update-fn-rl-drawni nfix unsigned-byte-p integer-range-p
     default-plus-1 default-plus-2 default-minus)))
  ("Subgoal *1/2" :use (:instance fn-rl-release-one-preserves (m (car mask)))
    :in-theory (e/d (fn-rl-release-from)
     (fn-rl-release-one-preserves fn-rl-ci fn-rl-update-ci fn-rl-wfp fn-rl-slotp fn-resource-ledgerp
      fn-rl-drawni update-fn-rl-drawni nfix unsigned-byte-p integer-range-p
      default-plus-1 default-plus-2 default-minus))))))

(local (defthm fn-rl-release-from-frame
 (implies (and (natp f) (not (member-equal f '(1 5 6 7 8 9 10 11 12 13))))
  (equal (nth f (fn-rl-release-from i slot mask ledger)) (nth f ledger)))
 :hints (("Goal" :induct (fn-rl-release-from i slot mask ledger)
          :in-theory (e/d (fn-rl-release-from fn-rl-update-ci) (nth update-nth))))))

(local (defthm fn-rl-release-from-keeps-slotp
 (equal (fn-rl-slotp s (fn-rl-release-from i slot mask ledger)) (fn-rl-slotp s ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-slotp fn-rl-count) (fn-rl-release-from nth))))))

(local (defthm fn-rl-release-from-keeps-gens-length
 (equal (fn-rl-gens-length (fn-rl-release-from i slot mask ledger)) (fn-rl-gens-length ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-gens-length) (fn-rl-release-from nth))))))

(local (defthm fn-rl-release-from-keeps-phases-length
 (equal (fn-rl-phases-length (fn-rl-release-from i slot mask ledger)) (fn-rl-phases-length ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-phases-length) (fn-rl-release-from nth))))))

(local (defthm fn-rl-release-from-keeps-gensi
 (equal (fn-rl-gensi s (fn-rl-release-from i slot mask ledger)) (fn-rl-gensi s ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-gensi) (fn-rl-release-from nth))))))

(verify-guards fn-rl-release-from
 :hints (("Goal" :use ((:instance fn-rl-ci-nat (ledger fn-resource-ledger))
  (:instance fn-rl-drawni-nat (ledger fn-resource-ledger))
  (:instance fn-rl-release-one-preserves (ledger fn-resource-ledger) (m (car mask)))
  (:instance fn-rl-release-head-type (ledger fn-resource-ledger)
     (d (if (eql (car mask) 1) (fn-rl-ci i slot fn-resource-ledger) 0))))
 :in-theory (disable fn-rl-release-head-type fn-rl-release-one-preserves fn-rl-ci-nat fn-rl-drawni-nat
  fn-rl-ci fn-rl-update-ci fn-rl-wfp fn-resource-ledgerp fn-rl-drawni fn-rl-budgeti update-fn-rl-drawni
  fn-rl-slotp nfix unsigned-byte-p integer-range-p default-plus-1 default-plus-2 default-minus))))

(verify-guards fn-rl-settle
 :hints (("Goal" :use (:instance fn-rl-slot-bounds (ledger fn-resource-ledger))
 :in-theory (disable fn-rl-slot-bounds fn-rl-gens-length fn-rl-phases-length fn-rl-wfp fn-rl-slotp
 fn-resource-ledgerp fn-rl-release-from fn-rl-gensi fn-rl-phasesi update-fn-rl-phasesi))))

(defthm fn-rl-charge-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (or (equal phase 1) (equal phase 2)))
  (and (fn-resource-ledgerp (mv-nth 2 (fn-rl-charge slot demand phase ledger)))
       (fn-rl-wfp (mv-nth 2 (fn-rl-charge slot demand phase ledger)))))
 :hints (("Goal" :use (fn-rl-generation-increment-type fn-rl-slot-bounds)
  :in-theory (e/d (fn-rl-charge)
   (fn-rl-generation-increment-type fn-rl-slot-bounds fn-rl-gens-length fn-rl-phases-length
    fn-rl-wfp fn-rl-slotp fn-resource-ledgerp fn-rl-charge-from fn-rl-fits-from fn-rl-update-ci
    fn-rl-gensi fn-rl-phasesi update-fn-rl-phasesi update-fn-rl-gensi
    fn-rv-vectorp unsigned-byte-p integer-range-p default-plus-1 default-plus-2)))))

(defthm fn-rl-draw-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (and (fn-resource-ledgerp (mv-nth 2 (fn-rl-draw slot demand ledger)))
       (fn-rl-wfp (mv-nth 2 (fn-rl-draw slot demand ledger)))))
 :hints (("Goal" :in-theory (e/d (fn-rl-draw) (fn-rl-charge fn-rl-wfp fn-resource-ledgerp)))))

(defthm fn-rl-settle-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (and (fn-resource-ledgerp (mv-nth 1 (fn-rl-settle slot gen ledger)))
       (fn-rl-wfp (mv-nth 1 (fn-rl-settle slot gen ledger)))))
 :hints (("Goal" :use fn-rl-slot-bounds
  :in-theory (e/d (fn-rl-settle)
   (fn-rl-slot-bounds fn-rl-gens-length fn-rl-phases-length fn-rl-wfp fn-rl-slotp fn-resource-ledgerp
    fn-rl-release-from fn-rl-gensi fn-rl-phasesi update-fn-rl-phasesi)))))

(defthm fn-rl-draw-preserves-worker-receipts
 (let ((after (mv-nth 2 (fn-rl-draw slot demand ledger))))
  (and (equal (fn-rl-worker-resident after) (fn-rl-worker-resident ledger))
       (equal (fn-rl-worker-operation after) (fn-rl-worker-operation ledger))
       (equal (fn-rl-worker-physical after) (fn-rl-worker-physical ledger))
       (equal (fn-rl-worker-outcome after) (fn-rl-worker-outcome ledger))))
 :hints (("Goal" :in-theory (e/d (fn-rl-draw fn-rl-charge)
                 (fn-rl-charge-from fn-rl-gensi fn-rl-phasesi fn-rl-fits-from nth update-nth)))))

(defthm fn-rl-settle-preserves-worker-receipts
 (let ((after (mv-nth 1 (fn-rl-settle slot gen ledger))))
  (and (equal (fn-rl-worker-resident after) (fn-rl-worker-resident ledger))
       (equal (fn-rl-worker-operation after) (fn-rl-worker-operation ledger))
       (equal (fn-rl-worker-physical after) (fn-rl-worker-physical ledger))
       (equal (fn-rl-worker-outcome after) (fn-rl-worker-outcome ledger))))
 :hints (("Goal" :in-theory (e/d (fn-rl-settle)
                 (fn-rl-release-from fn-rl-gensi fn-rl-phasesi nth update-nth)))))
)
