; Teeth for books/resource-vector-relations (lane resource-ledger,
; 2026-10-01): Codex's fn-prs gate and PRF-380's credit ledger evaluated
; beside their resource-vector projections on concrete values -- the
; embedding, agreement of + and <=, the gate's verdict against the root
; bank's okp on a funded and an unfunded case, and a small node's credit
; ledger as an okp bank whose only coordinate is :resident.
(in-package "ACL2")
(include-book "../../books/resource-vector-relations")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *rvrt-mib* 1048576)

;; Codex's vectors: resident, disk, descriptors, workers, read-ids.
(defconst *rvrt-b* (list (* 64 *rvrt-mib*) 0 16 4 100))
(defconst *rvrt-u* (list (* 16 *rvrt-mib*) 0 2 1 0))
(defconst *rvrt-r* (list (* 8 *rvrt-mib*) 0 1 1 0))
(defconst *rvrt-c* (list (* 32 *rvrt-mib*) 0 3 2 7))
(defconst *rvrt-c-big* (list (* 48 *rvrt-mib*) 0 3 2 7))

(assert! (equal (fn-rv-of-prs *rvrt-b*) (list (* 64 *rvrt-mib*) 0 16 4 100 0 0 0 0)))
(assert! (fn-rv-vectorp (fn-rv-of-prs *rvrt-b*)))
(assert! (equal (fn-rv-of-prs (fn-prs-plus *rvrt-u* *rvrt-c*))
                (fn-rv-plus (fn-rv-of-prs *rvrt-u*) (fn-rv-of-prs *rvrt-c*))))
(assert! (equal (fn-prs-below *rvrt-c* *rvrt-b*)
                (fn-rv-below (fn-rv-of-prs *rvrt-c*) (fn-rv-of-prs *rvrt-b*))))
(assert! (equal (fn-prs-below *rvrt-b* *rvrt-c*)
                (fn-rv-below (fn-rv-of-prs *rvrt-b*) (fn-rv-of-prs *rvrt-c*))))

;; The gate's verdict is the root bank's okp: funded with C, not with C-big
;; (16 + 8 + 48 MiB exceeds 64).
(assert! (fn-prs-fundedp *rvrt-b* *rvrt-u* *rvrt-r* *rvrt-c*))
(assert! (fn-rv-okp (fn-rv-prs-root *rvrt-b* *rvrt-u* *rvrt-r* *rvrt-c*)))
(assert! (not (fn-prs-fundedp *rvrt-b* *rvrt-u* *rvrt-r* *rvrt-c-big*)))
(assert! (not (fn-rv-okp (fn-rv-prs-root *rvrt-b* *rvrt-u* *rvrt-r* *rvrt-c-big*))))
(assert! (equal (fn-rv-row 1 (fn-rv-prs-root *rvrt-b* *rvrt-u* *rvrt-r* *rvrt-c*))
                (list* 2 0 (fn-rv-of-prs *rvrt-r*))))
(assert! (equal (fn-rv-slack (fn-rv-prs-root *rvrt-b* *rvrt-u* *rvrt-r* *rvrt-c*))
                (list (* 8 *rvrt-mib*) 0 10 0 93 0 0 0 0)))

;; PRF-380's ledger (memory-credits-tests' small node): B 256 MiB, base 160
;; MiB, completion 8 MiB, runtime 16 MiB, no cache, two operations.
(defconst *rvrt-l*
  (fn-mcr-make (* 256 *rvrt-mib*) (* 160 *rvrt-mib*) 0 (* 8 *rvrt-mib*) (* 16 *rvrt-mib*) 0
               (list (cons 1 (cons 40000 1549248)) (cons 2 (cons 0 1589248)))))
(assert! (fn-mcr-fundedp *rvrt-l*))
(assert! (fn-rv-okp (fn-rv-bank-of-credits *rvrt-l*)))  ; evaluated; the theorem is NEXT
(assert! (fn-rv-fundedp (fn-rv-bank-of-credits *rvrt-l*)))
(assert! (equal (fn-rv-drawn (fn-rv-bank-of-credits *rvrt-l*))
                (fn-rv-resident (fn-mcr-total *rvrt-l*))))
(assert! (equal (fn-rv-at 0 (fn-rv-drawn (fn-rv-bank-of-credits *rvrt-l*)))
                (+ (* 184 *rvrt-mib*) 40000 1549248 1589248)))
(assert! (equal (fn-rv-spent (fn-rv-drawn (fn-rv-bank-of-credits *rvrt-l*))) *fn-rv-zero*))
(assert! (equal (fn-rv-slot-count (fn-rv-bank-of-credits *rvrt-l*)) 6))
;; A ledger past its budget is not an okp bank, and not funded.
(defconst *rvrt-l-past*
  (fn-mcr-make (* 256 *rvrt-mib*) (* 250 *rvrt-mib*) 0 (* 8 *rvrt-mib*) (* 16 *rvrt-mib*) 0 nil))
(assert! (not (fn-mcr-fundedp *rvrt-l-past*)))
(assert! (not (fn-rv-fundedp (fn-rv-bank-of-credits *rvrt-l-past*))))
(assert! (not (fn-rv-okp (fn-rv-bank-of-credits *rvrt-l-past*))))

;; Literal relation teeth (r18 F3).  These are the four proved relations
;; named by specs/resource-vector.md: prefix, plus, below, and funded root.
;; The credit-funded-by-definition projection is explicitly not a keystone;
;; the credit consistency and heap/connection relations are not proved here.

(defkeystone rvrt-prefix-teeth
  (implies (fn-prs-vectorp v)
           (fn-rv-vectorp (fn-rv-of-prs v)))
  :subject fn-rv-of-prs
  :mutations (:none "hypothesis removals only")
  :restates fn-rv-prs-vector-is-the-prefix
  :hyps (vector)
  :witness ((v *rvrt-b*))
  :breaks ((vector ((v nil))))
  :hints (("Goal" :by fn-rv-prs-vector-is-the-prefix)))

(defkeystone rvrt-plus-teeth
  (implies (and (fn-prs-vectorp a) (fn-prs-vectorp b))
           (equal (fn-rv-of-prs (fn-prs-plus a b))
                  (fn-rv-plus (fn-rv-of-prs a) (fn-rv-of-prs b))))
  :subject fn-prs-plus
  :mutations (:none "hypothesis removals only")
  :restates fn-rv-prs-plus-is-plus
  :hyps (a-vector b-vector)
  :witness ((a *rvrt-u*) (b *rvrt-c*))
  :breaks ((a-vector ((a nil)))
           (b-vector ((b '(0 0 0 0 0 1)))))
  :hints (("Goal" :by fn-rv-prs-plus-is-plus)))

;; Corrupted-input removal witnesses: a dotted tail is outside the logical
;; vector domain. APPEND in the embedding discards that tail, producing a
;; well-formed bank even though the original gate rejects the input. Each
;; case changes only one input; defkeystone checks all retained hypotheses,
;; failure of that input's hypothesis, and failure of the literal equality.
(defkeystone rvrt-funded-root-teeth
  (implies (and (fn-prs-vectorp budget) (fn-prs-vectorp used)
                (fn-prs-vectorp rescue) (fn-prs-vectorp charged))
           (equal (fn-prs-fundedp budget used rescue charged)
                  (fn-rv-okp (fn-rv-prs-root budget used rescue charged))))
  :subject fn-prs-fundedp
  :mutations (:none "hypothesis removals only")
  :restates fn-rv-prs-gate-is-a-funded-root
  :hyps (budget-vector used-vector rescue-vector charged-vector)
  :witness ((budget *rvrt-b*) (used *rvrt-u*)
            (rescue *rvrt-r*) (charged *rvrt-c*))
  :breaks ((budget-vector ((budget (append *rvrt-b* 'bad-tail)))
                          :corrupt "dotted budget; embedding drops its tail")
           (used-vector ((used (append *rvrt-u* 'bad-tail)))
                        :corrupt "dotted used; embedding drops its tail")
           (rescue-vector ((rescue (append *rvrt-r* 'bad-tail)))
                          :corrupt "dotted rescue; embedding drops its tail")
           (charged-vector ((charged (append *rvrt-c* 'bad-tail)))
                           :corrupt "dotted charged; embedding drops its tail"))
  :hints (("Goal" :by fn-rv-prs-gate-is-a-funded-root)))

;; fn-rv-prs-below-is-below: full-antecedent positive witness.  No breaking
;; value is claimed for either shape hypothesis: both comparators use NFIX,
;; missing coordinates are zero, and the embedding only appends zeros.
;; defkeystone requires a breaking value for every hypothesis, so use
;; assert-event here and retain the theorem exactly as supplied.
(assert-event
 (let ((a *rvrt-c*) (b *rvrt-b*))
   (and (fn-prs-vectorp a) (fn-prs-vectorp b)
        (equal (fn-prs-below a b)
               (fn-rv-below (fn-rv-of-prs a) (fn-rv-of-prs b)))))
 :msg "fn-rv-prs-below-is-below: full-antecedent positive witness")

;; Redundancy evidence, NOT removal witnesses: the omitted hypothesis
;; fails, the other holds, but the conclusion still holds (true and false
;; comparator outcomes respectively).
(assert-event
 (let ((a nil) (b *rvrt-b*))
   (and (not (fn-prs-vectorp a)) (fn-prs-vectorp b)
        (fn-prs-below a b)
        (equal (fn-prs-below a b)
               (fn-rv-below (fn-rv-of-prs a) (fn-rv-of-prs b)))))
 :msg "below: a-vector omitted, equality survives; not a removal witness")
(assert-event
 (let ((a *rvrt-c*) (b nil))
   (and (fn-prs-vectorp a) (not (fn-prs-vectorp b))
        (not (fn-prs-below a b))
        (equal (fn-prs-below a b)
               (fn-rv-below (fn-rv-of-prs a) (fn-rv-of-prs b)))))
 :msg "below: b-vector omitted, equality survives; not a removal witness")
