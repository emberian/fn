; fn: ONE accounting -- the existing mechanisms as projections of the
; resource vector (lane resource-ledger, 2026-10-01; planning/design-store-
; representation-2026-10-01.md section 2 and stage 6: "the credit ledger
; and heap figure related by theorem").  Four mechanisms exist at dev, each
; certified, each its own arithmetic:
;
;   Codex's cold-read gate     books/page-read-resources.lisp  fn-prs-fundedp
;                              over a 5-vector (resident disk descriptors
;                              workers read-ids): U + R + C <= B
;   the credit ledger PRF-380  books/memory-credits.lisp  fn-mcr-fundedp:
;                              BASE + CACHE + sum(U_i + R_i) + COMPLETION +
;                              RUNTIME <= BUDGET, resident octets only
;   the heap reservation       books/heap-reservation.lisp
;   PRF-198 / HST-013          fn-heap-reserve-decide: the dynamic space,
;                              the core and THREADS stacks fit the machine
;   the connection budget      books/connection-budget.lisp
;   PRF-223                    fn-cbud-run-decide: CAPACITY connections'
;                              resident octets fit the machine
;
; This book and books/resource-vector-relations-heap.lisp (the heap and
; connection relations, whose include closure is the owner's, so they are
; certified on the farm) state each as a bank (books/resource-vector.lisp)
; and prove the relation, so that there is one invariant, fn-rv-okp, of
; which each is a coordinate or a sum of coordinates:
;
;   fn-rv-prs-vector-is-the-prefix      Codex's 5-vector is this vector's
;                                       prefix: + and <= agree under the
;                                       embedding, and "release the reusable
;                                       coordinates only" is fn-rv-settle's
;                                       reusable/spent split
;   fn-rv-prs-gate-is-a-funded-root     fn-prs-fundedp B U R C is exactly
;                                       fn-rv-okp of the root bank whose
;                                       three rows are U (drawn), R (a
;                                       sub-bank) and C (drawn)
;   fn-rv-credit-ledger-is-the-resident-coordinate
;                                       a funded fn-mcr ledger is an okp bank
;                                       whose rows are its terms and whose
;                                       every coordinate but :resident is 0;
;                                       funded iff the resident coordinate
;                                       is (fn-rv-credit-ledger-funded-iff)
;   fn-rv-heap-reservation-funds-the-root
;                                       an accepted reservation is a funded
;                                       root whose :resident coordinate is
;                                       the reservation's octets against
;                                       the machine's and whose :workers
;                                       coordinate is the threads
;   fn-rv-connection-budget-funds-the-root
;                                       a held capacity is a funded root
;                                       whose :resident coordinate is the
;                                       resident figure of CAPACITY
;                                       connections against the machine
;
; What this does not do: move any mechanism onto the vector (stage 6's
; definterface :operation lane does that, specs/resource-vector.md) or
; claim that the four budgets are one number -- they are projections of
; different roots (the launcher's, the owner's, the cold pool's), related
; here by shape, to be unified by the operation layer.

(in-package "ACL2")
(include-book "resource-vector")
(include-book "page-read-resources")
(include-book "memory-credits")

(local (include-book "arithmetic-5/top" :dir :system))

; Codex's book closes its definitions; the relations open them.
(local (in-theory (enable fn-prs-nats-p fn-prs-vectorp fn-prs-plus fn-prs-below
                          fn-prs-fundedp)))

; -----------------------------------------------------------------------------
; Codex's fn-prs vector is the prefix.

(defconst *fn-rv-prs-k* 5)

(defun fn-rv-of-prs (v)
  (declare (xargs :guard (true-listp v)))
  (append v (fn-rv-zeros (- *fn-rv-k* *fn-rv-prs-k*))))

(local
 (defun fn-rv-ind2 (a b)
   (declare (xargs :measure (+ (acl2-count a) (acl2-count b))))
   (if (or (consp a) (consp b)) (fn-rv-ind2 (cdr a) (cdr b)) nil)))

(local
 (defthm fn-rv-nats-p-of-append
   (implies (and (fn-prs-nats-p a) (fn-rv-nats-p b))
            (fn-rv-nats-p (append a b)))
   :hints (("Goal" :in-theory (enable fn-rv-nats-p)))))

(local
 (defthm fn-rv-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-rv-prs-plus-of-append
   (implies (and (fn-prs-nats-p a) (fn-prs-nats-p b) (equal (len a) (len b)))
            (equal (fn-rv-plus (append a c) (append b d))
                   (append (fn-prs-plus a b) (fn-rv-plus c d))))
   :hints (("Goal" :induct (fn-rv-ind2 a b) :in-theory (enable fn-rv-plus)))))

(local
 (defthm fn-rv-prs-below-of-append
   (implies (and (fn-prs-nats-p a) (fn-prs-nats-p b) (equal (len a) (len b)))
            (equal (fn-rv-below (append a c) (append b d))
                   (and (fn-prs-below a b) (fn-rv-below c d))))
   :hints (("Goal" :induct (fn-rv-ind2 a b) :in-theory (enable fn-rv-below)))))

(defthm fn-rv-prs-vector-is-the-prefix
  (implies (fn-prs-vectorp v)
           (fn-rv-vectorp (fn-rv-of-prs v)))
  :hints (("Goal" :in-theory (enable fn-rv-vectorp))))

(defthm fn-rv-prs-plus-is-plus
  (implies (and (fn-prs-vectorp a) (fn-prs-vectorp b))
           (equal (fn-rv-of-prs (fn-prs-plus a b))
                  (fn-rv-plus (fn-rv-of-prs a) (fn-rv-of-prs b)))))

(defthm fn-rv-prs-below-is-below
  (implies (and (fn-prs-vectorp a) (fn-prs-vectorp b))
           (equal (fn-prs-below a b)
                  (fn-rv-below (fn-rv-of-prs a) (fn-rv-of-prs b)))))

; The gate's four vectors as the root bank: U at slot 0 (drawn), R at slot
; 1 (a sub-bank), C at slot 2 (drawn).
(defun fn-rv-prs-root (budget used rescue charged)
  (declare (xargs :guard (and (true-listp budget) (true-listp used)
                              (true-listp rescue) (true-listp charged))))
  (fn-rv-make (fn-rv-of-prs budget)
              (fn-rv-of-prs (fn-prs-plus used (fn-prs-plus rescue charged)))
              (list (cons 1 (fn-rv-of-prs used))
                    (cons 2 (fn-rv-of-prs rescue))
                    (cons 1 (fn-rv-of-prs charged)))))

(defthm fn-rv-prs-gate-is-a-funded-root
  (implies (and (fn-prs-vectorp budget) (fn-prs-vectorp used)
                (fn-prs-vectorp rescue) (fn-prs-vectorp charged))
           (equal (fn-prs-fundedp budget used rescue charged)
                  (fn-rv-okp (fn-rv-prs-root budget used rescue charged))))
  :hints (("Goal" :in-theory (e/d (fn-rv-okp fn-rv-bankp fn-rv-outstanding fn-rv-row-demand
                                   fn-rv-rowsp fn-rv-rowp fn-prs-fundedp)
                                  (fn-rv-of-prs fn-prs-vectorp fn-prs-plus fn-prs-below)))))

; -----------------------------------------------------------------------------
; PRF-380's credit ledger is the :resident coordinate.

(defun fn-rv-resident (n)
  (declare (xargs :guard (natp n)))
  (fn-rv-unit 0 n))

(defun fn-rv-credit-rows (ops)
  (declare (xargs :guard t))
  (if (consp ops)
      (cons (cons 1 (fn-rv-resident (if (consp (car ops))
                                        (+ (fn-mcr-op-owned (cdar ops))
                                           (fn-mcr-op-reserved (cdar ops)))
                                      0)))
            (fn-rv-credit-rows (cdr ops)))
    nil))

; The ledger as a bank: BASE drawn at slot 0 (the owner's baseline),
; COMPLETION and RUNTIME as sub-banks (the reserves), CACHE drawn, then one
; drawn row an operation (U_i + R_i).
(defun fn-rv-bank-of-credits (l)
  (declare (xargs :guard t))
  (fn-rv-make (fn-rv-resident (fn-mcr-budget l))
              (fn-rv-resident (fn-mcr-total l))
              (list* (cons 1 (fn-rv-resident (fn-mcr-base l)))
                     (cons 2 (fn-rv-resident (fn-mcr-completion l)))
                     (cons 2 (fn-rv-resident (fn-mcr-runtime l)))
                     (cons 1 (fn-rv-resident (fn-mcr-cache l)))
                     (fn-rv-credit-rows (fn-mcr-ops l)))))

(local
 (defthm fn-rv-resident-plus
   (implies (and (natp a) (natp b))
            (equal (fn-rv-plus (fn-rv-resident a) (fn-rv-resident b))
                   (fn-rv-resident (+ a b))))
   :hints (("Goal" :in-theory (enable fn-rv-plus)))))

(local
 (defthm fn-rv-resident-vectorp
   (implies (natp n) (fn-rv-vectorp (fn-rv-resident n)))
   :hints (("Goal" :in-theory (enable fn-rv-vectorp fn-rv-nats-p)))))

(local
 (defthm fn-rv-resident-below
   (implies (and (natp a) (natp b))
            (equal (fn-rv-below (fn-rv-resident a) (fn-rv-resident b)) (<= a b)))
   :hints (("Goal" :in-theory (enable fn-rv-below)))))

(local
 (defthm fn-rv-resident-zero
   (equal (fn-rv-resident 0) *fn-rv-zero*)))

(local
 (defthm fn-rv-credit-rows-rowsp
   (fn-rv-rowsp (fn-rv-credit-rows ops))
   :hints (("Goal" :in-theory (e/d (fn-rv-rowsp fn-rv-rowp) (fn-rv-resident fn-rv-unit))))))

(local
 (defthm fn-rv-credit-rows-outstanding
   (equal (fn-rv-outstanding (fn-rv-credit-rows ops))
          (fn-rv-resident (fn-mcr-ops-credit ops)))
   :hints (("Goal" :in-theory (e/d (fn-rv-outstanding fn-mcr-ops-credit)
                                   (fn-rv-resident fn-rv-unit))))))

(defthm fn-rv-credit-ledger-funded-iff
  (equal (fn-rv-fundedp (fn-rv-bank-of-credits l))
         (<= (fn-mcr-total l) (fn-mcr-budget l)))
  :hints (("Goal" :in-theory (e/d (fn-rv-fundedp fn-rv-bankp) (fn-rv-resident fn-rv-unit fn-mcr-total)))))

; NEXT (lane resource-ledger): fn-rv-credit-ledger-is-the-resident-coordinate,
; (implies (<= (fn-mcr-total l) (fn-mcr-budget l)) (fn-rv-okp (fn-rv-bank-of-credits l))),
; refused at the last probe only on (fn-rv-below *fn-rv-zero* (fn-rv-resident budget))
; in the all-zero case; see LANEDUMP.md.
