; fn: memory admission by credits (lane f8-reservation, 2026-09-28; D35 F8
; as split by ember 18:15Z; planning/review-2026-09-28-gpt6.md, "Memory and
; zero-copy calls").
;
; The heap figure (books/heap-store-figure.lisp) reserves the worst case of
; every term for the whole run.  The successor model admits WORK instead:
; an operation acquires CREDIT before it allocates -- what it owns now (U)
; and what it may still need to finish (R) -- and the ledger keeps
;
;     M_base + M_cache + sum_i (U_i + R_i) + E_completion + E_runtime <= B
;
; where M_base is the fixed runtime (image, threads, collector headroom),
; M_cache the octets the cache actually holds (credit comes back only after
; an actual eviction or unpinning), E_completion a separately funded bounded
; reserve an admitted operation may overdraw to finish, and E_runtime the
; runtime's own separately funded reserve.  Measurements tune the estimates
; U and R; they never authorise an allocation.
;
; The ledger: (BUDGET BASE CACHE COMPLETION RUNTIME DRAWN OPS), OPS an alist
; from an operation id to (U . R), DRAWN what operations have overdrawn of
; the completion reserve (at most COMPLETION).  Every transition returns
; (:ok LEDGER') or (:refused REASON); a refusal leaves the ledger unchanged.
;
;   fn-mcr-acquire  id U R   admit a new operation: refused by name when the
;                            credit does not fit (credit before allocation)
;   fn-mcr-grow     id X     move X of an operation's reserve to what it
;                            owns: never refused within the reserve (reserve
;                            to finish); the funded total is unchanged
;   fn-mcr-retain   id X     the operation's result becomes cache: X of what
;                            it owns moves to the cache, the rest and its
;                            reserve come back (the same credit follows the
;                            buffer; nothing counted twice or dropped)
;   fn-mcr-release  id       the operation's memory was freed: its credit
;                            comes back (the host calls it after the free,
;                            never on a client's timeout alone)
;   fn-mcr-evict    X        the cache released X octets: credit back, at
;                            most what the cache holds
;   fn-mcr-overdraw id X     an admitted operation needs X past its reserve
;                            to finish: drawn from the completion reserve,
;                            refused past it; the funded total is unchanged
;
; KEYSTONE fn-mcr-transitions-keep-funded: from a funded ledger every
; transition's result is funded.  With fn-mcr-acquire-refuses-exactly-past-
; the-budget, fn-mcr-grow-within-the-reserve-is-admitted and the
; conservation theorems (grow, overdraw: the total unchanged; retain: the
; retained octets move, the rest returns) they are the credit model's
; contract; the host's allocation sites are its subjects (the article slots
; of books/owner-article-slots.lisp are its first instance: U + R = one
; reserve a slot).

(in-package "ACL2")

(defun fn-mcr-op-owned (op) (declare (xargs :guard t)) (if (consp op) (nfix (car op)) 0))
(defun fn-mcr-op-reserved (op) (declare (xargs :guard t)) (if (consp op) (nfix (cdr op)) 0))

(defun fn-mcr-ops-credit (ops)
  (declare (xargs :guard t))
  (if (consp ops)
      (+ (if (consp (car ops))
             (+ (fn-mcr-op-owned (cdar ops)) (fn-mcr-op-reserved (cdar ops)))
           0)
         (fn-mcr-ops-credit (cdr ops)))
    0))

(defun fn-mcr-make (budget base cache completion runtime drawn ops)
  (declare (xargs :guard t))
  (list (nfix budget) (nfix base) (nfix cache) (nfix completion) (nfix runtime) (nfix drawn) ops))

(defun fn-mcr-budget (l) (declare (xargs :guard t)) (nfix (nth 0 (true-list-fix l))))
(defun fn-mcr-base (l) (declare (xargs :guard t)) (nfix (nth 1 (true-list-fix l))))
(defun fn-mcr-cache (l) (declare (xargs :guard t)) (nfix (nth 2 (true-list-fix l))))
(defun fn-mcr-completion (l) (declare (xargs :guard t)) (nfix (nth 3 (true-list-fix l))))
(defun fn-mcr-runtime (l) (declare (xargs :guard t)) (nfix (nth 4 (true-list-fix l))))
(defun fn-mcr-drawn (l) (declare (xargs :guard t)) (nfix (nth 5 (true-list-fix l))))
(defun fn-mcr-ops (l) (declare (xargs :guard t)) (nth 6 (true-list-fix l)))

; The funded total: every term of the equation.  The completion reserve is
; funded whole whether or not it is drawn (what is drawn of it is inside it).
(defun fn-mcr-total (l)
  (declare (xargs :guard t))
  (+ (fn-mcr-base l) (fn-mcr-cache l) (fn-mcr-ops-credit (fn-mcr-ops l))
     (fn-mcr-completion l) (fn-mcr-runtime l)))

; One entry an operation: each operation's credit is counted once.
(defun fn-mcr-opsp (ops)
  (declare (xargs :guard t))
  (and (alistp ops) (no-duplicatesp-equal (strip-cars ops))))

(defun fn-mcr-fundedp (l)
  (declare (xargs :guard t))
  (and (fn-mcr-opsp (fn-mcr-ops l))
       (<= (fn-mcr-total l) (fn-mcr-budget l))
       (<= (fn-mcr-drawn l) (fn-mcr-completion l))))

(defun fn-mcr-with (l cache drawn ops)
  (declare (xargs :guard t))
  (fn-mcr-make (fn-mcr-budget l) (fn-mcr-base l) cache (fn-mcr-completion l)
               (fn-mcr-runtime l) drawn ops))

(defun fn-mcr-op (id ops)
  (declare (xargs :guard t))
  (cdr (hons-assoc-equal id ops)))

; OPS without ID's entries.
(defun fn-mcr-drop (id ops)
  (declare (xargs :guard t))
  (if (consp ops)
      (if (and (consp (car ops)) (equal (caar ops) id))
          (fn-mcr-drop id (cdr ops))
        (cons (car ops) (fn-mcr-drop id (cdr ops))))
    nil))

; ID's credit is counted once in OPS: hons-assoc-equal finds the first entry
; and the ops a transition builds keep one entry an id (fn-mcr-put).
(defun fn-mcr-put (id op ops)
  (declare (xargs :guard t))
  (cons (cons id op) (fn-mcr-drop id ops)))

(defun fn-mcr-acquire (l id u r)
  (declare (xargs :guard t))
  (let ((need (+ (nfix u) (nfix r))))
    (cond ((hons-assoc-equal id (fn-mcr-ops l)) (list :refused :operation-already-admitted))
          ((< (fn-mcr-budget l) (+ (fn-mcr-total l) need))
           (list :refused :memory-budget-exhausted))
          (t (list :ok (fn-mcr-with l (fn-mcr-cache l) (fn-mcr-drawn l)
                                    (fn-mcr-put id (cons (nfix u) (nfix r)) (fn-mcr-ops l))))))))

(defun fn-mcr-grow (l id x)
  (declare (xargs :guard t))
  (let ((op (fn-mcr-op id (fn-mcr-ops l))))
    (cond ((not (hons-assoc-equal id (fn-mcr-ops l))) (list :refused :operation-not-admitted))
          ((< (fn-mcr-op-reserved op) (nfix x)) (list :refused :past-the-reserve))
          (t (list :ok (fn-mcr-with l (fn-mcr-cache l) (fn-mcr-drawn l)
                                    (fn-mcr-put id (cons (+ (fn-mcr-op-owned op) (nfix x))
                                                         (- (fn-mcr-op-reserved op) (nfix x)))
                                                (fn-mcr-ops l))))))))

(defun fn-mcr-retain (l id x)
  (declare (xargs :guard t))
  (let ((op (fn-mcr-op id (fn-mcr-ops l))))
    (cond ((not (hons-assoc-equal id (fn-mcr-ops l))) (list :refused :operation-not-admitted))
          ((< (fn-mcr-op-owned op) (nfix x)) (list :refused :past-what-it-owns))
          (t (list :ok (fn-mcr-with l (+ (fn-mcr-cache l) (nfix x)) (fn-mcr-drawn l)
                                    (fn-mcr-drop id (fn-mcr-ops l))))))))

(defun fn-mcr-release (l id)
  (declare (xargs :guard t))
  (if (hons-assoc-equal id (fn-mcr-ops l))
      (list :ok (fn-mcr-with l (fn-mcr-cache l) (fn-mcr-drawn l) (fn-mcr-drop id (fn-mcr-ops l))))
    (list :refused :operation-not-admitted)))

(defun fn-mcr-evict (l x)
  (declare (xargs :guard t))
  (if (< (fn-mcr-cache l) (nfix x))
      (list :refused :past-the-cache)
    (list :ok (fn-mcr-with l (- (fn-mcr-cache l) (nfix x)) (fn-mcr-drawn l) (fn-mcr-ops l)))))

(defun fn-mcr-overdraw (l id x)
  (declare (xargs :guard t))
  (cond ((not (hons-assoc-equal id (fn-mcr-ops l))) (list :refused :operation-not-admitted))
        ((< (fn-mcr-completion l) (+ (fn-mcr-drawn l) (nfix x)))
         (list :refused :completion-reserve-exhausted))
        (t (list :ok (fn-mcr-with l (fn-mcr-cache l) (+ (fn-mcr-drawn l) (nfix x))
                                  (fn-mcr-ops l))))))

; -----------------------------------------------------------------------------

(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-mcr-ops-credit-natp
  (natp (fn-mcr-ops-credit ops))
  :rule-classes :type-prescription)

;; The ops algebra.
(defthm fn-mcr-ops-credit-of-put
  (equal (fn-mcr-ops-credit (fn-mcr-put id op ops))
         (+ (fn-mcr-op-owned op) (fn-mcr-op-reserved op)
            (fn-mcr-ops-credit (fn-mcr-drop id ops)))))

(defthm fn-mcr-hons-assoc-when-not-member
  (implies (and (alistp ops) (not (member-equal k (strip-cars ops))))
           (not (hons-assoc-equal k ops))))

(defthm fn-mcr-drop-when-not-member
  (implies (and (alistp ops) (not (member-equal k (strip-cars ops))))
           (equal (fn-mcr-drop k ops) ops)))

(defthm fn-mcr-ops-credit-of-drop
  (implies (and (alistp ops) (no-duplicatesp-equal (strip-cars ops))
                (hons-assoc-equal id ops))
           (equal (fn-mcr-ops-credit ops)
                  (+ (fn-mcr-op-owned (cdr (hons-assoc-equal id ops)))
                     (fn-mcr-op-reserved (cdr (hons-assoc-equal id ops)))
                     (fn-mcr-ops-credit (fn-mcr-drop id ops))))))

(defthm fn-mcr-drop-when-absent
  (implies (and (alistp ops) (not (hons-assoc-equal id ops)))
           (equal (fn-mcr-drop id ops) ops)))

(defthm fn-mcr-alistp-of-drop
  (implies (alistp ops) (alistp (fn-mcr-drop id ops))))

(defthm fn-mcr-strip-cars-of-drop-subset
  (implies (not (member-equal k (strip-cars ops)))
           (not (member-equal k (strip-cars (fn-mcr-drop id ops))))))

(defthm fn-mcr-no-duplicates-of-drop
  (implies (no-duplicatesp-equal (strip-cars ops))
           (no-duplicatesp-equal (strip-cars (fn-mcr-drop id ops)))))

(defthm fn-mcr-id-not-in-drop
  (implies (alistp ops)
           (not (member-equal id (strip-cars (fn-mcr-drop id ops))))))

(defthm fn-mcr-opsp-of-put
  (implies (fn-mcr-opsp ops) (fn-mcr-opsp (fn-mcr-put id op ops))))

(defthm fn-mcr-opsp-of-drop
  (implies (fn-mcr-opsp ops) (fn-mcr-opsp (fn-mcr-drop id ops))))

(defthm fn-mcr-accessors-of-with
  (and (equal (fn-mcr-budget (fn-mcr-with l c d o)) (fn-mcr-budget l))
       (equal (fn-mcr-base (fn-mcr-with l c d o)) (fn-mcr-base l))
       (equal (fn-mcr-cache (fn-mcr-with l c d o)) (nfix c))
       (equal (fn-mcr-completion (fn-mcr-with l c d o)) (fn-mcr-completion l))
       (equal (fn-mcr-runtime (fn-mcr-with l c d o)) (fn-mcr-runtime l))
       (equal (fn-mcr-drawn (fn-mcr-with l c d o)) (nfix d))
       (equal (fn-mcr-ops (fn-mcr-with l c d o)) o)))

(in-theory (disable fn-mcr-with fn-mcr-budget fn-mcr-base fn-mcr-cache fn-mcr-completion
                    fn-mcr-runtime fn-mcr-drawn fn-mcr-ops fn-mcr-put fn-mcr-drop))

; -----------------------------------------------------------------------------
; The contract.

; Credit before allocation: an operation is admitted exactly when its whole
; credit fits beside everything already funded.
(defthm fn-mcr-acquire-refuses-exactly-past-the-budget
  (implies (not (hons-assoc-equal id (fn-mcr-ops l)))
           (equal (equal (car (fn-mcr-acquire l id u r)) :ok)
                  (<= (+ (fn-mcr-total l) (nfix u) (nfix r)) (fn-mcr-budget l)))))

; Reserve to finish: growth within an admitted operation's reserve is never
; refused, and it moves credit without changing the funded total.
(defthm fn-mcr-grow-within-the-reserve-is-admitted
  (implies (and (fn-mcr-opsp (fn-mcr-ops l))
                (hons-assoc-equal id (fn-mcr-ops l))
                (<= (nfix x) (fn-mcr-op-reserved (fn-mcr-op id (fn-mcr-ops l)))))
           (and (equal (car (fn-mcr-grow l id x)) :ok)
                (equal (fn-mcr-total (cadr (fn-mcr-grow l id x))) (fn-mcr-total l)))))

; An overdraft comes only from the separately funded completion reserve and
; changes no funded total.
(defthm fn-mcr-overdraw-is-within-the-completion-reserve
  (implies (equal (car (fn-mcr-overdraw l id x)) :ok)
           (and (<= (fn-mcr-drawn (cadr (fn-mcr-overdraw l id x))) (fn-mcr-completion l))
                (equal (fn-mcr-total (cadr (fn-mcr-overdraw l id x))) (fn-mcr-total l)))))

; Retention moves the retained octets to the cache and returns the rest: the
; total falls by exactly the credit not retained.
(defthm fn-mcr-retain-moves-the-credit
  (implies (and (fn-mcr-opsp (fn-mcr-ops l))
                (equal (car (fn-mcr-retain l id x)) :ok))
           (equal (fn-mcr-total (cadr (fn-mcr-retain l id x)))
                  (- (fn-mcr-total l)
                     (- (+ (fn-mcr-op-owned (fn-mcr-op id (fn-mcr-ops l)))
                           (fn-mcr-op-reserved (fn-mcr-op id (fn-mcr-ops l))))
                        (nfix x))))))

; Cache credit comes back only by an eviction, by exactly the octets evicted.
(defthm fn-mcr-evict-returns-what-was-evicted
  (implies (equal (car (fn-mcr-evict l x)) :ok)
           (equal (fn-mcr-cache (cadr (fn-mcr-evict l x)))
                  (- (fn-mcr-cache l) (nfix x)))))

; KEYSTONE.  From a funded ledger every transition's result is funded.
(defthm fn-mcr-transitions-keep-funded
  (implies (fn-mcr-fundedp l)
           (and (implies (equal (car (fn-mcr-acquire l id u r)) :ok)
                         (fn-mcr-fundedp (cadr (fn-mcr-acquire l id u r))))
                (implies (equal (car (fn-mcr-grow l id x)) :ok)
                         (fn-mcr-fundedp (cadr (fn-mcr-grow l id x))))
                (implies (equal (car (fn-mcr-retain l id x)) :ok)
                         (fn-mcr-fundedp (cadr (fn-mcr-retain l id x))))
                (implies (equal (car (fn-mcr-release l id)) :ok)
                         (fn-mcr-fundedp (cadr (fn-mcr-release l id))))
                (implies (equal (car (fn-mcr-evict l x)) :ok)
                         (fn-mcr-fundedp (cadr (fn-mcr-evict l x))))
                (implies (equal (car (fn-mcr-overdraw l id x)) :ok)
                         (fn-mcr-fundedp (cadr (fn-mcr-overdraw l id x)))))))
