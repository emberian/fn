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
; contract.  Its host subject is books/owner-credits.lisp (lane credits):
; the served read, the committer's take and seal, the batch's COMPLETE and
; the close move the article credits of one ledger a run by fn-mcr-resize
; and fn-mcr-move (below), whose keystone is
; fn-mcr-resize-and-move-keep-funded.

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

; -----------------------------------------------------------------------------
; RESIZE and MOVE (lane credits, B5, 2026-09-28): the two transitions the
; served path uses (books/owner-credits.lisp).  An operation's credit is
; FN-MCR-CREDIT-OF (owned plus reserved; zero when it holds none).
;
;   fn-mcr-resize id N    the operation now needs N: shrinking (N at most
;                         what it holds) is never refused -- reserve to
;                         finish -- and growing is admitted exactly when the
;                         growth fits beside everything funded, refused
;                         :memory-budget-exhausted by name otherwise, the
;                         ledger unchanged.  N = 0 releases it.
;   fn-mcr-move from to X the buffer changed hands: X of FROM's credit
;                         becomes TO's, never refused within what FROM
;                         holds; the funded total is unchanged (the same
;                         credit follows the buffer).
(defun fn-mcr-credit-of (id ops)
  (declare (xargs :guard t))
  (let ((pair (hons-assoc-equal id ops)))
    (if pair
        (+ (fn-mcr-op-owned (cdr pair)) (fn-mcr-op-reserved (cdr pair)))
      0)))

(defun fn-mcr-set (id n ops)
  (declare (xargs :guard t))
  (let ((n (nfix n)))
    (if (zp n) (fn-mcr-drop id ops) (fn-mcr-put id (cons 0 n) ops))))

(defun fn-mcr-resize (l id n)
  (declare (xargs :guard t))
  (let* ((ops (fn-mcr-ops l))
         (old (fn-mcr-credit-of id ops))
         (n (nfix n)))
    (if (and (< old n)
             (< (fn-mcr-budget l) (+ (- (fn-mcr-total l) old) n)))
        (list :refused :memory-budget-exhausted)
      (list :ok (fn-mcr-with l (fn-mcr-cache l) (fn-mcr-drawn l) (fn-mcr-set id n ops))))))

(defun fn-mcr-move (l from to x)
  (declare (xargs :guard t))
  (let* ((ops (fn-mcr-ops l))
         (have (fn-mcr-credit-of from ops))
         (x (nfix x)))
    (cond ((equal from to) (list :refused :same-operation))
          ((< have x) (list :refused :past-what-it-holds))
          (t (let ((ops1 (fn-mcr-set from (- have x) ops)))
               (list :ok (fn-mcr-with l (fn-mcr-cache l) (fn-mcr-drawn l)
                                      (fn-mcr-set to (+ (fn-mcr-credit-of to ops1) x)
                                                  ops1))))))))

(defthm fn-mcr-credit-of-natp
  (natp (fn-mcr-credit-of id ops))
  :rule-classes :type-prescription)

(defthm fn-mcr-ops-credit-splits-at
  (implies (fn-mcr-opsp ops)
           (equal (fn-mcr-ops-credit ops)
                  (+ (fn-mcr-credit-of id ops)
                     (fn-mcr-ops-credit (fn-mcr-drop id ops)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-mcr-ops-credit-of-drop))
           :in-theory (enable fn-mcr-drop-when-absent))))

(defthm fn-mcr-ops-credit-of-set
  (equal (fn-mcr-ops-credit (fn-mcr-set id n ops))
         (+ (nfix n) (fn-mcr-ops-credit (fn-mcr-drop id ops))))
  :hints (("Goal" :in-theory (enable fn-mcr-drop))))

(defthm fn-mcr-opsp-of-set
  (implies (fn-mcr-opsp ops) (fn-mcr-opsp (fn-mcr-set id n ops)))
  :hints (("Goal" :in-theory (disable fn-mcr-opsp))))

(defthm fn-mcr-hons-assoc-of-drop-same
  (not (hons-assoc-equal id (fn-mcr-drop id ops)))
  :hints (("Goal" :in-theory (enable fn-mcr-drop))))

(defthm fn-mcr-credit-of-set-same
  (equal (fn-mcr-credit-of id (fn-mcr-set id n ops)) (nfix n))
  :hints (("Goal" :in-theory (enable fn-mcr-put fn-mcr-drop))))

(defthm fn-mcr-hons-assoc-of-drop-other
  (implies (not (equal a b))
           (equal (hons-assoc-equal a (fn-mcr-drop b ops)) (hons-assoc-equal a ops)))
  :hints (("Goal" :in-theory (enable fn-mcr-drop))))

(defthm fn-mcr-credit-of-set-other
  (implies (not (equal a b))
           (equal (fn-mcr-credit-of a (fn-mcr-set b n ops)) (fn-mcr-credit-of a ops)))
  :hints (("Goal" :in-theory (enable fn-mcr-put))))

(in-theory (disable fn-mcr-credit-of fn-mcr-set))

(defthm fn-mcr-total-of-resize
  (implies (and (fn-mcr-opsp (fn-mcr-ops l))
                (equal (car (fn-mcr-resize l id n)) :ok))
           (equal (fn-mcr-total (cadr (fn-mcr-resize l id n)))
                  (+ (- (fn-mcr-total l) (fn-mcr-credit-of id (fn-mcr-ops l))) (nfix n))))
  :hints (("Goal" :use ((:instance fn-mcr-ops-credit-splits-at (ops (fn-mcr-ops l)))))))

(defthm fn-mcr-resize-refuses-exactly-past-the-budget
  (equal (equal (car (fn-mcr-resize l id n)) :ok)
         (or (<= (nfix n) (fn-mcr-credit-of id (fn-mcr-ops l)))
             (<= (+ (- (fn-mcr-total l) (fn-mcr-credit-of id (fn-mcr-ops l))) (nfix n))
                 (fn-mcr-budget l))))
  :hints (("Goal" :in-theory (disable fn-mcr-total))))

(defthm fn-mcr-resize-sets-the-credit
  (implies (equal (car (fn-mcr-resize l id n)) :ok)
           (and (equal (fn-mcr-credit-of id (fn-mcr-ops (cadr (fn-mcr-resize l id n)))) (nfix n))
                (implies (not (equal a id))
                         (equal (fn-mcr-credit-of a (fn-mcr-ops (cadr (fn-mcr-resize l id n))))
                                (fn-mcr-credit-of a (fn-mcr-ops l))))))
  :hints (("Goal" :in-theory (disable fn-mcr-total))))

(defthm fn-mcr-resize-keeps-the-rest
  (implies (equal (car (fn-mcr-resize l id n)) :ok)
           (and (equal (fn-mcr-budget (cadr (fn-mcr-resize l id n))) (fn-mcr-budget l))
                (equal (fn-mcr-cache (cadr (fn-mcr-resize l id n))) (fn-mcr-cache l))
                (equal (fn-mcr-drawn (cadr (fn-mcr-resize l id n))) (fn-mcr-drawn l))))
  :hints (("Goal" :in-theory (disable fn-mcr-total))))

(defthm fn-mcr-total-of-move
  (implies (and (fn-mcr-opsp (fn-mcr-ops l))
                (equal (car (fn-mcr-move l from to x)) :ok))
           (equal (fn-mcr-total (cadr (fn-mcr-move l from to x))) (fn-mcr-total l)))
  :hints (("Goal" :use ((:instance fn-mcr-ops-credit-splits-at (ops (fn-mcr-ops l)) (id from))
                        (:instance fn-mcr-ops-credit-splits-at
                                   (ops (fn-mcr-set from (- (fn-mcr-credit-of from (fn-mcr-ops l)) (nfix x))
                                                    (fn-mcr-ops l)))
                                   (id to))))))

(defthm fn-mcr-move-moves-the-credit
  (implies (equal (car (fn-mcr-move l from to x)) :ok)
           (and (equal (fn-mcr-credit-of from (fn-mcr-ops (cadr (fn-mcr-move l from to x))))
                       (- (fn-mcr-credit-of from (fn-mcr-ops l)) (nfix x)))
                (equal (fn-mcr-credit-of to (fn-mcr-ops (cadr (fn-mcr-move l from to x))))
                       (+ (fn-mcr-credit-of to (fn-mcr-ops l)) (nfix x)))
                (implies (and (not (equal a from)) (not (equal a to)))
                         (equal (fn-mcr-credit-of a (fn-mcr-ops (cadr (fn-mcr-move l from to x))))
                                (fn-mcr-credit-of a (fn-mcr-ops l)))))))

(defthm fn-mcr-move-within-what-it-holds-is-admitted
  (implies (and (not (equal from to))
                (<= (nfix x) (fn-mcr-credit-of from (fn-mcr-ops l))))
           (equal (car (fn-mcr-move l from to x)) :ok)))

; L1 keeps L's budget, completion reserve and what is drawn of it.
(defun fn-mcr-same-funding (l l1)
  (declare (xargs :guard t))
  (and (equal (fn-mcr-budget l1) (fn-mcr-budget l))
       (equal (fn-mcr-completion l1) (fn-mcr-completion l))
       (equal (fn-mcr-drawn l1) (fn-mcr-drawn l))))

;; What every admitted resize and move leaves as it was.
(defthm fn-mcr-resize-and-move-keep-the-rest
  (and (implies (equal (car (fn-mcr-resize l id n)) :ok)
                (and (fn-mcr-same-funding l (cadr (fn-mcr-resize l id n)))
                     (implies (fn-mcr-opsp (fn-mcr-ops l))
                              (fn-mcr-opsp (fn-mcr-ops (cadr (fn-mcr-resize l id n)))))))
       (implies (equal (car (fn-mcr-move l from to x)) :ok)
                (and (fn-mcr-same-funding l (cadr (fn-mcr-move l from to x)))
                     (implies (fn-mcr-opsp (fn-mcr-ops l))
                              (fn-mcr-opsp (fn-mcr-ops (cadr (fn-mcr-move l from to x)))))))))

;; KEYSTONE (lane credits).  From a funded ledger every admitted resize
;; and move leaves it funded.
(defthm fn-mcr-resize-and-move-keep-funded
  (implies (fn-mcr-fundedp l)
           (and (implies (equal (car (fn-mcr-resize l id n)) :ok)
                         (fn-mcr-fundedp (cadr (fn-mcr-resize l id n))))
                (implies (equal (car (fn-mcr-move l from to x)) :ok)
                         (fn-mcr-fundedp (cadr (fn-mcr-move l from to x))))))
  :hints (("Goal" :in-theory (e/d (fn-mcr-fundedp fn-mcr-same-funding)
                                  (fn-mcr-total fn-mcr-resize fn-mcr-move fn-mcr-opsp
                                   fn-mcr-resize-and-move-keep-the-rest))
           :use (fn-mcr-resize-and-move-keep-the-rest))))
