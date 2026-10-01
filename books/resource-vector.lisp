; fn: the resource vector and the bank -- ONE accounting (lane
; resource-ledger, 2026-10-01; planning/design-store-representation-
; 2026-10-01.md section 2, "the accounting is a resource vector, prepaid,
; by construction", stage 6 of its order; GPT-6's recovery-reserve row,
; planning/review-2026-09-30-gpt6-log2.md section 2: U + C + R <= B(P) over
; a resource vector, dW+ charged before acceptance, "refusal preserves
; funded rescue capability").  The precedent is seL4 untyped memory and
; KeyKOS space banks (build/coordinator/scholar-literature-2026-10-01.md
; section E.3): the system never allocates on its own; every request draws
; on its user's bank; the owner's own needs are a bank created first and
; never drawn by a user; teardown destroys the sub-bank.
;
; THE VECTOR.  A fixed-arity list of naturals, one coordinate a resource
; class (*fn-rv-coordinates*): resident octets (the collector's copy
; included), disk octets, descriptor credits, worker slots, then the finite
; identity spaces (read identities, Store transaction identities,
; configuration generations, connection identities) and work units.  The
; first five are Codex's fn-prs vector (books/page-read-resources.lisp),
; which is therefore this vector's prefix (books/resource-vector-relations).
; Coordinate-wise + (fn-rv-plus), the order <= (fn-rv-below) and the
; truncated difference (fn-rv-monus) make the vectors a commutative monoid
; with an order; nothing here is specific to a class.  A coordinate is
; REUSABLE (a settle returns it) or SPENT (an identity or work: drawn once,
; never returned, so a bank's drawn total in a spent coordinate only grows,
; and a destroyed sub-bank returns only what it had not spent).  A class is
; added by a row of the table, never by the host (D27: the host observes,
; ACL2 decides).
;
; THE BANK.  (BUDGET DRAWN SLOTS): the budget vector; the drawn vector,
; CARRIED in state and never recomputed on a served path; and SLOTS, a true
; list of rows (PHASE . DEMAND) indexed by position -- the slot number is
; the row's position, so the executable twin is a direct-index typed array
; (books/resource-vector-exec.lisp).  Phase 0 idle, 1 drawn, 2 a sub-bank
; (the row's demand is the sub-bank's whole budget: sub-banks PARTITION
; their parent, and a sub-bank's unused slack is not its siblings').  The
; transitions, each the list (WORD BANK'), a refused one returning the
; bank itself (a list, as books/memory-credits.lisp answers, so that every
; witness evaluates; the typed twin answers mv):
;
;   fn-rv-draw    slot demand  charge DEMAND on an idle slot: refused
;                              :resources-unavailable exactly when drawn +
;                              demand is not within the budget (the check
;                              precedes every effect), :slot-busy on a slot
;                              in use
;   fn-rv-open    slot budget  the same charge, the slot becoming a sub-bank
;   fn-rv-settle  slot         the draw's work is physically complete: its
;                              reusable coordinates return, its spent ones
;                              stay drawn; a second settle is :stale
;   fn-rv-refund  slot x       the draw needed less than it charged: x of
;                              its reusable part returns now, never refused
;                              within what it holds (reserve to finish)
;   fn-rv-grow    slot x       a sub-bank's budget grows by x (the owner's
;                              dW+ before acceptance): refused past the
;                              parent's budget, the sub-bank unchanged
;   fn-rv-destroy slot spent   the sub-bank is torn down: its budget returns
;                              less SPENT, what it had drawn in the spent
;                              coordinates (the caller passes
;                              (fn-rv-spent (fn-rv-drawn sub)))
;
; FN-RV-OKP is the carried invariant: budget, drawn and every row are
; vectors; drawn <= budget (FUNDED); the reusable part of drawn is exactly
; the reusable part of the outstanding rows' demands (nothing leaks, nothing
; is counted twice); and the spent part of the outstanding rows is within
; the spent part of drawn (what was spent and settled stays drawn).
;
; KEYSTONES, proved once over fn-rv-step (every transition) and so owed by
; no instance:
;   fn-rv-step-keeps-okp          from an okp bank every step's result is okp
;   fn-rv-step-refused-keeps-the-bank  a refused step returns the bank
;                                 itself; so fn-rv-refusal-keeps-slack (the
;                                 slack, budget - drawn, is unchanged) and
;                                 fn-rv-refused-run-keeps-the-bank (a run of
;                                 refused steps leaves it)
;   fn-rv-draw-admits-exactly-within-the-budget  the admission condition
;   fn-rv-settle-once             a slot settles at most once
;   fn-rv-destroy-returns-exactly-the-unsettled-draws
;   fn-rv-step-keeps-the-other-slots  a step on one slot leaves every other
;                                 row as it was; so the reserve, opened at
;                                 fn-rv-install's slot 1, is never drawn by
;                                 a step on a user's slot
;                                 (fn-rv-user-steps-keep-the-reserve)
;   fn-rv-install-reserves-the-owner-first  the installed root is okp with
;                                 the baseline and the reserve drawn and
;                                 nothing else; fn-rv-run-keeps-okp closes
;                                 okp under every run from it
;
; Not here: which operation may draw which coordinate, the tariff of an
; operation, and where the charge sits in a served entry.  That is
; `definterface :operation' (specs/resource-vector.md), the next lane; no
; served path calls this book (MODE 2026-10-01 section 3: no gate before
; its producer).

(in-package "ACL2")

; -----------------------------------------------------------------------------
; The coordinates.

(defconst *fn-rv-coordinates*
  '((:resident    :reusable)   ; 0 resident octets, the collector's copy included
    (:disk        :reusable)   ; 1 durable and workspace octets
    (:descriptors :reusable)   ; 2 descriptor credits
    (:workers     :reusable)   ; 3 executing worker slots
    (:read-ids    :spent)      ; 4 process-local read identities (fn-prs coordinate 4)
    (:txids       :spent)      ; 5 Store transaction identities
    (:config-gens :spent)      ; 6 configuration generations
    (:conn-ids    :spent)      ; 7 connection identities
    (:work        :spent)))    ; 8 work units of the quantum

(defconst *fn-rv-k* (len *fn-rv-coordinates*))

; The reusable mask: 1 at a reusable coordinate.  The spent coordinates are
; its complement (fn-rv-drop).
(defun fn-rv-mask-of (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (cons (if (and (consp (car rows)) (consp (cdar rows))
                     (eq (cadar rows) :reusable))
                1 0)
            (fn-rv-mask-of (cdr rows)))
    nil))

(defconst *fn-rv-reusable-mask* (fn-rv-mask-of *fn-rv-coordinates*))

(defun fn-rv-index-in (name rows i)
  (declare (xargs :guard (natp i)))
  (cond ((not (consp rows)) nil)
        ((and (consp (car rows)) (equal (caar rows) name)) i)
        (t (fn-rv-index-in name (cdr rows) (+ 1 i)))))

; The coordinate of a class by name, or NIL.
(defun fn-rv-index (name)
  (declare (xargs :guard t))
  (fn-rv-index-in name *fn-rv-coordinates* 0))

; -----------------------------------------------------------------------------
; The vector algebra.

(defun fn-rv-nats-p (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (fn-rv-nats-p (cdr xs)))
    (null xs)))

(defun fn-rv-vectorp (x)
  (declare (xargs :guard t))
  (and (fn-rv-nats-p x) (equal (len x) *fn-rv-k*)))

(defun fn-rv-zeros (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons 0 (fn-rv-zeros (- n 1)))))

(defconst *fn-rv-zero* (fn-rv-zeros *fn-rv-k*))

(defun fn-rv-plus (a b)
  (declare (xargs :guard (and (true-listp a) (true-listp b))
                  :measure (+ (acl2-count a) (acl2-count b))))
  (if (or (consp a) (consp b))
      (cons (+ (nfix (car a)) (nfix (car b)))
            (fn-rv-plus (cdr a) (cdr b)))
    nil))

(defun fn-rv-monus (a b)
  (declare (xargs :guard (and (true-listp a) (true-listp b))
                  :measure (+ (acl2-count a) (acl2-count b))))
  (if (or (consp a) (consp b))
      (cons (nfix (- (nfix (car a)) (nfix (car b))))
            (fn-rv-monus (cdr a) (cdr b)))
    nil))

(defun fn-rv-below (a b)
  (declare (xargs :guard (and (true-listp a) (true-listp b))
                  :measure (+ (acl2-count a) (acl2-count b))))
  (if (or (consp a) (consp b))
      (and (<= (nfix (car a)) (nfix (car b)))
           (fn-rv-below (cdr a) (cdr b)))
    t))

; KEEP the coordinates the mask marks (the rest 0); DROP them (the marked
; ones 0).
(defun fn-rv-keep (v mask)
  (declare (xargs :guard (and (true-listp v) (true-listp mask))))
  (if (consp v)
      (cons (if (eql (car mask) 1) (nfix (car v)) 0)
            (fn-rv-keep (cdr v) (cdr mask)))
    nil))

(defun fn-rv-drop (v mask)
  (declare (xargs :guard (and (true-listp v) (true-listp mask))))
  (if (consp v)
      (cons (if (eql (car mask) 1) 0 (nfix (car v)))
            (fn-rv-drop (cdr v) (cdr mask)))
    nil))

(defun fn-rv-reusable (v)
  (declare (xargs :guard (true-listp v)))
  (fn-rv-keep v *fn-rv-reusable-mask*))

(defun fn-rv-spent (v)
  (declare (xargs :guard (true-listp v)))
  (fn-rv-drop v *fn-rv-reusable-mask*))

(defun fn-rv-at (i v)
  (declare (xargs :guard (and (natp i) (true-listp v))))
  (nfix (nth i v)))

; The vector with N at coordinate I and 0 elsewhere.
(defun fn-rv-unit (i n)
  (declare (xargs :guard (and (natp i) (< i *fn-rv-k*) (natp n))))
  (update-nth i n *fn-rv-zero*))

; -----------------------------------------------------------------------------
; The algebra's facts.

(local (include-book "arithmetic-5/top" :dir :system))

; Induction over three lists at once, and over a count beside a list.
(local
 (defun fn-rv-ind3 (a b c)
   (declare (xargs :measure (+ (acl2-count a) (acl2-count b) (acl2-count c))))
   (if (or (consp a) (consp b) (consp c))
       (fn-rv-ind3 (cdr a) (cdr b) (cdr c))
     nil)))

(local
 (defun fn-rv-ind-n (n v)
   (if (zp n) v (fn-rv-ind-n (- n 1) (cdr v)))))

(defthm fn-rv-nats-p-of-plus
  (fn-rv-nats-p (fn-rv-plus a b)))

(defthm fn-rv-nats-p-of-monus
  (fn-rv-nats-p (fn-rv-monus a b)))

(defthm fn-rv-nats-p-of-keep
  (fn-rv-nats-p (fn-rv-keep v m)))

(defthm fn-rv-nats-p-of-drop
  (fn-rv-nats-p (fn-rv-drop v m)))

(defthm fn-rv-nats-p-of-zeros
  (fn-rv-nats-p (fn-rv-zeros n)))

(defthm fn-rv-len-of-plus
  (equal (len (fn-rv-plus a b)) (max (len a) (len b))))

(defthm fn-rv-len-of-monus
  (equal (len (fn-rv-monus a b)) (max (len a) (len b))))

(defthm fn-rv-len-of-keep
  (equal (len (fn-rv-keep v m)) (len v)))

(defthm fn-rv-len-of-drop
  (equal (len (fn-rv-drop v m)) (len v)))

(defthm fn-rv-len-of-zeros
  (equal (len (fn-rv-zeros n)) (nfix n)))

(defthm fn-rv-nats-p-forward-to-true-listp
  (implies (fn-rv-nats-p v) (true-listp v))
  :rule-classes :forward-chaining)

(defthm fn-rv-vectorp-of-plus
  (implies (and (fn-rv-vectorp a) (fn-rv-vectorp b))
           (fn-rv-vectorp (fn-rv-plus a b))))

(defthm fn-rv-vectorp-of-monus
  (implies (and (fn-rv-vectorp a) (fn-rv-vectorp b))
           (fn-rv-vectorp (fn-rv-monus a b))))

(defthm fn-rv-vectorp-of-keep
  (implies (fn-rv-vectorp v) (fn-rv-vectorp (fn-rv-keep v m))))

(defthm fn-rv-vectorp-of-drop
  (implies (fn-rv-vectorp v) (fn-rv-vectorp (fn-rv-drop v m))))

(defthm fn-rv-vectorp-of-zero
  (fn-rv-vectorp *fn-rv-zero*))

(defthm fn-rv-vectorp-of-reusable
  (implies (fn-rv-vectorp v) (fn-rv-vectorp (fn-rv-reusable v))))

(defthm fn-rv-vectorp-of-spent
  (implies (fn-rv-vectorp v) (fn-rv-vectorp (fn-rv-spent v))))

(defthm fn-rv-vectorp-forward
  (implies (fn-rv-vectorp v)
           (and (fn-rv-nats-p v) (true-listp v) (equal (len v) *fn-rv-k*)))
  :rule-classes :forward-chaining)

(defthm fn-rv-vectorp-is-a-true-list
  (implies (fn-rv-vectorp v) (true-listp v)))

(defthm fn-rv-plus-commutative
  (equal (fn-rv-plus a b) (fn-rv-plus b a)))

(defthm fn-rv-plus-associative
  (equal (fn-rv-plus (fn-rv-plus a b) c) (fn-rv-plus a (fn-rv-plus b c)))
  :hints (("Goal" :induct (fn-rv-ind3 a b c))))

(defthm fn-rv-plus-commutative-2
  (equal (fn-rv-plus a (fn-rv-plus b c)) (fn-rv-plus b (fn-rv-plus a c)))
  :hints (("Goal" :use ((:instance fn-rv-plus-associative)
                        (:instance fn-rv-plus-associative (a b) (b a)))
           :in-theory (disable fn-rv-plus-associative))))

(defthm fn-rv-plus-nil-left
  (implies (fn-rv-nats-p v)
           (equal (fn-rv-plus nil v) v)))

(defthm fn-rv-plus-zero-left
  (implies (and (fn-rv-nats-p v) (<= (nfix n) (len v)))
           (equal (fn-rv-plus (fn-rv-zeros n) v) v))
  :hints (("Goal" :induct (fn-rv-ind-n n v))))

(defthm fn-rv-plus-zero-right
  (implies (and (fn-rv-nats-p v) (<= (nfix n) (len v)))
           (equal (fn-rv-plus v (fn-rv-zeros n)) v))
  :hints (("Goal" :use fn-rv-plus-zero-left
           :in-theory (disable fn-rv-plus-zero-left))))

(defthm fn-rv-monus-zero-right
  (implies (fn-rv-nats-p v)
           (equal (fn-rv-monus v (fn-rv-zeros (len v))) v)))

(defthm fn-rv-keep-of-plus
  (equal (fn-rv-keep (fn-rv-plus a b) m)
         (fn-rv-plus (fn-rv-keep a m) (fn-rv-keep b m))))

(defthm fn-rv-drop-of-plus
  (equal (fn-rv-drop (fn-rv-plus a b) m)
         (fn-rv-plus (fn-rv-drop a m) (fn-rv-drop b m))))

(defthm fn-rv-keep-of-monus
  (equal (fn-rv-keep (fn-rv-monus a b) m)
         (fn-rv-monus (fn-rv-keep a m) (fn-rv-keep b m))))

(defthm fn-rv-drop-of-monus
  (equal (fn-rv-drop (fn-rv-monus a b) m)
         (fn-rv-monus (fn-rv-drop a m) (fn-rv-drop b m))))

(defthm fn-rv-keep-of-keep
  (equal (fn-rv-keep (fn-rv-keep v m) m) (fn-rv-keep v m)))

(defthm fn-rv-drop-of-drop
  (equal (fn-rv-drop (fn-rv-drop v m) m) (fn-rv-drop v m)))

(defthm fn-rv-drop-of-keep
  (equal (fn-rv-drop (fn-rv-keep v m) m) (fn-rv-zeros (len v))))

(defthm fn-rv-keep-of-drop
  (equal (fn-rv-keep (fn-rv-drop v m) m) (fn-rv-zeros (len v))))

(defthm fn-rv-keep-of-zeros
  (equal (fn-rv-keep (fn-rv-zeros n) m) (fn-rv-zeros n))
  :hints (("Goal" :induct (fn-rv-ind-n n m))))

(defthm fn-rv-drop-of-zeros
  (equal (fn-rv-drop (fn-rv-zeros n) m) (fn-rv-zeros n))
  :hints (("Goal" :induct (fn-rv-ind-n n m))))

(defthm fn-rv-below-reflexive
  (fn-rv-below v v)
  :hints (("Goal" :induct (len v))))

(defthm fn-rv-below-transitive
  (implies (and (fn-rv-below a b) (fn-rv-below b c))
           (fn-rv-below a c)))

(defthm fn-rv-below-zeros-is-zeros
  (implies (and (fn-rv-nats-p v) (<= (len v) (nfix n))
                (fn-rv-below v (fn-rv-zeros n)))
           (equal v (fn-rv-zeros (len v))))
  :hints (("Goal" :induct (fn-rv-ind-n n v)))
  :rule-classes nil)

(defthm fn-rv-below-plus-monotone
  (implies (fn-rv-below a b)
           (fn-rv-below (fn-rv-plus a c) (fn-rv-plus b c)))
  :hints (("Goal" :induct (fn-rv-ind3 a b c))))

(defthm fn-rv-below-monus-monotone
  (implies (fn-rv-below a b)
           (fn-rv-below (fn-rv-monus a c) (fn-rv-monus b c)))
  :hints (("Goal" :induct (fn-rv-ind3 a b c))))

(defthm fn-rv-below-keep-monotone
  (implies (fn-rv-below a b)
           (fn-rv-below (fn-rv-keep a m) (fn-rv-keep b m))))

(defthm fn-rv-below-drop-monotone
  (implies (fn-rv-below a b)
           (fn-rv-below (fn-rv-drop a m) (fn-rv-drop b m))))

(defthm fn-rv-below-of-plus-left
  (implies (fn-rv-below (fn-rv-plus a b) c)
           (fn-rv-below a c)))

(defthm fn-rv-below-of-plus-right
  (implies (fn-rv-below (fn-rv-plus a b) c)
           (fn-rv-below b c))
  :hints (("Goal" :use ((:instance fn-rv-below-of-plus-left (a b) (b a)))
           :in-theory (disable fn-rv-below-of-plus-left))))

(defthm fn-rv-below-plus-of-monus
  (implies (fn-rv-below (fn-rv-plus a b) c)
           (fn-rv-below a (fn-rv-monus c b))))

(defthm fn-rv-below-monus-self
  (fn-rv-below (fn-rv-monus a b) a))

(defthm fn-rv-below-self-plus
  (fn-rv-below a (fn-rv-plus a b)))

(defthm fn-rv-below-keep-self
  (fn-rv-below (fn-rv-keep v m) v))

(defthm fn-rv-below-drop-self
  (fn-rv-below (fn-rv-drop v m) v))

(defthm fn-rv-monus-of-plus-same
  (implies (and (fn-rv-nats-p a) (equal (len a) (len b)))
           (equal (fn-rv-monus (fn-rv-plus a b) b) a)))

(defthm fn-rv-plus-of-monus-below
  (implies (and (fn-rv-nats-p a) (equal (len a) (len b)) (fn-rv-below b a))
           (equal (fn-rv-plus (fn-rv-monus a b) b) a)))

(defthm fn-rv-plus-cancel-right
  (implies (and (fn-rv-nats-p a) (fn-rv-nats-p b) (equal (len a) (len b)))
           (equal (equal (fn-rv-plus a c) (fn-rv-plus b c))
                  (equal a b))))

(defthm fn-rv-below-by-keep-and-drop
  (implies (and (fn-rv-below (fn-rv-keep a m) (fn-rv-keep b m))
                (fn-rv-below (fn-rv-drop a m) (fn-rv-drop b m)))
           (fn-rv-below a b)))

; B - ((D - d) + s) = (B - D) + (d - s) when d <= D <= B and s <= d.
(defthm fn-rv-destroy-arithmetic
  (implies (and (fn-rv-nats-p d) (fn-rv-nats-p big) (fn-rv-nats-p s)
                (equal (len d) (len big)) (equal (len s) (len d))
                (equal (len b) (len d))
                (fn-rv-below d big) (fn-rv-below s d) (fn-rv-below big b))
           (equal (fn-rv-monus b (fn-rv-plus (fn-rv-monus big d) s))
                  (fn-rv-plus (fn-rv-monus b big) (fn-rv-monus d s)))))

(defthm fn-rv-nth-of-nats
  (implies (fn-rv-nats-p v)
           (equal (nfix (nth i v)) (if (< (nfix i) (len v)) (nth i v) 0))))


; The same facts with the common term on the left, as the AC normal form
; of fn-rv-plus may put it.
(defthm fn-rv-monus-of-plus-same-left
  (implies (and (fn-rv-nats-p a) (equal (len a) (len b)))
           (equal (fn-rv-monus (fn-rv-plus b a) b) a))
  :hints (("Goal" :use fn-rv-monus-of-plus-same
           :in-theory (disable fn-rv-monus-of-plus-same))))

(defthm fn-rv-below-plus-monotone-left
  (implies (fn-rv-below a b)
           (fn-rv-below (fn-rv-plus c a) (fn-rv-plus c b)))
  :hints (("Goal" :use fn-rv-below-plus-monotone
           :in-theory (disable fn-rv-below-plus-monotone))))

(defthm fn-rv-plus-cancel-left
  (implies (and (fn-rv-nats-p a) (fn-rv-nats-p b) (equal (len a) (len b)))
           (equal (equal (fn-rv-plus c a) (fn-rv-plus c b))
                  (equal a b)))
  :hints (("Goal" :use fn-rv-plus-cancel-right
           :in-theory (disable fn-rv-plus-cancel-right))))

; (o + (d - x)) - d = o - x when x <= d; (o + (d + x)) - d = o + x.
(defthm fn-rv-refund-arithmetic
  (implies (and (fn-rv-nats-p o) (fn-rv-nats-p d) (fn-rv-nats-p x)
                (equal (len d) (len o)) (equal (len x) (len o))
                (fn-rv-below x d))
           (equal (fn-rv-monus (fn-rv-plus o (fn-rv-monus d x)) d)
                  (fn-rv-monus o x)))
  :hints (("Goal" :induct (fn-rv-ind3 o d x)
           :in-theory (enable fn-rv-plus fn-rv-monus fn-rv-below fn-rv-nats-p))))

(defthm fn-rv-grow-arithmetic
  (implies (and (fn-rv-nats-p o) (fn-rv-nats-p d) (fn-rv-nats-p x)
                (equal (len d) (len o)) (equal (len x) (len o)))
           (equal (fn-rv-monus (fn-rv-plus o (fn-rv-plus d x)) d)
                  (fn-rv-plus o x)))
  :hints (("Goal" :induct (fn-rv-ind3 o d x)
           :in-theory (enable fn-rv-plus fn-rv-monus fn-rv-nats-p))))

; What a sub-bank returns (its budget less what it spent) covers the
; budget's reusable part.
(defthm fn-rv-keep-below-monus-drop
  (fn-rv-below (fn-rv-keep d m) (fn-rv-monus d (fn-rv-drop x m)))
  :hints (("Goal" :induct (fn-rv-ind3 d x m))))

(local
 (defun fn-rv-ind-nn (i n)
   (if (zp i) n (fn-rv-ind-nn (- i 1) (- n 1)))))

; The zero VECTOR (the literal the rewriter sees) is the identity on vectors.
(defthm fn-rv-plus-zero-vector-left
  (implies (fn-rv-vectorp v) (equal (fn-rv-plus *fn-rv-zero* v) v))
  :hints (("Goal" :use (:instance fn-rv-plus-zero-left (n *fn-rv-k*))
           :in-theory (e/d (fn-rv-vectorp) (fn-rv-plus-zero-left)))))

(defthm fn-rv-plus-zero-vector-right
  (implies (fn-rv-vectorp v) (equal (fn-rv-plus v *fn-rv-zero*) v))
  :hints (("Goal" :use (:instance fn-rv-plus-zero-right (n *fn-rv-k*))
           :in-theory (e/d (fn-rv-vectorp) (fn-rv-plus-zero-right)))))

(defthm fn-rv-monus-zero-vector-right
  (implies (fn-rv-vectorp v) (equal (fn-rv-monus v *fn-rv-zero*) v))
  :hints (("Goal" :use fn-rv-monus-zero-right
           :in-theory (e/d (fn-rv-vectorp) (fn-rv-monus-zero-right)))))

(defthm fn-rv-below-self-plus-right
  (fn-rv-below b (fn-rv-plus a b))
  :hints (("Goal" :use (:instance fn-rv-below-self-plus (a b) (b a))
           :in-theory (disable fn-rv-below-self-plus))))

(in-theory (disable fn-rv-plus fn-rv-monus fn-rv-below fn-rv-keep fn-rv-drop
                    fn-rv-zeros fn-rv-nats-p fn-rv-vectorp))

; -----------------------------------------------------------------------------
; The rows: (PHASE GEN . DEMAND).  GEN is the slot's generation, raised by
; every charge of the slot and kept when it idles; a charge answers it as
; the draw's completion token, and every later step on the charged slot
; names it, so a completion replayed after the slot was settled and drawn
; again is :stale (Codex review r06 F2: the slot alone let an old
; completion settle a new draw).

(defun fn-rv-rowp (row)
  (declare (xargs :guard t))
  (and (consp row) (natp (car row)) (<= (car row) 2)
       (consp (cdr row)) (natp (cadr row))
       (fn-rv-vectorp (cddr row))))

(defun fn-rv-rowsp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-rv-rowp (car rows)) (fn-rv-rowsp (cdr rows)))
    (null rows)))

(defun fn-rv-idle-row (gen)
  (declare (xargs :guard (natp gen)))
  (list* 0 gen *fn-rv-zero*))

(defconst *fn-rv-idle* (fn-rv-idle-row 0))

(defun fn-rv-idle-rows (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons *fn-rv-idle* (fn-rv-idle-rows (- n 1)))))

; What a row holds against the bank: its demand unless idle.
(defun fn-rv-row-demand (row)
  (declare (xargs :guard (fn-rv-rowp row)))
  (if (eql (car row) 0) *fn-rv-zero* (cddr row)))

(defun fn-rv-outstanding (rows)
  (declare (xargs :guard (fn-rv-rowsp rows)))
  (if (consp rows)
      (fn-rv-plus (fn-rv-row-demand (car rows)) (fn-rv-outstanding (cdr rows)))
    *fn-rv-zero*))

; -----------------------------------------------------------------------------
; The rows' facts.

(defthm fn-rv-rowsp-forward-to-true-listp
  (implies (fn-rv-rowsp rows) (true-listp rows))
  :rule-classes :forward-chaining)

(defthm fn-rv-rowp-of-nth
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows)))
           (fn-rv-rowp (nth i rows))))

(defthm fn-rv-rowsp-of-update-nth
  (implies (and (fn-rv-rowsp rows) (fn-rv-rowp row) (natp i) (< i (len rows)))
           (fn-rv-rowsp (update-nth i row rows))))

(defthm fn-rv-rowsp-of-idle-rows
  (fn-rv-rowsp (fn-rv-idle-rows n)))

(defthm fn-rv-len-of-idle-rows
  (equal (len (fn-rv-idle-rows n)) (nfix n)))

(defthm fn-rv-vectorp-of-row-demand
  (implies (fn-rv-rowp row) (fn-rv-vectorp (fn-rv-row-demand row))))

(defthm fn-rv-vectorp-of-outstanding
  (implies (fn-rv-rowsp rows) (fn-rv-vectorp (fn-rv-outstanding rows))))

(defthm fn-rv-nats-p-of-outstanding
  (implies (fn-rv-rowsp rows) (fn-rv-nats-p (fn-rv-outstanding rows)))
  :hints (("Goal" :use fn-rv-vectorp-of-outstanding
           :in-theory (disable fn-rv-vectorp-of-outstanding))))

; Replacing one row: what the new rows hold plus the old row's demand is
; what the old rows held plus the new row's demand.
(defthm fn-rv-outstanding-of-update-nth
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows)))
           (equal (fn-rv-plus (fn-rv-outstanding (update-nth i row rows))
                              (fn-rv-row-demand (nth i rows)))
                  (fn-rv-plus (fn-rv-outstanding rows) (fn-rv-row-demand row))))
  :hints (("Goal" :induct (fn-rv-ind-n i rows)
           :in-theory (disable fn-rv-row-demand))))

; A row's demand is within what the rows hold.
(defthm fn-rv-row-demand-below-outstanding
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows)))
           (fn-rv-below (fn-rv-row-demand (nth i rows)) (fn-rv-outstanding rows)))
  :hints (("Goal" :induct (fn-rv-ind-n i rows)
           :in-theory (disable fn-rv-row-demand))))

(defthm fn-rv-outstanding-of-idle-rows
  (equal (fn-rv-outstanding (fn-rv-idle-rows n)) *fn-rv-zero*))

(in-theory (disable fn-rv-outstanding fn-rv-row-demand fn-rv-rowp fn-rv-rowsp
                    fn-rv-idle-rows fn-rv-idle-row))

; -----------------------------------------------------------------------------
; The bank.

(defun fn-rv-make (budget drawn slots)
  (declare (xargs :guard t))
  (list budget drawn slots))

(defun fn-rv-budget (bank) (declare (xargs :guard t)) (nth 0 (true-list-fix bank)))
(defun fn-rv-drawn (bank) (declare (xargs :guard t)) (nth 1 (true-list-fix bank)))
(defun fn-rv-slots (bank) (declare (xargs :guard t)) (nth 2 (true-list-fix bank)))

; The structural recognizer (the guard of every transition); FN-RV-OKP
; below adds the carried invariant.
(defun fn-rv-bankp (bank)
  (declare (xargs :guard t))
  (and (fn-rv-vectorp (fn-rv-budget bank))
       (fn-rv-vectorp (fn-rv-drawn bank))
       (fn-rv-rowsp (fn-rv-slots bank))))

(defun fn-rv-slot-count (bank)
  (declare (xargs :guard (fn-rv-bankp bank)))
  (len (fn-rv-slots bank)))

(defun fn-rv-slotp (slot bank)
  (declare (xargs :guard (fn-rv-bankp bank)))
  (and (natp slot) (< slot (fn-rv-slot-count bank))))

(defun fn-rv-row (slot bank)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot))))
  (let ((r (nth slot (fn-rv-slots bank))))
    (if (consp r) r *fn-rv-idle*)))

(defun fn-rv-phase (slot bank)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot))))
  (nfix (car (fn-rv-row slot bank))))

(defun fn-rv-gen (slot bank)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot))))
  (let ((r (fn-rv-row slot bank)))
    (if (consp (cdr r)) (nfix (cadr r)) 0)))

(defun fn-rv-demand (slot bank)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot))))
  (let ((r (fn-rv-row slot bank)))
    (if (consp (cdr r)) (true-list-fix (cddr r)) nil)))

(defun fn-rv-fundedp (bank)
  (declare (xargs :guard (fn-rv-bankp bank)))
  (fn-rv-below (fn-rv-drawn bank) (fn-rv-budget bank)))

(defun fn-rv-slack (bank)
  (declare (xargs :guard (fn-rv-bankp bank)))
  (fn-rv-monus (fn-rv-budget bank) (fn-rv-drawn bank)))

(defun fn-rv-okp (bank)
  (declare (xargs :guard t))
  (and (fn-rv-bankp bank)
       (fn-rv-below (fn-rv-drawn bank) (fn-rv-budget bank))
       (equal (fn-rv-reusable (fn-rv-drawn bank))
              (fn-rv-reusable (fn-rv-outstanding (fn-rv-slots bank))))
       (fn-rv-below (fn-rv-spent (fn-rv-outstanding (fn-rv-slots bank)))
                    (fn-rv-spent (fn-rv-drawn bank)))))

; -----------------------------------------------------------------------------
; The transitions.  A charge answers (WORD BANK' GEN): GEN is the token of
; the draw; every later step on the slot names it.

(defun fn-rv-charge (bank slot demand phase)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot) (true-listp demand)
                              (or (eql phase 1) (eql phase 2)))))
  (cond ((not (and (fn-rv-slotp slot bank) (fn-rv-vectorp demand)))
         (list :invalid-draw bank))
        ((not (eql (fn-rv-phase slot bank) 0))
         (list :slot-busy bank))
        ((not (fn-rv-below (fn-rv-plus (fn-rv-drawn bank) demand) (fn-rv-budget bank)))
         (list :resources-unavailable bank))
        (t (let ((gen (+ 1 (fn-rv-gen slot bank))))
             (list (if (eql phase 2) :opened :drawn)
                   (fn-rv-make (fn-rv-budget bank)
                               (fn-rv-plus (fn-rv-drawn bank) demand)
                               (update-nth slot (list* phase gen demand) (fn-rv-slots bank)))
                   gen)))))

(defun fn-rv-draw (bank slot demand)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot) (true-listp demand))))
  (fn-rv-charge bank slot demand 1))

(defun fn-rv-open (bank slot budget)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot) (true-listp budget))))
  (fn-rv-charge bank slot budget 2))

; The token names the slot's current draw: phase 1 and the generation.
(defun fn-rv-drawnp (slot gen bank)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot))))
  (and (eql (fn-rv-phase slot bank) 1) (equal (fn-rv-gen slot bank) gen)))

(defun fn-rv-sub-bankp (slot gen bank)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot))))
  (and (eql (fn-rv-phase slot bank) 2) (equal (fn-rv-gen slot bank) gen)))

(defun fn-rv-settle (bank slot gen)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot))))
  (cond ((not (fn-rv-slotp slot bank)) (list :invalid-slot bank))
        ((not (fn-rv-drawnp slot gen bank)) (list :stale bank))
        (t (list :settled
               (fn-rv-make (fn-rv-budget bank)
                           (fn-rv-monus (fn-rv-drawn bank)
                                        (fn-rv-reusable (fn-rv-demand slot bank)))
                           (update-nth slot (fn-rv-idle-row (fn-rv-gen slot bank))
                                       (fn-rv-slots bank)))))))

(defun fn-rv-refund (bank slot gen x)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot) (true-listp x))))
  (cond ((not (and (fn-rv-slotp slot bank) (fn-rv-vectorp x))) (list :invalid-refund bank))
        ((not (fn-rv-drawnp slot gen bank)) (list :stale bank))
        ((not (fn-rv-below x (fn-rv-reusable (fn-rv-demand slot bank))))
         (list :past-what-it-holds bank))
        (t (list :refunded
               (fn-rv-make (fn-rv-budget bank)
                           (fn-rv-monus (fn-rv-drawn bank) x)
                           (update-nth slot (list* 1 (fn-rv-gen slot bank)
                                                   (fn-rv-monus (fn-rv-demand slot bank) x))
                                       (fn-rv-slots bank)))))))

(defun fn-rv-grow (bank slot gen x)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot) (true-listp x))))
  (cond ((not (and (fn-rv-slotp slot bank) (fn-rv-vectorp x))) (list :invalid-grow bank))
        ((not (fn-rv-sub-bankp slot gen bank)) (list :stale bank))
        ((not (fn-rv-below (fn-rv-plus (fn-rv-drawn bank) x) (fn-rv-budget bank)))
         (list :resources-unavailable bank))
        (t (list :grown
               (fn-rv-make (fn-rv-budget bank)
                           (fn-rv-plus (fn-rv-drawn bank) x)
                           (update-nth slot (list* 2 (fn-rv-gen slot bank)
                                                   (fn-rv-plus (fn-rv-demand slot bank) x))
                                       (fn-rv-slots bank)))))))

(defun fn-rv-destroy (bank slot gen spent)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp slot) (true-listp spent))))
  (cond ((not (and (fn-rv-slotp slot bank) (fn-rv-vectorp spent))) (list :invalid-destroy bank))
        ((not (fn-rv-sub-bankp slot gen bank)) (list :stale bank))
        ((not (fn-rv-below spent (fn-rv-spent (fn-rv-demand slot bank))))
         (list :sub-bank-overspent bank))
        (t (list :destroyed
               (fn-rv-make (fn-rv-budget bank)
                           (fn-rv-plus (fn-rv-monus (fn-rv-drawn bank) (fn-rv-demand slot bank))
                                       spent)
                           (update-nth slot (fn-rv-idle-row (fn-rv-gen slot bank))
                                       (fn-rv-slots bank)))))))

; Every transition as one step: OP is (:draw SLOT DEMAND), (:open SLOT
; BUDGET), (:settle SLOT GEN), (:refund SLOT GEN X), (:grow SLOT GEN X) or
; (:destroy SLOT GEN SPENT).
(defun fn-rv-step (bank op)
  (declare (xargs :guard (and (fn-rv-bankp bank) (true-listp op))))
  (let ((slot (nfix (nth 1 op)))
        (gen (nth 2 op))
        (arg (true-list-fix (nth 3 op))))
    (case (car op)
      (:draw (fn-rv-draw bank slot (true-list-fix (nth 2 op))))
      (:open (fn-rv-open bank slot (true-list-fix (nth 2 op))))
      (:settle (fn-rv-settle bank slot gen))
      (:refund (fn-rv-refund bank slot gen arg))
      (:grow (fn-rv-grow bank slot gen arg))
      (:destroy (fn-rv-destroy bank slot gen arg))
      (otherwise (list :unknown-step bank)))))

(defun fn-rv-admittedp (word)
  (declare (xargs :guard t))
  (and (member-eq word '(:drawn :opened :settled :refunded :grown :destroyed)) t))

(defun fn-rv-run (bank ops)
  (declare (xargs :guard (and (fn-rv-bankp bank) (true-list-listp ops))
                  :verify-guards nil))
  (if (consp ops)
      (let* ((one (fn-rv-step bank (car ops)))
             (rest (fn-rv-run (cadr one) (cdr ops))))
        (list (cons (car one) (car rest)) (cadr rest)))
    (list nil bank)))

(defun fn-rv-any-admittedp (words)
  (declare (xargs :guard t))
  (if (consp words)
      (or (fn-rv-admittedp (car words)) (fn-rv-any-admittedp (cdr words)))
    nil))

; The root: slot 0 the owner's permanent baseline (U: the image, the
; threads, the collector's headroom), slot 1 the maintenance reserve (R: the
; next image, the active segment, the rescue release) as a sub-bank, opened
; before any user's slot exists.  A start that cannot fund both is refused
; by the draw's own word.
(defun fn-rv-install (budget baseline reserve nslots)
  (declare (xargs :guard (and (true-listp budget) (true-listp baseline)
                              (true-listp reserve) (natp nslots))
                  :verify-guards nil))
  (if (not (and (fn-rv-vectorp budget) (<= 2 nslots)))
      (list :invalid-install nil)
    (let* ((first (fn-rv-draw (fn-rv-make budget *fn-rv-zero* (fn-rv-idle-rows nslots)) 0 baseline))
           (w1 (car first)))
      (if (not (eq w1 :drawn))
          (list w1 nil)
        (let* ((second (fn-rv-open (cadr first) 1 reserve))
               (w2 (car second)))
          (if (not (eq w2 :opened))
              (list w2 nil)
            (list :installed (cadr second))))))))


; -----------------------------------------------------------------------------
; The bank's facts.

(defthm fn-rv-true-list-fix-of-true-listp
  (implies (true-listp x) (equal (true-list-fix x) x)))

(defthm fn-rv-accessors-of-make
  (and (equal (fn-rv-budget (fn-rv-make b d s)) b)
       (equal (fn-rv-drawn (fn-rv-make b d s)) d)
       (equal (fn-rv-slots (fn-rv-make b d s)) s)))

(defthm fn-rv-bankp-forward
  (implies (fn-rv-bankp bank)
           (and (fn-rv-vectorp (fn-rv-budget bank))
                (fn-rv-vectorp (fn-rv-drawn bank))
                (fn-rv-rowsp (fn-rv-slots bank))))
  :rule-classes :forward-chaining)

(defthm fn-rv-okp-forward
  (implies (fn-rv-okp bank)
           (and (fn-rv-bankp bank)
                (fn-rv-below (fn-rv-drawn bank) (fn-rv-budget bank))
                (equal (fn-rv-reusable (fn-rv-drawn bank))
                       (fn-rv-reusable (fn-rv-outstanding (fn-rv-slots bank))))
                (fn-rv-below (fn-rv-spent (fn-rv-outstanding (fn-rv-slots bank)))
                             (fn-rv-spent (fn-rv-drawn bank)))))
  :rule-classes :forward-chaining)

(defthm fn-rv-row-is-the-nth-row
  (implies (and (fn-rv-rowsp (fn-rv-slots bank)) (natp slot)
                (< slot (len (fn-rv-slots bank))))
           (and (equal (fn-rv-row slot bank) (nth slot (fn-rv-slots bank)))
                (equal (fn-rv-phase slot bank) (car (nth slot (fn-rv-slots bank))))
                (equal (fn-rv-gen slot bank) (cadr (nth slot (fn-rv-slots bank))))
                (equal (fn-rv-demand slot bank) (cddr (nth slot (fn-rv-slots bank))))
                (fn-rv-vectorp (cddr (nth slot (fn-rv-slots bank))))
                (natp (car (nth slot (fn-rv-slots bank))))
                (natp (cadr (nth slot (fn-rv-slots bank))))))
  :hints (("Goal" :use (:instance fn-rv-rowp-of-nth (rows (fn-rv-slots bank)) (i slot))
           :in-theory (e/d (fn-rv-rowp) (fn-rv-rowp-of-nth)))))

(defthm fn-rv-rowp-of-list*
  (implies (and (natp p) (<= p 2) (natp g) (fn-rv-vectorp d))
           (fn-rv-rowp (list* p g d)))
  :hints (("Goal" :in-theory (enable fn-rv-rowp))))

(defthm fn-rv-rowp-of-idle-row
  (implies (natp g) (fn-rv-rowp (fn-rv-idle-row g)))
  :hints (("Goal" :in-theory (enable fn-rv-rowp fn-rv-idle-row))))

(defthm fn-rv-rowp-of-idle
  (fn-rv-rowp *fn-rv-idle*)
  :hints (("Goal" :in-theory (enable fn-rv-rowp))))

(defthm fn-rv-idle-row-fields
  (and (consp (fn-rv-idle-row g))
       (consp (cdr (fn-rv-idle-row g)))
       (equal (car (fn-rv-idle-row g)) 0)
       (equal (cadr (fn-rv-idle-row g)) g)
       (equal (cddr (fn-rv-idle-row g)) *fn-rv-zero*))
  :hints (("Goal" :in-theory (enable fn-rv-idle-row))))

(defthm fn-rv-row-demand-of-list*
  (equal (fn-rv-row-demand (list* p g d)) (if (eql p 0) *fn-rv-zero* d))
  :hints (("Goal" :in-theory (enable fn-rv-row-demand))))

(defthm fn-rv-row-demand-of-idle-row
  (equal (fn-rv-row-demand (fn-rv-idle-row g)) *fn-rv-zero*)
  :hints (("Goal" :in-theory (enable fn-rv-row-demand fn-rv-idle-row))))

(defthm fn-rv-row-demand-of-nth
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows)))
           (equal (fn-rv-row-demand (nth i rows))
                  (if (eql (car (nth i rows)) 0) *fn-rv-zero* (cddr (nth i rows)))))
  :hints (("Goal" :in-theory (enable fn-rv-row-demand))))

(defthm fn-rv-len-of-vector
  (implies (fn-rv-vectorp v) (equal (len v) *fn-rv-k*)))

(defthm fn-rv-row-fields-of-nth
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows)))
           (and (fn-rv-vectorp (cddr (nth i rows)))
                (natp (car (nth i rows)))
                (<= (car (nth i rows)) 2)
                (natp (cadr (nth i rows)))))
  :hints (("Goal" :use fn-rv-rowp-of-nth
           :in-theory (e/d (fn-rv-rowp) (fn-rv-rowp-of-nth)))))

(defthm fn-rv-nth-row-shape
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows)))
           (and (consp (nth i rows))
                (consp (cdr (nth i rows)))))
  :hints (("Goal" :use fn-rv-rowp-of-nth
           :in-theory (e/d (fn-rv-rowp) (fn-rv-rowp-of-nth)))))

(defthm fn-rv-car-of-nth-row-natp
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows)))
           (and (integerp (car (nth i rows))) (<= 0 (car (nth i rows)))))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-rv-row-fields-of-nth
           :in-theory (disable fn-rv-row-fields-of-nth))))

(defthm fn-rv-cadr-of-nth-row-natp
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows)))
           (and (integerp (cadr (nth i rows))) (<= 0 (cadr (nth i rows)))))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-rv-row-fields-of-nth
           :in-theory (disable fn-rv-row-fields-of-nth))))

(defthm fn-rv-nth-of-idle-rows
  (implies (and (natp i) (< i (nfix n)))
           (equal (nth i (fn-rv-idle-rows n)) *fn-rv-idle*))
  :hints (("Goal" :induct (fn-rv-ind-nn i n)
           :in-theory (enable fn-rv-idle-rows))))

; Replacing row I, each as a direct rewrite of the new outstanding vector:
; an idle row charged with D; a charged row idled; a charged row's demand
; replaced by D2.
(defthm fn-rv-outstanding-after-charging-an-idle-row
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows))
                (equal (car (nth i rows)) 0) (fn-rv-vectorp d) (natp g)
                (natp p) (<= p 2) (not (equal p 0)))
           (equal (fn-rv-outstanding (update-nth i (list* p g d) rows))
                  (fn-rv-plus (fn-rv-outstanding rows) d)))
  :hints (("Goal" :use (:instance fn-rv-outstanding-of-update-nth (row (list* p g d)))
           :in-theory (disable fn-rv-outstanding-of-update-nth))))

(defthm fn-rv-outstanding-after-idling-a-charged-row
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows))
                (not (equal (car (nth i rows)) 0)) (natp g))
           (equal (fn-rv-outstanding (update-nth i (fn-rv-idle-row g) rows))
                  (fn-rv-monus (fn-rv-outstanding rows) (cddr (nth i rows)))))
  :hints (("Goal" :use ((:instance fn-rv-outstanding-of-update-nth (row (fn-rv-idle-row g)))
                        (:instance fn-rv-monus-of-plus-same
                                   (a (fn-rv-outstanding (update-nth i (fn-rv-idle-row g) rows)))
                                   (b (cddr (nth i rows)))))
           :in-theory (disable fn-rv-outstanding-of-update-nth fn-rv-monus-of-plus-same))))

(defthm fn-rv-outstanding-after-replacing-a-charged-row
  (implies (and (fn-rv-rowsp rows) (natp i) (< i (len rows))
                (not (equal (car (nth i rows)) 0)) (fn-rv-vectorp d2) (natp g)
                (natp p) (<= p 2) (not (equal p 0)))
           (equal (fn-rv-outstanding (update-nth i (list* p g d2) rows))
                  (fn-rv-monus (fn-rv-plus (fn-rv-outstanding rows) d2) (cddr (nth i rows)))))
  :hints (("Goal" :use ((:instance fn-rv-outstanding-of-update-nth (row (list* p g d2)))
                        (:instance fn-rv-vectorp-of-outstanding
                                   (rows (update-nth i (list* p g d2) rows)))
                        (:instance fn-rv-monus-of-plus-same
                                   (a (fn-rv-outstanding (update-nth i (list* p g d2) rows)))
                                   (b (cddr (nth i rows)))))
           :in-theory (disable fn-rv-outstanding-of-update-nth fn-rv-monus-of-plus-same))))

; The algebra of each transition over vectors alone: DR the drawn vector
; and O the rows' outstanding before, D the row's demand, M the reusable
; mask; the two invariant hypotheses are fn-rv-okp's.
(local
 (defthm fn-rv-charge-algebra
   (implies (and (fn-rv-vectorp dr) (fn-rv-vectorp o) (fn-rv-vectorp d)
                 (equal (fn-rv-keep dr m) (fn-rv-keep o m))
                 (fn-rv-below (fn-rv-drop o m) (fn-rv-drop dr m)))
            (and (equal (fn-rv-keep (fn-rv-plus dr d) m) (fn-rv-keep (fn-rv-plus o d) m))
                 (fn-rv-below (fn-rv-drop (fn-rv-plus o d) m) (fn-rv-drop (fn-rv-plus dr d) m))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-rv-below-plus-monotone
                                    (a (fn-rv-drop o m)) (b (fn-rv-drop dr m)) (c (fn-rv-drop d m))))))))

(local
 (defthm fn-rv-settle-algebra
   (implies (and (fn-rv-vectorp dr) (fn-rv-vectorp o) (fn-rv-vectorp d)
                 (equal (fn-rv-keep dr m) (fn-rv-keep o m))
                 (fn-rv-below (fn-rv-drop o m) (fn-rv-drop dr m)))
            (and (equal (fn-rv-keep (fn-rv-monus dr (fn-rv-keep d m)) m)
                        (fn-rv-keep (fn-rv-monus o d) m))
                 (fn-rv-below (fn-rv-drop (fn-rv-monus o d) m)
                              (fn-rv-drop (fn-rv-monus dr (fn-rv-keep d m)) m))
                 (fn-rv-below (fn-rv-monus dr (fn-rv-keep d m)) dr)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-rv-below-transitive
                                    (a (fn-rv-monus (fn-rv-drop o m) (fn-rv-drop d m)))
                                    (b (fn-rv-drop o m)) (c (fn-rv-drop dr m))))))))

(local
 (defthm fn-rv-refund-algebra
   (implies (and (fn-rv-vectorp dr) (fn-rv-vectorp o) (fn-rv-vectorp d) (fn-rv-vectorp x)
                 (equal (fn-rv-keep dr m) (fn-rv-keep o m))
                 (fn-rv-below (fn-rv-drop o m) (fn-rv-drop dr m))
                 (fn-rv-below x (fn-rv-keep d m)))
            (and (equal (fn-rv-keep (fn-rv-monus dr x) m)
                        (fn-rv-keep (fn-rv-monus (fn-rv-plus o (fn-rv-monus d x)) d) m))
                 (fn-rv-below (fn-rv-drop (fn-rv-monus (fn-rv-plus o (fn-rv-monus d x)) d) m)
                              (fn-rv-drop (fn-rv-monus dr x) m))
                 (fn-rv-below (fn-rv-monus dr x) dr)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-rv-below-drop-monotone (a x) (b (fn-rv-keep d m)))
                  (:instance fn-rv-below-keep-monotone (a x) (b (fn-rv-keep d m)))
                  (:instance fn-rv-below-zeros-is-zeros (v (fn-rv-drop x m)) (n *fn-rv-k*))
                  (:instance fn-rv-refund-arithmetic
                             (o (fn-rv-keep o m)) (d (fn-rv-keep d m)) (x (fn-rv-keep x m)))
                  (:instance fn-rv-monus-of-plus-same (a (fn-rv-drop o m)) (b (fn-rv-drop d m))))))))

(local
 (defthm fn-rv-grow-algebra
   (implies (and (fn-rv-vectorp dr) (fn-rv-vectorp o) (fn-rv-vectorp d) (fn-rv-vectorp x)
                 (equal (fn-rv-keep dr m) (fn-rv-keep o m))
                 (fn-rv-below (fn-rv-drop o m) (fn-rv-drop dr m)))
            (and (equal (fn-rv-keep (fn-rv-plus dr x) m)
                        (fn-rv-keep (fn-rv-monus (fn-rv-plus o (fn-rv-plus d x)) d) m))
                 (fn-rv-below (fn-rv-drop (fn-rv-monus (fn-rv-plus o (fn-rv-plus d x)) d) m)
                              (fn-rv-drop (fn-rv-plus dr x) m))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-rv-grow-arithmetic
                             (o (fn-rv-keep o m)) (d (fn-rv-keep d m)) (x (fn-rv-keep x m)))
                  (:instance fn-rv-grow-arithmetic
                             (o (fn-rv-drop o m)) (d (fn-rv-drop d m)) (x (fn-rv-drop x m)))
                  (:instance fn-rv-below-plus-monotone
                             (a (fn-rv-drop o m)) (b (fn-rv-drop dr m)) (c (fn-rv-drop x m))))))))

(local
 (defthm fn-rv-destroy-algebra
   (implies (and (fn-rv-vectorp dr) (fn-rv-vectorp o) (fn-rv-vectorp d) (fn-rv-vectorp s)
                 (fn-rv-vectorp b)
                 (fn-rv-below dr b)
                 (equal (fn-rv-keep dr m) (fn-rv-keep o m))
                 (fn-rv-below (fn-rv-drop o m) (fn-rv-drop dr m))
                 (fn-rv-below s (fn-rv-drop d m))
                 (fn-rv-below d o))
            (and (equal (fn-rv-keep (fn-rv-plus (fn-rv-monus dr d) s) m)
                        (fn-rv-keep (fn-rv-monus o d) m))
                 (fn-rv-below (fn-rv-drop (fn-rv-monus o d) m)
                              (fn-rv-drop (fn-rv-plus (fn-rv-monus dr d) s) m))
                 (fn-rv-below d dr)
                 (fn-rv-below (fn-rv-plus (fn-rv-monus dr d) s) b)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-rv-below-keep-monotone (a s) (b (fn-rv-drop d m)))
                  (:instance fn-rv-below-zeros-is-zeros (v (fn-rv-keep s m)) (n *fn-rv-k*))
                  (:instance fn-rv-below-keep-monotone (a d) (b o))
                  (:instance fn-rv-below-drop-monotone (a d) (b o))
                  (:instance fn-rv-below-transitive
                             (a (fn-rv-drop d m)) (b (fn-rv-drop o m)) (c (fn-rv-drop dr m)))
                  (:instance fn-rv-below-by-keep-and-drop (a d) (b dr))
                  (:instance fn-rv-below-monus-monotone
                             (a (fn-rv-drop o m)) (b (fn-rv-drop dr m)) (c (fn-rv-drop d m)))
                  (:instance fn-rv-below-self-plus
                             (a (fn-rv-monus (fn-rv-drop dr m) (fn-rv-drop d m))) (b (fn-rv-drop s m)))
                  (:instance fn-rv-below-transitive
                             (a (fn-rv-monus (fn-rv-drop o m) (fn-rv-drop d m)))
                             (b (fn-rv-monus (fn-rv-drop dr m) (fn-rv-drop d m)))
                             (c (fn-rv-plus (fn-rv-monus (fn-rv-drop dr m) (fn-rv-drop d m)) (fn-rv-drop s m))))
                  (:instance fn-rv-below-transitive (a s) (b (fn-rv-drop d m)) (c d))
                  (:instance fn-rv-below-plus-monotone-left (a s) (b d) (c (fn-rv-monus dr d)))
                  (:instance fn-rv-plus-of-monus-below (a dr) (b d))
                  (:instance fn-rv-below-transitive
                             (a (fn-rv-plus (fn-rv-monus dr d) s)) (b dr) (c b)))))))

(local
 (defthm fn-rv-row-below-drawn-algebra
   (implies (and (fn-rv-vectorp dr) (fn-rv-vectorp o) (fn-rv-vectorp d)
                 (equal (fn-rv-keep dr m) (fn-rv-keep o m))
                 (fn-rv-below (fn-rv-drop o m) (fn-rv-drop dr m))
                 (fn-rv-below d o))
            (fn-rv-below d dr))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-rv-below-keep-monotone (a d) (b o))
                  (:instance fn-rv-below-drop-monotone (a d) (b o))
                  (:instance fn-rv-below-transitive
                             (a (fn-rv-drop d m)) (b (fn-rv-drop o m)) (c (fn-rv-drop dr m)))
                  (:instance fn-rv-below-by-keep-and-drop (a d) (b dr)))))))

; A charged row's demand is within what the bank has drawn.
(defthm fn-rv-charged-row-within-drawn
  (implies (and (fn-rv-okp bank) (fn-rv-slotp slot bank)
                (not (equal (fn-rv-phase slot bank) 0)))
           (fn-rv-below (fn-rv-demand slot bank) (fn-rv-drawn bank)))
  :hints (("Goal" :in-theory (enable fn-rv-okp fn-rv-bankp)
           :use ((:instance fn-rv-row-below-drawn-algebra
                            (dr (fn-rv-drawn bank)) (o (fn-rv-outstanding (fn-rv-slots bank)))
                            (d (cddr (nth slot (fn-rv-slots bank)))) (m *fn-rv-reusable-mask*))
                 (:instance fn-rv-row-demand-below-outstanding (rows (fn-rv-slots bank)) (i slot))))))

; -----------------------------------------------------------------------------
; The keystones.

(defthm fn-rv-charge-keeps-okp
  (implies (and (fn-rv-okp bank) (or (eql phase 1) (eql phase 2)))
           (fn-rv-okp (cadr (fn-rv-charge bank slot demand phase))))
  :hints (("Goal" :in-theory (enable fn-rv-okp fn-rv-bankp)
           :use ((:instance fn-rv-charge-algebra
                            (dr (fn-rv-drawn bank)) (o (fn-rv-outstanding (fn-rv-slots bank)))
                            (d demand) (m *fn-rv-reusable-mask*))))))

(defthm fn-rv-settle-keeps-okp
  (implies (fn-rv-okp bank)
           (fn-rv-okp (cadr (fn-rv-settle bank slot gen))))
  :hints (("Goal" :in-theory (enable fn-rv-okp fn-rv-bankp)
           :use ((:instance fn-rv-settle-algebra
                            (dr (fn-rv-drawn bank)) (o (fn-rv-outstanding (fn-rv-slots bank)))
                            (d (cddr (nth slot (fn-rv-slots bank)))) (m *fn-rv-reusable-mask*))
                 (:instance fn-rv-below-transitive
                            (a (fn-rv-monus (fn-rv-drawn bank)
                                            (fn-rv-keep (cddr (nth slot (fn-rv-slots bank))) *fn-rv-reusable-mask*)))
                            (b (fn-rv-drawn bank)) (c (fn-rv-budget bank)))))))

(defthm fn-rv-refund-keeps-okp
  (implies (fn-rv-okp bank)
           (fn-rv-okp (cadr (fn-rv-refund bank slot gen x))))
  :hints (("Goal" :in-theory (enable fn-rv-okp fn-rv-bankp)
           :use ((:instance fn-rv-refund-algebra
                            (dr (fn-rv-drawn bank)) (o (fn-rv-outstanding (fn-rv-slots bank)))
                            (d (cddr (nth slot (fn-rv-slots bank)))) (m *fn-rv-reusable-mask*))
                 (:instance fn-rv-below-transitive
                            (a (fn-rv-monus (fn-rv-drawn bank) x))
                            (b (fn-rv-drawn bank)) (c (fn-rv-budget bank)))))))

(defthm fn-rv-grow-keeps-okp
  (implies (fn-rv-okp bank)
           (fn-rv-okp (cadr (fn-rv-grow bank slot gen x))))
  :hints (("Goal" :in-theory (enable fn-rv-okp fn-rv-bankp)
           :use ((:instance fn-rv-grow-algebra
                            (dr (fn-rv-drawn bank)) (o (fn-rv-outstanding (fn-rv-slots bank)))
                            (d (cddr (nth slot (fn-rv-slots bank)))) (m *fn-rv-reusable-mask*))))))

(defthm fn-rv-destroy-keeps-okp
  (implies (fn-rv-okp bank)
           (fn-rv-okp (cadr (fn-rv-destroy bank slot gen spent))))
  :hints (("Goal" :in-theory (enable fn-rv-okp fn-rv-bankp)
           :use ((:instance fn-rv-destroy-algebra
                            (dr (fn-rv-drawn bank)) (o (fn-rv-outstanding (fn-rv-slots bank)))
                            (d (cddr (nth slot (fn-rv-slots bank)))) (s spent) (b (fn-rv-budget bank))
                            (m *fn-rv-reusable-mask*))
                 (:instance fn-rv-row-demand-below-outstanding (rows (fn-rv-slots bank)) (i slot))))))

; KEYSTONE.  From an okp bank every step's result is okp, admitted or not.
(defthm fn-rv-step-keeps-okp
  (implies (fn-rv-okp bank)
           (fn-rv-okp (cadr (fn-rv-step bank op))))
  :hints (("Goal" :in-theory (disable fn-rv-okp fn-rv-charge fn-rv-settle fn-rv-refund
                                      fn-rv-grow fn-rv-destroy))))

(defthm fn-rv-run-keeps-okp
  (implies (fn-rv-okp bank)
           (fn-rv-okp (cadr (fn-rv-run bank ops))))
  :hints (("Goal" :in-theory (disable fn-rv-okp fn-rv-step))))

; KEYSTONE.  A refused step returns the bank itself: the slack is as it was.
(defthm fn-rv-step-refused-keeps-the-bank
  (implies (not (fn-rv-admittedp (car (fn-rv-step bank op))))
           (equal (cadr (fn-rv-step bank op)) bank)))

(defthm fn-rv-refusal-keeps-slack
  (implies (not (fn-rv-admittedp (car (fn-rv-step bank op))))
           (equal (fn-rv-slack (cadr (fn-rv-step bank op))) (fn-rv-slack bank)))
  :hints (("Goal" :in-theory (disable fn-rv-step fn-rv-slack))))

(defthm fn-rv-refused-run-keeps-the-bank
  (implies (not (fn-rv-any-admittedp (car (fn-rv-run bank ops))))
           (equal (cadr (fn-rv-run bank ops)) bank))
  :hints (("Goal" :in-theory (disable fn-rv-step fn-rv-admittedp))))

; KEYSTONE.  A draw is admitted exactly when its slot is idle and the demand
; fits beside everything drawn: the check precedes every effect, and the
; effect is exactly the charge.  (A hypothesis (fn-rv-bankp bank) was removed
; after proving the weakened theorem: the equivalence is by definition.)
(defthm fn-rv-draw-admits-exactly-within-the-budget
  (equal (equal (car (fn-rv-draw bank slot demand)) :drawn)
         (and (fn-rv-slotp slot bank) (fn-rv-vectorp demand)
              (equal (fn-rv-phase slot bank) 0)
              (fn-rv-below (fn-rv-plus (fn-rv-drawn bank) demand) (fn-rv-budget bank)))))

(defthm fn-rv-draw-charges-exactly-the-demand
  (implies (equal (car (fn-rv-draw bank slot demand)) :drawn)
           (and (equal (fn-rv-drawn (cadr (fn-rv-draw bank slot demand)))
                       (fn-rv-plus (fn-rv-drawn bank) demand))
                (equal (fn-rv-budget (cadr (fn-rv-draw bank slot demand)))
                       (fn-rv-budget bank))
                (equal (fn-rv-row slot (cadr (fn-rv-draw bank slot demand)))
                       (list* 1 (+ 1 (fn-rv-gen slot bank)) demand))
                (equal (caddr (fn-rv-draw bank slot demand))
                       (+ 1 (fn-rv-gen slot bank))))))

; KEYSTONE.  A slot settles once: after a settle, a second settle of the
; same token is never admitted and leaves the bank.
(defthm fn-rv-settle-once
  (and (not (equal (car (fn-rv-settle (cadr (fn-rv-settle bank slot gen)) slot gen)) :settled))
       (equal (cadr (fn-rv-settle (cadr (fn-rv-settle bank slot gen)) slot gen))
              (cadr (fn-rv-settle bank slot gen)))))

; KEYSTONE.  A step on one slot leaves every other row as it was.
(defthm fn-rv-step-keeps-the-other-slots
  (implies (and (natp j) (not (equal j (nfix (nth 1 op)))))
           (equal (fn-rv-row j (cadr (fn-rv-step bank op)))
                  (fn-rv-row j bank)))
  :hints (("Goal" :in-theory (disable nth update-nth fn-rv-make fn-rv-slots
                                      fn-rv-budget fn-rv-drawn))))

; The generation of a slot never falls under a step, and a charge raises
; it by one: so a token names one draw of the slot, ever.
(defthm fn-rv-step-never-lowers-a-gen
  (implies (natp j)
           (<= (fn-rv-gen j bank) (fn-rv-gen j (cadr (fn-rv-step bank op)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable nth update-nth fn-rv-make fn-rv-slots
                                      fn-rv-budget fn-rv-drawn))))

(defthm fn-rv-run-never-lowers-a-gen
  (implies (natp j)
           (<= (fn-rv-gen j bank) (fn-rv-gen j (cadr (fn-rv-run bank ops)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-rv-step fn-rv-gen))))

(defthm fn-rv-charge-raises-the-gen
  (implies (fn-rv-admittedp (car (fn-rv-charge bank slot demand phase)))
           (equal (fn-rv-gen slot (cadr (fn-rv-charge bank slot demand phase)))
                  (+ 1 (fn-rv-gen slot bank))))
  :hints (("Goal" :in-theory (disable nth update-nth fn-rv-make fn-rv-slots
                                      fn-rv-budget fn-rv-drawn))))

(defthm fn-rv-settle-needs-the-token
  (implies (equal (car (fn-rv-settle bank slot gen)) :settled)
           (equal (fn-rv-gen slot bank) gen))
  :rule-classes nil)

(defthm fn-rv-slotp-forward
  (implies (fn-rv-slotp slot bank) (natp slot))
  :rule-classes :forward-chaining)

(defthm fn-rv-slotp-of-draw
  (equal (fn-rv-slotp s (cadr (fn-rv-draw bank slot d))) (fn-rv-slotp s bank))
  :hints (("Goal" :in-theory (disable nth update-nth fn-rv-make fn-rv-slots
                                      fn-rv-budget fn-rv-drawn))))

(defthm fn-rv-phase-and-gen-of-draw
  (implies (equal (car (fn-rv-draw bank slot demand)) :drawn)
           (and (equal (fn-rv-phase slot (cadr (fn-rv-draw bank slot demand))) 1)
                (equal (fn-rv-gen slot (cadr (fn-rv-draw bank slot demand)))
                       (+ 1 (fn-rv-gen slot bank)))))
  :hints (("Goal" :in-theory (e/d (fn-rv-phase fn-rv-gen) (fn-rv-row fn-rv-draw))
           :use fn-rv-draw-charges-exactly-the-demand)))

(defthm fn-rv-refused-draw-answers-the-bank
  (implies (not (equal (car (fn-rv-draw bank slot d)) :drawn))
           (and (equal (cadr (fn-rv-draw bank slot d)) bank)
                (equal (caddr (fn-rv-draw bank slot d)) nil)))
  :hints (("Goal" :in-theory (e/d (fn-rv-draw fn-rv-charge)
                                  (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn)))))

; KEYSTONE (Codex review r06 F2, the slot-reuse ABA).  A completion
; replayed after its slot was drawn again is :stale and leaves the bank:
; the first draw's token, any run, a second admitted draw of the slot,
; then the settle of the token.  (The first draw's admission is not
; assumed: a hypothesis (equal (car (fn-rv-draw bank slot d1)) :drawn) was
; removed after proving this weakened theorem -- a refused draw answers no
; token, and settling no token is :stale as well.)
(defthm fn-rv-replayed-completion-is-stale
  (implies (equal (car (fn-rv-draw (cadr (fn-rv-run (cadr (fn-rv-draw bank slot d1)) ops))
                                   slot d2))
                  :drawn)
           (let ((again (cadr (fn-rv-draw (cadr (fn-rv-run (cadr (fn-rv-draw bank slot d1)) ops))
                                          slot d2)))
                 (token (caddr (fn-rv-draw bank slot d1))))
             (and (equal (car (fn-rv-settle again slot token)) :stale)
                  (equal (cadr (fn-rv-settle again slot token)) again))))
  :hints (("Goal"
           :in-theory (e/d (fn-rv-settle fn-rv-drawnp)
                           ((:definition fn-rv-draw) (:definition fn-rv-run) (:definition fn-rv-slotp)
                            (:definition fn-rv-phase) (:definition fn-rv-gen) (:definition fn-rv-row)
                            fn-rv-draw-admits-exactly-within-the-budget
                            fn-rv-draw-charges-exactly-the-demand fn-rv-phase-and-gen-of-draw))
           :cases ((equal (car (fn-rv-draw bank slot d1)) :drawn))
           :use ((:instance fn-rv-refused-draw-answers-the-bank (d d1))
                 (:instance fn-rv-draw-charges-exactly-the-demand (demand d1))
                 (:instance fn-rv-phase-and-gen-of-draw (demand d1))
                 (:instance fn-rv-phase-and-gen-of-draw
                            (bank (cadr (fn-rv-run (cadr (fn-rv-draw bank slot d1)) ops)))
                            (demand d2))
                 (:instance fn-rv-run-never-lowers-a-gen
                            (j slot) (bank (cadr (fn-rv-draw bank slot d1))))
                 (:instance fn-rv-draw-admits-exactly-within-the-budget
                            (bank (cadr (fn-rv-run (cadr (fn-rv-draw bank slot d1)) ops)))
                            (demand d2))))))

; KEYSTONE.  The root: the baseline at slot 0 and the reserve at slot 1 are
; drawn before any user's slot exists, and nothing else is.
(defthm fn-rv-install-reserves-the-owner-first
  (implies (equal (car (fn-rv-install budget baseline reserve nslots)) :installed)
           (and (fn-rv-okp (cadr (fn-rv-install budget baseline reserve nslots)))
                (equal (fn-rv-budget (cadr (fn-rv-install budget baseline reserve nslots)))
                       budget)
                (equal (fn-rv-drawn (cadr (fn-rv-install budget baseline reserve nslots)))
                       (fn-rv-plus baseline reserve))
                (equal (fn-rv-row 0 (cadr (fn-rv-install budget baseline reserve nslots)))
                       (list* 1 1 baseline))
                (equal (fn-rv-row 1 (cadr (fn-rv-install budget baseline reserve nslots)))
                       (list* 2 1 reserve))
                (equal (fn-rv-slot-count (cadr (fn-rv-install budget baseline reserve nslots)))
                       nslots)
                (fn-rv-below (fn-rv-plus baseline reserve) budget)))
  :hints (("Goal" :in-theory (e/d (fn-rv-okp fn-rv-bankp)
                                  (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn)))))

; So every user's step (a slot other than 1) leaves the reserve's budget.
(defthm fn-rv-user-steps-keep-the-reserve
  (implies (not (equal (nfix (nth 1 op)) 1))
           (equal (fn-rv-row 1 (cadr (fn-rv-step bank op)))
                  (fn-rv-row 1 bank)))
  :hints (("Goal" :use (:instance fn-rv-step-keeps-the-other-slots (j 1))
           :in-theory (disable fn-rv-step-keeps-the-other-slots fn-rv-step fn-rv-row))))

; An admitted destroy's effect, exactly.
(defthm fn-rv-destroy-effects
  (implies (and (fn-rv-bankp bank) (fn-rv-slotp slot bank) (fn-rv-vectorp spent)
                (fn-rv-sub-bankp slot gen bank)
                (fn-rv-below spent (fn-rv-spent (fn-rv-demand slot bank))))
           (and (equal (car (fn-rv-destroy bank slot gen spent)) :destroyed)
                (equal (cadr (fn-rv-destroy bank slot gen spent))
                       (fn-rv-make (fn-rv-budget bank)
                                   (fn-rv-plus (fn-rv-monus (fn-rv-drawn bank)
                                                            (fn-rv-demand slot bank))
                                               spent)
                                   (update-nth slot (fn-rv-idle-row (fn-rv-gen slot bank))
                                               (fn-rv-slots bank))))))
  :hints (("Goal" :in-theory (disable nth update-nth fn-rv-make))))

; A sub-bank's spent part is within its budget, and what its budget returns
; after that covers the reusable part of every draw it still holds.
(defthm fn-rv-sub-bank-within-its-budget
  (implies (fn-rv-okp sub)
           (and (fn-rv-below (fn-rv-spent (fn-rv-drawn sub)) (fn-rv-spent (fn-rv-budget sub)))
                (fn-rv-below (fn-rv-spent (fn-rv-drawn sub)) (fn-rv-budget sub))
                (fn-rv-below (fn-rv-reusable (fn-rv-outstanding (fn-rv-slots sub)))
                             (fn-rv-monus (fn-rv-budget sub) (fn-rv-spent (fn-rv-drawn sub))))))
  :hints (("Goal" :in-theory (e/d (fn-rv-okp fn-rv-bankp) (fn-rv-budget fn-rv-drawn fn-rv-slots))
           :use ((:instance fn-rv-below-drop-monotone
                            (a (fn-rv-drawn sub)) (b (fn-rv-budget sub)) (m *fn-rv-reusable-mask*))
                 (:instance fn-rv-below-keep-monotone
                            (a (fn-rv-drawn sub)) (b (fn-rv-budget sub)) (m *fn-rv-reusable-mask*))
                 (:instance fn-rv-below-transitive
                            (a (fn-rv-drop (fn-rv-drawn sub) *fn-rv-reusable-mask*))
                            (b (fn-rv-drop (fn-rv-budget sub) *fn-rv-reusable-mask*))
                            (c (fn-rv-budget sub)))
                 (:instance fn-rv-keep-below-monus-drop
                            (d (fn-rv-budget sub)) (x (fn-rv-drawn sub)) (m *fn-rv-reusable-mask*))
                 (:instance fn-rv-below-transitive
                            (a (fn-rv-keep (fn-rv-outstanding (fn-rv-slots sub)) *fn-rv-reusable-mask*))
                            (b (fn-rv-keep (fn-rv-budget sub) *fn-rv-reusable-mask*))
                            (c (fn-rv-monus (fn-rv-budget sub)
                                            (fn-rv-drop (fn-rv-drawn sub) *fn-rv-reusable-mask*))))))))

; KEYSTONE.  Destroying a sub-bank returns exactly its budget less what it
; had spent, and that covers every draw the sub-bank still had outstanding.
(defthm fn-rv-destroy-returns-exactly-the-unsettled-draws
  (implies (and (fn-rv-okp bank) (fn-rv-okp sub)
                (fn-rv-slotp slot bank)
                (fn-rv-sub-bankp slot gen bank)
                (equal (fn-rv-budget sub) (fn-rv-demand slot bank)))
           (and (equal (car (fn-rv-destroy bank slot gen (fn-rv-spent (fn-rv-drawn sub))))
                       :destroyed)
                (equal (fn-rv-slack (cadr (fn-rv-destroy bank slot gen (fn-rv-spent (fn-rv-drawn sub)))))
                       (fn-rv-plus (fn-rv-slack bank)
                                   (fn-rv-monus (fn-rv-demand slot bank)
                                                (fn-rv-spent (fn-rv-drawn sub)))))
                (fn-rv-below (fn-rv-reusable (fn-rv-outstanding (fn-rv-slots sub)))
                             (fn-rv-monus (fn-rv-demand slot bank) (fn-rv-spent (fn-rv-drawn sub))))
                (equal (fn-rv-phase slot (cadr (fn-rv-destroy bank slot gen (fn-rv-spent (fn-rv-drawn sub)))))
                       0)))
  :hints (("Goal" :in-theory (e/d (fn-rv-slack)
                                  (nth update-nth fn-rv-make fn-rv-destroy fn-rv-okp fn-rv-bankp
                                   fn-rv-budget fn-rv-drawn fn-rv-slots fn-rv-row-is-the-nth-row
                                   fn-rv-slotp fn-rv-phase fn-rv-gen fn-rv-demand fn-rv-row
                                   fn-rv-sub-bankp fn-rv-spent fn-rv-reusable))
           :use ((:instance fn-rv-destroy-effects (spent (fn-rv-spent (fn-rv-drawn sub))))
                 (:instance fn-rv-charged-row-within-drawn)
                 (:instance fn-rv-sub-bank-within-its-budget)
                 (:instance fn-rv-destroy-arithmetic
                            (d (fn-rv-demand slot bank)) (big (fn-rv-drawn bank))
                            (s (fn-rv-spent (fn-rv-drawn sub)))
                            (b (fn-rv-budget bank)))))
          ("Goal'" :in-theory (e/d (fn-rv-slack fn-rv-row fn-rv-phase fn-rv-gen fn-rv-demand
                                    fn-rv-slotp fn-rv-sub-bankp fn-rv-idle-row)
                                   (nth update-nth fn-rv-make fn-rv-destroy fn-rv-okp fn-rv-bankp
                                    fn-rv-budget fn-rv-drawn fn-rv-slots
                                    fn-rv-spent fn-rv-reusable)))))

(defthm fn-rv-bankp-of-draw-and-open
  (implies (fn-rv-bankp bank)
           (and (fn-rv-bankp (cadr (fn-rv-draw bank slot demand)))
                (fn-rv-bankp (cadr (fn-rv-open bank slot demand)))))
  :hints (("Goal" :in-theory (enable fn-rv-bankp))))

; No step changes the budget or the slot count (the composition in
; books/resource-vector-tree.lisp rests on this).
(defthm fn-rv-step-keeps-the-budget-and-the-slot-count
  (and (equal (fn-rv-budget (cadr (fn-rv-step bank op))) (fn-rv-budget bank))
       (equal (fn-rv-slot-count (cadr (fn-rv-step bank op))) (fn-rv-slot-count bank)))
  :hints (("Goal" :in-theory (disable nth update-nth fn-rv-make fn-rv-slots
                                      fn-rv-budget fn-rv-drawn))))

; An admitted step names a slot of the bank, and what it leaves at that
; slot, per transition (the composition rests on these).
(defthm fn-rv-admitted-step-names-a-slot
  (implies (fn-rv-admittedp (car (fn-rv-step bank op)))
           (fn-rv-slotp (nfix (nth 1 op)) bank))
  :hints (("Goal" :in-theory (disable nth update-nth fn-rv-make fn-rv-slots
                                      fn-rv-budget fn-rv-drawn))))

(defthm fn-rv-open-effects
  (implies (equal (car (fn-rv-open bank slot budget)) :opened)
           (and (equal (fn-rv-phase slot (cadr (fn-rv-open bank slot budget))) 2)
                (equal (fn-rv-gen slot (cadr (fn-rv-open bank slot budget)))
                       (+ 1 (fn-rv-gen slot bank)))
                (equal (fn-rv-demand slot (cadr (fn-rv-open bank slot budget))) budget)
                (fn-rv-vectorp budget)))
  :hints (("Goal" :in-theory (e/d (fn-rv-phase fn-rv-gen fn-rv-demand fn-rv-row)
                                  (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn)))))

(defthm fn-rv-settle-effects
  (implies (equal (car (fn-rv-settle bank slot gen)) :settled)
           (equal (fn-rv-phase slot (cadr (fn-rv-settle bank slot gen))) 0))
  :hints (("Goal" :in-theory (e/d (fn-rv-phase fn-rv-row)
                                  (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn)))))

(defthm fn-rv-refund-effects
  (implies (equal (car (fn-rv-refund bank slot gen x)) :refunded)
           (equal (fn-rv-phase slot (cadr (fn-rv-refund bank slot gen x))) 1))
  :hints (("Goal" :in-theory (e/d (fn-rv-phase fn-rv-row)
                                  (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn)))))

(defthm fn-rv-grow-effects
  (implies (equal (car (fn-rv-grow bank slot gen x)) :grown)
           (and (equal (fn-rv-phase slot (cadr (fn-rv-grow bank slot gen x))) 2)
                (equal (fn-rv-gen slot (cadr (fn-rv-grow bank slot gen x))) (fn-rv-gen slot bank))
                (equal (fn-rv-demand slot (cadr (fn-rv-grow bank slot gen x)))
                       (fn-rv-plus (fn-rv-demand slot bank) x))
                (fn-rv-vectorp x)))
  :hints (("Goal" :in-theory (e/d (fn-rv-phase fn-rv-gen fn-rv-demand fn-rv-row)
                                  (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn)))))

(defthm fn-rv-destroy-idles-the-slot
  (implies (equal (car (fn-rv-destroy bank slot gen spent)) :destroyed)
           (and (equal (fn-rv-phase slot (cadr (fn-rv-destroy bank slot gen spent))) 0)
                (equal (fn-rv-gen slot (cadr (fn-rv-destroy bank slot gen spent))) gen)))
  :hints (("Goal" :in-theory (e/d (fn-rv-phase fn-rv-gen fn-rv-row fn-rv-sub-bankp)
                                  (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn)))))

; A token G that names no live sub-bank at slot J (the row is not phase 2
; with generation G, and the generation is at least G) never names one
; again: a charge raises the generation past G, and no other step gives
; the row phase 2 with a lower generation.  Inductive over steps and runs.
(defun fn-rv-token-retiredp (j g bank)
  (declare (xargs :guard (and (fn-rv-bankp bank) (natp j) (natp g))))
  (and (<= g (fn-rv-gen j bank))
       (implies (equal (fn-rv-phase j bank) 2) (< g (fn-rv-gen j bank)))))

(local
 (defthm fn-rv-charge-keeps-a-retired-token
   (implies (and (natp j) (fn-rv-token-retiredp j g bank))
            (fn-rv-token-retiredp j g (cadr (fn-rv-charge bank slot d phase))))
   :hints (("Goal" :in-theory (e/d (fn-rv-charge fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                    fn-rv-phase fn-rv-gen fn-rv-row fn-rv-drawnp fn-rv-sub-bankp
                                    fn-rv-token-retiredp fn-rv-slotp fn-rv-slot-count)
                                   (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn))))))

(local
 (defthm fn-rv-settle-keeps-a-retired-token
   (implies (and (natp j) (fn-rv-token-retiredp j g bank))
            (fn-rv-token-retiredp j g (cadr (fn-rv-settle bank slot gen))))
   :hints (("Goal" :in-theory (e/d (fn-rv-charge fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                    fn-rv-phase fn-rv-gen fn-rv-row fn-rv-drawnp fn-rv-sub-bankp
                                    fn-rv-token-retiredp fn-rv-slotp fn-rv-slot-count)
                                   (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn))))))

(local
 (defthm fn-rv-refund-keeps-a-retired-token
   (implies (and (natp j) (fn-rv-token-retiredp j g bank))
            (fn-rv-token-retiredp j g (cadr (fn-rv-refund bank slot gen x))))
   :hints (("Goal" :in-theory (e/d (fn-rv-charge fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                    fn-rv-phase fn-rv-gen fn-rv-row fn-rv-drawnp fn-rv-sub-bankp
                                    fn-rv-token-retiredp fn-rv-slotp fn-rv-slot-count)
                                   (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn))))))

(local
 (defthm fn-rv-grow-keeps-a-retired-token
   (implies (and (natp j) (fn-rv-token-retiredp j g bank))
            (fn-rv-token-retiredp j g (cadr (fn-rv-grow bank slot gen x))))
   :hints (("Goal" :in-theory (e/d (fn-rv-charge fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                    fn-rv-phase fn-rv-gen fn-rv-row fn-rv-drawnp fn-rv-sub-bankp
                                    fn-rv-token-retiredp fn-rv-slotp fn-rv-slot-count)
                                   (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn))))))

(local
 (defthm fn-rv-destroy-keeps-a-retired-token
   (implies (and (natp j) (fn-rv-token-retiredp j g bank))
            (fn-rv-token-retiredp j g (cadr (fn-rv-destroy bank slot gen x))))
   :hints (("Goal" :in-theory (e/d (fn-rv-charge fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                    fn-rv-phase fn-rv-gen fn-rv-row fn-rv-drawnp fn-rv-sub-bankp
                                    fn-rv-token-retiredp fn-rv-slotp fn-rv-slot-count)
                                   (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn))))))

(defthm fn-rv-step-keeps-a-retired-token
  (implies (and (natp j) (fn-rv-token-retiredp j g bank))
           (fn-rv-token-retiredp j g (cadr (fn-rv-step bank op))))
  :hints (("Goal" :in-theory (e/d (fn-rv-step fn-rv-draw fn-rv-open)
                                  (fn-rv-charge fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                   fn-rv-token-retiredp nth update-nth fn-rv-make)))))

(defthm fn-rv-run-keeps-a-retired-token
  (implies (and (natp j) (fn-rv-token-retiredp j g bank))
           (fn-rv-token-retiredp j g (cadr (fn-rv-run bank ops))))
  :hints (("Goal" :in-theory (e/d (fn-rv-run) (fn-rv-step fn-rv-token-retiredp)))))

(defthm fn-rv-retired-token-names-no-sub-bank
  (implies (fn-rv-token-retiredp j g bank)
           (not (fn-rv-sub-bankp j g bank)))
  :hints (("Goal" :in-theory (enable fn-rv-sub-bankp))))

(defthm fn-rv-destroy-retires-the-token
  (implies (and (natp slot) (equal (car (fn-rv-destroy bank slot gen spent)) :destroyed))
           (fn-rv-token-retiredp slot gen (cadr (fn-rv-destroy bank slot gen spent))))
  :hints (("Goal" :in-theory (e/d (fn-rv-destroy fn-rv-phase fn-rv-gen fn-rv-row fn-rv-sub-bankp
                                   fn-rv-token-retiredp fn-rv-slotp fn-rv-slot-count)
                                  (nth update-nth fn-rv-make fn-rv-slots fn-rv-budget fn-rv-drawn)))))

(verify-guards fn-rv-install
  :hints (("Goal" :in-theory (disable nth update-nth fn-rv-make))))

(in-theory (disable fn-rv-make fn-rv-budget fn-rv-drawn fn-rv-slots fn-rv-bankp fn-rv-okp
                    fn-rv-slot-count fn-rv-slotp fn-rv-row fn-rv-phase fn-rv-gen fn-rv-demand
                    fn-rv-drawnp fn-rv-sub-bankp fn-rv-token-retiredp
                    fn-rv-fundedp fn-rv-slack fn-rv-charge fn-rv-draw fn-rv-open
                    fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy fn-rv-step
                    fn-rv-run fn-rv-install))
