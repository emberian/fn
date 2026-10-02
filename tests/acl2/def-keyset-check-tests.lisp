; Teeth for books/def-keyset-check.lisp: one instance per sense, both
; executable arms at 0, threshold-1, threshold and threshold+1 elements,
; success and failure in each arm, a dotted tail under :base (null xs),
; the keyed instance with its named membership correspondence, the owed
; bridges witnessed through defteeth, and the refusals by name (c04 6a/6b).

(in-package "ACL2")
(include-book "../../books/def-keyset-check")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

; ---------------------------------------------------------------------------
; 1. :absent over identity keys (books/retention.lisp's disjointness), the
; :long policy: the set past eight elements, the walk below.

(def-keyset-check kct-disjointp (xs ys) :sense :absent)

(defconst *kct-7* '(1 2 3 4 5 6 7))
(defconst *kct-8* '(1 2 3 4 5 6 7 8))
(defconst *kct-9* '(1 2 3 4 5 6 7 8 9))

; the :logic is the walk; the policy chooses the arm by YS's length
(assert-event (and (kct-disjointp nil nil) (kct-disjointp '(10) nil)
                   (kct-disjointp '(10 11) *kct-7*) (not (kct-disjointp '(10 7) *kct-7*))
                   (kct-disjointp '(10 11) *kct-8*) (not (kct-disjointp '(8 11) *kct-8*))
                   (kct-disjointp '(10 11) *kct-9*) (not (kct-disjointp '(11 9) *kct-9*))))
(assert-event (and (not (fn-ks-longp *kct-7*)) (fn-ks-longp *kct-8*)))
; both arms agree with the :logic on every case above
(assert-event (and (equal (kct-disjointp-ks '(10 11) *kct-7*) (kct-disjointp-walk '(10 11) *kct-7*))
                   (equal (kct-disjointp-ks '(10 7) *kct-7*) (kct-disjointp-walk '(10 7) *kct-7*))
                   (equal (kct-disjointp-ks '(11 9) *kct-9*) (kct-disjointp-walk '(11 9) *kct-9*))
                   (equal (kct-disjointp-ks nil nil) (kct-disjointp-walk nil nil))))
; :base t: a dotted tail of XS ends the test as t
(assert-event (and (kct-disjointp '(10 . 11) *kct-9*) (kct-disjointp-ks '(10 . 11) *kct-9*)))

(defteeth kct-disjointp-ks-is-logic
  :claim (nil (equal (kct-disjointp-ks xs ys) (kct-disjointp-walk xs ys)))
  :subject kct-disjointp
  :witness ((xs '(10 7)) (ys *kct-9*))
  :breaks nil
  :mutations ((contaminated (:conclusion (equal (kct-disjointp-ks xs ys)
                                                (kct-disjointp-walk xs (cons 10 ys))))
                            ((xs '(10 11)) (ys *kct-9*))
                            :fault "a table holding a key YS never put")))

(defteeth kct-disjointp-walk-is-logic
  :claim (nil (equal (kct-disjointp-walk xs ys) (kct-disjointp xs ys)))
  :subject kct-disjointp
  :witness ((xs '(11 9)) (ys *kct-9*))
  :breaks nil
  :mutations ((inverted (:conclusion (equal (kct-disjointp-walk xs ys)
                                            (not (kct-disjointp xs ys))))
                        ((xs '(10 11)) (ys *kct-9*))
                        :fault "the sense inverted")))

; ---------------------------------------------------------------------------
; 2. :present over keyed records (books/store-files.lisp's successes): each
; XS element is a pair, bound among the records' pairs; :base (null xs); the
; :nonempty policy (no table for an empty XS); the membership stated the
; instance's way, with its correspondence named.

(defun kct-rec-pair (r) (declare (xargs :guard t)) (if (consp r) (car r) nil))
(defun kct-pairp (x) (declare (xargs :guard t)) (and (consp x) (natp (car x)) (natp (cdr x))))

(defun kct-has-pairp (pair records)
  (declare (xargs :guard t))
  (if (consp records)
      (or (equal pair (kct-rec-pair (car records))) (kct-has-pairp pair (cdr records)))
    nil))

(defun kct-pairs (records)
  (declare (xargs :guard t))
  (if (consp records) (cons (kct-rec-pair (car records)) (kct-pairs (cdr records))) nil))

(defthm kct-has-pairp-is-member
  (equal (kct-has-pairp pair records)
         (if (member-equal pair (kct-pairs records)) t nil)))

(def-keyset-check kct-success-listp (successes records)
  :sense :present
  :ys-key (lambda (r) (kct-rec-pair r))
  :each (lambda (x) (kct-pairp x))
  :base (null xs)
  :keys kct-pairs
  :logic-member (lambda (x ys) (kct-has-pairp x ys))
  :member-is kct-has-pairp-is-member
  :policy :nonempty)

(defconst *kct-recs* '(((0 . 7) :a) ((1 . 8) :b) ((2 . 9) :c)))
(assert-event (and (kct-success-listp nil *kct-recs*)
                   (kct-success-listp '((0 . 7)) *kct-recs*)
                   (kct-success-listp '((2 . 9) (0 . 7)) *kct-recs*)
                   (not (kct-success-listp '((3 . 9)) *kct-recs*))      ; unbound
                   (not (kct-success-listp '((0 . 7) x) *kct-recs*))    ; not a pair
                   (not (kct-success-listp '((0 . 7) . 1) *kct-recs*))  ; dotted tail
                   (not (kct-success-listp '((0 . 7)) nil))))
(assert-event (equal (kct-success-listp-ks '((2 . 9) (3 . 9)) *kct-recs*)
                     (kct-success-listp-walk '((2 . 9) (3 . 9)) *kct-recs*)))

(defteeth kct-success-listp-ks-is-logic
  :claim (nil (equal (kct-success-listp-ks successes records)
                     (kct-success-listp-walk successes records)))
  :subject kct-success-listp
  :witness ((successes '((2 . 9) (0 . 7))) (records *kct-recs*))
  :breaks nil
  :mutations ((lossy-key (:conclusion (equal (kct-success-listp-ks successes records)
                                             (kct-success-listp-walk successes
                                                                     (cons '((3 . 9) :d) records))))
                         ((successes '((3 . 9))) (records *kct-recs*))
                         :fault "a key put for a record YS does not hold")))

(defteeth kct-success-listp-walk-is-logic
  :claim (nil (equal (kct-success-listp-walk successes records)
                     (kct-success-listp successes records)))
  :subject kct-success-listp
  :witness ((successes '((0 . 7))) (records *kct-recs*))
  :breaks nil
  :mutations ((each-forgotten (:conclusion (equal (kct-success-listp-walk successes records)
                                                  (kct-success-listp (cdr successes) records)))
                              ((successes '(x (0 . 7))) (records *kct-recs*))
                              :fault "the per-element predicate skipped")))

(defteeth-check)

; ---------------------------------------------------------------------------
; 3. Refusals.

(assert-event (equal (fn-kc-refusal 'k '(xs ys) '(:sense :sometimes)) '(:bad-sense k)))
(assert-event (equal (fn-kc-refusal 'k '(xs ys) '(:sense :present :logic-member (lambda (x ys) t)))
                     '(:member-is-pairs-with-logic-member k)))
(assert-event (equal (fn-kc-refusal 'k '(xs ys) '(:sense :present :each (lambda (x y) t)))
                     '(:bad-lambda :each)))
(assert-event (equal (fn-kc-refusal 'k '(xs ys) '(:sense :present :policy :sometimes))
                     '(:bad-policy :sometimes)))
(assert-event (equal (fn-kc-refusal 'k '(xs) '(:sense :present)) '(:bad-formals (xs))))
(assert-event (equal (fn-kc-world-problem 'kct-disjointp '(:sense :absent) (w state))
                     '(:declared-twice kct-disjointp)))
(assert-event (equal (fn-kc-world-problem 'k '(:sense :absent :logic-member (lambda (x ys) t) :member-is nosuch)
                                          (w state))
                     '(:not-a-theorem k nosuch)))
(must-fail-checked
 (def-keyset-check kct-disjointp (xs ys) :sense :absent)
 :unchecked "refused by name at expansion (:declared-twice), before any event")
