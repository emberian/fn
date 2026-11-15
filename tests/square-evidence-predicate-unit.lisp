(in-package "ACL2")
(include-book "../books/square-evidence")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-ep-producer (x) (mv :ok x))
(defun fn2-ep-resultp (x) (natp x))
(defun fn2-ep-input (x) x)
(defun fn2-ep-domainp (x) (<= 0 x))
(defun-nx fn2-ep-claim-logical-positive ()
 (let ((x 2)) (and (and (integerp x) (fn2-ep-domainp x)) (fn2-ep-resultp (mv-nth 1 (fn2-ep-producer x))))))
(defthm-owed fn2-ep-claim (x)
 (implies (and (integerp x) (fn2-ep-domainp x))
          (fn2-ep-resultp (mv-nth 1 (fn2-ep-producer x))))
 :teeth (fn2-ep-claim-logical-positive))
; The actual original C must hold, not merely the remaining integer premise.
(must-fail
 (defsquare-evidence fn2-ep-claim :conclusion-kind :predicate
  :positive ((x '-1))
  :negative (:kind :hypothesis-removal :remove (fn2-ep-domainp x) :bindings ((x '-1)))))
; Cannot select an unrelated omitted hypothesis.
(must-fail
 (defsquare-evidence fn2-ep-claim :conclusion-kind :predicate
  :positive ((x '2))
  :negative (:kind :hypothesis-removal :remove (natp x) :bindings ((x '-1)))))
; No open constructor term can masquerade as a ground witness.
(must-fail
 (defsquare-evidence fn2-ep-claim :conclusion-kind :predicate
  :positive ((x (fn2-ep-input y)))
  :negative (:kind :hypothesis-removal :remove (fn2-ep-domainp x) :bindings ((x '-1)))))
; Predicate mode cannot pretend to establish endpoint-mutant correspondence.
(must-fail
 (defsquare-evidence fn2-ep-claim :conclusion-kind :predicate
  :positive ((x '2)) :negative (:kind :mutation :bindings ((x '-1)))))
(defthm fn2-ep-positive-ground
 (and (integerp (fn2-ep-input 2)) (fn2-ep-domainp (fn2-ep-input 2))
      (fn2-ep-resultp (mv-nth 1 (fn2-ep-producer (fn2-ep-input 2)))))
 :rule-classes nil)
(defsquare-evidence fn2-ep-claim :conclusion-kind :predicate
 :positive ((x (fn2-ep-input '2)))
 :positive-hints (("Goal" :use fn2-ep-positive-ground :in-theory (enable fn2-ep-input fn2-ep-resultp)))
 :negative-hints (("Goal" :in-theory (enable fn2-ep-input fn2-ep-resultp)))
 :negative (:kind :hypothesis-removal :remove (fn2-ep-domainp x)
            :bindings ((x (fn2-ep-input '-1)))))
(fn2-assert-square-evidence fn2-ep-claim)
(assert-event (member-eq 'fn2-ep-claim (fn2-owed-names (w state))))
; Coherent-looking metadata cannot redirect the live claim during replay.
(must-fail
 (progn
  (make-event
   (value `(table fn2-squares 'fn2-ep-claim
            ',(let* ((row (fn2-decl-row '(:square fn2-ep-claim) (w state)))
                     (e (fn2-decl-get :evidence row)))
                (fn2-decl-set :evidence
                  (fn2-decl-set :formula ''t e) row)))))
  (fn2-assert-square-evidence fn2-ep-claim)))
; A vacuously true conclusion cannot have a false-C removal witness.
(defun fn2-ep-always (x) (declare (ignore x)) t)
(defun-nx fn2-ep-vacuous-logical-positive ()
 (let ((x 2)) (and (integerp x) (fn2-ep-always x))))
(defthm-owed fn2-ep-vacuous (x)
 (implies (integerp x) (fn2-ep-always x))
 :teeth (fn2-ep-vacuous-logical-positive))
(must-fail
 (defsquare-evidence fn2-ep-vacuous :conclusion-kind :predicate
  :positive ((x '2))
  :negative (:kind :hypothesis-removal :remove (integerp x) :bindings ((x 'nil)))))

; A stored logical guard can itself be a conjunction. Preserve its exact
; subtree and every carrier hypothesis outside it when removing that domain.
(defun-nx fn2-ep-composite-logical-positive ()
 (let ((x 2)) (and (and (rationalp x) (and (integerp x) (fn2-ep-domainp x))) (fn2-ep-resultp (mv-nth 1 (fn2-ep-producer x))))))
(defthm-owed fn2-ep-composite (x)
 (implies (and (rationalp x) (and (integerp x) (fn2-ep-domainp x)))
          (fn2-ep-resultp (mv-nth 1 (fn2-ep-producer x))))
 :teeth (fn2-ep-composite-logical-positive))
(defsquare-evidence fn2-ep-composite :conclusion-kind :predicate
 :positive ((x '2))
 :negative (:kind :hypothesis-removal
            :remove (if (integerp x) (fn2-ep-domainp x) 'nil)
            :bindings ((x '-1))))
(fn2-assert-square-evidence fn2-ep-composite)
; Removing the composite does not excuse a false remaining carrier premise.
(defun-nx fn2-ep-remaining-logical-positive ()
 (let ((x 2)) (and (and (rationalp x) (and (integerp x) (fn2-ep-domainp x))) (fn2-ep-resultp (mv-nth 1 (fn2-ep-producer x))))))
(defthm-owed fn2-ep-remaining (x)
 (implies (and (rationalp x) (and (integerp x) (fn2-ep-domainp x)))
          (fn2-ep-resultp (mv-nth 1 (fn2-ep-producer x))))
 :teeth (fn2-ep-remaining-logical-positive))
(must-fail
 (defsquare-evidence fn2-ep-remaining :conclusion-kind :predicate
  :positive ((x '2))
  :negative (:kind :hypothesis-removal
             :remove (if (integerp x) (fn2-ep-domainp x) 'nil)
             :bindings ((x 'nil)))))

; True C alone is insufficient: the complete positive H must also hold.
(defun fn2-ep-smallp (x) (and (natp x) (< x 10)))
(defun-nx fn2-ep-false-h-logical-positive ()
 (let ((x 2)) (and (fn2-ep-smallp x) (fn2-ep-resultp x))))
(defthm-owed fn2-ep-false-h (x)
 (implies (fn2-ep-smallp x) (fn2-ep-resultp x))
 :teeth (fn2-ep-false-h-logical-positive))
(must-fail
 (defsquare-evidence fn2-ep-false-h :conclusion-kind :predicate
  :positive ((x '20))
  :negative (:kind :hypothesis-removal :remove (fn2-ep-smallp x)
             :bindings ((x '-1)))))
(defun-nx fn2-ep-duplicate-logical-positive ()
 (let ((x 2)) (and (and (integerp x) (fn2-ep-domainp x) (fn2-ep-domainp x)) (fn2-ep-resultp x))))
(defthm-owed fn2-ep-duplicate (x)
 (implies (and (integerp x) (fn2-ep-domainp x) (fn2-ep-domainp x))
          (fn2-ep-resultp x))
 :teeth (fn2-ep-duplicate-logical-positive))
(must-fail
 (defsquare-evidence fn2-ep-duplicate :conclusion-kind :predicate
  :positive ((x '2))
  :negative (:kind :hypothesis-removal :remove (fn2-ep-domainp x)
             :bindings ((x '-1)))))
; Old admitted theorem names/bodies cannot bless redirected bindings.
(must-fail
 (progn
  (make-event
   (value `(table fn2-squares 'fn2-ep-claim
            ',(let* ((row (fn2-decl-row '(:square fn2-ep-claim) (w state)))
                     (e (fn2-decl-get :evidence row)))
                (fn2-decl-set :evidence
                  (fn2-decl-set :positive-bindings '((x '-1)) e) row)))))
  (fn2-assert-square-evidence fn2-ep-claim)))

 ; Explicit multiplicity cannot drift, and removal never drops other premises.
(must-fail
 (defsquare-evidence fn2-ep-duplicate :conclusion-kind :predicate
  :positive ((x '2))
  :negative (:kind :hypothesis-removal :remove (fn2-ep-domainp x)
             :occurrences 3 :bindings ((x '-1)))))
(must-fail
 (defsquare-evidence fn2-ep-duplicate :conclusion-kind :predicate
  :positive ((x '2))
  :negative (:kind :hypothesis-removal :remove (fn2-ep-domainp x)
             :occurrences 2 :bindings ((x '-1/2)))))
(must-fail
 (defsquare-evidence fn2-ep-duplicate :conclusion-kind :predicate
  :positive ((x '2))
  :negative (:kind :hypothesis-removal :remove (fn2-ep-domainp x)
             :occurrences 0 :bindings ((x '-1)))))
(must-fail
 (defsquare-evidence fn2-ep-duplicate :conclusion-kind :predicate
  :positive ((x '2))
  :negative (:kind :hypothesis-removal :remove (fn2-ep-domainp x)
             :occurrences :two :bindings ((x '-1)))))
; A repeated identical premise is one semantic assumption. Its explicit
; multiplicity must match the live formula; default1 still refuses above.
(defsquare-evidence fn2-ep-duplicate :conclusion-kind :predicate
 :positive ((x '2))
 :negative (:kind :hypothesis-removal :remove (fn2-ep-domainp x)
            :occurrences 2 :bindings ((x '-1))))
(fn2-assert-square-evidence fn2-ep-duplicate)
