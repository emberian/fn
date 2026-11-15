(in-package "ACL2")
(include-book "../books/square-evidence")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-ep-producer (x) (mv :ok x))
(defun fn2-ep-resultp (x) (natp x))
(defun fn2-ep-input (x) x)
(defun fn2-ep-domainp (x) (<= 0 x))
(defthm-owed fn2-ep-claim (x)
 (implies (and (integerp x) (fn2-ep-domainp x))
          (fn2-ep-resultp (mv-nth 1 (fn2-ep-producer x)))))
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
(defsquare-evidence fn2-ep-claim :conclusion-kind :predicate
 :positive ((x (fn2-ep-input '2)))
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
(defthm-owed fn2-ep-vacuous (x)
 (implies (integerp x) (fn2-ep-always x)))
(must-fail
 (defsquare-evidence fn2-ep-vacuous :conclusion-kind :predicate
  :positive ((x '2))
  :negative (:kind :hypothesis-removal :remove (integerp x) :bindings ((x 'nil)))))

; A stored logical guard can itself be a conjunction. Preserve its exact
; subtree and every carrier hypothesis outside it when removing that domain.
(defthm-owed fn2-ep-composite (x)
 (implies (and (rationalp x) (and (integerp x) (fn2-ep-domainp x)))
          (fn2-ep-resultp (mv-nth 1 (fn2-ep-producer x)))))
(defsquare-evidence fn2-ep-composite :conclusion-kind :predicate
 :positive ((x '2))
 :negative (:kind :hypothesis-removal
            :remove (if (integerp x) (fn2-ep-domainp x) 'nil)
            :bindings ((x '-1))))
(fn2-assert-square-evidence fn2-ep-composite)
; Removing the composite does not excuse a false remaining carrier premise.
(defthm-owed fn2-ep-remaining (x)
 (implies (and (rationalp x) (and (integerp x) (fn2-ep-domainp x)))
          (fn2-ep-resultp (mv-nth 1 (fn2-ep-producer x)))))
(must-fail
 (defsquare-evidence fn2-ep-remaining :conclusion-kind :predicate
  :positive ((x '2))
  :negative (:kind :hypothesis-removal
             :remove (if (integerp x) (fn2-ep-domainp x) 'nil)
             :bindings ((x 'nil)))))
