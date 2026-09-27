; Teeth for books/defkeystone.lisp.
;
;   1. A keystone through the macro, with every kind of witness it generates:
;      the positive witness, a removal witness and must-fail per hypothesis
;      (one labelled a corrupted state), a mutation, a corrupted state, and
;      the :restates check against a separately admitted theorem.
;   2. The expansion pinned to one literal.  tools/ledger.py's
;      `defkeystone_expansion' reads the same two constants and must produce
;      the same literal (tests/test_ledger.py), so the static tools and ACL2
;      see one expansion.
;   3. One refusal per rule of `fn-dk-refusal', each naming what is missing,
;      and the macro itself refusing under must-fail (a hypothesis with no
;      breaking value; a breaking value at which a retained hypothesis fails;
;      a :restates whose formula differs).

(in-package "ACL2")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

(defun fn-dkt-add (x y)
  (declare (xargs :guard (acl2-numberp y)))
  (if (and (natp x) (< x 10)) (+ x y) 0))

; The statement as a source book would state it.
(defthm fn-dkt-add-adds-source
  (implies (and (natp x) (< x 10)) (equal (fn-dkt-add x y) (+ x y)))
  :hints (("Goal" :in-theory (enable fn-dkt-add))))

; ---------------------------------------------------------------------------
; 1. The keystone.  `:id :test' tells tools/keystone_emit.py this is a test
; of the macro, not a registry keystone.  x = 10 is reachable by any caller; it is labelled a
; corrupted state here only so that the label's text is exercised.

(defkeystone fn-dkt-add-adds
  (implies (and (natp x) (< x 10)) (equal (fn-dkt-add x y) (+ x y)))
  :subject fn-dkt-add
  :id :test
  :restates fn-dkt-add-adds-source
  :hyps (natp small)
  :witness ((x 3) (y 4))
  :breaks ((natp ((x -1)))
           (small ((x 10)) :corrupt "a label test, not a claim"))
  :mutations ((off-by-one (equal (fn-dkt-add x y) (+ 1 x y)) ((x 3))))
  :corrupt ((not-a-number ((x 'a))))
  :hints (("Goal" :in-theory (enable fn-dkt-add))))

; ---------------------------------------------------------------------------
; 2. The expansion, pinned.  The form below is the one admitted above.

(defconst *fn-dkt-sample*
  '(defkeystone fn-dkt-add-adds
     (implies (and (natp x) (< x 10)) (equal (fn-dkt-add x y) (+ x y)))
     :subject fn-dkt-add
     :id :test
     :restates fn-dkt-add-adds-source
     :hyps (natp small)
     :witness ((x 3) (y 4))
     :breaks ((natp ((x -1)))
              (small ((x 10)) :corrupt "a label test, not a claim"))
     :mutations ((off-by-one (equal (fn-dkt-add x y) (+ 1 x y)) ((x 3))))
     :corrupt ((not-a-number ((x 'a))))
     :hints (("Goal" :in-theory (enable fn-dkt-add)))))

(defconst *fn-dkt-sample-expansion*
  '(progn
     (defthm fn-dkt-add-adds
       (implies (and (natp x) (< x 10)) (equal (fn-dkt-add x y) (+ x y)))
       :hints (("Goal" :in-theory (enable fn-dkt-add))))
     (assert-event (equal (getpropc 'fn-dkt-add-adds 'theorem nil (w state))
                          (getpropc 'fn-dkt-add-adds-source 'theorem nil (w state)))
                   :msg "FN-DKT-ADD-ADDS: restates")
     (assert-event (and (let* ((x 3) (y 4)) (declare (ignorable x y)) (natp x))
                        (let* ((x 3) (y 4)) (declare (ignorable x y)) (< x 10))
                        (let* ((x 3) (y 4)) (declare (ignorable x y))
                          (equal (fn-dkt-add x y) (+ x y))))
                   :msg "FN-DKT-ADD-ADDS: witness")
     (assert-event
      (with-guard-checking :none
        (and (let* ((x -1) (y 4)) (declare (ignorable x y)) (< x 10))
             (not (let* ((x -1) (y 4)) (declare (ignorable x y)) (natp x)))
             (not (let* ((x -1) (y 4)) (declare (ignorable x y))
                    (equal (fn-dkt-add x y) (+ x y))))))
      :msg "FN-DKT-ADD-ADDS: without NATP")
     (local (must-fail-checked
             (defthm fn-dkt-add-adds-without-natp
               (implies (< x 10) (equal (fn-dkt-add x y) (+ x y)))
               :hints (("Goal" :in-theory (enable fn-dkt-add))))))
     (assert-event
      (with-guard-checking :none
        (and (let* ((x 10) (y 4)) (declare (ignorable x y)) (natp x))
             (not (let* ((x 10) (y 4)) (declare (ignorable x y)) (< x 10)))
             (not (let* ((x 10) (y 4)) (declare (ignorable x y))
                    (equal (fn-dkt-add x y) (+ x y))))))
      :msg "FN-DKT-ADD-ADDS: without SMALL (corrupted state: a label test, not a claim)")
     (local (must-fail-checked
             (defthm fn-dkt-add-adds-without-small
               (implies (natp x) (equal (fn-dkt-add x y) (+ x y)))
               :hints (("Goal" :in-theory (enable fn-dkt-add))))))
     (assert-event
      (with-guard-checking :none
        (not (let* ((x 3) (y 4)) (declare (ignorable x y))
               (equal (fn-dkt-add x y) (+ 1 x y)))))
      :msg "FN-DKT-ADD-ADDS: mutant OFF-BY-ONE")
     (local (must-fail-checked
             (defthm fn-dkt-add-adds-mutant-off-by-one
               (equal (fn-dkt-add x y) (+ 1 x y))
               :hints (("Goal" :in-theory (enable fn-dkt-add))))))
     (assert-event
      (with-guard-checking :none
        (and (not (let* ((x 'a) (y 4)) (declare (ignorable x y))
                    (and (natp x) (< x 10))))
             (not (let* ((x 'a) (y 4)) (declare (ignorable x y))
                    (equal (fn-dkt-add x y) (+ x y))))))
      :msg "FN-DKT-ADD-ADDS: corrupt NOT-A-NUMBER")))

(assert-event (equal (fn-dk-expand *fn-dkt-sample*) *fn-dkt-sample-expansion*))

; ---------------------------------------------------------------------------
; 3. Refusals, each by name.

(defconst *fn-dkt-term*
  '(implies (and (natp x) (< x 10)) (equal (fn-dkt-add x y) (+ x y))))

(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :hyps (natp small)
                         :witness ((x 3) (y 4)) :breaks ((natp ((x -1))))))
        '(:no-breaking-value small (< x 10))))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :witness ((x 3) (y 4))
                         :breaks ((h1 ((x -1))))))
        '(:no-breaking-value h2 (< x 10))))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :hyps (natp small)
                         :breaks ((natp ((x -1))) (small ((x 10))))))
        '(:no-witness k)))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:hyps (natp small) :witness ((x 3) (y 4))
                         :breaks ((natp ((x -1))) (small ((x 10))))))
        '(:no-subject k)))
(assert-event
 (equal (fn-dk-refusal 'k '(equal (fn-dkt-add 3 y) (+ 3 y))
                       '(:subject fn-dkt-add :witness ((y 4))))
        '(:no-teeth k)))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :hyps (natp small)
                         :witness ((x 3) (y 4))
                         :breaks ((natp ((x -1))) (smal ((x 10))))))
        '(:break-names-no-hypothesis smal)))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :hyps (natp small)
                         :witness ((x 3) (y 4)) :hint nil
                         :breaks ((natp ((x -1))) (small ((x 10))))))
        '(:unknown-keyword :hint)))
(assert-event
 (equal (car (fn-dk-refusal 'k *fn-dkt-term*
                            '(:subject fn-dkt-add :hyps (natp)
                              :witness ((x 3) (y 4))
                              :breaks ((natp ((x -1)))))))
        :bad-labels))
(assert-event
 (equal (car (fn-dk-refusal 'k *fn-dkt-term*
                            '(:subject fn-dkt-add :hyps (natp small)
                              :witness ((x 3) (y 4))
                              :breaks ((natp ((x -1)))
                                       (small ((x 10)) :corrupt "")))))
        :bad-breaks))
(assert-event
 (null (fn-dk-refusal 'k *fn-dkt-term*
                      '(:subject fn-dkt-add :hyps (natp small)
                        :witness ((x 3) (y 4))
                        :breaks ((natp ((x -1))) (small ((x 10))))))))

; The macro refuses a hypothesis with no breaking value, at expansion.
(must-fail-checked
 (defkeystone fn-dkt-unbroken
   (implies (and (natp x) (< x 10)) (equal (fn-dkt-add x y) (+ x y)))
   :subject fn-dkt-add :hyps (natp small) :witness ((x 3) (y 4))
   :breaks ((natp ((x -1))))
   :hints (("Goal" :in-theory (enable fn-dkt-add))))
 :expected :hard
 :unchecked "the expansion is refused by name (fn-dk-refusal :no-breaking-value), before any event")

; A breaking value at which a RETAINED hypothesis also fails is not a
; counterexample to the weakened theorem, and its removal witness refuses.
(must-fail-checked
 (defkeystone fn-dkt-misbroken
   (implies (and (natp x) (< x 10)) (equal (fn-dkt-add x y) (+ x y)))
   :subject fn-dkt-add :hyps (natp small) :witness ((x 3) (y 4))
   :breaks ((natp ((x -1))) (small ((x -10))))
   :hints (("Goal" :in-theory (enable fn-dkt-add))))
 :unchecked "a progn of events; its removal witness for SMALL asserts (natp -10)")

; A :restates whose formula differs is refused.
(must-fail-checked
 (defkeystone fn-dkt-misrestated
   (implies (and (natp x) (< x 10)) (equal (fn-dkt-add x y) (+ x y)))
   :subject fn-dkt-add :restates car-cons
   :hyps (natp small) :witness ((x 3) (y 4))
   :breaks ((natp ((x -1))) (small ((x 10))))
   :hints (("Goal" :in-theory (enable fn-dkt-add))))
 :unchecked "a progn of events; its restates check compares two different formulas")
