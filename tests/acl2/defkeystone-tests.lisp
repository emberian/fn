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
;   4. `defteeth' on a theorem admitted by an ordinary defthm: its row, a
;      visit bound with the state that attains it, the owed-row check
;      (`defteeth-check' passing, and refusing an owed bound the teeth do
;      not state), and its refusals (not a theorem; declared twice).

(in-package "ACL2")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

(defun fn-dkt-add (x y)
  (declare (xargs :guard (acl2-numberp y)))
  (if (and (natp x) (< x 10)) (+ x y) 0))

; The statement as a source book would state it.
(defthm fn-dkt-add-adds-source
  (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y)))
  :hints (("Goal" :in-theory (enable fn-dkt-add))))

; ---------------------------------------------------------------------------
; 1. The keystone.  `:id :test' tells tools/keystone_emit.py this is a test
; of the macro, not a registry keystone.  x = 10 is reachable by any caller; it is labelled a
; corrupted state here only so that the label's text is exercised.

(defkeystone fn-dkt-add-adds
  (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y)))
  :subject fn-dkt-add
  :id :test
  :restates fn-dkt-add-adds-source
  :hyps (natp small)
  :witness ((x 3) (y 4))
  :breaks ((natp ((x -1)))
           (small ((x 10)) :corrupt "a label test, not a claim"))
  :mutations ((strict (< (fix y) (fn-dkt-add x y)) ((x 0))))
  :corrupt ((not-a-number ((x 'a))))
  :hints (("Goal" :in-theory (enable fn-dkt-add))))

; ---------------------------------------------------------------------------
; 2. The expansion, pinned.  The form below is the one admitted above.

(defconst *fn-dkt-sample*
  '(defkeystone fn-dkt-add-adds
     (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y)))
     :subject fn-dkt-add
     :id :test
     :restates fn-dkt-add-adds-source
     :hyps (natp small)
     :witness ((x 3) (y 4))
     :breaks ((natp ((x -1)))
              (small ((x 10)) :corrupt "a label test, not a claim"))
     :mutations ((strict (< (fix y) (fn-dkt-add x y)) ((x 0))))
     :corrupt ((not-a-number ((x 'a))))
     :hints (("Goal" :in-theory (enable fn-dkt-add)))))

(defconst *fn-dkt-sample-expansion*
  '(progn
     (defthm fn-dkt-add-adds (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y))) :hints (("Goal" :in-theory (enable fn-dkt-add))))
     (assert-event (equal (getpropc 'fn-dkt-add-adds 'theorem nil (w state)) (getpropc 'fn-dkt-add-adds-source 'theorem nil (w state))) :msg "FN-DKT-ADD-ADDS: restates")
     (assert-event (and (let* ((x 3) (y 4)) (declare (ignorable x y)) (natp x)) (let* ((x 3) (y 4)) (declare (ignorable x y)) (< x 10)) (let* ((x 3) (y 4)) (declare (ignorable x y)) (<= (fix y) (fn-dkt-add x y)))) :msg "FN-DKT-ADD-ADDS: witness")
     (assert-event (with-guard-checking :none (and (let* ((x -1) (y 4)) (declare (ignorable x y)) (< x 10)) (not (let* ((x -1) (y 4)) (declare (ignorable x y)) (natp x))) (not (let* ((x -1) (y 4)) (declare (ignorable x y)) (<= (fix y) (fn-dkt-add x y)))))) :msg "FN-DKT-ADD-ADDS: without NATP")
     (local (must-fail-checked (defthm fn-dkt-add-adds-without-natp (implies (< x 10) (<= (fix y) (fn-dkt-add x y))) :hints (("Goal" :in-theory (enable fn-dkt-add))))))
     (assert-event (with-guard-checking :none (and (let* ((x 10) (y 4)) (declare (ignorable x y)) (natp x)) (not (let* ((x 10) (y 4)) (declare (ignorable x y)) (< x 10))) (not (let* ((x 10) (y 4)) (declare (ignorable x y)) (<= (fix y) (fn-dkt-add x y)))))) :msg "FN-DKT-ADD-ADDS: without SMALL (corrupted state: a label test, not a claim)")
     (local (must-fail-checked (defthm fn-dkt-add-adds-without-small (implies (natp x) (<= (fix y) (fn-dkt-add x y))) :hints (("Goal" :in-theory (enable fn-dkt-add))))))
     (assert-event (with-guard-checking :none (not (let* ((x 0) (y 4)) (declare (ignorable x y)) (< (fix y) (fn-dkt-add x y))))) :msg "FN-DKT-ADD-ADDS: mutant STRICT")
     (local (must-fail-checked (defthm fn-dkt-add-adds-mutant-strict (< (fix y) (fn-dkt-add x y)) :hints (("Goal" :in-theory (enable fn-dkt-add))))))
     (assert-event (with-guard-checking :none (and (not (let* ((x 'a) (y 4)) (declare (ignorable x y)) (and (natp x) (< x 10)))) (not (let* ((x 'a) (y 4)) (declare (ignorable x y)) (<= (fix y) (fn-dkt-add x y)))))) :msg "FN-DKT-ADD-ADDS: corrupt NOT-A-NUMBER")
     (table fn-teeth 'fn-dkt-add-adds '(:by defkeystone :hyps (natp small) :mutations (strict) :corrupt (not-a-number) :visits nil :allocation nil))))

(assert-event (equal (fn-dk-expand *fn-dkt-sample*) *fn-dkt-sample-expansion*))

; ---------------------------------------------------------------------------
; 3. Refusals, each by name.

(defconst *fn-dkt-term*
  '(implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y))))

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
        '(:no-mutation k)))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :hyps (natp small)
                         :witness ((x 3) (y 4)) :mutations (:none "x")
                         :breaks ((natp ((x -1))) (small ((x 10))))
                         :visits ((steps x 9))))
        '(:bad-visits ((steps x 9)))))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :hyps (natp small)
                         :witness ((x 3) (y 4)) :mutations (:none "x")
                         :breaks ((natp ((x -1))) (small ((x 10))))
                         :visits ((steps x 9 :attains ((x 9)))
                                  (steps x 9 :none "twice"))))
        '(:duplicate-visits (steps steps))))
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
                        :witness ((x 3) (y 4)) :mutations (:none "x")
                        :breaks ((natp ((x -1))) (small ((x 10))))))))

; The macro refuses a hypothesis with no breaking value, at expansion.
(must-fail-checked
 (defkeystone fn-dkt-unbroken
   (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y)))
   :subject fn-dkt-add :hyps (natp small) :witness ((x 3) (y 4))
   :breaks ((natp ((x -1))))
   :hints (("Goal" :in-theory (enable fn-dkt-add))))
 :unchecked "the expansion is refused by name (fn-dk-refusal :no-breaking-value), before any event")

; A breaking value at which a RETAINED hypothesis also fails is not a
; counterexample to the weakened theorem, and its removal witness refuses.
(must-fail-checked
 (defkeystone fn-dkt-misbroken
   (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y)))
   :subject fn-dkt-add :hyps (natp small) :witness ((x 3) (y 4))
   :breaks ((natp ((x -1))) (small ((x -10))))
   :mutations (:none "a refusal test")
   :hints (("Goal" :in-theory (enable fn-dkt-add))))
 :unchecked "a progn of events; its removal witness for SMALL asserts (natp -10)")

; A :restates whose formula differs is refused.
(must-fail-checked
 (defkeystone fn-dkt-misrestated
   (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y)))
   :subject fn-dkt-add :restates car-cons
   :hyps (natp small) :witness ((x 3) (y 4))
   :breaks ((natp ((x -1))) (small ((x 10))))
   :mutations (:none "a refusal test")
   :hints (("Goal" :in-theory (enable fn-dkt-add))))
 :unchecked "a progn of events; its restates check compares two different formulas")

; ---------------------------------------------------------------------------
; 4. defteeth: the teeth of a theorem an ordinary defthm admitted, its literal
; statement read from the world.  A generator owes a visit bound first
; (table fn-teeth-owed); the teeth state it with the same terms, and name
; the state that attains it.

(table fn-teeth-owed 'fn-dkt-add-adds-source '(:by fn-dkt-generator :visits ((x 9))))

(defteeth fn-dkt-add-adds-source
  :hyps (natp small)
  :witness ((x 3) (y 4))
  :breaks ((natp ((x -1))) (small ((x 10))))
  :mutations (:none "the removal witnesses are this test's teeth")
  :visits ((steps x 9 :attains ((x 9))))
  :hints (("Goal" :in-theory (enable fn-dkt-add))))

(assert-event
 (equal (cdr (assoc-eq 'fn-dkt-add-adds-source (table-alist 'fn-teeth (w state))))
        '(:by defteeth :hyps (natp small) :mutations :none :corrupt nil
          :visits ((steps x 9 :attains :rests-on nil)) :allocation nil)))

; The visit bound is a theorem of this world, named by its label.
(assert-event
 (equal (getpropc 'fn-dkt-add-adds-source-visits-steps 'theorem nil (w state))
        '(implies (if (natp x) (< x '10) 'nil) (not (< '9 x)))))

(defteeth-check)

; An owed bound the teeth do not state (fn-dkt-add-adds's row has none).
(must-fail-checked
 (progn (table fn-teeth-owed 'fn-dkt-add-adds '(:by fn-dkt-generator :visits ((x 8))))
        (defteeth-check))
 :unchecked "defteeth-check refuses by name: the teeth of fn-dkt-add-adds state no visit bound (x 8)")

; The refusals of defteeth itself.
(assert-event
 (equal (fn-teeth-refusal 'fn-dkt-nosuch '(:witness ((x 1))) (w state))
        '(:not-a-theorem fn-dkt-nosuch)))
(assert-event
 (equal (fn-teeth-refusal 'fn-dkt-add-adds-source
                          '(:witness ((x 3) (y 4)) :mutations (:none "x")
                            :breaks ((h1 ((x -1))) (h2 ((x 10)))))
                          (w state))
        '(:declared-twice fn-dkt-add-adds-source)))
(assert-event
 (equal (fn-teeth-refusal 'fn-dkt-add-adds-source-visits-steps
                          '(:witness ((x 3)) :mutations (:none "x")
                            :breaks ((h1 ((x -1)))))
                          (w state))
        '(:no-breaking-value h2 (< x 10))))
(must-fail-checked
 (defteeth fn-dkt-nosuch :witness ((x 1)) :breaks nil :mutations (:none "x"))
 :unchecked "the expansion is refused by name (fn-teeth-refusal :not-a-theorem), before any event")
