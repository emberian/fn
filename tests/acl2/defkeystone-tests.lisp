; Teeth for books/defkeystone.lisp (TEETH CONTRACT v1).
;
;   1. A keystone through `defkeystone', with every kind of witness it
;      generates: the positive witness, a removal witness per hypothesis (one
;      :logical), a checked-edit mutation, a corrupted state, and the
;      :restates check against a separately admitted theorem.
;   2. The expansions pinned to literals: `fn-dk-expand' (the defthm, the
;      restates check, the make-event that binds the teeth to the world) and
;      `fn-dk-teeth-events' (the teeth, :formula nil as the static mirror
;      reads them).  tools/ledger.py's `defkeystone_expansion' and
;      `defteeth_expansion' read the same constants and must produce the same
;      literals (tests/test_ledger.py), so the static tools and ACL2 see one
;      expansion.
;   3. One refusal per rule of `fn-dk-spec-refusal' / `fn-dk-refusal', each
;      naming what is missing (world-free), and the macro itself refusing
;      under must-fail (a hypothesis with no breaking value; a breaking value
;      at which a retained hypothesis fails; a :restates whose formula
;      differs).
;   4. `defteeth' on a theorem an ordinary defthm admitted: its row (the
;      claim, the world's formula), a visit bound with the state that attains
;      it, the owed-row check (`defteeth-check' passing, and refusing an owed
;      bound the teeth do not state), the world refusals (not a theorem; the
;      claim differs from the theorem; declared twice), and the two witness
;      modes (:witness-lemma, a :lemma on a removal) with :must-fail t.

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
; of the macro, not a registry keystone.  x = 10 is reachable by any caller;
; its removal is labelled :logical here only so that the label's text and
; the row's kind are exercised.

(defkeystone fn-dkt-add-adds
  (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y)))
  :subject fn-dkt-add
  :id :test
  :restates fn-dkt-add-adds-source
  :hyps (natp small)
  :witness ((x 3) (y 4))
  :breaks ((natp ((x -1)))
           (small ((x 10)) :logical "a label test, not a claim"))
  :mutations ((strict (:conclusion (< (fix y) (fn-dkt-add x y))) ((x 0))
                      :fault "an off-by-one adder"))
  :corrupt ((not-a-number ((x 'a))))
  :hints (("Goal" :in-theory (enable fn-dkt-add))))

(assert-event
 (equal (cdr (assoc-eq 'fn-dkt-add-adds (table-alist 'fn-teeth (w state))))
        '(:by defkeystone
          :claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
          :formula (implies (if (natp x) (< x '10) 'nil)
                            (not (< (fn-dkt-add x y) (fix y))))
          :subject fn-dkt-add
          :witness :executable
          :hyps (natp small)
          :removals ((natp :reachable) (small :logical))
          :mutations ((strict :conclusion "an off-by-one adder"))
          :corrupt (not-a-number)
          :visits nil :allocation nil)))

; ---------------------------------------------------------------------------
; 2. The expansions, pinned.  The form below is the one admitted above.

(defconst *fn-dkt-sample*
  '(defkeystone fn-dkt-add-adds
     (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y)))
     :subject fn-dkt-add
     :id :test
     :restates fn-dkt-add-adds-source
     :hyps (natp small)
     :witness ((x 3) (y 4))
     :breaks ((natp ((x -1)))
              (small ((x 10)) :logical "a label test, not a claim"))
     :mutations ((strict (:conclusion (< (fix y) (fn-dkt-add x y))) ((x 0))
                         :fault "an off-by-one adder"))
     :corrupt ((not-a-number ((x 'a))))
     :hints (("Goal" :in-theory (enable fn-dkt-add)))))

(defconst *fn-dkt-sample-spec*
  '(:claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
    :subject fn-dkt-add
    :witness ((x 3) (y 4))
    :breaks ((natp ((x -1)))
             (small ((x 10)) :logical "a label test, not a claim"))
    :mutations ((strict (:conclusion (< (fix y) (fn-dkt-add x y))) ((x 0))
                        :fault "an off-by-one adder"))
    :corrupt ((not-a-number ((x 'a))))
    :hints (("Goal" :in-theory (enable fn-dkt-add)))))

(defconst *fn-dkt-sample-expansion*
  '(progn
     (defthm fn-dkt-add-adds (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y))) :hints (("Goal" :in-theory (enable fn-dkt-add))))
     (assert-event (equal (getpropc 'fn-dkt-add-adds 'theorem nil (w state)) (getpropc 'fn-dkt-add-adds-source 'theorem nil (w state))) :msg "FN-DKT-ADD-ADDS: restates")
     (make-event (fn-dt-expand 'fn-dkt-add-adds 'defkeystone
                               '(:claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
                                 :subject fn-dkt-add
                                 :witness ((x 3) (y 4))
                                 :breaks ((natp ((x -1)))
                                          (small ((x 10)) :logical "a label test, not a claim"))
                                 :mutations ((strict (:conclusion (< (fix y) (fn-dkt-add x y))) ((x 0))
                                                     :fault "an off-by-one adder"))
                                 :corrupt ((not-a-number ((x 'a))))
                                 :hints (("Goal" :in-theory (enable fn-dkt-add))))
                               state))))

(defconst *fn-dkt-sample-teeth*
  '((assert-event (let* ((x 3) (y 4)) (declare (ignorable x y)) (and (natp x) (< x 10) (<= (fix y) (fn-dkt-add x y)))) :msg "FN-DKT-ADD-ADDS: witness")
    (assert-event (let* ((x -1) (y 4)) (declare (ignorable x y)) (and (< x 10) (not (natp x)) (not (<= (fix y) (fn-dkt-add x y))))) :msg "FN-DKT-ADD-ADDS: without NATP")
    (assert-event (with-guard-checking :none (let* ((x 10) (y 4)) (declare (ignorable x y)) (and (natp x) (not (< x 10)) (not (<= (fix y) (fn-dkt-add x y)))))) :msg "FN-DKT-ADD-ADDS: without SMALL (logical: a label test, not a claim)")
    (assert-event (let* ((x 0) (y 4)) (declare (ignorable x y)) (and (natp x) (< x 10) (<= (fix y) (fn-dkt-add x y)) (not (< (fix y) (fn-dkt-add x y))))) :msg "FN-DKT-ADD-ADDS: mutant STRICT")
    (assert-event (with-guard-checking :none (let* ((x 'a) (y 4)) (declare (ignorable x y)) (and (not (and (natp x) (< x 10))) (not (<= (fix y) (fn-dkt-add x y)))))) :msg "FN-DKT-ADD-ADDS: corrupt NOT-A-NUMBER")
    (table fn-teeth 'fn-dkt-add-adds
           '(:by defkeystone
             :claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
             :formula nil
             :subject fn-dkt-add
             :witness :executable
             :hyps (natp small)
             :removals ((natp :reachable) (small :logical))
             :mutations ((strict :conclusion "an off-by-one adder"))
             :corrupt (not-a-number)
             :visits nil :allocation nil))))

(assert-event (equal (fn-dk-expand *fn-dkt-sample*) *fn-dkt-sample-expansion*))
(assert-event (equal (fn-dk-spec-of 'fn-dkt-add-adds (caddr *fn-dkt-sample*) (cdddr *fn-dkt-sample*))
                     *fn-dkt-sample-spec*))
(assert-event (equal (fn-dk-teeth-events 'fn-dkt-add-adds 'defkeystone
                                         (cadr (assoc-keyword :claim *fn-dkt-sample-spec*))
                                         nil *fn-dkt-sample-spec*)
                     *fn-dkt-sample-teeth*))

; ---------------------------------------------------------------------------
; 3. Refusals, each by name (world-free).

(defconst *fn-dkt-term*
  '(implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y))))

(defconst *fn-dkt-claim*
  '(((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y))))

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
                                       (small ((x 10)) :logical "")))))
        :bad-breaks))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :claim nil :witness ((x 3) (y 4))))
        '(:claim-is-the-term k)))
; mutations: a free term is no longer a mutation; an edit must edit
(assert-event
 (equal (car (fn-dk-refusal 'k *fn-dkt-term*
                            '(:subject fn-dkt-add :hyps (natp small)
                              :witness ((x 3) (y 4))
                              :breaks ((natp ((x -1))) (small ((x 10))))
                              :mutations ((m nil ((x 0)) :fault "x")))))
        :bad-mutations))
; an edit without its fault intent
(assert-event
 (equal (car (fn-dk-refusal 'k *fn-dkt-term*
                            '(:subject fn-dkt-add :hyps (natp small)
                              :witness ((x 3) (y 4))
                              :breaks ((natp ((x -1))) (small ((x 10))))
                              :mutations ((m (:conclusion (< (fix y) (fn-dkt-add x y))) ((x 0)))))))
        :bad-mutations))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :hyps (natp small)
                         :witness ((x 3) (y 4))
                         :breaks ((natp ((x -1))) (small ((x 10))))
                         :mutations ((m (:conclusion nil) ((x 0)) :fault "x"))))
        '(:bad-edit m :constant-conclusion)))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :hyps (natp small)
                         :witness ((x 3) (y 4))
                         :breaks ((natp ((x -1))) (small ((x 10))))
                         :mutations ((m (:conclusion (<= (fix y) (fn-dkt-add x y))) ((x 0)) :fault "x"))))
        '(:bad-edit m :same-conclusion)))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :hyps (natp small)
                         :witness ((x 3) (y 4))
                         :breaks ((natp ((x -1))) (small ((x 10))))
                         :mutations ((m (:hypothesis small t) ((x 0)) :fault "x"))))
        '(:bad-edit m :trivial-hypothesis)))
(assert-event
 (equal (fn-dk-refusal 'k *fn-dkt-term*
                       '(:subject fn-dkt-add :hyps (natp small)
                         :witness ((x 3) (y 4))
                         :breaks ((natp ((x -1))) (small ((x 10))))
                         :mutations ((m (:hypothesis big (< x 100)) ((x 0)) :fault "x"))))
        '(:bad-edit m :edit-names-no-hypothesis)))
; bounds: the shape, duplicates, and a bound without a subject
(assert-event
 (equal (fn-teeth-refusal 'k
                          '(:claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
                            :subject fn-dkt-add
                            :witness ((x 3) (y 4)) :mutations (:deferred "x")
                            :breaks ((natp ((x -1))) (small ((x 10))))
                            :visits ((steps x 9))))
        '(:bad-bound ((steps x 9)))))
(assert-event
 (equal (fn-teeth-refusal 'k
                          '(:claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
                            :subject fn-dkt-add
                            :witness ((x 3) (y 4)) :mutations (:deferred "x")
                            :breaks ((natp ((x -1))) (small ((x 10))))
                            :visits ((steps x 9 :attains ((x 9)))
                                     (steps x 9 :not-attained "twice"))))
        '(:duplicate-bound (steps steps))))
(assert-event
 (equal (fn-teeth-refusal 'k
                          '(:claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
                            :witness ((x 3) (y 4)) :mutations (:deferred "x")
                            :breaks ((natp ((x -1))) (small ((x 10))))
                            :visits ((steps x 9 :attains ((x 9))))))
        '(:bound-without-subject k)))
(assert-event
 (equal (fn-teeth-refusal 'k '(:witness ((x 3)) :mutations (:deferred "x")))
        '(:no-claim k)))
(assert-event
 (null (fn-dk-refusal 'k *fn-dkt-term*
                      '(:subject fn-dkt-add :hyps (natp small)
                        :witness ((x 3) (y 4)) :mutations (:not-applicable "x")
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
   :mutations (:not-applicable "a refusal test")
   :hints (("Goal" :in-theory (enable fn-dkt-add))))
 :unchecked "a progn of events; its removal witness for SMALL asserts (natp -10)")

; A :restates whose formula differs is refused.
(must-fail-checked
 (defkeystone fn-dkt-misrestated
   (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y)))
   :subject fn-dkt-add :restates car-cons
   :hyps (natp small) :witness ((x 3) (y 4))
   :breaks ((natp ((x -1))) (small ((x 10))))
   :mutations (:not-applicable "a refusal test")
   :hints (("Goal" :in-theory (enable fn-dkt-add))))
 :unchecked "a progn of events; its restates check compares two different formulas")

; ---------------------------------------------------------------------------
; 4. defteeth: the teeth of a theorem an ordinary defthm admitted, bound to
; its literal statement.  A generator owes a visit bound first (table
; fn-teeth-owed); the teeth state it with the same terms, and name the state
; that attains it.

(table fn-teeth-owed 'fn-dkt-add-adds-source
       '(:by fn-dkt-generator
         :claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
         :subject fn-dkt-add
         :visits ((x 9))))

(defteeth fn-dkt-add-adds-source
  :claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
  :subject fn-dkt-add
  :witness ((x 3) (y 4))
  :breaks ((natp ((x -1))) (small ((x 10))))
  :mutations (:deferred "the removal witnesses are this test's teeth")
  :visits ((steps x 9 :attains ((x 9))))
  :hints (("Goal" :in-theory (enable fn-dkt-add))))

(assert-event
 (equal (cdr (assoc-eq 'fn-dkt-add-adds-source (table-alist 'fn-teeth (w state))))
        '(:by defteeth
          :claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
          :formula (implies (if (natp x) (< x '10) 'nil)
                            (not (< (fn-dkt-add x y) (fix y))))
          :subject fn-dkt-add
          :witness :executable
          :hyps (natp small)
          :removals ((natp :reachable) (small :reachable))
          :mutations :deferred
          :corrupt nil
          :visits ((steps x 9 :attains :rests-on nil :derived-by nil))
          :allocation nil)))

; The visit bound is a theorem of this world, named by its label.
(assert-event
 (equal (getpropc 'fn-dkt-add-adds-source-visits-steps 'theorem nil (w state))
        '(implies (if (natp x) (< x '10) 'nil) (not (< '9 x)))))

(defteeth-check)

; An owed bound the teeth do not state (fn-dkt-add-adds's row has none).
(must-fail-checked
 (progn (table fn-teeth-owed 'fn-dkt-add-adds
               '(:by fn-dkt-generator
                 :claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
                 :visits ((x 8))))
        (defteeth-check))
 :unchecked "defteeth-check refuses by name: the teeth of fn-dkt-add-adds state no visit bound (x 8)")

; An owed claim the teeth do not state.
(must-fail-checked
 (progn (table fn-teeth-owed 'fn-dkt-add-adds
               '(:by fn-dkt-generator
                 :claim (((natp (natp x))) (<= (fix y) (fn-dkt-add x y)))))
        (defteeth-check))
 :unchecked "defteeth-check refuses by name: the teeth of fn-dkt-add-adds state another claim")

; The world's refusals.
(assert-event
 (equal (fn-dt-world-problem 'fn-dkt-nosuch '(nil t) (w state))
        '(:not-a-theorem fn-dkt-nosuch)))
(assert-event
 (equal (car (fn-dt-world-problem 'fn-dkt-add-adds-source
                                  '(((natp (natp x))) (<= (fix y) (fn-dkt-add x y)))
                                  (w state)))
        :claim-differs))
; the claim is checked before the once-only rule: a differing claim on a
; name with teeth is refused as differing
(assert-event
 (equal (car (fn-dt-world-problem 'fn-dkt-add-adds-source-visits-steps
                                  '(((natp (natp x))) (<= x 9))
                                  (w state)))
        :claim-differs))
(assert-event
 (equal (fn-dt-world-problem 'fn-dkt-add-adds-source *fn-dkt-claim* (w state))
        '(:declared-twice fn-dkt-add-adds-source)))
(must-fail-checked
 (defteeth fn-dkt-nosuch :claim (nil t) :witness ((x 1)) :breaks nil
   :mutations (:not-applicable "x"))
 :unchecked "the expansion is refused by name (fn-dt-world-problem :not-a-theorem), before any event")
(must-fail-checked
 (defteeth fn-dkt-add-adds-source-visits-steps
   :claim (((natp (natp x))) (<= x 9))
   :witness ((x 1)) :breaks ((natp ((x -1)))) :mutations (:not-applicable "x"))
 :unchecked "the expansion is refused by name (fn-dt-world-problem :claim-differs): the theorem has two hypotheses")

; The other witness mode: a named ground theorem whose formula is the
; instantiated claim; and :must-fail t registers the weakened statements.
(defthm fn-dkt-add-adds-again
  (implies (and (natp x) (< x 10)) (<= (fix y) (fn-dkt-add x y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-dkt-add))))

(defthm fn-dkt-ground-witness
  (and (natp 3) (< 3 10) (<= (fix 4) (fn-dkt-add 3 4)))
  :rule-classes nil)

(defthm fn-dkt-ground-removal
  (and (< -1 10) (not (natp -1)) (not (<= (fix 4) (fn-dkt-add -1 4))))
  :rule-classes nil)

(defteeth fn-dkt-add-adds-again
  :claim (((natp (natp x)) (small (< x 10))) (<= (fix y) (fn-dkt-add x y)))
  :witness ((x 3) (y 4))
  :witness-lemma fn-dkt-ground-witness
  :breaks ((natp ((x -1)) :lemma fn-dkt-ground-removal)
           (small ((x 10))))
  :mutations ((weaker (:hypothesis small (< x 20)) ((x 15))
                      :fault "a bound of 20 where the adder stops at 10"))
  :must-fail t
  :hints (("Goal" :in-theory (enable fn-dkt-add))))

(assert-event
 (equal (fn-dk-get :witness (cdr (assoc-eq 'fn-dkt-add-adds-again (table-alist 'fn-teeth (w state)))))
        :lemma))
(assert-event
 (equal (fn-dk-get :removals (cdr (assoc-eq 'fn-dkt-add-adds-again (table-alist 'fn-teeth (w state)))))
        '((natp :lemma) (small :reachable))))

; A lemma-mode witness whose substitution is not closed is refused.
(assert-event
 (equal (car (fn-dt-lemma-problem 'fn-dkt-add-adds-again 'fn-dkt-ground-witness
                                  '((x 3)) '(and (natp x) (< x 10) (<= (fix y) (fn-dkt-add x y)))
                                  (w state)))
        :lemma-open))
(assert-event
 (equal (car (fn-dt-lemma-problem 'fn-dkt-add-adds-again 'fn-dkt-ground-witness
                                  '((x 3) (y z)) '(and (natp x) (< x 10) (<= (fix y) (fn-dkt-add x y)))
                                  (w state)))
        :lemma-open))

; A lemma whose formula is not the instantiated claim is refused.
(must-fail-checked
 (fn-dk-lemma-check fn-dkt-add-adds-again car-cons ((x 3) (y 4))
                    (and (natp x) (< x 10) (<= (fix y) (fn-dkt-add x y))) "witness")
 :unchecked "fn-dk-lemma-check refuses by name (:lemma-differs): car-cons is not the ground claim")
