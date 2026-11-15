; Exact live-claim refutations and CRITICAL stored-guard carrier controls.
; Production bodies/guards are unchanged. All new registry/proof events here
; require their own admission; the four original ground controls retain their
; separately recorded author PASS and do not certify the checkpoint book.
(in-package "ACL2")
(include-book "checkpoint-reader-scalar-domain-unit")
(include-book "../books/owed-discharge")
(include-book "../books/assurance-completion")

(defun-nx fn2-checkpoint-reader-refutation-arguments (which)
 (let* ((row (if (member-eq which '(:checker :positive)) 2 1))
        (base (if (eq which :positive) 256 0))
        (hash (if (eq which :positive) (fn2-digest-slot row *fn2-fc-hash*) 0))
        (geometry (if (eq which :positive) (fn2-digest-slot row *fn2-fc-geometry*) 0))
        (previous (if (eq which :positive) (fn2-digest-slot row *fn2-fc-previous-seal*) 0))
        (fc-n (if (eq which :checker) 1 (+ 1 row)))
        (b3-n (if (eq which :hasher) 0 (+ 1 row)))
        (digest-n (if (eq which :digests) 1 (* *fn2-digest-stride* (+ 1 row))))
        (fn2-checkpoints (fn2-checkpoints-init 1 (create-fn2-checkpoints)))
        (fn2-checkpoints (fn2-checkpoints-put 0 (state *fn2-checkpoint-state-preparing*)
                           (checkpoint 1) (history 1) (incarnation 1)))
        (fn2-checkpoint-refs (fn2-checkpoint-refs-init 6 (create-fn2-checkpoint-refs)))
        (fn2-checkpoint-refs (fn2-checkpoint-refs-put 0 (encoded-length *fn2-format-sector-size*)
                              (writer-epoch 1) (allocation 1)))
        (fn2-checkpoint-bytes (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-fc (fn2-fc-init fc-n (create-fn2-fc)))
        (fn2-fc-context (fn2-fc-context-init (+ 1 row) (create-fn2-fc-context)))
        (fn2-fc-context (fn2-fc-context-put row (location 0) (allocation 1)
                          (history 1) (incarnation 1) (writer-epoch 1)
                          (page-kind *page-kind-checkpoint-descriptor*)
                          (encoded-length *fn2-format-sector-size*)
                          (hash hash) (geometry geometry) (previous-seal previous)))
        (fn2-b3 (fn2-b3-table-init b3-n (create-fn2-b3)))
        (fn2-fields (fn2-fields-init (+ base *fn2-format-sealed-batch-num-fields*) (create-fn2-fields)))
        (fn2-pool (fn2-pool-columns-init 1 (create-fn2-pool)))
        (fn2-pool (resize-fn2-pool-data *fn2-format-sector-size* fn2-pool))
        (fn2-pool (fn2-pool-put 0 (state *fn2-pool-state-workspace*)
                     (cap *fn2-format-sector-size*) (fill *fn2-format-sector-size*)))
        (fn2-digests (fn2-digests-init digest-n (create-fn2-digests)))
        (off 0) (len *fn2-format-sector-size*))
  (list 0 row 0 0 off len base 0 0 0 1 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))

; Zero-argument teeth execute the same whole-guard/whole-original-H
; controls as the ground theorems, using logical stobj semantics throughout.
(defun-nx fn2-checkpoint-reader-guard-positive-check ()
 (fn2-checkpoint-reader-scalar-domain-check :positive))
(defthm fn2-checkpoint-reader-guard-positive-tooth
 (fn2-checkpoint-reader-guard-positive-check)
 :rule-classes nil
 :hints (("Goal" :use fn2-checkpoint-reader-positive-scalar-domain-ground
          :in-theory (e/d (fn2-checkpoint-reader-guard-positive-check)
                         (fn2-checkpoint-reader-scalar-domain-check)))))

(defun-nx fn2-checkpoint-reader-checker-domain-removal-check ()
 (fn2-checkpoint-reader-scalar-domain-check :checker))
(defthm fn2-checkpoint-reader-checker-domain-removal-tooth
 (fn2-checkpoint-reader-checker-domain-removal-check)
 :rule-classes nil
 :hints (("Goal" :use fn2-checkpoint-reader-checker-scalar-domain-ground
          :in-theory (e/d (fn2-checkpoint-reader-checker-domain-removal-check)
                         (fn2-checkpoint-reader-scalar-domain-check)))))

(defun-nx fn2-checkpoint-reader-hasher-domain-removal-check ()
 (fn2-checkpoint-reader-scalar-domain-check :hasher))
(defthm fn2-checkpoint-reader-hasher-domain-removal-tooth
 (fn2-checkpoint-reader-hasher-domain-removal-check)
 :rule-classes nil
 :hints (("Goal" :use fn2-checkpoint-reader-hasher-scalar-domain-ground
          :in-theory (e/d (fn2-checkpoint-reader-hasher-domain-removal-check)
                         (fn2-checkpoint-reader-scalar-domain-check)))))

(defun-nx fn2-checkpoint-reader-digests-domain-removal-check ()
 (fn2-checkpoint-reader-scalar-domain-check :digests))
(defthm fn2-checkpoint-reader-digests-domain-removal-tooth
 (fn2-checkpoint-reader-digests-domain-removal-check)
 :rule-classes nil
 :hints (("Goal" :use fn2-checkpoint-reader-digests-scalar-domain-ground
          :in-theory (e/d (fn2-checkpoint-reader-digests-domain-removal-check)
                         (fn2-checkpoint-reader-scalar-domain-check)))))


; Negation of a closed instance of THIS live original $OWED statement.
(defthm fn2-checkpoint-check-step-checker-type-refuted-instance
 (not (fn2-checkpoint-check-step-checker-type$owed
        (nth 0 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 1 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 2 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 3 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 4 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 5 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 6 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 7 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 8 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 9 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 10 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 11 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 12 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 13 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 14 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 15 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 16 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 17 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 18 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 19 (fn2-checkpoint-reader-refutation-arguments :checker))))
 :rule-classes nil
 :hints (("Goal"
  :use fn2-checkpoint-reader-checker-scalar-domain-ground
  :in-theory (e/d (fn2-checkpoint-reader-refutation-arguments
                    fn2-checkpoint-reader-scalar-domain-check fn2-checkpoint-check-step-checker-type$owed)
                   (fn2-checkpoint-check-step)))))
(defsquare-refuted fn2-checkpoint-check-step-checker-type
 fn2-checkpoint-check-step-checker-type-refuted-instance fn2-checkpoint-check-step-checker-type-under-guard)


; Negation of a closed instance of THIS live original $OWED statement.
(defthm fn2-checkpoint-check-step-checker-wfp-refuted-instance
 (not (fn2-checkpoint-check-step-checker-wfp$owed
        (nth 0 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 1 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 2 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 3 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 4 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 5 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 6 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 7 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 8 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 9 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 10 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 11 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 12 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 13 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 14 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 15 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 16 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 17 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 18 (fn2-checkpoint-reader-refutation-arguments :checker))
        (nth 19 (fn2-checkpoint-reader-refutation-arguments :checker))))
 :rule-classes nil
 :hints (("Goal"
  :use fn2-checkpoint-reader-checker-scalar-domain-ground
  :in-theory (e/d (fn2-checkpoint-reader-refutation-arguments
                    fn2-checkpoint-reader-scalar-domain-check fn2-checkpoint-check-step-checker-wfp$owed)
                   (fn2-checkpoint-check-step)))))
(defsquare-refuted fn2-checkpoint-check-step-checker-wfp
 fn2-checkpoint-check-step-checker-wfp-refuted-instance fn2-checkpoint-check-step-checker-wfp-under-guard)


; Negation of a closed instance of THIS live original $OWED statement.
(defthm fn2-checkpoint-check-step-hasher-type-refuted-instance
 (not (fn2-checkpoint-check-step-hasher-type$owed
        (nth 0 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 1 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 2 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 3 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 4 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 5 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 6 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 7 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 8 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 9 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 10 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 11 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 12 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 13 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 14 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 15 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 16 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 17 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 18 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 19 (fn2-checkpoint-reader-refutation-arguments :hasher))))
 :rule-classes nil
 :hints (("Goal"
  :use fn2-checkpoint-reader-hasher-scalar-domain-ground
  :in-theory (e/d (fn2-checkpoint-reader-refutation-arguments
                    fn2-checkpoint-reader-scalar-domain-check fn2-checkpoint-check-step-hasher-type$owed)
                   (fn2-checkpoint-check-step)))))
(defsquare-refuted fn2-checkpoint-check-step-hasher-type
 fn2-checkpoint-check-step-hasher-type-refuted-instance fn2-checkpoint-check-step-hasher-type-under-guard)


; Negation of a closed instance of THIS live original $OWED statement.
(defthm fn2-checkpoint-check-step-hasher-wfp-refuted-instance
 (not (fn2-checkpoint-check-step-hasher-wfp$owed
        (nth 0 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 1 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 2 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 3 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 4 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 5 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 6 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 7 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 8 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 9 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 10 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 11 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 12 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 13 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 14 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 15 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 16 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 17 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 18 (fn2-checkpoint-reader-refutation-arguments :hasher))
        (nth 19 (fn2-checkpoint-reader-refutation-arguments :hasher))))
 :rule-classes nil
 :hints (("Goal"
  :use fn2-checkpoint-reader-hasher-scalar-domain-ground
  :in-theory (e/d (fn2-checkpoint-reader-refutation-arguments
                    fn2-checkpoint-reader-scalar-domain-check fn2-checkpoint-check-step-hasher-wfp$owed)
                   (fn2-checkpoint-check-step)))))
(defsquare-refuted fn2-checkpoint-check-step-hasher-wfp
 fn2-checkpoint-check-step-hasher-wfp-refuted-instance fn2-checkpoint-check-step-hasher-wfp-under-guard)


; Negation of a closed instance of THIS live original $OWED statement.
(defthm fn2-checkpoint-check-step-digests-type-refuted-instance
 (not (fn2-checkpoint-check-step-digests-type$owed
        (nth 0 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 1 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 2 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 3 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 4 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 5 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 6 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 7 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 8 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 9 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 10 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 11 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 12 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 13 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 14 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 15 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 16 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 17 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 18 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 19 (fn2-checkpoint-reader-refutation-arguments :digests))))
 :rule-classes nil
 :hints (("Goal"
  :use fn2-checkpoint-reader-digests-scalar-domain-ground
  :in-theory (e/d (fn2-checkpoint-reader-refutation-arguments
                    fn2-checkpoint-reader-scalar-domain-check fn2-checkpoint-check-step-digests-type$owed)
                   (fn2-checkpoint-check-step)))))
(defsquare-refuted fn2-checkpoint-check-step-digests-type
 fn2-checkpoint-check-step-digests-type-refuted-instance fn2-checkpoint-check-step-digests-type-under-guard)


; Negation of a closed instance of THIS live original $OWED statement.
(defthm fn2-checkpoint-check-step-digests-wfp-refuted-instance
 (not (fn2-checkpoint-check-step-digests-wfp$owed
        (nth 0 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 1 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 2 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 3 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 4 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 5 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 6 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 7 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 8 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 9 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 10 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 11 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 12 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 13 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 14 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 15 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 16 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 17 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 18 (fn2-checkpoint-reader-refutation-arguments :digests))
        (nth 19 (fn2-checkpoint-reader-refutation-arguments :digests))))
 :rule-classes nil
 :hints (("Goal"
  :use fn2-checkpoint-reader-digests-scalar-domain-ground
  :in-theory (e/d (fn2-checkpoint-reader-refutation-arguments
                    fn2-checkpoint-reader-scalar-domain-check fn2-checkpoint-check-step-digests-wfp$owed)
                   (fn2-checkpoint-check-step)))))
(defsquare-refuted fn2-checkpoint-check-step-digests-wfp
 fn2-checkpoint-check-step-digests-wfp-refuted-instance fn2-checkpoint-check-step-digests-wfp-under-guard)

(local (defun fn2-checkpoint-reader-critical-events (args specs facts)
 (declare (xargs :verify-guards nil))
 (if (atom specs) nil
  (let* ((fact (car facts)) (theorem (cadr fact))
         (claim (fn2-columns-sym theorem "-CLAIM"))
         (negative (cdr (assoc-equal (caddar specs)
                       '((4 . fn2-checkpoint-reader-checker-domain-removal-check)
                         (5 . fn2-checkpoint-reader-hasher-domain-removal-check)
                         (8 . fn2-checkpoint-reader-digests-domain-removal-check))))))
   (append
    `((defthm-owed ,claim ,args ,(caddr fact)
       :teeth (fn2-checkpoint-reader-guard-positive-check ,negative)
       :layer :b :boundary :extraction
       :doc "Actual CHECK-STEP stored-guard carrier theorem, with whole-domain positive and domain-removal logical controls. Not descriptor authentication or boot readiness.")
      (fn2-owed-discharge ,claim ,theorem))
    (fn2-checkpoint-reader-critical-events args (cdr specs) (cdr facts)))))))


; Register the new six CRITICAL extraction/shape contracts from the SAME
; stored-guard metadata and carrier projections as the production interface.
; Each square has exact formula identity plus whole-H positive/removal teeth.
(make-event
 (let* ((world (w state)) (name 'fn2-checkpoint-check-step)
        (args (getpropc name 'formals :missing world))
        (inputs (getpropc name 'stobjs-in nil world))
        (outputs (getpropc name 'stobjs-out nil world))
        (guard (getpropc name 'guard :missing world))
        (carriers '((fn2-fc 4 :prefix "-CHECKER")
                    (fn2-b3 5 :prefix "-HASHER")
                    (fn2-digests 8 :prefix "-DIGESTS")))
        (hyps (remove-duplicates-equal
               (append (fn2-columns-carrier-hyps carriers)
                       (fn2-columns-readonly-type-hyps args inputs nil world)
                       (list guard))))
        (specs (fn2-columns-guard-domain-specs (fn2-columns-carrier-specs carriers)))
        (facts (fn2-columns-preservation-facts name (cons name args) specs hyps nil)))
  (if (or (eq args :missing) (eq guard :missing)
          (not (fn2-columns-contract-carriersp carriers args inputs outputs world)))
      (er soft 'checkpoint-reader-critical "Actual stored-guard producer metadata changed.")
    (value (cons 'progn
     (fn2-checkpoint-reader-critical-events args specs facts))))))

(local (defun fn2-checkpoint-reader-original-rows (names rows)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (cons (assoc-eq (car names) rows)
        (fn2-checkpoint-reader-original-rows (cdr names) rows)))))


; Refutation leaves originals unfinished. No replacement proves an original.
(assert-event
 (let* ((names '(fn2-checkpoint-check-step-checker-type fn2-checkpoint-check-step-checker-wfp fn2-checkpoint-check-step-hasher-type fn2-checkpoint-check-step-hasher-wfp fn2-checkpoint-check-step-digests-type fn2-checkpoint-check-step-digests-wfp))
        (rows (fn2-decl-rows :square (w state))))
  (and (subsetp-eq names (fn2-owed-names (w state)))
       (equal (nth 2 (fn2-square-counts (fn2-checkpoint-reader-original-rows names rows))) 0))))


; Bind predicate conclusions directly in the ONE canonical evidence store.
; All indices/cases are quoted because these are translated closed terms.
(local (defun fn2-checkpoint-reader-evidence-bindings (args which i)
 (declare (xargs :verify-guards nil))
 (if (atom args) nil
  (cons (list (car args)
              `(nth ',i (fn2-checkpoint-reader-refutation-arguments ',which)))
        (fn2-checkpoint-reader-evidence-bindings (cdr args) which (+ 1 i))))))
(local (defun fn2-checkpoint-reader-evidence-hints (ground)
 (declare (xargs :verify-guards nil))
 `(("Goal" :use ,ground
    :in-theory (e/d (fn2-checkpoint-reader-refutation-arguments
                      fn2-checkpoint-reader-scalar-domain-check)
                     (fn2-checkpoint-check-step))))))
(local (defun fn2-checkpoint-reader-evidence-events (specs facts args guard world)
 (declare (xargs :verify-guards nil))
 (if (atom specs) nil
  (let* ((claim (fn2-columns-sym (cadar facts) "-CLAIM"))
         (case (cdr (assoc-equal (caddar specs)
                                '((4 . :checker) (5 . :hasher) (8 . :digests)))))
         (ground (cdr (assoc-eq case
                    '((:checker . fn2-checkpoint-reader-checker-scalar-domain-ground)
                      (:hasher . fn2-checkpoint-reader-hasher-scalar-domain-ground)
                      (:digests . fn2-checkpoint-reader-digests-scalar-domain-ground)))))
         (row (fn2-decl-row (list :square claim) world))
         (statement (fn2-decl-get :statement row))
         (formula (fn2-decl-statement-body statement world)))
   (mv-let (hyp conclusion) (fn2-evidence-parts formula)
    (declare (ignore conclusion))
    (mv-let (count remaining) (fn2-evidence-hypothesis-cut hyp guard)
     (declare (ignore remaining))
     (if (not (and case ground row (equal count 1)
                    (equal args (fn2-decl-get :vars row))))
         (er hard 'checkpoint-reader-evidence
             "Stored guard must occur exactly once in actual live claim ~x0." claim)
       (cons
        (fn2-square-predicate-evidence-events-with-hints
         claim (fn2-checkpoint-reader-evidence-bindings args :positive 0)
         (list :kind :hypothesis-removal :remove guard
               :bindings (fn2-checkpoint-reader-evidence-bindings args case 0))
         (fn2-checkpoint-reader-evidence-hints
          'fn2-checkpoint-reader-positive-scalar-domain-ground)
         (fn2-checkpoint-reader-evidence-hints ground) nil world)
        (cons `(fn2-assert-square-evidence ,claim)
         (fn2-checkpoint-reader-evidence-events (cdr specs) (cdr facts) args guard world))))))))))
(make-event
 (let* ((world (w state)) (name 'fn2-checkpoint-check-step)
        (args (getpropc name 'formals :missing world))
        (guard (getpropc name 'guard :missing world))
        (carriers '((fn2-fc 4 :prefix "-CHECKER")
                    (fn2-b3 5 :prefix "-HASHER")
                    (fn2-digests 8 :prefix "-DIGESTS")))
        (specs (fn2-columns-guard-domain-specs (fn2-columns-carrier-specs carriers)))
        (facts (fn2-columns-preservation-facts name (cons name args) specs nil nil)))
  (if (or (eq args :missing) (eq guard :missing))
      (er soft 'checkpoint-reader-evidence "No actual reader guard/signature.")
    (value (cons 'progn
            (fn2-checkpoint-reader-evidence-events specs facts args guard world))))))
