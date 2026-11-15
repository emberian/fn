; Live obligation/evidence registration for the conditional native-node bridge.
(in-package "ACL2")
(include-book "native-b3-correspondence")
(include-book "assurance-completion")
(include-book "owed-discharge")
(fn2-book-layer :b)

; Exported by the actual qualified ACL2 model for the distinct input rows below;
; the formula-bound proofs independently check these literal values again.
(defconst *fn2-native-node-registry-words*
 '(3173671463 1472550981 728831264 1781307059
   418975159 50482707 149279093 1063045910))

(defun fn2-native-node-registry-seed (fn2-digests)
 (declare (xargs :stobjs fn2-digests :verify-guards nil))
 (let* ((fn2-digests (fn2-digests-init 3 fn2-digests))
        (fn2-digests (fn2-digest-store-words 0 1 2 3 4 5 6 7 8 fn2-digests))
        (fn2-digests (fn2-digest-store-words 1 9 10 11 12 13 14 15 16 fn2-digests))
        (fn2-digests (fn2-digest-store-words 2 17 18 19 20 21 22 23 24 fn2-digests)))
  fn2-digests))

(defun fn2-native-node-registry-statep (middle tail fn2-digests)
 (declare (xargs :stobjs fn2-digests :verify-guards nil))
 (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
      (equal (fn2-digests-rows fn2-digests) 3)
      (equal (fn2-digests-row-snapshot 0 fn2-digests) '(1 2 3 4 5 6 7 8))
      (equal (fn2-digests-row-snapshot 1 fn2-digests) middle)
      (equal (fn2-digests-row-snapshot 2 fn2-digests) tail)))

(defun fn2-native-node-registry-positive ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-digests
  (mv-let (answer fn2-digests)
   (let* ((fn2-digests (fn2-native-node-registry-seed fn2-digests))
          (before-ok (fn2-native-node-registry-statep '(9 10 11 12 13 14 15 16)
                         '(17 18 19 20 21 22 23 24) fn2-digests))
          (fn2-digests (fn2-digest-store-words 1 3173671463 1472550981 728831264 1781307059
                         418975159 50482707 149279093 1063045910 fn2-digests))
          (concrete-ok (fn2-native-node-registry-statep *fn2-native-node-registry-words*
                          '(17 18 19 20 21 22 23 24) fn2-digests))
          (fn2-digests (fn2-native-node-registry-seed fn2-digests))
          (fn2-digests (fn2-mk-node 1 0 1 fn2-digests)))
    (mv (and before-ok concrete-ok
             (fn2-native-node-registry-statep *fn2-native-node-registry-words*
               '(17 18 19 20 21 22 23 24) fn2-digests)) fn2-digests))
   answer)))

(defun fn2-native-node-registry-negative ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-digests
  (mv-let (answer fn2-digests)
   (let* ((fn2-digests (fn2-native-node-registry-seed fn2-digests))
          (before-ok (fn2-native-node-registry-statep '(9 10 11 12 13 14 15 16)
                         '(17 18 19 20 21 22 23 24) fn2-digests))
          (fn2-digests (fn2-digest-store-words 2 99 18 19 20 21 22 23 24 fn2-digests))
          (fn2-digests (fn2-digest-store-words 1 3173671463 1472550981 728831264 1781307059
                         418975159 50482707 149279093 1063045910 fn2-digests))
          (native-ok (fn2-native-node-registry-statep *fn2-native-node-registry-words*
                       '(99 18 19 20 21 22 23 24) fn2-digests))
          (native-tail (fn2-digests-row-snapshot 2 fn2-digests))
          (fn2-digests (fn2-native-node-registry-seed fn2-digests))
          (fn2-digests (fn2-mk-node 1 0 1 fn2-digests)))
    (mv (and before-ok native-ok
             (fn2-native-node-registry-statep *fn2-native-node-registry-words*
               '(17 18 19 20 21 22 23 24) fn2-digests)
             (not (equal native-tail (fn2-digests-row-snapshot 2 fn2-digests))))
        fn2-digests))
   answer)))

(assert-event (fn2-native-node-registry-positive))
(assert-event (fn2-native-node-registry-negative))

(make-event
 (value (fn2-declare '(:operation-set fn2-native-b3-boundary) nil nil nil)))

; The registered statement is generated from the actual admitted theorem,
; never a separately editable display formula. The discharge guard checks it.
(make-event
 (let ((body (getpropc 'fn2-native-mk-node-whole-effect 'theorem nil (w state))))
  (if (not body) (er soft 'native-b3-evidence "Missing native whole-effect proof.")
   (value
    `(defthm-owed fn2-native-mk-node-whole-effect
      (dst left right fn2-digests native-left native-right n0 n1 n2 n3 n4 n5 n6 n7 native-base)
      ,body
      :teeth (fn2-native-node-registry-positive fn2-native-node-registry-negative)
      :schema :g1 :claim :representation :layer :b
      :from (:operation-set fn2-native-b3-boundary)
      :boundary :native
      :sides (:concrete fn2-digest-store-words :reference fn2-mk-node)
      :shared ((:function fn2-digest-store-words))
      :contract fn2-digest-store-words-effect
      :doc "CRITICAL native extraction boundary: the actual scalar store's entire digest carrier equals FN2-MK-NODE under the explicit C/FFI input/output/protected-carrier observation assumption. This is conditional representation refinement, not proof of C, crypto security or the other native replacements.")))))

(fn2-owed-discharge fn2-native-mk-node-whole-effect fn2-native-mk-node-whole-effect)

(defconst *fn2-native-node-registry-positive-bindings*
 '((dst '1) (left '0) (right '1)
   (fn2-digests '((1 9 17) (2 10 18) (3 11 19) (4 12 20)
                 (5 13 21) (6 14 22) (7 15 23) (8 16 24) 3))
   (native-left '(1 2 3 4 5 6 7 8)) (native-right '(9 10 11 12 13 14 15 16))
   (n0 '3173671463) (n1 '1472550981) (n2 '728831264) (n3 '1781307059)
   (n4 '418975159) (n5 '50482707) (n6 '149279093) (n7 '1063045910)
   (native-base '((1 9 17) (2 10 18) (3 11 19) (4 12 20)
                 (5 13 21) (6 14 22) (7 15 23) (8 16 24) 3))))

(defconst *fn2-native-node-registry-negative-bindings*
 '((dst '1) (left '0) (right '1)
   (fn2-digests '((1 9 17) (2 10 18) (3 11 19) (4 12 20)
                 (5 13 21) (6 14 22) (7 15 23) (8 16 24) 3))
   (native-left '(1 2 3 4 5 6 7 8)) (native-right '(9 10 11 12 13 14 15 16))
   (n0 '3173671463) (n1 '1472550981) (n2 '728831264) (n3 '1781307059)
   (n4 '418975159) (n5 '50482707) (n6 '149279093) (n7 '1063045910)
   (native-base '((1 9 99) (2 10 18) (3 11 19) (4 12 20)
                 (5 13 21) (6 14 22) (7 15 23) (8 16 24) 3))))

; Keep this proven point available when another book rechecks the evidence.
; The generic assumption's soundness constraint deliberately has no rewrite rule.
(defthm fn2-native-node-registry-frame-observation-refused
 (not (fn2-a-crypto-native
       (list :fn2-b3-node '(1 2 3 4 5 6 7 8) '(9 10 11 12 13 14 15 16)
             *fn2-native-node-registry-words* *fn2-native-node-witness-digests*)
       (list :fn2-b3-node '(1 2 3 4 5 6 7 8) '(9 10 11 12 13 14 15 16)
             *fn2-native-node-registry-words*
             '((1 9 99) (2 10 18) (3 11 19) (4 12 20)
               (5 13 21) (6 14 22) (7 15 23) (8 16 24) 3))))
 :hints (("Goal" :use ((:instance fn2-a-crypto-native-correspondence
         (reference (list :fn2-b3-node '(1 2 3 4 5 6 7 8) '(9 10 11 12 13 14 15 16)
                           *fn2-native-node-registry-words* *fn2-native-node-witness-digests*))
         (native (list :fn2-b3-node '(1 2 3 4 5 6 7 8) '(9 10 11 12 13 14 15 16)
                        *fn2-native-node-registry-words*
                        '((1 9 99) (2 10 18) (3 11 19) (4 12 20)
                          (5 13 21) (6 14 22) (7 15 23) (8 16 24) 3))))))))

; Extract the actual translated hypothesis, including its CONS/LIST encoding.
; This prevents a source spelling from weakening or missing the removed premise.
(make-event
 (let* ((row (fn2-decl-row '(:square fn2-native-mk-node-whole-effect) (w state)))
        (formula (fn2-decl-statement-body (fn2-decl-get :statement row) (w state))))
  (mv-let (hyp conclusion) (fn2-evidence-parts formula)
   (declare (ignore conclusion))
   (let* ((hypotheses (fn2-evidence-hypotheses hyp))
          (removed (assoc-eq 'fn2-a-crypto-native hypotheses)))
    (if (not removed) (er soft 'native-b3-evidence "Missing live primitive assumption.")
     (value `(defsquare-evidence fn2-native-mk-node-whole-effect
              :positive ,*fn2-native-node-registry-positive-bindings*
              :negative (:kind :hypothesis-removal :remove ,removed
                         :bindings ,*fn2-native-node-registry-negative-bindings*))))))))

(fn2-assert-owed-teeth fn2-native-mk-node-whole-effect)
(fn2-assert-square-evidence fn2-native-mk-node-whole-effect)
(assert-event
 (not (fn2-assurance-row-problems 'fn2-native-mk-node-whole-effect '(fn2-mk-node) (w state))))
