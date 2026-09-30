; Operation census component; no installed runtime family or funded fixture.
(in-package "ACL2")
(include-book "../../books/index-writer-operation-demand")

(defun fn-iwd-test-builder (phase control shared)
 (declare (xargs :guard t))
 (list :index-builder phase :new :old :key 2 255 :pc :assigned
       :table-root 3 :table-id :row-root 2 :row-id :number-root
       :number-id shared control :receipt))
(defun fn-iwd-test-pending (kind phase)
 (declare (xargs :guard t))
 (list :page-reservation 0 1 0 :fresh :debt kind :new 0 :old-page phase nil nil))

; Complete selector roster, and fresh-only page registration.
(assert-event
 (equal
  (list (fn-iwd-operation-entry :generation-reserve nil nil)
        (fn-iwd-operation-entry :generation-register nil nil)
        (fn-iwd-operation-entry :page-reserve nil nil)
        (fn-iwd-operation-entry :page-register nil (fn-iwd-test-pending :rows :charged))
        (fn-iwd-operation-entry :publish nil nil))
  '(fn-igr-reserve fn-igr-register fn-ipa-reserve fn-ipa-register-fresh
    fn-ibp-writer-complete)))
(assert-event
 (equal (fn-iwd-operation-entry :page-register nil
          (update-nth 4 :recycled (fn-iwd-test-pending :rows :charged)))
        :unavailable))

(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :arena-held nil nil) nil) 'fn-ibp-writer-assignment-begin))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :assigning nil nil) nil) 'fn-ibp-writer-assignment-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :numbers nil nil) nil) 'fn-ibp-writer-number-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :row-source nil nil) nil) 'fn-ibp-writer-row-source-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :row-root nil nil) nil) 'fn-ipa-row-root-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :row-share nil nil) nil) 'fn-ipa-row-share-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-depth nil nil) nil) 'fn-ipa-table-depth-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-root nil nil) nil) 'fn-ipa-table-root-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-page-attached nil nil) nil) 'fn-ipa-table-page-advance))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-seal nil nil) nil) 'fn-ipa-table-seal-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :ready nil nil) nil) :ready))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :recovery-required nil nil) nil) :recovery-required))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :bogus nil nil) nil) :unavailable))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :layout nil nil) nil) 'fn-ibp-writer-row-source-begin))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :layout :requested nil) (fn-iwd-test-pending :rows :built)) 'fn-ipa-row-copy-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :layout :requested nil) (fn-iwd-test-pending :rows :copied)) 'fn-ipa-row-seal))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :layout :requested nil) (fn-iwd-test-pending :table :built)) 'fn-ipa-table-root-begin))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :layout :requested nil) nil) :constructor-required))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-layout nil nil) (fn-iwd-test-pending :rows :built)) 'fn-ipa-row-debt-transfer))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-layout nil :rows-shared) nil) 'fn-ipa-table-layout-begin))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-layout nil nil) nil) 'fn-ipa-row-share-begin))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-reinsert '(:table-reinsert 0 nil) nil) nil) 'fn-ipa-reinsert-begin))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-reinsert '(:table-reinsert 1 :row-directory) nil) nil) 'fn-ipa-reinsert-directory-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-reinsert '(:table-reinsert 1 :table-directory) nil) nil) 'fn-ipa-reinsert-directory-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-reinsert '(:table-reinsert 1 :row-read) nil) nil) 'fn-ipa-reinsert-row-read))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-reinsert '(:table-reinsert 1 :tag) nil) nil) 'fn-ipa-reinsert-tag))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-reinsert '(:table-reinsert 1 :place) nil) nil) 'fn-ipa-reinsert-place-one))
(assert-event (equal (fn-iwd-writer-entry (fn-iwd-test-builder :table-reinsert '(:table-reinsert 1 :bogus) nil) nil) :recovery-required))

; Positive witness for the full fixed-projection antecedent and conclusion.
(defconst *iwd-a* (fn-iwd-test-builder :layout :request nil))
(defconst *iwd-b* (update-nth 9 :different-retained-root *iwd-a*))
(defconst *iwd-p* (fn-iwd-test-pending :rows :built))
(defconst *iwd-q* (update-nth 9 :different-old-page *iwd-p*))
(assert-event
 (and (equal (fn-omk-at 1 *iwd-a*) (fn-omk-at 1 *iwd-b*))
      (equal (fn-omk-at 18 *iwd-a*) (fn-omk-at 18 *iwd-b*))
      (equal (fn-omk-at 17 *iwd-a*) (fn-omk-at 17 *iwd-b*))
      (equal (fn-omk-at 6 *iwd-p*) (fn-omk-at 6 *iwd-q*))
      (equal (fn-omk-at 10 *iwd-p*) (fn-omk-at 10 *iwd-q*))
      (equal (not *iwd-p*) (not *iwd-q*))
      (equal (fn-iwd-writer-entry *iwd-a* *iwd-p*)
             (fn-iwd-writer-entry *iwd-b* *iwd-q*))))

; Hypothesis removal 1: exact fixed projection, corrupted metadata only.
(assert-event
 (let ((a *iwd-a*) (b (update-nth 1 :ready *iwd-a*)) (p *iwd-p*) (q *iwd-q*))
  (and
   (not (equal (fn-omk-at 1 a) (fn-omk-at 1 b)))
   (equal (fn-omk-at 18 a) (fn-omk-at 18 b))
   (equal (fn-omk-at 17 a) (fn-omk-at 17 b))
   (equal (fn-omk-at 6 p) (fn-omk-at 6 q))
   (equal (fn-omk-at 10 p) (fn-omk-at 10 q))
   (equal (not p) (not q))
   (not (equal (fn-iwd-writer-entry a p) (fn-iwd-writer-entry b q))))))

; Hypothesis removal 2: exact fixed projection, corrupted metadata only.
(assert-event
 (let ((a *iwd-a*) (b (update-nth 18 nil *iwd-a*)) (p *iwd-p*) (q *iwd-q*))
  (and
   (equal (fn-omk-at 1 a) (fn-omk-at 1 b))
   (not (equal (fn-omk-at 18 a) (fn-omk-at 18 b)))
   (equal (fn-omk-at 17 a) (fn-omk-at 17 b))
   (equal (fn-omk-at 6 p) (fn-omk-at 6 q))
   (equal (fn-omk-at 10 p) (fn-omk-at 10 q))
   (equal (not p) (not q))
   (not (equal (fn-iwd-writer-entry a p) (fn-iwd-writer-entry b q))))))

; Hypothesis removal 3: exact fixed projection, corrupted metadata only.
(assert-event
 (let ((a (fn-iwd-test-builder :table-layout nil nil)) (b (fn-iwd-test-builder :table-layout nil :rows-shared)) (p nil) (q nil))
  (and
   (equal (fn-omk-at 1 a) (fn-omk-at 1 b))
   (equal (fn-omk-at 18 a) (fn-omk-at 18 b))
   (not (equal (fn-omk-at 17 a) (fn-omk-at 17 b)))
   (equal (fn-omk-at 6 p) (fn-omk-at 6 q))
   (equal (fn-omk-at 10 p) (fn-omk-at 10 q))
   (equal (not p) (not q))
   (not (equal (fn-iwd-writer-entry a p) (fn-iwd-writer-entry b q))))))

; Hypothesis removal 4: exact fixed projection, corrupted metadata only.
(assert-event
 (let ((a *iwd-a*) (b *iwd-b*) (p *iwd-p*) (q (update-nth 6 :table *iwd-p*)))
  (and
   (equal (fn-omk-at 1 a) (fn-omk-at 1 b))
   (equal (fn-omk-at 18 a) (fn-omk-at 18 b))
   (equal (fn-omk-at 17 a) (fn-omk-at 17 b))
   (not (equal (fn-omk-at 6 p) (fn-omk-at 6 q)))
   (equal (fn-omk-at 10 p) (fn-omk-at 10 q))
   (equal (not p) (not q))
   (not (equal (fn-iwd-writer-entry a p) (fn-iwd-writer-entry b q))))))

; Hypothesis removal 5: exact fixed projection, corrupted metadata only.
(assert-event
 (let ((a *iwd-a*) (b *iwd-b*) (p *iwd-p*) (q (update-nth 10 :copied *iwd-p*)))
  (and
   (equal (fn-omk-at 1 a) (fn-omk-at 1 b))
   (equal (fn-omk-at 18 a) (fn-omk-at 18 b))
   (equal (fn-omk-at 17 a) (fn-omk-at 17 b))
   (equal (fn-omk-at 6 p) (fn-omk-at 6 q))
   (not (equal (fn-omk-at 10 p) (fn-omk-at 10 q)))
   (equal (not p) (not q))
   (not (equal (fn-iwd-writer-entry a p) (fn-iwd-writer-entry b q))))))

; Hypothesis removal 6: exact fixed projection, corrupted metadata only.
(assert-event
 (let ((a (fn-iwd-test-builder :table-layout nil nil)) (b (fn-iwd-test-builder :table-layout nil nil)) (p nil) (q '(nil)))
  (and
   (equal (fn-omk-at 1 a) (fn-omk-at 1 b))
   (equal (fn-omk-at 18 a) (fn-omk-at 18 b))
   (equal (fn-omk-at 17 a) (fn-omk-at 17 b))
   (equal (fn-omk-at 6 p) (fn-omk-at 6 q))
   (equal (fn-omk-at 10 p) (fn-omk-at 10 q))
   (not (equal (not p) (not q)))
   (not (equal (fn-iwd-writer-entry a p) (fn-iwd-writer-entry b q))))))

; Whole emitted record asserts the exact tuple, retained references and absent
; installed domain. Chunk counts remain slots and do not become runtime bytes.
(assert-event
 (equal (mv-list 2 (fn-iwd-census :generation-reserve :pc nil nil 3 8))
  (list :census
   (fn-iwd-operation-make
    :generation-reserve 'fn-igr-reserve
    '(:operation-source "957dd74a4cba9c53e4a7d60124857b5fd874b6122ccb6a2520220ca33d09bf64" :generation-reserve nil)
    '((:token 4 1) (:receipt 8 1) (:builder 20 1))
    '((:table-words 2048 :u64) (:row-references 256 :retained)
      (:generation-rows 64 :retained) (:page-owner-rows 64 :retained))
    '(:callee-closure-required 3 8
      (generated-child-defaults persistent-directory-copy shared-roots
       scalar-bignum-domain caller-frame first-use collector external control))
    '(:carried-scalars nil nil nil nil nil nil nil nil nil nil)
    '(:borrowed-retained :pc nil nil nil nil nil nil nil nil)
    '(:primary :caller :first-use :collector :external :control
      :projection-control :retained-overlap :affine-lifetime :resource-components)))))
(assert-event
 (and (equal (fn-iwd-resource-contribution :generation-reserve) '(:resident-unavailable 0 0 0 1))
      (equal (fn-iwd-resource-contribution :page-reserve) '(:resident-unavailable 0 0 0 1))
      (equal (fn-iwd-resource-contribution :publish) '(:resident-unavailable 0 0 0 0))))
(assert-event
 (equal (mv-list 2 (fn-iwd-demand :census
   '(:runtime-operation-family :index-writer :runtime :image :profile :pool :source
     ((:request :heap :body 1 1)) nil nil nil nil nil :roots :cleanup)
   '((:heap :heap :body)))) '(:runtime-operation-unavailable nil)))
