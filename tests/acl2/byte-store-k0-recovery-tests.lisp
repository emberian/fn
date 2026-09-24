; Teeth for books/byte-store-k0-recovery.lisp: K0 over the recovery program.
; The witnesses are crash images of two POST cut states of the K5 fixture's
; second publication and second allocation, so the store already retains an
; acknowledged record and every image is a non-trivial one: record-linked
; (a pending transaction link, kept or lost) and frontier-replaced (a pending
; frontier rename, kept or lost -- the lost one is the K2f rollback arm).
(in-package "ACL2")
(include-book "../../books/byte-store-k0-recovery")
(include-book "byte-store-stable-prefix-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bsk0r-configs* (list *fn-cfg-default-record*))

(defun bsk0r-scan-f (image) (fn-bs-scan-frontier (fn-bs-scan-store image)))
(defun bsk0r-scan-r (image) (fn-bs-scan-records (fn-bs-scan-store image)))
(defun bsk0r-open (configs image)
  (fn-cpo-open-observed configs (bsk0r-scan-f image) (bsk0r-scan-r image)))
(defun bsk0r-host (configs image) (fn-sn-files (fn-sn-open-state (bsk0r-open configs image))))
(defun bsk0r-run (image k groups capacity)
  (fn-bs-run image k (fn-bs-recover-program) nil groups capacity))
(defun bsk0r-related-at (run k)
  (fn-bs-store-relation (car (nth k run)) (cdr (nth k run))))
; The six recovery-program cuts: recover-replayed, recover-barrier 1..5.
(defun bsk0r-cuts-related (run)
  (and (bsk0r-related-at run 1) (bsk0r-related-at run 4) (bsk0r-related-at run 7)
       (bsk0r-related-at run 10) (bsk0r-related-at run 13) (bsk0r-related-at run 16)))
(defun bsk0r-sweep (pair names)
  (fn-bs-run (car pair) (cdr pair) (fn-bs-recover-sweep-program names) nil
             *bsk5-groups* *bsk5-capacity*))

; The two POST cut states and their crash images.
(defun bsk0r-linked () (bsk5-linked-2))
(defun bsk0r-replaced ()
  (let ((pair (bsk5-finished)))
    (nth 9 (fn-bs-run (car pair) (cdr pair)
                      (fn-bs-frontier-program ".allocation-k5-2" (fn-bs-frontier-encode 2))
                      nil *bsk5-groups* *bsk5-capacity*))))
(defun bsk0r-keep-choices (pair)
  (fn-bs-view-choices (fn-bs-pending (car pair)) (fn-bs-unit (car pair))))
(defun bsk0r-keep (pair) (fn-bs-crash (car pair) (bsk0r-keep-choices pair)))
(defun bsk0r-lose (pair) (fn-bs-crash (car pair) nil))

(defun bsk0r-witness-okp (pair image)
  (let* ((entry (fn-bs-recovery-entry-kernel image))
         (seed-run (bsk0r-run image entry *bsk5-groups* *bsk5-capacity*))
         (host (bsk0r-host *bsk0r-configs* image))
         (host-run (bsk0r-run image host *bsk5-groups* *bsk5-capacity*)))
    (and (fn-bs-store-relation (car pair) (cdr pair))
         (fn-bs-store-relation image entry)
         (fn-sf-history-recoverablep *bsk5-groups* *bsk5-capacity*
                                     (bsk0r-scan-r image) (bsk0r-scan-f image))
         (equal (len seed-run) 17) (bsk0r-cuts-related seed-run)
         (fn-bs-run-relatedp seed-run)
         (equal (fn-sf-phase (cdr (nth 16 seed-run))) :ready)
         (fn-sn-open-okp (bsk0r-open *bsk0r-configs* image))
         (equal host (fn-bs-recovered-kernel (bsk0r-scan-f image) (bsk0r-scan-r image) 0))
         (fn-bs-store-relation image host)
         (equal (len host-run) 17) (bsk0r-cuts-related host-run)
         (equal (car (nth 16 host-run)) image)
         (equal (fn-sf-phase (cdr (nth 16 host-run))) :ready))))

; Reachable witnesses: every hypothesis holds, the images are crash images
; (legal choices), and every recovery cut is related, from the model's
; scanned entry and from the host's reopened kernel.
(assert-event
 (and (fn-bs-crash-choicesp (bsk0r-keep-choices (bsk0r-linked))
                            (fn-bs-pending (car (bsk0r-linked)))
                            (fn-bs-unit (car (bsk0r-linked))))
      (fn-bs-crash-choicesp (bsk0r-keep-choices (bsk0r-replaced))
                            (fn-bs-pending (car (bsk0r-replaced)))
                            (fn-bs-unit (car (bsk0r-replaced))))
      (consp (fn-bs-ops-for-dir (fn-bs-pending (car (bsk0r-linked))) :transactions))
      (consp (fn-bs-ops-for-dir (fn-bs-pending (car (bsk0r-replaced))) :root))))
(assert-event (bsk0r-witness-okp (bsk0r-linked) (bsk0r-keep (bsk0r-linked))))
(assert-event (bsk0r-witness-okp (bsk0r-linked) (bsk0r-lose (bsk0r-linked))))
(assert-event (bsk0r-witness-okp (bsk0r-replaced) (bsk0r-keep (bsk0r-replaced))))
(assert-event (bsk0r-witness-okp (bsk0r-replaced) (bsk0r-lose (bsk0r-replaced))))
; The images differ: two records or one; frontier 2 or the rolled-back 1.
(assert-event
 (and (equal (len (bsk0r-scan-r (bsk0r-keep (bsk0r-linked)))) 2)
      (equal (len (bsk0r-scan-r (bsk0r-lose (bsk0r-linked)))) 1)
      (equal (bsk0r-scan-f (bsk0r-keep (bsk0r-replaced))) 2)
      (equal (bsk0r-scan-f (bsk0r-lose (bsk0r-replaced))) 1)))

; recovery-stage-unlinked: the sweep of the staging orphan the linked cut
; left, from the last pair of the host's run; its cut pair is related.
(defun bsk0r-sweep-run ()
  (let ((image (bsk0r-keep (bsk0r-linked))))
    (bsk0r-sweep (nth 16 (bsk0r-run image (bsk0r-host *bsk0r-configs* image)
                                    *bsk5-groups* *bsk5-capacity*))
                 (list ".stage-k5-2"))))
(assert-event
 (let ((run (bsk0r-sweep-run)))
   (and (fn-bs-lookup (bsk0r-keep (bsk0r-linked)) :staging ".stage-k5-2")
        (equal (len run) 2)
        (not (fn-bs-lookup (car (nth 1 run)) :staging ".stage-k5-2"))
        (bsk0r-related-at run 1))))

; ---------------------------------------------------------------------------
; Drop the relation.  The empty byte store is its own crash image and no
; kernel is related to it; its scan faults and so does its entry.
(assert-event
 (and (equal (fn-bs-crash *fn-bs-empty-store* nil) *fn-bs-empty-store*)
      (not (fn-bs-store-relation *fn-bs-empty-store* (fn-sf-initial-state)))))
(must-fail
 (assert-event
  (fn-bs-store-relation *fn-bs-empty-store*
                        (fn-bs-recovery-entry-kernel *fn-bs-empty-store*))))
(must-fail
 (assert-event
  (bsk0r-cuts-related (bsk0r-run *fn-bs-empty-store*
                                 (fn-bs-recovery-entry-kernel *fn-bs-empty-store*)
                                 *bsk5-groups* *bsk5-capacity*))))

; Drop the crash-image premise.  A store whose first transaction is torn:
; the related state holds that inode durable and fenced, so no crash of it
; can change those octets.
(defun bsk0r-torn ()
  (let* ((image (bsk0r-keep (bsk0r-linked)))
         (ino (fn-bs-lookup image :transactions (fn-bs-txn-name 0))))
    (fn-bs-make (fn-bs-unit image)
                (put-assoc-equal ino '(1 2 3) (fn-bs-inodes image))
                (fn-bs-dirs image) nil (fn-bs-next-ino image))))
(assert-event
 (let* ((bs (car (bsk0r-linked)))
        (ino (fn-bs-durable-entry bs :transactions (fn-bs-txn-name 0))))
   (and (fn-bs-store-relation bs (cdr (bsk0r-linked)))
        (fn-bs-fencedp bs ino)
        (equal (fn-bs-lookup (bsk0r-torn) :transactions (fn-bs-txn-name 0)) ino)
        (not (equal (fn-bs-content (bsk0r-torn) ino) (fn-bs-durable-content bs ino))))))
(must-fail
 (assert-event
  (fn-bs-store-relation (bsk0r-torn) (fn-bs-recovery-entry-kernel (bsk0r-torn)))))

; Drop recoverability (the model's entry).  With no groups the scanned
; history does not replay and (:recover) lands in :fault, so the program never
; reaches :ready.  The pairs themselves stay related: :fault is outside both
; windows, where the relation fixes only the frontier and the records, which
; the fault keeps.  The host faults here and never reaches the cut.
(assert-event
 (not (fn-sf-history-recoverablep nil *bsk5-capacity*
                                  (bsk0r-scan-r (bsk0r-keep (bsk0r-linked)))
                                  (bsk0r-scan-f (bsk0r-keep (bsk0r-linked))))))
(assert-event
 (let* ((image (bsk0r-keep (bsk0r-linked)))
        (run (bsk0r-run image (fn-bs-recovery-entry-kernel image) nil *bsk5-capacity*)))
   (and (fn-bs-run-relatedp run)
        (equal (fn-sf-phase (cdr (nth 16 run))) :fault))))
(must-fail
 (assert-event
  (let* ((image (bsk0r-keep (bsk0r-linked)))
         (run (bsk0r-run image (fn-bs-recovery-entry-kernel image) nil *bsk5-capacity*)))
    (and (fn-bs-run-relatedp run)
         (equal (fn-sf-phase (cdr (nth 16 run))) :ready)))))

; Drop the host's open success.  With no configuration history the open
; refuses, and its "kernel" is not related to the image.
(assert-event
 (not (fn-sn-open-okp (bsk0r-open nil (bsk0r-keep (bsk0r-linked))))))
(must-fail
 (assert-event
  (let ((image (bsk0r-keep (bsk0r-linked))))
    (fn-bs-store-relation image (bsk0r-host nil image)))))
(must-fail
 (assert-event
  (let ((image (bsk0r-keep (bsk0r-linked))))
    (bsk0r-cuts-related (bsk0r-run image (bsk0r-host nil image)
                                   *bsk5-groups* *bsk5-capacity*)))))

; ---------------------------------------------------------------------------
; The link error arm.  Start: the second record, staged.
(defun bsk0r-l-start () (bsk5-frontier-2))
(defun bsk0r-l-prepared ()
  (fn-sf-prepare-record (cdr (bsk0r-l-start)) *bsk5-record-2*
                        *bsk5-groups* *bsk5-capacity*))
(defun bsk0r-l-arm (bs ks frame outcome)
  (let ((p6 (nth 6 (fn-bs-run bs ks (fn-bs-record-program ".stage-k5-2" (fn-bs-txn-name 1) frame)
                              nil *bsk5-groups* *bsk5-capacity*))))
    (mv-let (r bs7)
      (fn-bs-link (car p6) :staging ".stage-k5-2" :transactions (fn-bs-txn-name 1) outcome)
      (declare (ignore r))
      (fn-bs-store-relation bs7 (fn-sf-record-link-result (cdr p6) :error)))))
; Witness: an issued link that reported EIO (the pending link is in the
; byte state), and one refused before issue (it is not).
(assert-event
 (let ((bs (car (bsk0r-l-start))) (ks (bsk0r-l-prepared)))
   (and (fn-bs-store-relation bs ks)
        (fn-bs-record-inputp ks ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))
        (not (fn-bs-lookup bs :staging ".stage-k5-2"))
        (bsk0r-l-arm bs ks (bsk5-frame-2) '(:eio . :issued))
        (bsk0r-l-arm bs ks (bsk5-frame-2) '(:eio . 0)))))
; Drop the relation: the retained-record kernel over the initial image.
(must-fail
 (assert-event (bsk0r-l-arm (bsk5-initial) (bsk0r-l-prepared) (bsk5-frame-2) '(:eio . :issued))))
; Drop the input contract: the first record's frame for the second record.
(assert-event
 (not (fn-bs-record-inputp (bsk0r-l-prepared) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame))))
(must-fail
 (assert-event (bsk0r-l-arm (car (bsk0r-l-start)) (bsk0r-l-prepared) (bsk5-frame) '(:eio . :issued))))
; Drop the absent stage: O_EXCL fails, the run stops before pair 6.
(defun bsk0r-l-occupied ()
  (let ((bs (car (bsk0r-l-start))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs)
                (put-assoc-equal :staging
                                 (cons (cons ".stage-k5-2" 0)
                                       (cdr (assoc-equal :staging (fn-bs-dirs bs))))
                                 (fn-bs-dirs bs))
                (fn-bs-pending bs) (fn-bs-next-ino bs))))
(assert-event (fn-bs-lookup (bsk0r-l-occupied) :staging ".stage-k5-2"))
(must-fail
 (assert-event (bsk0r-l-arm (bsk0r-l-occupied) (bsk0r-l-prepared) (bsk5-frame-2) '(:eio . :issued))))
