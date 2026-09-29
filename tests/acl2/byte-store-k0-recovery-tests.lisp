; Teeth for books/byte-store-k0-recovery.lisp: K0 over the recovery program.
; The witnesses are crash images of two POST cut states of the K5 fixture's
; second publication and second allocation, so the store already retains an
; acknowledged record and every image is a non-trivial one: record-linked
; (a pending transaction link, kept or lost) and frontier-replaced (a pending
; frontier rename, kept or lost -- the lost one is the K2f rollback arm).
(in-package "ACL2")
(include-book "../../books/byte-store-k0-recovery")
(include-book "byte-store-stable-prefix-tests")
(include-book "must-fail-checked")

(defconst *bsk0r-configs* (list *fn-cfg-default-record*))

(defun bsk0r-scan-f (image) (fn-bs-scan-frontier (fn-bs-scan-store image)))
;; The records flip: the scan reads wire events; the recover entry interns them
;; into rows (here the fixture's rows over *bsk5-arena*), and the kernel and the
;; host's open run over the rows.
(defun bsk0r-scan-w (image) (fn-bs-scan-records (fn-bs-scan-store image)))
(defun bsk0r-row-of (w)
  (cond ((equal w *bsk5-record*) *bsk5-row*)
        ((equal w *bsk5-record-2*) *bsk5-row-2*)
        (t w)))
(defun bsk0r-rows-of (ws)
  (if (atom ws) nil (cons (bsk0r-row-of (car ws)) (bsk0r-rows-of (cdr ws)))))
(defun bsk0r-scan-r (image) (bsk0r-rows-of (bsk0r-scan-w image)))
(defun bsk0r-open (configs image)
  (fn-cpo-open-observed configs (bsk0r-scan-f image) (bsk0r-scan-r image)))
(defun bsk0r-host (configs image) (fn-sn-files (fn-sn-open-state (bsk0r-open configs image))))
(defun bsk0r-run (image k groups capacity)
  (fn-bs-run image k (fn-bs-recover-program) nil groups capacity))
(defun bsk0r-related-at (run k)
  (fn-bs-store-relation (car (nth k run)) (cdr (nth k run)) *bsk5-arena*))
; The four recovery-program cuts: recover-replayed, recover-barrier 1..3.
(defun bsk0r-cuts-related (run)
  (and (bsk0r-related-at run 1) (bsk0r-related-at run 4) (bsk0r-related-at run 7)
       (bsk0r-related-at run 10)))
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
  (let* ((entry (fn-bs-recovery-entry-kernel image (bsk0r-scan-r image)))
         (seed-run (bsk0r-run image entry *bsk5-groups* *bsk5-capacity*))
         (host (bsk0r-host *bsk0r-configs* image))
         (host-run (bsk0r-run image host *bsk5-groups* *bsk5-capacity*)))
    (and (fn-bs-store-relation (car pair) (cdr pair) *bsk5-arena*)
         (fn-bs-recovered-rowsp image (bsk0r-scan-r image) *bsk5-arena*)
         (fn-bs-store-relation image entry *bsk5-arena*)
         (fn-sf-history-recoverablep *bsk5-groups* *bsk5-capacity*
                                     (bsk0r-scan-r image) (bsk0r-scan-f image))
         (equal (len seed-run) 11) (bsk0r-cuts-related seed-run)
         (fn-bs-run-relatedp seed-run *bsk5-arena*)
         (equal (fn-sf-phase (cdr (nth 10 seed-run))) :ready)
         (fn-sn-open-okp (bsk0r-open *bsk0r-configs* image))
         (equal host (fn-bs-recovered-kernel (bsk0r-scan-f image) (bsk0r-scan-r image) 0))
         (fn-bs-store-relation image host *bsk5-arena*)
         (equal (len host-run) 11) (bsk0r-cuts-related host-run)
         (equal (car (nth 10 host-run)) image)
         (equal (fn-sf-phase (cdr (nth 10 host-run))) :ready))))

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

;;; KEYSTONE fn-bs-crash-image-reads-the-config (PRF-041, row B48 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Every crash image of a related store names and holds the durable config.
;;; KEYSTONE fn-bs-crash-image-frontier-decodes-to-a-natural (PRF-041, row B49 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Every crash image's root frontier decodes to a natural.
;;; KEYSTONE fn-bs-crash-image-namespace-is-contiguous (PRF-041, row B50 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Every crash image's transaction names are the contiguous txn-names prefix.
;;; KEYSTONE fn-bs-crash-image-records-do-not-fault (PRF-041, row B51 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Reading every crash image's transaction records does not fault.
;;; KEYSTONE fn-bs-store-crash-image-scans (PRF-041, row B52 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Every crash image of a related store scans.
;;; KEYSTONE fn-bs-store-crash-image-is-kernel-admissible (PRF-041, row B53 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Every crash image's scan is a recovery crash image of the related kernel.
; The shared antecedent: the pair is related (asserted in bsk0r-k1-okp) and
; each image is a crash image of its byte state (the four ground theorems;
; bsk0r-keep-linked-is-a-crash-image is the first).  Every image holds an
; article: a non-empty namespace, record list and scan.
(defthm bsk0r-keep-linked-is-a-crash-image
  (fn-bs-crash-imagep (car (bsk0r-linked)) (bsk0r-keep (bsk0r-linked)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-crash-imagep)
           :use ((:instance fn-bs-crash-imagep-suff
                            (s (car (bsk0r-linked)))
                            (choices (bsk0r-keep-choices (bsk0r-linked)))
                            (image (bsk0r-keep (bsk0r-linked))))))))
(defthm bsk0r-lose-linked-is-a-crash-image
  (fn-bs-crash-imagep (car (bsk0r-linked)) (bsk0r-lose (bsk0r-linked)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-crash-imagep)
           :use ((:instance fn-bs-crash-imagep-suff
                            (s (car (bsk0r-linked))) (choices nil)
                            (image (bsk0r-lose (bsk0r-linked))))))))
(defthm bsk0r-keep-replaced-is-a-crash-image
  (fn-bs-crash-imagep (car (bsk0r-replaced)) (bsk0r-keep (bsk0r-replaced)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-crash-imagep)
           :use ((:instance fn-bs-crash-imagep-suff
                            (s (car (bsk0r-replaced)))
                            (choices (bsk0r-keep-choices (bsk0r-replaced)))
                            (image (bsk0r-keep (bsk0r-replaced))))))))
(defthm bsk0r-lose-replaced-is-a-crash-image
  (fn-bs-crash-imagep (car (bsk0r-replaced)) (bsk0r-lose (bsk0r-replaced)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-crash-imagep)
           :use ((:instance fn-bs-crash-imagep-suff
                            (s (car (bsk0r-replaced))) (choices nil)
                            (image (bsk0r-lose (bsk0r-replaced))))))))
(defun bsk0r-k1-okp (pair image)
  (let* ((bs (car pair))
         (names (fn-bs-names image :transactions))
         (cfg (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
         (scan (fn-bs-scan-store image)))
    (and (fn-bs-store-relation bs (cdr pair) *bsk5-arena*)
         cfg
         (equal (fn-bs-lookup image :root *fn-bs-scan-config-name*) cfg)
         (consp (fn-bs-durable-content bs cfg))
         (equal (fn-bs-content image (fn-bs-lookup image :root *fn-bs-scan-config-name*))
                (fn-bs-durable-content bs cfg))
         (natp (fn-bs-frontier-decode
                (fn-bs-content image (fn-bs-lookup image :root *fn-bs-scan-frontier-name*))))
         (consp names)
         (equal names (fn-bs-txn-names (len names)))
         (consp (fn-bs-read-records image 0 (len names)))
         (not (equal (fn-bs-read-records image 0 (len names)) :fault))
         (fn-bs-scan-okp scan)
         (consp (fn-bs-scan-records scan))
         (fn-bs-alpha-recovery-crash-imagep (cdr pair) (fn-bs-scan-frontier scan)
                                            (fn-bs-scan-records scan) *bsk5-arena*))))
(assert-event
 (and (bsk0r-k1-okp (bsk0r-linked) (bsk0r-keep (bsk0r-linked)))
      (bsk0r-k1-okp (bsk0r-linked) (bsk0r-lose (bsk0r-linked)))
      (bsk0r-k1-okp (bsk0r-replaced) (bsk0r-keep (bsk0r-replaced)))
      (bsk0r-k1-okp (bsk0r-replaced) (bsk0r-lose (bsk0r-replaced)))))

;;; KEYSTONE fn-bs-quiet-scanned-store-is-related-to-every-recovered-kernel (PRF-041, row B21 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; A quiet image that scans is related to the recovered kernel at every barrier n = 0..3.
(defun bsk0r-quiet-okp (image)
  (let* ((f (bsk0r-scan-f image)) (rows (bsk0r-scan-r image)))
    (and (fn-bs-statep image)
         (equal (fn-bs-pending image) nil)
         (fn-bs-scan-okp (fn-bs-scan-store image))
         (fn-bs-authority-knownp image)
         (fn-record-uint32p f)
         (consp rows)
         (fn-sf-record-listp rows 0 0 f)
         (equal (fn-bs-rows-wire rows *bsk5-arena*) (bsk0r-scan-w image))
         (equal *fn-sf-recovery-barrier-count* 3)
         (fn-bs-store-relation image (fn-bs-recovered-kernel f rows 0) *bsk5-arena*)
         (fn-bs-store-relation image (fn-bs-recovered-kernel f rows 1) *bsk5-arena*)
         (fn-bs-store-relation image (fn-bs-recovered-kernel f rows 2) *bsk5-arena*)
         (fn-bs-store-relation image (fn-bs-recovered-kernel f rows 3) *bsk5-arena*))))
(assert-event
 (and (bsk0r-quiet-okp (bsk0r-keep (bsk0r-linked)))
      (bsk0r-quiet-okp (bsk0r-lose (bsk0r-linked)))
      (bsk0r-quiet-okp (bsk0r-keep (bsk0r-replaced)))
      (bsk0r-quiet-okp (bsk0r-lose (bsk0r-replaced)))))
;;; KEYSTONE fn-bs-recover-program-keeps-relation-at-every-cut (PRF-041, row B22 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; From the entry kernel, whose (:recover) dispatch is the recovered kernel at 0, the run is related and ends at barrier 3.
(defun bsk0r-recover-cut-okp (pair image)
  (let* ((f (bsk0r-scan-f image)) (rows (bsk0r-scan-r image))
         (k (fn-bs-recovery-entry-kernel image rows))
         (run (bsk0r-run image k *bsk5-groups* *bsk5-capacity*)))
    (and (fn-bs-store-relation (car pair) (cdr pair) *bsk5-arena*)
         (fn-bs-recovered-rowsp image rows *bsk5-arena*)
         (consp rows)
         (equal (fn-sf-dispatch k '(:recover) *bsk5-groups* *bsk5-capacity*)
                (fn-bs-recovered-kernel f rows 0))
         (fn-bs-run-relatedp run *bsk5-arena*)
         (equal (len run) 11)
         (equal (car (nth 10 run)) image)
         (equal (cdr (nth 10 run))
                (fn-bs-recovered-kernel f rows *fn-sf-recovery-barrier-count*)))))
(assert-event
 (and (bsk0r-recover-cut-okp (bsk0r-linked) (bsk0r-keep (bsk0r-linked)))
      (bsk0r-recover-cut-okp (bsk0r-linked) (bsk0r-lose (bsk0r-linked)))
      (bsk0r-recover-cut-okp (bsk0r-replaced) (bsk0r-keep (bsk0r-replaced)))
      (bsk0r-recover-cut-okp (bsk0r-replaced) (bsk0r-lose (bsk0r-replaced)))))

; recovery-stage-unlinked: the sweep of the staging orphan the linked cut
; left, from the last pair of the host's run; its cut pair is related.
(defun bsk0r-sweep-run ()
  (let ((image (bsk0r-keep (bsk0r-linked))))
    (bsk0r-sweep (nth 10 (bsk0r-run image (bsk0r-host *bsk0r-configs* image)
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
      (not (fn-bs-store-relation *fn-bs-empty-store* (fn-sf-initial-state) *bsk5-arena*))))
(must-fail-checked
 (assert-event
  (fn-bs-store-relation *fn-bs-empty-store*
                        (fn-bs-recovery-entry-kernel *fn-bs-empty-store* nil) *bsk5-arena*)))
(must-fail-checked
 (assert-event
  (bsk0r-cuts-related (bsk0r-run *fn-bs-empty-store*
                                 (fn-bs-recovery-entry-kernel *fn-bs-empty-store* nil)
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
   (and (fn-bs-store-relation bs (cdr (bsk0r-linked)) *bsk5-arena*)
        (fn-bs-fencedp bs ino)
        (equal (fn-bs-lookup (bsk0r-torn) :transactions (fn-bs-txn-name 0)) ino)
        (not (equal (fn-bs-content (bsk0r-torn) ino) (fn-bs-durable-content bs ino))))))
(must-fail-checked
 (assert-event
  (fn-bs-store-relation (bsk0r-torn) (fn-bs-recovery-entry-kernel (bsk0r-torn) (bsk0r-scan-r (bsk0r-torn))) *bsk5-arena*)))

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
        (run (bsk0r-run image (fn-bs-recovery-entry-kernel image (bsk0r-scan-r image)) nil *bsk5-capacity*)))
   (and (fn-bs-run-relatedp run *bsk5-arena*)
        (equal (fn-sf-phase (cdr (nth 10 run))) :fault))))
(must-fail-checked
 (assert-event
  (let* ((image (bsk0r-keep (bsk0r-linked)))
         (run (bsk0r-run image (fn-bs-recovery-entry-kernel image (bsk0r-scan-r image)) nil *bsk5-capacity*)))
    (and (fn-bs-run-relatedp run *bsk5-arena*)
         (equal (fn-sf-phase (cdr (nth 10 run))) :ready)))))

; Drop the host's open success.  With no configuration history the open
; refuses, and its "kernel" is not related to the image.
(assert-event
 (not (fn-sn-open-okp (bsk0r-open nil (bsk0r-keep (bsk0r-linked))))))
(must-fail-checked
 (assert-event
  (let ((image (bsk0r-keep (bsk0r-linked))))
    (fn-bs-store-relation image (bsk0r-host nil image) *bsk5-arena*))))
(must-fail-checked
 (assert-event
  (let ((image (bsk0r-keep (bsk0r-linked))))
    (bsk0r-cuts-related (bsk0r-run image (bsk0r-host nil image)
                                   *bsk5-groups* *bsk5-capacity*)))))

; ---------------------------------------------------------------------------
; The link error arm.  Start: the second record, staged.
(defun bsk0r-l-start () (bsk5-frontier-2))
(defun bsk0r-l-prepared ()
  (fn-sf-prepare-record (cdr (bsk0r-l-start)) *bsk5-row-2*
                        *bsk5-groups* *bsk5-capacity*))
(defun bsk0r-l-arm (bs ks frame outcome)
  (let ((p6 (nth 6 (fn-bs-run bs ks (fn-bs-record-program ".stage-k5-2" (fn-bs-txn-name 1) frame)
                              nil *bsk5-groups* *bsk5-capacity*))))
    (mv-let (r bs7)
      (fn-bs-link (car p6) :staging ".stage-k5-2" :transactions (fn-bs-txn-name 1) outcome)
      (declare (ignore r))
      (fn-bs-store-relation bs7 (fn-sf-record-link-result (cdr p6) :error) *bsk5-arena*))))
; Witness: an issued link that reported EIO (the pending link is in the
; byte state), and one refused before issue (it is not).
(assert-event
 (let ((bs (car (bsk0r-l-start))) (ks (bsk0r-l-prepared)))
   (and (fn-bs-store-relation bs ks *bsk5-arena*)
        (fn-bs-record-inputp ks ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2) *bsk5-arena*)
        (not (fn-bs-lookup bs :staging ".stage-k5-2"))
        (bsk0r-l-arm bs ks (bsk5-frame-2) '(:eio . :issued))
        (bsk0r-l-arm bs ks (bsk5-frame-2) '(:eio . 0)))))
; Drop the relation: the retained-record kernel over the initial image.
(must-fail-checked
 (assert-event (bsk0r-l-arm (bsk5-initial) (bsk0r-l-prepared) (bsk5-frame-2) '(:eio . :issued))))
; Drop the input contract: the first record's frame for the second record.
(assert-event
 (not (fn-bs-record-inputp (bsk0r-l-prepared) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame) *bsk5-arena*)))
(must-fail-checked
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
(must-fail-checked
 (assert-event (bsk0r-l-arm (bsk0r-l-occupied) (bsk0r-l-prepared) (bsk5-frame-2) '(:eio . :issued))))
