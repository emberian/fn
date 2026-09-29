; Teeth for the K0 cut-coordinate keystones (books/byte-store-k0.lisp).
; The witnesses are the SECOND frontier, record and finish programs of the
; K5 fixture, so the Store already retains one acknowledged record: the
; related state is not the empty initial image.
(in-package "ACL2")
(include-book "../../books/byte-store-k0-staging")
(include-book "byte-store-stable-prefix-tests")
(include-book "must-fail-checked")

(defun bsk0-related-at (run k)
  (fn-bs-store-relation (car (nth k run)) (cdr (nth k run)) *bsk5-arena*))

; ---------------------------------------------------------------------------
; P-FRONTIER.  Start: the :ready pair after the first finish.
(defun bsk0-f-start () (bsk5-finished))
(defun bsk0-f-run (bs ks stage octets)
  (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
             nil *bsk5-groups* *bsk5-capacity*))
(defun bsk0-f-good ()
  (bsk0-f-run (car (bsk0-f-start)) (cdr (bsk0-f-start))
              ".allocation-k0" (fn-bs-frontier-encode 2)))

; Reachable witness: every hypothesis holds and every proved cut is related.
(assert-event
 (let ((bs (car (bsk0-f-start))) (ks (cdr (bsk0-f-start))) (run (bsk0-f-good)))
   (and (fn-bs-store-relation bs ks *bsk5-arena*)
        (consp (fn-sf-records ks))
        (fn-bs-frontier-inputp ks ".allocation-k0" (fn-bs-frontier-encode 2))
        (not (fn-bs-lookup bs :staging ".allocation-k0"))
        (equal (len run) 16)
        (bsk0-related-at run 7) (bsk0-related-at run 13) (bsk0-related-at run 15)
        ;; the cuts not claimed by this book are related on this witness too;
        ;; that is a test, not a theorem.
        (bsk0-related-at run 2) (bsk0-related-at run 4)
        (bsk0-related-at run 9) (bsk0-related-at run 11))))

; Drop the relation: a kernel that retains one record over the initial byte
; image with none.  Input and staging premises still hold.
(assert-event
 (let ((ks (cdr (bsk0-f-start))))
   (and (not (fn-bs-store-relation (bsk5-initial) ks *bsk5-arena*))
        (fn-bs-frontier-inputp ks ".allocation-k0" (fn-bs-frontier-encode 2))
        (not (fn-bs-lookup (bsk5-initial) :staging ".allocation-k0")))))
(must-fail-checked
 (assert-event
  (bsk0-related-at (bsk0-f-run (bsk5-initial) (cdr (bsk0-f-start))
                               ".allocation-k0" (fn-bs-frontier-encode 2))
                   15)))

; Drop the input contract: recycle the old frontier bytes (the counterexample
; to unqualified K0, crash-model-v2 K0 row).  The process still reaches
; :reserved, and the reserved cut is not related.
(assert-event
 (not (fn-bs-frontier-inputp (cdr (bsk0-f-start)) ".allocation-k0"
                             (fn-bs-frontier-encode 1))))
(must-fail-checked
 (assert-event
  (bsk0-related-at (bsk0-f-run (car (bsk0-f-start)) (cdr (bsk0-f-start))
                               ".allocation-k0" (fn-bs-frontier-encode 1))
                   15)))

; Drop the absent-stage premise: O_EXCL fails, the run stops at its first
; syscall, and no reserved cut exists.
(defun bsk0-f-occupied ()
  (let ((bs (car (bsk0-f-start))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs)
                (put-assoc-equal :staging
                                 (cons (cons ".allocation-k0" 0)
                                       (cdr (assoc-equal :staging (fn-bs-dirs bs))))
                                 (fn-bs-dirs bs))
                (fn-bs-pending bs) (fn-bs-next-ino bs))))
(assert-event (fn-bs-lookup (bsk0-f-occupied) :staging ".allocation-k0"))
(must-fail-checked
 (assert-event
  (bsk0-related-at (bsk0-f-run (bsk0-f-occupied) (cdr (bsk0-f-start))
                               ".allocation-k0" (fn-bs-frontier-encode 2))
                   15)))

; ---------------------------------------------------------------------------
; P-RECORD.  bsk5-record-2-run is the second publication.
(defun bsk0-r-start () (bsk5-frontier-2))
(defun bsk0-r-prepared ()
  (fn-sf-prepare-record (cdr (bsk0-r-start)) *bsk5-row-2*
                        *bsk5-groups* *bsk5-capacity*))
(defun bsk0-r-run (bs ks stage name frame)
  (fn-bs-run bs ks (fn-bs-record-program stage name frame)
             nil *bsk5-groups* *bsk5-capacity*))

(assert-event
 (let ((bs (car (bsk0-r-start))) (ks (bsk0-r-prepared)) (run (bsk5-record-2-run)))
   (and (fn-bs-store-relation bs ks *bsk5-arena*)
        (fn-bs-record-inputp ks ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2) *bsk5-arena*)
        (not (fn-bs-lookup bs :staging ".stage-k5-2"))
        (equal (len run) 19)
        (bsk0-related-at run 6) (bsk0-related-at run 8) (bsk0-related-at run 10)
        (bsk0-related-at run 12) (bsk0-related-at run 14)
        (equal (fn-sf-phase (cdr (nth 14 run))) :completing)
        (bsk0-related-at run 1) (bsk0-related-at run 3)
        (bsk0-related-at run 16) (bsk0-related-at run 18))))

; Drop the relation: the prepared kernel over the initial byte image.
(assert-event
 (and (not (fn-bs-store-relation (bsk5-initial) (bsk0-r-prepared) *bsk5-arena*))
      (fn-bs-record-inputp (bsk0-r-prepared) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2) *bsk5-arena*)))
(must-fail-checked
 (assert-event
  (bsk0-related-at (bsk0-r-run (bsk5-initial) (bsk0-r-prepared)
                               ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))
                   14)))

; Drop the input contract: publish the FIRST record's frame under the second
; name.  The link lands, but its target does not decode to the candidate.
(assert-event
 (not (fn-bs-record-inputp (bsk0-r-prepared) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame) *bsk5-arena*)))
(must-fail-checked
 (assert-event
  (bsk0-related-at (bsk0-r-run (car (bsk0-r-start)) (bsk0-r-prepared)
                               ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame))
                   14)))

; Drop the absent-stage premise.
(defun bsk0-r-occupied ()
  (let ((bs (car (bsk0-r-start))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs)
                (put-assoc-equal :staging
                                 (cons (cons ".stage-k5-2" 0)
                                       (cdr (assoc-equal :staging (fn-bs-dirs bs))))
                                 (fn-bs-dirs bs))
                (fn-bs-pending bs) (fn-bs-next-ino bs))))
(must-fail-checked
 (assert-event
  (bsk0-related-at (bsk0-r-run (bsk0-r-occupied) (bsk0-r-prepared)
                               ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))
                   14)))

; ---------------------------------------------------------------------------
; P-FINISH, from the completing pair of the second publication.
(defun bsk0-fin-run (bs ks)
  (fn-bs-run bs ks (fn-bs-finish-program 1 1) nil *bsk5-groups* *bsk5-capacity*))
(assert-event
 (let* ((pair (car (last (bsk5-record-2-run))))
        (run (bsk0-fin-run (car pair) (cdr pair))))
   (and (fn-bs-store-relation (car pair) (cdr pair) *bsk5-arena*)
        (fn-bs-finish-inputp (cdr pair) 1 1)
        (fn-bs-run-relatedp run *bsk5-arena*)
        (equal (fn-sf-phase (cdr (nth 3 run))) :ready)
        (equal (len (fn-sf-successes (cdr (nth 3 run)))) 2))))
; Drop the relation: the completing kernel over the pre-publication bytes.
(must-fail-checked
 (assert-event
  (let ((pair (car (last (bsk5-record-2-run)))))
    (fn-bs-run-relatedp (bsk0-fin-run (car (bsk0-r-start)) (cdr pair)) *bsk5-arena*))))
; The completion claim needs its input: a wrong txid leaves the kernel
; :completing.
(must-fail-checked
 (assert-event
  (let ((pair (car (last (bsk5-record-2-run)))))
    (equal (fn-sf-phase (cdr (nth 3 (fn-bs-run (car pair) (cdr pair)
                                               (fn-bs-finish-program 1 7) nil
                                               *bsk5-groups* *bsk5-capacity*))))
           :ready))))

; ---------------------------------------------------------------------------
; Lane p10-k0-b: the staging-only cuts, frontier-replaced/-attempted, and the
; error arms are now theorems.  The witnesses above already evaluate every
; one of those cuts on the retained-history fixture; below, one must-fail
; per hypothesis per newly covered cut.
(defmacro bsk0-unrelated-at (run k)
  `(must-fail-checked (assert-event (bsk0-related-at ,run ,k))))
(defun bsk0-f-bad-relation ()
  (bsk0-f-run (bsk5-initial) (cdr (bsk0-f-start)) ".allocation-k0" (fn-bs-frontier-encode 2)))
(defun bsk0-f-bad-stage ()
  (bsk0-f-run (car (bsk0-f-start)) (cdr (bsk0-f-start)) 'not-a-name (fn-bs-frontier-encode 2)))
(defun bsk0-f-bad-octets ()
  (bsk0-f-run (car (bsk0-f-start)) (cdr (bsk0-f-start)) ".allocation-k0" '(256)))
(defun bsk0-f-recycled ()
  (bsk0-f-run (car (bsk0-f-start)) (cdr (bsk0-f-start)) ".allocation-k0" (fn-bs-frontier-encode 1)))
(defun bsk0-f-bad-absent ()
  (bsk0-f-run (bsk0-f-occupied) (cdr (bsk0-f-start)) ".allocation-k0" (fn-bs-frontier-encode 2)))
(assert-event
 (let ((ks (cdr (bsk0-f-start))))
   (and (not (fn-bs-frontier-inputp ks 'not-a-name (fn-bs-frontier-encode 2)))
        (not (fn-bs-lookup (car (bsk0-f-start)) :staging 'not-a-name))
        (not (fn-bs-frontier-inputp ks ".allocation-k0" '(256))))))
; frontier-created (2), frontier-written (4), frontier-replaced (9),
; frontier-attempted (11).
(bsk0-unrelated-at (bsk0-f-bad-relation) 2)
(bsk0-unrelated-at (bsk0-f-bad-relation) 4)
(bsk0-unrelated-at (bsk0-f-bad-relation) 9)
(bsk0-unrelated-at (bsk0-f-bad-relation) 11)
(bsk0-unrelated-at (bsk0-f-bad-stage) 2)
(bsk0-unrelated-at (bsk0-f-bad-octets) 4)
(bsk0-unrelated-at (bsk0-f-recycled) 9)
(bsk0-unrelated-at (bsk0-f-recycled) 11)
(bsk0-unrelated-at (bsk0-f-bad-absent) 2)
(bsk0-unrelated-at (bsk0-f-bad-absent) 4)
(bsk0-unrelated-at (bsk0-f-bad-absent) 9)
(bsk0-unrelated-at (bsk0-f-bad-absent) 11)

(defun bsk0-r-bad-relation ()
  (bsk0-r-run (bsk5-initial) (bsk0-r-prepared) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2)))
(defun bsk0-r-bad-stage ()
  (bsk0-r-run (car (bsk0-r-start)) (bsk0-r-prepared) 'not-a-name (fn-bs-txn-name 1) (bsk5-frame-2)))
(defun bsk0-r-bad-frame ()
  (bsk0-r-run (car (bsk0-r-start)) (bsk0-r-prepared) ".stage-k5-2" (fn-bs-txn-name 1) '(256)))
(defun bsk0-r-wrong-frame ()
  (bsk0-r-run (car (bsk0-r-start)) (bsk0-r-prepared) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame)))
(defun bsk0-r-bad-absent ()
  (bsk0-r-run (bsk0-r-occupied) (bsk0-r-prepared) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2)))
(assert-event
 (and (not (fn-bs-record-inputp (bsk0-r-prepared) 'not-a-name (fn-bs-txn-name 1) (bsk5-frame-2) *bsk5-arena*))
      (not (fn-bs-record-inputp (bsk0-r-prepared) ".stage-k5-2" (fn-bs-txn-name 1) '(256) *bsk5-arena*))))
; record-created (1), record-written (3), record-stage-unlinked (16),
; record-staging-cleaned (18).
(bsk0-unrelated-at (bsk0-r-bad-relation) 1)
(bsk0-unrelated-at (bsk0-r-bad-relation) 3)
(bsk0-unrelated-at (bsk0-r-bad-relation) 16)
(bsk0-unrelated-at (bsk0-r-bad-relation) 18)
(bsk0-unrelated-at (bsk0-r-bad-stage) 1)
(bsk0-unrelated-at (bsk0-r-bad-frame) 3)
(bsk0-unrelated-at (bsk0-r-wrong-frame) 16)
(bsk0-unrelated-at (bsk0-r-wrong-frame) 18)
(bsk0-unrelated-at (bsk0-r-bad-absent) 1)
(bsk0-unrelated-at (bsk0-r-bad-absent) 3)
(bsk0-unrelated-at (bsk0-r-bad-absent) 16)
(bsk0-unrelated-at (bsk0-r-bad-absent) 18)

; Error arms: the host's error observation applied to the cut pair.
(defun bsk0-f-arms-okp (run)
  (and (fn-bs-store-relation (car (nth 6 run))
                             (fn-sf-frontier-replace-result (cdr (nth 6 run)) :error) *bsk5-arena*)
       (fn-bs-store-relation (car (nth 9 run))
                             (fn-sf-frontier-replace-result (cdr (nth 6 run)) :error) *bsk5-arena*)
       (fn-bs-store-relation (car (nth 11 run))
                             (fn-sf-frontier-dir-result (cdr (nth 11 run)) :error) *bsk5-arena*)))
(defun bsk0-r-arms-okp (run)
  (and (fn-bs-store-relation (car (nth 6 run))
                             (fn-sf-record-link-result (cdr (nth 6 run)) :error) *bsk5-arena*)
       (fn-bs-store-relation (car (nth 10 run))
                             (fn-sf-record-dir-result (cdr (nth 10 run)) :error) *bsk5-arena*)))
; Reachable, non-degenerate: each error observation moves the kernel.
(assert-event
 (let ((f (bsk0-f-good)) (r (bsk5-record-2-run)))
   (and (bsk0-f-arms-okp f) (bsk0-r-arms-okp r)
        (equal (fn-sf-phase (fn-sf-frontier-replace-result (cdr (nth 6 f)) :error)) :fenced-frontier)
        (equal (fn-sf-phase (fn-sf-frontier-dir-result (cdr (nth 11 f)) :error)) :fenced-frontier)
        (equal (fn-sf-phase (fn-sf-record-link-result (cdr (nth 6 r)) :error)) :fenced-record)
        (equal (fn-sf-phase (fn-sf-record-dir-result (cdr (nth 10 r)) :error)) :fenced-record))))
(must-fail-checked (assert-event (bsk0-f-arms-okp (bsk0-f-bad-relation))))
(must-fail-checked (assert-event (bsk0-f-arms-okp (bsk0-f-bad-stage))))
(must-fail-checked (assert-event (bsk0-f-arms-okp (bsk0-f-bad-absent))))
(must-fail-checked (assert-event (bsk0-r-arms-okp (bsk0-r-bad-relation))))
(must-fail-checked (assert-event (bsk0-r-arms-okp (bsk0-r-bad-stage))))
(must-fail-checked (assert-event (bsk0-r-arms-okp (bsk0-r-bad-absent))))

; ---------------------------------------------------------------------------
;;; KEYSTONE fn-bs-k0-record-fence-pair-relation (PRF-041, row B2 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; From a related start with a valid record input and an absent stage, the
;;; record program's pair 11 (the fsync-dir fence of the link) is related.
(assert-event
 (let ((bs (car (bsk0-r-start))) (ks (bsk0-r-prepared)) (run (bsk5-record-2-run)))
   (and (equal run (bsk0-r-run bs ks ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2)))
        (fn-bs-store-relation bs ks *bsk5-arena*)
        (consp (fn-sf-records ks))
        (fn-bs-record-inputp ks ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2) *bsk5-arena*)
        (not (fn-bs-lookup bs :staging ".stage-k5-2"))
        (bsk0-related-at run 11))))
(bsk0-unrelated-at (bsk0-r-bad-relation) 11)
(bsk0-unrelated-at (bsk0-r-wrong-frame) 11)
(bsk0-unrelated-at (bsk0-r-bad-absent) 11)

;;; KEYSTONE fn-bs-record-directory-commit-observation-preserves-relation (PRF-041, row B3 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; A related :record-attempted pair whose transaction directory is committed
;;; stays related after the :ok directory observation, which moves it to :completing.
(defun bsk0-dir-commit-okp (bs ks)
  (and (fn-bs-store-relation bs (fn-sf-record-dir-result ks :ok) *bsk5-arena*)
       (equal (fn-sf-phase (fn-sf-record-dir-result ks :ok)) :completing)))
(assert-event
 (let* ((p (nth 12 (bsk5-record-2-run))) (bs (car p)) (ks (cdr p)))
   (and (fn-bs-store-relation bs ks *bsk5-arena*)
        (consp (fn-sf-records ks))
        (equal (fn-sf-phase ks) :record-attempted)
        (fn-bs-record-directory-committedp bs ks *bsk5-arena*)
        (bsk0-dir-commit-okp bs ks)
        (equal (fn-sf-record-dir-result ks :ok) (cdr (nth 14 (bsk5-record-2-run)))))))
; Drop the committed directory: at pair 10 the link is not yet fenced.
(assert-event
 (let* ((p (nth 10 (bsk5-record-2-run))) (bs (car p)) (ks (cdr p)))
   (and (fn-bs-store-relation bs ks *bsk5-arena*)
        (equal (fn-sf-phase ks) :record-attempted)
        (not (fn-bs-record-directory-committedp bs ks *bsk5-arena*)))))
(must-fail-checked
 (assert-event
  (let ((p (nth 10 (bsk5-record-2-run)))) (bsk0-dir-commit-okp (car p) (cdr p)))))
; The same drop over the retained article: the pre-publication bytes still
; relate to the attempted kernel (the link is not yet durable), but the
; directory is not committed there and the :ok observation breaks the relation.
(assert-event
 (let ((bs (car (bsk0-r-start))) (ks (cdr (nth 12 (bsk5-record-2-run)))))
   (and (fn-bs-store-relation bs ks *bsk5-arena*)
        (equal (fn-sf-phase ks) :record-attempted)
        (not (fn-bs-record-directory-committedp bs ks *bsk5-arena*)))))
(must-fail-checked
 (assert-event
  (bsk0-dir-commit-okp (car (bsk0-r-start)) (cdr (nth 12 (bsk5-record-2-run))))))
; Drop the relation: the committed kernel over the initial byte image.
(assert-event
 (let ((ks (cdr (nth 12 (bsk5-record-2-run)))))
   (and (not (fn-bs-store-relation (bsk5-initial) ks *bsk5-arena*))
        (equal (fn-sf-phase ks) :record-attempted))))
(must-fail-checked
 (assert-event (bsk0-dir-commit-okp (bsk5-initial) (cdr (nth 12 (bsk5-record-2-run))))))

;;; KEYSTONE fn-bs-k0-staging-create-preserves-relation (PRF-041, row B11 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Creating an absent staging name over a related, replay-invisible pair keeps it related.
(defun bsk0-created (b stage)
  (mv-let (r b1) (fn-bs-create b :staging stage :ok) (declare (ignore r)) b1))
(assert-event
 (let ((b (car (bsk0-r-start))) (k (bsk0-r-prepared)) (stage ".stage-k5-2"))
   (and (fn-bs-store-relation b k *bsk5-arena*)
        (consp (fn-sf-records k))
        (not (fn-bs-replay-visiblep k))
        (fn-bs-namep stage)
        (not (fn-bs-lookup b :staging stage))
        (fn-bs-store-relation (bsk0-created b stage) k *bsk5-arena*)
        (equal (bsk0-created b stage) (car (nth 1 (bsk5-record-2-run)))))))
; Drop the relation: the created stage over the initial byte image.
(assert-event (not (fn-bs-store-relation (bsk5-initial) (bsk0-r-prepared) *bsk5-arena*)))
(must-fail-checked
 (assert-event
  (fn-bs-store-relation (bsk0-created (bsk5-initial) ".stage-k5-2") (bsk0-r-prepared) *bsk5-arena*)))

;;; KEYSTONE fn-bs-k0-staging-fence-preserves-relation (PRF-041, row B12 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Fencing the staging directory of a related, replay-invisible pair keeps it related.
(assert-event
 (let ((b (car (bsk0-r-start))) (k (bsk0-r-prepared)))
   (and (fn-bs-store-relation b k *bsk5-arena*)
        (consp (fn-sf-records k))
        (not (fn-bs-replay-visiblep k))
        (fn-bs-store-relation (fn-bs-fence-dir b :staging) k *bsk5-arena*))))
(assert-event
 (let ((p (nth 16 (bsk5-record-2-run))))
   (and (fn-bs-store-relation (car p) (cdr p) *bsk5-arena*)
        (not (fn-bs-replay-visiblep (cdr p)))
        (fn-bs-store-relation (fn-bs-fence-dir (car p) :staging) (cdr p) *bsk5-arena*))))
(must-fail-checked
 (assert-event
  (fn-bs-store-relation (fn-bs-fence-dir (bsk5-initial) :staging) (bsk0-r-prepared) *bsk5-arena*)))

;;; KEYSTONE fn-bs-k0-pending-staging-extension-preserves-relation (PRF-041, row B10 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Appending pending operations that touch neither :root nor :transactions and
;;; write no authority inode keeps a related, replay-invisible pair related.
;;; The instance is the record program's write of the second frame into the
;;; staging inode created at pair 1.
(defun bsk0-ext-b () (car (nth 1 (bsk5-record-2-run))))
(defun bsk0-ext-k () (cdr (nth 1 (bsk5-record-2-run))))
(defun bsk0-ext-ops (b)
  (list (list :write (fn-bs-lookup b :staging ".stage-k5-2") 0 (bsk5-frame-2))))
(defun bsk0-ext (b ops)
  (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
              (append (fn-bs-pending b) ops) (fn-bs-next-ino b)))
(assert-event
 (let* ((b (bsk0-ext-b)) (k (bsk0-ext-k)) (ops (bsk0-ext-ops b)))
   (and (fn-bs-store-relation b k *bsk5-arena*)
        (consp (fn-sf-records k))
        (not (fn-bs-replay-visiblep k))
        (fn-bs-statep (bsk0-ext b ops))
        (not (fn-bs-ops-for-dir ops :root))
        (not (fn-bs-ops-for-dir ops :transactions))
        (fn-bs-k0-writes-avoid ops (fn-bs-authority-inode-list b))
        (fn-bs-store-relation (bsk0-ext b ops) k *bsk5-arena*))))
; Drop writes-avoid: the same write aimed at an authority inode (the
; retained record's) is a legal byte state, and the pair is no longer related.
(defun bsk0-ext-bad-ops (b)
  (list (list :write (car (fn-bs-authority-inode-list b)) 0 (bsk5-frame-2))))
(assert-event
 (let* ((b (bsk0-ext-b)) (k (bsk0-ext-k)) (ops (bsk0-ext-bad-ops b)))
   (and (fn-bs-store-relation b k *bsk5-arena*)
        (not (fn-bs-replay-visiblep k))
        (fn-bs-statep (bsk0-ext b ops))
        (not (fn-bs-ops-for-dir ops :root))
        (not (fn-bs-ops-for-dir ops :transactions))
        (not (fn-bs-k0-writes-avoid ops (fn-bs-authority-inode-list b))))))
(must-fail-checked
 (assert-event
  (let ((b (bsk0-ext-b)))
    (fn-bs-store-relation (bsk0-ext b (bsk0-ext-bad-ops b)) (bsk0-ext-k) *bsk5-arena*))))
