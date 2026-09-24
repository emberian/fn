; Teeth for the K0 cut-coordinate keystones (books/byte-store-k0.lisp).
; The witnesses are the SECOND frontier, record and finish programs of the
; K5 fixture, so the Store already retains one acknowledged record: the
; related state is not the empty initial image.
(in-package "ACL2")
(include-book "../../books/byte-store-k0-staging")
(include-book "byte-store-stable-prefix-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bsk0-related-at (run k)
  (fn-bs-store-relation (car (nth k run)) (cdr (nth k run))))

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
   (and (fn-bs-store-relation bs ks)
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
   (and (not (fn-bs-store-relation (bsk5-initial) ks))
        (fn-bs-frontier-inputp ks ".allocation-k0" (fn-bs-frontier-encode 2))
        (not (fn-bs-lookup (bsk5-initial) :staging ".allocation-k0")))))
(must-fail
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
(must-fail
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
(must-fail
 (assert-event
  (bsk0-related-at (bsk0-f-run (bsk0-f-occupied) (cdr (bsk0-f-start))
                               ".allocation-k0" (fn-bs-frontier-encode 2))
                   15)))

; ---------------------------------------------------------------------------
; P-RECORD.  bsk5-record-2-run is the second publication.
(defun bsk0-r-start () (bsk5-frontier-2))
(defun bsk0-r-prepared ()
  (fn-sf-prepare-record (cdr (bsk0-r-start)) *bsk5-record-2*
                        *bsk5-groups* *bsk5-capacity*))
(defun bsk0-r-run (bs ks stage name frame)
  (fn-bs-run bs ks (fn-bs-record-program stage name frame)
             nil *bsk5-groups* *bsk5-capacity*))

(assert-event
 (let ((bs (car (bsk0-r-start))) (ks (bsk0-r-prepared)) (run (bsk5-record-2-run)))
   (and (fn-bs-store-relation bs ks)
        (fn-bs-record-inputp ks ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))
        (not (fn-bs-lookup bs :staging ".stage-k5-2"))
        (equal (len run) 19)
        (bsk0-related-at run 6) (bsk0-related-at run 8) (bsk0-related-at run 10)
        (bsk0-related-at run 12) (bsk0-related-at run 14)
        (equal (fn-sf-phase (cdr (nth 14 run))) :completing)
        (bsk0-related-at run 1) (bsk0-related-at run 3)
        (bsk0-related-at run 16) (bsk0-related-at run 18))))

; Drop the relation: the prepared kernel over the initial byte image.
(assert-event
 (and (not (fn-bs-store-relation (bsk5-initial) (bsk0-r-prepared)))
      (fn-bs-record-inputp (bsk0-r-prepared) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))))
(must-fail
 (assert-event
  (bsk0-related-at (bsk0-r-run (bsk5-initial) (bsk0-r-prepared)
                               ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))
                   14)))

; Drop the input contract: publish the FIRST record's frame under the second
; name.  The link lands, but its target does not decode to the candidate.
(assert-event
 (not (fn-bs-record-inputp (bsk0-r-prepared) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame))))
(must-fail
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
(must-fail
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
   (and (fn-bs-store-relation (car pair) (cdr pair))
        (fn-bs-finish-inputp (cdr pair) 1 1)
        (fn-bs-run-relatedp run)
        (equal (fn-sf-phase (cdr (nth 3 run))) :ready)
        (equal (len (fn-sf-successes (cdr (nth 3 run)))) 2))))
; Drop the relation: the completing kernel over the pre-publication bytes.
(must-fail
 (assert-event
  (let ((pair (car (last (bsk5-record-2-run)))))
    (fn-bs-run-relatedp (bsk0-fin-run (car (bsk0-r-start)) (cdr pair))))))
; The completion claim needs its input: a wrong txid leaves the kernel
; :completing.
(must-fail
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
  `(must-fail (assert-event (bsk0-related-at ,run ,k))))
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
 (and (not (fn-bs-record-inputp (bsk0-r-prepared) 'not-a-name (fn-bs-txn-name 1) (bsk5-frame-2)))
      (not (fn-bs-record-inputp (bsk0-r-prepared) ".stage-k5-2" (fn-bs-txn-name 1) '(256)))))
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
                             (fn-sf-frontier-replace-result (cdr (nth 6 run)) :error))
       (fn-bs-store-relation (car (nth 9 run))
                             (fn-sf-frontier-replace-result (cdr (nth 6 run)) :error))
       (fn-bs-store-relation (car (nth 11 run))
                             (fn-sf-frontier-dir-result (cdr (nth 11 run)) :error))))
(defun bsk0-r-arms-okp (run)
  (and (fn-bs-store-relation (car (nth 6 run))
                             (fn-sf-record-link-result (cdr (nth 6 run)) :error))
       (fn-bs-store-relation (car (nth 10 run))
                             (fn-sf-record-dir-result (cdr (nth 10 run)) :error))))
; Reachable, non-degenerate: each error observation moves the kernel.
(assert-event
 (let ((f (bsk0-f-good)) (r (bsk5-record-2-run)))
   (and (bsk0-f-arms-okp f) (bsk0-r-arms-okp r)
        (equal (fn-sf-phase (fn-sf-frontier-replace-result (cdr (nth 6 f)) :error)) :fenced-frontier)
        (equal (fn-sf-phase (fn-sf-frontier-dir-result (cdr (nth 11 f)) :error)) :fenced-frontier)
        (equal (fn-sf-phase (fn-sf-record-link-result (cdr (nth 6 r)) :error)) :fenced-record)
        (equal (fn-sf-phase (fn-sf-record-dir-result (cdr (nth 10 r)) :error)) :fenced-record))))
(must-fail (assert-event (bsk0-f-arms-okp (bsk0-f-bad-relation))))
(must-fail (assert-event (bsk0-f-arms-okp (bsk0-f-bad-stage))))
(must-fail (assert-event (bsk0-f-arms-okp (bsk0-f-bad-absent))))
(must-fail (assert-event (bsk0-r-arms-okp (bsk0-r-bad-relation))))
(must-fail (assert-event (bsk0-r-arms-okp (bsk0-r-bad-stage))))
(must-fail (assert-event (bsk0-r-arms-okp (bsk0-r-bad-absent))))
