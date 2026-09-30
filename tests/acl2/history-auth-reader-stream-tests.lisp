(in-package "ACL2")
(include-book "../../books/history-auth-reader-stream")
(include-book "history-auth-reader-tests")

; Test-only traversal asserts full carried antecedent/conclusion at each actual
; request, completion, byte, digest tick and release on a nonempty authentic chain.
(defun fn-hsr-auth-stream-test-run (fuel c buffer pages pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix fuel) :verify-guards nil))
  (if (zp fuel) (mv nil c pgs-digest-state)
    (let ((antecedent (and (fn-hsr-auth-carryp c) (fn-hsr-auth-carryp c))))
      (case (fn-hsr-field 0 c)
        (:need-read
         (mv-let (v request waiting) (fn-hsr-auth-request c)
           (let ((bytes (cdr (assoc-equal (fn-hsr-field 5 request) pages))))
             (mv-let (completed next) (fn-hsr-auth-complete request (fn-hsr-field 3 request) (len bytes) :read-ok waiting)
               (mv-let (ok final pgs-digest-state)
                 (fn-hsr-auth-stream-test-run (1- fuel) next bytes pages pgs-digest-state)
                 (mv (and antecedent (equal v :need-read) (equal completed :yield)
                          (fn-hsr-auth-carryp waiting) (fn-hsr-auth-carryp waiting)
                          (fn-hsr-auth-carryp next) (fn-hsr-auth-carryp next) ok)
                     final pgs-digest-state))))))
        (:digest
         (mv-let (v next pgs-digest-state) (fn-hsr-auth-digest-tick c pgs-digest-state)
           (declare (ignore v))
           (mv-let (ok final pgs-digest-state)
             (fn-hsr-auth-stream-test-run (1- fuel) next buffer pages pgs-digest-state)
             (mv (and antecedent (fn-hsr-auth-carryp next) (fn-hsr-auth-carryp next) ok)
                 final pgs-digest-state))))
        (:byte
         (let ((demand (fn-hsr-auth-byte-demand c)))
           (mv-let (v next) (fn-hsr-auth-feed-byte (fn-hsr-field 1 demand) (fn-hsr-field 2 demand) (car buffer) c)
             (mv-let (ok final pgs-digest-state)
               (fn-hsr-auth-stream-test-run (1- fuel) next (cdr buffer) pages pgs-digest-state)
               (mv (and antecedent (equal v :yield) (fn-hsr-auth-carryp next) (fn-hsr-auth-carryp next) ok)
                   final pgs-digest-state)))))
        (:release
         (mv-let (v next) (fn-hsr-auth-release (fn-hsr-field 5 (fn-hsr-field 1 c)) c)
           (mv-let (ok final pgs-digest-state)
             (fn-hsr-auth-stream-test-run (1- fuel) next nil pages pgs-digest-state)
             (mv (and antecedent (equal v :released) (fn-hsr-auth-carryp next) (fn-hsr-auth-carryp next) ok)
                 final pgs-digest-state))))
        (otherwise (mv (and antecedent (equal (fn-hsr-field 0 c) :verified)) c pgs-digest-state))))))

(defthm fn-hsr-auth-stream-trajectory-positive
  (let* ((root (fn-hsr-field 2 (second (fn-hsr-auth-test-waiting))))
         (c (mv-nth 1 (fn-hsr-auth-begin root 0 41 '(:captured 7) '(:lease 8 2))))
         (selected (fn-hsr-auth-select-page 0 c (create-pgs-digest-state)))
         (run (fn-hsr-auth-stream-test-run 60000 (mv-nth 1 selected) nil *fn-hsr-auth-pages* (mv-nth 2 selected))))
    (and (fn-hsr-auth-carryp c) (fn-hsr-auth-carryp c)
         (equal (fn-hsr-field 0 c) :idle)
         (equal (mv-nth 0 selected) :yield)
         (fn-hsr-auth-carryp (mv-nth 1 selected)) (fn-hsr-auth-carryp (mv-nth 1 selected))
         (mv-nth 0 run)
         (equal (fn-hsr-field 17 (mv-nth 1 run)) '(:verified-page 0 41 0 304 2))))
  :rule-classes nil)


(defthm fn-hsr-auth-stream-cancel-positive
  (let* ((c (second (fn-hsr-auth-test-waiting)))
         (cancelled (fn-hsr-auth-cancel c)))
    (and (fn-hsr-auth-carryp c)
         (equal (fn-hsr-field 0 c) :waiting)
         (fn-hsr-auth-carryp (mv-nth 1 cancelled))
         (equal (fn-hsr-field 0 (mv-nth 1 cancelled)) :waiting)))
  :rule-classes nil)

(defthm fn-hsr-auth-stream-join-positive
  (let* ((issued (fn-hsr-auth-test-waiting)) (request (first issued)) (c (second issued))
         (joined (fn-hsr-auth-joined-failure request :uncertain c)))
    (and (fn-hsr-auth-carryp c)
         (equal request (fn-hsr-field 4 (fn-hsr-field 1 c)))
         (fn-hsr-auth-carryp (mv-nth 1 joined))
         (equal (fn-hsr-field 0 (mv-nth 1 joined)) :uncertain)))
  :rule-classes nil)

; Literal one-hypothesis removals over separately labelled corrupted state.
(defthm fn-hsr-auth-stream-carry-removals-corrupted-state
  (and (not (fn-hsr-auth-carryp nil))
       (not (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-select-page 0 nil (create-pgs-digest-state)))))
       (not (fn-hsr-auth-carryp (mv-nth 2 (fn-hsr-auth-request nil))))
       (not (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-complete nil 0 16384 :read-ok nil))))
       (not (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-feed-byte 0 0 0 nil))))
       (not (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-digest-tick nil (create-pgs-digest-state)))))
       (not (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-release 0 nil))))
       (not (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-cancel nil))))
       (not (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-joined-failure nil :uncertain nil))))
       (not (fn-hsr-auth-carryp (mv-nth 1 (fn-hsr-auth-finish-phase nil (create-pgs-digest-state))))))
  :rule-classes nil)

(defthm fn-hsr-auth-stream-open-lifetime-mode-removal
  (let* ((c (second (fn-hsr-auth-test-waiting)))
         (opened (fn-hsr-auth-open-phase :directory 17 2048 1 0 0 c (create-pgs-digest-state))))
    (and (fn-hsr-auth-carryp c)
         (not (member-eq (fn-hsr-field 0 (fn-hsr-field 1 c)) '(:idle :observed)))
         (equal (mv-nth 0 opened) :yield)
         (not (fn-hsr-auth-carryp (mv-nth 1 opened)))))
  :rule-classes nil)

(defthm fn-hsr-auth-stream-open-carry-removal-corrupted-state
  (let* ((c '(:idle (:idle)))
         (opened (fn-hsr-auth-open-phase :directory 17 2048 1 0 0 c (create-pgs-digest-state))))
    (and (member-eq (fn-hsr-field 0 (fn-hsr-field 1 c)) '(:idle :observed))
         (not (fn-hsr-auth-carryp c))
         (not (fn-hsr-auth-carryp (mv-nth 1 opened)))))
  :rule-classes nil)

(defthm fn-hsr-auth-stream-open-positive
  (let* ((root (fn-hsr-field 2 (second (fn-hsr-auth-test-waiting))))
         (initial (mv-nth 1 (fn-hsr-auth-begin root 0 41 '(:captured 7) '(:lease 8 2))))
         (c (fn-hsr-put 14 1 initial))
         (opened (fn-hsr-auth-open-phase :directory 17 2048 1 0 (fn-hsr-field 4 root) c (create-pgs-digest-state))))
    (and (fn-hsr-auth-carryp c)
         (member-eq (fn-hsr-field 0 (fn-hsr-field 1 c)) '(:idle :observed))
         (equal (mv-nth 0 opened) :yield)
         (equal (fn-hsr-field 0 (mv-nth 1 opened)) :need-read)
         (fn-hsr-auth-carryp (mv-nth 1 opened))))
  :rule-classes nil)

(defthm fn-hsr-auth-stream-finish-positive
  (let* ((root (fn-hsr-field 2 (second (fn-hsr-auth-test-waiting))))
         (initial (mv-nth 1 (fn-hsr-auth-begin root 0 41 '(:captured 7) '(:lease 8 2))))
         (selected (fn-hsr-auth-select-page 0 initial (create-pgs-digest-state)))
         (run (fn-hsr-auth-stream-test-run 60000 (mv-nth 1 selected) nil *fn-hsr-auth-pages* (mv-nth 2 selected)))
         (verified (mv-nth 1 run))
         (c (fn-hsr-put 0 :digest (fn-hsr-put 17 nil verified)))
         (finished (fn-hsr-auth-finish-phase c (mv-nth 2 run))))
    (and (mv-nth 0 run)
         (equal (fn-hsr-field 17 verified) '(:verified-page 0 41 0 304 2))
         (fn-hsr-auth-carryp c)
         (equal (pgs-dc-mode (mv-nth 2 run)) :done)
         (equal (mv-nth 0 finished) '(:verified-page 0 41 0 304 2))
         (equal (mv-nth 1 finished) verified)
         (fn-hsr-auth-carryp (mv-nth 1 finished))))
  :rule-classes nil)

(defthm fn-hsr-auth-stream-begin-hypothesis-removal
  (let ((begun (fn-hsr-auth-begin nil 0 41 '(:captured 7) '(:lease 8 2))))
    (and (not (equal (mv-nth 0 begun) :idle))
         (not (fn-hsr-auth-carryp (mv-nth 1 begun)))))
  :rule-classes nil)

; Mutation witness: the older u64 shape accepts this scratch, while the
; maintained carry rejects its non-u32 word. This is not a reachable source.
(defthm fn-hsr-auth-stream-non-u32-scratch-mutation
  (let* ((issued (fn-hsr-auth-test-waiting)) (request (first issued))
         (c (fn-hsr-put 9 '(1099511627776 0) (second issued)))
         (completed (fn-hsr-auth-complete request 0 16384 :read-ok c)))
    (and (fn-hsr-auth-lifetimep c)
         (equal (mod (len (fn-hsr-field 9 c)) 2) 0)
         (not (fn-b3-word-listp (fn-hsr-field 9 c)))
         (not (fn-hsr-auth-carryp c))
         (equal (mv-nth 0 completed) :yield)
         (not (fn-hsr-auth-carryp (mv-nth 1 completed)))))
  :rule-classes nil)
