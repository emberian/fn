; Local-witness instantiations of named positional assumptions, not native truth.
(in-package "ACL2")
(include-book "../../books/history-image-private-trace")
(include-book "history-image-writer-refinement-tests")

(local (defun hpit-model-write (before after file offset octets got outcome)
 (declare (xargs :guard t :verify-guards nil))
 (or (not (eq outcome :ok))
     (and (natp offset) (equal got (len octets))
          (equal (fn-bs-content after file)
                 (fn-bs-splice (fn-bs-content before file) offset octets))))))
(local (defun hpit-model-read (bytes file offset count octets got outcome)
 (declare (xargs :guard t :verify-guards nil))
 (or (not (eq outcome :ok))
     (and (natp offset) (natp count) (equal got count)
          (<= (+ offset count) (len (fn-bs-content bytes file)))
          (equal octets (take count (nthcdr offset (fn-bs-content bytes file))))))))
(local (defun hpit-model-file (content)
 (declare (xargs :guard t :verify-guards nil))
 (fn-bs-make 1 (list (cons 7 content)) nil nil 8)))

(local (defthm fn-hpit-full-private-write-readback-in-local-witness-model
 (implies (and (true-listp payload)
               (hpit-model-write before after file offset payload write-got :ok)
               (hpit-model-read after file offset (len payload) bytes read-got :ok))
  (equal bytes payload))

 :rule-classes nil
 :hints (("Goal" :use ((:functional-instance fn-hpit-full-private-write-readback
  (fn-assume-hpi-positional-write hpit-model-write)
  (fn-assume-hpi-positional-read hpit-model-read)))))))

(local (defthm fn-hpit-actual-read-observation-is-private-range-in-local-witness-model
 (let* ((plan (fn-hie-plan c effect stage ledger))
        (offset (fn-omk-at 3 plan)) (count (fn-omk-at 4 plan)))
  (implies (and (equal (fn-omk-at 1 plan) :read)
                (hpit-model-read visible file offset count bytes got :ok)
                (fn-hpi-octets-p count bytes))
   (equal (fn-hie-observation c effect stage ledger got :ok bytes)
    (list (if (equal (fn-omk-at 0 effect) :read-stage) :image-read :spool-read)
          (fn-omk-at 1 effect) stage (fn-omk-at 3 effect)
          (fn-omk-at 4 effect) (fn-omk-at 5 effect) (fn-omk-at 8 effect)
          :ok (take count (nthcdr offset (fn-bs-content visible file)))))))

 :rule-classes nil
 :hints (("Goal" :use ((:functional-instance fn-hpit-actual-read-observation-is-private-range
  (fn-assume-hpi-positional-write hpit-model-write)
  (fn-assume-hpi-positional-read hpit-model-read)))))))

; Complete three-premise write/readback positive in the local witness model.
(local (assert-event
 (let ((before (hpit-model-file '(1 2 3 4))) (after (hpit-model-file '(1 9 8 4)))
       (payload '(9 8)) (bytes '(9 8)))
  (and (true-listp payload)
       (hpit-model-write before after 7 1 payload 2 :ok)
       (hpit-model-read after 7 1 (len payload) bytes 2 :ok)
       (equal bytes payload)))))
; Remove the write assumption: correct later read cannot repair a lying write.
(local (assert-event
 (let ((before (hpit-model-file '(1 2 3 4))) (after (hpit-model-file '(1 2 3 4)))
       (payload '(9 8)) (bytes '(2 3)))
  (and (true-listp payload)
       (not (hpit-model-write before after 7 1 payload 2 :ok))
       (hpit-model-read after 7 1 (len payload) bytes 2 :ok)
       (not (equal bytes payload))))))
; Remove the read assumption: full-count typed bytes may still be a lie.
(local (assert-event
 (let ((before (hpit-model-file '(1 2 3 4))) (after (hpit-model-file '(1 9 8 4)))
       (payload '(9 8)) (bytes '(9 7)))
  (and (true-listp payload)
       (hpit-model-write before after 7 1 payload 2 :ok)
       (not (hpit-model-read after 7 1 (len payload) bytes 2 :ok))
       (not (equal bytes payload))))))
; Remove list shape: explicitly corrupt abstract payload, not a guarded syscall.
(local (defthm hpit-model-improper-payload-removal
 (let ((before (hpit-model-file '(1 2 3 4))) (after (hpit-model-file '(1 9 3 4)))
       (payload '(9 . 8)) (bytes '(9)))
  (and (not (true-listp payload))
       (hpit-model-write before after 7 1 payload 1 :ok)
       (hpit-model-read after 7 1 (len payload) bytes 1 :ok)
       (not (equal bytes payload))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable hpit-model-file hpit-model-write hpit-model-read fn-bs-splice)))))

; Same actual emitted controller operations as the complete writer fixture.
; The local file model instantiates the named byte assumption; it is not
; evidence that a native FD or syscall satisfies that assumption.
(local (defun hpit-model-read-point (stop mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance (fn-omk-at 1 maintenance)
                  10000000 "node" 17 "trail")))
   (mv-let (r fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (hpiw-test-until 50000 stop initial nil ledger nil nil 0 '(:decoded (:span 3 0 1 3))
      '(0 65 66 67) (fn-hp-mkey "ABC" 17)
      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (let* ((effect (nth 2 r)) (c (nth 3 r)) (ledger (nth 4 r))
           (stage (fn-omk-at 3 c)) (plan (fn-hie-plan c effect stage ledger))
           (offset (fn-omk-at 3 plan)) (count (fn-omk-at 4 plan))
           (eo (fn-omk-at 6 effect))
           (original-bytes
            (case stop
             (:read-stage (take count
               (nthcdr (mod eo 16384)
                (pgs-words-le-octets (cdr (assoc-equal (floor (- eo 16384) 16384) (nth 5 r)))))))
             (:read-spool (cdr (assoc-equal (cons (fn-omk-at 4 effect) (fn-omk-at 5 effect)) (nth 6 r))))
             (otherwise (fn-omk-at 9 effect))))
           (bytes (case mode
             (:read-assumption (cons (mod (+ 1 (nfix (car original-bytes))) 256) (cdr original-bytes)))
             (:octets (cons 999 (cdr original-bytes)))
             (otherwise original-bytes)))
           (model-bytes (if (eq mode :octets) bytes original-bytes))
           (visible (hpit-model-file (fn-bs-splice nil offset model-bytes)))
           (premises (list (equal (fn-omk-at 1 plan) :read)
                           (if (hpit-model-read visible 7 offset count bytes count :ok) t nil)
                           (if (fn-hpi-octets-p count bytes) t nil)))
           (expected (case mode (:direction '(nil t t)) (:read-assumption '(t nil t))
                                (:octets '(t t nil)) (otherwise '(t t t))))
           (law (equal (fn-hie-observation c effect stage ledger count :ok bytes)
             (list (if (equal (fn-omk-at 0 effect) :read-stage) :image-read :spool-read)
                   (fn-omk-at 1 effect) stage (fn-omk-at 3 effect)
                   (fn-omk-at 4 effect) (fn-omk-at 5 effect) (fn-omk-at 8 effect)
                   :ok (take count (nthcdr offset (fn-bs-content visible 7)))))))
     (mv (and (eq admitted :admitted) (eq (car r) :stopped) (eq (car effect) stop)
              (equal premises expected) (equal law (eq mode :positive)))
         fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))

(local (defun hpit-model-local-read-point (stop mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpit-model-read-point stop mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result))))

; Complete actual read-stage local-model positive witness.
(local (assert-event (hpit-model-local-read-point :read-stage :positive)))

; Complete actual read-stage local-model read-assumption witness.
(local (assert-event (hpit-model-local-read-point :read-stage :read-assumption)))

; Complete actual read-stage local-model octets witness.
(local (assert-event (hpit-model-local-read-point :read-stage :octets)))

; Complete actual read-spool local-model positive witness.
(local (assert-event (hpit-model-local-read-point :read-spool :positive)))

; Complete actual read-spool local-model read-assumption witness.
(local (assert-event (hpit-model-local-read-point :read-spool :read-assumption)))

; Complete actual read-spool local-model octets witness.
(local (assert-event (hpit-model-local-read-point :read-spool :octets)))

; Remove direction only at an actual issued spool write; not a read syscall.
(local (assert-event (hpit-model-local-read-point :write-spool :direction)))

(local (defun hpit-model-other-role (before after file other outcome)
 (declare (xargs :guard t :verify-guards nil))
 (or (not (eq outcome :ok)) (equal file other)
     (equal (fn-bs-content after other) (fn-bs-content before other)))))

(local (defun hpit-model-step-p (before step files)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((after (nth 0 step)) (role (nth 1 step)) (offset (nth 2 step))
        (payload (nth 3 step)) (got (nth 4 step)) (file (nth role files)))
  (and (true-listp files) (equal (len files) 3) (no-duplicatesp-equal files)
       (natp role) (< role 3)
       (hpit-model-write before after file offset payload got :ok)
       (hpit-model-other-role before after file (nth 0 files) :ok)
       (hpit-model-other-role before after file (nth 1 files) :ok)
       (hpit-model-other-role before after file (nth 2 files) :ok)))))

(local (defun hpit-model-trace-p (before steps files)
 (declare (xargs :guard t :verify-guards nil))
 (if (atom steps) (null steps)
  (and (hpit-model-step-p before (car steps) files)
       (hpit-model-trace-p (nth 0 (car steps)) (cdr steps) files)))))

(local (defthm hpit-model-step-has-complete-role-output
 (implies (hpit-model-step-p before step files)
  (equal (fn-hpit-role-view (nth 0 step) files)
         (fn-hpit-model-role-write (fn-hpit-role-view before files) step)))
 :rule-classes nil
 :hints (("Goal" :use ((:functional-instance fn-hpit-private-write-updates-exactly-three-retained-roles
  (fn-assume-hpi-positional-write hpit-model-write)
  (fn-assume-hpi-positional-other-role hpit-model-other-role)
  (fn-hpit-private-write-step-p hpit-model-step-p)))))))
(local (defthm hpit-model-trace-has-complete-role-output
 (implies (hpit-model-trace-p before steps files)
  (equal (fn-hpit-role-view (fn-hpit-private-trace-after before steps) files)
         (fn-hpit-model-role-trace (fn-hpit-role-view before files) steps)))
 :rule-classes nil
 :hints (("Goal" :use ((:functional-instance fn-hpit-interleaved-private-trace-has-exact-visible-bytes
  (fn-assume-hpi-positional-write hpit-model-write)
  (fn-assume-hpi-positional-other-role hpit-model-other-role)
  (fn-hpit-private-write-step-p hpit-model-step-p)
  (fn-hpit-private-write-trace-p hpit-model-trace-p)))))))
(local (defun hpit-model-three-files (stage data table)
 (declare (xargs :guard t :verify-guards nil))
 (fn-bs-make 1 (list (cons 1 stage) (cons 2 data) (cons 3 table)) nil nil 4)))

; Full single-write antecedent and whole three-file conclusion.
(local (assert-event
 (let* ((before (hpit-model-three-files '(0 0) '(0) '(0)))
        (after (hpit-model-three-files '(0 9) '(0) '(0)))
        (step (list after 0 1 '(9) 1)) (files '(1 2 3)))
  (and (hpit-model-step-p before step files)
       (equal (fn-hpit-role-view after files)
              (fn-hpit-model-role-write (fn-hpit-role-view before files) step))))))
; Remove sole step antecedent by corrupting only an untouched role's frame.
; The actual written bytes/count, role domain and other frames still hold.
(local (assert-event
 (let* ((before (hpit-model-three-files '(0 0) '(0) '(0)))
        (after (hpit-model-three-files '(0 9) '(88) '(0)))
        (step (list after 0 1 '(9) 1)) (files '(1 2 3)))
  (and (true-listp files) (equal (len files) 3) (no-duplicatesp-equal files)
       (natp (nth 1 step)) (< (nth 1 step) 3)
       (hpit-model-write before after 1 1 '(9) 1 :ok)
       (hpit-model-other-role before after 1 1 :ok)
       (not (hpit-model-other-role before after 1 2 :ok))
       (hpit-model-other-role before after 1 3 :ok)
       (not (hpit-model-step-p before step files))
       (not (equal (fn-hpit-role-view after files)
                   (fn-hpit-model-role-write (fn-hpit-role-view before files) step)))))))
; Entire interleaved stage, data-spool, table-spool trace with all role frames.
(local (assert-event
 (let* ((before (hpit-model-three-files '(0 0) '(0) '(0)))
        (a (hpit-model-three-files '(0 9) '(0) '(0)))
        (b (hpit-model-three-files '(0 9) '(7) '(0)))
        (z (hpit-model-three-files '(0 9) '(7) '(6)))
        (steps (list (list a 0 1 '(9) 1) (list b 1 0 '(7) 1) (list z 2 0 '(6) 1)))
        (files '(1 2 3)))
  (and (hpit-model-trace-p before steps files)
       (equal (fn-hpit-role-view (fn-hpit-private-trace-after before steps) files)
              (fn-hpit-model-role-trace (fn-hpit-role-view before files) steps))
       (equal (fn-hpit-role-view z files) '((0 9) (7) (6)))))))
; Sole trace antecedent removal: two genuine writes followed by a lying
; table-write observation that changes an untouched stage byte.
(local (assert-event
 (let* ((before (hpit-model-three-files '(0 0) '(0) '(0)))
        (a (hpit-model-three-files '(0 9) '(0) '(0)))
        (b (hpit-model-three-files '(0 9) '(7) '(0)))
        (z (hpit-model-three-files '(0 88) '(7) '(6)))
        (last (list z 2 0 '(6) 1))
        (steps (list (list a 0 1 '(9) 1) (list b 1 0 '(7) 1) last))
        (files '(1 2 3)))
  (and (hpit-model-step-p before (car steps) files)
       (hpit-model-step-p a (cadr steps) files)
       (hpit-model-write b z 3 0 '(6) 1 :ok)
       (not (hpit-model-other-role b z 3 1 :ok))
       (hpit-model-other-role b z 3 2 :ok)
       (hpit-model-other-role b z 3 3 :ok)
       (not (hpit-model-step-p b last files))
       (not (hpit-model-trace-p before steps files))
       (not (equal (fn-hpit-role-view (fn-hpit-private-trace-after before steps) files)
                   (fn-hpit-model-role-trace (fn-hpit-role-view before files) steps)))))))
