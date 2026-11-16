; Observed process-death coordinates joined to the existing actual-core replay.
; This is a process-visible file-effects relation, not a power-loss theorem.
(in-package "ACL2")
(include-book "native-device-envelope")

; No records may follow the selected ordinal. Unselected boundaries count too,
; including TLS/COMP cuts for which this physical-storage consumer makes no claim.
(defun fn2-nde-cut-prefix (rows ordinal control physical)
 (declare (xargs :verify-guards nil))
 (if (atom rows) (mv :missing-cut nil nil nil)
  (let ((row (car rows)))
   (cond
    ((and (true-listp row) (equal (len row) 2) (eq (car row) :control)
          (fn2-nde-control-shape-p (cadr row)))
     (fn2-nde-cut-prefix (cdr rows) ordinal (cons (cadr row) control) physical))
    ((and (true-listp row) (member-eq (car row) '(:submit :begin :return)))
     (fn2-nde-cut-prefix (cdr rows) ordinal control (cons row physical)))
    ((and (true-listp row) (equal (len row) 6) (eq (car row) :boundary)
          (equal (nth 1 row) (+ 1 ordinal)) (stringp (nth 2 row))
          (booleanp (nth 5 row)))
     (if (nth 5 row)
         (if (null (cdr rows)) (mv :ok (reverse control) (reverse physical) row)
           (mv :after-cut nil nil nil))
       (fn2-nde-cut-prefix (cdr rows) (+ 1 ordinal) control physical)))
    (t (mv :malformed-cut-capture nil nil nil))))))

(defun fn2-nde-cut-postedp (slot gen trace)
 (if (atom trace) nil
  (or (and (eq (caar trace) :post)
           (equal slot (nth 2 (car trace))) (equal gen (nth 3 (car trace))))
      (fn2-nde-cut-postedp slot gen (cdr trace)))))
(defun fn2-nde-cut-begunp (id records)
 (if (atom records) nil
  (or (equal (car records) (list :begin id))
      (fn2-nde-cut-begunp id (cdr records)))))
(defun fn2-nde-cut-pending (records pending)
 (if (atom records) pending
  (let ((row (car records)))
   (fn2-nde-cut-pending (cdr records)
    (case (car row)
     (:submit (append pending (list (nth 1 row))))
     (:return (remove1-equal (nth 1 row) pending))
     (otherwise pending))))))

; Before syscall: the FIFO head has NOT begun, so it cannot explain effects.
; After syscall: its real return (including short/error) must exist; no
; terminal Post may be invented. The shared decoder retains error Writes as
; uncertain spans and does not turn a returned Fence into power-loss evidence.
(defun fn2-nde-cut-position (cut trace records backend)
 (declare (xargs :verify-guards nil))
 (let* ((label (nth 2 cut)) (slot (nth 3 cut)) (gen (nth 4 cut))
        (take (fn2-nde-take slot gen trace))
        (job (fn2-nde-job slot gen records)) (id (nth 1 job)))
  (cond
   ((not (and (natp slot) (natp gen) take (fn2-nde-kind (nth 3 take))
              (eq (fn2-device-request (fn2-nde-kind (nth 3 take)) (nth 11 take) backend) :perform)
              (not (fn2-nde-cut-postedp slot gen trace)))) :cut-identity)
   ((equal label "device-submit")
    (if (and (not job) (equal (car (last trace)) '(:ack 1))
             (equal (car (last (butlast trace 1))) take))
        :before-submit :cut-submit-position))
   ((equal label "device-syscall")
    (if (and job (equal id (car (fn2-nde-cut-pending records nil)))
             (not (fn2-nde-cut-begunp id records)))
        :before-physical :cut-begin-position))
   ((equal label "device-syscall-return")
    (if (and job (equal (car (last records)) (fn2-nde-return id records)))
        :after-physical :cut-return-position))
   ((equal label "device-return")
    (if (and job (fn2-nde-return id records)) :before-terminal-post :cut-return-position))
   (t :unmapped-cut))))

(defun fn2-native-device-cut-replay (capture fd backend)
 (declare (xargs :verify-guards nil))
 (if (not (and (true-listp capture)
                (true-listp (car capture)) (equal (len (car capture)) 2)
                (eq (caar capture) :profile)
                (true-listp (cadr capture)) (equal (len (cadr capture)) 4)
                (eq (caadr capture) :boot-start)))
     (list :malformed-capture nil nil)
  (mv-let (code trace records cut) (fn2-nde-cut-prefix (cddr capture) 0 nil nil)
   (if (not (eq code :ok)) (list code nil nil)
    (let ((position (fn2-nde-cut-position cut trace records backend)))
     (if (not (member-eq position '(:before-submit :before-physical :after-physical :before-terminal-post)))
         (list position nil nil)
      (let ((replayed (fn2-native-device-control-replay
                        (cadar capture) (cadr capture) trace records fd backend)))
       (list (car replayed) position (cadr replayed)))))))))
