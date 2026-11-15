; Independent literal scheduler state and complete core representation relation.
; Definitions are extracted unchanged so effect lifting can use R before
; the reference transition is defined; trace is never its semantic input.
(in-package "ACL2")
(include-book "assembly-reference")
(include-book "core-scheduler-wake")
(include-book "queue-model")

; A literal weighted calendar and independent FIFO state. Selection history
; may occupy a fifth list element; queue operations preserve extra elements.
(defun fn2-ref-weight-pass (weights k slot)
  (declare (xargs :guard (and (natp k) (natp slot))))
  (if (atom weights) nil
    (if (< k (nfix (car weights)))
        (cons (list :principal slot) (fn2-ref-weight-pass (cdr weights) k (+ 1 slot)))
      (fn2-ref-weight-pass (cdr weights) k (+ 1 slot)))))

(defun fn2-ref-weight-round (weights k)
  (declare (xargs :guard (natp k) :measure (nfix (- 255 (nfix k)))))
  (if (or (not (natp k)) (>= k 255)) nil
    (let ((pass (fn2-ref-weight-pass weights k 0)))
      (if (atom pass) nil (append pass (fn2-ref-weight-round weights (+ 1 k)))))))

(defun fn2-ref-calendar-build (entries in-block)
  (declare (xargs :guard (natp in-block)))
  (if (atom entries) nil
    (cons (car entries)
          (if (or (atom (cdr entries)) (= in-block (1- *fn2-calendar-principals-per-group*)))
              (append '((:service 0) (:service 1) (:service 2) (:service 3))
                      (fn2-ref-calendar-build (cdr entries) 0))
            (fn2-ref-calendar-build (cdr entries) (+ 1 in-block))))))

(defun fn2-ref-calendar (weights)
  (declare (xargs :guard t))
  (fn2-ref-calendar-build (fn2-ref-weight-round weights 0) 0))

(defun fn2-ref-calendar-count (calendar slot)
  (declare (xargs :guard t))
  (if (atom calendar) 0
    (+ (if (equal (car calendar) (list :principal slot)) 1 0)
       (fn2-ref-calendar-count (cdr calendar) slot))))

(defun fn2-ref-calendar-weights (calendar slot p)
  (declare (xargs :guard (and (natp slot) (natp p)) :measure (nfix (- (nfix p) (nfix slot)))))
  (if (or (not (natp slot)) (>= slot (nfix p))) nil
    (cons (fn2-ref-calendar-count calendar slot)
          (fn2-ref-calendar-weights calendar (+ 1 slot) p))))

(defun fn2-ref-weights-in-range (weights)
  (declare (xargs :guard t))
  (or (atom weights)
      (and (natp (car weights)) (<= 1 (car weights)) (<= (car weights) 255)
           (fn2-ref-weights-in-range (cdr weights)))))

(defun fn2-ref-lists (weights cursor queues)
  (declare (xargs :verify-guards nil))
  (list (fn2-ref-calendar weights) cursor queues '(0 0 0 0)))



(defun fn2-ref-wake (id lists fn2-ref-core)
  (declare (xargs :stobjs fn2-ref-core :verify-guards nil))
  (if (equal id *fn2-none*) (mv lists fn2-ref-core)
    (let* ((valid (eq (fn2-machine-principal-slot-read-code id fn2-ref-core) :ok))
           (principal (and valid (fn2-machine-principal-slot id fn2-ref-core)))
           (queues (nth 2 lists)) (queue (fn2-ref-queue principal queues)))
    (cond ((or (not valid)
               (not (fn2-ref-list-member (list :principal principal) (car lists))))
           (let ((fn2-ref-core (fn2-core-stop *fn2-stop-reason-wake-bounds* fn2-ref-core)))
             (mv lists fn2-ref-core)))
          ((fn2-ref-queued-anywhere id queues) (mv lists fn2-ref-core))
          ((or (>= (len queue) *fn2-none*)
               (>= (fn2-ref-queue-count queues) *fn2-none*)
               (and (consp queue) (not (fn2-machine-idp (car (last queue)) fn2-ref-core))))
           (let ((fn2-ref-core (fn2-core-stop *fn2-stop-reason-wake-state* fn2-ref-core)))
             (mv lists fn2-ref-core)))
          (t (mv (update-nth 2 (fn2-ref-enqueue id principal queues) lists) fn2-ref-core))))))

; Intrusive links are read only on the CONCRETE side of the relation.
; Timer metadata remains compared even though reference queue links are unused.
(defun fn2-ref-concrete-queue (fuel id fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil :measure (nfix fuel)))
  (cond ((equal id *fn2-none*) nil)
        ((or (zp fuel) (>= (nfix id) (fn2-sched-rows fn2-sched))) '(:bad-chain))
        (t (cons id (fn2-ref-concrete-queue (- fuel 1) (fn2-sched-next id fn2-sched) fn2-sched)))))

(defun fn2-ref-queues-difference (left queues fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil :measure (nfix left)))
  (if (zp left) nil
    (let* ((p (- left 1))
           (actual (fn2-ref-concrete-queue (fn2-sched-rows fn2-sched)
                                          (fn2-sched-headsi p fn2-sched) fn2-sched))
           (expected (fn2-ref-queue p queues)))
      (if (and (equal actual expected) (equal (len actual) (fn2-sched-countsi p fn2-sched))
               (equal (fn2-sched-tailsi p fn2-sched)
                      (if (consp actual) (car (last actual)) *fn2-none*)))
          (fn2-ref-queues-difference (- left 1) queues fn2-sched)
        (list :principal-fifo p actual expected)))))

(defun fn2-ref-calendar-difference (calendar i fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil))
  (if (atom calendar) nil
    (let* ((e (car calendar)) (p (fn2-sched-nprincipals fn2-sched))
           (code (if (eq (car e) :principal) (cadr e) (+ p (nfix (cadr e))))))
      (if (equal code (fn2-sched-calendari i fn2-sched))
          (fn2-ref-calendar-difference (cdr calendar) (+ 1 (nfix i)) fn2-sched)
        (list :calendar-entry i)))))

(defun fn2-ref-machine-links (id queue prev)
  (declare (xargs :verify-guards nil))
  (if (atom queue) nil
    (if (equal id (car queue))
        (list prev (if (consp (cdr queue)) (cadr queue) *fn2-none*))
      (fn2-ref-machine-links id (cdr queue) (car queue)))))

(defun fn2-ref-machine-queue (id queues)
  (declare (xargs :verify-guards nil))
  (if (atom queues) nil
    (let ((links (fn2-ref-machine-links id (cdar queues) *fn2-none*)))
      (if links (cons (caar queues) links)
        (fn2-ref-machine-queue id (cdr queues))))))

(defun fn2-ref-links-difference (left queues fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil :measure (nfix left)))
  (if (zp left) nil
    (let* ((id (- left 1)) (entry (fn2-ref-machine-queue id queues)))
      (if (and (equal (fn2-sched-in-queue id fn2-sched) (if entry 1 0))
               (or (not entry)
                   (and (equal (fn2-sched-principal id fn2-sched) (car entry))
                        (equal (fn2-sched-prev id fn2-sched) (cadr entry))
                        (equal (fn2-sched-next id fn2-sched) (caddr entry)))))
          (fn2-ref-links-difference (- left 1) queues fn2-sched)
        (list :runnable-links id)))))

(defun fn2-ref-scheduler-difference (lists fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core)))
    (difference)
    (cond ((let ((weights (fn2-ref-calendar-weights (nth 0 lists) 0 (fn2-sched-nprincipals fn2-sched))))
             (not (and (fn2-ref-weights-in-range weights)
                       (equal (nth 0 lists) (fn2-ref-calendar weights)))))
           '(:literal-calendar))
          ((not (equal (fn2-sched-queued fn2-sched) (fn2-ref-queue-count (nth 2 lists))))
           '(:runnable-count))
          ((not (equal (fn2-sched-cursor fn2-sched) (nth 1 lists))) '(:calendar-position))
          ((not (equal (fn2-sched-calendar-length fn2-sched) (len (nth 0 lists)))) '(:calendar-length))
          ((not (equal (list (fn2-sched-servicesi 0 fn2-sched) (fn2-sched-servicesi 1 fn2-sched)
                            (fn2-sched-servicesi 2 fn2-sched) (fn2-sched-servicesi 3 fn2-sched))
                       (nth 3 lists))) '(:service-flags))
          (t (or (fn2-ref-calendar-difference (nth 0 lists) 0 fn2-sched)
                 (fn2-ref-queues-difference (fn2-sched-nprincipals fn2-sched) (nth 2 lists) fn2-sched)
                 (fn2-ref-links-difference (fn2-sched-rows fn2-sched) (nth 2 lists) fn2-sched))))
    difference))

(defun fn2-ref-timer-row-difference (left fn2-sched fn2-sched-ref)
  (declare (xargs :stobjs (fn2-sched fn2-sched-ref) :verify-guards nil :measure (nfix left)))
  (if (zp left) nil
    (let ((i (- left 1)))
      (if (and (equal (fn2-sched-deadline i fn2-sched) (fn2-sched-deadline i fn2-sched-ref))
               (equal (fn2-sched-expired i fn2-sched) (fn2-sched-expired i fn2-sched-ref)))
          (fn2-ref-timer-row-difference i fn2-sched fn2-sched-ref)
        (list :timer-row i)))))

(defun fn2-ref-timer-state-difference (fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core))) (difference)
    (stobj-let ((fn2-sched-ref (fn2-core-sched-ref fn2-ref-core))) (difference)
      (cond ((not (equal (fn2-sched-rows fn2-sched) (fn2-sched-rows fn2-sched-ref))) '(:timer-rows))
            ((not (equal (fn2-sched-armed-timers fn2-sched) (fn2-sched-armed-timers fn2-sched-ref))) '(:timer-armed))
            ((not (equal (fn2-sched-earliest-deadline fn2-sched) (fn2-sched-earliest-deadline fn2-sched-ref))) '(:timer-earliest))
            ((not (equal (fn2-sched-scan-min fn2-sched) (fn2-sched-scan-min fn2-sched-ref))) '(:timer-scan-min))
            (t (fn2-ref-timer-row-difference (fn2-sched-rows fn2-sched) fn2-sched fn2-sched-ref)))
      difference)
    difference))

(defun fn2-ref-difference (fn2-core fn2-ref-core lists)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (or (fn2-ref-scheduler-difference lists fn2-core)
      (fn2-ref-timer-state-difference fn2-core fn2-ref-core)
      (fn2-ref-core-difference fn2-core fn2-ref-core)))

(defun fn2-representation-relation (fn2-core fn2-ref-core lists)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (not (fn2-ref-difference fn2-core fn2-ref-core lists)))
(in-theory (disable fn2-ref-difference fn2-representation-relation))
