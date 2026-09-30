(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun nfix (x) (if (natp x) x 0))
(defun zp (x) (not (and (integerp x) (> x 0))))
(defparameter *fn-log-sink-close-wait-seconds* 10)
(defvar *fnn-log-queue-mutex* (sb-thread:make-mutex))
(defvar *fnn-log-queue-ready* (sb-thread:make-waitqueue))
(defvar *fnn-log-queue-head* nil)
(defvar *fnn-log-queue-tail* nil)
(defvar *fnn-log-sink* nil)
(defvar *fnn-log-writer* nil)
(defvar *fnn-owner-log-fd* nil)
(defvar *fnn-owner-retained-service* nil)
(defvar *fnn-owner-retained-settlement* :held)
(defvar *fnn-owner-reserving-thread* nil)
(defvar *fnn-owner-caller-reservation* nil)
(defparameter +fnn-lock-un+ 8)
(defstruct fnn-log fd spare)
(defstruct fnn-store log lock-fd completion-pending fenced)
(defstruct fnn-owner-service store)
(defvar *recorded* nil)
(defvar *fail-close* nil)
(defvar *entered* (sb-thread:make-semaphore))
(defvar *release* (sb-thread:make-semaphore))
(defun alive () (and *fnn-log-writer* (sb-thread:thread-alive-p *fnn-log-writer*)))
(defun fnn-close (fd) (push (list :close fd (alive)) *recorded*)
 (when (eql fd *fail-close*) (error "recording physical close uncertainty")))
(defun fnn-flock (fd mode) (push (list :flock fd mode (alive)) *recorded*))
(defun fnn-lstat (path) (declare (ignore path)) t)
(defun fnn-unlink (path) (push (list :unlink path (alive)) *recorded*))
(defun fnn-fault (&rest args) (error "fault ~s" args))
(defun fnn-indeterminate (&rest args) (error "uncertain ~s" args))
(defun fnn-log-write-item (destination octets)
 (sb-thread:signal-semaphore *entered*)
 (assert (sb-thread:wait-on-semaphore *release* :timeout 30))
 (push (list :journal-write destination (length octets)) *recorded*) :written)


(defun fn-log-sink-field (i s)
  
  (cond ((atom s) 0)
        ((zp i) (nfix (car s)))
        (t (fn-log-sink-field (1- i) (cdr s)))))

(defun fn-log-sink-pending-octets (s)  (fn-log-sink-field 0 s))

(defun fn-log-sink-pending-lines (s)  (fn-log-sink-field 1 s))

(defun fn-log-sink-dropped (s)  (fn-log-sink-field 2 s))

(defun fn-log-sink-written (s)  (fn-log-sink-field 3 s))

(defun fn-log-sink-offered (s)  (fn-log-sink-field 4 s))

(defun fn-log-sink-init ()
  
  (list 0 0 0 0 0))

(defun fn-log-sink-offer (s len bound)
  
  (let ((po (fn-log-sink-pending-octets s))
        (pl (fn-log-sink-pending-lines s))
        (d (fn-log-sink-dropped s))
        (w (fn-log-sink-written s))
        (o (fn-log-sink-offered s))
        (len (nfix len))
        (bound (nfix bound)))
    (if (or (zp pl) (<= (+ po len) bound))
        (list :queue (list (+ po len) (+ 1 pl) d w (+ 1 o)))
      (list :drop (list po pl (+ 1 d) w (+ 1 o))))))

(defun fn-log-sink-take (s len outcome)
  
  (let ((po (fn-log-sink-pending-octets s))
        (pl (fn-log-sink-pending-lines s))
        (d (fn-log-sink-dropped s))
        (w (fn-log-sink-written s))
        (o (fn-log-sink-offered s)))
    (if (zp pl)
        (list po pl d w o)
      (list (if (equal pl 1) 0 (nfix (- po (nfix len))))
            (1- pl)
            (if (equal outcome :written) d (+ 1 d))
            (if (equal outcome :written) (+ 1 w) w)
            o))))

(defun fn-log-sink-close-wait-seconds ()
  
  *fn-log-sink-close-wait-seconds*)

(defun fn-ort-log-close-action (join-observation pending-lines pending-octets queuedp)
  
  (if (and (or (equal join-observation :joined)
               (equal join-observation :absent))
           (equal pending-lines 0) (equal pending-octets 0)
           (equal queuedp nil))
      :joined
    :held))

(defun fn-ort-log-close-exit (prior uncertain action)
  
  (if (equal action :joined) prior uncertain))

(defun fn-ort-report-close-action (log-action journal-observation)
  
  (if (and (equal log-action :joined)
           (or (equal journal-observation :closed)
               (equal journal-observation :absent)))
      :joined
    :held))

(defun fn-ort-store-close-action (settlement authority-presentp caller-fd-presentp)
  
  (cond ((not (equal settlement :joined)) :held)
        ((equal authority-presentp nil) :settled)
        ((not (equal caller-fd-presentp nil)) :defer)
        (t :close)))

(defun fn-ort-service-settlement-action (settlement store-observation)
  
  (if (and (equal settlement :joined)
           (or (equal store-observation :closed)
               (equal store-observation :absent)))
      :joined :held))

(defun fn-ort-service-start-action (writer-presentp authority-presentp)
  
  (if (and (equal writer-presentp nil) (equal authority-presentp nil))
      :start :held))

(defun fn-ort-service-claim-action (writer-presentp authority-presentp reservation-ownedp)
  
  (if (and (equal writer-presentp nil)
           (or (equal authority-presentp nil) (equal reservation-ownedp t)))
      :start :held))

(defun fn-ort-service-start-reason (action)
  
  (if (equal action :held) "prior owner authority is unsettled" ""))

(defun fnn-core (name &rest args) (apply (symbol-function name) args))

(defun fnn-log-queue-push (item)
  "Append ITEM; the caller holds the queue mutex."
  (let ((cell (list item)))
    (if *fnn-log-queue-tail*
        (setf (cdr *fnn-log-queue-tail*) cell)
        (setq *fnn-log-queue-head* cell))
    (setq *fnn-log-queue-tail* cell)
    (sb-thread:condition-notify *fnn-log-queue-ready*)))

(defun fnn-log-sink-accept (sink what)
  (unless (and (listp sink) (= (length sink) 5)
               (every (lambda (n) (and (integerp n) (<= 0 n))) sink))
    (fnn-fault "ACL2 returned a malformed log sink after ~a" what))
  (setq *fnn-log-sink* sink))

(defun fnn-log-writer-loop ()
  (loop
    (let ((item (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
                  (loop until *fnn-log-queue-head*
                        do (sb-thread:condition-wait *fnn-log-queue-ready*
                                                     *fnn-log-queue-mutex*))
                  (prog1 (pop *fnn-log-queue-head*)
                    (unless *fnn-log-queue-head*
                      (setq *fnn-log-queue-tail* nil))))))
      (case (car item)
        (:stop (return))
        (:swap
         ;; Only this thread writes the descriptor while it runs.
         (let ((old *fnn-owner-log-fd*))
           (setq *fnn-owner-log-fd* (cdr item))
           (when old (ignore-errors (fnn-close old)))))
        (t
         (let ((outcome (fnn-log-write-item (car item) (cdr item))))
           (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
             (fnn-log-sink-accept
              (fnn-core 'fn-log-sink-take *fnn-log-sink* (length (cdr item)) outcome)
              "a write"))))))))

(defun fnn-log-writer-start ()
  "Start the owner's log writer with ACL2's empty sink (fn-log-sink-init)."
  (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
    (unless *fnn-log-writer*
      (fnn-log-sink-accept (fnn-core 'fn-log-sink-init) "init")
      (setq *fnn-log-queue-head* nil
            *fnn-log-queue-tail* nil
            *fnn-log-writer*
            (sb-thread:make-thread #'fnn-log-writer-loop
                                   :name "fn service log writer")))))

(defun fnn-log-writer-stop ()
  "Ask the writer to drain and stop, and wait for it at most ACL2's
fn-log-sink-close-wait-seconds.  A writer still blocked on its sink then is
left running (lines keep being offered and dropped, never waited on) and the
process exits without it: what it had queued, a wedged sink would lose
anyway."
  ;; Return only the physical join observation. A caller must not turn the
  ;; bounded wait into a claim that the journal producer relinquished its job.
  (let ((thread (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
                  (when *fnn-log-writer*
                    (fnn-log-queue-push (list :stop))
                    *fnn-log-writer*))))
    (if thread
      (multiple-value-bind (value outcome)
          (sb-thread:join-thread thread
                                 :timeout (fnn-core 'fn-log-sink-close-wait-seconds)
                                 :default :timeout)
        (declare (ignore value))
        (if (eq outcome :timeout)
            :timeout
          (progn
            (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
              (setq *fnn-log-writer* nil
                    *fnn-log-queue-head* nil
                    *fnn-log-queue-tail* nil))
            :joined)))
      :absent)))

(defun fnn-log-discard-spare (log)
  "Close and unlink a spare that will not be renamed (another index, or the
store closing).  Removing a staged name is never uncertain for the history:
the open ignores and sweeps it."
  (let ((spare (fnn-log-spare log)))
    (when spare
      (destructuring-bind (index path fd) spare
        (declare (ignore index))
        ;; An ambiguous close retains the spare identity/debt. The caller
        ;; fences the Store and must not allocate or reuse this descriptor.
        (fnn-close fd)
        (setf (fnn-log-spare log) nil)
        (ignore-errors (when (fnn-lstat path) (fnn-unlink path)))))))

(defun fnn-store-close (store)
  (setf (fnn-store-completion-pending store) nil)
  (let ((log (fnn-store-log store)))
    (when log
      ;; Keep the handle and Store authority on any uncertain physical close.
      ;; Callers may retry/recover; a silent error is not definite teardown.
      (fnn-log-discard-spare log)
      (fnn-close (fnn-log-fd log))
      (setf (fnn-store-log store) nil)))
  (let ((fd (fnn-store-lock-fd store)))
    (when fd
      ;; A failed unlock/close is uncertainty, not proof that the lock remains
      ;; held. Preserve its handle and let the caller retain recovery authority.
      (unwind-protect (fnn-flock fd +fnn-lock-un+)
        (fnn-close fd))
      (setf (fnn-store-lock-fd store) nil))))

(defun fnn-owner-run-admission ()
  (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
    (fnn-core 'fn-ort-service-start-action
              (and *fnn-log-writer* t) (and *fnn-owner-retained-service* t))))

(defun fnn-owner-claim-run-authority (&optional caller-reservation)
  (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
    (let ((action (fnn-core 'fn-ort-service-claim-action
                            (and *fnn-log-writer* t)
                            (and *fnn-owner-retained-service* t)
                            (and caller-reservation
                                 (eq *fnn-owner-retained-service* t)
                                 (eq *fnn-owner-reserving-thread* sb-thread:*current-thread*)
                                 t))))
      (unless (eq action :start)
        (fnn-indeterminate "~a" (fnn-core 'fn-ort-service-start-reason action)))
      (setq *fnn-owner-retained-service* t
            *fnn-owner-reserving-thread* sb-thread:*current-thread*
            *fnn-owner-retained-settlement* :held))))

(defun fnn-owner-retain-run-authority (service)
  (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
    (when service (setq *fnn-owner-retained-service* service
                        *fnn-owner-reserving-thread* nil))))

(defun fnn-owner-store-settlement (service settlement)
  "Retain the actual service and Store lock until writer/journal settlement.
Store close errors are physical uncertainty, never silent authority release."
  (let ((action
          (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
            (fnn-core 'fn-ort-store-close-action settlement
                      (and *fnn-owner-retained-service* t)
                      (and *fnn-owner-log-fd* t)))))
    (case action
      (:held (setq *fnn-owner-retained-settlement* action) action)
      ;; The operator caller still owes its final direct log line/close.
      ;; Keep the Store lock and actual service, without relabeling joined
      ;; producer settlement as uncertainty while that caller finishes.
      (:defer (setq *fnn-owner-retained-settlement* settlement) settlement)
      (:settled (fnn-core 'fn-ort-service-settlement-action settlement :absent))
      (:close
       (let* ((observation
                (if service
                    (handler-case
                        (progn (fnn-store-close (fnn-owner-service-store service)) :closed)
                      (error ()
                        (setf (fnn-store-fenced (fnn-owner-service-store service)) t)
                        :uncertain))
                  :absent))
              (result (fnn-core 'fn-ort-service-settlement-action settlement observation)))
         (setq *fnn-owner-retained-settlement* result)
         (when (eq result :joined)
           (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
             (setq *fnn-owner-retained-service* nil
                   *fnn-owner-reserving-thread* nil)))
         result))
      (otherwise (fnn-fault "malformed Store settlement action ~a" action)))))


(let* ((store (make-fnn-store :log (make-fnn-log :fd 401) :lock-fd 402 :completion-pending :owed))
       (service (make-fnn-owner-service :store store)))
 (assert (eq (fnn-owner-run-admission) :start))
 (fnn-owner-claim-run-authority)
 ;; Initial reservation rejects another caller; only its dynamic owner-entry
 ;; token can consume it before installing the service.
 (assert (handler-case (progn (fnn-owner-claim-run-authority nil) nil) (error () t)))
 (let ((worker (sb-thread:make-thread
          (lambda () (handler-case (progn (fnn-owner-claim-run-authority t) nil) (error () t))))))
  (assert (eq (sb-thread:join-thread worker) t)))
 (fnn-owner-claim-run-authority t)
 (fnn-owner-retain-run-authority service)
 (fnn-log-writer-start)
 (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
  (dotimes (i 2)
   (let ((answer (fnn-core 'fn-log-sink-offer *fnn-log-sink* 3 1048576)))
    (assert (eq (first answer) :queue))
    (fnn-log-sink-accept (second answer) :fixture)
    (fnn-log-queue-push (cons :journal '(65 66 10))))))
 (assert (sb-thread:wait-on-semaphore *entered* :timeout 2))
 (assert (eq (fnn-log-writer-stop) :timeout))
 (assert (alive))
 (assert *fnn-log-queue-head*)
 (assert (= (fn-log-sink-pending-lines *fnn-log-sink*) 2))
 (assert (= (fn-log-sink-pending-octets *fnn-log-sink*) 6))
 (let ((settlement (fn-ort-log-close-action :timeout 2 6 t)))
  (assert (eq settlement :held))
  (assert (eq (fnn-owner-store-settlement service settlement) :held)))
 (assert (null *recorded*))
 (assert (eq *fnn-owner-retained-service* service))
 (assert (= (fnn-store-lock-fd store) 402))
 (assert (= (fnn-log-fd (fnn-store-log store)) 401))
 (assert (eq (fnn-owner-run-admission) :held))
 (assert (handler-case (progn (fnn-owner-claim-run-authority) nil) (error () t)))
 (assert (eq *fnn-owner-retained-service* service))
 (format t "PASS queued-timeout retains actual writer/service/Store descriptors and startup fence~%")
 (sb-thread:signal-semaphore *release*)
 (assert (sb-thread:wait-on-semaphore *entered* :timeout 2))
 (sb-thread:signal-semaphore *release*)
 (assert (eq (fnn-log-writer-stop) :joined))
 (assert (null *fnn-log-writer*))
 (assert (null *fnn-log-queue-head*))
 (assert (= (fn-log-sink-pending-lines *fnn-log-sink*) 0))
 (assert (= (fn-log-sink-pending-octets *fnn-log-sink*) 0))
 (let ((settlement (fn-ort-report-close-action
                     (fn-ort-log-close-action :joined 0 0 nil) :closed)))
  (setq *fnn-owner-log-fd* 403)
  (assert (eq (fnn-owner-store-settlement service settlement) :joined))
  (assert (eq *fnn-owner-retained-service* service))
  (assert (= (fnn-store-lock-fd store) 402))
  (assert (eq (fnn-owner-run-admission) :held))
  (assert (= (length *recorded*) 2))
  (fnn-close *fnn-owner-log-fd*)
  (setq *fnn-owner-log-fd* nil)
  (assert (eq (fnn-owner-store-settlement service settlement) :joined)))
 (assert (null *fnn-owner-retained-service*))
 (assert (null (fnn-store-log store)))
 (assert (null (fnn-store-lock-fd store)))
 (assert (null (fnn-store-completion-pending store)))
 (assert (eq (fnn-owner-run-admission) :start))
 (assert (= (count '(:close 401 nil) *recorded* :test #'equal) 1))
 (assert (= (count '(:close 402 nil) *recorded* :test #'equal) 1))
 (assert (= (count '(:flock 402 8 nil) *recorded* :test #'equal) 1))
 (format t "PASS joined writer, caller defer, actual Store teardown exactly once~%"))
;; A failed record-log close cannot silently count as :closed or erase
;; its actual handle. A lock close fault preserves recovery authority but
;; makes no claim that the already-attempted unlock left the lock held.
(dolist (failing-fd '(503 501 502))
 (let* ((store (make-fnn-store :log (make-fnn-log :fd 501
                   :spare (and (= failing-fd 503) (list 1 "/recording-stage" 503))) :lock-fd 502))
        (service (make-fnn-owner-service :store store))
        (*fnn-owner-retained-service* nil)
        (*fnn-owner-retained-settlement* :held)
        (*fail-close* failing-fd))
  (fnn-owner-claim-run-authority)
  (fnn-owner-retain-run-authority service)
  (assert (eq (fnn-owner-store-settlement service :joined) :held))
  (assert (eq *fnn-owner-retained-service* service))
  (assert (= (fnn-store-lock-fd store) 502))
  (when (member failing-fd '(501 503))
   (assert (= (fnn-log-fd (fnn-store-log store)) 501)))
  (when (= failing-fd 503)
   (assert (equal (fnn-log-spare (fnn-store-log store)) '(1 "/recording-stage" 503))))
  (assert (eq (fnn-owner-run-admission) :held))
  (assert (fnn-store-fenced store))
  ;; Existing continuation carries :held, so it never retries/reuses an
  ;; ambiguously closed descriptor. These are independent recording Stores.
  (let ((count-before (length *recorded*)))
   (assert (eq (fnn-owner-store-settlement service *fnn-owner-retained-settlement*) :held))
   (assert (= count-before (length *recorded*))))))
(format t "PASS physical-close uncertainty preserves handles/recovery authority; no held-lock inference~%")
(format t "STORE-AUTHORITY-PASS ~s~%" (reverse *recorded*))

