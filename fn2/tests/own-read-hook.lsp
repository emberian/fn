; Raw Common Lisp acceptance instrumentation, loaded after ACL2's :q and LD.
; No served definition or logical event changes. Only the scenario-bound
; concrete core is observed; the separately allocated reference core is not.
; R6: every new range-read primitive must report its examined range here too.
(in-package "ACL2")
(defvar *fn2-own-hook-originals* nil)
(defvar *fn2-own-hook-core* nil)
(defvar *fn2-own-hook-monitor* nil)
(defvar *fn2-own-hook-read-original* nil)
(defvar *fn2-own-hook-reads* (make-hash-table))

(defun fn2-own-hook-reset ()
  (clrhash *fn2-own-hook-reads*))

(defun fn2-own-hook-read (slot gen index kind owner owner-gen core)
  (multiple-value-bind (code byte)
      (funcall *fn2-own-hook-read-original* slot gen index kind owner owner-gen core)
    (when (eq core *fn2-own-hook-core*)
      (assert *fn2-own-hook-monitor*)
      (incf (gethash kind *fn2-own-hook-reads* 0))
      (fn2-own-observe-read slot gen index code byte core *fn2-own-hook-monitor*))
    (values code byte)))

(defun fn2-own-hook-install ()
  (assert (null *fn2-own-hook-originals*))
  ; fn2-own-check-trace-turn is the A4 scenarios' (echo-scenario.lisp); a
  ; driver without it (D's sim-layer-d) binds the core and monitor itself.
  (dolist (name '(fn2-core-read fn2-core-write fn2-own-check-trace-turn))
    (when (fboundp name)
      (push (cons name (symbol-function name)) *fn2-own-hook-originals*)))
  (setf *fn2-own-hook-read-original* (symbol-function 'fn2-core-read)
        (symbol-function 'fn2-core-read) #'fn2-own-hook-read)
  (let ((turn (cdr (assoc 'fn2-own-check-trace-turn *fn2-own-hook-originals*)))
        (write-byte (cdr (assoc 'fn2-core-write *fn2-own-hook-originals*))))
    (when turn
      (setf (symbol-function 'fn2-own-check-trace-turn)
            (lambda (profile cursor queues core own reference)
              (let ((*fn2-own-hook-core* core) (*fn2-own-hook-monitor* own))
                (funcall turn profile cursor queues core own reference)))))
    (setf (symbol-function 'fn2-core-write)
          (lambda (slot gen index byte kind owner owner-gen core)
            (multiple-value-bind (code core)
                (funcall write-byte slot gen index byte kind owner owner-gen core)
              ; A legitimate scribe refill supersedes old received provenance.
              (when (eq core *fn2-own-hook-core*)
                (fn2-own-observe-core-write slot gen index code byte core
                                            *fn2-own-hook-monitor*))
              (values code core)))))
  (fn2-own-hook-reset))

(defun fn2-own-hook-restore ()
  (dolist (entry *fn2-own-hook-originals*)
    (setf (symbol-function (car entry)) (cdr entry)))
  (setf *fn2-own-hook-originals* nil *fn2-own-hook-read-original* nil))

(defun fn2-own-hook-report (label &optional require-scribe)
  (when require-scribe
    (assert (plusp (gethash *fn2-scribe-kind* *fn2-own-hook-reads* 0))))
  (format t "OWN READS ~A listener=~D echo/null=~D scribe=~D total=~D~%"
          label
          (gethash *fn2-listener-kind* *fn2-own-hook-reads* 0)
          (gethash *fn2-echo-kind* *fn2-own-hook-reads* 0)
          (gethash *fn2-scribe-kind* *fn2-own-hook-reads* 0)
          (loop for n being the hash-values of *fn2-own-hook-reads* sum n)))

; Mutate the raw read result, not the monitor: even when a broken reader
; claims :ok, the same installed hook must reject past-fill and leased-in.
; A legal positive and a separate-core exclusion control precede the faults.
(defun fn2-own-hook-control ()
  (assert *fn2-own-hook-originals*)
  (let* ((core (create-fn2-core)) (own (create-fn2-own))
         (*fn2-own-hook-core* core) (*fn2-own-hook-monitor* own))
    (fn2-core-init *fn2-profile-tiny* core)
    (fn2-own-init *fn2-profile-tiny* own)
    (multiple-value-bind (code slot gen) (fn2-core-reserve 0 1 0 1 core)
      (assert (eq code :ok))
      (assert (eq (fn2-core-write slot gen 0 99 1 0 1 core) :ok))
      (multiple-value-bind (code byte) (fn2-core-read slot gen 0 1 0 1 core)
        (assert (and (eq code :ok) (= byte 99) (eq (fn2-own-status own) :pass))))
      (let ((*fn2-own-hook-core* (create-fn2-core))
            (before (gethash 1 *fn2-own-hook-reads* 0)))
        (fn2-core-read slot gen 0 1 0 1 core)
        (assert (= before (gethash 1 *fn2-own-hook-reads* 0))))
      (assert (not (eq (fn2-core-read slot gen 1 1 0 1 core) :ok)))
      (assert (eq (fn2-own-status own) :pass))
      (let ((*fn2-own-hook-read-original*
              (lambda (&rest args) (declare (ignore args)) (values :ok 99))))
        (fn2-core-read slot gen 1 1 0 1 core)
        (assert (equal (fn2-own-status own) '(:fail :unreadable-input))))
      (update-fn2-own-error 0 own)
      (assert (eq (fn2-core-reset slot gen 1 0 1 core) :ok))
      (assert (eq (fn2-pool-lease-in slot gen 1 0 1 1 0 1 (fn2-core-pool core)) :ok))
      (assert (not (eq (fn2-core-read slot gen 0 1 0 1 core) :ok)))
      (assert (eq (fn2-own-status own) :pass))
      (let ((*fn2-own-hook-read-original*
              (lambda (&rest args) (declare (ignore args)) (values :ok 99))))
        (fn2-core-read slot gen 0 1 0 1 core)
        (assert (equal (fn2-own-status own) '(:fail :unreadable-input))))))
  (format t "OWN READ HOOK CONTROLS legal=PASS separate-core=PASS real-refusals=PASS past-fill=REJECTED leased-in=REJECTED~%")
  (fn2-own-hook-reset))
