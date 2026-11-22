;;; Test-only process-death coordinate. Observe the actual peer actor before
;;; it executes its separate checkpoint arm. No observer enters the image
;;; launcher or its certified worlds.
(in-package "ACL2")
(require :sb-posix)

(defvar *fn2-peer-cut-mode*
  (or (sb-ext:posix-getenv "FN2_TEST_PEER_CUT_MODE")
      (error "Missing peer cut mode.")))
(unless (member *fn2-peer-cut-mode* '("kill" "observe") :test #'string=)
  (error "Invalid peer cut mode."))

(defvar *fn2-peer-cut-run* (symbol-function 'fn2-peer-pull-run))
(defvar *fn2-peer-cut-baseline* nil)
(defvar *fn2-peer-cut-reached* nil)

(defun fn2-peer-cut-frontier (core)
  (multiple-value-bind (code published) (fn2-read-frontier core)
    (unless (eq code :ok) (error "No settled publication frontier at peer cut."))
    published))

(setf (symbol-function 'fn2-peer-pull-run)
  (lambda (id budget core)
    (when (and (not *fn2-peer-cut-reached*)
               (eq (fn2-peer-pull-snapshot-read-code id core) :ok))
      (let ((phase (fn2-peer-pull-row-phase id core))
            (generation (fn2-machine-generation id core)))
        (when (and (equal phase *fn2-peer-pull-state-connect*) (not *fn2-peer-cut-baseline*))
          (setf *fn2-peer-cut-baseline* (list id generation (fn2-peer-cut-frontier core))))
        (when (and (equal phase *fn2-peer-pull-state-checkpoint*)
                   (equal (fn2-peer-pull-row-import-step id core) 0)
                   (equal (fn2-peer-pull-row-import-left id core) 0)
                   (< (fn2-peer-pull-row-resume-position id core)
                      (fn2-peer-pull-row-import-next id core)))
          (destructuring-bind (actor gen baseline) *fn2-peer-cut-baseline*
            (let* ((published (fn2-peer-cut-frontier core))
                   (killing (string= *fn2-peer-cut-mode* "kill")))
              (unless (and (= actor id) (= gen generation)
                           (= (fn2-peer-pull-row-import-count id core) 1)
                           (= (fn2-peer-pull-row-import-absent id core) 1)
                           (if killing (< baseline published) (= baseline published)))
                (error "Peer cut did not distinguish new settlement from unchanged retry."))
              (setf *fn2-peer-cut-reached* t)
              ;; Numeric coordinates only. No RX/TX, credentials or source
              ;; body are copied. The original checkpoint arm has not run.
              (format t "~%PEER-POSITION-CUT ~d ~d ~d ~d ~d ~d ~d ~d ~d ~d~%"
                      id generation baseline published
                      (fn2-peer-pull-row-consumer id core)
                      (fn2-peer-pull-row-remote-history id core)
                      (fn2-peer-pull-row-remote-incarnation id core)
                      (fn2-peer-pull-row-remote-view id core)
                      (fn2-peer-pull-row-resume-position id core)
                      (fn2-peer-pull-row-import-next id core))
              (finish-output)
              (when killing
                (sb-posix:kill (%fn2-native-getpid) sb-posix:sigkill)))))))
    (funcall *fn2-peer-cut-run* id budget core)))
