;;; Actual SBCL mutex/thread and deployed extent event transport only.
;;; No fn semantics are stubbed or interpreted here. Full PageIO replay still
;;; needs P/other O edges and matching model/source dependencies.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(defpackage "ACL2_*1*_ACL2" (:use "CL"))
(in-package "ACL2")
(defun load-observer-forms (path wanted)
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof) until (eq form :eof)
            for name = (and (consp form) (if (consp (cadr form)) (caadr form) (cadr form)))
            when (member name wanted)
              do (eval form) (setf missing (remove name missing))))
    (when missing (error "Missing actual observer forms: ~s" missing))))
(load-observer-forms "host/native/io.lisp"
                     '(*fnn-native-observer* *fnn-native-actor-identity* *fnn-native-wait-release*
                       fnn-with-observed-mutex fnn-observed-condition-wait))
(load-observer-forms "host/native/extent.lisp" '(fnn-extent-native-observe))
;; The absent collector must not evaluate observer-only arguments or resolve
;; any late-loaded owner callback, even before owner.lisp has loaded.
(fnn-extent-native-observe :issue t (error "inactive event evaluated"))
(let ((mutex (sb-thread:make-mutex)))
  (assert (equal (multiple-value-list (fnn-with-observed-mutex (mutex :extent) (values 1 2))) '(1 2))))
;; Inactive timeout also works before any owner collector function is loaded.
(let ((mutex (sb-thread:make-mutex)) (queue (sb-thread:make-waitqueue)))
  (fnn-with-observed-mutex (mutex :extent)
    (assert (null (fnn-observed-condition-wait queue mutex :extent :timeout 0.001)))))
(load-observer-forms "host/native/owner.lisp"
                     '(fnn-native-observation-row fnn-native-observation
                       fnn-native-observation-create fnn-native-reserve-thread-identity
                       fnn-native-observed-thread-thunk fnn-native-observation-reserve
                       fnn-native-observe fnn-native-observation-complete fnn-native-observation-unavailable
                       fnn-native-observation-events))
(let* ((*fnn-native-observer* (fnn-native-observation-create 16))
       (mutex (sb-thread:make-mutex)) (measured-identity nil)
       (thread (sb-thread:make-thread
                (fnn-native-observed-thread-thunk
                 (lambda ()
                   (setf measured-identity *fnn-native-actor-identity*)
                   (fnn-with-observed-mutex (mutex :extent :wait-p t)
                     (assert (sb-thread:holding-mutex-p mutex))
                     ;; Literal transport fixture, not an actual fn read or model verdict.
                     (fnn-extent-native-observe :job-result t '(opaque-token) :read)))))))
  (sb-thread:join-thread thread)
  (multiple-value-bind (status events reason) (fnn-native-observation-events *fnn-native-observer*)
    (assert (eq status :complete)) (assert (null reason))
    (assert (stringp measured-identity))
    (assert (equal events (list (list :acquire measured-identity :extent)
                               (list :job-result measured-identity '(opaque-token) :read)
                               (list :release measured-identity :extent))))
    (format t "EXTENT-TRANSPORT ~s~%FULL-PAGEIO-COMPARISON :UNAVAILABLE~%" events)))
;; Unknown native thread identity cannot acquire a comparable event by alias.
(let ((*fnn-native-observer* (fnn-native-observation-create 2)) (*fnn-native-actor-identity* nil))
  (fnn-extent-native-observe :close t 1)
  (multiple-value-bind (status events reason) (fnn-native-observation-events *fnn-native-observer*)
    (assert (eq status :unavailable)) (assert (null events)) (assert (eq reason :identity-unavailable))))
;;; A real wait releases E before the competing actor acquires it. The
;;; release record remains reserved until the waiting primitive returns.
(let* ((*fnn-native-observer* (fnn-native-observation-create 16))
       (*fnn-native-actor-identity* (symbol-name (fnn-native-reserve-thread-identity)))
       (mutex (sb-thread:make-mutex)) (queue (sb-thread:make-waitqueue))
       (ready (sb-thread:make-semaphore)) (wait-id nil) (wait-result nil)
       (thread (sb-thread:make-thread
                (fnn-native-observed-thread-thunk
                 (lambda ()
                   (setq wait-id *fnn-native-actor-identity*)
                   (fnn-with-observed-mutex (mutex :extent)
                     (sb-thread:signal-semaphore ready)
                     (setq wait-result (fnn-observed-condition-wait queue mutex :extent))
                     (assert (sb-thread:holding-mutex-p mutex))))))))
  (sb-thread:wait-on-semaphore ready)
  (fnn-with-observed-mutex (mutex :extent)
    (multiple-value-bind (status events reason) (fnn-native-observation-events *fnn-native-observer*)
      (assert (eq status :pending)) (assert (null reason))
      (assert (equal events (list (list :acquire wait-id :extent)))))
    (sb-thread:condition-notify queue))
  (sb-thread:join-thread thread)
  (assert wait-result)
  (multiple-value-bind (status events reason) (fnn-native-observation-events *fnn-native-observer*)
    (assert (eq status :complete)) (assert (null reason))
    (assert (equal events
                   (list (list :acquire wait-id :extent) (list :release wait-id :extent)
                         (list :acquire *fnn-native-actor-identity* :extent)
                         (list :release *fnn-native-actor-identity* :extent)
                         (list :acquire wait-id :extent) (list :release wait-id :extent))))))
;; The timed wait actually returns without ownership. Exactly one release
;; appears; no final unlock or reacquisition is fabricated by the envelope.
(let ((*fnn-native-observer* (fnn-native-observation-create 8))
      (*fnn-native-actor-identity* (symbol-name (fnn-native-reserve-thread-identity)))
      (mutex (sb-thread:make-mutex)) (queue (sb-thread:make-waitqueue)))
  (fnn-with-observed-mutex (mutex :extent)
    (assert (null (fnn-observed-condition-wait queue mutex :extent :timeout 0.01)))
    (assert (not (sb-thread:holding-mutex-p mutex))))
  (multiple-value-bind (status events reason) (fnn-native-observation-events *fnn-native-observer*)
    (assert (eq status :complete)) (assert (null reason))
    (assert (equal events (list (list :acquire *fnn-native-actor-identity* :extent)
                               (list :release *fnn-native-actor-identity* :extent))))))
;; A real pre-release primitive error is preserved; its reserved release is
;; never presented as a valid physical schedule.
(let ((*fnn-native-observer* (fnn-native-observation-create 8))
      (*fnn-native-actor-identity* (symbol-name (fnn-native-reserve-thread-identity)))
      (mutex (sb-thread:make-mutex)))
  (assert (handler-case
              (progn (fnn-with-observed-mutex (mutex :extent)
                       (fnn-observed-condition-wait nil mutex :extent)) nil)
            (type-error () t)))
  (multiple-value-bind (status events reason) (fnn-native-observation-events *fnn-native-observer*)
    (assert (eq status :unavailable)) (assert (null events))
    (assert (eq reason :wait-observation-escaped))))
;; An uninstrumented timeout cannot silently invent a held-lock schedule.
(let ((*fnn-native-observer* (fnn-native-observation-create 8))
      (*fnn-native-actor-identity* (symbol-name (fnn-native-reserve-thread-identity)))
      (mutex (sb-thread:make-mutex)) (queue (sb-thread:make-waitqueue)))
  (fnn-with-observed-mutex (mutex :extent)
    (sb-thread:condition-wait queue mutex :timeout 0.01))
  (multiple-value-bind (status events reason) (fnn-native-observation-events *fnn-native-observer*)
    (assert (eq status :unavailable)) (assert (null events))
    (assert (eq reason :unobserved-unlock))))
(format t "EXTENT WAIT OBSERVATION PASS: actual contested release/reacquire, timeout, escaped primitive, missing seam~%")
