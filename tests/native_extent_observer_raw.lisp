;;; Actual SBCL mutex/thread and deployed extent event transport only.
;;; No fn semantics are stubbed or interpreted here. Full PageIO replay still
;;; needs wait/P/other O edges and matching model/image dependencies.
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
                     '(*fnn-native-observer* *fnn-native-actor-identity* fnn-with-observed-mutex))
(load-observer-forms "host/native/extent.lisp" '(fnn-extent-native-observe))
;; The absent collector must not evaluate observer-only arguments or resolve
;; any late-loaded owner callback, even before owner.lisp has loaded.
(fnn-extent-native-observe :issue t (error "inactive event evaluated"))
(let ((mutex (sb-thread:make-mutex)))
  (assert (equal (multiple-value-list (fnn-with-observed-mutex (mutex :extent) (values 1 2))) '(1 2))))
(load-observer-forms "host/native/owner.lisp"
                     '(fnn-native-observation-row fnn-native-observation
                       fnn-native-observation-create fnn-native-reserve-thread-identity
                       fnn-native-observed-thread-thunk fnn-native-observation-reserve
                       fnn-native-observe fnn-native-observation-complete fnn-native-observation-events))
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
