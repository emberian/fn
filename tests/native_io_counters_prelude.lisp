;;; The deployed per-request I/O counters (host/native/io.lisp), read from the
;;; source for harnesses that load host/native/trace.lisp without io.lisp.
(require :sb-posix)
(require :sb-bsd-sockets)
(in-package "ACL2")
(with-open-file (stream "host/native/io.lisp")
  (loop for form = (read stream nil :eof)
        until (eq form :eof)
        when (and (consp form)
                  (or (equal (list (car form) (cadr form))
                             '(defstruct (fnn-io-counters (:constructor %make-fnn-io-counters))))
                      (member (list (car form) (cadr form))
                              '((defvar *fnn-io-counters*) (defmacro fnn-io-count)) :test #'equal)))
          do (eval form)))
