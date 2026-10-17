;;; MEM-003: the collection while the owner is idle.  SBCL returns freed pages
;;; to the OS only after a collection of a generation above 1, and the nursery
;;; trigger's collections are generation 0 and 1, so a burst's garbage stays
;;; resident until something collects higher.  ACL2 decides when
;;; (books/idle-collection.lisp fn-idle-gc-quiet, fn-idle-gc-decide); this
;;; observes the two facts the decision reads and makes the one call it
;;; names.  The marks are the allocation counter at the previous tick and at
;;; the last collection; the first tick takes the current counter for both
;;; (the open's own full collection is the last one before it).
(defvar *fnn-idle-gc-tick-mark* nil)
(defvar *fnn-idle-gc-collect-mark* nil)
(defvar *fnn-idle-gc-quiet* 0)

(defun fnn-owner-maybe-collect-idle (service)
  (let* ((consed (sb-ext:get-bytes-consed))
         (publishing (fnn-with-roster (service)
                       (and (or (fnn-owner-service-publisher service)
                                (fnn-owner-service-exporter service))
                            t))))
    (unless *fnn-idle-gc-tick-mark*
      (setq *fnn-idle-gc-tick-mark* consed
            *fnn-idle-gc-collect-mark* consed))
    (setq *fnn-idle-gc-quiet*
          (fnn-core 'fn-idle-gc-quiet *fnn-idle-gc-quiet* publishing
                    (- consed *fnn-idle-gc-tick-mark*))
          *fnn-idle-gc-tick-mark* consed)
    (let ((verdict (fnn-core 'fn-idle-gc-decide *fnn-idle-gc-quiet* publishing
                             (- consed *fnn-idle-gc-collect-mark*))))
      (when (consp verdict)
        (sb-ext:gc :gen (second verdict))
        (setq *fnn-idle-gc-tick-mark* (sb-ext:get-bytes-consed)
              *fnn-idle-gc-collect-mark* *fnn-idle-gc-tick-mark*)))))
