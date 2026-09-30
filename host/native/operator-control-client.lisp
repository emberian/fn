;;; Shared operator administration client; no NNTP or POST service.
;;; ACL2 chooses liveness, the FNCT grammar and the outcome vocabulary.
(in-package "ACL2")

(defun fnn-operator-status-detail (status word)
  "STATUS, then the reason word ACL2 says the operator's line carries
(fn-native-control-reply-detail, PKT-453 (a)): its octets, not a host word."
  (let ((detail (and word (fnn-core 'fn-native-control-host-reply-detail status word))))
    (if (fnn-octet-list-p detail)
        (format nil "~a ~a" status (fnn-octets-string (fnn-octets detail)))
      status)))

(defun fnn-operator-live-socket-present (control-path)
  (fnn-control-socket-path-p (fnn-lstat (fnn-octets-string control-path))))

(defun fnn-operator-live-admin-observe (root control-path-list queryp)
  "PKT-344: two observations, ACL2's decision (fn-native-control-liveness-decides):
a socket node with the lock free or absent is a crashed owner's (:stale), and
only a free or absent lock starts the offline executor.  A :stale node is
removed under the control-path lease; a query does not use the :held arm (the
read-only executor's own shared lock answers it), so it prints only the
:stale note."
  (let* ((socket-path (and (fnn-octet-list-p control-path-list)
                           (consp control-path-list)
                           (fnn-octets control-path-list)))
         (liveness (fnn-core 'fn-native-control-host-liveness
                             (and socket-path
                                  (fnn-operator-live-socket-present socket-path)
                                  t)
                             (fnn-store-owner-observation root)))
         (note (fnn-core 'fn-native-control-host-liveness-note liveness)))
    (when (eq liveness :stale)
      (fnn-control-remove-stale-offline socket-path))
    (when (and (stringp note) (or (not queryp) (eq liveness :stale)))
      (fnn-err "~a" note))
    liveness))

(defun fnn-operator-live-admin (control-path argv liveness)
  "The exit code and detail of an administrative vector: the live owner's
answer (:live), or the refusal of a store whose lock an owner holds (:held)."
  (if (eq liveness :held)
      (values (fnn-core 'fn-native-control-host-status-exit-code :refused) nil)
    (multiple-value-bind (status word line)
        (fnn-control-admin control-path argv)
      ;; Row S1: a reply that carries the owner's line (a limit decision,
      ;; books/native-control-line.lisp kind 23) prints that line, ACL2's
      ;; octets (fn-native-control-printed-line-is-the-decisions).
      ;; A reply with no line (LINE nil: every refusal that names only its
      ;; word, PKT-453 (a)) prints the word.  NIL is an octet list (the
      ;; empty one), so the test is for a line with octets, never for an
      ;; octet list: `control revoke' printed `REFUSED ' and no word
      ;; (BF's 48-module run at 444fb9f41, test_native_control).
      (let ((printed (and (consp line)
                          (fnn-core 'fn-native-control-host-lined-detail
                                    (list :status status word line))))
            (detail (fnn-operator-status-detail status word)))
        (values (fnn-core 'fn-native-control-host-status-exit-code status)
                (cond ((consp printed)
                       (format nil "~a ~a" status (fnn-octets-string (fnn-octets printed))))
                      ((not (eq detail status)) detail)))))))

(defun fnn-operator-live-request (control-path argv)
  "PKT-868: an administrative vector the live owner answers with a word of
its own state (the compaction request): the exit code of ACL2's status, and
the word printed as ACL2 rendered it (the reply detail names only refusals)."
  (multiple-value-bind (status word) (fnn-control-admin control-path argv)
    ;; The request's own first word names it ("compaction requested",
    ;; "reclaim requested"); ACL2 decides the word printed after it: the
    ;; owner's, else the status's name ("reclaim fault", never "reclaim
    ;; NONE" beside exit FAULT; books/control-request-word.lisp).
    (when (and (fnn-octet-list-p word) (consp argv) (fnn-octet-list-p (first argv)))
      (let ((printed (fnn-core 'fn-crqw-request-word status word)))
        (unless (fnn-octet-list-p printed)
          (fnn-fault "ACL2 returned a malformed request word"))
        (fnn-out "~a ~a" (fnn-octets-string (fnn-octets (first argv)))
                 (fnn-octets-string (fnn-octets printed)))))
    (fnn-core 'fn-native-control-host-status-exit-code status)))
