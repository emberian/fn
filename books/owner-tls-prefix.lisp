; fn: the ACL2-owned receive prefix for an owner STARTTLS transition.
;
; The physical adapter observes bytes with MSG_PEEK, calls this transition
; once, then consumes exactly fn-own-tls-result-consumed bytes.  The owner
; state and effects are those of fn-ocfg-read on the entire observation;
; bytes after the count belong to the TLS record layer.

(in-package "ACL2")
(include-book "owner-config")
(include-book "served-tls-prefix")

(defun fn-own-tls-served-conn (o conn)
  (declare (xargs :guard t))
  (fn-served-make-conn (fn-own-conn-wire conn)
                       (fn-own-conn-live-session o conn)
                       (fn-own-conn-archive conn)
                       (fn-own-conn-config conn)
                       (fn-own-conn-observation conn)
                       (fn-own-clock o)))

(defun fn-own-tls-consumed (o id octets)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (fn-served-tls-consumed (fn-own-tls-served-conn o conn) octets)
      (len octets))))

; (:fn-own-tls-result consumed effects configured-owner).
(defun fn-own-tls-make-result (consumed result)
  (declare (xargs :guard t))
  (list :fn-own-tls-result consumed (fn-ag-car result) (fn-ag-cdr result)))

(defun fn-own-tls-result-consumed (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr result)))

(defun fn-own-tls-result-effects (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))

(defun fn-own-tls-result-owner (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))

(defun fn-ocfg-read-tls-prefix (oc id octets)
  (declare (xargs :guard (fn-wire-octet-listp octets)))
  (let* ((consumed (fn-own-tls-consumed (fn-ocfg-owner oc) id octets))
         (result (fn-ocfg-read oc id (take consumed octets))))
    (fn-own-tls-make-result consumed result)))

(defthm fn-own-tls-consumed-is-bounded
  (<= (fn-own-tls-consumed o id octets) (len octets))
  :rule-classes :linear)

; The actual host-call transition returns exactly fn-ocfg-read's effects and
; configured-owner state.  This is the correspondence that permits the raw
; socket layer to leave the suffix unread without changing NNTP semantics.
(defthm fn-ocfg-read-tls-prefix-is-full-read
  (let ((tls-result (fn-ocfg-read-tls-prefix oc id octets))
        (full-result (fn-ocfg-read oc id octets)))
    (and (equal (fn-own-tls-result-effects tls-result)
                (car full-result))
         (equal (fn-own-tls-result-owner tls-result)
                (cdr full-result))))
  :hints (("Goal"
           :cases ((fn-own-find-conn id
                                     (fn-own-conns (fn-ocfg-owner oc))))
           :use ((:instance fn-served-step-of-tls-consumed-prefix
                            (conn
                             (fn-own-tls-served-conn
                              (fn-ocfg-owner oc)
                              (fn-own-find-conn
                               id (fn-own-conns (fn-ocfg-owner oc)))))))
           :in-theory (e/d (fn-ocfg-read-tls-prefix
                            fn-own-tls-make-result
                            fn-own-tls-result-effects
                            fn-own-tls-result-owner
                            fn-own-tls-consumed
                            fn-ocfg-read
                            fn-own-read)
                           (fn-served-step
                            fn-served-step-of-tls-consumed-prefix)))))
