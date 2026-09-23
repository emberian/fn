; fn: one-pass configured-owner receive with physical prefix ownership.
;
; The native host calls fn-ocfg-read-tls-prefix once per observed socket
; region.  It lifts fn-served-step-counted through the same fn-own-finish-read
; bookkeeping as fn-own-read, so framing, dispatch and owner mutation execute
; once while the host also receives the exact physical prefix count.

(in-package "ACL2")
(include-book "owner-config")
(include-book "served-tls-prefix")

; (:fn-own-tls-result consumed effects configured-owner).
(defun fn-own-tls-make-result (consumed effects owner)
  (declare (xargs :guard t))
  (list :fn-own-tls-result consumed effects owner))

(defun fn-own-tls-result-consumed (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr result)))

(defun fn-own-tls-result-effects (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))

(defun fn-own-tls-result-owner (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))

(defun fn-own-tls-served-conn (o conn)
  (declare (xargs :guard t))
  (fn-served-make-conn-group-indexed (fn-own-conn-wire conn)
                              (fn-own-conn-live-session o conn)
                              (fn-own-conn-archive conn)
                              (fn-own-conn-config conn)
                              (fn-own-conn-observation conn)
                              (fn-own-clock o)
                              (fn-own-conn-verdicts conn)
                              (fn-own-conn-index conn)
                              (fn-own-conn-group-index conn)))

(defthm fn-own-tls-served-conn-keeps-reader-pins
  (and (equal (fn-served-conn-verdicts (fn-own-tls-served-conn o conn))
              (fn-own-conn-verdicts conn))
       (equal (fn-served-conn-index (fn-own-tls-served-conn o conn))
              (fn-own-conn-index conn)))
  :hints (("Goal" :in-theory (enable fn-own-tls-served-conn))))

(defun fn-own-read-tls-prefix (o id octets)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((counted
                 (fn-served-step-counted-fast
                  (fn-own-tls-served-conn o conn) octets))
               (result
                 (fn-own-finish-read
                  o conn (fn-served-counted-result counted))))
          (fn-own-tls-make-result
           (fn-served-counted-consumed counted) (car result) (cdr result)))
      (fn-own-tls-make-result (len octets) nil o))))

(defun fn-ocfg-read-tls-prefix (oc id octets)
  (declare (xargs :guard (fn-wire-octet-listp octets)))
  (let ((result (fn-own-read-tls-prefix (fn-ocfg-owner oc) id octets)))
    (fn-own-tls-make-result
     (fn-own-tls-result-consumed result)
     (fn-own-tls-result-effects result)
     (fn-ocfg-with-owner oc (fn-own-tls-result-owner result)))))

(defthm fn-own-read-tls-prefix-consumed-is-bounded
  (<= (fn-own-tls-result-consumed
       (fn-own-read-tls-prefix o id octets))
      (len octets))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable fn-own-read-tls-prefix
                              fn-own-tls-make-result
                              fn-own-tls-result-consumed)
           :use ((:instance fn-served-step-counted-fast-consumed-is-bounded
                            (conn
                             (fn-own-tls-served-conn
                              o (fn-own-find-conn id (fn-own-conns o)))))))))

; The actual host-call transition returns exactly fn-ocfg-read's effects and
; configured-owner state.  The counted transition is a single execution;
; this theorem relates its result to the pre-existing semantic entry point.
; The wire hypothesis is the domain `fn-served-step-counted-fast-is-reference'
; (books/served-tls-prefix).  Carrying it through the historical configured-owner
; relation remains a separate proof obligation; the static `fn-ocfg-statep'
; is not a valid premise after a live domain or capacity change.
(defthm fn-ocfg-read-tls-prefix-is-full-read
  (implies
   (fn-wire-statep
    (fn-own-conn-wire
     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
   (let ((tls-result (fn-ocfg-read-tls-prefix oc id octets))
         (full-result (fn-ocfg-read oc id octets)))
     (and (equal (fn-own-tls-result-effects tls-result)
                 (car full-result))
          (equal (fn-own-tls-result-owner tls-result)
                 (cdr full-result)))))
  :hints (("Goal"
           :in-theory (enable fn-ocfg-read-tls-prefix
                              fn-own-read-tls-prefix
                              fn-own-tls-make-result
                              fn-own-tls-result-consumed
                              fn-own-tls-result-effects
                              fn-own-tls-result-owner
                              fn-ocfg-read
                              fn-own-read
                              fn-own-tls-served-conn)
           :use ((:instance fn-served-step-counted-fast-is-reference
                            (conn
                             (fn-own-tls-served-conn
                              (fn-ocfg-owner oc)
                              (fn-own-find-conn
                               id (fn-own-conns (fn-ocfg-owner oc))))))
                 (:instance fn-served-step-counted-result-is-step
                            (conn
                             (fn-own-tls-served-conn
                              (fn-ocfg-owner oc)
                              (fn-own-find-conn
                               id (fn-own-conns (fn-ocfg-owner oc))))))))))

(in-theory (disable fn-own-tls-make-result
                    fn-own-tls-result-consumed
                    fn-own-tls-result-effects
                    fn-own-tls-result-owner
                    fn-own-tls-served-conn
                    fn-own-read-tls-prefix
                    fn-ocfg-read-tls-prefix))
