; Proof-only reader invariant for live configuration histories.  This keeps
; every connection's wire and lookup projection with its own historical
; archive, not the current Store's final domain or current article set.
(in-package "ACL2")
(include-book "config-owner-live")
(include-book "owner-tls-prefix")

(defun fn-ocri-connp (conn)
  (declare (xargs :guard t))
  (and (fn-wire-statep (fn-own-conn-wire conn))
       (fn-midx-correspondencep
        (fn-own-conn-index conn)
        (fn-state-articles (fn-own-conn-archive conn)))
       (fn-sn-verdict-listp (fn-own-conn-verdicts conn))))

(defun fn-ocri-conns-p (conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (and (fn-ocri-connp (car conns))
           (fn-ocri-conns-p (cdr conns)))
    (null conns)))

(defun fn-ocri-viewp (view)
  (declare (xargs :guard t))
  (and (fn-midx-correspondencep
        (fn-own-view-index view)
        (fn-state-articles (fn-own-view-archive view)))
       (fn-sn-verdict-listp (fn-own-view-verdicts view))))

(defun fn-ocri-relation (oc)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (and (fn-ocl-relation oc)
         (fn-ocri-viewp (fn-own-view o))
         (fn-ocri-conns-p (fn-own-conns o)))))

(defthm fn-ocri-found-conn-is-carried
  (implies (and (fn-ocri-conns-p conns)
                (fn-own-find-conn id conns))
           (fn-ocri-connp (fn-own-find-conn id conns)))
  :hints (("Goal" :induct (fn-ocri-conns-p conns)
           :in-theory (enable fn-own-find-conn))))

; The outer function is the one host/owner-host.lisp calls on each socket
; chunk.  Historical replay and exact per-connection pins establish the
; selected wire premise of the direct counted/full equivalence theorem.
(defthm fn-ocri-host-tls-read-refines-historical-read
  (implies
   (fn-ocri-relation oc)
   (let ((tls (fn-ocfg-read-tls-prefix oc id octets))
         (full (fn-ocfg-read oc id octets)))
     (and (equal (fn-own-tls-result-effects tls) (car full))
          (equal (fn-own-tls-result-owner tls) (cdr full)))))
  :hints (("Goal"
           :cases ((fn-own-find-conn id
                                      (fn-own-conns (fn-ocfg-owner oc))))
           :use ((:instance fn-ocri-found-conn-is-carried
                            (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-ocfg-read-tls-prefix-is-full-read))
           :in-theory (e/d (fn-ocfg-read-tls-prefix
                            fn-own-read-tls-prefix fn-ocfg-read fn-own-read
                            fn-own-tls-make-result
                            fn-own-tls-result-consumed
                            fn-own-tls-result-effects
                            fn-own-tls-result-owner
                            fn-ocfg-with-owner)
                           (fn-ocfg-read-tls-prefix-is-full-read
                               fn-ocri-found-conn-is-carried)))))
