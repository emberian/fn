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
                            fn-ocfg-with-read-owner)
                           (fn-ocfg-read-tls-prefix-is-full-read
                               fn-ocri-found-conn-is-carried)))))

(defthm fn-ocri-conns-p-of-remove
  (implies (fn-ocri-conns-p conns)
           (fn-ocri-conns-p (fn-own-remove-conn id conns)))
  :hints (("Goal" :induct (fn-own-remove-conn id conns)
           :in-theory (enable fn-own-remove-conn))))

(defthm fn-ocri-conns-p-of-replace
  (implies (and (fn-ocri-conns-p conns)
                (fn-ocri-connp conn))
           (fn-ocri-conns-p (fn-own-replace-conn conn conns)))
  :hints (("Goal" :induct (fn-own-replace-conn conn conns)
           :in-theory (enable fn-own-replace-conn))))

(defthm fn-ocri-connp-of-reader-context-copy
  (implies (fn-ocri-connp conn)
           (fn-ocri-connp
            (fn-own-conn-make-indexed
             (fn-own-conn-id conn) (fn-own-conn-version conn)
             (fn-own-conn-frontier conn) (fn-own-conn-wire conn)
             session (fn-own-conn-archive conn)
             (fn-own-conn-config conn) (fn-own-conn-observation conn)
             (fn-own-conn-verdicts conn) (fn-own-conn-index conn))))
  :hints (("Goal" :in-theory (enable fn-ocri-connp))))

(defthm fn-ocri-reader-context-preserves-reader-pins
  (implies (fn-ocri-conns-p (fn-own-conns o))
           (fn-ocri-conns-p
            (fn-own-conns (fn-own-reader-context o id cfg))))
  :hints (("Goal" :in-theory (e/d (fn-own-reader-context
                                    fn-own-set-conns)
                                   (fn-ocri-conns-p fn-ocri-connp)))))

(defthm fn-ocri-opened-reader-has-view-pins
  (implies (and (fn-ocri-viewp view)
                (posp line-limit) (posp body-limit))
           (fn-ocri-connp
            (fn-own-conn-make-indexed
             id version frontier
             (fn-wire-initial-state line-limit body-limit)
             session (fn-own-view-archive view) config observation
             (fn-own-view-verdicts view) (fn-own-view-index view))))
  :hints (("Goal"
           :use ((:instance fn-wire-initial-state-is-state))
           :in-theory (enable fn-ocri-connp fn-ocri-viewp))))

(defthm fn-ocri-own-body-limit-positive
  (posp (fn-own-body-limit o))
  :hints (("Goal" :in-theory (enable fn-own-body-limit))))

(defthm fn-ocri-own-open-preserves-reader-pins
  (implies (and (fn-ocri-viewp (fn-own-view o))
                (fn-ocri-conns-p (fn-own-conns o)))
           (fn-ocri-conns-p (fn-own-conns (cdr (fn-own-open o acfg)))))
  :hints (("Goal"
           :use ((:instance fn-ocri-opened-reader-has-view-pins
                            (view (fn-own-view o))
                            (line-limit *fn-nntp-max-initial-line-octets*)
                            (body-limit (fn-own-body-limit o))
                            (id (fn-own-next-id o))
                            (version (fn-own-view-version (fn-own-view o)))
                            (frontier (fn-own-view-frontier (fn-own-view o)))
                            (session (fn-auth-open-session
                                      (fn-own-view-archive (fn-own-view o))
                                      nil nil nil acfg nil))
                            (config (fn-own-config o))
                            (observation (fn-own-clock o))))
           :in-theory (e/d (fn-own-open
                            fn-served-open-indexed
                            fn-ocri-conns-p)
                           (fn-own-body-limit fn-ocri-connp
                            fn-ocri-viewp fn-wire-statep
                            fn-midx-correspondencep
                            fn-sn-verdict-listp)))))

(defthm fn-ocri-own-open-keeps-view
  (equal (fn-own-view (cdr (fn-own-open o acfg)))
         (fn-own-view o))
  :hints (("Goal" :in-theory (enable fn-own-open))))

(defthm fn-ocri-open-preserves-historical-reader-relation
  (implies (fn-ocri-relation oc)
           (fn-ocri-relation (cdr (fn-ocfg-open oc acfg))))
  :hints (("Goal"
           :use (fn-ocl-open-preserves-historical-relation
                 (:instance fn-ocri-own-open-preserves-reader-pins
                            (o (fn-ocfg-owner oc))))
           :in-theory (e/d (fn-ocri-relation fn-ocfg-open)
                           (fn-ocl-relation fn-ocri-viewp
                            fn-ocri-conns-p fn-own-open
                            fn-ocl-open-preserves-historical-relation
                            fn-ocri-own-open-preserves-reader-pins)))))

(defthm fn-ocri-served-step-keeps-valid-wire
  (implies (fn-wire-statep (fn-served-conn-wire conn))
           (fn-wire-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-served-step conn octets)))))
  :hints (("Goal"
           :use ((:instance fn-served-feed-preserves-wire-statep))
           :in-theory (e/d (fn-served-step)
                           (fn-served-feed
                            fn-served-feed-preserves-wire-statep
                            fn-wire-statep)))))

; Read can replace its selected connection or remove it after an invalid
; next session.  Both outcomes retain the historical pin invariant on every
; connection that remains; this theorem does not assume static Store groups.
(defthm fn-ocri-own-read-preserves-reader-pins
  (implies (fn-ocri-conns-p (fn-own-conns o))
           (fn-ocri-conns-p (fn-own-conns (cdr (fn-own-read o id octets)))))
  :hints (("Goal"
           :use ((:instance fn-ocri-found-conn-is-carried
                            (conns (fn-own-conns o))))
           :in-theory (e/d (fn-own-read fn-own-finish-read
                            fn-own-set-conns fn-own-enqueue
                            fn-ocri-connp)
                           (fn-served-step fn-ocri-found-conn-is-carried
                            fn-wire-statep fn-midx-correspondencep
                            fn-sn-verdict-listp)))))

(defthm fn-ocri-own-read-keeps-view
  (equal (fn-own-view (cdr (fn-own-read o id octets)))
         (fn-own-view o))
  :hints (("Goal" :in-theory (enable fn-own-read fn-own-finish-read
                                     fn-own-set-conns fn-own-enqueue))))

(defthm fn-ocri-read-preserves-added-reader-invariants
  (implies
   (and (fn-ocri-relation oc)
        (fn-ocl-relation (cdr (fn-ocfg-read oc id octets))))
   (fn-ocri-relation (cdr (fn-ocfg-read oc id octets))))
  :hints (("Goal"
           :use ((:instance fn-ocri-own-read-preserves-reader-pins
                            (o (fn-ocfg-owner oc))))
           :in-theory (e/d (fn-ocri-relation fn-ocfg-read
                            fn-ocfg-with-read-owner)
                           (fn-ocl-relation
                            fn-ocri-own-read-preserves-reader-pins
                            fn-own-read fn-ocri-conns-p fn-ocri-viewp)))))
