; The historical ADVANCE relation also carries the reader's immutable
; wire state, recorded verdicts and archive-relative lookup projection.
(in-package "ACL2")
(include-book "config-owner-advance-invariants")
(include-book "config-owner-read-invariants")

(defthm fn-ocari-repinned-connection-has-reader-pins
  (implies
   (and (fn-ocri-connp conn)
        (fn-ocri-viewp view))
   (fn-ocri-connp
    (fn-own-conn-make-group-indexed
     (fn-own-conn-id conn)
     (fn-own-view-version view)
     (fn-own-view-frontier view)
     (fn-own-conn-wire conn)
     session
     (fn-own-view-archive view)
     (fn-own-conn-config conn)
     (fn-own-conn-observation conn)
     (fn-own-view-verdicts view)
     (fn-own-view-index view)
     (fn-own-view-group-index view))))
  :hints (("Goal" :in-theory (enable fn-ocri-connp fn-ocri-viewp))))

(defthm fn-ocari-owner-advance-preserves-reader-pins
  (implies
   (and (fn-ocri-viewp (fn-own-view o))
        (fn-ocri-conns-p (fn-own-conns o)))
   (fn-ocri-conns-p
    (fn-own-conns (cdr (fn-own-advance-result o id)))))
  :hints
  (("Goal"
    :use ((:instance fn-ocri-found-conn-is-carried
                     (conns (fn-own-conns o)))
          (:instance
           fn-ocari-repinned-connection-has-reader-pins
           (conn (fn-own-find-conn id (fn-own-conns o)))
           (view (fn-own-view o))
           (session
            (let* ((old (fn-own-conn-session
                         (fn-own-find-conn id (fn-own-conns o)))))
              (fn-auth-with-base
               old
               (fn-peer-with-base
                (fn-auth-session-base old)
                (fn-post-make-session
                 (fn-nntp-set-cursor
                  (fn-nntp-open-session
                   (fn-own-view-archive (fn-own-view o)))
                  (fn-nntp-session-group
                   (fn-post-session-base
                    (fn-peer-session-base (fn-auth-session-base old))))
                  (fn-nntp-session-current
                   (fn-post-session-base
                    (fn-peer-session-base (fn-auth-session-base old)))))
                 (fn-post-session-awaiting
                  (fn-peer-session-base (fn-auth-session-base old)))))))))
          (:instance fn-ocri-conns-p-of-replace
                     (conns (fn-own-conns o))
                     (conn
                      (fn-own-find-conn
                       id (fn-own-conns
                           (cdr (fn-own-advance-result o id)))))))
    :in-theory
    (e/d (fn-own-advance-result fn-own-set-conns)
         (fn-ocri-connp fn-ocri-viewp fn-ocri-conns-p
          fn-own-conn-boundedp
          fn-ocari-repinned-connection-has-reader-pins)))))

(defthm fn-ocari-advance-preserves-historical-reader-relation
  (implies (fn-ocri-relation oc)
           (fn-ocri-relation (fn-ocfg-advance oc id)))
  :hints
  (("Goal"
    :use (fn-ocl-advance-preserves-historical-relation
          (:instance fn-ocari-owner-advance-preserves-reader-pins
                     (o (fn-ocfg-owner oc)))
          (:instance fn-ocl-advance-result-keeps-owner-control))
    :in-theory
    (e/d (fn-ocri-relation fn-ocfg-advance)
         (fn-ocl-relation fn-own-advance-result fn-ocri-conns-p
          fn-ocri-viewp fn-ocari-owner-advance-preserves-reader-pins)))))
