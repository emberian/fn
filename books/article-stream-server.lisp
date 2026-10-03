; Exact shared ARTICLE Xref server capture. This boundary needs no owner,
; catalog or current-view reconstruction: both authorization projections keep
; the connection's listing, and command observation changes only the clock.
(in-package "ACL2")
(include-book "nntp-auth")
(include-book "nntp-xref")

(defun fn-asto-server-candidate (config)
  (declare (xargs :guard t))
  (fn-nntp-listing-server (fn-inj-config-listing config)))

(local
 (defthm fn-asto-moderation-listing-preserved
   (equal (fn-inj-config-listing (fn-auth-moderation-config as config))
          (fn-inj-config-listing config))
   :hints (("Goal" :in-theory (enable fn-auth-moderation-config)))))

(defthm fn-asto-server-candidate-is-original-server
  (equal
   (fn-nntp-xref-server
    (fn-post-command-env
     (fn-auth-view-config as (fn-auth-moderation-config as config) archive)
     observation injection wire-event))
   (if (fn-xref-serverp (fn-asto-server-candidate config))
       (fn-asto-server-candidate config) nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-asto-server-candidate fn-nntp-xref-server
                                     fn-post-command-env)
                  :use ((:instance fn-auth-view-config-keeps
                                   (config (fn-auth-moderation-config as config)))
                        (:instance fn-post-reader-env-listing
                         (config (fn-auth-view-config as
                                    (fn-auth-moderation-config as config) archive)))))))
