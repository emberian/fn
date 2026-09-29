; books/owner-reclaim-instant.lisp -- the reclaim's instant recorded LIVE
; (row Q16, lane online-reclaim-6, PRF-987).
;
; A running owner answers `store reclaim' by recording the instant first
; through the live reconfiguration (host/owner-host.lisp
; fn-owner-orc-instant-stage -> fn-owner-reconfigure-deltas -> the owner
; model's :reconfigure step, which stages fn-ocfg-reconfig-record over the
; one delta fn-rci-delta NOW), then running the installing pass over the
; recorded configuration.  KEYSTONE fn-orli-live-record-decides-the-context:
; the configuration that record yields is fn-rci-recorded-config at the
; owner's generation, next txid and configuration stamp, so the pass's
; context is the one the offline `store reclaim' decides at the same
; instant (books/reclaim-instant.lisp fn-rci-recorded-context-is-the-
; decided-context).

(in-package "ACL2")
(include-book "owner-config")
(include-book "reclaim-instant")

; The staged record is the offline record at the owner's coordinates.
(defthm fn-orli-live-record-is-the-recorded-config-by-definition
  (equal (fn-cfg-apply-record cfg (fn-ocfg-reconfig-record oc (list (fn-rci-delta now))))
         (fn-rci-recorded-config
          cfg
          (fn-cfg-generation (fn-ocfg-config oc))
          (fn-state-next-txid (fn-node-acceptance (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
          (+ 1 (fn-cfg-generation (fn-ocfg-config oc)))
          (fn-ocfg-config-stamp (fn-own-clock (fn-ocfg-owner oc)))
          now))
  :hints (("Goal" :in-theory (union-theories '(fn-ocfg-reconfig-record fn-rci-recorded-config)
                                             (theory 'minimal-theory)))))

; KEYSTONE.  The configuration the live record yields decides the context of
; the retention rule the configuration held before it, at NOW: the offline
; decision's context (fn-rclp-ctx).
(defthm fn-orli-live-record-decides-the-context
  (implies (fn-rci-instantp now)
           (equal (fn-rci-context
                   (fn-cfg-value
                    (fn-cfg-apply-record cfg (fn-ocfg-reconfig-record oc (list (fn-rci-delta now)))))
                   s)
                  (fn-rclp-ctx (fn-rcl-config-rule (fn-cfg-value cfg)) now s)))
  :hints (("Goal" :in-theory (disable fn-rci-recorded-config fn-ocfg-reconfig-record
                                      fn-rci-context fn-rclp-ctx fn-rcl-config-rule
                                      fn-cfg-apply-record fn-rci-delta (:e fn-rci-delta))
           :use (fn-orli-live-record-is-the-recorded-config-by-definition
                 (:instance fn-rci-recorded-context-is-the-decided-context
                            (q (fn-cfg-generation (fn-ocfg-config oc)))
                            (tx (fn-state-next-txid
                                 (fn-node-acceptance (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))))
                            (g (+ 1 (fn-cfg-generation (fn-ocfg-config oc))))
                            (stamp (fn-ocfg-config-stamp (fn-own-clock (fn-ocfg-owner oc)))))))))
