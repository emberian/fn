; fn: the expiry's instant, recorded (Q14; with books/reclaim-instant.lisp).
;
; `store reclaim' records its instant NOW as the configuration row
; `retention-reclaim-at' before it rewrites anything (PKT-857), so that
; `store reclaim --recorded' (the completion of a reclaim whose record was
; published before a process death) decides exactly as the reclaim did.
; Under an expiry policy the context also carries the set the policy expires
; at NOW (books/expiry.lisp `fn-xpy-ctx'), and that set is a function of the
; configuration's quota rows, the instant and the Store: the recorded
; configuration carries the same quota rows (the instant's delta is a
; `:set-limit', which leaves them) and the same NOW, so the recorded context
; is the decided context (KEYSTONE `fn-xpy-rci-recorded-context-is-the-
; decided-context').  A restart in the middle of an expiring reclaim
; therefore completes the same expiry.
(in-package "ACL2")
(include-book "expiry")
(include-book "reclaim-instant")

; The context a replay derives from a configuration value and the Store.
(defun fn-xpy-rci-context (v s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-xpy-ctx (fn-rcl-config-rule v) (fn-rci-config-now v) s v fn-arena))

(local
 (defthm fn-xpy-rci-value-of-apply-record
   (equal (fn-cfg-value (fn-cfg-apply-record cfg (fn-cfg-record-make q tx g change stamp)))
          (fn-cfg-apply (fn-cfg-value cfg) g stamp change))
   :hints (("Goal" :in-theory (enable fn-cfg-apply-record fn-cfg-value fn-cfg-make
                                      fn-cfg-ag-car fn-cfg-ag-cdr)))))

(local
 (defthm fn-xpy-rci-quotas-of-set-limit
   (equal (fn-cfg-quotas (fn-cfg-apply-delta v gen stamp
                                             (list :set-limit slot "" n nil)))
          (fn-cfg-quotas v))
   :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-delta-kind fn-cfg-delta-a
                                      fn-cfg-delta-b fn-cfg-delta-n fn-cfg-delta-rows
                                      fn-cfg-ag-car fn-cfg-ag-cdr)))))

; The instant's record leaves the quota rows, so the expiry policy, as they
; were.
(defthm fn-xpy-rci-recorded-config-keeps-the-policy
  (equal (fn-cfg-quotas (fn-cfg-value (fn-rci-recorded-config cfg q tx g stamp now)))
         (fn-cfg-quotas (fn-cfg-value cfg)))
  :hints (("Goal" :in-theory (enable fn-rci-recorded-config fn-cfg-apply fn-rci-delta
                                     fn-cfg-set-limit fn-cfg-delta-make))))

;  KEYSTONE.  The context a replay derives from the recorded configuration
; is the context the host decided under (host/checkpoint-host.lisp
; fn-store-reclaim-context: RULE the configuration's, NOW the clock's stamp,
; the expired set of the configuration's policy at NOW over the Store).
(defthm fn-xpy-rci-recorded-context-is-the-decided-context
  (implies (fn-rci-instantp now)
           (equal (fn-xpy-rci-context (fn-cfg-value (fn-rci-recorded-config cfg q tx g stamp now))
                                      s fn-arena)
                  (fn-xpy-ctx (fn-rcl-config-rule (fn-cfg-value cfg)) now s
                              (fn-cfg-value cfg) fn-arena)))
  :hints (("Goal" :in-theory (disable fn-rci-recorded-config fn-rcl-config-rule
                                      fn-rci-config-now fn-rci-recordedp
                                      fn-xpy-expired-set fn-rclp-ctx-expiring)
           :use (fn-rci-recorded-instant-reads-back
                 fn-xpy-rci-recorded-config-keeps-the-policy))))
