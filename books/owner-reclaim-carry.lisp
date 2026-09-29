; Pure off-mutex rebuild under the actual native host entry name.
; The definition is moved unchanged from host/owner-host.lisp. Its cold
; rebuild callees are not all guard verified: this entry remains :ideal.
; PRF-1060 establishes only the returned carry, not live state preservation.
; W9 appends the obligation view at field 6; fields 0..5 keep their exact
; meanings. This initialization is off mutex and must be budgeted beside
; the old view before its allocation; it is never a served read fallback.
(in-package "ACL2")
(include-book "owner-reclaim-pass")
(include-book "post-retain-carried")
(include-book "store-budget")
(include-book "store-capacity-vector")
(include-book "peer-carriage")
(include-book "retention-obligation-view")

(defun fn-owner-orcp-rebuild (rows configs frontier max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((r (fn-orcp-rebuild rows configs frontier max-conns))
         (oc (cadr r)))
    (if (equal oc :fault)
        (list (car r) :fault nil nil nil nil nil)
      (let* ((s (fn-own-store (fn-ocfg-owner oc)))
             (records (fn-sf-records (fn-sn-files s)))
             (count (fn-sf-records-count (fn-sn-files s))))
        (list (car r) oc
              (fn-prc-refresh nil (fn-node-retention (fn-sn-node s)))
              (cons count (fn-sbud-bytes-used s))
              (cons count (fn-cvec-record-debt records))
              (cons count (fn-pcb-tally-records records nil))
              (fn-rov-build (fn-retain-pins (fn-node-retention (fn-sn-node s)))))))))


(defthm fn-owner-orcp-rebuild-establishes-retain-carry
  (fn-prc-carryp (nth 2 (fn-owner-orcp-rebuild rows configs frontier max-conns)))
  :hints (("Goal" :in-theory (union-theories
                             '(fn-owner-orcp-rebuild nth endp zp car-cons cdr-cons
                               (:executable-counterpart zp)
                               (:executable-counterpart binary-+)
                               (:executable-counterpart unary--)
                               fn-prc-carryp-when-atom fn-prc-carryp-of-refresh)
                             (theory 'minimal-theory)))))

(defthm fn-owner-orcp-rebuild-establishes-obligation-view
  (implies (and (not (equal (nth 1 (fn-owner-orcp-rebuild rows configs frontier max-conns)) :fault))
                (fn-retain-obligation-listp
                 (fn-retain-pins
                  (fn-node-retention
                   (fn-sn-node
                    (fn-own-store
                     (fn-ocfg-owner (nth 1 (fn-owner-orcp-rebuild rows configs frontier max-conns)))))))))
           (fn-rov-correspondp
            (nth 6 (fn-owner-orcp-rebuild rows configs frontier max-conns))
            (fn-retain-pins
             (fn-node-retention
              (fn-sn-node
               (fn-own-store
                (fn-ocfg-owner (nth 1 (fn-owner-orcp-rebuild rows configs frontier max-conns)))))))))
  :hints (("Goal" :in-theory (e/d (fn-owner-orcp-rebuild) (fn-orcp-rebuild)))))
