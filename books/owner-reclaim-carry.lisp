; Pure off-mutex rebuild under the actual native host entry name.
; Its cold rebuild callees are not all guard verified: this entry remains
; :ideal.  PRF-1060 establishes only the returned carry, not live state
; preservation.  W9's obligation view (field 6) is parked
; (books/owner-obligation-state.lisp, lane figure-and-contract): the rebuild
; returns fields 0..5.
;
; Lane reclaim (2026-10-04, PRF-1315): the entry takes the rebuilt CAPTURE E,
; not the rewritten rows.  The host builds E chunk by chunk from the pinned
; history (books/reclaim-chunked-walk.lisp fn-rcw-acc-*, pass 3 of
; books/reclaim-chunked-seal.lisp), so no whole row list reaches this call.
; Over the capture of ROWS it is the rebuild fn-orcp-rebuild of ROWS
; (fn-owner-orcp-rebuild-of-capture-is-the-rebuild below), so the full-open
; keystone holds of it.
(in-package "ACL2")
(include-book "owner-reclaim-pass")
(include-book "post-retain-carried")
(include-book "store-budget")
(include-book "store-capacity-vector")
(include-book "peer-carriage")

(defun fn-owner-orcp-rebuild (e configs frontier max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((r (list e (fn-ock-recover-extended e configs frontier max-conns)))
         (oc (cadr r)))
    (if (equal oc :fault)
        (list (car r) :fault nil nil nil nil)
      (let* ((s (fn-own-store (fn-ocfg-owner oc)))
             (records (fn-sf-records (fn-sn-files s)))
             (count (fn-sf-records-count (fn-sn-files s))))
        (list (car r) oc
              (fn-prc-refresh nil (fn-node-retention (fn-sn-node s)))
              (cons count (fn-sbud-bytes-used s))
              (cons count (fn-cvec-record-debt records))
              (cons count (fn-pcb-tally-records records nil)))))))


(defthm fn-owner-orcp-rebuild-establishes-retain-carry
  (fn-prc-carryp (nth 2 (fn-owner-orcp-rebuild e configs frontier max-conns)))
  :hints (("Goal" :in-theory (union-theories
                             '(fn-owner-orcp-rebuild nth endp zp car-cons cdr-cons
                               (:executable-counterpart zp)
                               (:executable-counterpart binary-+)
                               (:executable-counterpart unary--)
                               fn-prc-carryp-when-atom fn-prc-carryp-of-refresh)
                             (theory 'minimal-theory)))))


; The entry over the capture of ROWS is the whole-list rebuild's owner
; (fn-orcp-rebuild: the empty capture extended over ROWS), so
; fn-orcp-rebuild-is-the-full-open transfers.
(defthm fn-owner-orcp-rebuild-of-capture-is-the-rebuild
  (implies (true-listp rows)
           (equal (cadr (fn-owner-orcp-rebuild (fn-sco-capture configs rows)
                                               configs frontier max-conns))
                  (cadr (fn-orcp-rebuild rows configs frontier max-conns))))
  :hints (("Goal" :use ((:instance fn-sco-extend-of-capture (prefix nil) (suffix rows)))
                  :in-theory (union-theories
                              '(fn-owner-orcp-rebuild fn-orcp-rebuild
                                fn-rii-sco-extend-is-sco-extend binary-append
                                car-cons cdr-cons (:executable-counterpart consp))
                              (theory 'minimal-theory)))))

; KEYSTONE (with fn-orcp-rebuild-is-the-full-open).  The host's rebuild of
; the capture of ROWS is the owner the full open of ROWS installs.
(defthm fn-owner-orcp-rebuild-of-capture-is-the-full-open
  (implies (true-listp rows)
           (equal (cadr (fn-owner-orcp-rebuild (fn-sco-capture configs rows)
                                               configs frontier max-conns))
                  (fn-ock-recover-full configs frontier rows max-conns)))
  :hints (("Goal" :use (fn-owner-orcp-rebuild-of-capture-is-the-rebuild
                        fn-orcp-rebuild-is-the-full-open)
                  :in-theory (theory 'minimal-theory))))
