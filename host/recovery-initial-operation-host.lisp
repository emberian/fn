; Readonly custody handoff for an already-issued INITIAL operation.
; No token issuance/refresh, canonical seal or role return occurs here.
(in-package "ACL2")
(include-book "recovery-initial-source-host")
(include-book "../books/owner-canonical-read-state")
(include-book "../books/recovery-initial-operation-lineage")
(defun fn-owner-recovery-initial-operation-currentp (token state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((issuer (fn-owner-recovery-global 'fn-owner-recovery-source state))
        (origin (fn-omk-at 3 issuer))
        (current-origin (fn-owner-recovery-global 'fn-store-recovery-open-origin state))
        (epoch (fn-owner-canonical-epoch state))
        (generation (fn-owner-recovery-source-generation-value issuer state))
        (store (fn-owner-recovery-global 'fn-store-sn state))
        (files (fn-sn-files store)))
  (and
   ; Origin checks retain the same actual loader generation, epoch and mode.
   (if (fn-rsoa-originp origin)
       (and (fn-rsoa-originp current-origin)
            (equal (fn-omk-at 1 current-origin) (fn-omk-at 1 origin))
            (equal (fn-omk-at 2 current-origin) epoch)
            (eq (fn-omk-at 3 current-origin) (fn-omk-at 3 origin)))
     (fn-rsa-metap (fn-store-sco-recovery-source-value state)))
   (eq (fn-sf-phase files) :ready)
   (fn-owner-recovery-records-formp (fn-sf-records-field files))
   (fn-rsa-initial-operation-lineagep
    issuer token epoch generation (fn-sf-records-count files)
    (fn-sf-frontier files) (fn-owner-canonical-state state)))))
