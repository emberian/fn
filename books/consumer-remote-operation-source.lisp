; Actual common operation-source join for the separate remote transport.
; No positive native operation-entry is installed yet. Neither a valid
; family nor a role table can substitute for that installed entry.
(in-package "ACL2")
(include-book "runtime-operation-source")

(defun fn-cro-source-plan (kind source-status role-status)
 (declare (xargs :guard t))
 (cond ((not (member-eq kind '(:remote-header :remote-frame)))
        '(:refused :remote-operation-kind))
       ((not (eq source-status :runtime-operation-available))
        '(:unavailable :remote-operation-source))
       ((not (eq role-status :runtime-operation-available))
        '(:unavailable :remote-operation-roles))
       (t '(:unavailable :remote-operation-entry-installer))))

(defun fn-owner-remote-operation-preflight (kind fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
 (mv-let (source-status family)
     (fn-owner-runtime-operation-source kind fn-page-read-pool state)
  (declare (ignore family))
  (if (not (eq source-status :runtime-operation-available))
      (mv nil (fn-cro-source-plan kind source-status :runtime-operation-unavailable) state)
   (mv-let (role-status table)
       (fn-owner-runtime-operation-role-table kind fn-page-read-pool state)
    (declare (ignore table))
    (mv nil (fn-cro-source-plan kind source-status role-status) state)))))

(in-theory (disable fn-cro-source-plan fn-owner-remote-operation-preflight))
