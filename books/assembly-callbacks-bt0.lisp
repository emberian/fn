; First half of the commit kind's B-S2 section (txn member scan/open/join and
; checkpoint retirement coordinator), split so each book stays well under the
; 4 GiB SBCL dynamic-space ceiling of acl2-literal-4g-tls64k.
(in-package "ACL2")
(include-book "assembly-callbacks-b")
(make-event
 (let* ((body (fn2-commit-event-forms-1t))
        (pos-a (position-equal '(fn2-checkpoint-allocation-coordinator-events) body)))
   (if pos-a
       (value (take pos-a body))
     (er soft 'assembly-callbacks-bt0 "Could not locate allocation coordinator events in fn2-commit-event-forms-1t."))))
