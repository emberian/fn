(in-package "ACL2")
(include-book "../../books/consumer-remote-operation-source")
; Pure classification preserves unavailable until actual common entry exists.
(assert-event
 (and (equal (fn-cro-source-plan :remote-header :runtime-operation-unavailable nil)
             '(:unavailable :remote-operation-source))
      (equal (fn-cro-source-plan :remote-frame :runtime-operation-unavailable nil)
             '(:unavailable :remote-operation-source))
      (equal (fn-cro-source-plan :owner-admin :runtime-operation-unavailable nil)
             '(:refused :remote-operation-kind))
      (equal (fn-cro-source-plan :remote-header :runtime-operation-available nil)
             '(:unavailable :remote-operation-roles))
      (equal (fn-cro-source-plan :remote-frame :runtime-operation-available :runtime-operation-available)
             '(:unavailable :remote-operation-entry-installer))))
; Actual current getter/STATE caller executions. These are source-world
; unavailable observations, not TLS/native listener or installed authority.
(make-event
 (mv-let (erp answer state)
  (fn-owner-remote-operation-preflight :remote-header fn-page-read-pool state)
  (if (and (not erp) (equal answer '(:unavailable :remote-operation-source)))
      (value '(value-triple :passed))
    (er soft 'remote-header "Unexpected actual preflight ~x0" answer))))
(make-event
 (mv-let (erp answer state)
  (fn-owner-remote-operation-preflight :remote-frame fn-page-read-pool state)
  (if (and (not erp) (equal answer '(:unavailable :remote-operation-source)))
      (value '(value-triple :passed))
    (er soft 'remote-frame "Unexpected actual preflight ~x0" answer))))
(make-event
 (mv-let (erp answer state)
  (fn-owner-remote-operation-preflight :owner-admin fn-page-read-pool state)
  (if (and (not erp) (equal answer '(:refused :remote-operation-kind)))
      (value '(value-triple :passed))
    (er soft 'remote-private "Unexpected actual preflight ~x0" answer))))
