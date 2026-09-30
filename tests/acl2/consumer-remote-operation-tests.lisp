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
(fn-owner-remote-operation-preflight :remote-header fn-page-read-pool state)
(fn-owner-remote-operation-preflight :remote-frame fn-page-read-pool state)
(fn-owner-remote-operation-preflight :owner-admin fn-page-read-pool state)
