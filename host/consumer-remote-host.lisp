; Additive remote caller wrappers, loaded after host/owner-host.lisp.
; Actual current configured owner/account publication is read in one span.
(in-package "ACL2")
(include-book "../books/consumer-remote-scope")
(include-book "../books/consumer-account-state")
(include-book "../books/owner-canonical-epoch")

(defun fn-owner-remote-ingress (request protectedp g state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (boundp-global 'fn-owner state)) (value '(:unavailable :owner))
  (let* ((files (fn-sn-files (fn-owner-store state)))
         (cp (fn-sn-consumer (fn-owner-store state))))
   (value (fn-cre-ingress request protectedp g cp
            (fn-owner-canonical-epoch state) (fn-sf-records-count files)
            (fn-owner-account-root-state state))))))

; Auth/read policy/configured-generation are captured from the same owner.
; The selected CP cursor names the exact consumer; ingress checks current
; principal and account creation before borrowing its immutable definition.
; The caller owes genuine issuer, retained source custody, source recheck and
; retirement before this cursor can serve an article or authorize a write.
(defun fn-owner-remote-scope-begin (request protectedp g selected-cursor state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (boundp-global 'fn-owner state)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store state)) (files (fn-sn-files store))
         (cp (fn-sn-consumer store))
         (ingress (fn-cre-ingress request protectedp g cp
                    (fn-owner-canonical-epoch state) (fn-sf-records-count files)
                    (fn-owner-account-root-state state)))
         (route (if (and (eq (fn-cp-nth 6 selected-cursor) :ready)
                         (equal (fn-cp-nth 1 selected-cursor) (fn-cp-nth 4 request)))
                    (fn-cre-selected-route ingress (fn-cp-nth 9 selected-cursor))
                  '(:refused :consumer-preparation-incomplete))))
   (value (if (eq (fn-cp-nth 0 route) :definition-request)
              (fn-crs-begin ingress (fn-cfg-generation (fn-owner-config state))
                           (fn-own-config (fn-owner-core state)) (fn-cp-nth 1 route))
            route)))))

; Reauthenticate and reread current scalar lineage before every tick. No
; captured credential, canonical epoch or source lease supplies authority.
(defun fn-owner-remote-scope-tick (request protectedp g cursor state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (boundp-global 'fn-owner state)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store state)) (files (fn-sn-files store))
         (ingress (fn-cre-ingress request protectedp g (fn-sn-consumer store)
                    (fn-owner-canonical-epoch state) (fn-sf-records-count files)
                    (fn-owner-account-root-state state))))
   (value (if (eq (fn-cp-nth 0 ingress) :authenticated)
              (fn-crs-tick cursor (fn-crs-key ingress
                                   (fn-cfg-generation (fn-owner-config state))) g)
            ingress)))))
