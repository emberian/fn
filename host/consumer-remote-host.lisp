; Additive remote caller wrappers, loaded after host/owner-host.lisp.
; Actual current configured owner/account publication is read in one span.
(in-package "ACL2")
(include-book "../books/consumer-remote-dispatch")
(include-book "../books/consumer-account-carries-state")
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

; Selected entry preparation borrows the sole maintained metadata5. This
; capture coordinate is semantic data, never the actual runtime source token.
(defun fn-owner-remote-selection-begin (request protectedp g state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (boundp-global 'fn-owner state)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store state)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config state)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state))))
   (value (if (eq (fn-cp-nth 0 ingress) :authenticated)
      (list :selection (fn-crx-coordinate ingress cp generation count) ingress cp generation
        (fn-cep-begin cp (list :remote-select (fn-cp-nth 4 request))
                          (fn-owner-account-carries-read state))) ingress)))))

; Every prepared entry step authenticates the explicit current account again
; and rejects a changed semantic capture before touching any borrowed cell.
; The actual owner entry additionally owes retained source/custody validation.
(defun fn-owner-remote-selection-tick (request protectedp g captured cursor state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (boundp-global 'fn-owner state)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store state)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config state)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state))))
   (value (cond ((not (eq (fn-cp-nth 0 ingress) :authenticated)) ingress)
                ((not (equal captured (fn-crx-coordinate ingress cp generation count)))
                 '(:refused :consumer-source-changed))
                (t (fn-cep-tick cursor)))))))

(defun fn-owner-remote-selected-plan (request protectedp g captured cep definition state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (boundp-global 'fn-owner state)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store state)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config state)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state))))
   (value (cond ((not (eq (fn-cp-nth 0 ingress) :authenticated)) ingress)
                ((not (equal captured (fn-crx-coordinate ingress cp generation count)))
                 '(:refused :consumer-source-changed))
                (t (fn-crx-selected-plan cp ingress cep definition generation)))))))

(defun fn-owner-remote-decision-begin (request protectedp g captured cep definition state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (boundp-global 'fn-owner state)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store state)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config state)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state)))
         (profile (fn-owner-store-profile state)))
   (value (cond ((not (eq (fn-cp-nth 0 ingress) :authenticated)) ingress)
                ((not profile) '(:unavailable :profile))
                ((not (equal captured (fn-crx-coordinate ingress cp generation count)))
                 '(:refused :consumer-source-changed))
                (t (fn-crd-begin captured ingress cp cep definition
                           (fn-store-profile-max-consumers profile) generation)))))))

(defun fn-owner-remote-decision-tick (request protectedp g cursor state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (boundp-global 'fn-owner state)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store state)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config state)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state))))
   (value (if (eq (fn-cp-nth 0 ingress) :authenticated)
               (fn-crd-tick cursor (fn-crx-coordinate ingress cp generation count)) ingress)))))

; Saved selected proposal and exact new CP/carries only. This has no frontier
; allocation, persistence, Store publication or durable ACK side effect.
(defun fn-owner-remote-decision-finish (request protectedp g cursor state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (boundp-global 'fn-owner state)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store state)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config state)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state))))
   (value (if (eq (fn-cp-nth 0 ingress) :authenticated)
               (fn-crd-finish cursor (fn-crx-coordinate ingress cp generation count)
                              (fn-owner-account-carries-read state)) ingress)))))
