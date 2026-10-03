; Additive remote caller wrappers, loaded after host/owner-host.lisp.
; Actual current configured owner/account publication is read in one span.
(in-package "ACL2")
(include-book "../books/consumer-remote-dispatch")
(include-book "../books/consumer-remote-query-profile")
(include-book "../books/consumer-remote-operation-source")
(include-book "../books/consumer-remote-event-buffer")
(include-book "../books/consumer-account-carries-state")
(include-book "../books/consumer-account-state")
(include-book "../books/owner-canonical-epoch")
(include-book "../books/store-node-files-selector") ; fn-sn-files

(defun fn-owner-remote-ingress (request protectedp g fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (if (not (fn-owner-boundp fn-owner-st)) (value '(:unavailable :owner))
  (let* ((files (fn-sn-files (fn-owner-store fn-owner-st)))
         (cp (fn-sn-consumer (fn-owner-store fn-owner-st))))
   (value (fn-cre-ingress request protectedp g cp
            (fn-owner-canonical-epoch state) (fn-sf-records-count files)
            (fn-owner-account-root-state state))))))

; Auth/read policy/configured-generation are captured from the same owner.
; The selected CP cursor names the exact consumer; ingress checks current
; principal and account creation before borrowing its immutable definition.
; The caller owes genuine issuer, retained source custody, source recheck and
; retirement before this cursor can serve an article or authorize a write.
(defun fn-owner-remote-scope-begin (request protectedp g selected-cursor fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (if (not (fn-owner-boundp fn-owner-st)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store fn-owner-st)) (files (fn-sn-files store))
         (cp (fn-sn-consumer store))
         (ingress (fn-cre-ingress request protectedp g cp
                    (fn-owner-canonical-epoch state) (fn-sf-records-count files)
                    (fn-owner-account-root-state state)))
         (route (if (and (eq (fn-cp-nth 6 selected-cursor) :ready)
                         (equal (fn-cp-nth 1 selected-cursor) (fn-cp-nth 4 request)))
                    (fn-cre-selected-route ingress (fn-cp-nth 9 selected-cursor))
                  '(:refused :consumer-preparation-incomplete))))
   (value (if (eq (fn-cp-nth 0 route) :definition-request)
              (fn-crs-begin ingress (fn-cfg-generation (fn-owner-config fn-owner-st))
                           (fn-own-config (fn-owner-core fn-owner-st)) (fn-cp-nth 1 route))
            route)))))

; Reauthenticate and reread current scalar lineage before every tick. No
; captured credential, canonical epoch or source lease supplies authority.
(defun fn-owner-remote-scope-tick (request protectedp g cursor fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (if (not (fn-owner-boundp fn-owner-st)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store fn-owner-st)) (files (fn-sn-files store))
         (ingress (fn-cre-ingress request protectedp g (fn-sn-consumer store)
                    (fn-owner-canonical-epoch state) (fn-sf-records-count files)
                    (fn-owner-account-root-state state))))
   (value (if (eq (fn-cp-nth 0 ingress) :authenticated)
              (fn-crs-tick cursor (fn-crs-key ingress
                                   (fn-cfg-generation (fn-owner-config fn-owner-st))) g)
            ingress)))))

; Selected entry preparation borrows the sole maintained metadata5. This
; capture coordinate is semantic data, never the actual runtime source token.
(defun fn-owner-remote-selection-begin (request protectedp g fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (if (not (fn-owner-boundp fn-owner-st)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store fn-owner-st)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config fn-owner-st)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state))))
   (value (if (eq (fn-cp-nth 0 ingress) :authenticated)
      (list :selection (fn-crx-coordinate ingress cp generation count) ingress cp generation
        (fn-cep-begin cp (list :remote-select (fn-cp-nth 4 request))
                          (fn-owner-account-carries-read state))) ingress)))))

; Every prepared entry step authenticates the explicit current account again
; and rejects a changed semantic capture before touching any borrowed cell.
; The actual owner entry additionally owes retained source/custody validation.
(defun fn-owner-remote-selection-tick (request protectedp g captured cursor fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (if (not (fn-owner-boundp fn-owner-st)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store fn-owner-st)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config fn-owner-st)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state))))
   (value (cond ((not (eq (fn-cp-nth 0 ingress) :authenticated)) ingress)
                ((not (equal captured (fn-crx-coordinate ingress cp generation count)))
                 '(:refused :consumer-source-changed))
                (t (fn-cep-tick cursor)))))))

(defun fn-owner-remote-selected-plan (request protectedp g captured cep definition fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (if (not (fn-owner-boundp fn-owner-st)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store fn-owner-st)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config fn-owner-st)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state))))
   (value (cond ((not (eq (fn-cp-nth 0 ingress) :authenticated)) ingress)
                ((not (equal captured (fn-crx-coordinate ingress cp generation count)))
                 '(:refused :consumer-source-changed))
                (t (fn-crx-selected-plan cp ingress cep definition generation)))))))

(defun fn-owner-remote-decision-begin (request protectedp g captured cep definition fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (if (not (fn-owner-boundp fn-owner-st)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store fn-owner-st)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config fn-owner-st)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state)))
         (profile (fn-owner-store-profile state)))
   (value (cond ((not (eq (fn-cp-nth 0 ingress) :authenticated)) ingress)
                ((not profile) '(:unavailable :profile))
                ((not (equal captured (fn-crx-coordinate ingress cp generation count)))
                 '(:refused :consumer-source-changed))
                (t (fn-crd-begin captured ingress cp cep definition
                           (fn-store-profile-max-consumers profile) generation)))))))

(defun fn-owner-remote-decision-tick (request protectedp g cursor fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (if (not (fn-owner-boundp fn-owner-st)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store fn-owner-st)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config fn-owner-st)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state))))
   (value (if (eq (fn-cp-nth 0 ingress) :authenticated)
               (fn-crd-tick cursor (fn-crx-coordinate ingress cp generation count)) ingress)))))

; Saved selected proposal and exact new CP/carries only. This has no frontier
; allocation, persistence, Store publication or durable ACK side effect.
(defun fn-owner-remote-decision-finish (request protectedp g cursor fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (if (not (fn-owner-boundp fn-owner-st)) (value '(:unavailable :owner))
  (let* ((store (fn-owner-store fn-owner-st)) (cp (fn-sn-consumer store))
         (count (fn-sf-records-count (fn-sn-files store)))
         (generation (fn-cfg-generation (fn-owner-config fn-owner-st)))
         (ingress (fn-cre-ingress request protectedp g cp (fn-owner-canonical-epoch state)
                                  count (fn-owner-account-root-state state))))
   (value (if (eq (fn-cp-nth 0 ingress) :authenticated)
               (fn-crd-finish cursor (fn-crx-coordinate ingress cp generation count)
                              (fn-owner-account-carries-read state)) ingress)))))


; Required current-C query policy, captured before frame admission. This is
; not the installed runtime family/role descriptor or an allocation grant.
; The actual owner source issuer must keep/revalidate this C/profile span.
(defun fn-owner-remote-query-policy-key (fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (list :query-policy-current (fn-owner-canonical-epoch state)
       (fn-cfg-generation (fn-owner-config fn-owner-st))))

(defun fn-owner-remote-query-record-ceiling (state)
 (declare (xargs :stobjs state :mode :program))
 ; The sole profile publisher carries its admission once. Borrow that exact
 ; installed child; no fn-bs-profile-validp or profile tree scan runs here.
 (let ((carry (fn-owner-profile-carry state)))
  (and (consp carry) (cdr carry)
       (fn-bs-pf *fn-bs-pf-max-record-octets* (car carry)))))

(defun fn-owner-remote-query-policy-begin (fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (let ((record-ceiling (fn-owner-remote-query-record-ceiling state)))
  (if (not (and (fn-owner-boundp fn-owner-st) record-ceiling))
      (value '(:unavailable :store-profile))
   (value (fn-crp-begin (fn-owner-remote-query-policy-key fn-owner-st state)
          (fn-cfg-limits (fn-cfg-value (fn-owner-config fn-owner-st))) record-ceiling)))))

(defun fn-owner-remote-query-policy-tick (cursor fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (let ((record-ceiling (fn-owner-remote-query-record-ceiling state)))
  (if (not (and (fn-owner-boundp fn-owner-st) record-ceiling))
      (value '(:unavailable :store-profile))
   (value (fn-crp-tick cursor (fn-owner-remote-query-policy-key fn-owner-st state) record-ceiling)))))

(defun fn-owner-remote-query-runtime-verdict (cursor fn-owner-st state)
 (declare (xargs :stobjs (fn-owner-st state) :mode :program))
 (let ((record-ceiling (fn-owner-remote-query-record-ceiling state)))
  (if (not (and (fn-owner-boundp fn-owner-st) record-ceiling))
      (value '(:unavailable :store-profile))
   (value (fn-crp-runtime-verdict
            (fn-crp-finish cursor (fn-owner-remote-query-policy-key fn-owner-st state) record-ceiling))))))

; Called only inside the genuine event-specific consumer publication turn
; after exact record-extent reservation and current-source revalidation.
; This adapter neither allocates a grant nor publishes/acknowledges a row.
(defun fn-owner-remote-event-buffer-step (cursor current-key extent fn-octets state)
 (declare (xargs :stobjs (fn-octets state) :mode :program))
 (mv-let (answer fn-octets) (fn-crevb-step cursor current-key extent fn-octets)
  (mv nil answer fn-octets state)))
