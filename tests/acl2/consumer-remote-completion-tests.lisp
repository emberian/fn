(in-package "ACL2")
(include-book "../../books/consumer-remote-completion-model")
(include-book "../../books/consumer-remote-dispatch")
(include-book "consumer-remote-scope-tests")

; Proof fixture annotations, never a served metadata reconstruction.
(defun fn-crdt-list-meta (xs)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp xs) (fn-caac-list-cons (fn-scs-summary (car xs)) (fn-crdt-list-meta (cdr xs))) nil))
(defun fn-crdt-fields-meta (xs)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp xs) (cons (fn-scs-summary (car xs)) (fn-crdt-fields-meta (cdr xs))) nil))
(defun fn-crdt-meta (cp)
 (declare (xargs :guard t :verify-guards nil))
 (list :account-carries (fn-crdt-fields-meta cp)
       (fn-crdt-list-meta (fn-cp-nth 4 (fn-cp-nth 6 cp))) nil
       (fn-crdt-list-meta (fn-cp-nth 5 cp))))
(defun fn-crdt-cep-run (fuel result)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 result) :yield))) result
  (fn-crdt-cep-run (1- fuel) (fn-cep-tick (fn-cp-nth 1 result)))))
(defun fn-crdt-decision-run (fuel result key)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 result) :yield))) result
  (fn-crdt-decision-run (1- fuel) (fn-crd-tick (fn-cp-nth 1 result) key) key)))
(defun fn-crdt-ingress (cp op groups cursor seconds)
 (declare (xargs :guard t :verify-guards nil))
 (fn-cre-ingress (fn-crit-request op '(97) '(99) groups cursor seconds)
                  t 3 cp 3 (fn-cp-nth 3 cp) (fn-crat-pub)))
(defun fn-crdt-cep (cp)
 (declare (xargs :guard t :verify-guards nil))
 (fn-cp-nth 1 (fn-crdt-cep-run 80 (fn-cep-begin cp '(:remote-select (99)) (fn-crdt-meta cp)))))
(defun fn-crdt-definition (ingress groups)
 (declare (xargs :guard t :verify-guards nil))
 (fn-cp-nth 1 (fn-crst-run 80 (fn-crs-begin ingress 7 (fn-crst-config nil nil) groups)
                           (fn-crs-key ingress 7) 3)))
(defun fn-crdt-prepared (cp op groups)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((i (fn-crdt-ingress cp op groups nil 0)) (cep (fn-crdt-cep cp))
        (d (fn-crdt-definition i groups)) (key (fn-crx-coordinate i cp 7 (fn-cp-nth 3 cp)))
        (result (fn-crdt-decision-run 80 (fn-crd-begin key i cp cep d 3 7) key)))
  (fn-crd-finish (fn-cp-nth 1 result) key (fn-crdt-meta cp))))

; New registration matches actual CP apply and exact canonical entry/CP carry.
(assert-event
 (let* ((cp (fn-crat-cp)) (r (fn-crdt-prepared cp :register '((97) (98))))
        (op (fn-cp-nth 1 (fn-cp-nth 1 r))) (next (fn-cp-nth 2 r)))
  (and (eq (car r) :prepared) (equal (fn-cp-nth 0 op) :remote-register)
       (equal (fn-cp-nth 3 op) '(99)) (equal (fn-cp-nth 4 op) (fn-cp-nth 4 cp))
       (equal next (fn-cp-apply cp op)) (equal (fn-cp-nth 3 r) (fn-crdt-meta next))
       (equal (fn-cp-nth 5 r) 2) (equal (fn-cp-nth 6 r) 6))))

(defun fn-crdt-first ()
 (declare (xargs :guard t :verify-guards nil))
 (fn-crdt-prepared (fn-crat-cp) :register '((97) (98))))
(defun fn-crdt-cp ()
 (declare (xargs :guard t :verify-guards nil))
 (fn-cp-nth 2 (fn-crdt-first)))
(defun fn-crdt-old ()
 (declare (xargs :guard t :verify-guards nil))
 (car (fn-cp-nth 5 (fn-crdt-cp))))

; Exact retry keeps the old registration epoch, query version and position;
; differing definition refuses register and requires an explicit rebase.
(assert-event
 (let ((retry (fn-crdt-prepared (fn-crdt-cp) :register '((97) (98))))
       (change (fn-crdt-prepared (fn-crdt-cp) :register '((97))))
       (rebase (fn-crdt-prepared (fn-crdt-cp) :rebase '((97)))))
  (and (equal retry (list :no-op (fn-cp-scope-cursor (fn-crdt-cp) (fn-crdt-old))))
       (equal change '(:refused :rebase-required))
       (eq (car rebase) :prepared)
       (equal (fn-cp-nth 4 (fn-cp-nth 1 (fn-cp-nth 1 rebase))) (fn-cp-nth 4 (fn-crdt-cp)))
       (equal (fn-cp-nth 2 rebase)
              (fn-cp-apply (fn-crdt-cp) (fn-cp-nth 1 (fn-cp-nth 1 rebase)))))))

; The actual all-eight dispatcher returns scoped read plans or proposals.
(defun fn-crdt-plan (op cursor seconds)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((i (fn-crdt-ingress (fn-crdt-cp) op
             (if (member-eq op '(:register :rebase)) '((97) (98)) nil) cursor seconds))
        (cep (fn-crdt-cep (fn-crdt-cp))) (d (fn-crdt-definition i '((97) (98)))))
  (fn-crx-selected-plan (fn-crdt-cp) i cep d 7)))
(assert-event
 (and (eq (car (fn-crdt-plan :register nil 0)) :definition-proposal)
      (eq (car (fn-crdt-plan :rebase nil 0)) :definition-proposal)
      (eq (car (fn-crdt-plan :poll nil 0)) :scan-request)
      (equal (fn-cp-nth 6 (fn-crdt-plan :wait nil 1)) 1)
      (eq (car (fn-crdt-plan :position nil 0)) :position)
      (equal (fn-crdt-plan :status nil 0)
             (list :status 0 (fn-cp-nth 3 (fn-crdt-cp)) (fn-cp-nth 3 (fn-crdt-cp))))
      (eq (car (fn-crdt-plan :ack (fn-cp-cursor-encode
                  (update-nth 9 1 (fn-cp-scope-cursor (fn-crdt-cp) (fn-crdt-old)))) 0)) :write)
      (eq (car (fn-crdt-plan :unregister nil 0)) :write)))

;@positive fn-crd-tick-preserves-exact-definition-comparison-and-capacity
(assert-event
 (let* ((cep (fn-crdt-cep (fn-crdt-cp)))
        (s (fn-crd-state '(1) nil (fn-crdt-cp) cep nil '((97) (98)) '((97) (98)) :compare t 0 3)))
  (and (fn-crdm-domainp s) (equal '(1) (fn-cp-nth 1 s))
       (or (not (eq (fn-cp-nth 8 s) :capacity)) (not (fn-cp-nth 9 (fn-cp-nth 4 s))))
       (equal (fn-crdm-answer (fn-crd-tick s '(1))) (fn-crdm-observe s)))))
;@hypothesis-removal fn-crd-tick-preserves-exact-definition-comparison-and-capacity current-key
(assert-event
 (let ((s (fn-crd-state '(1) nil (fn-crdt-cp) (fn-crdt-cep (fn-crdt-cp)) nil '((97)) '((97)) :compare t 0 3)))
  (and (fn-crdm-domainp s) (not (equal '(2) (fn-cp-nth 1 s)))
       (or (not (eq (fn-cp-nth 8 s) :capacity)) (not (fn-cp-nth 9 (fn-cp-nth 4 s))))
       (not (equal (fn-crdm-answer (fn-crd-tick s '(2))) (fn-crdm-observe s))))))
;@hypothesis-removal fn-crd-tick-preserves-exact-definition-comparison-and-capacity maintained-domain
; Corrupted cursor: comparison names no selected old entry.
(assert-event
 (let ((s (fn-crd-state '(1) nil nil nil nil nil nil :compare t 0 3)))
  (and (not (fn-crdm-domainp s)) (equal '(1) (fn-cp-nth 1 s))
       (or (not (eq (fn-cp-nth 8 s) :capacity)) (not (fn-cp-nth 9 (fn-cp-nth 4 s))))
       (not (equal (fn-crdm-answer (fn-crd-tick s '(1))) (fn-crdm-observe s))))))
;@hypothesis-removal fn-crd-tick-preserves-exact-definition-comparison-and-capacity absent-entry-capacity
; Corrupted cursor: existing-entry selection has been placed in new capacity.
(assert-event
 (let ((s (fn-crd-state '(1) nil (fn-crdt-cp) (fn-crdt-cep (fn-crdt-cp)) nil nil nil :capacity nil 0 3)))
  (and (fn-crdm-domainp s) (equal '(1) (fn-cp-nth 1 s))
       (not (or (not (eq (fn-cp-nth 8 s) :capacity)) (not (fn-cp-nth 9 (fn-cp-nth 4 s)))))
       (not (equal (fn-crdm-answer (fn-crd-tick s '(1))) (fn-crdm-observe s))))))

(defun fn-crdt-carry-law (c p q a qv v e gm)
 (declare (xargs :guard t :verify-guards nil))
 (let ((entry (fn-cp-event-entry (list :remote-register c p q qv v e '((97) (98)) a))))
  (equal (fn-crd-entry-carry entry gm) (fn-scs-summary entry))))
;@positive fn-crd-remote-entry-constructor-has-exact-canonical-carry
(assert-event
 (let ((gm (fn-crdt-list-meta '((97) (98)))))
  (and (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(112))
       (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(65))
       (integerp 1) (integerp 2) (integerp 1)
       (equal (fn-caac-list-carry gm) (fn-scs-summary '((97) (98))))
       (fn-crdt-carry-law '(99) '(112) '(99) '(65) 1 2 1 gm))))
;@hypothesis-removal fn-crd-remote-entry-constructor-has-exact-canonical-carry consumer-octets
(assert-event
 (let ((gm (fn-crdt-list-meta '((97) (98)))))
  (and (not (fn-scc-octet-listp '(999))) (fn-scc-octet-listp '(112)) (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(65)) (integerp 1) (integerp 2) (integerp 1) (equal (fn-caac-list-carry gm) (fn-scs-summary '((97) (98))))
       (not (fn-crdt-carry-law '(999) '(112) '(99) '(65) 1 2 1 gm)))))
;@hypothesis-removal fn-crd-remote-entry-constructor-has-exact-canonical-carry principal-octets
(assert-event
 (let ((gm (fn-crdt-list-meta '((97) (98)))))
  (and (fn-scc-octet-listp '(99)) (not (fn-scc-octet-listp '(999))) (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(65)) (integerp 1) (integerp 2) (integerp 1) (equal (fn-caac-list-carry gm) (fn-scs-summary '((97) (98))))
       (not (fn-crdt-carry-law '(99) '(999) '(99) '(65) 1 2 1 gm)))))
;@hypothesis-removal fn-crd-remote-entry-constructor-has-exact-canonical-carry query-octets
(assert-event
 (let ((gm (fn-crdt-list-meta '((97) (98)))))
  (and (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(112)) (not (fn-scc-octet-listp '(999))) (fn-scc-octet-listp '(65)) (integerp 1) (integerp 2) (integerp 1) (equal (fn-caac-list-carry gm) (fn-scs-summary '((97) (98))))
       (not (fn-crdt-carry-law '(99) '(112) '(999) '(65) 1 2 1 gm)))))
;@hypothesis-removal fn-crd-remote-entry-constructor-has-exact-canonical-carry account-octets
(assert-event
 (let ((gm (fn-crdt-list-meta '((97) (98)))))
  (and (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(112)) (fn-scc-octet-listp '(99)) (not (fn-scc-octet-listp '(999))) (integerp 1) (integerp 2) (integerp 1) (equal (fn-caac-list-carry gm) (fn-scs-summary '((97) (98))))
       (not (fn-crdt-carry-law '(99) '(112) '(99) '(999) 1 2 1 gm)))))
;@hypothesis-removal fn-crd-remote-entry-constructor-has-exact-canonical-carry query-version
(assert-event
 (let ((gm (fn-crdt-list-meta '((97) (98)))))
  (and (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(112)) (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(65)) (not (integerp '(7))) (integerp 2) (integerp 1) (equal (fn-caac-list-carry gm) (fn-scs-summary '((97) (98))))
       (not (fn-crdt-carry-law '(99) '(112) '(99) '(65) '(7) 2 1 gm)))))
;@hypothesis-removal fn-crd-remote-entry-constructor-has-exact-canonical-carry view
(assert-event
 (let ((gm (fn-crdt-list-meta '((97) (98)))))
  (and (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(112)) (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(65)) (integerp 1) (not (integerp '(7))) (integerp 1) (equal (fn-caac-list-carry gm) (fn-scs-summary '((97) (98))))
       (not (fn-crdt-carry-law '(99) '(112) '(99) '(65) 1 '(7) 1 gm)))))
;@hypothesis-removal fn-crd-remote-entry-constructor-has-exact-canonical-carry epoch
(assert-event
 (let ((gm (fn-crdt-list-meta '((97) (98)))))
  (and (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(112)) (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(65)) (integerp 1) (integerp 2) (not (integerp '(7))) (equal (fn-caac-list-carry gm) (fn-scs-summary '((97) (98))))
       (not (fn-crdt-carry-law '(99) '(112) '(99) '(65) 1 2 '(7) gm)))))
;@hypothesis-removal fn-crd-remote-entry-constructor-has-exact-canonical-carry exact-group-carry
(assert-event
 (let ((gm (fn-crdt-list-meta '((97) (98)))))
  (declare (ignore gm))
  (and (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(112)) (fn-scc-octet-listp '(99)) (fn-scc-octet-listp '(65)) (integerp 1) (integerp 2) (integerp 1) (not (equal (fn-caac-list-carry nil) (fn-scs-summary '((97) (98)))))
       (not (fn-crdt-carry-law '(99) '(112) '(99) '(65) 1 2 1 nil)))))

(defun fn-crdt-plan-law (i cep d)
 (declare (xargs :guard t))
 (let ((old (fn-cp-nth 9 cep)))
  (and (eq (fn-cp-nth 0 i) :authenticated)
       (equal (fn-cp-nth 1 old) (fn-cp-nth 4 (fn-cp-nth 1 i)))
       (equal (fn-cp-nth 2 old) (fn-cp-nth 2 i))
       (equal (fn-cp-nth 9 old) (fn-cp-nth 3 i))
       (eq (fn-cp-nth 3 d) :ready)
       (equal (fn-cp-nth 1 d) (fn-crs-key i 7)))))
;@positive fn-crx-selected-existing-plan-is-current-account-scoped
(assert-event
 (let* ((cp (fn-crdt-cp)) (i (fn-crdt-ingress cp :poll nil nil 0))
        (cep (fn-crdt-cep cp)) (d (fn-crdt-definition i '((97) (98))))
        (plan (fn-crx-selected-plan cp i cep d 7)))
  (and (fn-cp-nth 9 cep)
       (member-eq (car plan) '(:definition-proposal :position :status :write :no-op :scan-request))
       (fn-crdt-plan-law i cep d))))
;@hypothesis-removal fn-crx-selected-existing-plan-is-current-account-scoped selected-existing-entry
(assert-event
 (let* ((cp (fn-crat-cp)) (i (fn-crdt-ingress cp :register '((97)) nil 0))
        (cep (fn-crdt-cep cp)) (d (fn-crdt-definition i '((97))))
        (plan (fn-crx-selected-plan cp i cep d 7)))
  (and (not (fn-cp-nth 9 cep))
       (member-eq (car plan) '(:definition-proposal :position :status :write :no-op :scan-request))
       (not (fn-crdt-plan-law i cep d)))))
;@hypothesis-removal fn-crx-selected-existing-plan-is-current-account-scoped non-refused-plan
; Corrupted selected owner; no article or mutation may be dispatched.
(assert-event
 (let* ((cp (fn-crdt-cp)) (i (fn-crdt-ingress cp :poll nil nil 0))
        (cep (update-nth 9 (update-nth 2 '(7) (fn-crdt-old)) (fn-crdt-cep cp)))
        (d (fn-crdt-definition i '((97) (98))))
        (plan (fn-crx-selected-plan cp i cep d 7)))
  (and (fn-cp-nth 9 cep)
       (not (member-eq (car plan) '(:definition-proposal :position :status :write :no-op :scan-request)))
       (not (fn-crdt-plan-law i cep d)))))
