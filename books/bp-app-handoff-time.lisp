; A3 delivery eligibility at one current same-boot observation.  A held
; carrier's kind-5 arrival anchor is durable; an old row without it is
; explicitly unknown and cannot authorize a new Store handoff.  Clock
; uncertainty belongs to that carrier; publication uncertainty is fenced by
; the foundation step and cannot be passed over by this selector.
(in-package "ACL2")
(include-book "bp-app-handoff")

(defun fn-bpah-held-expiry (held observation)
  (declare (xargs :guard t))
  (if (not (and (fn-bpnf-heldp held)
                (fn-clock-observationp observation)))
      :uncertain
    (let* ((primary (fn-bpb-bundle-primary
                     (fn-bpnf-held-bundle held)))
           (anchor (fn-bpn-nth 9 held))
           (creation (fn-bpp-creation-time primary))
           (lifetime (fn-bpp-lifetime primary)))
      (if (not (and (fn-clock-timep creation)
                    (fn-clock-timep lifetime)))
          :uncertain
        (cond
         ((equal anchor '(:wall))
          (fn-clock-expiry-decision
           creation lifetime nil observation))
         ((and (true-listp anchor) (equal (len anchor) 3)
               (equal (car anchor) :observed-age)
               (fn-clock-timep (cadr anchor))
               (fn-clock-timep (caddr anchor))
               (fn-clock-age-anchorp
                (cons (cadr anchor) (caddr anchor))))
          (fn-clock-expiry-decision
           creation lifetime (cons (cadr anchor) (caddr anchor))
           observation))
         (t :uncertain))))))

;; PRF-136: the same decision read from the row's primary block, without
;; fn-bpnf-heldp's re-encoding; a served scan asks it first
;; (fn-bpn-report-find-expired-held), and on a held row it is the decision
;; (fn-bpah-held-expiry-header-of-held).
(defun fn-bpah-held-expiry-header (held observation)
  (declare (xargs :guard t))
  (if (not (and (fn-bpnf-held-primary-blockp held)
                (fn-clock-observationp observation)))
      :uncertain
    (let* ((primary (fn-bpb-bundle-primary
                     (fn-bpnf-held-bundle held)))
           (anchor (fn-bpn-nth 9 held))
           (creation (fn-bpp-creation-time primary))
           (lifetime (fn-bpp-lifetime primary)))
      (if (not (and (fn-clock-timep creation)
                    (fn-clock-timep lifetime)))
          :uncertain
        (cond
         ((equal anchor '(:wall))
          (fn-clock-expiry-decision
           creation lifetime nil observation))
         ((and (true-listp anchor) (equal (len anchor) 3)
               (equal (car anchor) :observed-age)
               (fn-clock-timep (cadr anchor))
               (fn-clock-timep (caddr anchor))
               (fn-clock-age-anchorp
                (cons (cadr anchor) (caddr anchor))))
          (fn-clock-expiry-decision
           creation lifetime (cons (cadr anchor) (caddr anchor))
           observation))
         (t :uncertain))))))

(defthm fn-bpah-held-expiry-header-of-held
  (implies (fn-bpnf-heldp held)
           (equal (fn-bpah-held-expiry-header held observation)
                  (fn-bpah-held-expiry held observation)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-heldp-primary-blockp))
           :in-theory (e/d (fn-bpah-held-expiry-header fn-bpah-held-expiry
                            fn-bpnf-held-primary-blockp)
                           (fn-bpnf-heldp fn-bpb-bundlep fn-bpp-blockp))))
  :rule-classes nil)

(defun fn-bpah-select-oldest-at (held-list node observation selected)
  (declare (xargs :guard t :measure (acl2-count held-list)))
  (if (atom held-list)
      selected
    (let* ((candidate (car held-list))
           (selected
            (if (and (fn-bpah-local-pendingp candidate node)
                     (equal (fn-bpah-held-expiry
                             candidate observation) :live)
                     (or (null selected)
                         (< (nfix (fn-bpn-nth 3 candidate))
                            (nfix (fn-bpn-nth 3 selected)))))
                candidate selected)))
      (fn-bpah-select-oldest-at
       (cdr held-list) node observation selected))))

; If no live carrier can be served, preserve the oldest clock-uncertain
; carrier as an explicit answer to the owner.  It never authorizes Store.
(defun fn-bpah-select-oldest-uncertain-at (held-list node observation selected)
  (declare (xargs :guard t :measure (acl2-count held-list)))
  (if (atom held-list)
      selected
    (let* ((candidate (car held-list))
           (selected
            (if (and (fn-bpah-local-pendingp candidate node)
                     (equal (fn-bpah-held-expiry candidate observation)
                            :uncertain)
                     (or (null selected)
                         (< (nfix (fn-bpn-nth 3 candidate))
                            (nfix (fn-bpn-nth 3 selected)))))
                candidate selected)))
      (fn-bpah-select-oldest-uncertain-at
       (cdr held-list) node observation selected))))

(defun fn-bpah-pending-decision-at (st node observation)
  (declare (xargs :guard t))
  (let ((held (fn-bpah-select-oldest-at
               (fn-bpnf-held-list st) node observation nil)))
    (if (not held)
        (let ((uncertain
               (fn-bpah-select-oldest-uncertain-at
                (fn-bpnf-held-list st) node observation nil)))
          (if uncertain
              (list :uncertain
                    (fn-bpnf-held-key
                     (fn-bpnf-held-principal uncertain)
                     (fn-bpnf-held-id uncertain)))
            nil))
      (let* ((bundle (fn-bpnf-held-bundle held))
             (primary (fn-bpb-bundle-primary bundle))
             (key (fn-bpnf-held-key (fn-bpnf-held-principal held)
                                      (fn-bpnf-held-id held))))
        (if (not (and (fn-bpnf-heldp held)
                      (fn-bpb-bundlep bundle)
                      (fn-bpp-blockp primary)))
            (list :uncertain key)
          (list :ready
                (list :delivery key (fn-bpah-held-class held)
                      (fn-bpb-payload bundle) (fn-bpn-nth 4 held)
                      (fn-bpp-primary-identity primary)
                      (fn-bpaj-eid-text (fn-bpp-source primary))
                      (fn-bpaj-eid-text (fn-bpp-destination primary)))))))))

(defthm fn-bpah-select-oldest-at-is-live
  (implies (and (or (null selected)
                    (equal (fn-bpah-held-expiry selected observation) :live))
                (fn-bpah-select-oldest-at
                 held-list node observation selected))
           (equal (fn-bpah-held-expiry
                   (fn-bpah-select-oldest-at
                    held-list node observation selected)
                   observation)
                  :live))
  :hints (("Goal" :induct (fn-bpah-select-oldest-at
                            held-list node observation selected)
           :in-theory (e/d (fn-bpah-select-oldest-at)
                           (fn-bpah-held-expiry
                            fn-bpah-local-pendingp)))))

(defthm fn-bpah-pending-decision-at-ready-is-live-by-definition
  (implies (equal (car (fn-bpah-pending-decision-at
                        st node observation)) :ready)
           (equal (fn-bpah-held-expiry
                   (fn-bpah-select-oldest-at
                    (fn-bpnf-held-list st) node observation nil)
                   observation)
                  :live))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpah-select-oldest-at-is-live
                            (held-list (fn-bpnf-held-list st))
                            (selected nil)))
           :in-theory (e/d (fn-bpah-pending-decision-at)
                           (fn-bpah-held-expiry
                            fn-bpah-select-oldest-at
                            fn-bpah-select-oldest-at-is-live
                            fn-bpah-select-oldest-uncertain-at
                            fn-bpnf-heldp
                            fn-bpb-bundlep
                            fn-bpp-blockp))))
  :rule-classes nil)

(verify-guards fn-bpah-held-expiry)
(local
 (defthm fn-bpah-primary-blockp-true-listp
   (implies (fn-bpp-blockp primary) (true-listp primary))
   :rule-classes :forward-chaining))
(verify-guards fn-bpah-held-expiry-header
  :hints (("Goal" :in-theory (e/d (fn-bpnf-held-primary-blockp)
                                  (fn-bpp-blockp)))))
(verify-guards fn-bpah-select-oldest-at)
(verify-guards fn-bpah-select-oldest-uncertain-at)
(verify-guards fn-bpah-pending-decision-at)
