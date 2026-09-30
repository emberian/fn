; Actual owner installation and effects for W9's carried projections.
; Initialization/reclaim put a reconstructed view at their own boundary;
; an ordinary install applies exactly one ledger delta, never a rebuild.
(in-package "ACL2")
(include-book "state-globals")
(include-book "owner-config")
(include-book "retention-obligation-view")

(defun fn-rov-oc-ledger (oc)
  (declare (xargs :guard t))
  (fn-node-retention (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))

(defun fn-owner-obligation-view (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-obligation-view state)
      (f-get-global 'fn-owner-obligation-view state)
    nil))

(defun fn-owner-obligation-view-put (view state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner-obligation-view view state))

(defun fn-rov-owner-ledger (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner state)
      (fn-rov-oc-ledger (f-get-global 'fn-owner state))
    nil))

(defun fn-rov-owner-correspondp (state)
  (declare (xargs :stobjs state :guard t :verify-guards nil))
  (and (boundp-global 'fn-owner state)
       (fn-rov-correspondp (fn-owner-obligation-view state)
                          (fn-retain-pins (fn-rov-owner-ledger state)))))

; This is the exact host-called function, moved from owner-host. Owner
; effects remain one global put. The second global stores the delta view.
(defun fn-owner-install-ocfg (oc state)
  (declare (xargs :stobjs state :guard t))
  (let* ((view (fn-rov-update (fn-rov-owner-ledger state)
                            (fn-rov-oc-ledger oc)
                            (fn-owner-obligation-view state)))
         (state (fn-owner-obligation-view-put view state)))
    (f-put-global 'fn-owner oc state)))

(defthm fn-owner-obligation-view-of-put
  (equal (fn-owner-obligation-view (fn-owner-obligation-view-put view state)) view))

(defthm fn-owner-obligation-view-put-preserves-state-p1
  (implies (state-p1 state)
           (state-p1 (fn-owner-obligation-view-put view state))))

(defthm fn-owner-obligation-view-of-other-global-put
  (implies (not (equal key 'fn-owner-obligation-view))
           (equal (fn-owner-obligation-view (f-put-global key value state))
                  (fn-owner-obligation-view state))))

(defthm fn-owner-installed-ocfg-effect
  (equal (f-get-global 'fn-owner (fn-owner-install-ocfg oc state)) oc))
(defthm fn-owner-installed-owner-bound
  (boundp-global 'fn-owner (fn-owner-install-ocfg oc state)))

(defthm fn-owner-installed-view-effect
  (equal (fn-owner-obligation-view (fn-owner-install-ocfg oc state))
         (fn-rov-update (fn-rov-owner-ledger state) (fn-rov-oc-ledger oc)
                        (fn-owner-obligation-view state))))

(defthm fn-owner-installed-other-global-effect
  (implies (and (not (equal key 'fn-owner))
                (not (equal key 'fn-owner-obligation-view)))
           (equal (f-get-global key (fn-owner-install-ocfg oc state))
                  (f-get-global key state))))

(defthm fn-owner-installed-state-p1
  (implies (state-p1 state) (state-p1 (fn-owner-install-ocfg oc state))))

(defthm fn-rov-owner-installed-ledger
  (equal (fn-rov-owner-ledger (fn-owner-install-ocfg oc state)) (fn-rov-oc-ledger oc)))

; The conditional lemma is an effects boundary, not the claim that every
; writer meets it. Each actual caller must prove its installed ledger's
; transition and the carried relation at entry.
(defthm fn-rov-owner-install-preserves-correspondence
  (implies (fn-rov-correspondp
            (fn-rov-update (fn-rov-owner-ledger state) (fn-rov-oc-ledger oc)
                           (fn-owner-obligation-view state))
            (fn-retain-pins (fn-rov-oc-ledger oc)))
           (fn-rov-owner-correspondp (fn-owner-install-ocfg oc state))))

(defthm fn-rov-owner-install-unchanged-ledger
  (implies (and (fn-rov-owner-correspondp state)
                (equal (fn-rov-oc-ledger oc) (fn-rov-owner-ledger state)))
           (fn-rov-owner-correspondp (fn-owner-install-ocfg oc state)))
  :hints (("Goal" :in-theory (disable fn-owner-install-ocfg)
           :use ((:instance fn-rov-owner-install-preserves-correspondence)))))

; Cold/open and off-mutex reclaim install a supplied reconstruction. The
; pure effects below make the atomic pair explicit; an ordinary transition
; does not call this function.
(defun fn-owner-install-rebuilt-ocfg (oc view state)
  (declare (xargs :stobjs state :guard t))
  (let ((state (fn-owner-obligation-view-put view state)))
    (f-put-global 'fn-owner oc state)))

(defun fn-owner-install-open-ocfg (oc state)
  (declare (xargs :stobjs state
                  :guard (fn-retain-obligation-listp
                          (fn-retain-pins (fn-rov-oc-ledger oc)))))
  (fn-owner-install-rebuilt-ocfg
   oc (fn-rov-build (fn-retain-pins (fn-rov-oc-ledger oc))) state))

(defthm fn-owner-rebuilt-ocfg-effect
  (equal (f-get-global 'fn-owner (fn-owner-install-rebuilt-ocfg oc view state)) oc))
(defthm fn-owner-rebuilt-owner-bound
  (boundp-global 'fn-owner (fn-owner-install-rebuilt-ocfg oc view state)))
(defthm fn-owner-rebuilt-view-effect
  (equal (fn-owner-obligation-view (fn-owner-install-rebuilt-ocfg oc view state)) view))
(defthm fn-owner-rebuilt-other-global-effect
  (implies (and (not (equal key 'fn-owner))
                (not (equal key 'fn-owner-obligation-view)))
           (equal (f-get-global key (fn-owner-install-rebuilt-ocfg oc view state))
                  (f-get-global key state))))
(defthm fn-owner-rebuilt-state-p1
  (implies (state-p1 state)
           (state-p1 (fn-owner-install-rebuilt-ocfg oc view state))))
(defthm fn-rov-owner-rebuilt-ledger
  (equal (fn-rov-owner-ledger (fn-owner-install-rebuilt-ocfg oc view state))
         (fn-rov-oc-ledger oc)))
(defthm fn-rov-owner-rebuilt-establishes-correspondence
  (implies (fn-rov-correspondp view (fn-retain-pins (fn-rov-oc-ledger oc)))
           (fn-rov-owner-correspondp (fn-owner-install-rebuilt-ocfg oc view state))))
(defthm fn-rov-owner-open-establishes-correspondence
  (fn-rov-owner-correspondp (fn-owner-install-open-ocfg oc state))
  :hints (("Goal" :in-theory (disable fn-owner-install-rebuilt-ocfg)
           :use ((:instance fn-rov-owner-rebuilt-establishes-correspondence
                    (view (fn-rov-build (fn-retain-pins (fn-rov-oc-ledger oc)))))))))
(defthm fn-owner-open-state-p1
  (implies (state-p1 state) (state-p1 (fn-owner-install-open-ocfg oc state))))
(defthm fn-owner-open-owner-bound
  (boundp-global 'fn-owner (fn-owner-install-open-ocfg oc state)))

(in-theory (disable fn-rov-oc-ledger fn-owner-obligation-view
                    fn-owner-obligation-view-put fn-rov-owner-ledger
                    fn-rov-owner-correspondp fn-owner-install-ocfg
                    fn-owner-install-rebuilt-ocfg fn-owner-install-open-ocfg))
