(in-package "ACL2")
(include-book "../../books/owner-obligation-writers")
(include-book "identity-retain-carried-tests")

(in-theory (disable (:executable-counterpart fn-rov-correspondp)
                    (:executable-counterpart fn-vdc-correspondp)
                    (:executable-counterpart fn-rov-owner-correspondp)))

; Literal antecedent and conclusion on the same configured signed-post
; fixture used by the live wrapper witness below. The quantified relation
; is proved, while the executable witness observes staging and exact view.
(defthm rovwt-positive-correspondence
  (and (fn-rov-owner-correspondp (fn-owner-install-open-ocfg *pse-k2-reserved* state))
       (fn-rov-owner-correspondp
        (mv-nth 2 (fn-owner-prepare-identity *pse-comp* fn-arena
                    (fn-owner-install-open-ocfg *pse-k2-reserved* state)))))
  :hints (("Goal" :in-theory (e/d (fn-rov-oc-ledger)
                                 (fn-owner-prepare-identity fn-rov-owner-correspondp
                                  fn-owner-install-open-ocfg))
           :use ((:instance fn-owner-prepare-identity-preserves-obligation-view
                   (event *pse-comp*)
                   (state (fn-owner-install-open-ocfg *pse-k2-reserved* state)))))))

; Corrupted-state hypothesis removal: wrong total before and after the
; reachable prepare. All actual executable entry guards remain established.
(defthm rovwt-corrupted-total-removes-correspondence
  (let ((bad (fn-owner-obligation-view-put '(100000 . nil)
              (fn-owner-install-open-ocfg *pse-k2-reserved* state))))
    (and (not (fn-rov-owner-correspondp bad))
         (not (fn-rov-owner-correspondp
               (mv-nth 2 (fn-owner-prepare-identity *pse-comp* fn-arena bad))))))
  :hints (("Goal" :in-theory
           (e/d (fn-rov-owner-correspondp fn-rov-correspondp fn-rov-oc-ledger)
                (fn-owner-prepare-identity fn-owner-install-open-ocfg
                 put-global boundp-global fn-rov-owner-ledger fn-rov-owner-ledger-is-oc-ledger
                 fn-vdc-correspondp)))))

(defun rovwt-live-prepare (badp state)
  (declare (xargs :stobjs state :mode :program))
  (with-local-stobj fn-arena
    (mv-let (ok fn-arena state)
      (let* ((fn-arena (fn-arn-seal-many *sr-arena* fn-arena))
             (state (fn-owner-install-open-ocfg *pse-k2-reserved* state))
             (state (fn-owner-retain-carry-put *irct-carry* state))
             (state (if badp (fn-owner-obligation-view-put '(100000 . nil) state) state))
             (view (fn-owner-obligation-view state))
             (ledger (fn-rov-owner-ledger state))
             (entry (and (boundp-global 'fn-owner state)
                          (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))
                          (fn-prc-carryp (fn-owner-retain-carry state)))))
        (mv-let (erp word state) (fn-owner-prepare-identity *pse-comp* fn-arena state)
          (mv (and entry (not erp)
                   (equal word (list :seal (fn-oii-identity-payload *pse-comp*)))
                   (equal (fn-owner-ocfg state) *ois-staged*)
                   (equal (fn-owner-obligation-view state) view)
                   (equal (fn-rov-owner-ledger state) ledger)
                   (if badp
                       (not (equal (fn-rov-count view) (len (fn-retain-pins ledger))))
                     (equal (fn-rov-count view) (len (fn-retain-pins ledger)))))
              fn-arena state)))
      (mv ok state))))

(defun rovwt-live-witness (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((old-owner (if (boundp-global 'fn-owner state) (f-get-global 'fn-owner state) nil))
         (old-carry (fn-owner-retain-carry state))
         (old-view (fn-owner-obligation-view state))
         (old-candidate (if (boundp-global 'fn-owner-cat-candidate state)
                            (f-get-global 'fn-owner-cat-candidate state) nil)))
    (mv-let (positive state) (rovwt-live-prepare nil state)
      (mv-let (negative state) (rovwt-live-prepare t state)
        (let* ((state (f-put-global 'fn-owner old-owner state))
               (state (fn-owner-retain-carry-put old-carry state))
               (state (fn-owner-obligation-view-put old-view state))
               (state (f-put-global 'fn-owner-cat-candidate old-candidate state)))
          (mv (and positive negative) state))))))
(make-event
 (mv-let (ok state) (rovwt-live-witness state)
   (value (list 'assert-event ok))))
