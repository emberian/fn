(in-package "ACL2")
(include-book "../../books/owner-obligation-completion")
(include-book "identity-retain-carried-tests")

(in-theory (disable (:executable-counterpart fn-rov-correspondp)
                    (:executable-counterpart fn-vdc-correspondp)
                    (:executable-counterpart fn-rov-owner-correspondp)))

(local
 (defthm rovct-ocfg-of-open
   (equal (fn-owner-ocfg (fn-owner-install-open-ocfg oc state)) oc)
   :hints (("Goal" :in-theory (enable fn-owner-ocfg fn-owner-install-open-ocfg
                                      fn-owner-install-rebuilt-ocfg fn-owner-obligation-view-put)))))
(local
 (defthm rovct-ocfg-of-view-put
   (equal (fn-owner-ocfg (fn-owner-obligation-view-put view state)) (fn-owner-ocfg state))
   :hints (("Goal" :in-theory (e/d (fn-owner-obligation-view-put) (put-global))))))

(local
 (defthm rovct-carry-of-view-put
   (equal (fn-owner-retain-carry (fn-owner-obligation-view-put view state))
          (fn-owner-retain-carry state))
   :hints (("Goal" :in-theory (e/d (fn-owner-obligation-view-put) (put-global))))))
(local
 (defthm rovct-view-of-carry-put
   (equal (fn-owner-obligation-view (fn-owner-retain-carry-put carry state))
          (fn-owner-obligation-view state))
   :hints (("Goal" :in-theory (e/d (fn-owner-retain-carry-put) (put-global))))))
(local
 (defthm rovct-ledger-of-carry-put
   (equal (fn-rov-owner-ledger (fn-owner-retain-carry-put carry state))
          (fn-rov-owner-ledger state))
   :hints (("Goal" :in-theory (e/d (fn-owner-retain-carry-put) (put-global))))))

(defthm rovct-positive-completion
  (let ((start (fn-owner-retain-carry-put *irct-fcarry*
               (fn-owner-install-open-ocfg *ois-ordered* state))))
    (and (fn-rov-owner-correspondp start)
         (fn-rov-owner-correspondp
          (mv-nth 2 (fn-owner-finish-synced fn-hist start)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-owner-retain-carry-put)
                                 (put-global fn-rov-owner-correspondp
                                  fn-owner-install-open-ocfg fn-owner-finish-synced)))))

; Corrupted view removes the sole preservation hypothesis at a reachable
; reserved owner: completion refuses and preserves the wrong total. The
; live witness below additionally exercises the corruption through a durable
; signed commit with the concrete decoder attachment.
(defthm rovct-corrupt-total-removes-correspondence
  (let ((bad (fn-owner-obligation-view-put '(100000 . nil)
              (fn-owner-retain-carry-put *irct-carry*
               (fn-owner-install-open-ocfg *pse-k2-reserved* state)))))
    (and (not (fn-rov-owner-correspondp bad))
         (not (fn-rov-owner-correspondp
               (mv-nth 2 (fn-owner-finish-synced fn-hist bad))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-owner-finish-synced
                 fn-rov-owner-correspondp fn-rov-correspondp fn-rov-oc-ledger
                 fn-irc-rix-ocfg-complete fn-irc-rix-own-complete
                 fn-irc-rix-own-complete-enabled)
                (put-global boundp-global fn-owner-install-ocfg fn-owner-install-open-ocfg
                 fn-vdc-correspondp fn-own-refresh-ix
                 fn-irc-rix-ocfg-complete-is-rix fn-irc-rix-own-complete-is-rix
                 fn-irc-rix-own-complete-enabled-is-rix fn-irc-sn-finish-enabled-is-ccar)))))

(defun rovct-live-finish (badp state)
  (declare (xargs :stobjs state :mode :program))
  (with-local-stobj fn-hist
    (mv-let (ok fn-hist state)
      (let* ((fn-hist (fn-hist-load
                       (true-list-fix (fn-sf-records
                         (fn-sn-files (lgt-store *ois-ordered*)))) 0 fn-hist))
             (state (fn-owner-install-open-ocfg *ois-ordered* state))
             (state (fn-owner-retain-carry-put *irct-fcarry* state))
             (state (if badp (fn-owner-obligation-view-put '(100000 . nil) state) state))
             (guards (and (boundp-global 'fn-owner state)
                          (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))
                          (fn-prc-carryp (fn-owner-retain-carry state)))))
        (mv-let (erp word state) (fn-owner-finish-synced fn-hist state)
          (let* ((pins (fn-retain-pins (fn-rov-owner-ledger state)))
                 (view (fn-owner-obligation-view state))
                 (subject (fn-retain-obligation-subject (car pins))))
            (mv (and guards (not erp) (equal word :durable)
                     (equal (lgt-phase (fn-owner-ocfg state)) :ready)
                     (consp pins)
                     (if badp
                         (not (equal (fn-rov-count view) (len pins)))
                       (and (equal (fn-rov-count view) (len pins))
                            (equal (fn-rov-subject subject view)
                                   (fn-vd-oracle-at subject (fn-rov-contribs pins))))))
                fn-hist state))))
      (mv ok state))))
(defun rovct-live-witness (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((old-owner (and (boundp-global 'fn-owner state) (f-get-global 'fn-owner state)))
        (old-carry (fn-owner-retain-carry state))
        (old-view (fn-owner-obligation-view state)))
    (mv-let (positive state) (rovct-live-finish nil state)
      (mv-let (negative state) (rovct-live-finish t state)
        (let* ((state (f-put-global 'fn-owner old-owner state))
               (state (fn-owner-retain-carry-put old-carry state))
               (state (fn-owner-obligation-view-put old-view state)))
          (mv (and positive negative) state))))))
(make-event
 (mv-let (ok state) (rovct-live-witness state)
   (value (list 'assert-event ok))))
