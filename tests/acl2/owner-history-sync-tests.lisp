; Ground st teeth plus the actual state-returning entry's startup law.
(in-package "ACL2")
(include-book "../../books/owner-history-sync")
(include-book "../../books/defkeystone")

; Logical states use ACL2's own st constructor. The initial reload set
; models the exact f-put-global in fn-store-sn-reset/open-classified.
(defun fn-hhs-witness-state ()
  (declare (xargs :guard t :verify-guards nil))
  (update-nth 2 (add-pair 'fn-store-sn-hist-reload t (nth 2 (build-state)))
              (build-state)))

(defthm fn-hhs-startup-positive
  (not (fn-host-hist-reloadp
        (mv-nth 1 (fn-host-hist-startup nil nil (fn-hhs-witness-state))))))

(defthm fn-hhs-startup-skipped
  (and (not (fn-host-hist-reloadp
             (mv-nth 1 (fn-host-hist-startup nil nil (fn-hhs-witness-state)))))
       (not (not (fn-host-hist-reloadp (fn-hhs-witness-state)))))
  :hints (("Goal" :in-theory (enable fn-hhs-witness-state fn-host-hist-reloadp))))

(defteeth fn-host-hist-startup-consumes-reload
  :claim (() (not (fn-host-hist-reloadp
                   (mv-nth 1 (fn-host-hist-startup store hist st)))))
  :subject fn-host-hist-startup
  :witness ((store nil) (hist nil) (st (fn-hhs-witness-state)))
  :witness-lemma fn-hhs-startup-positive
  :breaks ()
  :mutations ((skip-first-sync
               (:conclusion (not (fn-host-hist-reloadp st)))
               ((store nil) (hist nil) (st (fn-hhs-witness-state)))
               :fault "install skips its first history synchronization"
               :lemma fn-hhs-startup-skipped)))

(defun fn-hhs-ready-state ()
  (declare (xargs :guard t :verify-guards nil))
  (update-nth 2 (add-pair 'fn-store-sn-hist-reload nil (nth 2 (build-state)))
              (build-state)))

(defthm fn-hhs-frame-positive
  (and (not (equal 'fn-owner 'fn-store-sn-hist-reload))
       (equal (fn-host-hist-reloadp
               (f-put-global 'fn-owner t (fn-hhs-ready-state)))
              (fn-host-hist-reloadp (fn-hhs-ready-state))))
  :rule-classes nil)

(defthm fn-hhs-frame-removed
  (and (not (not (equal 'fn-store-sn-hist-reload 'fn-store-sn-hist-reload)))
       (not (equal (fn-host-hist-reloadp
                    (f-put-global 'fn-store-sn-hist-reload t (fn-hhs-ready-state)))
                   (fn-host-hist-reloadp (fn-hhs-ready-state)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-host-hist-reloadp fn-hhs-ready-state))))

(defteeth fn-host-hist-reloadp-of-other-global-put
  :claim (((other (not (equal key 'fn-store-sn-hist-reload))))
          (equal (fn-host-hist-reloadp (f-put-global key value st))
                 (fn-host-hist-reloadp st)))
  :subject fn-owner-step
  :witness ((key 'fn-owner) (value t) (st (fn-hhs-ready-state)))
  :witness-lemma fn-hhs-frame-positive
  :breaks ((other ((key 'fn-store-sn-hist-reload) (value t)
                  (st (fn-hhs-ready-state))) :lemma fn-hhs-frame-removed))
  :mutations (:not-applicable "the skipped-install mutation is attached to the startup theorem above"))

; A configured empty owner, constructed by the model's normal startup
; constructors, taking a valid :open event. No disk or payload read is used.
(defun fn-hhs-owner-state ()
  (declare (xargs :guard t :verify-guards nil))
  (update-nth 2
    (add-pair 'fn-owner
              (fn-ocfg-make (fn-own-start (fn-sn-initial nil 0) 2)
                            (fn-cfg-initial) nil nil)
              (nth 2 (fn-hhs-ready-state)))
    (fn-hhs-ready-state)))

(defthm fn-hhs-step-positive
  (equal (fn-host-hist-reloadp
          (fn-owner-step '(:open) nil (fn-hhs-owner-state)))
         (fn-host-hist-reloadp (fn-hhs-owner-state))))

(defthm fn-hhs-step-mutation
  (and (equal (fn-host-hist-reloadp
               (fn-owner-step '(:open) nil (fn-hhs-owner-state)))
              (fn-host-hist-reloadp (fn-hhs-owner-state)))
       (not (equal (fn-host-hist-reloadp
                    (f-put-global 'fn-store-sn-hist-reload t
                      (fn-owner-step '(:open) nil (fn-hhs-owner-state))))
                   (fn-host-hist-reloadp (fn-hhs-owner-state)))))
  :hints (("Goal" :in-theory (enable fn-host-hist-reloadp fn-hhs-owner-state
                                    fn-hhs-ready-state))))

(defteeth fn-owner-step-preserves-history-ready
  :claim (() (equal (fn-host-hist-reloadp (fn-owner-step event arena st))
                    (fn-host-hist-reloadp st)))
  :subject fn-owner-step
  :witness ((event '(:open)) (arena nil) (st (fn-hhs-owner-state)))
  :witness-lemma fn-hhs-step-positive
  :breaks ()
  :mutations ((reload-mid-run
               (:conclusion
                (equal (fn-host-hist-reloadp
                        (f-put-global 'fn-store-sn-hist-reload t
                          (fn-owner-step event arena st)))
                       (fn-host-hist-reloadp st)))
               ((event '(:open)) (arena nil) (st (fn-hhs-owner-state)))
               :fault "an owner step sets reload while the service is running"
               :lemma fn-hhs-step-mutation)))

(defthm fn-hhs-ready-witness-is-startup-result-by-definition
  (equal (fn-hhs-ready-state)
         (mv-nth 1 (fn-host-hist-startup nil nil (fn-hhs-witness-state))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hhs-ready-state fn-hhs-witness-state
                                    fn-host-hist-startup))))

(defthm fn-hhs-owner-witness-meets-step-guard
  (and (state-p1 (fn-hhs-owner-state))
       (boundp-global 'fn-owner (fn-hhs-owner-state))
       (fn-sn-statep (fn-own-store (fn-ocfg-owner (fn-owner-ocfg (fn-hhs-owner-state)))))
       (fn-ocfg-eventp (fn-owner-ocfg (fn-hhs-owner-state)) '(:open))
       (not (fn-host-hist-reloadp (fn-hhs-owner-state))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hhs-owner-state fn-hhs-ready-state
                                    fn-owner-ocfg fn-host-hist-reloadp))))
