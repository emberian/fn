; The actual native POST reservation-refusal and known-abort writers.
; Their bodies and guards are unchanged from host/owner-host.lisp.  The
; writer profile declares the complete host-called carried-state boundary;
; the two retention globals remain authoritative until their private
; carrier migration. No independent shadow copy is introduced.
(in-package "ACL2")
(include-book "def-carried-writer")
(include-book "owner-retain-writer-frame")
(include-book "owner-prepare-outcome")
(include-book "owner-prepare-served-ocl")
(include-book "owner-log-ocl")

(def-carried-profile fn-owner-post-retain
  :invariant fn-owner-retain-statep
  :installers (fn-owner-install-ocfg fn-owner-retain-carry-put)
  :carried-globals (fn-owner fn-owner-retain-carry)
  :at ((oc (fn-owner-ocfg state)))
  :bridge fn-owner-retain-statep-implies-lgoc
  :frame (fn-orh-retain-statep-of-other-global-put
          fn-orh-retain-statep-of-install-ocfg
          fn-orh-retain-statep-of-retain-carry-put)
  :theory (mv-nth nth zp car-cons cdr-cons
           (:executable-counterpart zp) (:executable-counterpart equal))
  ; the guard proofs: the accessors' frame and the store projection the
  ; carried conjuncts read (a writer adds its own :guard-theory)
  :guard-theory (fn-owner-ocfg-of-other-global-put fn-owner-bound-of-other-global-put
                 fn-owner-retain-carry-of-other-global-put
                 fn-owner-bound-of-install-ocfg fn-owner-ocfg-of-install-ocfg
                 fn-owner-retain-carry-of-install-ocfg
                 fn-owner-retain-statep-implies-entry-guard fn-sbud-oc-store)
  ; no :step here: fn-owner-step is host/owner-host.lisp's, absent from any
  ; book world; a writer through it says :step (fn-owner-step EVENT THM)
  :suffix retain-state)


(defthm fn-pout-refuse-reservation-preserves-owner-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp
            (mv-nth 1 (fn-pout-refuse-reservation oc fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-lgoc-refuse-reservation-preserves-invariant
                            (txid (1- (fn-sf-frontier
                                       (fn-sn-files (fn-sbud-oc-store oc)))))))
           :in-theory '(fn-pout-refuse-reservation mv-nth car-cons cdr-cons
                         (:executable-counterpart zp)))))

(defthm fn-pout-known-abort-preserves-owner-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp
            (mv-nth 1 (fn-pout-known-abort oc fn-arena))))
  :rule-classes nil
  :hints (("Goal" :use (fn-psrv-known-abort-preserves-invariant)
           :in-theory '(fn-pout-known-abort mv-nth car-cons cdr-cons
                         (:executable-counterpart zp)))))

(defun fn-owner-refuse-reservation (fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state))))))
  (mv-let (word next)
    (fn-pout-refuse-reservation (fn-owner-ocfg state) fn-arena)
    (let* ((state (fn-owner-install-ocfg next state))
           ; The store holds no transaction now, so the catalog holds no
           ; pending row either (books/served-catalog-join-host-post.lisp
           ; fn-sjh-okp-at-owner-refuse-reservation: LINK with none).
           (state (if (equal word :refused)
                      (f-put-global 'fn-owner-cat-pending nil state)
                    state)))
      (value word))))

(def-carried-writer fn-owner-refuse-reservation
  :profile fn-owner-post-retain
  :bridges ((fn-sn-statep fn-owner-retain-statep-implies-entry-guard))
  :via (fn-pout-refuse-reservation-preserves-owner-invariant))

(defun fn-owner-known-abort (fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state))))))
  (mv-let (word next)
    (fn-pout-known-abort (fn-owner-ocfg state) fn-arena)
    (let* ((state (fn-owner-install-ocfg next state))
           ; The aborted transaction's catalog row goes with it: its pending
           ; row is no longer the store's in-flight row, and a later
           ; non-sealing identity completion would otherwise run the
           ; catalog's finish with it (a :stale-token fault;
           ; books/served-catalog-join-host-post.lisp
           ; fn-sjh-okp-at-owner-known-abort: LINK with none).
           (state (if (equal word :aborted)
                      (f-put-global 'fn-owner-cat-pending nil state)
                    state)))
      (value word))))

(def-carried-writer fn-owner-known-abort
  :profile fn-owner-post-retain
  :bridges ((fn-sn-statep fn-owner-retain-statep-implies-entry-guard))
  :via (fn-pout-known-abort-preserves-owner-invariant))

(defthm fn-owner-refuse-reservation-exact-effects
  (let* ((result (fn-owner-refuse-reservation fn-arena state))
         (next-state (mv-nth 2 result))
         (model (fn-pout-refuse-reservation (fn-owner-ocfg state) fn-arena)))
    (and (equal (mv-nth 0 result) nil)
         (equal (mv-nth 1 result) (mv-nth 0 model))
         (equal (fn-owner-ocfg next-state) (mv-nth 1 model))
         (equal (fn-owner-retain-carry next-state)
                (fn-owner-retain-carry state))))
  :hints (("Goal" :in-theory '(fn-owner-refuse-reservation mv-nth nth
                               car-cons cdr-cons
                               (:executable-counterpart zp)
                               (:executable-counterpart equal)
                               fn-owner-ocfg-of-install-ocfg
                               fn-owner-retain-carry-of-install-ocfg
                               fn-owner-ocfg-of-other-global-put
                               fn-owner-retain-carry-of-other-global-put))))

(defthm fn-owner-known-abort-exact-effects
  (let* ((result (fn-owner-known-abort fn-arena state))
         (next-state (mv-nth 2 result))
         (model (fn-pout-known-abort (fn-owner-ocfg state) fn-arena)))
    (and (equal (mv-nth 0 result) nil)
         (equal (mv-nth 1 result) (mv-nth 0 model))
         (equal (fn-owner-ocfg next-state) (mv-nth 1 model))
         (equal (fn-owner-retain-carry next-state)
                (fn-owner-retain-carry state))))
  :hints (("Goal" :in-theory '(fn-owner-known-abort mv-nth nth
                               car-cons cdr-cons
                               (:executable-counterpart zp)
                               (:executable-counterpart equal)
                               fn-owner-ocfg-of-install-ocfg
                               fn-owner-retain-carry-of-install-ocfg
                               fn-owner-ocfg-of-other-global-put
                               fn-owner-retain-carry-of-other-global-put))))

(in-theory (disable fn-owner-refuse-reservation fn-owner-known-abort))
