; owner-retain-host.lisp -- the owner's carried relation across the host
; writers host/owner-host.lisp defines (stage 5, lane raw-dispatch-3).
;
; fn-owner-retain-statep (books/owner-retain-transitions.lisp) is what D40's
; raw dispatch over fn-owner-retain-carried would skip the guard on: the
; owner bound, fn-lgoc-invariantp of the configured owner (so fn-sn-statep
; of the Store, its whole-log record validation included) and fn-prc-carryp
; of the retention carry (the pin/release disjointness).  The row's
; completeness check counts every host entry that writes the owner's
; globals; each one needs :logic mode, verified guards and the statement
; below.  owner-host.lisp is ld'd, not certified, so the statements live in
; this file, ld'd right after it (the way host/allocation-epoch-host.lisp
; does), and are admitted when the image is built.
;
; Each statement: (implies (fn-owner-retain-statep state)
;                          (fn-owner-retain-statep STATE-RETURNED)).
; The owner half comes from the configured-owner keystone that F carries
; fn-lgoc-invariantp (books/owner-host-relation.lisp, cited by name); the
; retention carry and every other global pass through by the frame lemmas.

(in-package "ACL2")
(include-book "../books/owner-host-relation")
(include-book "../books/owner-retain-transitions")
(include-book "../books/owner-connection-callbacks")

; -----------------------------------------------------------------------------
; The frame: a write to any other global keeps the relation; an install of a
; configured owner that carries fn-lgoc-invariantp establishes the owner half.

(defthm fn-orh-retain-statep-of-other-global-put
  (implies (and (not (equal key 'fn-owner))
                (not (equal key 'fn-owner-retain-carry)))
           (equal (fn-owner-retain-statep (f-put-global key value state))
                  (fn-owner-retain-statep state)))
  :hints (("Goal" :in-theory '(fn-owner-retain-statep
                               fn-owner-ocfg-of-other-global-put
                               fn-owner-bound-of-other-global-put
                               fn-owner-retain-carry-of-other-global-put))))

(defthm fn-owner-retain-statep-implies-lgoc
  (implies (fn-owner-retain-statep state)
           (fn-lgoc-invariantp (fn-owner-ocfg state)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-owner-retain-statep))))

(defthm fn-orh-retain-statep-of-install-ocfg
  (implies (and (fn-owner-retain-statep state)
                (fn-lgoc-invariantp oc))
           (fn-owner-retain-statep (fn-owner-install-ocfg oc state)))
  :hints (("Goal" :in-theory '(fn-owner-retain-statep
                               fn-owner-bound-of-install-ocfg
                               fn-owner-ocfg-of-install-ocfg
                               fn-owner-retain-carry-of-install-ocfg))))

(defthm fn-orh-retain-statep-of-install-served-effects
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (fn-owner-callback-install-effects effects state)))
  :hints (("Goal" :in-theory '(fn-owner-callback-install-effects
                               fn-owner-install-served-effects
                               fn-orh-retain-statep-of-other-global-put))))

(defthm fn-orh-retain-statep-of-put-credits
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (fn-owner-put-credits l state)))
  :hints (("Goal" :in-theory '(fn-owner-put-credits
                               fn-orh-retain-statep-of-other-global-put))))

; -----------------------------------------------------------------------------
; The writers.

(defthm fn-owner-install-effects-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (fn-owner-install-effects effects state)))
  :hints (("Goal" :in-theory '(fn-owner-install-effects
                               fn-orh-retain-statep-of-install-served-effects))))

(defthm fn-owner-close-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (mv-nth 2 (fn-owner-close id fn-arena state))))
  :hints (("Goal" :in-theory '(fn-owner-close fn-owner-callback-close
                               mv-nth nth zp car-cons cdr-cons
                               (:executable-counterpart zp)
                               fn-orh-retain-statep-of-put-credits
                               fn-orh-retain-statep-of-install-ocfg)
           :use ((:instance fn-ohr-step-close-preserves-carried-relation
                            (oc (fn-owner-ocfg state)))
                 (:instance fn-owner-callback-close-branch-unfolds
                            (oc (fn-owner-ocfg state)))
                 (:instance fn-owner-retain-statep-implies-lgoc
                            (state state))))))

(defthm fn-owner-fault-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (mv-nth 2 (fn-owner-fault id state))))
  :hints (("Goal" :in-theory '(fn-owner-fault fn-owner-callback-fault
                               mv-nth nth zp car-cons cdr-cons
                               (:executable-counterpart zp)
                               fn-orh-retain-statep-of-put-credits
                               fn-orh-retain-statep-of-install-served-effects
                               fn-orh-retain-statep-of-install-ocfg)
           :use ((:instance fn-ohr-fault-preserves-carried-relation
                            (oc (fn-owner-ocfg state)))
                 (:instance fn-owner-retain-statep-implies-lgoc
                            (state state))))))

(defthm fn-owner-open-peer-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (mv-nth 2 (fn-owner-open-peer peer-octets state))))
  :hints (("Goal" :in-theory '(fn-owner-open-peer fn-owner-callback-open-peer
                               mv-nth nth zp car-cons cdr-cons
                               (:executable-counterpart zp)
                               fn-orh-retain-statep-of-other-global-put
                               fn-orh-retain-statep-of-install-served-effects
                               fn-orh-retain-statep-of-install-ocfg)
           :use ((:instance fn-ohr-open-peer-preserves-carried-relation
                            (oc (fn-owner-ocfg state))
                            (peer (fn-store-octets->string peer-octets))
                            (acfg (fn-owner-auth state)))
                 (:instance fn-owner-retain-statep-implies-lgoc
                            (state state))))))

(defthm fn-owner-install-node-secret-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (mv-nth 2 (fn-owner-install-node-secret ring state))))
  :hints (("Goal" :in-theory '(fn-owner-install-node-secret fn-owner-replace-core
                               fn-owner-core fn-owner-ocfg
                               mv-nth nth zp car-cons cdr-cons
                               (:executable-counterpart zp)
                               fn-orh-retain-statep-of-install-ocfg)
           :use ((:instance fn-ohr-with-node-secret-preserves-carried-relation
                            (oc (fn-owner-ocfg state)) (secret ring))
                 (:instance fn-owner-retain-statep-implies-lgoc (state state))))))

(defthm fn-owner-apply-limit-profile-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (mv-nth 2 (fn-owner-apply-limit-profile values state))))
  :hints (("Goal" :in-theory '(fn-owner-apply-limit-profile fn-owner-replace-core
                               fn-owner-core fn-owner-ocfg
                               mv-nth nth zp car-cons cdr-cons
                               (:executable-counterpart zp)
                               (:executable-counterpart equal)
                               fn-orh-retain-statep-of-other-global-put
                               fn-orh-retain-statep-of-install-ocfg)
           :use ((:instance fn-ohr-osb-install-preserves-carried-relation
                            (oc (fn-owner-ocfg state)) (profile values))
                 (:instance fn-owner-retain-statep-implies-lgoc (state state))))))

(defthm fn-owner-step-take-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (fn-owner-step (list :take) fn-arena state)))
  :hints (("Goal" :in-theory '(fn-owner-step fn-orh-retain-statep-of-install-ocfg)
           :use ((:instance fn-ohr-step-take-preserves-carried-relation
                            (oc (fn-owner-ocfg state)))
                 (:instance fn-owner-retain-statep-implies-lgoc (state state))))))

(defthm fn-owner-take-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (mv-nth 2 (fn-owner-take fn-arena state))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-owner-take fn-owner-put-credits
                                fn-owner-step-take-preserves-retain-state
                                fn-orh-retain-statep-of-other-global-put)
                              (theory 'minimal-theory)))))

(defthm fn-owner-step-control-submit-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep
            (fn-owner-step (list :control-submit msgid groups octets) fn-arena state)))
  :hints (("Goal" :in-theory '(fn-owner-step fn-orh-retain-statep-of-install-ocfg)
           :use ((:instance fn-ohr-step-control-submit-preserves-carried-relation
                            (oc (fn-owner-ocfg state)))
                 (:instance fn-owner-retain-statep-implies-lgoc (state state))))))

(defthm fn-owner-control-submit-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep
            (mv-nth 2 (fn-owner-control-submit msgid-octets group-octets payload
                                               fn-arena state))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-owner-control-submit
                                fn-owner-step-control-submit-preserves-retain-state
                                fn-orh-retain-statep-of-other-global-put)
                              (theory 'minimal-theory)))))

; The fused grant/prepare installs only on an authorized grant, and then the
; owner fn-pdc-ocfg-prepare-retention makes (books/owner-identity-prepare.lisp
; fn-idrp-retention-preparation-consumes-exact-current-grant), which carries
; the relation (fn-pdc-ocfg-prepare-retention-preserves-invariant).
(defthm fn-owner-idrp-install-preserves-lgoc
  (implies (and (fn-lgoc-invariantp oc)
                (mv-nth 3 (fn-idrp-prepare-retention oc event grant fn-arena)))
           (fn-lgoc-invariantp (mv-nth 1 (fn-idrp-prepare-retention oc event grant fn-arena))))
  :hints (("Goal" :use (fn-idrp-retention-preparation-consumes-exact-current-grant
                        (:instance fn-pdc-ocfg-prepare-retention-preserves-invariant
                                   (e event)))
           :in-theory (theory 'minimal-theory))))

(defthm fn-owner-prepare-retention-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep
            (mv-nth 2 (fn-owner-prepare-retention kind id-octets subject-octets
                                                  evidence-octets charge
                                                  fn-arena state))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-owner-prepare-retention
                                fn-orh-retain-statep-of-other-global-put
                                fn-orh-retain-statep-of-install-ocfg
                                fn-owner-idrp-install-preserves-lgoc)
                              (theory 'minimal-theory))
           :use ((:instance fn-owner-retain-statep-implies-lgoc (state state))))))

; fn-owner-io's guard is the io family's O(1) one (lane carrier S1); the
; carried relation concludes it through the whole store state.
(defthm fn-owner-retain-statep-implies-io-guard
  (implies (fn-owner-retain-statep state)
           (fn-sf-countersp (fn-sn-files (fn-sbud-oc-store (fn-owner-ocfg state)))))
  :hints (("Goal" :in-theory '(fn-sn-statep-implies-files-countersp)
           :use fn-owner-retain-statep-implies-entry-guard)))

; Teeth: the host entry's guard, read from the world, walks no whole log.
(make-event
 (if (intersectp-eq (all-fnnames (guard 'fn-owner-io nil (w state)))
                    '(fn-sf-statep fn-sn-statep fn-sf-record-listp fn-sf-success-listp
                      fn-sf-shapep fn-sn-shapep fn-node-statep fn-lgoc-invariantp))
     (er soft 'fn-owner-io-guard "whole-log predicate in the guard of fn-owner-io")
   (value '(value-triple :fn-owner-io-guard-o1))))

; fn-owner-io: an unsafe observation is refused in the body (state
; unchanged); each safe arm is a configured-owner keystone.
(defthm fn-owner-io-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (mv-nth 2 (fn-owner-io operation result state))))
  :hints (("Goal" :in-theory '(fn-owner-io fn-owner-io-safep fn-sbud-oc-store
                               mv-nth nth zp car-cons cdr-cons
                               (:executable-counterpart zp)
                               fn-orh-retain-statep-of-install-ocfg)
           :use ((:instance fn-owner-retain-statep-implies-lgoc (state state))
                 (:instance fn-lgoc-log-reserve-preserves-invariant
                            (oc (fn-owner-ocfg state)))
                 (:instance fn-lgoc-log-order-preserves-invariant
                            (oc (fn-owner-ocfg state)))
                 (:instance fn-lgoc-rcon-io-preserves-invariant
                            (oc (fn-owner-ocfg state)))))))

; The refusal arm (teeth): an unsafe observation answers :unsafe-observation
; and returns the state it was given, so the refusal is distinct from every
; phase word the step answers and writes nothing.  Both arms are inhabited:
; a reservation is safe on any store, and an operation the file route does
; not name is unsafe on any store.
(defthm fn-owner-io-refuses-an-unsafe-observation
  (implies (not (fn-owner-io-safep (fn-sbud-oc-store (fn-owner-ocfg state))
                                   operation result))
           (and (equal (mv-nth 1 (fn-owner-io operation result state))
                       :unsafe-observation)
                (equal (mv-nth 2 (fn-owner-io operation result state)) state)))
  :hints (("Goal" :in-theory '(fn-owner-io mv-nth nth zp car-cons cdr-cons
                               (:executable-counterpart zp)))))
(assert-event (fn-owner-io-safep nil :log-reserve :ok))
(assert-event (not (fn-owner-io-safep nil :no-such-operation :ok)))
