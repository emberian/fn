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
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena-attach")
(include-book "../books/history-paged-attach")
(include-book "../books/catalog-paged-attach")
(include-book "../books/owner-host-relation")
(include-book "../books/owner-retain-transitions")
(include-book "../books/owner-connection-callbacks")
(include-book "owner-host")

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

; The held bank is an auxiliary global, including after a logical close
; while physical disposal is outstanding.  It frames the carried Store.
(defthm fn-orh-retain-statep-of-held-open
  (equal (fn-owner-retain-statep (fn-owner-memory-held-open id physical state))
         (fn-owner-retain-statep state))
  :hints (("Goal" :in-theory '(fn-owner-memory-held-open
                               fn-orh-retain-statep-of-other-global-put))))

(defthm fn-orh-retain-statep-of-held-close
  (equal (fn-owner-retain-statep (fn-owner-memory-held-close id state))
         (fn-owner-retain-statep state))
  :hints (("Goal" :in-theory '(fn-owner-memory-held-close
                               fn-orh-retain-statep-of-other-global-put))))

; The admission's returned bank is installed without changing owner or carry.
(defthm fn-orh-retain-statep-of-held-install
 (equal (fn-owner-retain-statep (fn-owner-memory-held-install result state))
        (fn-owner-retain-statep state))
 :hints (("Goal" :in-theory '(fn-owner-memory-held-install
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
                               fn-adm-operator-close fn-owner-memory-held-close
                               fn-owner-memory-held-bank fn-orh-retain-statep-of-other-global-put
                               fn-orh-retain-statep-of-held-close
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
                               fn-adm-operator-close fn-owner-memory-held-close
                               fn-owner-memory-held-bank fn-orh-retain-statep-of-other-global-put
                               fn-orh-retain-statep-of-held-close
                               mv-nth nth zp car-cons cdr-cons
                               (:executable-counterpart zp)
                               fn-orh-retain-statep-of-put-credits
                               fn-orh-retain-statep-of-install-served-effects
                               fn-orh-retain-statep-of-install-ocfg)
           :use ((:instance fn-ohr-fault-preserves-carried-relation
                            (oc (fn-owner-ocfg state)))
                 (:instance fn-owner-retain-statep-implies-lgoc
                            (state state))))))

;; M28 (STEP 5 merge): the priced peer open installs exactly the ocfg open's
;; result, or leaves the ocfg unchanged. This is the named frame fact K1's retained-state
;; proofs of fn-owner-open-peer take (books/owner-retain-live.lisp).
(defthm fn-adm-peer-open-opens-the-ocfg-open-or-nothing
  (let ((opened (fn-exp-at 1 (fn-adm-peer-open oc peer acfg bank configured capacity))))
    (or (equal opened (cons nil oc))
        (equal opened (fn-ocfg-open-peer oc peer acfg))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-adm-peer-open fn-adm-held-open fn-adm-held-open-refusal fn-exp-at nth zp car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart nth) (:executable-counterpart fn-exp-at) (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart binary-+) (:executable-counterpart unary--)) (theory 'minimal-theory)))))

(local (defthm m24-peer-open-owner-preserves-carried-relation
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (cdr (fn-exp-at 1
    (fn-adm-held-open :peer oc xs lim acfg peer address now bank configured capacity)))))
 :hints (("Goal" :use fn-ohr-open-peer-preserves-carried-relation
 :in-theory (union-theories '(fn-adm-held-open fn-adm-held-open-refusal fn-exp-at-of-cons
   car-cons cdr-cons (:executable-counterpart fn-exp-at)
   (:executable-counterpart posp) (:executable-counterpart member-equal))
  (theory 'minimal-theory))))))

(local (defthm m24-rollback-owner-by-definition
 (equal (fn-exp-at 1 (update-nth 3 peak (update-nth 2 bank r))) (fn-exp-at 1 r))
 :hints (("Goal" :expand ((update-nth 3 peak (update-nth 2 bank r))
 (update-nth 2 bank r) (fn-exp-at 1 r))
 :in-theory (union-theories '(fn-exp-at update-nth car-cons cdr-cons fn-cstp-car-update-nth fn-cstp-cdr-update-nth adt-consp-of-update-nth
   (:executable-counterpart zp) (:executable-counterpart binary-+))
  (theory 'minimal-theory))))))

(local (defthm m24-peer-transfer-owner-preserves-carried-relation
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (cdr (fn-exp-at 1
    (fn-adm-transport-rearm :peer oc xs lim acfg peer address now
                            bank old-id configured capacity)))))
 :hints (("Goal" :use ((:instance m24-rollback-owner-by-definition
    (r (fn-adm-held-open :peer oc xs lim acfg peer address now
                         (fn-adm-hh-return bank old-id) configured capacity))
    (peak (nfix (fn-adm-hh-count bank))))) :in-theory (union-theories
 '(fn-adm-transport-rearm fn-adm-held-open-refusal fn-exp-at-of-cons
   m24-rollback-owner-by-definition m24-peer-open-owner-preserves-carried-relation
   car-cons cdr-cons (:executable-counterpart fn-exp-at)
   (:executable-counterpart posp) (:executable-counterpart member-equal))
 (theory 'minimal-theory))))))

(defthm fn-owner-open-peer-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep (mv-nth 2 (fn-owner-open-peer peer-octets state))))
  :hints (("Goal" :in-theory '(fn-owner-open-peer fn-owner-held-callback-open-peer
                               fn-owner-memory-held-install fn-adm-peer-open
                               fn-exp-at m24-peer-open-owner-preserves-carried-relation
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

(defthm fn-owner-peer-rearm-preserves-retain-state
 (implies (fn-owner-retain-statep state)
  (fn-owner-retain-statep (mv-nth 2 (fn-owner-peer-rearm peer-octets old-id state))))
 :hints (("Goal" :in-theory '(fn-owner-peer-rearm fn-owner-held-callback-open-peer
  fn-owner-memory-held-install fn-exp-at mv-nth nth zp car-cons cdr-cons
  (:executable-counterpart zp) m24-peer-transfer-owner-preserves-carried-relation
  fn-orh-retain-statep-of-other-global-put fn-orh-retain-statep-of-install-served-effects
  fn-orh-retain-statep-of-install-ocfg)
  :use ((:instance fn-owner-retain-statep-implies-lgoc (state state))))))

(local (defthm m24-legacy-exposure-keeps-store-by-definition
 (equal (fn-own-store (fn-ocfg-owner (fn-exp-open-ocfg
          (fn-ocar-exp-open oc xs lim acfg peer address now))))
        (fn-own-store (fn-ocfg-owner oc)))
 :hints (("Goal" :in-theory (union-theories
 '(fn-ocar-exp-open fn-exp-open-ocfg fn-exp-at-of-cons car-cons cdr-cons
   fn-ocar-ocfg-open-keeps-store fn-ohr-open-peer-keeps-store-and-view
   (:executable-counterpart fn-exp-at) (:executable-counterpart posp))
 (theory 'minimal-theory))))))

(local (defthm m24-legacy-exposure-preserves-carried-relation
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (fn-exp-open-ocfg (fn-ocar-exp-open oc xs lim acfg peer address now))))
 :hints (("Goal"
  :use ((:instance fn-ohr-carried-of-same-store
          (x (fn-exp-open-ocfg (fn-ocar-exp-open oc xs lim acfg peer address now))))
        (:instance fn-ohr-carried-implies-ocl-relation)
        (:instance fn-ohr-exposure-open-preserves-ocl-relation)
        (:instance m24-legacy-exposure-keeps-store-by-definition))
  :in-theory (union-theories nil (theory 'minimal-theory))))))

; Selector wiring only: the exposure owner accessor is field one.
(local (defthm m24-legacy-exposure-owner-at-preserves-carried-relation-by-definition
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (fn-exp-at 1 (fn-ocar-exp-open oc xs lim acfg peer address now))))
 :hints (("Goal" :use m24-legacy-exposure-preserves-carried-relation
  :in-theory (union-theories '(fn-exp-open-ocfg) (theory 'minimal-theory))))))

(local (defthm m24-exposure-admission-preserves-carried-relation
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (fn-exp-open-ocfg (fn-exp-at 1
   (fn-adm-held-open :exposure oc xs lim acfg peer address now bank configured capacity)))))
 :hints (("Goal" :in-theory (union-theories
  '(fn-adm-held-open fn-adm-held-open-refusal fn-exp-open-ocfg
    fn-exp-at-of-cons m24-legacy-exposure-owner-at-preserves-carried-relation-by-definition
    car-cons cdr-cons (:executable-counterpart fn-exp-at)
    (:executable-counterpart posp) (:executable-counterpart member-equal))
  (theory 'minimal-theory))))))



; Selector wiring only: the transition result contains the exposure result.
(local (defthm m24-exposure-admission-owner-at-preserves-carried-relation-by-definition
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (fn-exp-at 1 (fn-exp-at 1
   (fn-adm-held-open :exposure oc xs lim acfg peer address now bank configured capacity)))))
 :hints (("Goal" :use m24-exposure-admission-preserves-carried-relation
  :in-theory (union-theories '(fn-exp-open-ocfg) (theory 'minimal-theory))))))

(local (defthm m24-exposure-transfer-preserves-carried-relation
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (fn-exp-open-ocfg (fn-exp-at 1
   (fn-adm-transport-rearm :exposure oc xs lim acfg peer address now bank old-id configured capacity)))))
 :hints (("Goal" :use ((:instance m24-rollback-owner-by-definition
    (r (fn-adm-held-open :exposure oc xs lim acfg peer address now
                         (fn-adm-hh-return bank old-id) configured capacity))
    (peak (nfix (fn-adm-hh-count bank))))) :in-theory (union-theories
  '(fn-adm-transport-rearm fn-adm-held-open-refusal fn-exp-open-ocfg
    fn-exp-at-of-cons m24-rollback-owner-by-definition
    m24-exposure-admission-owner-at-preserves-carried-relation-by-definition
    car-cons cdr-cons (:executable-counterpart fn-exp-at)
    (:executable-counterpart posp) (:executable-counterpart member-equal))
  (theory 'minimal-theory))))))

; Selector wiring only: the wrapper installs field one of the exposure result.
(local (defthm m24-exposure-transfer-owner-at-preserves-carried-relation-by-definition
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (fn-exp-at 1 (fn-exp-at 1
   (fn-adm-transport-rearm :exposure oc xs lim acfg peer address now
                           bank old-id configured capacity)))))
 :hints (("Goal" :use m24-exposure-transfer-preserves-carried-relation
  :in-theory (union-theories '(fn-exp-open-ocfg) (theory 'minimal-theory))))))

(defthm fn-owner-exposure-rearm-preserves-retain-state
 (implies (fn-owner-retain-statep state)
  (fn-owner-retain-statep (mv-nth 2
   (fn-owner-exposure-rearm family address peer-octets old-id state))))
 :hints (("Goal" :in-theory '(fn-owner-exposure-rearm fn-owner-held-callback-exposure-open
  fn-orh-retain-statep-of-held-install fn-exp-at fn-exp-open-ocfg mv-nth nth zp car-cons cdr-cons
  (:executable-counterpart zp)
  m24-exposure-transfer-owner-at-preserves-carried-relation-by-definition
  fn-orh-retain-statep-of-other-global-put fn-orh-retain-statep-of-install-served-effects
  fn-orh-retain-statep-of-install-ocfg)
  :use ((:instance fn-owner-retain-statep-implies-lgoc (state state))))))

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

; fn-owner-io: an unsafe observation is refused in the body (state
; unchanged); each safe arm is a configured-owner keystone.  The safe set is
; the served one (fn-psrv-io-safep: any staged record may publish), so the
; :log-order and file arms use the psrv keystones, which need no staged-article
; premise.
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
                 (:instance fn-psrv-log-order-preserves-invariant
                            (oc (fn-owner-ocfg state)))
                 (:instance fn-psrv-rcon-io-preserves-invariant
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
