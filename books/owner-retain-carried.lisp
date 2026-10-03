; owner-retain-carried.lisp -- the owner's carried entry-state relation,
; declared (lane def-carried, 2026-10-01; the def-carried pilot).
;
; `fn-owner-retain-statep' (books/owner-retain-transitions.lisp) is the
; relation the host carries in the ACL2 state across the owner's served
; entries: the owner bound, `fn-lgoc-invariantp' of the configured owner
; (so `fn-sn-statep' of the live Store, by fn-lgoc-invariant-statep) and
; `fn-prc-carryp' of the retention carry.  Until this book its coverage --
; where it is established, which host-called transitions preserve it, what
; it concludes -- was prose beside the theorems.  Here it is one
; `def-carried' form (books/def-carried.lisp), checked against the world:
;
; - established at the recovery install
;   (fn-owner-install-extended-establishes-retain-state,
;   books/owner-recovery-retain.lisp);
; - preserved by the host-called identity prepare
;   (fn-owner-prepare-identity-preserves-retain-state), stated over the
;   HOST SUBJECT `fn-owner-prepare-identity' and the ACL2 state it returns:
;   the host-subject argument D40's withheld owner annotations wait on
;   (planning/decisions.md D40, "implementation status");
; - concluding the entry guard's carried conjuncts
;   (fn-owner-retain-statep-implies-entry-guard).
;
; The form emits the row `fn-owner-retain-carried' in the table
; `fn-carried', the generated statements -- the prepare's preservation
; under its own guard, the install's establishment, the two bridges from
; the relation to the prepare's guard conjuncts -- each proved from the
; named theorem as a hint, and the trace theorem
; `fn-owner-retain-carried-run-carries'.
;
; RAW DISPATCH, AND UNDER WHAT.  The install establishes the relation only on
; its success word :recovering (:ok; on :fault and on :article-numbers-
; damaged -- fn-onb-open-okp, which the install itself checks -- it
; establishes nothing), and only for an owner that is :fault or satisfies
; fn-lgoc-invariantp, a premise no host check can supply and no guard may
; evaluate (fn-cst-relation compares the node to the replay of every event).
; That premise is declared (:hyps) and DISCHARGED at the install's two
; producers (:produced): fn-ock-recover-extended (fn-owner-recover-extended)
; and fn-ock-install of the Store open's pair (fn-owner-recover-from-store-
; open), each under the named assumption A-RECOVERED-OPEN
; (books/assumptions-recovery.lisp): the checkpoint is a capture extension
; (KEYSTONE fn-lgoc-recover-installs-invariant; the recovery-refinement
; subject, PRF-1212/1216).  D40 accepts the row
; because the open is no host entry and every ACL2 caller passes a
; producer's call; tools/interface_emit.py refuses any raw-host call of it.
; The open is witnessed (the empty history's recovery, ground stobj values,
; ACL2's built state): its generated reaches theorem is proved by
; evaluation.  So raw dispatch over this row is a claim UNDER
; A-RECOVERED-OPEN, named.
;
; What remains (the stage-5 work of
; planning/design-store-representation-2026-10-01.md): the carried state is
; the ACL2 state, so every host-called entry that RETURNS state owes a
; preservation theorem; the completeness check reads the `fn-interfaces'
; table, complete only in the image world (host/interfaces.lisp), so it is
; vacuous here and `(def-carried-check fn-owner-retain-carried)' there names
; the first owed entry.  Of the ten entries whose guard walks fn-sn-statep,
; three are transitions here (prepare-identity, -consumer, -topic); the six
; in host/owner-host.lisp (fn-owner-step, -io, -begin, -finish,
; -known-abort, -refuse-reservation) wait on stage 0's host load, and
; fn-owner-finish-synced's state half needs (fn-hist-of-storep fn-hist
; store), a TWO-stobj premise one-stobj rows cannot carry (stage 5).
;
; NOT RAW-DISPATCHED (r29-Q4).  Only an entry this row covers -- the open
; and the three transitions above -- may be declared `:raw-with (:carried
; fn-owner-retain-carried)'.  These state-returning owner entries have no
; preservation theorem here and stay on the executable-counterpart path,
; whole guard evaluated: fn-owner-step, fn-owner-io, fn-owner-begin,
; fn-owner-finish, fn-owner-known-abort, fn-owner-refuse-reservation,
; fn-owner-finish-synced, fn-owner-reconfigure-unstage,
; fn-owner-set-auth-config and fn-owner-orcp-swap.  And until each of them
; carries the relation, the relation is not an invariant of the served
; state, so no entry is raw-dispatched over this row at all: the image
; world's completeness check names the first of them.

; Nothing changes for dependents: this book adds a row, its theorems and the
; trace over functions its includes define; it redefines nothing.

(in-package "ACL2")
(include-book "def-carried")
(include-book "owner-recovery-retain")
(include-book "owner-cursor-domain") ; fn-owner-prepare-consumer, -topic
(include-book "assumptions-recovery") ; A-RECOVERED-OPEN

; -----------------------------------------------------------------------------
; The open's premise, discharged at its producers under A-RECOVERED-OPEN.
; fn-owner-install-extended establishes the relation for an owner that
; satisfies fn-lgoc-invariantp, or refuses (:fault).  The host hands it the
; output of one of two producers (host/owner-host.lisp): fn-ock-recover-
; extended of E (fn-owner-recover-extended) and fn-ock-install of the Store
; open's pair (fn-owner-recover-from-store-open).  Each producer's output is
; :fault or satisfies the invariant when its input is what A-RECOVERED-OPEN
; names (KEYSTONE fn-lgoc-recover-installs-invariant;
; fn-ock-install-of-store-open-by-definition).
(defthm fn-owner-recover-extended-produces-invariant
  (implies (fn-assume-capture-extensionp extended configs)
           (or (equal (fn-ock-recover-extended extended configs frontier max-conns) :fault)
               (fn-lgoc-invariantp (fn-ock-recover-extended extended configs frontier max-conns))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-assume-capture-extension-is-one (e extended))
                        (:instance fn-lgoc-recover-installs-invariant
                                   (prefix (fn-assume-capture-prefix extended configs))
                                   (suffix (fn-assume-capture-suffix extended configs))))
           :in-theory (theory 'minimal-theory))))
(defthm fn-owner-store-open-install-produces-invariant
  (implies (fn-assume-store-open-pairp replayed opened)
           (or (equal (fn-ock-install replayed opened max-conns) :fault)
               (fn-lgoc-invariantp (fn-ock-install replayed opened max-conns))))
  :rule-classes nil
  :hints (("Goal" :use (fn-assume-store-open-pair-is-an-open
                        (:instance fn-ock-install-of-store-open-by-definition
                                   (e (fn-assume-store-open-e replayed opened))
                                   (configs (fn-assume-store-open-configs replayed opened))
                                   (frontier (fn-assume-store-open-frontier replayed opened)))
                        (:instance fn-owner-recover-extended-produces-invariant
                                   (extended (fn-assume-store-open-e replayed opened))
                                   (configs (fn-assume-store-open-configs replayed opened))
                                   (frontier (fn-assume-store-open-frontier replayed opened))))
           :in-theory (theory 'minimal-theory))))
(defthm fn-owner-install-extended-word-when-refused
  (implies (or (equal oc :fault) (not (fn-onb-open-okp (fn-ocfg-owner oc))))
           (not (equal (mv-nth 1 (fn-owner-install-extended
                                  oc extended key fn-arena fn-cat fn-hist fn-owner-st state))
                       :recovering)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-owner-install-extended mv-nth nth zp
                                               car-cons cdr-cons
                                               (:executable-counterpart equal)
                                               (:executable-counterpart zp))
                                             (theory 'minimal-theory)))))
(defthm fn-owner-install-extended-establishes-when-recovering
  (implies (or (equal oc :fault) (fn-lgoc-invariantp oc))
           (if (equal (mv-nth 1 (fn-owner-install-extended
                                 oc extended key fn-arena fn-cat fn-hist fn-owner-st state))
                      :recovering)
               (fn-owner-retain-statep
                (mv-nth 5 (fn-owner-install-extended
                           oc extended key fn-arena fn-cat fn-hist fn-owner-st state)))
             t))
  :rule-classes nil
  :hints (("Goal" :use (fn-owner-install-extended-word-when-refused
                        fn-owner-install-extended-establishes-retain-state)
           :in-theory (theory 'minimal-theory))))

; -----------------------------------------------------------------------------
; Transitions: the host-called consumer and topic prepares (books/owner-
; cursor-domain.lisp) keep the relation, from the owner keystones
; fn-pdc-ocfg-prepare-consumer-preserves-invariant and
; fn-pdc-psrv-prepare-topic-preserves-invariant (the prepares are the carried
; fn-pdc-pout-prepare-consumer/-topic since PRF-1230); the retention carry and the
; owner binding pass through fn-owner-install-ocfg.
(defthm fn-owner-prepare-consumer-preserves-retain-state
  (implies (fn-owner-retain-statep fn-owner-st)
           (fn-owner-retain-statep
            (mv-nth 2 (fn-owner-prepare-consumer event fn-arena fn-owner-st state))))
  :hints (("Goal" :in-theory
           '(fn-owner-retain-statep fn-owner-prepare-consumer
             fn-pdc-pout-prepare-consumer mv-nth nth zp car-cons cdr-cons
             fn-owner-bound-of-install-ocfg fn-owner-ocfg-of-install-ocfg
             fn-owner-retain-carry-of-install-ocfg
             fn-pdc-ocfg-prepare-consumer-preserves-invariant))))
(defthm fn-owner-prepare-topic-preserves-retain-state
  (implies (fn-owner-retain-statep fn-owner-st)
           (fn-owner-retain-statep
            (mv-nth 2 (fn-owner-prepare-topic event fn-arena fn-owner-st state))))
  :hints (("Goal" :in-theory
           '(fn-owner-retain-statep fn-owner-prepare-topic
             fn-pdc-pout-prepare-topic mv-nth nth zp car-cons cdr-cons
             fn-owner-bound-of-install-ocfg fn-owner-ocfg-of-install-ocfg
             fn-owner-retain-carry-of-install-ocfg
             fn-pdc-psrv-prepare-topic-preserves-invariant))))

; -----------------------------------------------------------------------------
; The row.  The open's success word is :recovering (:ok): on :fault and on
; :article-numbers-damaged (fn-onb-open-okp, which the install itself checks)
; it establishes nothing.  The witness is the empty history's recovery (a
; fresh Store under the default configuration, frontier 0, 4 connections),
; ground stobjs' logical values, a zero key and ACL2's built state: the
; generated fn-owner-retain-carried-fn-owner-install-extended-reaches is the
; guard, the premise and :recovering there, proved by evaluation.
(defun fn-owner-retain-witness-oc ()
  (declare (xargs :guard t :verify-guards nil))
  (let ((configs (list *fn-cfg-default-record*)))
    (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture configs nil) configs nil)
                             configs 0 4)))
(defun fn-owner-retain-witness-state ()
  (declare (xargs :guard t :verify-guards nil))
  (build-state))
(def-carried fn-owner-retain-carried
  :invariant fn-owner-retain-statep
  :established ((fn-owner-install-extended
                 fn-owner-install-extended-establishes-when-recovering
                 :ok (equal (mv-nth 1 _) :recovering)
                 :hyps ((or (equal oc :fault) (fn-lgoc-invariantp oc)))
                 :produced ((fn-ock-recover-extended
                             fn-owner-recover-extended-produces-invariant
                             :assuming ((fn-assume-capture-extensionp extended configs)))
                            (fn-ock-install
                             fn-owner-store-open-install-produces-invariant
                             :assuming ((fn-assume-store-open-pairp replayed opened))))
                 :witness ((fn-owner-retain-witness-oc) nil (make-list 32 :initial-element 0)
                           (create-fn-arena$a) (create-fn-cat$a) (create-fn-hist$a)
                           (create-fn-owner-st) (fn-owner-retain-witness-state))))
  :transitions ((fn-owner-prepare-identity
                 fn-owner-prepare-identity-preserves-retain-state)
                (fn-owner-prepare-consumer
                 fn-owner-prepare-consumer-preserves-retain-state)
                (fn-owner-prepare-topic
                 fn-owner-prepare-topic-preserves-retain-state))
  :concludes ((fn-sn-statep fn-owner-retain-statep-implies-entry-guard)
              (fn-prc-carryp fn-owner-retain-statep-implies-entry-guard)))

; The row's D40 data for the one transition: only generated names.
(assert-event
 (equal (fn-cd-raw-with 'fn-owner-retain-carried 'fn-owner-prepare-identity (w state))
        '(fn-owner-retain-carried-fn-owner-prepare-identity-carries
          fn-owner-retain-carried-fn-sn-statep-bridge
          fn-owner-retain-carried-fn-prc-carryp-bridge)))

; In this book's world the row backs raw dispatch of its transition: the
; open's premise is produced (no caller here hands it another argument), and
; completeness is vacuous (no owner fn-interfaces entry is declared here).
; In the image world def-carried-check names every owed transition first.
(assert-event
 (null (fn-cd-raw-problem 'fn-owner-retain-carried 'fn-owner-prepare-identity (w state))))

(in-theory (disable fn-owner-retain-carried-step fn-owner-retain-carried-okp
                    fn-owner-retain-carried-run fn-owner-retain-carried-run-okp))
