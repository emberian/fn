; Teeth for books/owner-log-ocl.lisp and books/config-store-steps.lisp
; (PRF-285, PRF-286): the configured owner's carried invariant across the
; format-9 commit, the configuration completion and recovery.  The witness is
; owner-advance-carried-tests' configured owner (*scar-t-oc*, config-owner-live-
; tests' recovered owner with a reader open) and its POST article
; (*acar-t-record*), run through the log route's host steps.
(in-package "ACL2")
(include-book "../../books/owner-log-ocl")
(include-book "owner-advance-carried-tests")
(include-book "config-owner-publish-tests")

; -----------------------------------------------------------------------------
; The witnesses: the log route's host steps on the configured owner.
(defconst *lgt-oc0* *scar-t-oc*)
(defconst *lgt-reserved* (fn-olr-ocfg-reserve *lgt-oc0*))
(defconst *lgt-prepared* (fn-sbud-prepare *lgt-reserved* *acar-t-record* 1000000))
(defconst *lgt-ordered* (fn-olr-ocfg-order *lgt-prepared*))
(defconst *lgt-finished*
  (fn-ocfg-with-owner *lgt-ordered*
                      (cdr (in-arena-fn-ccar-own-finish *sr-arena* (fn-ocfg-owner *lgt-ordered*)
                                                        (fn-ocfg-config *lgt-ordered*)))))
(defconst *lgt-refused*
  (in-arena-acar-t-ocfg-run *sr-arena* *lgt-reserved* (list '(:store (:refuse-reservation 8)))))

(defun lgt-phase (oc) (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
(defun lgt-store (oc) (fn-own-store (fn-ocfg-owner oc)))

; A corrupted companion: the owner with its Store's topic prefix counter moved
; off the history's length (fn-sn-statep and fn-ocl-relation do not read it).
(defun lgt-with-topic (oc next)
  (fn-ocfg-with-owner
   oc (fn-ocl-owner-with-store
       (fn-ocfg-owner oc)
       (update-nth 12 (fn-th-prefix-state :ok next nil nil nil nil nil) (lgt-store oc)))))

; -----------------------------------------------------------------------------
; fn-lgoc-log-reserve-preserves-invariant.  Reachable witness: the recovered
; configured owner at :ready carries the invariant; the log route's
; reservation reaches :reserved one past the frontier and carries it.
(assert-event (fn-lgoc-invariantp *lgt-oc0*))
(assert-event (equal (lgt-phase *lgt-oc0*) :ready))
(assert-event (equal (fn-sf-frontier (fn-sn-files (lgt-store *lgt-oc0*))) 8))
(assert-event (fn-lgoc-invariantp *lgt-reserved*))
(assert-event (equal (lgt-phase *lgt-reserved*) :reserved))
(assert-event (equal (fn-sf-frontier (fn-sn-files (lgt-store *lgt-reserved*))) 9))
; Hypothesis fn-lgoc-invariantp (corrupted-state witness): the topic counter
; at 99 over a two-record history; the reservation keeps it, so the
; conclusion fails while the relation itself holds.
(defconst *lgt-bad-oc0* (lgt-with-topic *lgt-oc0* 99))
(assert-event (fn-ocl-relation *lgt-bad-oc0*))
(assert-event (not (fn-lgoc-invariantp *lgt-bad-oc0*)))
(assert-event (not (fn-lgoc-invariantp (fn-olr-ocfg-reserve *lgt-bad-oc0*))))

; -----------------------------------------------------------------------------
; fn-lgoc-sbud-prepare-preserves-invariant.  Reachable witness: at :reserved,
; the article's group fn.letters is served by the live configuration; the
; prepare stages it and carries the invariant.
(assert-event (fn-held-p *acar-t-record*))
(assert-event (fn-cnode-selection-servedp (fn-ocfg-config *lgt-reserved*)
                                          (fn-record-groups *acar-t-record*)))
(assert-event (fn-lgoc-invariantp *lgt-prepared*))
(assert-event (equal (lgt-phase *lgt-prepared*) :record-staged))
(assert-event (equal (fn-sf-record-candidate (fn-sn-files (lgt-store *lgt-prepared*)))
                     *acar-t-record*))
; Hypothesis "served" (reachable witness): a live configuration completion
; retires fn.letters (generation 5; the name stays in the Store's allocation
; domain), the owner carries the invariant, and the prepare -- which does not
; test the served table itself -- stages the article anyway: the configured
; relation fails, because the configured replay refuses an article in a
; group its configuration does not serve.  host/owner-host.lisp
; fn-owner-prepare-buffer tests fn-cnode-selection-servedp before it calls
; the prepare; that test is what the theorem's hypothesis names.
(defconst *lgt-retire*
  (fn-cfg-record-make 4 8 5 (list (fn-cfg-remove-group "fn.letters"))
                      *fn-cfg-default-stamp*))
(defconst *lgt-retired*
  (cadr (mv-list 2 (fn-oclc-publish (fn-ocfg-make (fn-ocfg-owner *lgt-oc0*)
                                                  (fn-ocfg-config *lgt-oc0*)
                                                  (fn-ocfg-pins *lgt-oc0*) *lgt-retire*)
                                    5 1000000))))
(defconst *lgt-r-reserved* (fn-olr-ocfg-reserve *lgt-retired*))
(defconst *lgt-r-prepared* (fn-sbud-prepare *lgt-r-reserved* *acar-t-record* 1000000))
(assert-event (equal (fn-cfg-generation (fn-ocfg-config *lgt-retired*)) 5))
(assert-event (fn-lgoc-invariantp *lgt-r-reserved*))
(assert-event (member-equal "fn.letters" (fn-sn-groups (lgt-store *lgt-r-reserved*))))
(assert-event (not (fn-cnode-selection-servedp (fn-ocfg-config *lgt-r-reserved*)
                                               (fn-record-groups *acar-t-record*))))
(assert-event (equal (lgt-phase *lgt-r-prepared*) :record-staged))
(assert-event (not (fn-ocl-relation *lgt-r-prepared*)))
(assert-event (not (fn-cst-relation (lgt-store *lgt-r-prepared*))))
; Hypothesis fn-lgoc-invariantp (corrupted-state witness): the topic counter
; off at :reserved; the staged article's topic step faults, so the companion
; fails after the prepare.
(defconst *lgt-bad-reserved* (lgt-with-topic *lgt-reserved* 99))
(assert-event (fn-ocl-relation *lgt-bad-reserved*))
(assert-event (not (fn-lgoc-invariantp *lgt-bad-reserved*)))
(assert-event (not (fn-lgoc-invariantp
                    (fn-sbud-prepare *lgt-bad-reserved* *acar-t-record* 1000000))))

; fn-lgoc-pidx-sbud-prepare-preserves-invariant: the host's prepare, with its
; two carried index premises, on the same witness.
(assert-event (fn-scar-view-indexedp (fn-ocfg-owner *lgt-reserved*)))

(assert-event (equal (fn-pidx-sbud-prepare *lgt-reserved* *acar-t-record* 1000000)
                     *lgt-prepared*))
(assert-event (fn-lgoc-invariantp (fn-pidx-sbud-prepare *lgt-reserved* *acar-t-record* 1000000)))

; -----------------------------------------------------------------------------
; fn-lgoc-log-order-preserves-invariant.  Reachable witness: the staged article
; ordered into the log reaches :completing with the history one record longer
; and carries the invariant.
(assert-event (fn-lgoc-article-stagedp (lgt-store *lgt-prepared*)))
(assert-event (fn-lgoc-invariantp *lgt-ordered*))
(assert-event (equal (lgt-phase *lgt-ordered*) :completing))
(assert-event (equal (len (fn-sf-records (fn-sn-files (lgt-store *lgt-ordered*)))) 3))
; Hypothesis fn-lgoc-invariantp -- THE FINDING (corrupted-state witness): at
; :record-attempted fn-ocl-relation holds with the topic counter off, and the
; directory observation that publishes the article leaves an owner that does
; NOT satisfy fn-ocl-relation: its :completing arm asks the topic prefix to
; accept the completion record.  fn-ocl-relation alone is not closed under
; the order step; the companion fn-cstp-carriedp is what carries it.
(defconst *lgt-attempted*
  (fn-rcon-ocfg-io (fn-rcon-ocfg-io *lgt-prepared* :record-file :ok) :record-link :ok))
(defconst *lgt-bad-attempted* (lgt-with-topic *lgt-attempted* 99))
(assert-event (equal (lgt-phase *lgt-attempted*) :record-attempted))
(assert-event (fn-lgoc-invariantp *lgt-attempted*))
(assert-event (fn-ocl-relation *lgt-bad-attempted*))
(assert-event (not (fn-cstp-carriedp (lgt-store *lgt-bad-attempted*))))
(assert-event (fn-lgoc-article-stagedp (lgt-store *lgt-bad-attempted*)))
(assert-event (not (fn-ocl-relation (fn-olr-ocfg-order *lgt-bad-attempted*))))
(assert-event (equal (lgt-phase (fn-olr-ocfg-order *lgt-bad-attempted*)) :completing))
; Hypothesis fn-lgoc-article-stagedp is the proof's scope (the article
; commit), not a known counterexample: no witness is claimed for it.

; -----------------------------------------------------------------------------
; fn-lgoc-finish-preserves-invariant.  Reachable witness: the finish returns
; to :ready with three records and carries the invariant.
(assert-event (fn-lgoc-invariantp *lgt-finished*))
(assert-event (equal (lgt-phase *lgt-finished*) :ready))
(assert-event (equal (len (fn-sf-records (fn-sn-files (lgt-store *lgt-finished*)))) 3))
; Hypothesis (corrupted-state witness): at :completing with the topic counter
; off the completion is not enabled, the finish changes nothing, and the
; owner satisfies neither conjunct's companion.
(defconst *lgt-bad-ordered* (lgt-with-topic *lgt-ordered* 99))
(assert-event (not (fn-lgoc-invariantp *lgt-bad-ordered*)))
(assert-event
 (not (fn-lgoc-invariantp
       (fn-ocfg-with-owner *lgt-bad-ordered*
                           (cdr (in-arena-fn-ccar-own-finish *sr-arena* (fn-ocfg-owner *lgt-bad-ordered*)
                                                             (fn-ocfg-config *lgt-bad-ordered*)))))))

; -----------------------------------------------------------------------------
; fn-lgoc-refuse-reservation-preserves-invariant.  Reachable witness: the
; refused reservation returns to :ready at the spent frontier.
(assert-event (fn-lgoc-invariantp *lgt-refused*))
(assert-event (equal (lgt-phase *lgt-refused*) :ready))
(assert-event (equal (fn-sf-frontier (fn-sn-files (lgt-store *lgt-refused*))) 9))
(assert-event
 (not (fn-lgoc-invariantp
       (in-arena-acar-t-ocfg-run *sr-arena* *lgt-bad-reserved*
                                 (list '(:store (:refuse-reservation 8)))))))

; -----------------------------------------------------------------------------
; fn-lgoc-publish-preserves-invariant.  Reachable witness:
; config-owner-publish-tests' staged group request completes :durable and
; the published owner carries the invariant.
(assert-event (fn-lgoc-invariantp *ocp-closed*))
(assert-event (equal (car (mv-list 2 (fn-oclc-publish *ocp-closed* 3 *ocp-max*))) :durable))
(assert-event (fn-lgoc-invariantp (cadr (mv-list 2 (fn-oclc-publish *ocp-closed* 3 *ocp-max*)))))
; Hypothesis: the forged owner (its configuration is not the replayed one)
; answers :recovery-required and keeps an owner without the invariant.
(assert-event (not (fn-lgoc-invariantp *ocp-forged*)))
(assert-event (not (fn-lgoc-invariantp (cadr (mv-list 2 (fn-oclc-publish *ocp-forged* 3 *ocp-max*))))))

; -----------------------------------------------------------------------------
; fn-lgoc-recover-installs-invariant.  Reachable witness: the owner installed
; from a checkpoint capture extended over the rest of the history.
(defconst *lgt-rc-events*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-lgt" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-lgt" "subject" "evidence" 0)))
(defconst *lgt-rc-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
(defconst *lgt-rc*
  (fn-ock-recover-extended
   (fn-sco-extend (fn-sco-capture *lgt-rc-configs* (list (car *lgt-rc-events*)))
                  *lgt-rc-configs* (cdr *lgt-rc-events*))
   *lgt-rc-configs* 8 4))
(assert-event (not (equal *lgt-rc* :fault)))
(assert-event (fn-lgoc-invariantp *lgt-rc*))
(assert-event (equal (lgt-phase *lgt-rc*) :recovering))
; Hypothesis: with no connection bound the install answers :fault, which does
; not carry the invariant.
(assert-event
 (not (fn-lgoc-invariantp
       (fn-ock-recover-extended
        (fn-sco-extend (fn-sco-capture *lgt-rc-configs* (list (car *lgt-rc-events*)))
                       *lgt-rc-configs* (cdr *lgt-rc-events*))
        *lgt-rc-configs* 8 nil))))
; The recovery barriers carry it on (fn-lgoc-rcon-io-preserves-invariant).
(defconst *lgt-rc-ready*
  (fn-rcon-ocfg-io (fn-rcon-ocfg-io (fn-rcon-ocfg-io
    *lgt-rc* :recovery-barrier :ok) :recovery-barrier :ok) :recovery-barrier :ok))
(assert-event (equal (lgt-phase *lgt-rc-ready*) :ready))
(assert-event (fn-lgoc-invariantp *lgt-rc-ready*))

; -----------------------------------------------------------------------------
; books/config-store-steps.lisp (PRF-285): the Store-level keystones on the
; same witnesses.
(defconst *lgt-s-ready* (lgt-store *lgt-oc0*))
(defconst *lgt-s-reserved* (lgt-store *lgt-reserved*))
(defconst *lgt-s-prepared* (lgt-store *lgt-prepared*))
(defconst *lgt-s-attempted* (lgt-store *lgt-attempted*))

; fn-cstp-reserve-io-preserves-relation: the first reservation step.
(assert-event (fn-cst-relation *lgt-s-ready*))
(assert-event (fn-cst-relation (fn-sn-io *lgt-s-ready* :start-frontier nil)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-sn-io *lgt-s-ready* :start-frontier nil)))
                     :frontier-staged))
; without fn-cst-relation (corrupted-state witness): the node advanced past
; the frontier (still a node state, so the step runs).
(defconst *lgt-s-far-ready*
  (update-nth 3 (fn-replay-advance-txid (fn-sn-node *lgt-s-ready*) 20) *lgt-s-ready*))
(assert-event (fn-sn-statep *lgt-s-far-ready*))
(assert-event (not (fn-cst-relation *lgt-s-far-ready*)))
(assert-event (not (fn-cst-relation (fn-sn-io *lgt-s-far-ready* :start-frontier nil))))

; fn-cstp-spc-prepare-preserves-relation: served (above), and without the
; served hypothesis the retired-group witness.
(assert-event (fn-cst-relation *lgt-s-reserved*))
(assert-event (fn-cpr-event-servedp
               (fn-cstp-fold (fn-sn-config-history *lgt-s-reserved*)
                             (fn-sf-records (fn-sn-files *lgt-s-reserved*)))
               *acar-t-record*))
(assert-event (equal (fn-spc-prepare *lgt-s-reserved* *acar-t-record*) *lgt-s-prepared*))
(assert-event (fn-cst-relation *lgt-s-prepared*))
(defconst *lgt-s-r-reserved* (lgt-store *lgt-r-reserved*))
(assert-event (fn-cst-relation *lgt-s-r-reserved*))
(assert-event (not (fn-cpr-event-servedp
                    (fn-cstp-fold (fn-sn-config-history *lgt-s-r-reserved*)
                                  (fn-sf-records (fn-sn-files *lgt-s-r-reserved*)))
                    *acar-t-record*)))
(assert-event (not (fn-cst-relation (fn-spc-prepare *lgt-s-r-reserved* *acar-t-record*))))

; fn-cstp-record-io-preserves-relation: the record file step.
(assert-event (fn-cst-relation (fn-sn-io *lgt-s-prepared* :record-file :ok)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-sn-io *lgt-s-prepared* :record-file :ok)))
                     :record-data-durable))

; fn-cstp-held-record-dir-preserves-relation: the publishing observation, and
; without fn-cstp-carriedp the corrupted topic counter.
(assert-event (fn-cst-relation *lgt-s-attempted*))
(assert-event (fn-cstp-carriedp *lgt-s-attempted*))
(assert-event (fn-held-p (fn-sf-record-candidate (fn-sn-files *lgt-s-attempted*))))
(assert-event (fn-cst-relation (fn-sn-io *lgt-s-attempted* :record-directory :ok)))
(assert-event (fn-cstp-carriedp (fn-sn-io *lgt-s-attempted* :record-directory :ok)))
(defconst *lgt-s-bad-attempted* (lgt-store *lgt-bad-attempted*))
(assert-event (fn-cst-relation *lgt-s-bad-attempted*))
(assert-event (not (fn-cstp-carriedp *lgt-s-bad-attempted*)))
(assert-event (not (fn-cst-relation (fn-sn-io *lgt-s-bad-attempted* :record-directory :ok))))
(assert-event (not (fn-sn-completion-enabledp
                    (fn-sn-io *lgt-s-bad-attempted* :record-directory :ok))))

; fn-cstp-refuse-reservation-preserves.
(assert-event (fn-cst-relation (fn-sn-refuse-reservation *lgt-s-reserved* 8)))
(assert-event (fn-cstp-carriedp (fn-sn-refuse-reservation *lgt-s-reserved* 8)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-sn-refuse-reservation *lgt-s-reserved* 8)))
                     :ready))

; fn-cstp-replay-append-event: the configured fold over the history extended
; by the article is one step from the fold without it, and recoverable one
; past the article's transaction id.
(defconst *lgt-s-configs* (fn-sn-config-history *lgt-s-reserved*))
(defconst *lgt-s-events* (fn-sf-records (fn-sn-files *lgt-s-reserved*)))
(assert-event (fn-cst-recoverablep *lgt-s-configs* *lgt-s-events* 8))
(assert-event (equal (fn-store-event-sequence *acar-t-record*) (len *lgt-s-events*)))
(assert-event (equal (fn-store-event-txid *acar-t-record*) 8))
(assert-event (fn-cst-recoverablep *lgt-s-configs* (append *lgt-s-events* (list *acar-t-record*)) 9))
(assert-event (equal (fn-cst-replay-node *lgt-s-configs*
                                         (append *lgt-s-events* (list *acar-t-record*)) 9)
                     (fn-replay-apply-record (fn-cst-replay-node *lgt-s-configs* *lgt-s-events* 8)
                                             *acar-t-record*)))

; fn-cstp-open-establishes-carriedp.
(assert-event (equal (fn-sn-open-kind (fn-cpo-open-observed *lgt-rc-configs* 8 *lgt-rc-events*))
                     :ok))
(assert-event (fn-cstp-carriedp
               (fn-sn-open-state (fn-cpo-open-observed *lgt-rc-configs* 8 *lgt-rc-events*))))

; -----------------------------------------------------------------------------
; books/config-owner-carried.lisp (PRF-287): the live request's authorization
; from the carried state.
(defun lgt-reopens (oc)
  ; The conclusion of fn-oclc-authorized-record-reopens, evaluated.
  (let* ((st (fn-own-store (fn-ocfg-owner oc)))
         (record (fn-ocfg-staged oc)))
    (mv-let (next config1)
      (fn-oclc-configure st (fn-ocfg-config oc) record)
      (and (fn-cpo-history-relation next)
           (equal (fn-sn-config-history next)
                  (append (fn-sn-config-history st) (list record)))
           (equal (fn-sf-records (fn-sn-files next)) (fn-sf-records (fn-sn-files st)))
           (equal (fn-sf-frontier (fn-sn-files next)) (fn-sf-frontier (fn-sn-files st)))
           (equal config1 (fn-ocl-store-config next))))))

; Reachable witness: the staged group request is authorized, its completion
; is :durable, and the history reopens to what it installs.
(assert-event (fn-ocl-relation *ocp-closed*))
(assert-event (fn-oclc-live-authorizep *ocp-closed*))
(assert-event (equal (car (mv-list 2 (fn-oclc-publish *ocp-closed* 3 *ocp-max*))) :durable))
(assert-event (lgt-reopens *ocp-closed*))
; An unauthorized request: the retirement staged against a Store whose
; frontier moved past the record's transaction id (the refused reservation
; spent 8).  The invariant holds; the authorization refuses; had it been
; published, the completion would answer :recovery-required; and the reopen
; conclusion fails (the history is not extended).
(defconst *lgt-stale*
  (fn-ocfg-make (fn-ocfg-owner *lgt-refused*) (fn-ocfg-config *lgt-refused*)
                (fn-ocfg-pins *lgt-refused*) *lgt-retire*))
(assert-event (fn-ocl-relation *lgt-stale*))
(assert-event (not (fn-oclc-live-authorizep *lgt-stale*)))
(assert-event (equal (car (mv-list 2 (fn-oclc-publish *lgt-stale* 5 *ocp-max*)))
                     :recovery-required))
(assert-event (not (lgt-reopens *lgt-stale*)))
; fn-oclc-authorized-record-reopens without fn-ocl-relation (corrupted-state
; witness): the staged request's Store with its node replaced by the initial
; node (a node state; the history is two records): the authorization admits
; the record, and the installed Store does not reopen to it.
(defconst *lgt-hollow*
  (let* ((o (fn-ocfg-owner *ocp-closed*))
         (st (fn-own-store o))
         (st2 (update-nth 3 (fn-node-initial-state (fn-sn-groups st) (fn-sn-capacity st)) st)))
    (fn-ocfg-with-owner *ocp-closed* (fn-ocl-owner-with-store o st2))))
(assert-event (not (fn-ocl-relation *lgt-hollow*)))
(assert-event (fn-oclc-live-authorizep *lgt-hollow*))
(assert-event (not (lgt-reopens *lgt-hollow*)))
; fn-oclc-live-authorizep-is-durable-completion without the generation
; hypothesis: the authorized request asked at generation 4 is refused.
(assert-event (not (equal (fn-cfg-record-generation (fn-ocfg-staged *ocp-closed*)) 4)))
(assert-event (equal (car (mv-list 2 (fn-oclc-publish *ocp-closed* 4 *ocp-max*))) :refused))

; =============================================================================
; Audit packets G1-4 (PRF-286) and G5-7 (PRF-285), lane audit-fixes.
; -----------------------------------------------------------------------------
; G1-4, fn-lgoc-log-order-preserves-invariant's (fn-lgoc-article-stagedp ...).
; The only non-article candidate the owner stages at a record phase is a
; retention event (fn-sn-prepare-retention; a configuration record goes
; through fn-oclc-complete, never the record files).  Staged on the reserved
; owner and ordered, it keeps the invariant: at this reachable state the
; hypothesis is not needed.  It is redundant: the weakened theorem is
; fn-psrv-log-order-preserves-invariant, restated by name in
; owner-prepare-served-events-tests (g12b-lgoc-log-order-...).
(defun lgt-ret-event (oc kind charge)
  (let* ((s (lgt-store oc))
         (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (fn-store-retention-event-make kind (fn-sn-identity-next s) txid txid "obl" "sub" "evi" charge)))
(defconst *lgt-ret-staged*
  (in-arena-acar-t-ocfg-run *sr-arena* *lgt-reserved*
                            (list (list :store (list :prepare-retention (lgt-ret-event *lgt-reserved* :undertake 1))))))
(defconst *lgt-ret-attempted*
  (fn-rcon-ocfg-io (fn-rcon-ocfg-io *lgt-ret-staged* :record-file :ok) :record-link :ok))
(assert-event
 (and (equal (lgt-phase *lgt-ret-staged*) :record-staged)
      (fn-lgoc-invariantp *lgt-ret-staged*)
      (not (fn-lgoc-article-stagedp (lgt-store *lgt-ret-staged*)))
      (equal (lgt-phase (fn-olr-ocfg-order *lgt-ret-staged*)) :completing)
      (fn-lgoc-invariantp (fn-olr-ocfg-order *lgt-ret-staged*))))

; G1-4, fn-lgoc-rcon-io-preserves-invariant's (fn-lgoc-io-safep ...).  Every
; observation outside the safe set tried on reached owners keeps the
; invariant: the excluded directory :ok at :record-attempted over the
; retention candidate, an unknown operation, a directory observation at
; :ready, a barrier and a :complete word at :record-staged.  No tooth exists
; on these witnesses.  The hypothesis is redundant: the weakened theorem is
; proved in owner-prepare-served-events-tests
; (g12b-lgoc-rcon-io-preserves-invariant-without-io-safep, through
; fn-snt-unknown-io-is-no-op for the operations fn-sn-file-step does not
; name).
(assert-event
 (and (fn-lgoc-invariantp *lgt-ret-attempted*)
      (equal (lgt-phase *lgt-ret-attempted*) :record-attempted)
      (not (fn-lgoc-io-safep (lgt-store *lgt-ret-attempted*) :record-directory :ok))
      (fn-lgoc-invariantp (fn-rcon-ocfg-io *lgt-ret-attempted* :record-directory :ok))
      (not (fn-lgoc-io-safep (lgt-store *lgt-reserved*) :foo :ok))
      (equal (fn-rcon-ocfg-io *lgt-reserved* :foo :ok) *lgt-reserved*)
      (fn-lgoc-invariantp (fn-rcon-ocfg-io *lgt-oc0* :record-directory :ok))
      (fn-lgoc-invariantp (fn-rcon-ocfg-io *lgt-prepared* :recovery-barrier :ok))
      (fn-lgoc-invariantp (fn-rcon-ocfg-io *lgt-prepared* :complete :ok))))

; G1-4, fn-lgoc-pidx-sbud-prepare-preserves-invariant's two index premises.
; CORRUPTED owner: the finished owner (it holds the article) reserved again,
; its view's Message-ID trie replaced by the empty trie (it hides the held
; article; fn-scar-view-indexedp fails, the invariant holds).  A record under
; the held Message-ID is still refused (the owner is unchanged, so the
; invariant holds after it), and a fake trie refuses a fresh record
; (post-identity-index-tests).  A corrupted index turns the host's prepare
; into a refusal, never into a staging the invariant rejects, on every
; witness tried; the premises are those of the bridge fn-pidx = fn-sbud
; (post-identity-index-tests' teeth), not of this invariant.  No tooth here.
; The Store index premise (fn-ceis-indexedp) is redundant: the weakened
; theorem is proved in owner-prepare-served-events-tests
; (g12b-lgoc-pidx-sbud-prepare-without-ceis-indexedp).
(defconst *lgt-f-reserved* (fn-olr-ocfg-reserve *lgt-finished*))
(defun lgt-view-with-index (v index)
  (fn-own-view-make-visible
   (fn-own-view-version v) (fn-own-view-frontier v) (fn-own-view-archive v)
   (fn-own-view-verdicts v) index (fn-own-view-group-index v) (fn-own-view-withdrawals v)
   (fn-own-view-raw v) (fn-own-view-withdrawn v) (fn-own-view-keyring v)))
(defun lgt-owner-with-view (o v)
  (fn-own-make (fn-own-store o) v (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
               (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
               (fn-own-node-secret o) (fn-own-refused o)))
(defconst *lgt-blind-reserved*
  (fn-ocfg-with-owner *lgt-f-reserved*
                      (lgt-owner-with-view (fn-ocfg-owner *lgt-f-reserved*)
                                           (lgt-view-with-index (fn-own-view (fn-ocfg-owner *lgt-f-reserved*))
                                                                (fn-midx-build nil)))))
(make-event
 `(defconst *lgt-blind-prepared*
    ',(with-guard-checking :none
        (fn-pidx-sbud-prepare *lgt-blind-reserved* (own-record 3 9 "<ocmt@example>") 1000000))))
(assert-event
 (and (fn-lgoc-invariantp *lgt-blind-reserved*)
      (not (fn-scar-view-indexedp (fn-ocfg-owner *lgt-blind-reserved*)))
      (equal (lgt-phase *lgt-blind-prepared*) :reserved)
      (fn-lgoc-invariantp *lgt-blind-prepared*)))
; fn-lgoc-ocl-relation-of-owner-with-store is a lemma of the step keystones
; (their hints instantiate it); it is no longer a registry event of PRF-286.

; -----------------------------------------------------------------------------
; G5-7 (PRF-285): books/config-store-steps.lisp companions.
; fn-cstp-finish-preserves-carriedp.  Positive: the ordered article's Store at
; :completing.  Removal of carriedp (CORRUPTED: the topic counter at 99).
; The :completing hypothesis: at :record-staged the finish changes nothing
; and carriedp holds after it, so no tooth exists on this witness.
(defconst *lgt-s-ordered* (lgt-store *lgt-ordered*))
(defconst *lgt-s-bad-ordered* (lgt-store *lgt-bad-ordered*))
(assert-event
 (and (fn-cstp-carriedp *lgt-s-ordered*)
      (equal (fn-sf-phase (fn-sn-files *lgt-s-ordered*)) :completing)
      (fn-cstp-carriedp (fn-sn-finish *lgt-s-ordered*))))
(assert-event
 (and (not (fn-cstp-carriedp *lgt-s-bad-ordered*))
      (equal (fn-sf-phase (fn-sn-files *lgt-s-bad-ordered*)) :completing)
      (not (fn-cstp-carriedp (fn-sn-finish *lgt-s-bad-ordered*)))))
(assert-event
 (and (fn-cstp-carriedp *lgt-s-prepared*)
      (not (equal (fn-sf-phase (fn-sn-files *lgt-s-prepared*)) :completing))
      (fn-cstp-carriedp (fn-sn-finish *lgt-s-prepared*))))

; fn-cstp-replay-append-event.  Every hypothesis and every conjunct of the
; conclusion on the reserved Store's history and the article; removals: the
; article at the wrong sequence (3), at the wrong transaction id (9), and
; after a configuration that retires its group (not served).
(defun lgt-rae-hyps (configs events txid event)
  (let* ((base (fn-cst-replay-node configs events txid))
         (applied (fn-replay-apply-record base event)))
    (list (true-listp configs) (true-listp events)
          (fn-cst-recoverablep configs events txid)
          (fn-store-event-p event)
          (equal (fn-store-event-sequence event) (len events))
          (equal (fn-store-event-txid event) txid)
          (fn-cpr-event-servedp (fn-cstp-fold configs events) event)
          (fn-node-statep applied))))
(defun lgt-rae-concl (configs events txid event)
  (let* ((base (fn-cst-replay-node configs events txid))
         (applied (fn-replay-apply-record base event)))
    (and (equal (fn-replay-result-kind (fn-cpr-replay configs (append events (list event)))) :ok)
         (equal (fn-cstp-fold configs (append events (list event)))
                (fn-cnode-make applied (fn-cnode-config (fn-cstp-fold configs events))))
         (equal (fn-cst-replay-node configs (append events (list event)) (+ 1 txid)) applied)
         (fn-cst-recoverablep configs (append events (list event)) (+ 1 txid)))))
(defconst *lgt-s-r-configs* (fn-sn-config-history *lgt-s-r-reserved*))
(defconst *lgt-s-r-events* (fn-sf-records (fn-sn-files *lgt-s-r-reserved*)))
(assert-event
 (and (equal (lgt-rae-hyps *lgt-s-configs* *lgt-s-events* 8 *acar-t-record*) '(t t t t t t t t))
      (lgt-rae-concl *lgt-s-configs* *lgt-s-events* 8 *acar-t-record*)))
(assert-event
 (and (equal (lgt-rae-hyps *lgt-s-configs* *lgt-s-events* 8 (own-record 3 8 "<ocmt@example>"))
             '(t t t t nil t t t))
      (not (lgt-rae-concl *lgt-s-configs* *lgt-s-events* 8 (own-record 3 8 "<ocmt@example>")))))
(assert-event
 (and (equal (lgt-rae-hyps *lgt-s-configs* *lgt-s-events* 8 (own-record 2 9 "<ocmt@example>"))
             '(t t t t t nil t t))
      (not (lgt-rae-concl *lgt-s-configs* *lgt-s-events* 8 (own-record 2 9 "<ocmt@example>")))))
(assert-event
 (and (equal (lgt-rae-hyps *lgt-s-r-configs* *lgt-s-r-events* 8 *acar-t-record*) '(t t t t t t nil t))
      (not (lgt-rae-concl *lgt-s-r-configs* *lgt-s-r-events* 8 *acar-t-record*))))

; fn-cstp-record-io-preserves-relation, removal of the :record-directory
; exclusion (CORRUPTED: the topic counter at 99 at :record-attempted): the
; relation holds, the operation is a record step, the excluded publishing
; observation is taken, and the relation fails after it.
(assert-event
 (and (fn-cst-relation *lgt-s-bad-attempted*)
      (equal (fn-sf-phase (fn-sn-files *lgt-s-bad-attempted*)) :record-attempted)
      (not (fn-cst-relation (fn-sn-io *lgt-s-bad-attempted* :record-directory :ok)))))

; fn-cstp-refuse-reservation-preserves.  Removal of carriedp (CORRUPTED: the
; topic counter at 99 at :reserved): the relation holds, and the refused
; reservation is not carried.  Removal of the relation (CORRUPTED: the node
; advanced past the frontier): carried, not related, and not related after.
(defconst *lgt-s-bad-reserved* (lgt-store *lgt-bad-reserved*))
(defconst *lgt-s-far-reserved*
  (update-nth 3 (fn-replay-advance-txid (fn-sn-node *lgt-s-reserved*) 20) *lgt-s-reserved*))
(assert-event
 (and (fn-cst-relation *lgt-s-bad-reserved*)
      (not (fn-cstp-carriedp *lgt-s-bad-reserved*))
      (not (fn-cstp-carriedp (fn-sn-refuse-reservation *lgt-s-bad-reserved* 8)))))
(assert-event
 (and (fn-cstp-carriedp *lgt-s-far-reserved*)
      (not (fn-cst-relation *lgt-s-far-reserved*))
      (not (fn-cst-relation (fn-sn-refuse-reservation *lgt-s-far-reserved* 8)))))

; fn-cstp-open-establishes-carriedp, removal of the :ok kind: the same
; history opened at frontier 0 answers :error, and its state is not carried.
(assert-event
 (and (not (equal (fn-sn-open-kind (fn-cpo-open-observed *lgt-rc-configs* 0 *lgt-rc-events*)) :ok))
      (not (fn-cstp-carriedp
            (fn-sn-open-state (fn-cpo-open-observed *lgt-rc-configs* 0 *lgt-rc-events*))))))
