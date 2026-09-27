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
(assert-event (fn-ceis-indexedp (fn-sbud-oc-store *lgt-reserved*)))
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
  (fn-rcon-ocfg-io (fn-rcon-ocfg-io (fn-rcon-ocfg-io (fn-rcon-ocfg-io (fn-rcon-ocfg-io
    *lgt-rc* :recovery-barrier :ok) :recovery-barrier :ok) :recovery-barrier :ok)
    :recovery-barrier :ok) :recovery-barrier :ok))
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
