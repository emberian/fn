; Reachable teeth for the identity, consumer and topic prepares of
; books/owner-prepare-served-ocl.lisp (lane host-decisions, item 3; PRF-290).
; prepare-served's own test book witnessed these three keystones only on
; corrupted states: no configured-owner fixture carried the events.  Here
; owner-log-ocl-tests' configured owner (*lgt-oc0*, recovered, a reader open)
; is driven by the log route's host steps (fn-olr-ocfg-reserve, the host's
; prepare, fn-olr-ocfg-order, the finish) over the events ACL2 itself
; proposes to the host:
;   topic     fn-th-local-propose :install (host/owner-host.lisp
;             fn-owner-topic-propose), over the Store's carried projection;
;   consumer  fn-col-bootstrap (fn-owner-consumer-local-bootstrap);
;   identity  fn-hsig-keyring-event (the keyring snapshot the key-statement
;             plan commits) and fn-pa-authorized-event (the signed
;             composite), whose held row is the Store's composite row.
; The signatures are topic-history-authorship-tests' fixtures (observations
; :verified); every other value is computed by ACL2 from the reached owner.
(in-package "ACL2")
(include-book "owner-prepare-served-tests")
(include-book "../../books/topic-history-local-proposals")
(include-book "../../books/consumer-owner-local")
(include-book "../../books/hybrid-store")
(include-book "../../books/peer-authored-accept")
(include-book "topic-history-authorship-tests")

(defun pse-coords (oc)
  ; The Store coordinates ACL2 hands a proposal: (sequence txid).
  (let ((s (lgt-store oc)))
    (list (fn-sn-identity-next s)
          (fn-state-next-txid (fn-node-acceptance (fn-sn-node s))))))
(defun pse-finish (oc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc)
                                                  (fn-ocfg-config oc) fn-arena))))
(bpr-lift pse-finish 1)
(defun pse-candidate (oc) (fn-sf-record-candidate (fn-sn-files (lgt-store oc))))

; -----------------------------------------------------------------------------
; The proposals, from the configured owner at :ready (the host asks before it
; reserves; the reservation moves neither coordinate).
(assert-event (equal (pse-coords *lgt-oc0*) (pse-coords *lgt-reserved*)))
(defconst *pse-topic-proposal*
  (fn-th-local-propose :install (fn-sn-topic (lgt-store *lgt-oc0*))
                       (second (pse-coords *lgt-oc0*)) 0 1000
                       (make-list 32 :initial-element 5) 0))
(defconst *pse-consumer-proposal*
  (fn-col-bootstrap (fn-ocfg-owner *lgt-oc0*) (make-list 32 :initial-element 1)
                    (make-list 32 :initial-element 2)))
(assert-event (equal (car *pse-topic-proposal*) :ok))
(assert-event (equal (car *pse-consumer-proposal*) :write))
(defconst *pse-topic-event* (cadr *pse-topic-proposal*))
(defconst *pse-consumer-event* (cadr *pse-consumer-proposal*))
(make-event `(defconst *pse-keyring*
               ',(let ((c (pse-coords *lgt-oc0*)))
                   (fn-hsig-keyring-event (first c) (second c) (second c) 1
                                          *tha-principal* *tha-keys*))))
(assert-event (fn-th-topic-eventp *pse-topic-event*))
(assert-event (fn-cpe-eventp *pse-consumer-event*))
(assert-event (fn-stxk-p *pse-keyring*))

; -----------------------------------------------------------------------------
; fn-psrv-prepare-topic-preserves-invariant and
; fn-psrv-prepare-topic-is-ocfg-step-when-admitted.  Reachable positive
; witness: at :reserved the invariant holds, the event is a Store event and
; the carried consumer projection admits it at the Store's next sequence;
; the host's topic prepare stages exactly it, equals the configured owner's
; (:store (:prepare-topic E)), and carries the invariant; the log order and
; the finish complete it, carrying the invariant (the completion the
; consumer test exists for).
(make-event `(defconst *pse-topic-staged*
               ',(fn-psrv-prepare-topic *lgt-reserved* *pse-topic-event*)))
(assert-event (fn-lgoc-invariantp *lgt-reserved*))
(assert-event (fn-store-event-p *pse-topic-event*))
(assert-event (let ((s (lgt-store *lgt-reserved*)))
                (eq (car (fn-cpe-projection-step (fn-sn-consumer s) *pse-topic-event*
                                                 (fn-sn-identity-next s)))
                    :ok)))
(assert-event (equal *pse-topic-staged*
                     (in-arena-acar-t-ocfg-run
                      *sr-arena* *lgt-reserved*
                      (list (list :store (list :prepare-topic *pse-topic-event*))))))
(assert-event (equal (lgt-phase *pse-topic-staged*) :record-staged))
(assert-event (equal (pse-candidate *pse-topic-staged*) *pse-topic-event*))
(assert-event (fn-lgoc-invariantp *pse-topic-staged*))
(make-event `(defconst *pse-topic-ordered* ',(fn-olr-ocfg-order *pse-topic-staged*)))
(make-event `(defconst *pse-topic-finished*
               ',(in-arena-pse-finish *sr-arena* *pse-topic-ordered*)))
(assert-event (equal (lgt-phase *pse-topic-ordered*) :completing))
(assert-event (fn-lgoc-invariantp *pse-topic-ordered*))
(assert-event (equal (lgt-phase *pse-topic-finished*) :ready))
(assert-event (fn-lgoc-invariantp *pse-topic-finished*))
; The projection-refused branch: no reachable witness.  ACL2's topic
; proposals take their sequence from the carried topic projection
; (fn-th-at 1), and fn-cpe-projection-step refuses a non-consumer event only
; when that sequence is not the Store's next, the next is the u32 ceiling,
; or the consumer frontier is not the next; on every owner reached here the
; three counters agree (below), and the invariant's replay companions carry
; them together.  Argued, not proved.  Corrupted-state witness of the
; hypothesis: the topic counter moved to 99 (*lgt-bad-reserved*); the
; invariant fails before, the prepare leaves the owner unchanged, and it
; fails after.
(assert-event (let ((s (lgt-store *lgt-reserved*)))
                (and (equal (fn-th-at 1 (fn-sn-topic s)) (fn-sn-identity-next s))
                     (equal (fn-store-event-sequence *pse-topic-event*)
                            (fn-sn-identity-next s)))))
(assert-event (not (fn-lgoc-invariantp *lgt-bad-reserved*)))
(assert-event (equal (fn-psrv-prepare-topic *lgt-bad-reserved* *pse-topic-event*)
                     *lgt-bad-reserved*))
(assert-event (not (fn-lgoc-invariantp
                    (fn-psrv-prepare-topic *lgt-bad-reserved* *pse-topic-event*))))

; -----------------------------------------------------------------------------
; fn-psrv-prepare-consumer-preserves-invariant.  Reachable positive witness:
; the bootstrap ACL2 proposes for the unbootstrapped Store is staged by
; (:store (:prepare-consumer E)) (host/owner-host.lisp
; fn-owner-prepare-consumer) and carries the invariant; order and finish
; complete it and the Store's consumer projection is bootstrapped.
(assert-event (null (fn-sn-consumer (lgt-store *lgt-reserved*))))
(make-event `(defconst *pse-consumer-staged*
               ',(in-arena-acar-t-ocfg-run
                  *sr-arena* *lgt-reserved*
                  (list (list :store (list :prepare-consumer *pse-consumer-event*))))))
(assert-event (equal (lgt-phase *pse-consumer-staged*) :record-staged))
(assert-event (equal (pse-candidate *pse-consumer-staged*) *pse-consumer-event*))
(assert-event (fn-lgoc-invariantp *pse-consumer-staged*))
(make-event `(defconst *pse-consumer-ordered* ',(fn-olr-ocfg-order *pse-consumer-staged*)))
(make-event `(defconst *pse-consumer-finished*
               ',(in-arena-pse-finish *sr-arena* *pse-consumer-ordered*)))
(assert-event (equal (lgt-phase *pse-consumer-ordered*) :completing))
(assert-event (fn-lgoc-invariantp *pse-consumer-ordered*))
(assert-event (equal (lgt-phase *pse-consumer-finished*) :ready))
(assert-event (fn-lgoc-invariantp *pse-consumer-finished*))
(assert-event (consp (fn-sn-consumer (lgt-store *pse-consumer-finished*))))
; Hypothesis (corrupted-state witness): on the corrupted owner the consumer
; prepare does not restore the invariant.
(assert-event (not (fn-lgoc-invariantp
                    (in-arena-acar-t-ocfg-run
                     *sr-arena* *lgt-bad-reserved*
                     (list (list :store (list :prepare-consumer *pse-consumer-event*)))))))

; -----------------------------------------------------------------------------
; fn-psrv-prepare-identity-preserves-invariant.  Reachable positive witness,
; keyring snapshot: the host's identity prepare stages the enrolment and
; carries the invariant; order and finish complete it (keyring generation 1).
(make-event `(defconst *pse-identity-staged*
               ',(fn-psrv-prepare-identity *lgt-reserved* *pse-keyring*)))
(assert-event (equal (lgt-phase *pse-identity-staged*) :record-staged))
(assert-event (equal (pse-candidate *pse-identity-staged*) *pse-keyring*))
(assert-event (fn-lgoc-invariantp *pse-identity-staged*))
(make-event `(defconst *pse-k-ordered* ',(fn-olr-ocfg-order *pse-identity-staged*)))
(make-event `(defconst *pse-k-finished* ',(in-arena-pse-finish *sr-arena* *pse-k-ordered*)))
(assert-event (fn-lgoc-invariantp *pse-k-ordered*))
(assert-event (equal (lgt-phase *pse-k-finished*) :ready))
(assert-event (fn-lgoc-invariantp *pse-k-finished*))
(assert-event (equal (fn-sn-keyring-snapshots (lgt-store *pse-k-finished*))
                     (list *pse-keyring*)))
; Hypothesis (corrupted-state witness): the corrupted owner stages the
; snapshot and the invariant still fails.
(assert-event (equal (lgt-phase (fn-psrv-prepare-identity *lgt-bad-reserved* *pse-keyring*))
                     :record-staged))
(assert-event (not (fn-lgoc-invariantp
                    (fn-psrv-prepare-identity *lgt-bad-reserved* *pse-keyring*))))

; The signed composite over the enrolled Store: the article
; topic-history-authorship-tests signed (Message-ID and group its authored
; source files: "<topic-binding@example.invalid>", fn.test), built by
; fn-pa-authorized-event at the owner's next coordinates, held as the
; Store's composite row.
(defconst *pse-obs* (fn-clock-observation 2000000 1600000010000 500 t))
(defconst *pse-msgid* "<topic-binding@example.invalid>")
(defun pse-composite (oc)
  (let ((c (pse-coords oc)))
    (fn-pa-authorized-event
     (first c) (second c) (second c) *pse-msgid* *tha-received* '("fn.test")
     (fn-record-octets-string
      (fn-id-text (fn-id-obligation-of (fn-record-string-octets *pse-msgid*)
                                       (fn-id-subject-of-payload *tha-received*))))
     *tha-received-subject* "served-post-evidence"
     (fn-charge-for-payload (len *tha-received*))
     (fn-sn-keyring-snapshots (lgt-store oc)) *tha-ml-key* :verified :verified *pse-obs*)))
(defun pse-row (w) (fn-hstxa-make w (fn-held-plain (fn-replay-composite-record w) 0)))

; Reachable positive witness, signed composite (fn.test served): staged,
; invariant carried.
(defconst *pse-k2-reserved* (fn-olr-ocfg-reserve *pse-k-finished*))
(make-event `(defconst *pse-comp* ',(pse-composite *pse-k2-reserved*)))
(make-event `(defconst *pse-crow* ',(pse-row *pse-comp*)))
(assert-event (fn-stxa-p *pse-comp*))
(assert-event (fn-hstxa-p *pse-crow*))
(assert-event (fn-lgoc-invariantp *pse-k2-reserved*))
(assert-event (fn-psrv-event-servedp (fn-ocfg-config *pse-k2-reserved*) *pse-crow*))
(assert-event (equal (lgt-phase (fn-psrv-prepare-identity *pse-k2-reserved* *pse-crow*))
                     :record-staged))
(assert-event (fn-lgoc-invariantp (fn-psrv-prepare-identity *pse-k2-reserved* *pse-crow*)))
; The plain composite (fn-stxa-p, the wire value fn-pa-authorized-event and
; fn-pcb-carried-event return) is not staged: fn-ccar-sn-prepare-identity
; admits a composite only as the row (fn-hstxa-p).  The host's entry interns
; the row first (books/owner-identity-served.lisp fn-oiis-prepare-identity,
; signed-post); its teeth are tests/acl2/owner-identity-served-tests.lisp.
(assert-event (not (fn-hstxa-p *pse-comp*)))
(assert-event (equal (fn-psrv-prepare-identity *pse-k2-reserved* *pse-comp*)
                     *pse-k2-reserved*))

; THE UNSERVED-COMPOSITE WITNESS, refused by name (reachable): a live
; completion retires fn.test (as *lgt-retire* retires fn.letters), the
; author enrols, and the composite whose article files in fn.test reaches
; the identity prepare.  The host's prepare leaves the owner unchanged with
; the invariant; the prepare without the served test
; (fn-ccar-ocfg-prepare-identity) stages it and breaks the invariant (the
; counterexample prepare-served fixed).
(defconst *pse-retire-test*
  (fn-cfg-record-make 4 8 5 (list (fn-cfg-remove-group "fn.test")) *fn-cfg-default-stamp*))
(defconst *pse-t-retired*
  (cadr (mv-list 2 (fn-oclc-publish (fn-ocfg-make (fn-ocfg-owner *lgt-oc0*)
                                                  (fn-ocfg-config *lgt-oc0*)
                                                  (fn-ocfg-pins *lgt-oc0*) *pse-retire-test*)
                                    5 1000000))))
(assert-event (fn-lgoc-invariantp *pse-t-retired*))
(defconst *pse-t-reserved* (fn-olr-ocfg-reserve *pse-t-retired*))
(make-event `(defconst *pse-t-keyring*
               ',(let ((c (pse-coords *pse-t-reserved*)))
                   (fn-hsig-keyring-event (first c) (second c) (second c) 1
                                          *tha-principal* *tha-keys*))))
(make-event `(defconst *pse-t-k-staged* ',(fn-psrv-prepare-identity *pse-t-reserved* *pse-t-keyring*)))
(make-event `(defconst *pse-t-k-ordered* ',(fn-olr-ocfg-order *pse-t-k-staged*)))
(make-event `(defconst *pse-t-k-finished* ',(in-arena-pse-finish *sr-arena* *pse-t-k-ordered*)))
(assert-event (equal (lgt-phase *pse-t-k-finished*) :ready))
(defconst *pse-t2-reserved* (fn-olr-ocfg-reserve *pse-t-k-finished*))
(make-event `(defconst *pse-t-comp* ',(pse-composite *pse-t2-reserved*)))
(make-event `(defconst *pse-t-crow* ',(pse-row *pse-t-comp*)))
(assert-event (fn-hstxa-p *pse-t-crow*))
(assert-event (fn-lgoc-invariantp *pse-t2-reserved*))
(assert-event (not (fn-psrv-event-servedp (fn-ocfg-config *pse-t2-reserved*) *pse-t-crow*)))
(assert-event (equal (fn-psrv-prepare-identity *pse-t2-reserved* *pse-t-crow*) *pse-t2-reserved*))
(assert-event (fn-lgoc-invariantp (fn-psrv-prepare-identity *pse-t2-reserved* *pse-t-crow*)))
(assert-event (equal (lgt-phase (fn-ccar-ocfg-prepare-identity *pse-t2-reserved* *pse-t-crow*))
                     :record-staged))
(assert-event (not (fn-lgoc-invariantp
                    (fn-ccar-ocfg-prepare-identity *pse-t2-reserved* *pse-t-crow*))))
