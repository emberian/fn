; Witness and teeth for the receiver relation over an evolving Store
; (books/bp-receiver-evolving-*-invariants.lisp; specs/bp-evolving-store.md).
;
; One real Store built by fn-sn-initial, fn-sn-io, fn-sn-prepare and
; fn-sn-finish (tests/acl2/bp-receipt-tests.lisp) carries the live trace the
; host runs in tools/run_bp_receive.py: a request is accepted, an unrelated
; article is ingested with receiver steps interleaved mid-ingress, the
; process crashes, reopens through fn-sn-open-observed, runs its recovery
; barriers, and fn-bprj-install regenerates the same receipt bytes.

(in-package "ACL2")
(include-book "../../books/bp-receiver-evolving-store-invariants")
(include-book "bp-receipt-records-tests")
(include-book "must-fail-checked")
(include-book "../../books/codec-attach")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-record-invariants-vocabulary fn-cbor-record-vocabulary
                          fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; A second, unrelated article: Message-ID <receipt-2@example>.

(defconst *bpre-adu2* (update-nth 21 50 *bpr-adu*))
(assert-event (equal (nth 21 *bpr-adu*) 49))
(assert-event (not (equal *bpre-adu2* *bpr-adu*)))
(defconst *bpre-context2*
  (fn-bpi-make-context "dtn://fn.lab/inbox" "dtn://other.lab" "local-bid-2" 300 (fn-clock-observation 1 841000000000 0 t)))
; A distinct archive obligation and subject: retention admits one obligation
; per identity, so the second article carries its own.
(defconst *bpre-policy2*
  (fn-bpi-make-policy "dtn://fn.lab/inbox" "dtn://fn.lab/inbox" *bpr-map*
                      "archive:receiver-2" "subject:receiver-2"
                      "unsigned-ingress-v0" 1 "receiver-policy" "terms-1"
                      "dtn://fn.lab/issuer"))
(make-event `(defconst *bpre-prepared2* ',(fn-bpi-ingress-prepare (bpr-reserve *bpr-store*) *bpre-policy2* *bpre-context2* *bpre-adu2* 1)))
(assert-event (equal (fn-bpi-result-kind *bpre-prepared2*) :prepared))
;; The second ADU takes handle 1 (the first took 0): the Store retains the
;; held ROW, the receiver is handed its WIRE record (records-flip).  The
;; arena of this trace holds both ADUs (*bpre-payloads*); *bpre-arena* is
;; its logical value.
(defconst *bpre-row2* (fn-bpi-result-record *bpre-prepared2*))
(defconst *bpre-record2* (fn-bpi-result-wire *bpre-prepared2*))
(assert-event (fn-held-p *bpre-row2*))
(assert-event (fn-record-p *bpre-record2*))
(defconst *bpre-payloads* (list *bpr-adu* *bpre-adu2*))
(defconst *bpre-arena* *bpre-payloads*)
(bpr-lift fn-bpi-node-wire-committedp 2)
(bpr-lift fn-bpr-live-install 2)
(bpr-lift fn-bpr-live-run 2)
(bpr-lift fn-bpr-rows-stand-for 2)
(bpr-lift fn-bprr-replay 2)
(bpr-lift fn-bprv-context-groundedp 3)
(bpr-lift fn-bprv-evolving-invariantp 3)
(bpr-lift fn-bprv-find-grounding-record 3)
(bpr-lift fn-bprv-invariantp 3)
(bpr-lift fn-bprv-system-invariantp 3)
(bpr-lift fn-bprv-system-step 3)

(assert-event (not (equal (fn-record-msgid *bpre-record2*) (fn-record-msgid *bpr-record*))))

; -----------------------------------------------------------------------------
; The live trace.  The receiver opens fresh (config record only) against the
; ready Store holding the first article.

(defconst *bpre-live0*
  (list *bpr-store* (fn-bpr-initial-state *bpr-config*) (list *bprr-config-record*)))
(assert-event (fn-snt-relation *bpr-store*))
(assert-event (equal (fn-bprv-phase *bpr-store*) :ready))
(assert-event (equal (in-arena-fn-bprr-replay *bpre-payloads* *bpr-store* (list *bprr-config-record*))
                     (list t (fn-bpr-initial-state *bpr-config*))))

(defconst *bpre-events*
  (list (list :apply *bprr-request-record*)
        '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare *bpre-row2*))
        ; receiver step while the Store is :record-staged
        (list :apply *bprr-intent-record*)
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))
        ; receiver step while the Store is :completing, the second record
        ; already in the history and not yet node-committed
        (list :apply *bprr-decision-record*)
        '(:store (:finish))))

(defun bpre-run-prefixes (live events fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp events)
      (cons live (bpre-run-prefixes (fn-bpr-live-step live (car events) fn-arena) (cdr events) fn-arena))
    (list live)))
(defun bpre-all-system-invariant (lives fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp lives)
      (and (fn-bprv-system-invariantp (car (car lives)) (cadr (car lives)) (caddr (car lives)) fn-arena)
           (bpre-all-system-invariant (cdr lives) fn-arena))
    t))
(defun bpre-retired-invariant-failures (lives fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp lives)
      (+ (if (fn-bprv-invariantp (car (car lives)) (cadr (car lives)) (caddr (car lives)) fn-arena) 0 1)
         (bpre-retired-invariant-failures (cdr lives) fn-arena))
    0))
(bpr-lift bpre-all-system-invariant 1)
(bpr-lift bpre-retired-invariant-failures 1)
(bpr-lift bpre-run-prefixes 2)
(defun bpre-phases (lives)
  (if (consp lives)
      (cons (fn-bprv-phase (car (car lives))) (bpre-phases (cdr lives)))
    nil))

(make-event `(defconst *bpre-lives* ',(in-arena-bpre-run-prefixes *bpre-payloads* *bpre-live0* *bpre-events*)))
(make-event `(defconst *bpre-final* ',(in-arena-fn-bpr-live-run *bpre-payloads* *bpre-live0* *bpre-events*)))
(assert-event (equal (car (last *bpre-lives*)) *bpre-final*))

; Every intermediate state satisfies the restated invariant.
(assert-event (in-arena-bpre-all-system-invariant *bpre-payloads* *bpre-lives*))
(defun bpre-count-ready (phases)
  (if (consp phases)
      (+ (if (equal (car phases) :ready) 1 0) (bpre-count-ready (cdr phases)))
    0))
(assert-event (equal (len *bpre-lives*) 13))
(assert-event (equal (bpre-count-ready (bpre-phases *bpre-lives*)) 3))
(assert-event (equal (nth 5 (bpre-phases *bpre-lives*)) :reserved))
(assert-event (equal (nth 6 (bpre-phases *bpre-lives*)) :record-staged))
(assert-event (equal (nth 10 (bpre-phases *bpre-lives*)) :completing))
(assert-event (equal (nth 12 (bpre-phases *bpre-lives*)) :ready))
; The retired fixed-Store invariant fails at every one of the ten non-ready
; states: the restatement is necessary, not a rephrasing.
(assert-event (equal (in-arena-bpre-retired-invariant-failures *bpre-payloads* *bpre-lives*) 10))
(assert-event (in-arena-fn-bprv-invariantp *bpre-payloads* (car *bpre-final*) (cadr *bpre-final*) (caddr *bpre-final*)))

; The final live state: both records durable, the receipt held, the journal
; exactly the four records fn-bprj-apply accepted.
(defconst *bpre-final-store* (car *bpre-final*))
(defconst *bpre-final-state* (cadr *bpre-final*))
(defconst *bpre-journal* (caddr *bpre-final*))
(assert-event (equal *bpre-journal*
                     (list *bprr-config-record* *bprr-request-record*
                           *bprr-intent-record* *bprr-decision-record*)))
(assert-event (equal (fn-bprv-phase *bpre-final-store*) :ready))
(assert-event (equal (fn-bprv-history *bpre-final-store*) (list *bpr-row* *bpre-row2*)))
(assert-event (fn-bpi-node-record-committedp (fn-sn-node *bpre-final-store*) *bpr-row*))
(assert-event (fn-bpi-node-record-committedp (fn-sn-node *bpre-final-store*) *bpre-row2*))
(assert-event (equal (fn-bpr-receipt-adu *bpre-final-state* *bpr-request*) *bpr-receipt-adu*))
(assert-event (equal (in-arena-fn-bprr-replay *bpre-payloads* *bpre-final-store* *bpre-journal*) (list t *bpre-final-state*)))

; The mid-ingress states, named for the teeth below.
(defconst *bpre-staged* (nth 6 *bpre-lives*))
(defconst *bpre-completing* (nth 10 *bpre-lives*))
(assert-event (equal (fn-bprv-phase (car *bpre-staged*)) :record-staged))
(assert-event (equal (fn-bprv-phase (car *bpre-completing*)) :completing))
(assert-event (in-arena-fn-bprv-evolving-invariantp *bpre-payloads* (car *bpre-staged*) (cadr *bpre-staged*) (caddr *bpre-staged*)))
(assert-event (not (in-arena-fn-bprv-invariantp *bpre-payloads* (car *bpre-staged*) (cadr *bpre-staged*) (caddr *bpre-staged*))))
(assert-event (member-equal *bpre-row2* (fn-bprv-history (car *bpre-completing*))))
(assert-event (fn-snt-relation (car *bpre-completing*)))
(assert-event (not (fn-bpi-node-record-committedp (fn-sn-node (car *bpre-completing*)) *bpre-row2*)))

; -----------------------------------------------------------------------------
; Crash, reopen through the host's entry, recovery barriers, fn-bprj-install.

(defconst *bpre-frontier* (fn-sf-frontier (fn-sn-files *bpre-final-store*)))
(defconst *bpre-records* (fn-sf-records (fn-sn-files *bpre-final-store*)))
(assert-event (fn-sf-crash-imagep (fn-sn-files *bpre-final-store*) *bpre-frontier* *bpre-records*))
; The reopen theorems' identity hypothesis (commit 4857c648) holds of this
; image, so the restart below is a live instance of all three.
(assert-event (fn-sn-observed-identity-okp *bpre-records*))
(make-event `(defconst *bpre-opened* ',(fn-sn-open-observed (fn-sn-groups *bpre-final-store*) (fn-sn-capacity *bpre-final-store*)
                       *bpre-frontier* *bpre-records*)))
(assert-event (fn-sn-open-okp *bpre-opened*))
(assert-event (equal (fn-bprv-phase (fn-sn-open-state *bpre-opened*)) :recovering))
(defconst *bpre-barriers*
  '((:io :recovery-barrier :ok) (:io :recovery-barrier :ok) (:io :recovery-barrier :ok)))
(make-event `(defconst *bpre-probe* ',(fn-snrt-run (fn-sn-open-state *bpre-opened*) *bpre-barriers*)))
(assert-event (equal (fn-bprv-phase *bpre-probe*) :ready))
(assert-event (fn-snt-relation *bpre-probe*))
(make-event `(defconst *bpre-installed* ',(in-arena-fn-bpr-live-install *bpre-payloads* *bpre-probe* *bpre-journal*)))
(assert-event (equal (cadr *bpre-installed*) *bpre-final-state*))
(assert-event (equal (fn-bpr-receipt-adu (cadr *bpre-installed*) *bpr-request*) *bpr-receipt-adu*))
(assert-event (in-arena-fn-bprv-system-invariantp *bpre-payloads* *bpre-probe* *bpre-final-state* *bpre-journal*))
(assert-event (in-arena-fn-bprv-system-invariantp *bpre-payloads* (fn-sn-open-state *bpre-opened*) *bpre-final-state* *bpre-journal*))

; The same restart inside the kernel's own crash constructor: the receiver
; state is retained through :replaying (empty node) and recovery.
(defconst *bpre-crash-events*
  (append *bpre-events*
          (list '(:store (:crash :old :present)) '(:store (:recover))
                '(:store (:io :recovery-barrier :ok)) '(:store (:io :recovery-barrier :ok))
                '(:store (:io :recovery-barrier :ok)))))
(make-event `(defconst *bpre-crash-lives* ',(in-arena-bpre-run-prefixes *bpre-payloads* *bpre-live0* *bpre-crash-events*)))
(assert-event (in-arena-bpre-all-system-invariant *bpre-payloads* *bpre-crash-lives*))
(defconst *bpre-replaying* (nth 13 *bpre-crash-lives*))
(assert-event (equal (fn-bprv-phase (car *bpre-replaying*)) :replaying))
(assert-event (equal (fn-sn-node (car *bpre-replaying*))
                     (fn-node-initial-state *bpr-groups* 20)))
(defconst *bpre-recovered* (car (last *bpre-crash-lives*)))
(assert-event (equal (fn-bprv-phase (car *bpre-recovered*)) :ready))
(assert-event (equal (fn-bpr-receipt-adu (cadr *bpre-recovered*) *bpr-request*) *bpr-receipt-adu*))
(assert-event (equal (in-arena-fn-bprr-replay *bpre-payloads* (car *bpre-recovered*) (caddr *bpre-recovered*))
                     (list t (cadr *bpre-recovered*))))

; -----------------------------------------------------------------------------
; Since PKT-646 the receiver's contexts hold a reference whose digest is
; `fn-frame-digest' (A-CRYPTO): the prover cannot evaluate it over these
; ground terms, so each must-fail below that reaches the receiver fails by
; search, not by evaluation.  Its counter-witness is the evaluation witness
; that follows it, `(assert-event (not BODY))', with the digest running
; through its attachment; `:do-not-induct' keeps that search bounded, and
; the four whose search reaches the receiver's contexts (grounded-without-
; history-record, monotone-without-prefix, node-grounded-without-idle-phase,
; reopen-without-admissible-image) run in the minimal theory: for them the
; evaluation witness is the whole evidence.

; Teeth.  One must-fail per hypothesis, each violating only that hypothesis
; and stating the keystone's conclusion.

; fn-bprv-grounded-context-has-history-record: a context whose record is in
; no history is not grounded, and its grounding record is not a record.
(assert-event (in-arena-fn-bprv-context-groundedp *bpre-payloads* *bpr-config* *bprr-context* (list *bpr-row*)))
(assert-event (not (in-arena-fn-bprv-context-groundedp *bpre-payloads* *bpr-config* *bprr-context* (list *bpre-row2*))))
; The row's bytes are read through the arena: over an arena that holds other
; bytes at the first row's handle, the context is not grounded in it.
(assert-event (not (in-arena-fn-bprv-context-groundedp (list *bpre-adu2*) *bpr-config* *bprr-context*
                                                     (list *bpr-row*))))
(local
 (must-fail-checked
  (defthm bpre-teeth-grounded-without-history-record
    (let ((record (fn-bprv-find-grounding-record *bpr-config* *bprr-context* (list *bpre-row2*) *bpre-arena*)))
      (and (fn-record-p record)
           (fn-bpr-rows-stand-for record (list *bpre-row2*) *bpre-arena*)))
    :hints (("Goal" :do-not-induct t
                     :in-theory (theory 'minimal-theory))))))
(assert-event (not (let ((record (in-arena-fn-bprv-find-grounding-record *bpre-payloads* *bpr-config* *bprr-context* (list *bpre-row2*))))
      (and (fn-record-p record)
           (in-arena-fn-bpr-rows-stand-for *bpre-payloads* record (list *bpre-row2*)))))) ; evaluation witness for bpre-teeth-grounded-without-history-record

; fn-bprv-grounded-monotone: a history that drops the record is not a prefix,
; and groundedness does not carry to it.
(assert-event (not (fn-sf-prefixp (list *bpr-row*) (list *bpre-row2*))))
(local
 (must-fail-checked
  (defthm bpre-teeth-monotone-without-prefix
    (implies (fn-bprv-context-groundedp *bpr-config* *bprr-context* (list *bpr-row*) *bpre-arena*)
             (fn-bprv-context-groundedp *bpr-config* *bprr-context* (list *bpre-row2*) *bpre-arena*))
    :hints (("Goal" :do-not-induct t
                     :in-theory (theory 'minimal-theory))))))
(assert-event (not (implies (in-arena-fn-bprv-context-groundedp *bpre-payloads* *bpr-config* *bprr-context* (list *bpr-row*))
             (in-arena-fn-bprv-context-groundedp *bpre-payloads* *bpr-config* *bprr-context* (list *bpre-row2*))))) ; evaluation witness for bpre-teeth-monotone-without-prefix

; fn-bprv-system-step-preserves-invariant: a receiver record outside the
; journal breaks fn-bprv-entries-decidedp.
(defconst *bpre-intent-journal*
  (list *bprr-config-record* *bprr-request-record* *bprr-intent-record*))
(make-event `(defconst *bpre-intent-state* ',(cadr (in-arena-fn-bprr-replay *bpre-payloads* *bpr-store* *bpre-intent-journal*))))
(assert-event (in-arena-fn-bprv-system-invariantp *bpre-payloads* *bpr-store* *bpre-intent-state* *bpre-intent-journal*))
(assert-event (not (member-equal *bprr-decision-record* *bpre-intent-journal*)))
(local
 (must-fail-checked
  (defthm bpre-teeth-system-step-without-journaled-record
    (let ((next (fn-bprv-system-step *bpr-store* *bpre-intent-state*
                                     (list :receiver *bprr-decision-record*) *bpre-arena*)))
      (fn-bprv-system-invariantp (car next) (cadr next) *bpre-intent-journal* *bpre-arena*))
    :hints (("Goal" :do-not-induct t)))))
(assert-event (not (let ((next (in-arena-fn-bprv-system-step *bpre-payloads* *bpr-store* *bpre-intent-state* (list :receiver *bprr-decision-record*))))
      (in-arena-fn-bprv-system-invariantp *bpre-payloads* (car next) (cadr next) *bpre-intent-journal*)))) ; evaluation witness for bpre-teeth-system-step-without-journaled-record

; fn-bprv-history-record-is-node-committed-when-idle, three hypotheses.
; Without the idle phase: the :completing Store holds the second record in
; its history and its node has not completed it.
(local
 (must-fail-checked
  (defthm bpre-teeth-committed-without-idle-phase
    (implies (and (fn-snt-relation (car *bpre-completing*))
                  (fn-held-p *bpre-row2*)
                  (member-equal *bpre-row2* (fn-bprv-history (car *bpre-completing*))))
             (fn-bpi-node-record-committedp (fn-sn-node (car *bpre-completing*)) *bpre-row2*))
    :hints (("Goal" :do-not-induct t)))))
(assert-event (not (implies (and (fn-snt-relation (car *bpre-completing*))
                  (fn-held-p *bpre-row2*)
                  (member-equal *bpre-row2* (fn-bprv-history (car *bpre-completing*))))
             (fn-bpi-node-record-committedp (fn-sn-node (car *bpre-completing*)) *bpre-row2*)))) ; evaluation witness for bpre-teeth-committed-without-idle-phase
; Without the live-history relation: the ready files with an empty node.
(defconst *bpre-forged-store*
  (fn-sn-make *bpr-groups* 20 (fn-sn-files *bpre-final-store*)
              (fn-node-initial-state *bpr-groups* 20)
              nil (fn-stx-index-empty)))
(assert-event (fn-sn-statep *bpre-forged-store*))
(assert-event (equal (fn-bprv-phase *bpre-forged-store*) :ready))
(assert-event (not (fn-snt-relation *bpre-forged-store*)))
(local
 (must-fail-checked
  (defthm bpre-teeth-committed-without-relation
    (implies (and (member-equal (fn-bprv-phase *bpre-forged-store*)
                                '(:ready :recovering :fenced-recovery))
                  (fn-held-p *bpr-row*)
                  (member-equal *bpr-row* (fn-bprv-history *bpre-forged-store*)))
             (fn-bpi-node-record-committedp (fn-sn-node *bpre-forged-store*) *bpr-row*))
    :hints (("Goal" :do-not-induct t)))))
(assert-event (not (implies (and (member-equal (fn-bprv-phase *bpre-forged-store*)
                                '(:ready :recovering :fenced-recovery))
                  (fn-held-p *bpr-row*)
                  (member-equal *bpr-row* (fn-bprv-history *bpre-forged-store*)))
             (fn-bpi-node-record-committedp (fn-sn-node *bpre-forged-store*) *bpr-row*)))) ; evaluation witness for bpre-teeth-committed-without-relation
; Without membership: the second record before its ingress.
(assert-event (not (member-equal *bpre-row2* (fn-bprv-history *bpr-store*))))
; Without the article hypothesis (`fn-held-p' since the records flip; `fn-record-p',
; restated 2026-09-23): a
; retention undertake committed through the public Store transitions on the
; final Store.  The Store is :ready and related, the event is in its history,
; and it installs no article under its own name, so the node does not hold it
; committed.  This is the reachable Store that refutes the statement without
; the hypothesis, not only its proof.
(make-event `(defconst *bpre-retention* ',(fn-store-retention-event-make :undertake 2 2 2
                                 "retained-obligation" "retained-subject"
                                 "retained-evidence" 1)))
(make-event `(defconst *bpre-retained-store*
  ',(fn-sn-finish (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-prepare-retention (bpr-reserve *bpre-final-store*)
                                                                          *bpre-retention*)
                                                :record-file :ok)
                                      :record-link :ok)
                            :record-directory :ok))))
(assert-event (equal (fn-bprv-phase *bpre-retained-store*) :ready))
(assert-event (fn-snt-relation *bpre-retained-store*))
(assert-event (member-equal *bpre-retention* (fn-bprv-history *bpre-retained-store*)))
(assert-event (fn-store-event-p *bpre-retention*))
(assert-event (not (fn-held-p *bpre-retention*)))
(local
 (must-fail-checked
  (defthm bpre-teeth-committed-without-article-record
    (implies (and (fn-snt-relation *bpre-retained-store*)
                  (member-equal (fn-bprv-phase *bpre-retained-store*)
                                '(:ready :recovering :fenced-recovery))
                  (member-equal *bpre-retention* (fn-bprv-history *bpre-retained-store*)))
             (fn-bpi-node-record-committedp (fn-sn-node *bpre-retained-store*)
                                            *bpre-retention*))
    :hints (("Goal" :do-not-induct t)))))
(assert-event (not (implies (and (fn-snt-relation *bpre-retained-store*)
                  (member-equal (fn-bprv-phase *bpre-retained-store*)
                                '(:ready :recovering :fenced-recovery))
                  (member-equal *bpre-retention* (fn-bprv-history *bpre-retained-store*)))
             (fn-bpi-node-record-committedp (fn-sn-node *bpre-retained-store*)
                                            *bpre-retention*)))) ; evaluation witness for bpre-teeth-committed-without-article-record
; The article records of the same Store stay committed across the retention
; event: the non-degenerate instance of the restated theorem.
(assert-event (fn-bpi-node-record-committedp (fn-sn-node *bpre-retained-store*) *bpre-row2*))
(assert-event (fn-bpi-node-record-committedp (fn-sn-node *bpre-retained-store*) *bpr-row*))

(local
 (must-fail-checked
  (defthm bpre-teeth-committed-without-membership
    (implies (and (fn-snt-relation *bpr-store*)
                  (member-equal (fn-bprv-phase *bpr-store*) '(:ready :recovering :fenced-recovery))
                  (fn-held-p *bpre-row2*))
             (fn-bpi-node-record-committedp (fn-sn-node *bpr-store*) *bpre-row2*))
    :hints (("Goal" :do-not-induct t)))))
(assert-event (not (implies (and (fn-snt-relation *bpr-store*)
                  (member-equal (fn-bprv-phase *bpr-store*) '(:ready :recovering :fenced-recovery))
                  (fn-held-p *bpre-row2*))
             (fn-bpi-node-record-committedp (fn-sn-node *bpr-store*) *bpre-row2*)))) ; evaluation witness for bpre-teeth-committed-without-membership

; fn-bprv-evolving-output-is-node-grounded-when-idle: the phase tolerance the
; design is for.  In :replaying with the post-crash empty node the history
; conclusion (L18) holds while the node conclusion (L20) is false.
(defconst *bpre-replaying-context*
  (fn-bpr-find-context (fn-bpa-request-work-id *bpr-request*)
                       (fn-bpr-state-contexts (cadr *bpre-replaying*))))
; The grounding search resolves the context's reference (fn-frame-digest,
; which runs through its attachment: a make-event, PKT-646).
(make-event
 `(defconst *bpre-replaying-record*
    ',(in-arena-fn-bprv-find-grounding-record *bpre-payloads* *bpr-config* *bpre-replaying-context* (fn-bprv-history (car *bpre-replaying*)))))
(assert-event (in-arena-fn-bprv-evolving-invariantp *bpre-payloads* (car *bpre-replaying*) (cadr *bpre-replaying*) (caddr *bpre-replaying*)))
(assert-event (fn-snt-relation (car *bpre-replaying*)))
(assert-event (fn-bpr-receipt-adu (cadr *bpre-replaying*) *bpr-request*))
(assert-event (and (fn-record-p *bpre-replaying-record*)
                   (in-arena-fn-bpr-rows-stand-for *bpre-payloads* *bpre-replaying-record* (fn-bprv-history (car *bpre-replaying*)))
                   (equal *bpre-replaying-context*
                          (fn-bpr-context-from-request *bpre-replaying-record* *bpr-request*))))
(local
 (must-fail-checked
  (defthm bpre-teeth-node-grounded-without-idle-phase
    (implies (and (fn-bprv-evolving-invariantp (car *bpre-replaying*) (cadr *bpre-replaying*)
                                               (caddr *bpre-replaying*) *bpre-arena*)
                  (fn-snt-relation (car *bpre-replaying*))
                  (fn-bpr-receipt-adu (cadr *bpre-replaying*) *bpr-request*))
             (fn-bpi-node-wire-committedp (fn-sn-node (car *bpre-replaying*)) *bpre-replaying-record* *bpre-arena*))
    :hints (("Goal" :do-not-induct t
                     :in-theory (theory 'minimal-theory))))))
(assert-event (not (implies (and (in-arena-fn-bprv-evolving-invariantp *bpre-payloads* (car *bpre-replaying*) (cadr *bpre-replaying*) (caddr *bpre-replaying*))
                  (fn-snt-relation (car *bpre-replaying*))
                  (fn-bpr-receipt-adu (cadr *bpre-replaying*) *bpr-request*))
             (in-arena-fn-bpi-node-wire-committedp *bpre-payloads* (fn-sn-node (car *bpre-replaying*)) *bpre-replaying-record*)))) ; evaluation witness for bpre-teeth-node-grounded-without-idle-phase

; fn-bpr-live-state-is-replay-of-journal, four hypotheses.
; Without a ready probe: the reopened Store before its barriers refuses the
; request context and replay stops.
(defconst *bpre-recovering-probe* (fn-sn-open-state *bpre-opened*))
(assert-event (fn-snt-relation *bpre-recovering-probe*))
(assert-event (fn-bprv-extendsp *bpre-final-store* *bpre-recovering-probe*))
(assert-event (not (equal (fn-bprv-phase *bpre-recovering-probe*) :ready)))
(local
 (must-fail-checked
  (defthm bpre-teeth-live-replay-without-ready-probe
    (implies (and (fn-snt-relation *bpr-store*)
                  (equal (fn-bprr-replay *bpre-recovering-probe* (list *bprr-config-record*) *bpre-arena*)
                         (list t (fn-bpr-initial-state *bpr-config*)))
                  (fn-snt-relation *bpre-recovering-probe*)
                  (fn-bprv-extendsp (car (fn-bpr-live-run *bpre-live0* *bpre-events* *bpre-arena*))
                                    *bpre-recovering-probe*))
             (equal (fn-bprr-replay *bpre-recovering-probe*
                                    (caddr (fn-bpr-live-run *bpre-live0* *bpre-events* *bpre-arena*)) *bpre-arena*)
                    (list t (cadr (fn-bpr-live-run *bpre-live0* *bpre-events* *bpre-arena*)))))
    :hints (("Goal" :do-not-induct t)))))
(assert-event (not (implies (and (fn-snt-relation *bpr-store*)
                  (equal (in-arena-fn-bprr-replay *bpre-payloads* *bpre-recovering-probe* (list *bprr-config-record*))
                         (list t (fn-bpr-initial-state *bpr-config*)))
                  (fn-snt-relation *bpre-recovering-probe*)
                  (fn-bprv-extendsp (car (in-arena-fn-bpr-live-run *bpre-payloads* *bpre-live0* *bpre-events*))
                                    *bpre-recovering-probe*))
             (equal (in-arena-fn-bprr-replay *bpre-payloads* *bpre-recovering-probe* (caddr (in-arena-fn-bpr-live-run *bpre-payloads* *bpre-live0* *bpre-events*)))
                    (list t (cadr (in-arena-fn-bpr-live-run *bpre-payloads* *bpre-live0* *bpre-events*))))))) ; evaluation witness for bpre-teeth-live-replay-without-ready-probe
; Without history extension: a ready related Store that never held the record.
(make-event `(defconst *bpre-empty-probe* ',(fn-snrt-run (fn-sn-open-state (fn-sn-open-observed *bpr-groups* 20 0 nil)) *bpre-barriers*)))
(assert-event (fn-snt-relation *bpre-empty-probe*))
(assert-event (equal (fn-bprv-phase *bpre-empty-probe*) :ready))
(assert-event (not (fn-bprv-extendsp *bpre-final-store* *bpre-empty-probe*)))
(local
 (must-fail-checked
  (defthm bpre-teeth-live-replay-without-extension
    (implies (and (fn-snt-relation *bpr-store*)
                  (equal (fn-bprr-replay *bpre-empty-probe* (list *bprr-config-record*) *bpre-arena*)
                         (list t (fn-bpr-initial-state *bpr-config*)))
                  (fn-snt-relation *bpre-empty-probe*)
                  (equal (fn-bprv-phase *bpre-empty-probe*) :ready))
             (equal (fn-bprr-replay *bpre-empty-probe*
                                    (caddr (fn-bpr-live-run *bpre-live0* *bpre-events* *bpre-arena*)) *bpre-arena*)
                    (list t (cadr (fn-bpr-live-run *bpre-live0* *bpre-events* *bpre-arena*)))))
    :hints (("Goal" :do-not-induct t)))))
(assert-event (not (implies (and (fn-snt-relation *bpr-store*)
                  (equal (in-arena-fn-bprr-replay *bpre-payloads* *bpre-empty-probe* (list *bprr-config-record*))
                         (list t (fn-bpr-initial-state *bpr-config*)))
                  (fn-snt-relation *bpre-empty-probe*)
                  (equal (fn-bprv-phase *bpre-empty-probe*) :ready))
             (equal (in-arena-fn-bprr-replay *bpre-payloads* *bpre-empty-probe* (caddr (in-arena-fn-bpr-live-run *bpre-payloads* *bpre-live0* *bpre-events*)))
                    (list t (cadr (in-arena-fn-bpr-live-run *bpre-payloads* *bpre-live0* *bpre-events*))))))) ; evaluation witness for bpre-teeth-live-replay-without-extension
; Without the base agreement: a live state ahead of its journal stays ahead.
(defconst *bpre-ahead-live0*
  (list *bpr-store* *bpr-context-state* (list *bprr-config-record*)))
(assert-event (not (equal (in-arena-fn-bprr-replay *bpre-payloads* *bpre-probe* (caddr *bpre-ahead-live0*))
                          (list t (cadr *bpre-ahead-live0*)))))
(local
 (must-fail-checked
  (defthm bpre-teeth-live-replay-without-base-agreement
    (implies (and (fn-snt-relation *bpr-store*)
                  (fn-snt-relation *bpre-probe*)
                  (equal (fn-bprv-phase *bpre-probe*) :ready)
                  (fn-bprv-extendsp (car (fn-bpr-live-run *bpre-ahead-live0* (cdr *bpre-events*) *bpre-arena*))
                                    *bpre-probe*))
             (equal (fn-bprr-replay *bpre-probe*
                                    (caddr (fn-bpr-live-run *bpre-ahead-live0* (cdr *bpre-events*) *bpre-arena*)) *bpre-arena*)
                    (list t (cadr (fn-bpr-live-run *bpre-ahead-live0* (cdr *bpre-events*) *bpre-arena*)))))
    :hints (("Goal" :do-not-induct t)))))
(assert-event (not (implies (and (fn-snt-relation *bpr-store*)
                  (fn-snt-relation *bpre-probe*)
                  (equal (fn-bprv-phase *bpre-probe*) :ready)
                  (fn-bprv-extendsp (car (in-arena-fn-bpr-live-run *bpre-payloads* *bpre-ahead-live0* (cdr *bpre-events*)))
                                    *bpre-probe*))
             (equal (in-arena-fn-bprr-replay *bpre-payloads* *bpre-probe* (caddr (in-arena-fn-bpr-live-run *bpre-payloads* *bpre-ahead-live0* (cdr *bpre-events*))))
                    (list t (cadr (in-arena-fn-bpr-live-run *bpre-payloads* *bpre-ahead-live0* (cdr *bpre-events*)))))))) ; evaluation witness for bpre-teeth-live-replay-without-base-agreement
; Without the live Store's relation: the conclusion is not refuted (every
; accepted record was accepted by a typed Store, whose history the kernel
; extends), so the hypothesis is refuted where it does work, in
; fn-bpr-live-step-extends-history: an untyped Store with an improper record
; list is a no-op for every transition and is not its own prefix.
(defconst *bpre-untyped-store*
  (fn-sn-make *bpr-groups* 20 (fn-sf-make :ready 3 nil (cons *bpr-row* 7) nil nil nil
                                          *fn-sf-recovery-barrier-count*)
              (fn-sn-node *bpr-store*) nil (fn-stx-index-empty)))
(assert-event (not (fn-sn-statep *bpre-untyped-store*)))
; fn-snrt-step carries (fn-sn-statep s) now (store, 2026-09-19); this witness is a
; non-state on purpose, so it is evaluated on the :logic body.
(assert-event (with-guard-checking :none
               (equal (fn-snrt-step *bpre-untyped-store* '(:io :start-frontier nil))
                      *bpre-untyped-store*)))
(local
 (must-fail-checked
  (defthm bpre-teeth-live-extension-without-relation
    (fn-bprv-extendsp *bpre-untyped-store*
                      (car (fn-bpr-live-step (list *bpre-untyped-store* *bpr-initial*
                                                   (list *bprr-config-record*))
                                             '(:store (:io :start-frontier nil)) *bpre-arena*))))))

; fn-bprv-evolving-invariant-survives-observed-reopen: an image that is not
; admissible (the history dropped) reopens to a Store the contexts are not
; grounded in.
(assert-event (not (fn-sf-crash-imagep (fn-sn-files *bpre-final-store*) *bpre-frontier* nil)))
(local
 (must-fail-checked
  (defthm bpre-teeth-reopen-without-admissible-image
    (implies (and (fn-bprv-system-invariantp *bpre-final-store* *bpre-final-state* *bpre-journal* *bpre-arena*)
                  (fn-sn-observed-identity-okp nil))
             (let ((opened (fn-sn-open-observed (fn-sn-groups *bpre-final-store*)
                                                (fn-sn-capacity *bpre-final-store*)
                                                *bpre-frontier* nil)))
               (and (fn-sn-open-okp opened)
                    (fn-bprv-system-invariantp (fn-sn-open-state opened)
                                               *bpre-final-state* *bpre-journal* *bpre-arena*))))
    :hints (("Goal" :do-not-induct t
                     :in-theory (theory 'minimal-theory))))))
(assert-event (not (implies (and (in-arena-fn-bprv-system-invariantp *bpre-payloads* *bpre-final-store* *bpre-final-state* *bpre-journal*)
                  (fn-sn-observed-identity-okp nil))
             (let ((opened (fn-sn-open-observed (fn-sn-groups *bpre-final-store*)
                                                (fn-sn-capacity *bpre-final-store*)
                                                *bpre-frontier* nil)))
               (and (fn-sn-open-okp opened)
                    (in-arena-fn-bprv-system-invariantp *bpre-payloads* (fn-sn-open-state opened) *bpre-final-state* *bpre-journal*)))))) ; evaluation witness for bpre-teeth-reopen-without-admissible-image

; -----------------------------------------------------------------------------
; fn-bprv-evolving-output-is-history-grounded (PRF-012, restated by flip-L4
; over fn-bpr-rows-stand-for; audit packet G6-3, lane audit-fixes).  Its
; conclusion, verbatim, as one executable predicate over the arena.
(defun bpre-hg-conclusion (store st journal request fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                       (fn-bpr-state-contexts st)))
         (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                     (fn-bpr-state-receipts st)))
         (record (fn-bprv-find-grounding-record
                  (fn-bpr-state-config st) context
                  (fn-bpr-article-records (fn-bprv-history store)) fn-arena)))
    (and (consp context)
         (equal (fn-bpaj-request-ref request)
                (fn-bpr-context-request-ref context))
         (fn-record-p record)
         (fn-bpr-rows-stand-for record (fn-bpr-article-records (fn-bprv-history store))
                                fn-arena)
         (equal context (fn-bpr-context-from-request
                         record (fn-bpr-context-resolve context record)))
         (equal (fn-bpa-request-article (fn-bpr-context-resolve context record))
                (fn-record-payload record))
         (equal (fn-bpa-request-subject (fn-bpr-context-resolve context record))
                (fn-record-content-subject record))
         (member-equal entry (fn-bpr-state-receipts st))
         (fn-bprv-entry-decidedp entry journal)
         (equal (fn-bpr-receipt-entry-receipt entry)
                (fn-bpr-receipt-for context (fn-bpr-state-config st)
                                    (fn-bpa-receipt-id
                                     (fn-bpr-receipt-entry-receipt entry))))
         (equal (fn-bpr-receipt-adu st request)
                (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry))))))
(bpr-lift bpre-hg-conclusion 4)

; Positive witnesses: the complete antecedent and conclusion on three states
; the live trace reaches -- the recovered Store after the crash (:ready), the
; post-crash replaying Store (its node empty, its history intact), and the
; final state of the uncrashed run.
(assert-event
 (and (in-arena-fn-bprv-evolving-invariantp *bpre-payloads* (car *bpre-recovered*)
                                            (cadr *bpre-recovered*) (caddr *bpre-recovered*))
      (fn-bpr-receipt-adu (cadr *bpre-recovered*) *bpr-request*)
      (in-arena-bpre-hg-conclusion *bpre-payloads* (car *bpre-recovered*) (cadr *bpre-recovered*)
                                   (caddr *bpre-recovered*) *bpr-request*)))
(assert-event
 (and (in-arena-fn-bprv-evolving-invariantp *bpre-payloads* (car *bpre-replaying*)
                                            (cadr *bpre-replaying*) (caddr *bpre-replaying*))
      (fn-bpr-receipt-adu (cadr *bpre-replaying*) *bpr-request*)
      (in-arena-bpre-hg-conclusion *bpre-payloads* (car *bpre-replaying*) (cadr *bpre-replaying*)
                                   (caddr *bpre-replaying*) *bpr-request*)))
(assert-event
 (and (in-arena-fn-bprv-evolving-invariantp *bpre-payloads* (car *bpre-final*)
                                            (cadr *bpre-final*) (caddr *bpre-final*))
      (fn-bpr-receipt-adu (cadr *bpre-final*) *bpr-request*)
      (in-arena-bpre-hg-conclusion *bpre-payloads* (car *bpre-final*) (cadr *bpre-final*)
                                   (caddr *bpre-final*) *bpr-request*)))

; Removal of (fn-bpr-receipt-adu st request): the receiver's opening state
; (reached: the first state of the live trace) holds the invariant, has no
; receipt for the request, and the conclusion fails (no context).
(assert-event
 (and (in-arena-fn-bprv-evolving-invariantp *bpre-payloads* (car *bpre-live0*)
                                            (cadr *bpre-live0*) (caddr *bpre-live0*))
      (not (fn-bpr-receipt-adu (cadr *bpre-live0*) *bpr-request*))
      (not (in-arena-bpre-hg-conclusion *bpre-payloads* (car *bpre-live0*) (cadr *bpre-live0*)
                                        (caddr *bpre-live0*) *bpr-request*))))

; Removal of the evolving invariant (CORRUPTED STATE, not reached): the
; recovered receiver state and journal paired with an initial Store whose
; history holds no article.  The receipt is still answered; the invariant
; fails (the context is grounded in no history record), and so does the
; conclusion (no grounding record).
(defconst *bpre-hg-orphan-store* (fn-sn-initial *bpr-groups* 20))
(assert-event
 (and (not (in-arena-fn-bprv-evolving-invariantp *bpre-payloads* *bpre-hg-orphan-store*
                                                 (cadr *bpre-recovered*) (caddr *bpre-recovered*)))
      (fn-bpr-receipt-adu (cadr *bpre-recovered*) *bpr-request*)
      (not (in-arena-bpre-hg-conclusion *bpre-payloads* *bpre-hg-orphan-store* (cadr *bpre-recovered*)
                                        (caddr *bpre-recovered*) *bpr-request*))))
