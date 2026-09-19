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
(include-book "std/testing/must-fail" :dir :system)
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
  (fn-bpi-make-context "dtn://fn.lab/inbox" "dtn://other.lab" "local-bid-2" 300))
; A distinct archive obligation and subject: retention admits one obligation
; per identity, so the second article carries its own.
(defconst *bpre-policy2*
  (fn-bpi-make-policy "dtn://fn.lab/inbox" "dtn://fn.lab/inbox" *bpr-map*
                      "archive:receiver-2" "subject:receiver-2"
                      "unsigned-ingress-v0" 1 "receiver-policy" "terms-1"
                      "dtn://fn.lab/issuer"))
(defconst *bpre-prepared2*
  (fn-bpi-ingress-prepare (bpr-reserve *bpr-store*) *bpre-policy2* *bpre-context2* *bpre-adu2*))
(assert-event (equal (fn-bpi-result-kind *bpre-prepared2*) :prepared))
(defconst *bpre-record2* (fn-bpi-result-record *bpre-prepared2*))
(assert-event (fn-record-p *bpre-record2*))
(assert-event (not (equal (fn-record-msgid *bpre-record2*) (fn-record-msgid *bpr-record*))))

; -----------------------------------------------------------------------------
; The live trace.  The receiver opens fresh (config record only) against the
; ready Store holding the first article.

(defconst *bpre-live0*
  (list *bpr-store* (fn-bpr-initial-state *bpr-config*) (list *bprr-config-record*)))
(assert-event (fn-snt-relation *bpr-store*))
(assert-event (equal (fn-bprv-phase *bpr-store*) :ready))
(assert-event (equal (fn-bprr-replay *bpr-store* (list *bprr-config-record*))
                     (list t (fn-bpr-initial-state *bpr-config*))))

(defconst *bpre-events*
  (list (list :apply *bprr-request-record*)
        '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare *bpre-record2*))
        ; receiver step while the Store is :record-staged
        (list :apply *bprr-intent-record*)
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))
        ; receiver step while the Store is :completing, the second record
        ; already in the history and not yet node-committed
        (list :apply *bprr-decision-record*)
        '(:store (:finish))))

(defun bpre-run-prefixes (live events)
  (if (consp events)
      (cons live (bpre-run-prefixes (fn-bpr-live-step live (car events)) (cdr events)))
    (list live)))
(defun bpre-all-system-invariant (lives)
  (if (consp lives)
      (and (fn-bprv-system-invariantp (car (car lives)) (cadr (car lives)) (caddr (car lives)))
           (bpre-all-system-invariant (cdr lives)))
    t))
(defun bpre-retired-invariant-failures (lives)
  (if (consp lives)
      (+ (if (fn-bprv-invariantp (car (car lives)) (cadr (car lives)) (caddr (car lives))) 0 1)
         (bpre-retired-invariant-failures (cdr lives)))
    0))
(defun bpre-phases (lives)
  (if (consp lives)
      (cons (fn-bprv-phase (car (car lives))) (bpre-phases (cdr lives)))
    nil))

(defconst *bpre-lives* (bpre-run-prefixes *bpre-live0* *bpre-events*))
(defconst *bpre-final* (fn-bpr-live-run *bpre-live0* *bpre-events*))
(assert-event (equal (car (last *bpre-lives*)) *bpre-final*))

; Every intermediate state satisfies the restated invariant.
(assert-event (bpre-all-system-invariant *bpre-lives*))
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
(assert-event (equal (bpre-retired-invariant-failures *bpre-lives*) 10))
(assert-event (fn-bprv-invariantp (car *bpre-final*) (cadr *bpre-final*) (caddr *bpre-final*)))

; The final live state: both records durable, the receipt held, the journal
; exactly the four records fn-bprj-apply accepted.
(defconst *bpre-final-store* (car *bpre-final*))
(defconst *bpre-final-state* (cadr *bpre-final*))
(defconst *bpre-journal* (caddr *bpre-final*))
(assert-event (equal *bpre-journal*
                     (list *bprr-config-record* *bprr-request-record*
                           *bprr-intent-record* *bprr-decision-record*)))
(assert-event (equal (fn-bprv-phase *bpre-final-store*) :ready))
(assert-event (equal (fn-bprv-history *bpre-final-store*) (list *bpr-record* *bpre-record2*)))
(assert-event (fn-bpi-node-record-committedp (fn-sn-node *bpre-final-store*) *bpr-record*))
(assert-event (fn-bpi-node-record-committedp (fn-sn-node *bpre-final-store*) *bpre-record2*))
(assert-event (equal (fn-bpr-receipt-adu *bpre-final-state* *bpr-request*) *bpr-receipt-adu*))
(assert-event (equal (fn-bprr-replay *bpre-final-store* *bpre-journal*) (list t *bpre-final-state*)))

; The mid-ingress states, named for the teeth below.
(defconst *bpre-staged* (nth 6 *bpre-lives*))
(defconst *bpre-completing* (nth 10 *bpre-lives*))
(assert-event (equal (fn-bprv-phase (car *bpre-staged*)) :record-staged))
(assert-event (equal (fn-bprv-phase (car *bpre-completing*)) :completing))
(assert-event (fn-bprv-evolving-invariantp (car *bpre-staged*) (cadr *bpre-staged*) (caddr *bpre-staged*)))
(assert-event (not (fn-bprv-invariantp (car *bpre-staged*) (cadr *bpre-staged*) (caddr *bpre-staged*))))
(assert-event (member-equal *bpre-record2* (fn-bprv-history (car *bpre-completing*))))
(assert-event (fn-snt-relation (car *bpre-completing*)))
(assert-event (not (fn-bpi-node-record-committedp (fn-sn-node (car *bpre-completing*)) *bpre-record2*)))

; -----------------------------------------------------------------------------
; Crash, reopen through the host's entry, recovery barriers, fn-bprj-install.

(defconst *bpre-frontier* (fn-sf-frontier (fn-sn-files *bpre-final-store*)))
(defconst *bpre-records* (fn-sf-records (fn-sn-files *bpre-final-store*)))
(assert-event (fn-sf-crash-imagep (fn-sn-files *bpre-final-store*) *bpre-frontier* *bpre-records*))
(defconst *bpre-opened*
  (fn-sn-open-observed (fn-sn-groups *bpre-final-store*) (fn-sn-capacity *bpre-final-store*)
                       *bpre-frontier* *bpre-records*))
(assert-event (fn-sn-open-okp *bpre-opened*))
(assert-event (equal (fn-bprv-phase (fn-sn-open-state *bpre-opened*)) :recovering))
(defconst *bpre-barriers*
  '((:io :recovery-barrier :ok) (:io :recovery-barrier :ok) (:io :recovery-barrier :ok)
    (:io :recovery-barrier :ok) (:io :recovery-barrier :ok)))
(defconst *bpre-probe* (fn-snrt-run (fn-sn-open-state *bpre-opened*) *bpre-barriers*))
(assert-event (equal (fn-bprv-phase *bpre-probe*) :ready))
(assert-event (fn-snt-relation *bpre-probe*))
(defconst *bpre-installed* (fn-bpr-live-install *bpre-probe* *bpre-journal*))
(assert-event (equal (cadr *bpre-installed*) *bpre-final-state*))
(assert-event (equal (fn-bpr-receipt-adu (cadr *bpre-installed*) *bpr-request*) *bpr-receipt-adu*))
(assert-event (fn-bprv-system-invariantp *bpre-probe* *bpre-final-state* *bpre-journal*))
(assert-event (fn-bprv-system-invariantp (fn-sn-open-state *bpre-opened*) *bpre-final-state* *bpre-journal*))

; The same restart inside the kernel's own crash constructor: the receiver
; state is retained through :replaying (empty node) and recovery.
(defconst *bpre-crash-events*
  (append *bpre-events*
          (list '(:store (:crash :old :present)) '(:store (:recover))
                '(:store (:io :recovery-barrier :ok)) '(:store (:io :recovery-barrier :ok))
                '(:store (:io :recovery-barrier :ok)) '(:store (:io :recovery-barrier :ok))
                '(:store (:io :recovery-barrier :ok)))))
(defconst *bpre-crash-lives* (bpre-run-prefixes *bpre-live0* *bpre-crash-events*))
(assert-event (bpre-all-system-invariant *bpre-crash-lives*))
(defconst *bpre-replaying* (nth 13 *bpre-crash-lives*))
(assert-event (equal (fn-bprv-phase (car *bpre-replaying*)) :replaying))
(assert-event (equal (fn-sn-node (car *bpre-replaying*))
                     (fn-node-initial-state *bpr-groups* 20)))
(defconst *bpre-recovered* (car (last *bpre-crash-lives*)))
(assert-event (equal (fn-bprv-phase (car *bpre-recovered*)) :ready))
(assert-event (equal (fn-bpr-receipt-adu (cadr *bpre-recovered*) *bpr-request*) *bpr-receipt-adu*))
(assert-event (equal (fn-bprr-replay (car *bpre-recovered*) (caddr *bpre-recovered*))
                     (list t (cadr *bpre-recovered*))))

; -----------------------------------------------------------------------------
; Teeth.  One must-fail per hypothesis, each violating only that hypothesis
; and stating the keystone's conclusion.

; fn-bprv-grounded-context-has-history-record: a context whose record is in
; no history is not grounded, and its grounding record is not a record.
(assert-event (fn-bprv-context-groundedp *bpr-config* *bprr-context* (list *bpr-record*)))
(assert-event (not (fn-bprv-context-groundedp *bpr-config* *bprr-context* (list *bpre-record2*))))
(local
 (must-fail
  (defthm bpre-teeth-grounded-without-history-record
    (let ((record (fn-bprv-find-grounding-record *bpr-config* *bprr-context* (list *bpre-record2*))))
      (and (fn-record-p record)
           (member-equal record (list *bpre-record2*)))))))

; fn-bprv-grounded-monotone: a history that drops the record is not a prefix,
; and groundedness does not carry to it.
(assert-event (not (fn-sf-prefixp (list *bpr-record*) (list *bpre-record2*))))
(local
 (must-fail
  (defthm bpre-teeth-monotone-without-prefix
    (implies (fn-bprv-context-groundedp *bpr-config* *bprr-context* (list *bpr-record*))
             (fn-bprv-context-groundedp *bpr-config* *bprr-context* (list *bpre-record2*))))))

; fn-bprv-system-step-preserves-invariant: a receiver record outside the
; journal breaks fn-bprv-entries-decidedp.
(defconst *bpre-intent-journal*
  (list *bprr-config-record* *bprr-request-record* *bprr-intent-record*))
(defconst *bpre-intent-state*
  (cadr (fn-bprr-replay *bpr-store* *bpre-intent-journal*)))
(assert-event (fn-bprv-system-invariantp *bpr-store* *bpre-intent-state* *bpre-intent-journal*))
(assert-event (not (member-equal *bprr-decision-record* *bpre-intent-journal*)))
(local
 (must-fail
  (defthm bpre-teeth-system-step-without-journaled-record
    (let ((next (fn-bprv-system-step *bpr-store* *bpre-intent-state*
                                     (list :receiver *bprr-decision-record*))))
      (fn-bprv-system-invariantp (car next) (cadr next) *bpre-intent-journal*)))))

; fn-bprv-history-record-is-node-committed-when-idle, three hypotheses.
; Without the idle phase: the :completing Store holds the second record in
; its history and its node has not completed it.
(local
 (must-fail
  (defthm bpre-teeth-committed-without-idle-phase
    (implies (and (fn-snt-relation (car *bpre-completing*))
                  (member-equal *bpre-record2* (fn-bprv-history (car *bpre-completing*))))
             (fn-bpi-node-record-committedp (fn-sn-node (car *bpre-completing*)) *bpre-record2*)))))
; Without the live-history relation: the ready files with an empty node.
(defconst *bpre-forged-store*
  (fn-sn-make *bpr-groups* 20 (fn-sn-files *bpre-final-store*)
              (fn-node-initial-state *bpr-groups* 20)))
(assert-event (fn-sn-statep *bpre-forged-store*))
(assert-event (equal (fn-bprv-phase *bpre-forged-store*) :ready))
(assert-event (not (fn-snt-relation *bpre-forged-store*)))
(local
 (must-fail
  (defthm bpre-teeth-committed-without-relation
    (implies (and (member-equal (fn-bprv-phase *bpre-forged-store*)
                                '(:ready :recovering :fenced-recovery))
                  (member-equal *bpr-record* (fn-bprv-history *bpre-forged-store*)))
             (fn-bpi-node-record-committedp (fn-sn-node *bpre-forged-store*) *bpr-record*)))))
; Without membership: the second record before its ingress.
(assert-event (not (member-equal *bpre-record2* (fn-bprv-history *bpr-store*))))
(local
 (must-fail
  (defthm bpre-teeth-committed-without-membership
    (implies (and (fn-snt-relation *bpr-store*)
                  (member-equal (fn-bprv-phase *bpr-store*) '(:ready :recovering :fenced-recovery)))
             (fn-bpi-node-record-committedp (fn-sn-node *bpr-store*) *bpre-record2*)))))

; fn-bprv-evolving-output-is-node-grounded-when-idle: the phase tolerance the
; design is for.  In :replaying with the post-crash empty node the history
; conclusion (L18) holds while the node conclusion (L20) is false.
(defconst *bpre-replaying-context*
  (fn-bpr-find-context (fn-bpa-request-work-id *bpr-request*)
                       (fn-bpr-state-contexts (cadr *bpre-replaying*))))
(defconst *bpre-replaying-record*
  (fn-bprv-find-grounding-record *bpr-config* *bpre-replaying-context*
                                 (fn-bprv-history (car *bpre-replaying*))))
(assert-event (fn-bprv-evolving-invariantp (car *bpre-replaying*) (cadr *bpre-replaying*)
                                           (caddr *bpre-replaying*)))
(assert-event (fn-snt-relation (car *bpre-replaying*)))
(assert-event (fn-bpr-receipt-adu (cadr *bpre-replaying*) *bpr-request*))
(assert-event (and (fn-record-p *bpre-replaying-record*)
                   (member-equal *bpre-replaying-record* (fn-bprv-history (car *bpre-replaying*)))
                   (equal *bpre-replaying-context*
                          (fn-bpr-context-from-request *bpre-replaying-record* *bpr-request*))))
(local
 (must-fail
  (defthm bpre-teeth-node-grounded-without-idle-phase
    (implies (and (fn-bprv-evolving-invariantp (car *bpre-replaying*) (cadr *bpre-replaying*)
                                               (caddr *bpre-replaying*))
                  (fn-snt-relation (car *bpre-replaying*))
                  (fn-bpr-receipt-adu (cadr *bpre-replaying*) *bpr-request*))
             (fn-bpi-node-record-committedp (fn-sn-node (car *bpre-replaying*))
                                            *bpre-replaying-record*)))))

; fn-bpr-live-state-is-replay-of-journal, four hypotheses.
; Without a ready probe: the reopened Store before its barriers refuses the
; request context and replay stops.
(defconst *bpre-recovering-probe* (fn-sn-open-state *bpre-opened*))
(assert-event (fn-snt-relation *bpre-recovering-probe*))
(assert-event (fn-bprv-extendsp *bpre-final-store* *bpre-recovering-probe*))
(assert-event (not (equal (fn-bprv-phase *bpre-recovering-probe*) :ready)))
(local
 (must-fail
  (defthm bpre-teeth-live-replay-without-ready-probe
    (implies (and (fn-snt-relation *bpr-store*)
                  (equal (fn-bprr-replay *bpre-recovering-probe* (list *bprr-config-record*))
                         (list t (fn-bpr-initial-state *bpr-config*)))
                  (fn-snt-relation *bpre-recovering-probe*)
                  (fn-bprv-extendsp (car (fn-bpr-live-run *bpre-live0* *bpre-events*))
                                    *bpre-recovering-probe*))
             (equal (fn-bprr-replay *bpre-recovering-probe*
                                    (caddr (fn-bpr-live-run *bpre-live0* *bpre-events*)))
                    (list t (cadr (fn-bpr-live-run *bpre-live0* *bpre-events*))))))))
; Without history extension: a ready related Store that never held the record.
(defconst *bpre-empty-probe*
  (fn-snrt-run (fn-sn-open-state (fn-sn-open-observed *bpr-groups* 20 0 nil)) *bpre-barriers*))
(assert-event (fn-snt-relation *bpre-empty-probe*))
(assert-event (equal (fn-bprv-phase *bpre-empty-probe*) :ready))
(assert-event (not (fn-bprv-extendsp *bpre-final-store* *bpre-empty-probe*)))
(local
 (must-fail
  (defthm bpre-teeth-live-replay-without-extension
    (implies (and (fn-snt-relation *bpr-store*)
                  (equal (fn-bprr-replay *bpre-empty-probe* (list *bprr-config-record*))
                         (list t (fn-bpr-initial-state *bpr-config*)))
                  (fn-snt-relation *bpre-empty-probe*)
                  (equal (fn-bprv-phase *bpre-empty-probe*) :ready))
             (equal (fn-bprr-replay *bpre-empty-probe*
                                    (caddr (fn-bpr-live-run *bpre-live0* *bpre-events*)))
                    (list t (cadr (fn-bpr-live-run *bpre-live0* *bpre-events*))))))))
; Without the base agreement: a live state ahead of its journal stays ahead.
(defconst *bpre-ahead-live0*
  (list *bpr-store* *bpr-context-state* (list *bprr-config-record*)))
(assert-event (not (equal (fn-bprr-replay *bpre-probe* (caddr *bpre-ahead-live0*))
                          (list t (cadr *bpre-ahead-live0*)))))
(local
 (must-fail
  (defthm bpre-teeth-live-replay-without-base-agreement
    (implies (and (fn-snt-relation *bpr-store*)
                  (fn-snt-relation *bpre-probe*)
                  (equal (fn-bprv-phase *bpre-probe*) :ready)
                  (fn-bprv-extendsp (car (fn-bpr-live-run *bpre-ahead-live0* (cdr *bpre-events*)))
                                    *bpre-probe*))
             (equal (fn-bprr-replay *bpre-probe*
                                    (caddr (fn-bpr-live-run *bpre-ahead-live0* (cdr *bpre-events*))))
                    (list t (cadr (fn-bpr-live-run *bpre-ahead-live0* (cdr *bpre-events*)))))))))
; Without the live Store's relation: the conclusion is not refuted (every
; accepted record was accepted by a typed Store, whose history the kernel
; extends), so the hypothesis is refuted where it does work, in
; fn-bpr-live-step-extends-history: an untyped Store with an improper record
; list is a no-op for every transition and is not its own prefix.
(defconst *bpre-untyped-store*
  (fn-sn-make *bpr-groups* 20 (fn-sf-make :ready 3 nil (cons *bpr-record* 7) nil nil nil 5)
              (fn-sn-node *bpr-store*)))
(assert-event (not (fn-sn-statep *bpre-untyped-store*)))
(assert-event (equal (fn-snrt-step *bpre-untyped-store* '(:io :start-frontier nil))
                     *bpre-untyped-store*))
(local
 (must-fail
  (defthm bpre-teeth-live-extension-without-relation
    (fn-bprv-extendsp *bpre-untyped-store*
                      (car (fn-bpr-live-step (list *bpre-untyped-store* *bpr-initial*
                                                   (list *bprr-config-record*))
                                             '(:store (:io :start-frontier nil))))))))

; fn-bprv-evolving-invariant-survives-observed-reopen: an image that is not
; admissible (the history dropped) reopens to a Store the contexts are not
; grounded in.
(assert-event (not (fn-sf-crash-imagep (fn-sn-files *bpre-final-store*) *bpre-frontier* nil)))
(local
 (must-fail
  (defthm bpre-teeth-reopen-without-admissible-image
    (implies (fn-bprv-system-invariantp *bpre-final-store* *bpre-final-state* *bpre-journal*)
             (let ((opened (fn-sn-open-observed (fn-sn-groups *bpre-final-store*)
                                                (fn-sn-capacity *bpre-final-store*)
                                                *bpre-frontier* nil)))
               (and (fn-sn-open-okp opened)
                    (fn-bprv-system-invariantp (fn-sn-open-state opened)
                                               *bpre-final-state* *bpre-journal*)))))))
