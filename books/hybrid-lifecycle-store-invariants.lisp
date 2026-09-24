; Connect the operator-local key view to the actual Store completion path.
(in-package "ACL2")
(include-book "hybrid-lifecycle")
(include-book "store-node-resolution")

(defun fn-hls-current-enrollment (s requested)
  (declare (xargs :guard t))
  (fn-hl-current-enrollment requested (fn-sn-keyring-snapshots s)))

; Identity completion is the sole live Store update of the carried snapshot
; list. This projection exposes the exact identity interpreter result to the
; host-facing selector without validating the full Store on a served path.
(defthm fn-hls-finish-identity-current-enrollment
  (equal (fn-hls-current-enrollment
          (fn-sn-finish-identity s files record node) requested)
         (fn-hl-current-enrollment
          requested
          (fn-stxk-context-snapshots
           (fn-replay-identity-step (fn-sn-identity-context s) record))))
  :hints (("Goal" :in-theory
           (e/d (fn-hls-current-enrollment fn-sn-finish-identity)
                (fn-hl-current-enrollment fn-replay-identity-step
                 fn-stxk-p fn-stxe-p fn-stxa-p)))))

(defthm fn-hls-current-enrollment-of-with-consumer
  (equal (fn-hls-current-enrollment (fn-sn-with-consumer s consumer) requested)
         (fn-hls-current-enrollment s requested))
  :hints (("Goal" :in-theory (enable fn-hls-current-enrollment))))

(defthm fn-hls-current-enrollment-of-with-topic
  (equal (fn-hls-current-enrollment (fn-sn-with-topic s topic) requested)
         (fn-hls-current-enrollment s requested))
  :hints (("Goal" :in-theory (enable fn-hls-current-enrollment))))

(defthm fn-hls-finish-snapshot-current-enrollment
  (implies (and (fn-sn-completion-enabledp s)
                (fn-stxk-p (fn-sn-completion-record s))
                (not (fn-store-retention-event-p
                      (fn-sn-completion-record s)))
                (not (fn-cpe-eventp (fn-sn-completion-record s)))
                (not (fn-th-topic-eventp (fn-sn-completion-record s))))
           (equal
            (fn-hls-current-enrollment (fn-sn-finish s) requested)
            (fn-hl-current-enrollment
             requested
             (fn-stxk-context-snapshots
              (fn-replay-identity-step
               (fn-sn-identity-context s)
               (fn-sn-completion-record s))))))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-finish)
                (fn-sn-completion-enabledp fn-stxk-p fn-stxe-p fn-stxa-p
                 fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp
                 fn-hls-current-enrollment fn-hl-current-enrollment
                 fn-replay-identity-step
                 fn-sn-finish-identity)))))

; A kind-3 record starts with a numeric Store sequence. Retention, consumer
; and topic events use disjoint leading tags. Keep their codecs closed in the
; completed-snapshot proof below.
(defthm fn-hls-snapshot-has-numeric-first-field
  (implies (fn-stxk-p event) (natp (car event)))
  :hints (("Goal" :in-theory (enable fn-stxk-p fn-stxk-shapep
                                     fn-stxk-sequence fn-record-uint32p))))

(defthm fn-hls-snapshot-disjoint-from-other-store-events
  (implies (fn-stxk-p event)
           (and (not (fn-store-retention-event-p event))
                (not (fn-cpe-eventp event))
                (not (fn-th-topic-eventp event))))
  :hints (("Goal"
           :use (fn-hls-snapshot-has-numeric-first-field
                 (:instance fn-th-topic-event-is-not-stxk))
           :in-theory
           (e/d (fn-store-retention-event-p fn-store-event-nth
                  fn-cpe-eventp fn-cp-nth)
                (fn-stxk-p fn-th-topic-eventp)))))

; This is the completed Store-node statement: the same per-principal selector
; the host calls reads exactly the snapshot history returned by the identity
; interpreter for the durable event. The premise is the actual finish gate,
; not a hypothetical successful snapshot application.
(defthm fn-hls-finish-snapshot-from-maintained-state
  (implies (and (fn-sn-completion-enabledp s)
                (fn-stxk-p (fn-sn-completion-record s)))
           (equal
            (fn-hls-current-enrollment (fn-sn-finish s) requested)
            (fn-hl-current-enrollment
             requested
             (fn-stxk-context-snapshots
              (fn-replay-identity-step
               (fn-sn-identity-context s)
               (fn-sn-completion-record s))))))
  :hints (("Goal"
           :use ((:instance fn-hls-snapshot-disjoint-from-other-store-events
                            (event (fn-sn-completion-record s)))
                 (:instance fn-hls-finish-snapshot-current-enrollment))
           :in-theory
           (disable fn-sn-finish fn-hls-current-enrollment
                    fn-hl-current-enrollment fn-replay-identity-step
                    fn-stxk-p fn-sn-completion-enabledp))))

; A keyring snapshot changes the prospective local authority, not a recorded
; kind-4 verdict. The identity context used for one completion starts with no
; newly emitted verdicts, and the snapshot arm emits none.
(defthm fn-hls-snapshot-identity-step-has-no-new-verdict
  (implies (fn-stxk-p event)
           (equal (fn-stxk-context-verdicts
                   (fn-replay-identity-step
                    (fn-sn-identity-context s) event))
                  nil))
  :hints (("Goal" :in-theory
           (e/d (fn-replay-identity-step fn-sn-identity-context
                  fn-stxk-apply-snapshot fn-stxk-fault fn-stxk-context)
                (fn-stxk-p fn-stxe-p fn-stxa-p
                 fn-hsig-keyring-snapshot-value
                 fn-replay-identity-advance)))))

(defthm fn-hls-finish-identity-snapshot-keeps-verdicts
  (implies (fn-stxk-p record)
           (equal (fn-sn-verdicts
                   (fn-sn-finish-identity s files record node))
                  (fn-sn-verdicts s)))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-finish-identity fn-replay-verdict-pairs)
                (fn-stxk-p fn-replay-identity-step
                 fn-sn-identity-context)))))

(defthm fn-hls-finish-snapshot-keeps-historical-verdicts
  (implies (fn-stxk-p (fn-sn-completion-record s))
           (equal (fn-sn-verdicts (fn-sn-finish s))
                  (fn-sn-verdicts s)))
  :hints (("Goal"
           :use ((:instance fn-hls-snapshot-disjoint-from-other-store-events
                            (event (fn-sn-completion-record s))))
           :in-theory
           (e/d (fn-sn-finish)
                (fn-sn-completion-enabledp fn-stxk-p fn-stxe-p fn-stxa-p
                 fn-store-retention-event-p fn-cpe-eventp
                 fn-th-topic-eventp fn-sn-finish-identity)))))

; The derived event index is unrelated to author authority. Recovery installs
; the exact identity replay context through fn-sn-update-replayed before the
; topic, event-index and consumer projections are layered around it.
(defthm fn-hls-current-enrollment-of-with-event-index
  (equal (fn-hls-current-enrollment
          (fn-sn-with-event-index s event-index) requested)
         (fn-hls-current-enrollment s requested))
  :hints (("Goal" :in-theory (enable fn-hls-current-enrollment))))

(defthm fn-hls-current-enrollment-of-update-replayed
  (equal (fn-hls-current-enrollment
          (fn-sn-update-replayed s files node index identity-context)
          requested)
         (fn-hl-current-enrollment
          requested (fn-stxk-context-snapshots identity-context)))
  :hints (("Goal" :in-theory (enable fn-hls-current-enrollment))))

; A successful recovery recomputes the local author view from durable Store
; records. The phase premises identify the actual crash/replay branch; a
; pre-publication candidate is absent from those records, while a published
; kind-3 event is replayed even if live finish never ran.
(defthm fn-hls-successful-recover-current-enrollment
  (implies
   (and (fn-sn-statep s)
        (equal (fn-sf-phase (fn-sn-files s)) :replaying)
        (equal (fn-sf-phase (fn-sn-files (fn-sn-recover s))) :recovering))
   (equal
    (fn-hls-current-enrollment (fn-sn-recover s) requested)
    (fn-hl-current-enrollment
     requested
     (fn-stxk-context-snapshots
      (fn-replay-identity
       (fn-sf-records
        (fn-sf-recover (fn-sn-files s)
                       (fn-sn-groups s) (fn-sn-capacity s))))))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-sn-recover)
                (fn-sn-statep fn-sf-recover fn-replay-identity
                 fn-hls-current-enrollment fn-hl-current-enrollment
                 fn-cpe-projection-replay fn-th-prefix-project)))))

(defthm fn-hls-successful-recover-historical-verdicts
  (implies
   (and (fn-sn-statep s)
        (equal (fn-sf-phase (fn-sn-files s)) :replaying)
        (equal (fn-sf-phase (fn-sn-files (fn-sn-recover s))) :recovering))
   (equal
    (fn-sn-verdicts (fn-sn-recover s))
    (fn-replay-verdict-pairs
     (fn-stxk-context-verdicts
      (fn-replay-identity
       (fn-sf-records
        (fn-sf-recover (fn-sn-files s)
                       (fn-sn-groups s) (fn-sn-capacity s))))))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-sn-recover)
                (fn-sn-statep fn-sf-recover fn-replay-identity
                 fn-cpe-projection-replay fn-th-prefix-project)))))

;; ---------------------------------------------------------------------------
;; P8 / PRF-026.  A kind-4 (hybrid acceptance) completion records its verdict.
;; The kind-4 composite is fn-stxa-p; its verdict event is the exact kind-2
;; bytes it carries.  Standalone kind-2 evidence (fn-stxe-p) is validated but
;; deliberately contributes no accepted verdict (books/replay.lisp).
(defthm fn-hls-kind4-has-numeric-first-field
  (implies (fn-stxa-p event) (natp (car event)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-stxa-p fn-stxa-shapep
                                     fn-stxa-sequence fn-record-uint32p))))

(defthm fn-hls-kind4-disjoint-from-other-store-events
  (implies (fn-stxa-p event)
           (and (not (fn-store-retention-event-p event))
                (not (fn-cpe-eventp event))
                (not (fn-th-topic-eventp event))
                (not (fn-stxk-p event))
                (not (fn-stxe-p event))))
  :hints (("Goal"
           :use (fn-hls-kind4-has-numeric-first-field
                 (:instance fn-th-topic-event-is-not-stxa))
           :in-theory
           (e/d (fn-store-retention-event-p fn-store-event-nth
                  fn-cpe-eventp fn-cp-nth
                  fn-stxa-p fn-stxa-shapep fn-stxk-p fn-stxk-shapep
                  fn-stxe-p fn-stxe-shapep)
                (fn-th-topic-eventp)))))

(defthm fn-hls-kind4-identity-step-emits-its-verdict-event
  (implies (and (fn-stxa-p event)
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-step (fn-sn-identity-context s)
                                                 event))
                       :ok))
           (equal (fn-stxk-context-verdicts
                   (fn-replay-identity-step (fn-sn-identity-context s) event))
                  (list (fn-stmt-value
                         (fn-stxe-decode-exact
                          (fn-stxa-verdict-event event))))))
  :hints (("Goal"
           :use ((:instance fn-hls-kind4-disjoint-from-other-store-events))
           :in-theory
           (e/d (fn-replay-identity-step fn-sn-identity-context
                  fn-stxk-apply-verdict fn-stxk-fault fn-stxk-context)
                (fn-stxk-p fn-stxe-p fn-stxa-p fn-stxa-bindsp
                 fn-hsig-article-event-snapshot-bindsp fn-stxe-decode-exact
                 fn-hls-kind4-disjoint-from-other-store-events
                 fn-replay-identity-advance)))))

(defthm fn-hls-kind4-identity-step-ok-has-evidence-record
  (implies (and (fn-stxa-p event)
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-step (fn-sn-identity-context s)
                                                 event))
                       :ok))
           (fn-stxe-p (fn-stmt-value
                       (fn-stxe-decode-exact
                        (fn-stxa-verdict-event event)))))
  :hints (("Goal"
           :use ((:instance fn-hls-kind4-disjoint-from-other-store-events))
           :in-theory
           (e/d (fn-replay-identity-step fn-sn-identity-context
                  fn-stxk-apply-verdict fn-stxk-fault fn-stxk-context)
                (fn-stxk-p fn-stxe-p fn-stxa-p fn-stxa-bindsp
                 fn-hsig-article-event-snapshot-bindsp fn-stxe-decode-exact
                 fn-hls-kind4-disjoint-from-other-store-events
                 fn-replay-identity-advance)))))

(defthm fn-hls-finish-kind4-verdicts
  (implies (and (fn-sn-completion-enabledp s)
                (fn-stxa-p (fn-sn-completion-record s)))
           (equal (fn-sn-verdicts (fn-sn-finish s))
                  (let ((v (fn-stmt-value
                            (fn-stxe-decode-exact
                             (fn-stxa-verdict-event
                              (fn-sn-completion-record s))))))
                    (cons (cons (fn-stxe-msgid v)
                                (fn-stx-make-verdict
                                 (fn-stxe-token v) (fn-stxe-detail v)
                                 (fn-stxe-keyring-generation v)))
                          (fn-sn-verdicts s)))))
  :hints (("Goal"
           :use ((:instance fn-hls-kind4-disjoint-from-other-store-events
                            (event (fn-sn-completion-record s)))
                 (:instance fn-hls-kind4-identity-step-emits-its-verdict-event
                            (event (fn-sn-completion-record s)))
                 (:instance fn-hls-kind4-identity-step-ok-has-evidence-record
                            (event (fn-sn-completion-record s))))
           :in-theory
           (e/d (fn-sn-finish fn-sn-finish-identity fn-replay-verdict-pairs
                  fn-sn-completion-enabledp fn-sn-completion-core-enabledp)
                (fn-stxk-p fn-stxe-p fn-stxa-p fn-store-retention-event-p
                 fn-cpe-eventp fn-th-topic-eventp fn-replay-identity-step
                 fn-sn-identity-context fn-stxe-decode-exact
                 fn-hls-kind4-disjoint-from-other-store-events
                 fn-hls-kind4-identity-step-emits-its-verdict-event
                 fn-hls-kind4-identity-step-ok-has-evidence-record
                 fn-sn-completion-record fn-replay-apply-record
                 fn-cpe-projection-step fn-th-prefix-step fn-th-at
                 fn-sf-core-completion fn-sf-emit-success fn-sn-statep
                 fn-stx-index-add fn-sn-composite-delta)))))

(defun fn-hls-kind4-verdict-event (record)
  (declare (xargs :guard t))
  (fn-stmt-value (fn-stxe-decode-exact (fn-stxa-verdict-event record))))

;; Keystone.  Subject: fn-sn-finish, which the owner's (:complete) event runs
;; (books/owner.lisp fn-own-complete; host/owner-host.lisp fn-owner-finish)
;; and host/store-node-host.lisp fn-store-sn-finish calls directly.  The
;; query is fn-sn-verdict-lookup, the list the reader pin copies.
(defthm fn-sn-finish-of-a-kind-4-acceptance-records-its-verdict
  (implies (and (fn-sn-completion-enabledp s)
                (fn-stxa-p (fn-sn-completion-record s)))
           (let ((v (fn-hls-kind4-verdict-event (fn-sn-completion-record s))))
             (equal (fn-sn-verdict-lookup (fn-sn-finish s) (fn-stxe-msgid v))
                    (fn-stx-make-verdict (fn-stxe-token v) (fn-stxe-detail v)
                                         (fn-stxe-keyring-generation v)))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-verdict-lookup fn-sn-verdict-lookup-list
                            fn-hls-kind4-verdict-event)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-stxa-p fn-stxe-decode-exact fn-stx-make-verdict)))))
(defthm fn-sn-finish-of-a-kind-4-acceptance-keeps-other-verdicts
  (implies (and (fn-sn-completion-enabledp s)
                (fn-stxa-p (fn-sn-completion-record s))
                (not (equal msgid
                            (fn-stxe-msgid (fn-hls-kind4-verdict-event
                                            (fn-sn-completion-record s))))))
           (equal (fn-sn-verdict-lookup (fn-sn-finish s) msgid)
                  (fn-sn-verdict-lookup s msgid)))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-verdict-lookup fn-sn-verdict-lookup-list
                            fn-hls-kind4-verdict-event)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-stxa-p fn-stxe-decode-exact fn-stx-make-verdict)))))
