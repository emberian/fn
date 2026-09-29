; fn: keystones of the mutable service owner (C1-05).
;
; The subject of every theorem here is a function tools/run_owner.py calls
; through host/owner-host.lisp: fn-own-start (fn-owner-recover), fn-own-read
; (fn-owner-chunk-span-at: the served port, one fn-served-step per socket read over
; the pinned archive), fn-own-step through fn-own-open / fn-own-advance /
; fn-own-close / fn-own-begin / fn-own-store-step / fn-own-complete /
; fn-own-observe / fn-own-declare-group, and fn-own-run as the arbitrary
; finite event list the host produces.  fn-own-reopen is the process restart
; the host performs by calling fn-owner-recover again over the image on disk.
; fn-own-read-step is the per-event law under the served port: the byte fold
; inside fn-served-step applies fn-served-dispatch once per framed event
; (books/served.lisp), and fn-own-read-step is that one step with the owner's
; bookkeeping around it.  The served POST path (w5/owner-post) adds
; fn-own-take-submission (the writer step, fn-owner-take) and fn-own-outcome
; (fn-owner-outcome): the only owner entry that renders a POST outcome.
;
; Keystones (each has a reachable witness and one concrete violating value
; per hypothesis in tests/acl2/owner-tests.lisp; statements unchanged from
; the first cut of this lane except where a name is new):
;   fn-own-read-is-served-step-on-pinned-prefix         (K1, served port; new)
;   fn-own-read-is-served-step-on-pinned-prefix-after-any-trace   (new)
;   fn-own-reader-sees-pinned-prefix-replay            (K1, per event)
;   fn-own-reader-sees-pinned-prefix-replay-after-any-trace
;   fn-own-completion-consumed-once                    (K2)
;   fn-own-pinned-prefix-survives-any-trace            (K3)
;   fn-own-reclaim-floor-below-every-pin
;   fn-own-connections-bounded-after-any-trace         (K4)
;   fn-own-completed-post-survives-close-and-any-trace (K5)
;   fn-own-run-preserves-relation, fn-own-run-preserves-store-relation (K6)
;   fn-own-open-observed-start-relation                (root)
;   fn-own-every-fact-is-clock-stamped, fn-own-declare-group-without-clock-
;   is-refused, fn-own-declared-group-is-replayed      (facts)
;   fn-own-outcome-completion-is-one-of-four           (POST outcome; clock refusal)
;   fn-own-durable-reply-names-a-durable-record        (POST outcome; new)
;   fn-own-read-touches-only-its-connection            (POST isolation; new)
;   fn-own-outcome-touches-only-its-connection         (POST isolation; new)
;
; Statements changed by the w4-post-compose byte fold, not by this lane's
; choice: the served connection is six fields, so the two served-port
; keystones thread the connection's pinned config and observation, and the
; owner's current clock observation as the injection clock, into
; fn-served-make-conn; the per-event law is stated over fn-served-dispatch
; (fn-nntp-post-step with the article-mode switch), the step the fold now
; applies, where it was stated over fn-nntp-step before POST existed.
;
; Local vocabulary opened here (named on the deputy board): the owner's own
; fn-own-vocabulary; store's fn-snt-relation (fn-own-idle-node-is-replay),
; fn-snrt-step, fn-snt-step and the fn-sn-* transitions
; (fn-own-snrt-step-keeps-configuration), fn-sn-completion-enabledp
; (fn-own-completion-needs-completing-phase), fn-sf-crash-imagep
; (fn-own-crash-image-extends-records), fn-sn-open-okp and fn-sn-open-errorp
; (fn-own-open-kind-ok-is-okp); nntp's session record
; (fn-own-open-session-boundedp); served's fn-served-open (the same lemma).

(in-package "ACL2")
;
; Split 2026-09-27 (lane owner-books-split; D26: every book certifies under
; 10 s at two jobs) into four chained parts along its structure, in this order.
; Statements and names are the ones this book always had; each part replays
; the local prelude of the first.  This book includes the parts and keeps the
; export theory, so every includer is unchanged.
(include-book "owner-invariants-relation")
(include-book "owner-invariants-step")
(include-book "owner-invariants-served")
(include-book "owner-invariants-outcome")


; -----------------------------------------------------------------------------
; Export theory.  Keystones and the relation's list vocabulary stay enabled;
; the relation itself, the per-event preservation lemmas and the store facts
; proved here for the owner's own use are withdrawn under one name.

(deftheory fn-own-invariants-vocabulary
  '(fn-own-take-of-len fn-own-prefixp-len fn-own-take-of-prefix
    fn-own-prefix-archive-of-prefix fn-own-has-pairp-of-prefix
    fn-own-member-of-append-last fn-own-member-of-append-left
    fn-own-conn-okp fn-own-view-okp fn-own-relation
    fn-own-conns-okp-of-prefix fn-own-view-okp-of-prefix
    fn-own-ledger-durablep-of-prefix fn-own-ledger-durablep-append
    fn-own-ledger-durablep-member fn-own-facts-okp-append
    fn-own-find-conn-okp fn-own-find-conn-id fn-own-replace-conn-okp
    fn-own-replace-conn-len fn-own-remove-conn-okp fn-own-remove-conn-len
    fn-own-ids-below-next-p fn-own-replace-conn-ids-below-next
    fn-own-remove-conn-ids-below-next fn-own-ids-below-next-p-of-open
    fn-own-idle-node-is-replay fn-own-related-records-true-list
    fn-own-relation-records-true-list
    fn-own-related-frontier-natural fn-own-snrt-step-keeps-configuration
    fn-own-snrt-step-preserves-relation fn-own-snrt-step-records-prefix
    fn-own-completion-pair-has-record fn-own-completion-needs-completing-phase
    fn-own-crash-image-extends-records
    fn-own-refresh-keeps-fields fn-own-refresh-preserves-relation
    fn-own-open-session-boundedp fn-own-open-preserves-relation
    fn-own-read-preserves-relation fn-own-read-step-preserves-relation
    fn-own-advance-preserves-relation fn-own-close-preserves-relation
    fn-own-begin-preserves-relation fn-own-store-step-preserves-relation
    fn-own-complete-preserves-relation fn-own-reopen-preserves-relation
    fn-own-observe-preserves-relation fn-own-group-fact-make-is-fact
    fn-own-declare-group-preserves-relation fn-own-configure-preserves-relation
    fn-own-take-submission-preserves-relation fn-own-outcome-preserves-relation
    fn-own-find-conn-of-replace-conn-other fn-own-find-conn-of-remove-conn-other
    fn-own-conn-boundedp-is-post-session
    ; free-variable `groups' on its one hypothesis, so as a rewrite rule it
    ; would be tried on every `fn-auth-sessionp' term an includer states,
    ; exactly as its `-is-post-session' sibling would.  Both are withdrawn;
    ; this book reaches them with `:use' and so should an includer.
    fn-own-conn-boundedp-is-auth-session
    fn-own-step-preserves-relation
    fn-own-start-relation fn-own-complete-ledger-is-exact-pair
    fn-own-connection-events-keep-store-bound-and-ledger
    fn-own-step-records-prefix fn-own-run-records-prefix
    fn-own-min-pinned-below-floor fn-own-min-pinned-below-found
    fn-own-conns-okp-are-bounded fn-own-step-keeps-max-conns
    fn-own-run-keeps-max-conns fn-own-step-ledger-grows fn-own-run-ledger-grows
    fn-own-facts-okp-member fn-own-replay-facts-append
    fn-own-take-installs-the-queued-submission-whatever-it-carries
    fn-own-transit-outcome-touches-only-its-connection
    fn-own-transit-outcome-needs-a-transit-submission))

(in-theory (disable fn-own-invariants-vocabulary))
