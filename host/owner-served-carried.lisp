; owner-served-carried.lisp -- the owner's carried relation over the host
; writers that are proved, relied on under a NAMED assumption for the rest
; (lane post-guard-off, 2026-10-03; ember: "we can just not have that guard").
;
; WHY.  Every owner entry on the POST path had the guard
; (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state))), and the executable
; counterpart evaluates it on every call: a walk of the whole record log,
; the success keyset and the node (COST-GATE, image set 45e05c7fd: 92 ms and
; 11.8 MB per fn-owner-io call at 1000 articles, two calls per POST, linear
; in the store; about 9 s per call extrapolated to 100k).  The guard cannot
; be narrowed: every fn-sf step is (if (mbe :logic (fn-sf-statep s) :exec t)
; STEP s), which forces fn-sf-statep into every guard above it
; (planning/design/sf-statep-idiom-2026-10-03.md).  D40's raw dispatch is the
; way to skip it -- the guard-verified definition runs where its guard holds
; -- and needs a carried invariant that implies the guard and that every
; writer of the carried state preserves.
;
; WHAT IS PROVED.  fn-owner-retain-statep (books/owner-retain-transitions.lisp)
; implies each such guard (fn-owner-retain-statep-implies-entry-guard); it is
; established at the recovery install under A-RECOVERED-OPEN (the pilot row
; fn-owner-retain-carried, books/owner-retain-carried.lisp, whose open this
; row repeats verbatim and def-carried re-checks); and it is preserved by the
; thirteen writers listed as :transitions below: STAGE-5B's tier A
; (host/owner-retain-host.lisp, frozen at f98e1ff1b) and the pilot's three
; prepares.  def-carried generates each NAME-FN-carries statement from the
; world and proves it from the named theorem.
;
; WHAT IS ASSUMED: A-OWNER-INVARIANT-CARRIED (specs/failures.md).  The carried
; state is the whole ACL2 state, so every host-called entry that returns
; state is a writer of it, and def-carried's completeness demands a
; preservation theorem for each.  The ones not yet proved are the :incomplete
; owed list below: the escape names them one by one, so a writer added later
; is refused at image build until it is proved or owed here, and a proved one
; must leave the list.  Most of them never write 'fn-owner or
; 'fn-owner-retain-carry (the only globals the relation reads), but
; 237 of them are :program and can carry no theorem at all; the
; carrier move (STAGE-5B, lane/stage-5b-carrier: the owner's state in its
; own stobj, so only its writers return it) is the principled replacement.
; Each owed writer is a ledger item (planning/repair, category proof-owed).
;
; WHAT USES IT.  The entries host/interfaces.lisp declares
; `:raw-with (:carried fn-owner-served-carried :assuming
; A-OWNER-INVARIANT-CARRIED)'; books/definterface.lisp refuses that
; annotation unless the entry is a listed transition here and the assumption
; is the one this row names, and host/native/io.lisp prints each such entry
; at image build.  The developer selector FN_NATIVE_DISPATCH_COUNTERPART=1
; keeps the counterpart path (the whole guard evaluated) for comparison.
;
; Loaded by host/native/build.lisp after every ACL2-mode host file (the owed
; writers are defined by then) and before host/interfaces.lisp.

(in-package "ACL2")
(include-book "../books/definterface") ; def-carried, with the :incomplete escape
(include-book "../books/owner-retain-carried") ; the pilot row and its open

(def-carried fn-owner-served-carried
  :invariant fn-owner-retain-statep
  ; the pilot's open, verbatim (books/owner-retain-carried.lisp)
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
                           (fn-owner-retain-witness-state))))
  :transitions (; the pilot's (books/owner-retain-carried.lisp)
                (fn-owner-prepare-identity fn-owner-prepare-identity-preserves-retain-state)
                (fn-owner-prepare-consumer fn-owner-prepare-consumer-preserves-retain-state)
                (fn-owner-prepare-topic fn-owner-prepare-topic-preserves-retain-state)
                ; STAGE-5B tier A (host/owner-retain-host.lisp)
                (fn-owner-io fn-owner-io-preserves-retain-state)
                (fn-owner-take fn-owner-take-preserves-retain-state)
                (fn-owner-control-submit fn-owner-control-submit-preserves-retain-state)
                (fn-owner-prepare-retention fn-owner-prepare-retention-preserves-retain-state)
                (fn-owner-install-effects fn-owner-install-effects-preserves-retain-state)
                (fn-owner-close fn-owner-close-preserves-retain-state)
                (fn-owner-fault fn-owner-fault-preserves-retain-state)
                (fn-owner-open-peer fn-owner-open-peer-preserves-retain-state)
                (fn-owner-install-node-secret fn-owner-install-node-secret-preserves-retain-state)
                (fn-owner-apply-limit-profile fn-owner-apply-limit-profile-preserves-retain-state))
  :concludes ((fn-sn-statep fn-owner-retain-statep-implies-entry-guard)
              (fn-prc-carryp fn-owner-retain-statep-implies-entry-guard))
  :incomplete (A-OWNER-INVARIANT-CARRIED
               (OWED-LIST-PLACEHOLDER))
  :trace nil)
