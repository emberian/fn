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
; What this book does NOT claim.  The install establishes the relation
; only under two premises its guard does not say, declared as :hyps, so the
; row backs NO raw dispatch (fn-cd-raw-problem).  They are not alike.
; (fn-onb-open-okp (fn-ocfg-owner oc)) the install itself CHECKS, refusing
; :article-numbers-damaged otherwise: it is a premise only because the
; generated establishment has no verdict condition (an open that refuses
; establishes nothing on its refusal arm).  (fn-lgoc-invariantp oc) no host
; check can supply and no guard may evaluate (fn-cst-relation compares the
; node to the replay of every event: an open from a checkpoint must not
; re-walk the history, planning/design-store-representation-2026-10-01.md);
; it is DISCHARGED BY THEOREM for the owner the host's open produces,
; fn-lgoc-recover-installs-invariant (books/owner-log-ocl.lisp) over
; fn-ock-install of the Store open's pair
; (fn-ock-install-of-store-open-by-definition), under the one premise the
; whole recovery rests on: the decoded checkpoint is a capture of a prefix
; of the history the log continues (the recovery-refinement subject,
; PRF-1212/1216).  Raw dispatch over this row therefore waits on def-carried
; saying both honestly -- an establishment conditioned on the open's
; success word, and a premise discharged by a named producer keystone under
; named assumptions -- and on the recovery refinement admitting the store
; instance; neither is a :hyps the host does not check.  The carried state is the ACL2
; state, so every host-called entry that RETURNS state owes a preservation
; theorem; the completeness check that demands it reads the `fn-interfaces'
; table, which is complete only in the image world (host/interfaces.lisp).
; In this book's world that table holds no owner entry, so the check is
; vacuous here; `(def-carried-check fn-owner-retain-carried)' in the image
; world names the first owed entry (fn-owner-finish-synced, then
; fn-owner-io, -begin, -step, ...: the COVERAGE rows of
; books/owner-host-relation.lisp restated over the host subject).  That
; list is the stage-5 work of
; planning/design-store-representation-2026-10-01.md.

; Nothing changes for dependents: this book adds a row and the trace
; theorem over functions owner-recovery-retain already defines; it redefines
; nothing and leaves every included theorem's statement as it was.

(in-package "ACL2")
(include-book "def-carried")
(include-book "owner-recovery-retain")

(def-carried fn-owner-retain-carried
  :invariant fn-owner-retain-statep
  :established ((fn-owner-install-extended
                 fn-owner-install-extended-establishes-retain-state
                 :hyps ((fn-onb-open-okp (fn-ocfg-owner oc))
                        (fn-lgoc-invariantp oc))))
  :transitions ((fn-owner-prepare-identity
                 fn-owner-prepare-identity-preserves-retain-state))
  :concludes ((fn-sn-statep fn-owner-retain-statep-implies-entry-guard)
              (fn-prc-carryp fn-owner-retain-statep-implies-entry-guard)))

; The row's D40 data for the one transition: only generated names.
(assert-event
 (equal (fn-cd-raw-with 'fn-owner-retain-carried 'fn-owner-prepare-identity (w state))
        '(fn-owner-retain-carried-fn-owner-prepare-identity-carries
          fn-owner-retain-carried-fn-sn-statep-bridge
          fn-owner-retain-carried-fn-prc-carryp-bridge)))

; The open's establishment assumes what the host does not check (the
; configured owner opens and satisfies fn-lgoc-invariantp), so the row backs
; no raw dispatch until that premise is the open's guard.
(assert-event
 (fn-cd-raw-problem 'fn-owner-retain-carried 'fn-owner-prepare-identity (w state)))

(in-theory (disable fn-owner-retain-carried-step fn-owner-retain-carried-okp
                    fn-owner-retain-carried-run fn-owner-retain-carried-run-okp))
