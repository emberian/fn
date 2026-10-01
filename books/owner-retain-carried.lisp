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
; `fn-carried', and -- the transition theorem has the trace shape -- the
; trace theorem `fn-owner-retain-carried-run-carries': along every sequence
; of the listed transitions from a state satisfying the relation, the
; relation holds, by functional instantiation of fn-cd-run-carries.
;
; What this book does NOT claim.  The writers of the carried state are
; `fn-owner-install-ocfg' and `fn-owner-retain-carry-put'; every host-called
; entry whose definition reaches one of them owes a preservation theorem,
; and the completeness check that demands it reads the `fn-interfaces'
; table, which is complete only in the image world (host/interfaces.lisp).
; In this book's world that table holds no owner entry, so the check is
; vacuous here; `(def-carried-check fn-owner-retain-carried)' in the image
; world names the first owed entry (fn-owner-finish-synced, whose carry
; half fn-owner-finish-synced-preserves-retain-carry exists while its
; fn-lgoc-invariantp half does not; then fn-owner-io, -begin, -step, ...:
; the COVERAGE rows of books/owner-host-relation.lisp restated over the
; host subject).  That list is the stage-5 work of
; planning/design-store-representation-2026-10-01.md; this row is where
; each theorem is named as it lands, and `:raw-with (:carried
; fn-owner-retain-carried)' on an entry is refused until its row exists.
;
; Nothing changes for dependents: this book adds a row and the trace
; theorem over functions owner-recovery-retain already defines; it redefines
; nothing and leaves every included theorem's statement as it was.

(in-package "ACL2")
(include-book "def-carried")
(include-book "owner-recovery-retain")

(def-carried fn-owner-retain-carried
  :invariant fn-owner-retain-statep
  :established ((fn-owner-install-extended
                 fn-owner-install-extended-establishes-retain-state))
  :transitions ((fn-owner-prepare-identity
                 fn-owner-prepare-identity-preserves-retain-state))
  :concludes ((fn-sn-statep fn-owner-retain-statep-implies-entry-guard)
              (fn-prc-carryp fn-owner-retain-statep-implies-entry-guard))
  :writers (fn-owner-install-ocfg fn-owner-retain-carry-put)
  :trace t)

; The row's D40 data for the one transition: the bridges, the open, its own.
(assert-event
 (equal (fn-cd-raw-with 'fn-owner-retain-carried 'fn-owner-prepare-identity (w state))
        '(fn-owner-retain-statep-implies-entry-guard
          fn-owner-retain-statep-implies-entry-guard
          fn-owner-install-extended-establishes-retain-state
          fn-owner-prepare-identity-preserves-retain-state)))

(in-theory (disable fn-owner-retain-carried-step fn-owner-retain-carried-okp
                    fn-owner-retain-carried-run fn-owner-retain-carried-run-okp))
