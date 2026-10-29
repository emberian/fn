; Run via fn2/tools/certify.sh --export-owed after the unit books certify.
; Certified unit books validate the exact functions recorded in the world.
(in-package "ACL2")
(set-cbd "../../")
(include-book "fn2/tests/owed-unit")
(include-book "fn2/tests/pool-unit")
(include-book "fn2/tests/vocab-unit")
(include-book "fn2/tests/core-unit")
(include-book "fn2/tests/sched-unit")
(include-book "fn2/tests/executor-unit")
(include-book "fn2/tests/reference-unit")
; Layer B's unit books (registered by the B seat; include-only).
(include-book "fn2/tests/alloc-unit")
(include-book "fn2/tests/crash-model-unit")
(include-book "fn2/tests/log-model-unit")
(include-book "fn2/tests/blake3-unit")
(include-book "fn2/tests/merkle-unit")
(include-book "fn2/tests/format-check-unit")
(include-book "fn2/tests/layout-teeth-unit")

(defun fn2-owed-write-term (term channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (mv-let (col state) (fmt1 "~x0" (list (cons #\0 term)) 0 channel state nil)
    (declare (ignore col)) state))
(defun fn2-owed-write-entries (entries channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (if (atom entries) state
    (let* ((name (caar entries)) (row (cdar entries))
           (state (princ$ "| `" channel state))
           (state (prin1$ name channel state))
           (state (princ$ "` | " channel state))
           (state (prin1$ (car (fn2-decl-get :proof row)) channel state))
           (state (princ$ " | " channel state))
           (state (prin1$ (fn2-decl-get :schema row) channel state))
           (state (princ$ " | `" channel state))
           (state (fn2-owed-write-term (cadr (member-eq :formula row)) channel state))
           (state (princ$ "` | `" channel state))
           (state (fn2-owed-write-term (cadr (member-eq :teeth row)) channel state))
           (state (princ$ "` | " channel state))
           (state (princ$ (cadr (member-eq :doc row)) channel state))
           (state (princ$ " | `" channel state))
           (state (fn2-owed-write-term (fn2-decl-get :checks row) channel state))
           (state (princ$ "` | `" channel state))
           (state (fn2-owed-write-term (fn2-decl-get :shared row) channel state))
           (state (princ$ "` | `" channel state))
           (state (fn2-owed-write-term (fn2-decl-get :claim row) channel state))
           (state (princ$ "` | `" channel state))
           (state (fn2-owed-write-term (fn2-decl-get :contract row) channel state))
           (state (princ$ "` | `" channel state))
           (state (fn2-owed-write-term (fn2-decl-get :shared-handler-mutation row) channel state))
           (state (princ$ "` |
" channel state)))
      (fn2-owed-write-entries (cdr entries) channel state))))


(defun fn2-owed-write-counts (rows channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (let* ((counts (fn2-square-counts rows))
         (state (princ$ "Requirements: " channel state))
         (state (prin1$ (nth 0 counts) channel state))
         (state (princ$ "; bound statements: " channel state))
         (state (prin1$ (nth 1 counts) channel state))
         (state (princ$ "; admitted proofs: " channel state))
         (state (prin1$ (nth 2 counts) channel state))
         (state (princ$ "; check coverage: " channel state))
         (state (prin1$ (nth 3 counts) channel state)))
    (princ$ " rows with a passing, exercised check.

" channel state)))
(defun fn2-owed-write-groups (groups rows channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (if (atom groups) state
    (let* ((group (car groups)) (members (fn2-square-group-rows group rows))
           (state (princ$ "### Case source / schema: `" channel state))
           (state (fn2-owed-write-term (cdr group) channel state))
           (state (princ$ "`

" channel state))
           (state (fn2-owed-write-counts members channel state))
           (state (princ$ "| Name | Status | Schema | Exact statement | Evaluating functions | Description | Check scope | Shared declarations | Claim | Contract | Shared-handler mutation control |
|---|---|---|---|---|---|---|---|---|---|---|
" channel state))
           (state (fn2-owed-write-entries (fn2-square-owed-rows members) channel state))
           (state (if (consp (cdr groups)) (princ$ "
" channel state) state)))
      (fn2-owed-write-groups (cdr groups) rows channel state))))

(defun fn2-owed-owner-rows (owner rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (if (equal owner (fn2-decl-get :owner (cdar rows)))
        (cons (car rows) (fn2-owed-owner-rows owner (cdr rows)))
      (fn2-owed-owner-rows owner (cdr rows)))))
(defun fn2-owed-write-owners (owners rows channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (if (atom owners) state
    (let* ((members (fn2-owed-owner-rows (car owners) rows))
           (state (princ$ "## Correspondence / owner: `" channel state))
           (state (fn2-owed-write-term (car owners) channel state))
           (state (princ$ "`

" channel state))
           (state (fn2-owed-write-counts members channel state))
           (state (fn2-owed-write-groups
                    (remove-duplicates-equal (fn2-square-groups members)) members channel state))
           (state (if (consp (cdr owners)) (princ$ "
" channel state) state)))
      (fn2-owed-write-owners (cdr owners) rows channel state))))

; Ordinary I/O, never a certifying event. Also used by the scoped export control.
(defun fn2-owed-export (path rows state)
  (declare (xargs :stobjs state :verify-guards nil))
  (mv-let (channel state) (open-output-channel path :character state)
    (if (not channel)
        (prog2$ (er hard 'fn2-owed-export "Cannot write ~x0." path) state)
      (let* ((state (princ$ "# Recorded obligations

Generated from the ACL2 `fn2-squares` world table by
`fn2/tools/certify.sh --export-owed` after certifying the unit books.
Do not edit this file; change the registrations and regenerate it.
Proof and check evidence are separate: checked rows remain owed. Teeth are
named evaluators, not admitted proofs or scoped check records. Check coverage
counts rows with a passing record and positive exercised count; the full scope
is printed beside each owed row. Unbound requirements have no statement.
Counts are grouped by owner (correspondence when present), case source, and schema.
Cases are proof obligations, not independent semantic guarantees. Turn composition
is listed under the same correspondence as its cases; no case catalogue is bound
until its contract exists. NIL case source means a hand-stated requirement.

" channel state))
             (state (fn2-owed-write-counts rows channel state))
             (state (fn2-owed-write-owners
                      (remove-duplicates-equal (strip-cars (fn2-square-groups rows))) rows channel state)))
        (close-output-channel channel state)))))
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(fn2-owed-export "fn2/docs/OWED.md" (fn2-decl-rows :square (w state)) state)
(value-triple (cw "FN2-OWED-EXPORT PASS~%"))
