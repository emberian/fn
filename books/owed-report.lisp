; The exporter and its focused controls use one implementation.
(in-package "ACL2")
(include-book "owed")

(defun fn2-owed-claim-term (row world)
 (declare (xargs :verify-guards nil))
 (fn2-decl-statement-body (fn2-decl-get :statement row) world))

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
           (state (if (consp (cdr (fn2-decl-get :proof row)))
                      (let* ((state (princ$ " `" channel state))
                             (state (prin1$ (cadr (fn2-decl-get :proof row)) channel state)))
                        (princ$ "`" channel state))
                    state))
           (state (princ$ " | " channel state))
           (state (prin1$ (fn2-decl-get :schema row) channel state))
           (state (princ$ " | `" channel state))
           ; :formula is author/display metadata, not a guarded binding.  The
           ; exact claim is the current statement function's translated body.
           (state (fn2-owed-write-term
                    (fn2-owed-claim-term row (w state))
                    channel state))
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
; Rows an admitted theorem discharges, listed after the owed rows with the theorem's name.
(defun fn2-owed-proved-rows (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (if (eq (car (fn2-decl-get :proof (cdar rows))) :proved)
        (cons (car rows) (fn2-owed-proved-rows (cdr rows)))
      (fn2-owed-proved-rows (cdr rows)))))
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
           (state (fn2-owed-write-entries (append (fn2-square-owed-rows members) (fn2-owed-proved-rows members))
                                          channel state))
           (state (if (consp (cdr groups)) (princ$ "
" channel state) state)))
      (fn2-owed-write-groups (cdr groups) rows channel state))))

; A correspondence's cases, split by whether a passing, exercised check
; record exists: the unexercised ones are listed, never folded into a count.
(defun fn2-owed-case-split (rows covered)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let ((case (fn2-decl-get :case (cdar rows))))
      (append (and case (iff covered (fn2-square-coveredp (fn2-decl-get :checks (cdar rows))))
                   (list case))
              (fn2-owed-case-split (cdr rows) covered)))))
(defun fn2-owed-write-cases (rows channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (let ((exercised (fn2-owed-case-split rows t)) (unexercised (fn2-owed-case-split rows nil)))
    (if (not (or exercised unexercised)) state
      (let* ((state (princ$ "Cases with a passing, exercised check (" channel state))
             (state (prin1$ (len exercised) channel state))
             (state (princ$ "): `" channel state))
             (state (fn2-owed-write-term exercised channel state))
             (state (princ$ "`

Cases without one (" channel state))
             (state (prin1$ (len unexercised) channel state))
             (state (princ$ "): `" channel state))
             (state (fn2-owed-write-term unexercised channel state)))
        (princ$ "`

" channel state)))))

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
           (state (fn2-owed-write-cases members channel state))
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
`tools/certify.sh --export-owed` after certifying the unit books.
Do not edit this file; change the registrations and regenerate it.
Proof and check evidence are separate: checked rows remain owed. Teeth are
named evaluators, not admitted proofs or scoped check records. Check coverage
counts rows with a passing record and positive exercised count; the full scope
is printed beside each owed row. Unbound requirements have no statement.
Counts are grouped by owner (correspondence when present), case source, and schema.
Cases are proof obligations, not independent semantic guarantees. Turn composition
is listed under the same correspondence as its cases; no case catalogue is bound
until its contract exists. NIL case source means a hand-stated requirement.
A row with an admitted proof is listed after its group's owed rows, with status
:PROVED and the name of the theorem that discharges its statement.

" channel state))
             (state (fn2-owed-write-counts rows channel state))
             (state (fn2-owed-write-owners
                      (remove-duplicates-equal (strip-cars (fn2-square-groups rows))) rows channel state)))
        (close-output-channel channel state)))))
