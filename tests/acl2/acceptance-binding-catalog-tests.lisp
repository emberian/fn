; Whole-row lookup through the concrete catalog, not an acceptance projection.
(in-package "ACL2")
(include-book "../../books/acceptance-binding-catalog")

(defconst *abct-r0*
  (fn-held-plain (fn-record-make 0 1 1 "<a@x>" '(65) '("g") "o" "s" "old" 1 10) 0))
(defconst *abct-r1*
  (fn-held-plain (fn-record-make 1 2 2 "<b@x>" '(66) '("g") "o2" "s2" "other" 1 11) 1))
; Multiple rows for one key exercise last-visible selection; production's
; acceptance invariant disallows a replacement, the catalog itself does not.
(defconst *abct-r2*
  (fn-held-plain (fn-record-make 2 3 3 "<a@x>" '(67) '("g") "o3" "s3" "new" 1 12) 2))
(defconst *abct-cat* (list *abct-r0* *abct-r1* *abct-r2*))

(assert-event
 (and (equal (fn-abc-row "<a@x>" 3 *abct-cat*)
             (fn-abc-find-row "<a@x>" (fn-cat-count *abct-cat*) 3 *abct-cat*))
      (equal (fn-abc-row "<a@x>" 3 *abct-cat*) *abct-r2*)
      (equal (fn-record-release-evidence (fn-abc-row "<a@x>" 3 *abct-cat*)) "new")
      (equal (fn-abc-row "<a@x>" 2 *abct-cat*) *abct-r0*)
      (equal (fn-abc-row "<missing@x>" 3 *abct-cat*) nil)))

(defun abct-run (fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-cat (fn-cat-commit *abct-r0* fn-cat))
         (fn-cat (fn-cat-commit *abct-r1* fn-cat))
         (fn-cat (fn-cat-commit *abct-r2* fn-cat))
         (before (and (equal (fn-abc-row "<a@x>" 3 fn-cat)
                            (fn-abc-find-row "<a@x>" (fn-cat-count fn-cat) 3 fn-cat))
                      (equal (fn-record-release-evidence (fn-abc-row "<a@x>" 3 fn-cat)) "new")
                      (equal (fn-record-release-evidence (fn-abc-row "<a@x>" 2 fn-cat)) "old")))
         (fn-cat (fn-cat-withdraw 2 9 fn-cat)))
    (mv (and before
             (equal (fn-record-release-evidence (fn-abc-row "<a@x>" 3 fn-cat)) "new")
             (equal (fn-record-release-evidence (fn-abc-row "<a@x>" 4 fn-cat)) "old")
             (equal (fn-abc-row "<a@x>" 4 fn-cat)
                    (fn-abc-find-row "<a@x>" (fn-cat-count fn-cat) 4 fn-cat))) fn-cat)))
(defun abct-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat
    (mv-let (ok fn-cat) (abct-run fn-cat) ok)))
(assert-event (abct-exec))
(assert-event (eq (symbol-class 'fn-abc-row (w state)) :common-lisp-compliant))
