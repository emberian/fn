; Guarded internal bounded cursor source; not an installed terminal authority.
(in-package "ACL2")
(include-book "page-read-ledger")

; Cursor12 retains original rows and immutable root through every phase.
(defun fn-prwt-cursor (token revision original remaining prefix rebuilt found
                            phase root intent receipt)
  (declare (xargs :guard t))
  (list :window-terminal token revision original remaining prefix rebuilt
        found phase root intent receipt))

(defun fn-prwt-start (root revision rows)
  (declare (xargs :guard t))
  (fn-prwt-cursor (fn-prl-nth 1 root) revision rows rows nil nil nil
                  :scan root nil nil))

; One step has at most one row/token comparison or one reconstruction cons.
; Token equality has a fixed9/11-cell source representation under caller carry.
; This internal operation does not validate arbitrary graph-shaped tokens.
(defun fn-prwt-one (cursor)
  (declare (xargs :guard t))
  (let* ((token (fn-prl-nth 1 cursor))
         (revision (fn-prl-nth 2 cursor))
         (original (fn-prl-nth 3 cursor))
         (remaining (fn-prl-nth 4 cursor))
         (prefix (fn-prl-nth 5 cursor))
         (rebuilt (fn-prl-nth 6 cursor))
         (found (fn-prl-nth 7 cursor))
         (phase (fn-prl-nth 8 cursor))
         (root (fn-prl-nth 9 cursor))
         (intent (fn-prl-nth 10 cursor))
         (receipt (fn-prl-nth 11 cursor)))
    (cond
     ((eq phase :scan)
      (cond
       ((consp remaining)
        (let* ((row (car remaining))
               (match (equal (fn-prl-nth 0 row) token)))
          (fn-prwt-cursor token revision original (cdr remaining)
                          (if match prefix (cons row prefix)) rebuilt
                          (if (and match (not found)) row found)
                          :scan root intent receipt)))
       (remaining cursor)
       (t (fn-prwt-cursor token revision original nil prefix rebuilt found
                          :rebuild root intent receipt))))
     ((eq phase :rebuild)
      (cond
       ((consp prefix)
        (fn-prwt-cursor token revision original remaining (cdr prefix)
                        (cons (car prefix) rebuilt) found :rebuild
                        root intent receipt))
       (prefix cursor)
       (t (fn-prwt-cursor token revision original remaining nil rebuilt found
                          :commit-ready root intent receipt))))
     (t cursor))))

; Fuel alone is work, not allocation authority. The actual indexed caller must
; obtain a fresh installed ATS BODY allowance before invoking this function.
(defun fn-prwt-run (cursor fuel)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel)
          (not (member-eq (fn-prl-nth 8 cursor) '(:scan :rebuild))))
      (mv cursor fuel)
    (fn-prwt-run (fn-prwt-one cursor) (- fuel 1))))

; SOURCE ghost: remaining/reverse/rebuilt/original graphs are retained, not
; reclaimed by a pointer drop. No output-size-as-allocation substitution.
; Per work step constructs cursor12 and at most one cons. Final indexed store
; additionally rebuilds fixed context10/custody12 wrappers; the actor and ATS
; call/condition/primitive census are still required, so 13 is not a byte grant.
;
; Deliberately no release/receipt constructor or supplied JOINED parameter.
; Actual slot executor must fetch CURRENT qs-inputsi itself, detect context9 as
; unavailable, validate full query token/registered slot, and retain cursor in
; custody field11. Commit needs status-returning DATA6 publisher plus actual
; epilogue observation, scalar revision check and latest C/NEXT. Uninstalled.

; The actual bounded scanner preserves every captured authority reference.
; This frame does not establish return, alias settlement or release.
(defthm fn-prwt-one-retains-captured-authority
 (let ((next (fn-prwt-one cursor)))
  (and (equal (fn-prl-nth 1 next) (fn-prl-nth 1 cursor))
       (equal (fn-prl-nth 2 next) (fn-prl-nth 2 cursor))
       (equal (fn-prl-nth 3 next) (fn-prl-nth 3 cursor))
       (equal (fn-prl-nth 9 next) (fn-prl-nth 9 cursor))
       (equal (fn-prl-nth 10 next) (fn-prl-nth 10 cursor))
       (equal (fn-prl-nth 11 next) (fn-prl-nth 11 cursor))))
 :hints (("Goal" :in-theory (enable fn-prwt-one fn-prwt-cursor fn-prl-nth))))

(defthm fn-prwt-run-retains-captured-authority
 (let ((next (mv-nth 0 (fn-prwt-run cursor fuel))))
  (and (equal (fn-prl-nth 1 next) (fn-prl-nth 1 cursor))
       (equal (fn-prl-nth 2 next) (fn-prl-nth 2 cursor))
       (equal (fn-prl-nth 3 next) (fn-prl-nth 3 cursor))
       (equal (fn-prl-nth 9 next) (fn-prl-nth 9 cursor))
       (equal (fn-prl-nth 10 next) (fn-prl-nth 10 cursor))
       (equal (fn-prl-nth 11 next) (fn-prl-nth 11 cursor))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-prwt-run cursor fuel)
                  :in-theory (e/d (fn-prwt-run) (fn-prwt-one fn-prl-nth)))))
