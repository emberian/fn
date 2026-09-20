; fn: the authority outcome -- "accepted, authority refused" as its own word.
;
; specs/substrate-transport.md section 2.3 and SUB-004.  This is the one
; place the index and the policy gate meet, and it is a separate book so
; that neither cluster depends on the other.

(in-package "ACL2")
(include-book "stx-policy")
(include-book "stx-index")

; -----------------------------------------------------------------------------
; "Accepted, authority refused" is a distinct outcome (D13, SUB-004)
;
; specs/substrate-transport.md section 2.3 proposed adding :equivocation and
; :authority-equivocation to *fn-peer-reasons*.  This book does NOT do that,
; and the departure is a strengthening rather than a weakening: every member
; of *fn-peer-reasons* is a reason a transit DECISION refuses bytes, and an
; equivocating article must be accepted -- refusing it would let a hostile
; peer delete content by replaying a fork and would destroy the evidence of
; the fork.  Putting the two reasons in that enumeration would make
; "refuse :equivocation" a well-typed transit decision, which is exactly the
; sentence the spine forbids.  They live in their own enumeration, on the
; authority axis, and the transit decision cannot spell them.

(defconst *fn-stx-authority-outcomes*
  '(:admitted :refused :equivocation :authority-equivocation))

(defun fn-stx-records-creator-scan (rs p)
  (declare (xargs :guard t))
  (if (consp rs)
      (or (equal (fn-stx-record-creator (car rs)) p)
          (fn-stx-records-creator-scan (cdr rs) p))
    nil))

(defun fn-stx-authority-forkedp (index authority)
  (declare (xargs :guard t))
  (if (fn-stx-records-creator-scan (fn-stx-index-records index) authority) t nil))

(defun fn-stx-authority-outcome (index node article keyring group authority)
  (declare (xargs :guard (and (fn-article-syntax-p article)
                              (fn-prin-keyringp keyring))))
  (let ((s (fn-stx-statement-of article)))
    (cond ((and s (fn-stx-index-equivocatorp index (fn-stmt-creator s)
                                             (fn-stmt-incarnation s)))
           :equivocation)
          ((fn-stx-authority-forkedp index authority) :authority-equivocation)
          ((fn-stx-transit-authority-ok node article keyring group authority)
           :admitted)
          (t :refused))))

(defthm fn-stx-authority-outcome-is-typed
  (member-equal (fn-stx-authority-outcome index node article keyring group
                                          authority)
                *fn-stx-authority-outcomes*))

; The creator has forked this slot: the statement carries no authority, and
; the outcome says so in its own word rather than in the word a refused
; transfer would use.
(defthm fn-stx-equivocating-creator-is-never-admitted
  (implies (and (fn-stx-statement-of article)
                (fn-stx-index-equivocatorp
                 index
                 (fn-stmt-creator (fn-stx-statement-of article))
                 (fn-stmt-incarnation (fn-stx-statement-of article))))
           (equal (fn-stx-authority-outcome index node article keyring group
                                            authority)
                  :equivocation)))

; The group authority has forked: fn-pol-current is nil and the group admits
; nothing until a later unforked policy, which is already fn-pol-current-s
; behaviour; the outcome names it rather than reporting a bare refusal.
(defthm fn-stx-forked-authority-is-its-own-outcome
  (implies (and (fn-stx-authority-forkedp index authority)
                (not (and (fn-stx-statement-of article)
                          (fn-stx-index-equivocatorp
                           index
                           (fn-stmt-creator (fn-stx-statement-of article))
                           (fn-stmt-incarnation (fn-stx-statement-of article))))))
           (equal (fn-stx-authority-outcome index node article keyring group
                                            authority)
                  :authority-equivocation)))


; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).

(in-theory (disable (:d fn-stx-records-creator-scan)
                    (:d fn-stx-authority-forkedp)
                    (:d fn-stx-authority-outcome)))
