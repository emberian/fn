; fn acceptance primitives: total executable helpers, primitive domains, and
; the local-number watermark allocator.
;
; Split from acceptance.lisp at its seam in the 2026-09-19 realignment.
; acceptance.lisp includes this book and keeps the records, the state
; recognizer and the transitions.  This book models no bytes-on-disk,
; network, or cryptography.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Total executable helpers.
;
; Raw Common Lisp CAR/CDR and list primitives have narrower domains than
; ACL2's total logic.  Each helper IS its logical primitive: the :logic branch
; is the primitive and the :exec branch reproduces its value on atoms and
; dotted lists without leaving the raw primitive's domain.  There is no
; `fn-ag-car-is-car' twin to export; opening the definition is the equality.

(defun fn-ag-car (x)
  (declare (xargs :guard t))
  (mbe :logic (car x)
       :exec (if (consp x) (car x) nil)))

(defun fn-ag-cdr (x)
  (declare (xargs :guard t))
  (mbe :logic (cdr x)
       :exec (if (consp x) (cdr x) nil)))

(defun fn-ag-member (x xs)
  (declare (xargs :guard t))
  (mbe :logic (member-equal x xs)
       :exec (if (consp xs)
                 (if (equal x (car xs)) xs (fn-ag-member x (cdr xs)))
               nil)))

; `fn-ag-append''s executable was a cons around a recursive call, one
; control-stack frame per element of XS: an ARTICLE reply for a 3 MiB article
; exhausted the image's stack inside `fn-owner-chunk' (large-article,
; 2026-09-25).  The twin copies XS once onto an accumulator in a tail call
; and reverses it onto YS with `revappend', which is iterative; it allocates
; 2|XS| conses and a constant stack, and accepts any XS as `append' does
; (a non-list tail is dropped).
(defun fn-ag-rev-onto (xs acc)
  (declare (xargs :guard t))
  (if (consp xs)
      (fn-ag-rev-onto (cdr xs) (cons (car xs) acc))
    acc))

(defthm fn-ag-rev-onto-true-listp
  (implies (true-listp acc)
           (true-listp (fn-ag-rev-onto xs acc))))

(local
 (defthm fn-ag-revappend-of-rev-onto
   (equal (revappend (fn-ag-rev-onto xs acc) ys)
          (revappend acc (append xs ys)))))

(defun fn-ag-append-exec (xs ys)
  (declare (xargs :guard t))
  (revappend (fn-ag-rev-onto xs nil) ys))

; Keystone (D27 concrete twin): the iterative append is `append' on every
; argument.
(defthm fn-ag-append-exec-is-append
  (equal (fn-ag-append-exec xs ys)
         (append xs ys)))

(defun fn-ag-append (xs ys)
  (declare (xargs :guard t))
  (mbe :logic (append xs ys)
       :exec (fn-ag-append-exec xs ys)))

(defun fn-ag-less (x y)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :use completion-of-<))))
  (mbe :logic (< x y)
       :exec (if (and (rationalp x) (rationalp y))
                 (< x y)
               (let ((x1 (if (acl2-numberp x) x 0))
                     (y1 (if (acl2-numberp y) y 0)))
                 (or (< (realpart x1) (realpart y1))
                     (and (equal (realpart x1) (realpart y1))
                          (< (imagpart x1) (imagpart y1))))))))

; Compatibility name for the one includer that cites the former twin theorem
; by :use (books/transfer.lisp).  It is the definition; it is not a rule.
(defthm fn-ag-less-is-less (equal (fn-ag-less x y) (< x y)) :rule-classes nil)

; -----------------------------------------------------------------------------
; Primitive domains and list helpers

(defun fn-octetp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (integerp x) (<= 0 x) (<= x 255)))

(verify-guards fn-octetp)

(defun fn-octet-listp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (fn-octetp (car xs))
           (fn-octet-listp (cdr xs)))
    (null xs)))

(verify-guards fn-octet-listp)

(defun fn-string-listp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (stringp (car xs))
           (fn-string-listp (cdr xs)))
    (null xs)))

(verify-guards fn-string-listp)

(defun fn-no-duplicatesp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp xs)
           (and (not (member-equal (car xs) (cdr xs)))
                (fn-no-duplicatesp (cdr xs)))
         t)
       :exec
       (if (consp xs)
           (and (not (fn-ag-member (fn-ag-car xs) (fn-ag-cdr xs)))
                (fn-no-duplicatesp (fn-ag-cdr xs)))
         t)))

(verify-guards fn-no-duplicatesp)

(defun fn-subsetp (xs ys)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp xs)
           (and (member-equal (car xs) ys)
                (fn-subsetp (cdr xs) ys))
         t)
       :exec
       (if (consp xs)
           (and (fn-ag-member (fn-ag-car xs) ys)
                (fn-subsetp (fn-ag-cdr xs) ys))
         t)))

(verify-guards fn-subsetp)

(defun fn-selection-validp (selection configured)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp selection)
       (fn-string-listp selection)
       (fn-no-duplicatesp selection)
       (fn-subsetp selection configured)))

(verify-guards fn-selection-validp)

(defun fn-fencedp (x)
  (declare (xargs :guard t :verify-guards nil))
  (or (null x) (equal x t)))

(verify-guards fn-fencedp)

; -----------------------------------------------------------------------------
; Local group watermarks and membership allocation

; A nexts list is kept in configured-group order.  Its entries are
; (group . next-number); numbers are allocated from the current watermark.
(defun fn-nexts-for-p (groups nexts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (and (consp nexts)
           (consp (car nexts))
           (equal (car (car nexts)) (car groups))
           (posp (cdr (car nexts)))
           (fn-nexts-for-p (cdr groups) (cdr nexts)))
    (null nexts)))

(verify-guards fn-nexts-for-p)

(defun fn-initial-nexts (groups)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (cons (cons (car groups) 1)
            (fn-initial-nexts (cdr groups)))
    nil))

(verify-guards fn-initial-nexts)

(defun fn-next-number (group nexts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp nexts)
           (if (equal group (car (car nexts)))
               (cdr (car nexts))
             (fn-next-number group (cdr nexts)))
         0)
       :exec
       (if (consp nexts)
           (if (equal group (fn-ag-car (fn-ag-car nexts)))
               (fn-ag-cdr (fn-ag-car nexts))
             (fn-next-number group (fn-ag-cdr nexts)))
         0)))

(verify-guards fn-next-number)

(defun fn-bump-number (group nexts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp nexts)
           (if (equal group (car (car nexts)))
               (cons (cons (car (car nexts))
                           (1+ (cdr (car nexts))))
                     (cdr nexts))
             (cons (car nexts)
                   (fn-bump-number group (cdr nexts))))
         nil)
       :exec
       (if (consp nexts)
           (if (equal group (fn-ag-car (fn-ag-car nexts)))
               (cons (cons (fn-ag-car (fn-ag-car nexts))
                           (1+ (fix (fn-ag-cdr (fn-ag-car nexts)))))
                     (fn-ag-cdr nexts))
             (cons (fn-ag-car nexts)
                   (fn-bump-number group (fn-ag-cdr nexts))))
         nil)))

(verify-guards fn-bump-number)

(defun fn-allocate-memberships (groups nexts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (cons (cons (car groups)
                  (fn-next-number (car groups) nexts))
            (fn-allocate-memberships
             (cdr groups)
             (fn-bump-number (car groups) nexts)))
    nil))

(verify-guards fn-allocate-memberships)

(defun fn-advance-nexts (groups nexts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (fn-advance-nexts (cdr groups)
                        (fn-bump-number (car groups) nexts))
    nexts))

(verify-guards fn-advance-nexts)

(defun fn-membership-listp (groups memberships)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (and (consp memberships)
           (consp (car memberships))
           (equal (car (car memberships)) (car groups))
           (posp (cdr (car memberships)))
           (fn-membership-listp (cdr groups) (cdr memberships)))
    (null memberships)))

(verify-guards fn-membership-listp)

(defun fn-memberships-at-watermarkp (memberships nexts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp memberships)
           (and (equal (cdr (car memberships))
                       (fn-next-number (car (car memberships)) nexts))
                (fn-memberships-at-watermarkp (cdr memberships) nexts))
         t)
       :exec
       (if (consp memberships)
           (and (equal (fn-ag-cdr (fn-ag-car memberships))
                       (fn-next-number (fn-ag-car (fn-ag-car memberships))
                                       nexts))
                (fn-memberships-at-watermarkp (fn-ag-cdr memberships) nexts))
         t)))

(verify-guards fn-memberships-at-watermarkp)

(defun fn-memberships-below-nextsp (memberships nexts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp memberships)
           (and (< (cdr (car memberships))
                   (fn-next-number (car (car memberships)) nexts))
                (fn-memberships-below-nextsp (cdr memberships) nexts))
         t)
       :exec
       (if (consp memberships)
           (and (fn-ag-less (fn-ag-cdr (fn-ag-car memberships))
                            (fn-next-number (fn-ag-car (fn-ag-car memberships))
                                            nexts))
                (fn-memberships-below-nextsp (fn-ag-cdr memberships) nexts))
         t)))

(verify-guards fn-memberships-below-nextsp)

(defthm fn-initial-nexts-are-valid
  (implies (fn-string-listp groups)
           (fn-nexts-for-p groups (fn-initial-nexts groups)))
  :hints (("Goal" :induct (fn-initial-nexts groups))))

; -----------------------------------------------------------------------------
; Export.  Everything here is list-recursive vocabulary that the books above
; induct on and open; nothing is a record.  The book withdraws nothing.
(in-theory (current-theory :here))
