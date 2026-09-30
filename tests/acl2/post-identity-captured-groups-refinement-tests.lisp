(in-package "ACL2")
(include-book "../../books/post-identity-captured-groups-refinement")
(include-book "post-identity-captured-tests")

; All positives reach group entry from actual mandatory binding-gated begin,
; using the existing one-transition fixture. Provider grants are literal.
(defun pic-gt-until (c fuel)
 (declare (xargs :measure (nfix fuel) :verify-guards nil))
 (if (or (zp fuel) (equal (fn-pic-get phase c) :done)
         (and (equal (fn-pic-get phase c) :compare-incoming)
              (equal (fn-pic-demand c) :control))) c
   (pic-gt-until (pic-test-drive c '(65 66 67) '(65 66 67) 1) (1- fuel))))
(defun pic-gt-before (left right)
 (declare (xargs :verify-guards nil))
 (pic-gt-until (pic-test-begin left right) 1000))
(defun-nx pic-gt-start (left right)
 (declare (xargs :stobjs nil :verify-guards nil))
 (mv-nth 1 (fn-pic-next (pic-gt-before left right) 1 '(65 66 67))))

(defthm pic-gt-entry-positive
 (let* ((c (pic-gt-before '("g") '("g")))
        (next (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (fn-pic-string-listp (fn-pic-get groups c))
       (fn-pic-string-listp (fn-record-groups (fn-pic-get held c)))
       (member-eq (fn-pic-get phase c) '(:compare-incoming :digest-compare))
       (equal (fn-pic-get phase next) :groups)
       (fn-pic-group-productp next)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable pic-gt-start fn-pic-group-productp))))
(defthm pic-gt-step-positive-resumption
 (let* ((c (pic-gt-start '("g") '("g")))
        (next (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (fn-pic-group-productp c) (equal (fn-pic-get incoming-n c) (len '(65 66 67)))
       (fn-pic-group-outcomep next) (fn-pic-group-productp next)
       (equal (fn-pic-at 3 (fn-pic-get group-cursor next)) 1)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable pic-gt-start fn-pic-group-productp fn-pic-group-outcomep))))
(defthm pic-gt-step-positive-duplicate
 (let* ((c (pic-gt-start nil nil))
        (next (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (fn-pic-group-productp c) (equal (fn-pic-get incoming-n c) (len '(65 66 67)))
       (fn-pic-group-outcomep next)
       (equal (fn-pic-get phase next) :done) (equal (fn-pic-get result next) :duplicate)
       (equal (fn-pic-get groups next) (fn-record-groups (fn-pic-get held next)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable pic-gt-start fn-pic-group-productp fn-pic-group-outcomep))))
(defthm pic-gt-step-positive-conflict
 (let* ((c (pic-gt-start '("g") '("h")))
        (next (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (fn-pic-group-productp c) (equal (fn-pic-get incoming-n c) (len '(65 66 67)))
       (fn-pic-group-outcomep next)
       (equal (fn-pic-get phase next) :done) (equal (fn-pic-get result next) :conflict)
       (not (equal (fn-pic-get groups next) (fn-record-groups (fn-pic-get held next))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable pic-gt-start fn-pic-group-productp fn-pic-group-outcomep))))
; Carried-product removal: skipped corrupt cursor falsely confirms unequal
; original groups, while incoming extent remains exact.
(defthm pic-gt-step-product-removal-corrupted-cursor
 (let* ((c (fn-pic-set group-cursor (fn-pic-groups-begin nil nil)
              (pic-gt-start '("g") '("h"))))
        (next (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (not (fn-pic-group-productp c))
       (equal (fn-pic-get incoming-n c) (len '(65 66 67)))
       (not (fn-pic-group-outcomep next))
       (equal (fn-pic-get result next) :duplicate)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable pic-gt-start fn-pic-group-productp fn-pic-group-outcomep))))
; Extent removal: correct group product, stale incoming extent refuses.
(defthm pic-gt-step-extent-removal-mutated-source
 (let* ((c (fn-pic-set incoming-n 4 (pic-gt-start nil nil)))
        (next (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (fn-pic-group-productp c)
       (not (equal (fn-pic-get incoming-n c) (len '(65 66 67))))
       (not (fn-pic-group-outcomep next))
       (equal (fn-pic-get result next) :refused)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable pic-gt-start fn-pic-group-productp fn-pic-group-outcomep))))
; Entry left-type removal: right type and phase retained, corrupt incoming
; group list creates an invalid cursor instead of an exact carried product.
(defthm pic-gt-entry-left-removal-corrupted-groups
 (let* ((c (fn-pic-set groups '(9) (pic-gt-before '("g") '("g"))))
        (next (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (not (fn-pic-string-listp (fn-pic-get groups c)))
       (fn-pic-string-listp (fn-record-groups (fn-pic-get held c)))
       (member-eq (fn-pic-get phase c) '(:compare-incoming :digest-compare))
       (equal (fn-pic-get phase next) :groups) (not (fn-pic-group-productp next))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-group-productp))))
; Entry right-type removal: incoming type and phase retained; corrupt retained
; held groups. This is a logical corruption, not an authorized provider row.
(defthm pic-gt-entry-right-removal-corrupted-held-groups
 (let* ((before (pic-gt-before '("g") '("g")))
        (c (fn-pic-set held (update-nth 5 '(9) (fn-pic-get held before)) before))
        (next (mv-nth 1 (fn-pic-next c 1 '(65 66 67)))))
  (and (fn-pic-string-listp (fn-pic-get groups c))
       (not (fn-pic-string-listp (fn-record-groups (fn-pic-get held c))))
       (member-eq (fn-pic-get phase c) '(:compare-incoming :digest-compare))
       (equal (fn-pic-get phase next) :groups) (not (fn-pic-group-productp next))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pic-group-productp))))
; Entry phase removal: both proper original group lists remain, but an
; already-corrupt group continuation is not reestablished at zero fuel.
(defthm pic-gt-entry-phase-removal-corrupted-existing-cursor
 (let* ((c (fn-pic-set group-cursor (fn-pic-groups-begin nil nil)
              (pic-gt-start '("g") '("h"))))
        (next (mv-nth 1 (fn-pic-next c 0 '(65 66 67)))))
  (and (fn-pic-string-listp (fn-pic-get groups c))
       (fn-pic-string-listp (fn-record-groups (fn-pic-get held c)))
       (not (member-eq (fn-pic-get phase c) '(:compare-incoming :digest-compare)))
       (equal (fn-pic-get phase next) :groups) (not (fn-pic-group-productp next))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable pic-gt-start fn-pic-group-productp))))
