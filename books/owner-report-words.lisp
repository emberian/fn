; Literal public obligation report primitives.
(in-package "ACL2")
(include-book "native-live-status-words")
(include-book "owner-report-owner-accessors")
(include-book "owner-report-generated-accessors")

(local
 (defthm fn-orw-digits-listp
   (implies (true-listp acc) (true-listp (fn-nls-digits n acc)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (disable floor mod)))))
(defthm fn-orw-nat-listp
  (true-listp (fn-nls-nat n))
  :rule-classes :type-prescription)

(defun fn-nls-value (v)
  "A reported value: a word or a natural."
  (declare (xargs :guard t))
  (if (stringp v) (fn-nls-text v) (fn-nls-nat v)))

(defconst *fn-nls-lf* '(10))

(defun fn-nls-field (name n)
  "` NAME=N'."
  (declare (xargs :guard t))
  (append (fn-nls-text " ") (fn-nls-text name) (fn-nls-text "=") (fn-nls-value n)))

(defun fn-nls-kind-words (kind)
  (declare (xargs :guard t))
  (if (equal kind :forward) (fn-nls-text "forward") (fn-nls-text "archive")))

(defun fn-nls-obligation-line (o)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nls-text "obligation id=")
          (fn-nls-text (fn-retain-obligation-id o))
          (fn-nls-text " kind=")
          (fn-nls-kind-words (fn-retain-obligation-kind o))
          (fn-nls-field "charge" (fn-retain-obligation-charge o))
          (fn-nls-text " subject=")
          (fn-nls-text (fn-retain-obligation-subject o))
          *fn-nls-lf*))

(defun fn-nls-obligation-lines-rev (pins acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pins)
      (fn-nls-obligation-lines-rev (cdr pins)
                                   (revappend (fn-nls-obligation-line (car pins)) acc))
    acc))

(defun fn-nls-obligation-lines (pins)
  "One line per held retention obligation, in the ledger's order."
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp pins)
           (append (fn-nls-obligation-line (car pins))
                   (fn-nls-obligation-lines (cdr pins)))
         nil)
       :exec (revappend (fn-nls-obligation-lines-rev pins nil) nil)))

(defun fn-nls-retention (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-node-retention (fn-sn-node s)))

(encapsulate ()
  (local
   (defthm fn-nls-revappend-revappend-lines
     (equal (revappend (revappend x y) z)
            (revappend y (append x z)))))
  (local
   (defthm fn-nls-revappend-of-append-lines
     (equal (revappend (append x y) z)
            (revappend y (revappend x z)))))
  (local
   (defthm fn-nls-obligation-lines-rev-is-revappend
     (equal (fn-nls-obligation-lines-rev pins acc)
            (revappend (fn-nls-obligation-lines pins) acc))
     :hints (("Goal" :in-theory (disable fn-nls-obligation-line)))))
  (local
   (defthm fn-nls-true-listp-of-obligation-lines
     (true-listp (fn-nls-obligation-lines pins))))
  (local
   (defthm fn-nls-append-nil-lines
     (implies (true-listp x) (equal (append x nil) x))))
  (verify-guards fn-nls-obligation-line)
  (verify-guards fn-nls-obligation-lines-rev)
  (verify-guards fn-nls-obligation-lines
    :hints (("Goal" :in-theory (disable fn-nls-obligation-line)))))
(verify-guards fn-nls-retention)
