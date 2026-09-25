;; fn: the proto-article field checks of RFC 5537 section 3.5, split out of
;; books/injection.lisp so that the low books that read them do not include
;; the whole injecting agent.
;
; books/hybrid-carrier.lisp and books/hybrid-store.lisp name only the forms
; below: the field-name constants, the total list helpers, the RFC 5536
; section 3 mandatory-field checks and fn-inj-proto-reason.  Before this book
; they included books/injection.lisp, so every change to the injection
; decision (fn-inj-decide, the calendar, the D25 inverse) recertified the
; 400-odd books above the hybrid store (planning/audit-2026-09-25-twins-fanin.md
; packet 1).  books/injection.lisp includes this book and remains the owner of
; the decision; nothing here decides injection.  The definitions and their
; exported theory are those books/injection.lisp had: each is disabled at the
; end of this book, as fn-inj-vocabulary disabled it there.

(in-package "ACL2")
(include-book "article-fields")
(include-book "mailbox")

(defconst *fn-inj-path-name* '(112 97 116 104))
(defconst *fn-inj-from-name* '(102 114 111 109))
(defconst *fn-inj-subject-name* '(115 117 98 106 101 99 116))
(defconst *fn-inj-date-name* '(100 97 116 101))
(defconst *fn-inj-injection-date-name* '(105 110 106 101 99 116 105 111 110 45 100 97 116 101))

; -----------------------------------------------------------------------------
; Total list helpers.  Every function in this book is total: its guard is t or
; the article recognizer, and it coerces its arguments.

(defun fn-inj-car (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-inj-cdr (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

(defun fn-inj-nth (k xs)
  (declare (xargs :guard t :measure (nfix k)))
  (let ((k (nfix k)))
    (if (zp k) (fn-inj-car xs)
      (fn-inj-nth (- k 1) (fn-inj-cdr xs)))))

; -----------------------------------------------------------------------------
; Field presence, as RFC 5536 section 3 mandatory fields

(defun fn-inj-single-fieldp (article name)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (let ((fields (fn-article-get-headers article name)))
    (and (consp fields) (null (cdr fields)))))

(defun fn-inj-absentp (article name)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (null (fn-article-get-headers article name)))

; RFC 5536 section 3.1.2: From is an RFC 5322 mailbox-list (books/mailbox.lisp,
; the bounded recognizer).  Presence alone was checked until 2026-09-22, and
; `From: yue' was injected and served (planning/evidence/agents-on-hbox-
; 2026-09-22.md).  Read only after :from-missing and :from-duplicate, so the
; field is the one From field.
(defun fn-inj-from-validp (article)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (let ((fields (fn-article-get-headers article *fn-inj-from-name*)))
    (and (consp fields)
         (fn-article-fieldp (car fields))
         (fn-mbx-mailbox-listp (fn-article-field-unfolded-value (car fields))))))

(defun fn-inj-mandatory-reason (article)
  ; nil when every field a proto-article must supply is present exactly once
  ; and no field this agent generates is already present.
  (declare (xargs :guard (fn-article-syntax-p article)))
  (cond
   ((not (fn-inj-absentp article *fn-inj-path-name*)) :path-present)
   ((not (fn-inj-absentp article *fn-inj-injection-date-name*))
    :injection-date-present)
   ((fn-inj-absentp article *fn-inj-from-name*) :from-missing)
   ((not (fn-inj-single-fieldp article *fn-inj-from-name*)) :from-duplicate)
   ((not (fn-inj-from-validp article)) :from-invalid)
   ((fn-inj-absentp article *fn-inj-subject-name*) :subject-missing)
   ((not (fn-inj-single-fieldp article *fn-inj-subject-name*))
    :subject-duplicate)
   ((and (not (fn-inj-absentp article *fn-inj-date-name*))
         (not (fn-inj-single-fieldp article *fn-inj-date-name*)))
    :date-duplicate)
   (t nil)))

; RFC 5537 section 3.5 item 2's syntax check, read from the result of the
; article parser: the reason of an :error result, nil otherwise.
(defun fn-inj-proto-reason (check)
  (declare (xargs :guard t))
  (if (equal (fn-inj-nth 0 check) :error) (fn-inj-nth 1 check) nil))

; ---------------------------------------------------------------------------
; Export theory, as in books/injection.lisp: proof vocabulary, not rules an
; includer inherits.  books/injection.lisp re-enables it locally for its own
; proofs and lists every name again in fn-inj-vocabulary.

(deftheory fn-inj-shape-vocabulary
  '(fn-inj-car fn-inj-cdr fn-inj-nth fn-inj-single-fieldp fn-inj-absentp
    fn-inj-from-validp fn-inj-mandatory-reason fn-inj-proto-reason))

(in-theory (disable fn-inj-shape-vocabulary))
