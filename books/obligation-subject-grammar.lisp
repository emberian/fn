; Read-only W9 inspection of one immutable content subject. The query uses
; the existing record metadata type, so it adds no stored-data ceiling.
(in-package "ACL2")
(include-book "records-shape")

(defun fn-oqg-kindp (kind)
  (declare (xargs :guard t))
  (and (consp kind) (equal (car kind) :obligation-subject)
       (fn-record-metadata-bytes-p (cdr kind))))

(defun fn-oqg-parse (words)
  (declare (xargs :guard t))
  (if (and (consp words) (equal (car words) "subject")
           (consp (cdr words)) (null (cddr words))
           (fn-record-metadata-bytes-p (cadr words)))
      (list :kind (cons :obligation-subject (cadr words)))
    (list :usage :obligation-subject)))

(defthm fn-oqg-parse-kind-is-a-kind
  (implies (equal (car (fn-oqg-parse words)) :kind)
           (fn-oqg-kindp (cadr (fn-oqg-parse words)))))

(in-theory (disable fn-oqg-kindp fn-oqg-parse))
