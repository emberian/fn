(in-package "ACL2")
(include-book "../../books/topic-history-metadata-invariants")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *th-id*
  (append *fn-id-subject-label* '(0 1 1)
          (make-list 32 :initial-element 5)))
(defconst *th-principal* (make-list 32 :initial-element 7))
(defconst *th-author* (list *th-principal* *th-id*))
(defconst *th-root* (list :root (make-list 32 :initial-element 1)
                          *th-principal* *th-id* '(109 105 110 105)
                          (list *th-author*)))
(defconst *th-control* (list :control *th-id* *th-id* (list *th-author*)))
(defconst *th-report* (list :report *th-id* *th-id* (list *th-id*)))
(assert-event (fn-th-value-p *th-root*))
(assert-event (fn-th-value-p *th-control*))
(assert-event (fn-th-value-p *th-report*))
(assert-event (equal (fn-th-decode (fn-th-encode *th-root*))
                     (fn-stmt-ok *th-root*)))
(assert-event (equal (fn-th-decode (fn-th-encode *th-control*))
                     (fn-stmt-ok *th-control*)))
(assert-event (equal (fn-th-decode (fn-th-encode *th-report*))
                     (fn-stmt-ok *th-report*)))
(assert-event (equal (fn-th-field-decode (fn-th-field-encode *th-root*))
                     (fn-stmt-ok *th-root*)))
(defun fn-t-th-authors-from (i remaining)
  (declare (xargs :guard (and (natp i) (natp remaining))
                  :measure (nfix remaining)))
  (if (zp remaining) nil
    (cons (list (cons i (make-list 31 :initial-element 0)) *th-id*)
          (fn-t-th-authors-from (1+ i) (1- remaining)))))
(defconst *th-max-root*
  (list :root (make-list 32 :initial-element 1) *th-principal*
        *th-id* (make-list 64 :initial-element 97)
        (fn-t-th-authors-from 0 16)))
(assert-event (fn-th-value-p *th-max-root*))
(assert-event (equal (len (fn-th-encode *th-max-root*)) 1531))
(assert-event (equal (len (fn-th-items *th-max-root*)) 39))
(assert-event (equal (len (fn-th-field-encode *th-max-root*)) 2047))
(assert-event (equal (fn-th-decode (fn-th-encode *th-max-root*))
                     (fn-stmt-ok *th-max-root*)))
(assert-event (not (fn-th-value-p
                    (list :root (make-list 32 :initial-element 1)
                          *th-principal* *th-id* '(109)
                          (fn-t-th-authors-from 0 17)))))
(assert-event (not (fn-th-value-p
                    (list :report *th-id* *th-id* (list *th-id* *th-id*)))))
(assert-event (not (fn-th-value-p
                    (list :control *th-id* *th-id*
                          (list *th-author* *th-author*)))))
(assert-event (not (fn-stmt-okp
                    (fn-th-decode (cons 0 (fn-th-encode *th-root*))))))
(assert-event (equal (fn-th-decode (make-list 1537 :initial-element 0))
                     (fn-stmt-error :binary-limit)))
(assert-event (not (fn-stmt-okp (fn-th-field-decode
                                 (append '(118 49 32) '(65 9 65 65 65))))))
(defun fn-t-th-line (text)
  (declare (xargs :guard t))
  (append (fn-record-string-octets text) '(13 10)))
(defconst *th-source-head*
  (append (fn-t-th-line "From: a")
          (fn-t-th-line "Subject: t")
          (fn-t-th-line "Date: Sun, 01 Jan 2023 00:00:00 +0000")
          (fn-t-th-line "Newsgroups: fn.test")
          (fn-t-th-line "Message-ID: <th@example>")))
(assert-event
 (let* ((field-line (append (fn-record-string-octets "FN-Topic: ")
                            (fn-th-field-encode *th-root*) '(13 10)))
        (source (append *th-source-head* field-line '(13 10 120))))
   (equal (fn-th-host-inspect-source source) (fn-stmt-ok *th-root*))))
; A relay's Path, Xref, and even a competing received FN-Topic do not become
; the authored source passed to the native inspection subject.
(assert-event
 (let* ((field-line (append (fn-record-string-octets "FN-Topic: ")
                            (fn-th-field-encode *th-root*) '(13 10)))
        (source (append *th-source-head* field-line '(13 10 120)))
        (received (append (fn-t-th-line "Path: relay!not-for-mail")
                          (fn-t-th-line "Xref: relay fn.test:9")
                          (append (fn-record-string-octets "FN-Topic: ")
                                  (fn-th-field-encode *th-control*) '(13 10))
                          source)))
   (and (equal (fn-th-host-inspect-source source)
               (fn-stmt-ok *th-root*))
        (not (fn-stmt-okp (fn-th-host-inspect-source received))))))
(assert-event
 (let ((field-line (append (fn-record-string-octets "FN-Topic: ")
                           (fn-th-field-encode *th-root*) '(13 10))))
   (equal (fn-th-project-source
           (append *th-source-head* field-line field-line '(13 10 120)))
          (fn-stmt-error :duplicate))))
(assert-event (not (fn-stmt-okp
                    (fn-th-project-source
                     (append *th-source-head*
                             (fn-t-th-line "FN-Topic: v1 AA")
                             (fn-t-th-line (concatenate 'string
                                            (string #\Tab) "AA=="))
                             '(13 10 120))))))
; A positive candidate depends on the only field being intact.
(must-fail
 (defthm fn-th-project-source-ignores-field-change
   (equal (fn-th-project-source
           (append *th-source-head*
                   (append (fn-t-th-line "FN-Topic: v1 AAAA") '(13 10 120))))
          (fn-stmt-ok *th-root*))))
; Dropping the validity hypothesis loses the constructor inverse.
(must-fail
 (defthm fn-th-roundtrip-without-validity
   (equal (fn-th-decode (fn-th-encode
                         (list :control *th-id* *th-id*
                               (list *th-author* *th-author*))))
          (fn-stmt-ok (list :control *th-id* *th-id*
                            (list *th-author* *th-author*))))))
; A duplicate authored field cannot satisfy the successful-field binding.
(must-fail
 (defthm fn-th-host-inspect-duplicate-is-candidate
   (let ((field-line (append (fn-record-string-octets "FN-Topic: ")
                             (fn-th-field-encode *th-root*) '(13 10))))
     (fn-stmt-okp
      (fn-th-host-inspect-source
       (append *th-source-head* field-line field-line '(13 10 120)))))))
