; fn: lemmas about the line walk over a header of well-formed fields
; (fn-pu-line, fn-pu-after-line, fn-pu-strip, the field fold and the
; parser's field projection), shared by the two proofs that read a parsed
; article back as its octets: relaying cannot change who wrote an article
; (books/relay-source.lisp) and the served-POST filing plan
; (books/filed-stored.lisp, P4-3).  Each includer includes this book
; locally, so none of these rules reaches a third book.
(in-package "ACL2")

(include-book "article-properties")
(include-book "hybrid-carrier")
(include-book "path-update")


(defun rsp-field-wfp (field)
  (declare (xargs :guard t))
  (let ((lines (if (true-listp field) (fn-article-field-raw-lines field) nil)))
    (and (true-listp field)
         (consp lines)
         (fn-article-plain-linesp lines)
         (fn-article-wsp-startsp (cdr lines))
         (consp (car lines))
         (not (fn-pu-wspp (car (car lines))))
         (fn-article-has-colonp (car lines))
         (equal (fn-article-field-name field)
                (fn-article-ascii-downcase
                 (fn-article-name-before-colon (car lines)))))))

(defun rsp-fields-wfp (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (rsp-field-wfp (car fields))
           (rsp-fields-wfp (cdr fields)))
    (null fields)))

(defun rsp-path-or-xref-fieldp (field)
  (declare (xargs :guard t))
  (let ((line (append (if (and (true-listp field)
                               (consp (fn-article-field-raw-lines field))
                               (true-listp (car (fn-article-field-raw-lines field))))
                          (car (fn-article-field-raw-lines field))
                        nil)
                      '(13 10))))
    (or (fn-pu-named-p line *fn-pu-xref-colon*)
        (fn-pu-named-p line *fn-pu-path-colon*))))

(defun rsp-drop-path-xref (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (if (rsp-path-or-xref-fieldp (car fields))
          (rsp-drop-path-xref (cdr fields))
        (cons (car fields) (rsp-drop-path-xref (cdr fields))))
    nil))

(defthm rsp-pu-append-is-append
   (equal (fn-pu-append a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-pu-append))))

(defthm rsp-line-of-a-plain-line
   (implies (fn-article-crlf-freep l)
            (equal (fn-pu-line (append l (cons 13 (cons 10 r))))
                   (append l '(13 10))))
   :hints (("Goal" :in-theory (enable fn-pu-line fn-pu-crlf-atp))))

(defthm rsp-after-a-plain-line
   (implies (fn-article-crlf-freep l)
            (equal (fn-pu-after-line (append l (cons 13 (cons 10 r))))
                   r))
   :hints (("Goal" :in-theory (enable fn-pu-after-line fn-pu-crlf-atp))))

(defthm rsp-blank-line
   (and (equal (fn-pu-line (cons 13 (cons 10 r))) '(13 10))
        (equal (fn-pu-after-line (cons 13 (cons 10 r))) r))
   :hints (("Goal" :in-theory (enable fn-pu-line fn-pu-after-line fn-pu-crlf-atp))))

(defthm rsp-car-of-plain-line
   (implies (consp l)
            (equal (car (append l r)) (car l))))

(defthm rsp-plain-line-not-blank
   (implies (and (consp l) (fn-article-crlf-freep l))
            (not (equal (append l '(13 10)) '(13 10)))))

(defthm rsp-strip-continuations-dropped
   (implies (and (fn-article-plain-linesp conts)
                 (fn-article-wsp-startsp conts))
            (equal (fn-pu-strip (append (fn-article-lines-octets conts) r) t)
                   (fn-pu-strip r t)))
   :hints (("Goal" :induct (fn-article-lines-octets conts)
            :in-theory (enable fn-article-lines-octets fn-pu-wspp)
            :expand ((fn-pu-strip (append (car conts)
                                          (cons 13 (cons 10 (append (fn-article-lines-octets (cdr conts)) r))))
                                  t)))))

(defthm rsp-strip-continuations-kept
   (implies (and (fn-article-plain-linesp conts)
                 (fn-article-wsp-startsp conts))
            (equal (fn-pu-strip (append (fn-article-lines-octets conts) r) nil)
                   (append (fn-article-lines-octets conts) (fn-pu-strip r nil))))
   :hints (("Goal" :induct (fn-article-lines-octets conts)
            :in-theory (enable fn-article-lines-octets fn-pu-wspp)
            :expand ((fn-pu-strip (append (car conts)
                                          (cons 13 (cons 10 (append (fn-article-lines-octets (cdr conts)) r))))
                                  nil)))))

(defthm rsp-strip-of-a-field-line
   (implies (and (consp l) (fn-article-crlf-freep l) (not (fn-pu-wspp (car l))))
            (equal (fn-pu-strip (append l (cons 13 (cons 10 r))) d)
                   (if (or (fn-pu-named-p (append l '(13 10)) *fn-pu-xref-colon*)
                           (fn-pu-named-p (append l '(13 10)) *fn-pu-path-colon*))
                       (fn-pu-strip r t)
                     (append (append l '(13 10)) (fn-pu-strip r nil)))))
   :hints (("Goal" :expand ((fn-pu-strip (append l (cons 13 (cons 10 r))) d)))))

(defthm rsp-strip-of-the-blank-line
   (equal (fn-pu-strip (cons 13 (cons 10 r)) d) (cons 13 (cons 10 r)))
   :hints (("Goal" :expand ((fn-pu-strip (cons 13 (cons 10 r)) d)))))

(defun rsp-fields-induct (fields d)
   (if (consp fields)
       (list (rsp-fields-induct (cdr fields) t)
             (rsp-fields-induct (cdr fields) nil))
     d))

(defthm rsp-fields-octets-of-cons
   (equal (fn-article-fields-octets (cons f rest))
          (append (fn-article-lines-octets (fn-article-field-raw-lines f))
                  (fn-article-fields-octets rest)))
   :hints (("Goal" :in-theory (enable fn-article-fields-octets))))

(defthm rsp-strip-of-a-field
   (implies (and (consp fields) (rsp-field-wfp (car fields)))
            (equal (fn-pu-strip (append (fn-article-fields-octets fields) r) d)
                   (if (rsp-path-or-xref-fieldp (car fields))
                       (fn-pu-strip (append (fn-article-fields-octets (cdr fields)) r) t)
                     (append (fn-article-lines-octets (fn-article-field-raw-lines (car fields)))
                             (fn-pu-strip (append (fn-article-fields-octets (cdr fields)) r) nil)))))
   :hints (("Goal" :in-theory (e/d (fn-article-lines-octets) (fn-article-fields-octets fn-pu-named-p fn-pu-strip))
            :expand ((fn-article-fields-octets fields))
            :do-not '(generalize fertilize))))

(defthm rsp-strip-of-wf-fields
   (implies (rsp-fields-wfp fields)
            (equal (fn-pu-strip (append (fn-article-fields-octets fields)
                                        (cons 13 (cons 10 body)))
                                d)
                   (append (fn-article-fields-octets (rsp-drop-path-xref fields))
                           (cons 13 (cons 10 body)))))
   :hints (("Goal" :induct (rsp-fields-induct fields d)
            :in-theory (e/d () (fn-article-fields-octets rsp-field-wfp rsp-path-or-xref-fieldp fn-pu-strip)))
           ))

(defthm rsp-name-before-colon-of-append
   (implies (fn-article-has-colonp l)
            (equal (fn-article-name-before-colon (append l r))
                   (fn-article-name-before-colon l))))

(defun rsp-colon-freep (n)
   (declare (xargs :guard t))
   (if (consp n) (and (not (equal (car n) 58)) (rsp-colon-freep (cdr n))) (null n)))

(defthm rsp-named-p-names-the-field
   (implies (and (fn-pu-named-p line (append n '(58)))
                 (rsp-colon-freep n))
            (equal (fn-article-ascii-downcase (fn-article-name-before-colon line)) n))
   :hints (("Goal" :induct (fn-pu-named-p line n)
            :in-theory (enable fn-pu-named-p fn-pu-downcase))))

(defthm rsp-a-named-line-opens-with-ftext
   (implies (fn-article-namep (fn-article-ascii-downcase (fn-article-name-before-colon l)))
            (and (consp l) (not (fn-pu-wspp (car l)))))
   :hints (("Goal" :in-theory (enable fn-pu-wspp)
            :expand ((fn-article-name-before-colon l)
                     (fn-article-ascii-downcase (fn-article-name-before-colon l))))))

(defthm rsp-a-parsed-field-is-wf
   (implies (and (fn-article-field-correspondsp f) (fn-article-fieldp f))
            (rsp-field-wfp f))
   :hints (("Goal" :in-theory (e/d (fn-article-lower-namep)
                                   (fn-article-unfold-reference fn-article-namep fn-article-ascii-downcase
                                    fn-article-header-bytes-p fn-article-name-before-colon
                                    fn-article-has-colonp fn-article-plain-linesp fn-article-wsp-startsp))
            :use ((:instance rsp-a-named-line-opens-with-ftext
                   (l (car (fn-article-field-raw-lines f))))))))

(defthm rsp-parsed-fields-are-wf
   (implies (and (fn-article-fields-correspondp fields) (fn-article-field-listp fields))
            (rsp-fields-wfp fields))
   :hints (("Goal" :in-theory (disable rsp-field-wfp fn-article-field-correspondsp fn-article-fieldp))))

(defthm rsp-a-parsed-article-is-its-fields
   (implies (fn-article-result-okp (fn-article-parse y))
            (let ((article (fn-article-result-article (fn-article-parse y))))
              (and (true-listp article)
                   (rsp-fields-wfp (fn-article-fields article))
                   (true-listp (fn-article-body article))
                   (equal y (append (fn-article-fields-octets (fn-article-fields article))
                                    (cons 13 (cons 10 (fn-article-body article))))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-article-syntax-p fn-article-source
                                                fn-article-octet-list-true-listp
                                                fn-article-append-associative (:e binary-append) binary-append car-cons cdr-cons)
                                              (theory 'minimal-theory))
            :use ((:instance fn-article-successful-parse-syntax-p (octets y))
                  (:instance fn-article-successful-parse-fields-correspond (octets y))
                  (:instance fn-article-successful-parse-preserves-source (octets y))
                  (:instance fn-article-successful-parse-fields-recompose-header (octets y))
                  (:instance rsp-parsed-fields-are-wf
                   (fields (fn-article-fields (fn-article-result-article (fn-article-parse y)))))))))
