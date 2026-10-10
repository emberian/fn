; fn: lemmas about the article parser over a header built line by line
; (FN-ARTICLE-NEXT-LINE, the field fold, the field census and the control
; classifier), shared by the two proofs that a stored article keeps the
; Newsgroups, Control and Supersedes fields its source carried: packet 2's
; injected and peer events (books/filed-groups.lisp, P2-2 and P2-3) and
; packet 4's served POST (books/filed-stored.lisp, P4-1).  Each includer
; includes this book locally, so none of these rules reaches a third book.
(in-package "ACL2")

(include-book "article-header-limits")
(include-book "control-classify")
(include-book "cbor")

(defun o1p-line-ind (l acc left)
  (declare (xargs :measure (len l)))
  (if (consp l)
      (o1p-line-ind (cdr l) (cons (car l) acc) (1- left))
    (list acc left)))

(defthm o1p-next-line-aux-of-a-line
  (implies (and (fn-article-crlf-freep l) (true-listp l)
                (<= (len l) (nfix left)) (true-listp acc))
           (equal (fn-article-next-line-aux (append l (list* 13 10 r)) acc left)
                  (list :ok (append (reverse acc) l) r)))
  :hints (("Goal" :induct (o1p-line-ind l acc left)
           :in-theory (enable fn-article-next-line-aux))))

(defthm o1p-next-line-of-a-line
  (implies (and (fn-article-crlf-freep l) (true-listp l) (<= (len l) 998))
           (equal (fn-article-next-line (append l (list* 13 10 r)))
                  (list :ok l r)))
  :hints (("Goal" :in-theory (enable fn-article-next-line)
           :use ((:instance o1p-next-line-aux-of-a-line (acc nil) (left 998))))))

(defthm o1p-next-line-of-blank
  (equal (fn-article-next-line (list* 13 10 r)) (list :ok nil r))
  :hints (("Goal" :in-theory (enable fn-article-next-line fn-article-next-line-aux))))

(defthm o1p-next-line-aux-len
  (implies (and (true-listp line-rev)
                (fn-article-line-okp (fn-article-next-line-aux octets line-rev left)))
           (<= (len (fn-article-line-value (fn-article-next-line-aux octets line-rev left)))
               (+ (len line-rev) (nfix left))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left)
           :in-theory (enable fn-article-next-line-aux))))

(defthm o1p-next-line-len
  (implies (fn-article-line-okp (fn-article-next-line octets))
           (<= (len (fn-article-line-value (fn-article-next-line octets))) 998))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-article-next-line)
           :use ((:instance o1p-next-line-aux-len (line-rev nil) (left 998))))))

(defun o1p-line-okp (l)
  (declare (xargs :guard t))
  (and (true-listp l) (consp l) (fn-article-crlf-freep l) (<= (len l) 998)))

(defun o1p-folds-okp (ls)
  (declare (xargs :guard t))
  (if (consp ls)
      (and (o1p-line-okp (car ls)) (fn-article-fold-linep (car ls))
           (o1p-folds-okp (cdr ls)))
    (null ls)))

(defun o1p-fold-up (f ls)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ls)
      (o1p-fold-up (fn-article-add-fold f (car ls)) (cdr ls))
    f))

(defun o1p-fieldvp (f)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp f) (consp (car f))
       (o1p-line-okp (car (car f)))
       (not (fn-article-wspp (car (car (car f)))))
       (fn-article-line-okp (fn-article-new-field (car (car f))))
       (o1p-folds-okp (cdr (car f)))
       (equal f (o1p-fold-up (fn-article-line-value (fn-article-new-field (car (car f))))
                             (cdr (car f))))))

(defun o1p-closedp (f)
  (declare (xargs :guard t :verify-guards nil))
  (fn-article-has-vcharp (fn-article-field-unfolded-value f)))

(defun o1p-fieldsvp (fs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (and (o1p-fieldvp (car fs)) (o1p-closedp (car fs)) (o1p-fieldsvp (cdr fs)))
    (null fs)))

(defthm o1p-fold-up-append
  (equal (o1p-fold-up f (append a b)) (o1p-fold-up (o1p-fold-up f a) b)))

(defthm o1p-folds-okp-true-listp
  (implies (o1p-folds-okp a) (true-listp a))
  :rule-classes :forward-chaining)

(defthm o1p-folds-okp-append
  (implies (true-listp a)
           (equal (o1p-folds-okp (append a b)) (and (o1p-folds-okp a) (o1p-folds-okp b))))
  :hints (("Goal" :induct (o1p-folds-okp a))))

(defthm o1p-new-field-raw
  (implies (fn-article-line-okp (fn-article-new-field line))
           (equal (car (fn-article-line-value (fn-article-new-field line)))
                  (list line)))
  :hints (("Goal" :in-theory (enable fn-article-new-field))))

(defthm o1p-new-field-true-listp
  (implies (fn-article-line-okp (fn-article-new-field line))
           (true-listp (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal" :in-theory (enable fn-article-new-field))))

(defthm o1p-new-field-is-v
  (implies (and (o1p-line-okp line) (not (fn-article-wspp (car line)))
                (fn-article-line-okp (fn-article-new-field line)))
           (o1p-fieldvp (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal" :in-theory (e/d (o1p-fieldvp) (fn-article-new-field fn-article-line-value)))))

(defthm o1p-add-fold-is-v
  (implies (and (o1p-fieldvp f) (o1p-line-okp l) (fn-article-fold-linep l))
           (o1p-fieldvp (fn-article-add-fold f l)))
  :hints (("Goal" :in-theory (e/d (o1p-fieldvp fn-article-add-fold)
                                  (fn-article-new-field fn-article-line-value fn-article-fold-linep))
           :use ((:instance o1p-fold-up-append
                            (f (fn-article-line-value (fn-article-new-field (car (car f)))))
                            (a (cdr (car f))) (b (list l)))))))

(defthm o1p-fieldsvp-true-listp
  (implies (o1p-fieldsvp fs) (true-listp fs))
  :rule-classes :forward-chaining)

(defthm o1p-fieldsvp-append
  (implies (true-listp a)
           (equal (o1p-fieldsvp (append a b)) (and (o1p-fieldsvp a) (o1p-fieldsvp b))))
  :hints (("Goal" :induct (o1p-fieldsvp a))))

(defthm o1p-fieldsvp-rev
  (implies (o1p-fieldsvp a) (o1p-fieldsvp (rev a)))
  :hints (("Goal" :induct (o1p-fieldsvp a)
           :in-theory (enable rev))))

(defthm o1p-fieldsvp-revappend
  (implies (and (o1p-fieldsvp a) (o1p-fieldsvp b))
           (o1p-fieldsvp (revappend a b))))

(defthm o1p-fieldsvp-finish-fields
  (implies (and (o1p-fieldsvp fr)
                (or (null cur) (and (o1p-fieldvp cur) (o1p-closedp cur))))
           (o1p-fieldsvp (fn-article-finish-fields fr cur)))
  :hints (("Goal" :in-theory (enable fn-article-finish-fields))))

(defthm o1p-true-list-nonnil-is-consp
  (implies (and (true-listp x) x) (consp x))
  :rule-classes nil)

(defthm o1p-next-line-value-consp
  (implies (and (fn-article-line-okp (fn-article-next-line octets))
                (fn-article-line-value (fn-article-next-line octets)))
           (consp (fn-article-line-value (fn-article-next-line octets))))
  :hints (("Goal" :in-theory (disable fn-article-next-line fn-article-line-value)
           :use (fn-article-next-line-value-is-list
                 (:instance o1p-true-list-nonnil-is-consp
                            (x (fn-article-line-value (fn-article-next-line octets))))))))

(defthm o1p-next-line-value-is-a-line
  (implies (and (fn-article-line-okp (fn-article-next-line octets))
                (fn-article-line-value (fn-article-next-line octets)))
           (o1p-line-okp (fn-article-line-value (fn-article-next-line octets))))
  :hints (("Goal" :in-theory (e/d (o1p-line-okp)
                                  (fn-article-next-line fn-article-line-value))
           :use (fn-article-next-line-value-is-list
                 fn-article-next-line-value-crlf-free
                 o1p-next-line-value-consp
                 o1p-next-line-len))))

(defthm o1p-parse-lines-fields-v
  (implies (and (true-listp octets)
                (o1p-fieldsvp fields-rev)
                (or (null current) (o1p-fieldvp current))
                (fn-article-result-okp
                 (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                         fields-rev current header-rev)))
           (o1p-fieldsvp
            (fn-article-fields
             (fn-article-result-article
              (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                      fields-rev current header-rev)))))
  :hints (("Goal"
           :induct (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                           fields-rev current header-rev)
           :in-theory (e/d (fn-article-parse-lines fn-article-ok fn-article-make
                            fn-article-fields fn-article-result-okp fn-article-result-article
                            fn-article-field-closedp o1p-closedp)
                           (fn-article-next-line fn-article-next-line-aux
                            fn-article-new-field fn-article-add-fold
                            fn-article-finish-fields fn-article-body-crlfp
                            fn-article-header-rev-add-line
                            fn-article-line-value fn-article-line-rest
                            o1p-fieldvp)))))

(defthm o1p-parse-fields-v
  (implies (fn-article-result-okp (fn-article-parse octets))
           (o1p-fieldsvp (fn-article-fields (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance o1p-parse-lines-fields-v
                  (limits *fn-article-ceiling-limits*) (lines-left (1+ *fn-article-max-octets*))
                  (header-bytes 0) (nfields 0) (fields-rev nil) (current nil)
                  (header-rev nil)))
           :in-theory (e/d (fn-article-parse fn-article-parse-under
                            fn-article-octets-are-proper-list)
                           (fn-article-parse-lines fn-cbor-at-mostp
                            o1p-parse-lines-fields-v)))))

(defun o1p-nlines (fs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (+ (len (car (car fs))) (o1p-nlines (cdr fs)))
    0))

(defun o1p-hr-lines (hr lines)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp lines)
      (o1p-hr-lines (fn-article-header-rev-add-line hr (car lines)) (cdr lines))
    hr))

(defun o1p-run-fr (fs fr cur)
  (declare (xargs :guard t))
  (if (consp fs)
      (o1p-run-fr (cdr fs) (if cur (cons cur fr) fr) (car fs))
    fr))

(defun o1p-run-cur (fs cur)
  (declare (xargs :guard t))
  (if (consp fs) (o1p-run-cur (cdr fs) (car fs)) cur))

(defun o1p-run-nf (fs nf cur)
  (declare (xargs :guard t))
  (if (consp fs)
      (o1p-run-nf (cdr fs) (if cur (+ 1 (nfix nf)) nf) (car fs))
    nf))

(defun o1p-run-hr (fs hr)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (o1p-run-hr (cdr fs) (o1p-hr-lines hr (car (car fs))))
    hr))

(defthm o1p-new-field-consp
  (implies (fn-article-line-okp (fn-article-new-field line))
           (consp (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal" :in-theory (enable fn-article-new-field))))

(defthm o1p-parse-lines-of-a-fold
  (implies (and (o1p-line-okp l) (fn-article-fold-linep l) cur
                (posp nl) (natp hb)
                (<= (+ hb (len l) 2) (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines (append l (list* 13 10 rest))
                                          limits nl hb nf fr cur hr)
                  (fn-article-parse-lines rest limits (1- nl) (+ hb (len l) 2) nf fr
                                          (fn-article-add-fold cur l)
                                          (fn-article-header-rev-add-line hr l))))
  :hints (("Goal"
           :expand ((:free (cur hr nf fr)
                     (fn-article-parse-lines (append l (list* 13 10 rest))
                                             limits nl hb nf fr cur hr)))
           :in-theory (e/d (o1p-line-okp fn-article-fold-linep fn-article-wspp)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-header-bytes-p fn-article-has-vcharp
                            binary-append))
           :do-not-induct t)))

(defun o1p-folds-ind (ls cur nl hb hr)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ls)
      (o1p-folds-ind (cdr ls) (fn-article-add-fold cur (car ls)) (1- nl)
                     (+ hb (len (car ls)) 2)
                     (fn-article-header-rev-add-line hr (car ls)))
    (list cur nl hb hr)))

(defthm o1p-parse-lines-of-folds
  (implies (and (o1p-folds-okp ls) cur (natp nl) (natp hb)
                (<= (len ls) nl)
                (<= (+ hb (len (fn-article-lines-octets ls))) (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines (append (fn-article-lines-octets ls) rest)
                                          limits nl hb nf fr cur hr)
                  (fn-article-parse-lines rest limits (- nl (len ls))
                                          (+ hb (len (fn-article-lines-octets ls)))
                                          nf fr (o1p-fold-up cur ls) (o1p-hr-lines hr ls))))
  :hints (("Goal"
           :induct (o1p-folds-ind ls cur nl hb hr)
           :in-theory (e/d (fn-article-lines-octets)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-fold-linep)))))

(defthm o1p-parse-lines-of-a-new-field-line
  (implies (and (o1p-line-okp l) (not (fn-article-wspp (car l)))
                (fn-article-line-okp (fn-article-new-field l))
                (posp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (+ hb (len l) 2) (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines (append l (list* 13 10 rest))
                                          limits nl hb nf fr cur hr)
                  (fn-article-parse-lines rest limits (1- nl) (+ hb (len l) 2)
                                          (if cur (+ 1 nf) nf)
                                          (if cur (cons cur fr) fr)
                                          (fn-article-line-value (fn-article-new-field l))
                                          (fn-article-header-rev-add-line hr l))))
  :hints (("Goal"
           :expand ((:free (cur hr nf fr)
                     (fn-article-parse-lines (append l (list* 13 10 rest))
                                             limits nl hb nf fr cur hr)))
           :in-theory (e/d (o1p-line-okp fn-article-field-closedp)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-limit-fields fn-article-new-field
                            fn-article-header-bytes-p fn-article-has-vcharp
                            binary-append))
           :do-not-induct t)))

(defthm o1p-parse-lines-of-a-built-field
  (implies (and (o1p-line-okp l1) (not (fn-article-wspp (car l1)))
                (fn-article-line-okp (fn-article-new-field l1))
                (o1p-folds-okp folds)
                (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (+ 1 (len folds)) nl)
                (<= (+ hb (len l1) 2 (len (fn-article-lines-octets folds)))
                    (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-lines-octets (cons l1 folds)) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (+ 1 (len folds)))
                   (+ hb (len l1) 2 (len (fn-article-lines-octets folds)))
                   (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr)
                   (o1p-fold-up (fn-article-line-value (fn-article-new-field l1)) folds)
                   (o1p-hr-lines hr (cons l1 folds)))))
  :hints (("Goal"
           :in-theory (e/d (fn-article-lines-octets)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-limit-fields fn-article-new-field
                            fn-article-has-vcharp fn-article-line-value
                            o1p-parse-lines-of-a-new-field-line
                            o1p-parse-lines-of-folds))
           :do-not-induct t
           :use ((:instance o1p-parse-lines-of-a-new-field-line
                            (l l1) (rest (append (fn-article-lines-octets folds) rest)))
                 (:instance o1p-parse-lines-of-folds
                            (ls folds) (cur (fn-article-line-value (fn-article-new-field l1)))
                            (nl (1- nl)) (hb (+ hb (len l1) 2))
                            (nf (if cur (+ 1 nf) nf)) (fr (if cur (cons cur fr) fr))
                            (hr (fn-article-header-rev-add-line hr l1)))))))

(defthm o1p-cons-car-cdr
  (implies (consp x) (equal (cons (car x) (cdr x)) x)))

(defthm o1p-parse-lines-of-a-built-field-ls
  (implies (and (consp ls) (o1p-line-okp (car ls)) (not (fn-article-wspp (car (car ls))))
                (fn-article-line-okp (fn-article-new-field (car ls)))
                (o1p-folds-okp (cdr ls))
                (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (len ls) nl)
                (<= (+ hb (len (fn-article-lines-octets ls))) (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-lines-octets ls) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (len ls))
                   (+ hb (len (fn-article-lines-octets ls)))
                   (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr)
                   (o1p-fold-up (fn-article-line-value (fn-article-new-field (car ls))) (cdr ls))
                   (o1p-hr-lines hr ls))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-article-parse-lines fn-article-limit-octets fn-article-limit-fields
                               fn-article-new-field fn-article-line-value o1p-hr-lines
                               o1p-parse-lines-of-a-built-field)
           :expand ((len ls) (fn-article-lines-octets ls))
           :use ((:instance o1p-parse-lines-of-a-built-field
                            (l1 (car ls)) (folds (cdr ls)))))))

(defthm o1p-parse-lines-of-a-field
  (implies (and (o1p-fieldvp f)
                (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (len (car f)) nl)
                (<= (+ hb (len (fn-article-lines-octets (car f))))
                    (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-lines-octets (car f)) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (len (car f)))
                   (+ hb (len (fn-article-lines-octets (car f))))
                   (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr)
                   f (o1p-hr-lines hr (car f)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (o1p-fieldvp)
                           (fn-article-parse-lines fn-article-lines-octets
                            fn-article-limit-octets fn-article-limit-fields
                            fn-article-new-field fn-article-line-value
                            o1p-parse-lines-of-a-built-field-ls o1p-hr-lines))
           :use ((:instance o1p-parse-lines-of-a-built-field-ls (ls (car f)))))))

(defun o1p-fields-ind (fs nl hb nf fr cur hr)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (o1p-fields-ind (cdr fs) (- nl (len (car (car fs))))
                      (+ hb (len (fn-article-lines-octets (car (car fs)))))
                      (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr) (car fs)
                      (o1p-hr-lines hr (car (car fs))))
    (list nl hb nf fr cur hr)))

(defthm o1p-parse-lines-of-fields
  (implies (and (o1p-fieldsvp fs) (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (o1p-nlines fs) nl)
                (<= (+ hb (len (fn-article-fields-octets fs))) (fn-article-limit-octets limits))
                (<= (+ nf (if cur 1 0) (len fs)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-fields-octets fs) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (o1p-nlines fs))
                   (+ hb (len (fn-article-fields-octets fs)))
                   (o1p-run-nf fs nf cur) (o1p-run-fr fs fr cur)
                   (o1p-run-cur fs cur) (o1p-run-hr fs hr))))
  :hints (("Goal"
           :induct (o1p-fields-ind fs nl hb nf fr cur hr)
           :in-theory (e/d (o1p-closedp)
                           (fn-article-parse-lines fn-article-limit-octets
                            fn-article-limit-fields fn-article-lines-octets
                            o1p-hr-lines)))))

(defthm o1p-parse-lines-of-the-blank-line
  (implies (and (posp nl) (fn-article-body-crlfp body)
                (fn-article-field-closedp cur) (true-listp hr))
           (equal (fn-article-parse-lines (cons 13 (cons 10 body))
                                          limits nl hb nf fr cur hr)
                  (fn-article-ok
                   (fn-article-make (rev hr) body (fn-article-finish-fields fr cur)))))
  :hints (("Goal"
           :expand ((fn-article-parse-lines (cons 13 (cons 10 body))
                                            limits nl hb nf fr cur hr))
           :in-theory (disable fn-article-parse-lines fn-article-field-closedp
                               fn-article-body-crlfp fn-article-finish-fields)
           :use ((:instance fn-article-blank-line-partitions-input (octets (cons 13 (cons 10 body))))))))

(defthm o1p-hr-lines-true-listp
  (implies (true-listp hr) (true-listp (o1p-hr-lines hr lines)))
  :hints (("Goal" :in-theory (enable fn-article-header-rev-add-line))))

(defthm o1p-run-hr-true-listp
  (implies (true-listp hr) (true-listp (o1p-run-hr fs hr)))
  :hints (("Goal" :in-theory (disable o1p-hr-lines))))

(defthm o1p-run-cur-closed
  (implies (and (o1p-fieldsvp fs)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur))))
           (fn-article-field-closedp (o1p-run-cur fs cur)))
  :hints (("Goal" :in-theory (enable fn-article-field-closedp o1p-closedp))))

(defthm o1p-parse-lines-of-fields-and-body
  (implies (and (o1p-fieldsvp fs) (natp nl) (natp hb) (natp nf) (true-listp hr)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (< (o1p-nlines fs) nl)
                (<= (+ hb (len (fn-article-fields-octets fs))) (fn-article-limit-octets limits))
                (<= (+ nf (if cur 1 0) (len fs)) (fn-article-limit-fields limits))
                (fn-article-body-crlfp body))
           (equal (fn-article-parse-lines
                   (append (fn-article-fields-octets fs) (cons 13 (cons 10 body)))
                   limits nl hb nf fr cur hr)
                  (fn-article-ok
                   (fn-article-make (rev (o1p-run-hr fs hr)) body
                                    (fn-article-finish-fields (o1p-run-fr fs fr cur)
                                                              (o1p-run-cur fs cur))))))
  :hints (("Goal"
           :in-theory (disable fn-article-parse-lines fn-article-limit-octets
                               fn-article-limit-fields o1p-run-hr o1p-run-fr o1p-run-cur
                               o1p-run-nf fn-article-field-closedp o1p-nlines
                               fn-article-finish-fields fn-article-body-crlfp)
           :use ((:instance o1p-parse-lines-of-fields (rest (cons 13 (cons 10 body))))
                 (:instance o1p-parse-lines-of-the-blank-line
                            (nl (- nl (o1p-nlines fs)))
                            (hb (+ hb (len (fn-article-fields-octets fs))))
                            (nf (o1p-run-nf fs nf cur)) (fr (o1p-run-fr fs fr cur))
                            (cur (o1p-run-cur fs cur)) (hr (o1p-run-hr fs hr)))))))

(defthm o1p-reverse-is-rev
  (implies (true-listp x) (equal (reverse x) (rev x)))
  :hints (("Goal" :in-theory (enable rev))))

(defthm o1p-finish-fields-of-the-run
  (implies (and (o1p-fieldsvp fs) (true-listp fr))
           (equal (fn-article-finish-fields (o1p-run-fr fs fr cur) (o1p-run-cur fs cur))
                  (append (fn-article-finish-fields fr cur) fs)))
  :hints (("Goal" :induct (o1p-fields-ind fs nl hb nf fr cur hr)
           :in-theory (e/d (fn-article-finish-fields) (o1p-hr-lines)))))

(defun o1p-tl-linesp (ls)
  (declare (xargs :guard t))
  (if (consp ls) (and (true-listp (car ls)) (o1p-tl-linesp (cdr ls))) t))

(defthm o1p-folds-okp-tl-linesp
  (implies (o1p-folds-okp ls) (o1p-tl-linesp ls)))

(defthm o1p-fieldvp-tl-lines
  (implies (o1p-fieldvp f) (o1p-tl-linesp (car f)))
  :hints (("Goal" :in-theory (enable o1p-fieldvp)
           :use ((:instance o1p-cons-car-cdr (x (car f)))))))

(defthm o1p-hr-lines-recompose
  (implies (and (true-listp hr) (o1p-tl-linesp ls))
           (equal (rev (o1p-hr-lines hr ls))
                  (append (rev hr) (fn-article-lines-octets ls))))
  :hints (("Goal" :induct (o1p-hr-lines hr ls)
           :in-theory (e/d (fn-article-lines-octets)
                           (fn-article-header-rev-add-line fn-article-header-rev-add-line-recomposes))
           :do-not-induct t)
          ("Subgoal *1/1" :use ((:instance fn-article-header-rev-add-line-recomposes
                                           (header-rev hr) (line (car ls)))
                                (:instance fn-article-extended-header-is-list
                                           (header-rev hr) (line (car ls)))))))

(defthm o1p-run-hr-recompose
  (implies (and (o1p-fieldsvp fs) (true-listp hr))
           (equal (rev (o1p-run-hr fs hr))
                  (append (rev hr) (fn-article-fields-octets fs))))
  :hints (("Goal" :induct (o1p-fields-ind fs nl hb nf fr cur hr)
           :in-theory (e/d () (o1p-hr-lines fn-article-lines-octets)))))

(defthm o1p-len-le-len-append
  (<= (len b) (len (append a b)))
  :rule-classes :linear)

(defthm o1p-lines-le-octets
  (<= (len ls) (len (fn-article-lines-octets ls)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-article-lines-octets))))

(defthm o1p-nlines-le-octets
  (implies (o1p-fieldsvp fs)
           (<= (o1p-nlines fs) (len (fn-article-fields-octets fs))))
  :rule-classes :linear
  :hints (("Goal" :induct (o1p-nlines fs)
           :in-theory (e/d () (fn-article-lines-octets)))))

(defthm o1p-fields-le-nlines
  (implies (o1p-fieldsvp fs)
           (<= (len fs) (o1p-nlines fs)))
  :rule-classes :linear
  :hints (("Goal" :induct (o1p-nlines fs)
           :in-theory (enable o1p-fieldvp))))

(defthm o1p-parse-of-fields
  (implies (and (o1p-fieldsvp fs) (fn-article-body-crlfp body)
                (fn-cbor-octet-listp (append (fn-article-fields-octets fs)
                                             (cons 13 (cons 10 body))))
                (<= (len (append (fn-article-fields-octets fs) (cons 13 (cons 10 body))))
                    *fn-article-max-octets*))
           (equal (fn-article-parse (append (fn-article-fields-octets fs)
                                            (cons 13 (cons 10 body))))
                  (fn-article-ok (fn-article-make (fn-article-fields-octets fs) body fs))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-article-parse fn-article-parse-under fn-ap-at-most-is-length-bound)
                           (fn-article-parse-lines o1p-run-hr o1p-run-fr o1p-run-cur
                            o1p-nlines fn-article-fields-octets fn-article-finish-fields
                            fn-article-body-crlfp o1p-parse-lines-of-fields-and-body))
           :use ((:instance o1p-parse-lines-of-fields-and-body
                            (limits *fn-article-ceiling-limits*)
                            (nl (1+ *fn-article-max-octets*))
                            (hb 0) (nf 0) (fr nil) (cur nil) (hr nil))
                 (:instance o1p-finish-fields-of-the-run (fr nil) (cur nil))
                 (:instance o1p-run-hr-recompose (hr nil))
                 (:instance o1p-nlines-le-octets)
                 (:instance o1p-fields-le-nlines)))))

(defthm o1p-parse-lines-body-crlfp
  (implies (fn-article-result-okp
            (fn-article-parse-lines octets limits nl hb nf fr cur hr))
           (fn-article-body-crlfp
            (fn-article-body
             (fn-article-result-article
              (fn-article-parse-lines octets limits nl hb nf fr cur hr)))))
  :hints (("Goal"
           :induct (fn-article-parse-lines octets limits nl hb nf fr cur hr)
           :in-theory (e/d (fn-article-parse-lines fn-article-ok fn-article-make
                            fn-article-body fn-article-result-okp fn-article-result-article)
                           (fn-article-next-line fn-article-next-line-aux
                            fn-article-new-field fn-article-add-fold
                            fn-article-finish-fields fn-article-body-crlfp
                            fn-article-header-rev-add-line
                            fn-article-line-value fn-article-line-rest)))))

(defthm o1p-parse-body-crlfp
  (implies (fn-article-result-okp (fn-article-parse octets))
           (fn-article-body-crlfp
            (fn-article-body (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance o1p-parse-lines-body-crlfp
                  (limits *fn-article-ceiling-limits*) (nl (1+ *fn-article-max-octets*))
                  (hb 0) (nf 0) (fr nil) (cur nil) (hr nil)))
           :in-theory (e/d (fn-article-parse fn-article-parse-under)
                           (fn-article-parse-lines fn-cbor-at-mostp
                            o1p-parse-lines-body-crlfp)))))

(defthm o1p-parse-reconstructs
  (implies (fn-article-result-okp (fn-article-parse y))
           (let ((article (fn-article-result-article (fn-article-parse y))))
             (and (true-listp article)
                  (o1p-fieldsvp (fn-article-fields article))
                  (fn-article-body-crlfp (fn-article-body article))
                  (true-listp (fn-article-body article))
                  (equal y (append (fn-article-fields-octets (fn-article-fields article))
                                   (cons 13 (cons 10 (fn-article-body article))))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories '(fn-article-syntax-p fn-article-source
                                        fn-article-octet-list-true-listp
                                        fn-article-append-associative (:e binary-append)
                                        binary-append car-cons cdr-cons)
                                      (theory 'minimal-theory))
           :use ((:instance fn-article-successful-parse-syntax-p (octets y))
                 (:instance fn-article-successful-parse-preserves-source (octets y))
                 (:instance fn-article-successful-parse-fields-recompose-header (octets y))
                 (:instance o1p-parse-fields-v (octets y))
                 (:instance o1p-parse-body-crlfp (octets y))))))

(defthm o1p-parse-article-true-listp
  (implies (fn-article-result-okp (fn-article-parse y))
           (true-listp (fn-article-result-article (fn-article-parse y))))
  :hints (("Goal" :use ((:instance fn-article-successful-parse-syntax-p (octets y)))
           :in-theory (e/d (fn-article-syntax-p) (fn-article-parse fn-article-result-article)))))

(defthm o1p-classify-fields-by-named
  (implies (and (equal (fn-ctl-fields-named *fn-ctl-control-name* fs)
                       (fn-ctl-fields-named *fn-ctl-control-name* gs))
                (equal (fn-ctl-fields-named *fn-ctl-supersedes-name* fs)
                       (fn-ctl-fields-named *fn-ctl-supersedes-name* gs)))
           (equal (fn-ctl-classify-fields fs) (fn-ctl-classify-fields gs)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ctl-classify-fields)
                                  (fn-ctl-fields-named fn-ctl-parse-command)))))

(defthm o1p-agree-classify
  (implies (and (fn-article-result-okp (fn-article-parse s))
                (fn-article-result-okp (fn-article-parse r))
                (equal (fn-ctl-fields-named
                        *fn-ctl-control-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse s))))
                       (fn-ctl-fields-named
                        *fn-ctl-control-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse r)))))
                (equal (fn-ctl-fields-named
                        *fn-ctl-supersedes-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse s))))
                       (fn-ctl-fields-named
                        *fn-ctl-supersedes-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse r))))))
           (equal (fn-ctl-classify-octets s) (fn-ctl-classify-octets r)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-classify-octets fn-ctl-classify)
                                  (fn-article-parse fn-ctl-fields-named fn-ctl-parse-command
                                   fn-ctl-classify-fields fn-article-fields
                                   fn-article-result-article))
           :use (o1p-parse-article-true-listp
                 (:instance o1p-parse-article-true-listp (y r))
                 (:instance o1p-classify-fields-by-named
                            (fs (fn-article-fields (fn-article-result-article (fn-article-parse s))))
                            (gs (fn-article-fields (fn-article-result-article (fn-article-parse r)))))))))

(defthm o1p-car-of-fold-up
  (implies (and (true-listp (car f)) (true-listp ls))
           (equal (car (o1p-fold-up f ls)) (append (car f) ls)))
  :hints (("Goal" :induct (o1p-fold-up f ls) :in-theory (enable fn-article-add-fold))))

(defthm o1p-cadr-of-fold-up
  (equal (cadr (o1p-fold-up f ls)) (cadr f))
  :hints (("Goal" :induct (o1p-fold-up f ls) :in-theory (enable fn-article-add-fold))))

(defthm o1p-closed-of-fold-up
  (implies (fn-article-has-vcharp (caddr f))
           (fn-article-has-vcharp (caddr (o1p-fold-up f ls))))
  :hints (("Goal" :induct (o1p-fold-up f ls) :in-theory (enable fn-article-add-fold))))

(defthm o1p-fold-up-true-listp
  (implies (true-listp f) (true-listp (o1p-fold-up f ls)))
  :hints (("Goal" :induct (o1p-fold-up f ls) :in-theory (enable fn-article-add-fold))))

(in-theory (disable o1p-fieldvp o1p-closedp))

(defun o1p-fields-agree (fs gs)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-article-get-headers-aux fs *fn-af-newsgroups-name*)
              (fn-article-get-headers-aux gs *fn-af-newsgroups-name*))
       (equal (fn-ctl-fields-named *fn-ctl-control-name* fs)
              (fn-ctl-fields-named *fn-ctl-control-name* gs))
       (equal (fn-ctl-fields-named *fn-ctl-supersedes-name* fs)
              (fn-ctl-fields-named *fn-ctl-supersedes-name* gs))))

(defthm o1p-split-colon-of-a-name
  (implies (and (fn-article-ftext-listp name) (true-listp acc))
           (equal (fn-article-split-colon-aux (append name (cons 58 rest)) acc)
                  (list :ok (append (reverse acc) name) rest)))
  :hints (("Goal" :induct (o1p-line-ind name acc 0)
           :in-theory (enable fn-article-split-colon-aux fn-article-ftextp))))

(defthm o1p-get-headers-aux-skip
  (implies (not (equal (fn-article-field-name g) (fn-article-ascii-downcase name)))
           (equal (fn-article-get-headers-aux (cons g fs) name)
                  (fn-article-get-headers-aux fs name)))
  :hints (("Goal" :expand ((fn-article-get-headers-aux (cons g fs) name))
           :in-theory (enable fn-article-field-name-equalp))))

(defun o1p-prefix-clearp (pre)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pre)
      (and (true-listp (car pre))
           (not (equal (cadr (car pre)) *fn-af-newsgroups-name*))
           (not (equal (cadr (car pre)) *fn-ctl-control-name*))
           (not (equal (cadr (car pre)) *fn-ctl-supersedes-name*))
           (o1p-prefix-clearp (cdr pre)))
    t))

(defthm o1p-prefix-agrees
  (implies (o1p-prefix-clearp pre)
           (o1p-fields-agree (append pre fs) fs))
  :hints (("Goal" :induct (o1p-prefix-clearp pre)
           :in-theory (e/d (o1p-fields-agree fn-ctl-fields-named fn-ctl-field-name
                            fn-article-get-headers-aux fn-article-field-name-equalp)
                           ()))))

(defthm o1p-fields-octets-append
  (equal (fn-article-fields-octets (append a b))
         (append (fn-article-fields-octets a) (fn-article-fields-octets b)))
  :hints (("Goal" :induct (fn-article-fields-octets a)
           :in-theory (enable fn-article-fields-octets))))

(defthm o1p-cons-car-cdr
  (implies (consp x) (equal (cons (car x) (cdr x)) x)))

(defun o1p-octet-list-listp (xs) (declare (xargs :guard t))
  (if (consp xs) (and (fn-cbor-octet-listp (car xs)) (o1p-octet-list-listp (cdr xs))) t))

(defun o1p-names-okp (xs) (declare (xargs :guard t))
  (if (consp xs) (and (true-listp (car xs)) (fn-af-newsgroup-namep (car xs)) (o1p-names-okp (cdr xs))) t))

(defthm o1p-name-aux-octets
  (implies (and (true-listp b) (fn-af-newsgroup-name-aux b w)) (fn-cbor-octet-listp b))
  :hints (("Goal" :in-theory (enable fn-af-newsgroup-name-aux fn-af-newsgroup-component-charp fn-cbor-octet-listp fn-cbor-octetp))))

(defthm o1p-names-ok-octets
  (implies (o1p-names-okp xs) (o1p-octet-list-listp xs))
  :hints (("Goal" :in-theory (enable fn-af-newsgroup-namep))))

(defthm o1p-names-ok-revappend
  (implies (and (o1p-names-okp a) (o1p-names-okp b)) (o1p-names-okp (revappend a b)))
  :hints (("Goal" :induct (revappend a b) :in-theory (disable fn-af-newsgroup-namep))))

(defthm o1p-take-token-name-true-listp
  (implies (true-listp rev) (true-listp (cadr (fn-af-take-newsgroup-token bytes rev))))
  :hints (("Goal" :in-theory (enable fn-af-take-newsgroup-token))))

(defthm o1p-list-parse-aux-names-ok
  (implies (and (o1p-names-okp names-rev)
                (equal (car (fn-af-newsgroup-list-parse-aux bytes names-rev need fuel)) :ok))
           (o1p-names-okp (cadr (fn-af-newsgroup-list-parse-aux bytes names-rev need fuel))))
  :hints (("Goal" :induct (fn-af-newsgroup-list-parse-aux bytes names-rev need fuel)
           :in-theory (e/d (fn-af-newsgroup-list-parse-aux) (fn-af-newsgroup-namep fn-af-take-newsgroup-token fn-af-skip-wsp)))))
