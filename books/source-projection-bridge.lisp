; The carrier's authored-source projection and the injection inverse.
;
; fn-hc-authored-source (books/hybrid-carrier.lisp) is the signature subject
; of a parsed article: its header fields without the seven names of
; fn-hc-reserved-namep (FN-Authorship, Path, Xref, Injection-Date,
; Injection-Info, FN-Statement, FN-Policy), then CRLF and the body.
; fn-inj-source-of (books/injection.lisp) is the D25 comparison subject of a
; stored record: the octets after this agent's injected block.  They compute
; different values.  This book states how they relate.
(in-package "ACL2")
(include-book "hybrid-carrier")
(include-book "injection-invariants")
;
; THE RELATION.  For a stored record `stored' that is this agent's injection
; of `source' with neither the Message-ID nor the Date generated (which
; fn-hc-required-sourcep, the carrier's source profile, makes the only case:
; it requires one Message-ID and one Date in the source), and when both parse:
;   (fn-hc-authored-source (parse stored)) = (fn-hc-authored-source (parse source))
; and fn-inj-source-of returns exactly `source' (the injection inverse,
; books/injection-invariants.lisp).  So the carrier projection factors
; through the injection inverse.  The two subjects then differ exactly by
; the source's own reserved fields: fn-inj-source-of keeps them (an
; FN-Authorship carrier, FN-Statement, FN-Policy, a poster's Path or Xref),
; fn-hc-authored-source drops them; for a source with none, the projection
; is the source's header lines, CRLF and body.
;
; Outside that case they are not related by this theorem, and the tests show
; each hypothesis is needed: a generated Message-ID or Date line is not a
; reserved name, so the projection of the stored record carries it and the
; source's does not; an agent with a line break splits the Path line into a
; field the projection keeps; a source that does not parse alone (a leading
; continuation line) parses behind the block as part of Injection-Info.

(local (defthm fn-spj-len-of-append
  (equal (len (append a b)) (+ (len a) (len b)))))

(local (defthm fn-spj-append-assoc
  (equal (append (append a b) c) (append a (append b c)))))

(local
 (defun fn-spj-ind (x l l2 b b2 fr cur hr hr2)
   (declare (xargs :measure (nfix l)))
   (if (zp l) (list x l2 b b2 fr cur hr hr2)
     (let ((next (fn-article-next-line x)))
       (if (not (fn-article-line-okp next)) nil
         (let ((line (fn-article-line-value next))
               (rest (fn-article-line-rest next)))
           (if (null line) nil
             (if (fn-article-wspp (car line))
                 (fn-spj-ind rest (1- l) (1- l2) (+ b (len line) 2) (+ b2 (len line) 2)
                             fr (fn-article-add-fold cur line)
                             (fn-article-header-rev-add-line hr line)
                             (fn-article-header-rev-add-line hr2 line))
               (fn-spj-ind rest (1- l) (1- l2) (+ b (len line) 2) (+ b2 (len line) 2)
                           (if cur (cons cur fr) fr)
                           (fn-article-line-value (fn-article-new-field line))
                           (fn-article-header-rev-add-line hr line)
                           (fn-article-header-rev-add-line hr2 line))))))))))

(local
 (defthm fn-spj-parse-lines-with-older-fields
   (implies (and (fn-article-result-okp
                  (fn-article-parse-lines x l b (append fr tl) cur hr))
                 (true-listp fr) (true-listp tl)
                 (natp l) (natp l2) (<= l l2)
                 (natp b) (natp b2) (<= b2 b))
            (let ((a (fn-article-parse-lines x l b (append fr tl) cur hr))
                  (s (fn-article-parse-lines x l2 b2 fr cur hr2)))
              (and (fn-article-result-okp s)
                   (equal (fn-article-fields (fn-article-result-article a))
                          (append (reverse tl)
                                  (fn-article-fields (fn-article-result-article s))))
                   (equal (fn-article-body (fn-article-result-article a))
                          (fn-article-body (fn-article-result-article s))))))
   :hints (("Goal" :induct (fn-spj-ind x l l2 b b2 fr cur hr hr2)
            :in-theory (e/d (fn-article-parse-lines fn-article-finish-fields)
                            (fn-article-next-line fn-article-new-field
                             fn-article-add-fold fn-article-header-rev-add-line
                             fn-article-body-crlfp fn-article-fold-linep fn-article-wspp))))))

(defun fn-spj-line-freep (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (not (equal (car x) 13)) (not (equal (car x) 10))
           (fn-spj-line-freep (cdr x)))
    t))

(local
 (defthm fn-spj-next-line-aux-of-a-line
   (implies (and (fn-spj-line-freep l) (true-listp l) (natp left))
            (equal (fn-article-next-line-aux (append l (list* 13 10 rest)) line-rev left)
                   (if (<= (len l) left)
                       (list :ok (reverse (revappend l line-rev)) rest)
                     (fn-article-error :limit))))
   :hints (("Goal" :induct (fn-article-next-line-aux l line-rev left)
            :in-theory (enable fn-article-next-line-aux)))))

(local
 (defthm fn-spj-next-line-of-a-line
   (implies (and (fn-spj-line-freep l) (true-listp l))
            (equal (fn-article-next-line (append l (list* 13 10 rest)))
                   (if (<= (len l) *fn-article-max-line-octets*)
                       (list :ok l rest)
                     (fn-article-error :limit))))
   :hints (("Goal" :in-theory (enable fn-article-next-line)))))

(defun fn-spj-reserved-field-linep (l)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-article-new-field l)))
    (implies (fn-article-line-okp r)
             (fn-hc-reserved-namep (fn-article-field-name (fn-article-line-value r))))))

(local
 (defthm fn-spj-parse-lines-after-two-fields
   (implies (and (fn-article-result-okp (fn-article-parse-lines x l b (list f1) f2 hr))
                 (fn-article-result-okp (fn-article-parse-lines x l2 b2 nil nil hr2))
                 f2
                 (natp l) (natp l2) (<= l l2)
                 (natp b) (natp b2) (<= b2 b))
            (let ((a (fn-article-parse-lines x l b (list f1) f2 hr))
                  (s (fn-article-parse-lines x l2 b2 nil nil hr2)))
              (and (equal (fn-article-fields (fn-article-result-article a))
                          (list* f1 f2 (fn-article-fields (fn-article-result-article s))))
                   (equal (fn-article-body (fn-article-result-article a))
                          (fn-article-body (fn-article-result-article s))))))
   :hints (("Goal"
            :expand ((fn-article-parse-lines x l b (list f1) f2 hr)
                     (fn-article-parse-lines x l2 b2 nil nil hr2))
            :use ((:instance fn-spj-parse-lines-with-older-fields
                             (x (fn-article-line-rest (fn-article-next-line x)))
                             (l (1- l)) (l2 (1- l2))
                             (b (+ b (len (fn-article-line-value (fn-article-next-line x))) 2))
                             (b2 (+ b2 (len (fn-article-line-value (fn-article-next-line x))) 2))
                             (fr nil) (tl (list f2 f1))
                             (cur (fn-article-line-value
                                   (fn-article-new-field
                                    (fn-article-line-value (fn-article-next-line x)))))
                             (hr (fn-article-header-rev-add-line
                                  hr (fn-article-line-value (fn-article-next-line x))))
                             (hr2 (fn-article-header-rev-add-line
                                   hr2 (fn-article-line-value (fn-article-next-line x))))))
            :in-theory (e/d (fn-article-finish-fields)
                            (fn-article-parse-lines fn-spj-parse-lines-with-older-fields
                             fn-article-next-line fn-article-new-field
                             fn-article-add-fold fn-article-header-rev-add-line
                             fn-article-body-crlfp fn-article-fold-linep fn-article-wspp))))))

(local
 (defthm fn-spj-parse-lines-of-a-field-line
   (implies (and (fn-spj-line-freep l) (true-listp l) (consp l)
                 (not (fn-article-wspp (car l)))
                 (fn-article-result-okp
                  (fn-article-parse-lines (append l (list* 13 10 rest)) n b fr cur hr)))
            (equal (fn-article-parse-lines (append l (list* 13 10 rest)) n b fr cur hr)
                   (fn-article-parse-lines rest (1- n) (+ b (len l) 2)
                                           (if cur (cons cur fr) fr)
                                           (fn-article-line-value (fn-article-new-field l))
                                           (fn-article-header-rev-add-line hr l))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-article-parse-lines (append l (list* 13 10 rest)) n b fr cur hr))
            :in-theory (e/d () (fn-article-parse-lines fn-article-new-field
                                fn-article-header-rev-add-line fn-article-wspp))))))

(local
 (defthm fn-spj-split-colon-error-is-non-nil
   (implies (not (equal (car (fn-article-split-colon-aux l r)) :ok))
            (cadr (fn-article-split-colon-aux l r)))
   :hints (("Goal" :in-theory (enable fn-article-split-colon-aux fn-article-error)))))
(local
 (defthm fn-spj-new-field-value-is-non-nil
   (fn-article-line-value (fn-article-new-field l))
   :hints (("Goal" :in-theory (enable fn-article-new-field fn-article-make-field)))))

(local
 (defthm fn-spj-parsed-article-is-a-true-list
   (implies (fn-article-result-okp (fn-article-parse-lines x l b fr cur hr))
            (true-listp (fn-article-result-article (fn-article-parse-lines x l b fr cur hr))))
   :hints (("Goal" :induct (fn-article-parse-lines x l b fr cur hr)
            :in-theory (e/d (fn-article-parse-lines)
                            (fn-article-next-line fn-article-new-field
                             fn-article-add-fold fn-article-header-rev-add-line
                             fn-article-body-crlfp fn-article-fold-linep))))))

(local
 (defthm fn-spj-parsed-article-of-parse-is-a-true-list
   (implies (fn-article-result-okp (fn-article-parse x))
            (true-listp (fn-article-result-article (fn-article-parse x))))
   :hints (("Goal" :use ((:instance fn-spj-parsed-article-is-a-true-list
                                    (l (1+ *fn-article-max-header-lines*)) (b 0)
                                    (fr nil) (cur nil) (hr nil)))
            :in-theory (e/d (fn-article-parse)
                            (fn-article-parse-lines fn-spj-parsed-article-is-a-true-list))))))

(defthm fn-spj-two-lines-then-the-source
  (implies (and (fn-spj-line-freep l1) (true-listp l1) (consp l1)
                (not (fn-article-wspp (car l1)))
                (fn-spj-line-freep l2) (true-listp l2) (consp l2)
                (not (fn-article-wspp (car l2)))
                (fn-article-result-okp
                 (fn-article-parse (append l1 (list* 13 10 (append l2 (list* 13 10 src))))))
                (fn-article-result-okp (fn-article-parse src)))
           (let ((a (fn-article-result-article
                     (fn-article-parse (append l1 (list* 13 10 (append l2 (list* 13 10 src)))))))
                 (s (fn-article-result-article (fn-article-parse src))))
             (and (equal (fn-article-fields a)
                         (list* (fn-article-line-value (fn-article-new-field l1))
                                (fn-article-line-value (fn-article-new-field l2))
                                (fn-article-fields s)))
                  (equal (fn-article-body a) (fn-article-body s)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-spj-parse-lines-of-a-field-line
                            (l l1) (rest (append l2 (list* 13 10 src)))
                            (n (1+ *fn-article-max-header-lines*)) (b 0)
                            (fr nil) (cur nil) (hr nil))
                 (:instance fn-spj-parse-lines-of-a-field-line
                            (l l2) (rest src)
                            (n *fn-article-max-header-lines*) (b (+ (len l1) 2))
                            (fr nil)
                            (cur (fn-article-line-value (fn-article-new-field l1)))
                            (hr (fn-article-header-rev-add-line nil l1)))
                 (:instance fn-spj-parse-lines-after-two-fields
                            (x src) (l (1- *fn-article-max-header-lines*))
                            (b (+ (len l1) 2 (len l2) 2))
                            (f1 (fn-article-line-value (fn-article-new-field l1)))
                            (f2 (fn-article-line-value (fn-article-new-field l2)))
                            (hr (fn-article-header-rev-add-line
                                 (fn-article-header-rev-add-line nil l1) l2))
                            (l2 (1+ *fn-article-max-header-lines*)) (b2 0) (hr2 nil)))
           :in-theory (e/d (fn-article-parse)
                           (fn-article-parse-lines fn-article-new-field binary-append
                            fn-article-header-rev-add-line fn-article-wspp)))))

(local
 (defthm fn-spj-split-colon-error-code
   (implies (not (equal (car (fn-article-split-colon-aux l r)) :ok))
            (equal (cadr (fn-article-split-colon-aux l r)) :invalid-header))
   :hints (("Goal" :in-theory (enable fn-article-split-colon-aux fn-article-error)))))
(local
 (defthm fn-spj-source-header-skips-an-unprojected-field
   (implies (or (not (true-listp x)) (fn-hc-reserved-namep (fn-article-field-name x)))
            (equal (fn-hc-source-header (cons x fs)) (fn-hc-source-header fs)))
   :hints (("Goal" :in-theory (e/d (fn-hc-source-header) (fn-hc-reserved-namep))))))
(local
 (defthm fn-spj-reserved-line-is-unprojected
   (implies (fn-spj-reserved-field-linep l)
            (let ((v (fn-article-line-value (fn-article-new-field l))))
              (or (not (true-listp v)) (fn-hc-reserved-namep (fn-article-field-name v)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-spj-reserved-field-linep fn-article-new-field
                                    fn-article-error fn-article-line-okp fn-article-line-value)
                                   (fn-hc-reserved-namep fn-article-field-name))))))
(local
 (defthm fn-spj-source-header-skips-a-reserved-line
   (implies (fn-spj-reserved-field-linep l)
            (equal (fn-hc-source-header (cons (fn-article-line-value (fn-article-new-field l)) fs))
                   (fn-hc-source-header fs)))
   :hints (("Goal" :use (fn-spj-reserved-line-is-unprojected
                         (:instance fn-spj-source-header-skips-an-unprojected-field
                                    (x (fn-article-line-value (fn-article-new-field l)))))
            :in-theory (theory 'minimal-theory)))))


; KEYSTONE (general form).  Two header lines whose fields carry reserved
; names, put in front of a parsed source, leave the carrier projection of
; the parsed result unchanged.
(defthm fn-hc-authored-source-ignores-two-reserved-lines
  (implies (and (fn-spj-line-freep l1) (true-listp l1) (consp l1)
                (not (fn-article-wspp (car l1)))
                (fn-spj-reserved-field-linep l1)
                (fn-spj-line-freep l2) (true-listp l2) (consp l2)
                (not (fn-article-wspp (car l2)))
                (fn-spj-reserved-field-linep l2)
                (fn-article-result-okp
                 (fn-article-parse (append l1 (list* 13 10 (append l2 (list* 13 10 src))))))
                (fn-article-result-okp (fn-article-parse src)))
           (equal (fn-hc-authored-source
                   (fn-article-result-article
                    (fn-article-parse (append l1 (list* 13 10 (append l2 (list* 13 10 src)))))))
                  (fn-hc-authored-source
                   (fn-article-result-article (fn-article-parse src)))))
  :rule-classes nil
  :hints (("Goal" :use (fn-spj-two-lines-then-the-source
                        (:instance fn-spj-parsed-article-of-parse-is-a-true-list (x src))
                        (:instance fn-spj-parsed-article-of-parse-is-a-true-list
                                   (x (append l1 (list* 13 10 (append l2 (list* 13 10 src))))))
                        (:instance fn-spj-source-header-skips-a-reserved-line
                                   (l l2)
                                   (fs (fn-article-fields (fn-article-result-article
                                                           (fn-article-parse src)))))
                        (:instance fn-spj-source-header-skips-a-reserved-line
                                   (l l1)
                                   (fs (cons (fn-article-line-value (fn-article-new-field l2))
                                             (fn-article-fields (fn-article-result-article
                                                                 (fn-article-parse src)))))))
           :in-theory (e/d (fn-hc-authored-source fn-article-fields fn-article-body)
                           (fn-article-parse fn-hc-source-header binary-append
                            fn-spj-source-header-skips-a-reserved-line
                            fn-spj-reserved-field-linep fn-article-new-field
                            fn-spj-parsed-article-of-parse-is-a-true-list)))))

(local
 (defthm fn-spj-line-freep-of-append
   (equal (fn-spj-line-freep (append a b))
          (and (fn-spj-line-freep a) (fn-spj-line-freep b)))))
(local
 (defthm fn-spj-inj-append-is-append
   (equal (fn-inj-append a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))
(local
 (defthm fn-spj-injection-block-lines
   (equal (append (fn-inj-prefix date msgid agent nil nil) src)
          (append (append *fn-inj-path-field* agent *fn-inj-path-tail*)
                  (list* 13 10 (append (append *fn-inj-injection-info-field* agent)
                                       (list* 13 10 src)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-inj-prefix fn-inj-path-line
                                      fn-inj-injection-info-line)))))
(local
 (defthm fn-spj-path-line-is-reserved
   (fn-spj-reserved-field-linep (append *fn-inj-path-field* agent *fn-inj-path-tail*))
   :hints (("Goal" :in-theory (enable fn-spj-reserved-field-linep fn-article-new-field
                                      fn-article-split-colon-aux)))))
(local
 (defthm fn-spj-injection-info-line-is-reserved
   (fn-spj-reserved-field-linep (append *fn-inj-injection-info-field* agent))
   :hints (("Goal" :in-theory (enable fn-spj-reserved-field-linep fn-article-new-field
                                      fn-article-split-colon-aux)))))

; KEYSTONE (the injection).  This agent's block when it generated neither
; the Message-ID nor the Date is its Path line and its Injection-Info line
; (fn-inj-prefix with both generate flags nil); both name reserved fields,
; so the carrier projection of the parsed stored record is the carrier
; projection of the parsed source -- the octets fn-inj-source-of returns
; (fn-inj-source-of-inverts-the-injection).
(defthm fn-hc-authored-source-of-an-injection-without-generated-fields
  (implies (and (fn-spj-line-freep agent) (true-listp agent)
                (fn-article-result-okp
                 (fn-article-parse (append (fn-inj-prefix date msgid agent nil nil) src)))
                (fn-article-result-okp (fn-article-parse src)))
           (equal (fn-hc-authored-source
                   (fn-article-result-article
                    (fn-article-parse (append (fn-inj-prefix date msgid agent nil nil) src))))
                  (fn-hc-authored-source
                   (fn-article-result-article (fn-article-parse src)))))
  :hints (("Goal"
           :use (fn-spj-injection-block-lines
                 (:instance fn-hc-authored-source-ignores-two-reserved-lines
                            (l1 (append *fn-inj-path-field* agent *fn-inj-path-tail*))
                            (l2 (append *fn-inj-injection-info-field* agent))))
           :in-theory (e/d (fn-article-wspp)
                           (fn-article-parse fn-hc-authored-source fn-inj-prefix
                            fn-spj-reserved-field-linep)))))
