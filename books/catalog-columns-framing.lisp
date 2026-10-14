; Stored-section and Xref boundary refinement, including leading CRLF.
(in-package "ACL2")
(include-book "catalog-columns-selector-properties")
(include-book "lb-log-model-properties")

(defthm fn-lb-log-model-unwire-is-wire-inverse
 (equal (fn-lb-log-model-unwire (fn-lb-log-model-wire payload startp) startp) (true-list-fix payload))
 :hints (("Goal" :induct (fn-lb-log-model-wire payload startp)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-wire fn-lb-log-model-unwire true-list-fix binary-append)))))

(local (defthm fn-lbr11-xref-field-null-server-clean
 (fn-nov-clean-fieldp (fn-xref-field nil (fn-xref-pairs article)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-xref-field fn-xref-pairs fn-xref-locations-are-clean fn-xref-pairs-of-is-a-pair-list fn-nov-clean-field-of-append fn-nov-clean-fieldp fn-nov-field-octetp))))))

(local (defthm fn-lbr11-clean-field-octets
 (implies (fn-nov-clean-fieldp bytes) (fn-octet-listp bytes))
 :hints (("Goal" :induct (len bytes) :in-theory (union-theories (theory 'ground-zero) '(fn-nov-clean-fieldp fn-nov-field-octetp fn-octet-listp fn-octetp))))))

(local (defthm fn-lbr11-append-associative
 (equal (append (append a b) c) (append a (append b c)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(binary-append))))))

(local (defthm fn-lbr11-revappend-over-append
 (equal (revappend (append a b) acc) (revappend b (revappend a acc)))
 :hints (("Goal" :induct (revappend a acc) :in-theory (union-theories (theory 'ground-zero) '(revappend binary-append))))))

(local (defthm fn-lbr11-revappend-append-accumulator
 (equal (revappend a (append b c)) (append (revappend a b) c))
 :hints (("Goal" :induct (revappend a b) :in-theory (union-theories (theory 'ground-zero) '(revappend binary-append))))))

(local (defthm fn-lbr11-reverse-append
 (implies (and (true-listp a) (true-listp b))
 (equal (reverse (append a b)) (append (reverse b) (reverse a))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-revappend-append-accumulator (a b) (b nil) (c (revappend a nil))))
 :in-theory (union-theories (theory 'ground-zero) '(reverse fn-lbr11-revappend-over-append binary-append true-listp))))))

(local (defun fn-lbr11-clean-prefix-induct (field rev)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp field) (fn-lbr11-clean-prefix-induct (cdr field) (cons (car field) rev)) rev)))

(local (defthm fn-lbr11-clean-prefix-split-aux
 (implies (fn-nov-clean-fieldp field)
 (equal (fn-nntp-split-article-aux (append field rest) rev)
        (fn-nntp-split-article-aux rest (revappend field rev))))
 :hints (("Goal" :induct (fn-lbr11-clean-prefix-induct field rev)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr11-clean-prefix-induct fn-nov-clean-fieldp fn-nov-field-octetp fn-nntp-split-article-aux binary-append revappend))))))

(local (defthm fn-lbr11-revappend-as-append
 (implies (syntaxp (not (quotep b))) (equal (revappend a b) (append (revappend a nil) b)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-revappend-append-accumulator (b nil) (c b)))
 :in-theory (union-theories (theory 'ground-zero) '(binary-append))))))

(local (defthm fn-lbr11-split-aux-extra-prefix
 (implies (and (true-listp prefix-rev) (true-listp suffix-rev))
 (equal (fn-nntp-split-article-aux bytes (append prefix-rev suffix-rev))
 (let ((split (fn-nntp-split-article-aux bytes prefix-rev)))
 (if (fn-nntp-split-okp split)
     (list :ok (append (reverse suffix-rev) (fn-nntp-split-head split)) (fn-nntp-split-body split))
   (list :error)))))
 :hints (("Goal" :induct (fn-nntp-split-article-aux bytes prefix-rev)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-split-article-aux fn-nntp-split-okp fn-nntp-split-head fn-nntp-split-body
 fn-lbr11-revappend-as-append fn-lbr11-reverse-append fn-lbr11-revappend-over-append fn-lbr11-revappend-append-accumulator fn-lbr11-append-associative binary-append true-listp))))))

(local (defthm fn-lbr11-clean-field-proper
 (implies (fn-nov-clean-fieldp field) (true-listp field))
 :hints (("Goal" :induct (len field) :in-theory (union-theories (theory 'ground-zero) '(fn-nov-clean-fieldp true-listp))))))

(local (defthm fn-lbr11-octet-append
 (implies (and (fn-octet-listp a) (fn-octet-listp b)) (fn-octet-listp (append a b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(fn-octet-listp binary-append))))))

(local (defthm fn-lbr11-double-revappend
 (equal (revappend (revappend a b) c) (revappend b (append a c)))
 :hints (("Goal" :induct (revappend a b) :in-theory (union-theories (theory 'ground-zero) '(revappend binary-append))))))

(local (defthm fn-lbr11-append-nil-proper
 (implies (true-listp a) (equal (append a nil) a))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(binary-append true-listp))))))

(local (defthm fn-lbr11-clean-line-split
 (implies (and (fn-nov-clean-fieldp field) (fn-octet-listp payload))
 (equal (fn-nntp-split-article (append field '(13 10) payload))
  (if (and (consp payload) (consp (cdr payload)) (equal (car payload) 13) (equal (cadr payload) 10))
      (list :ok (append field '(13 10)) (cddr payload))
    (let ((split (fn-nntp-split-article payload)))
     (if (fn-nntp-split-okp split)
         (list :ok (append field '(13 10) (fn-nntp-split-head split)) (fn-nntp-split-body split))
       (list :error))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-split-aux-extra-prefix (bytes payload) (prefix-rev nil) (suffix-rev (append '(10 13) (revappend field nil))))
       (:instance fn-lbr11-clean-prefix-split-aux (rest (append '(13 10) payload)) (rev nil)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-split-article fn-nntp-split-okp fn-nntp-split-head fn-nntp-split-body
 fn-nntp-split-article-aux fn-lbr11-octet-append fn-lbr11-clean-field-octets
 fn-lbr11-clean-field-proper fn-lbr11-append-associative fn-lbr11-revappend-as-append
 fn-lbr11-double-revappend fn-lbr11-append-nil-proper fn-lbr11-reverse-append fn-lbr11-revappend-over-append binary-append reverse true-listp fn-octet-listp fn-octetp))))))

(local (defun fn-lbr11-clean-line-induct (field startp)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp field) (fn-lbr11-clean-line-induct (cdr field) nil) startp)))

(local (defthm fn-lbr11-clean-line-valid
 (implies (fn-nov-clean-fieldp field)
 (equal (fn-nntp-crlf-validp (append field '(13 10) payload) startp)
        (fn-nntp-crlf-validp payload t)))
 :hints (("Goal" :induct (fn-lbr11-clean-line-induct field startp)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr11-clean-line-induct fn-nov-clean-fieldp fn-nov-field-octetp fn-nntp-crlf-validp binary-append))))))

(local (defthm fn-lbr11-clean-field-wire
 (implies (fn-nov-clean-fieldp field)
 (equal (fn-lb-log-model-wire (append field '(13 10) payload) startp)
 (append (if (and startp (equal (car field) 46)) '(46) nil)
         field '(13 10) (fn-lb-log-model-wire payload t))))
 :hints (("Goal" :induct (fn-lbr11-clean-line-induct field startp)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr11-clean-line-induct fn-nov-clean-fieldp fn-nov-field-octetp fn-lb-log-model-wire binary-append fn-lbr11-append-associative))))))

(local (defthm fn-lbr11-split-ok-implies-octets
 (implies (fn-nntp-split-okp (fn-nntp-split-article bytes)) (fn-octet-listp bytes))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-split-article fn-nntp-split-okp))))))

(local (defthm fn-lbr11-framed-as-valid-split
 (equal (fn-nntp-framed-of-bytes bytes)
 (and (fn-octet-listp bytes) (fn-nntp-crlf-validp bytes t)
      (fn-nntp-split-okp (fn-nntp-split-article bytes))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-nntp-crlf-validp-is-crlf-lines-ok) (:instance fn-lbr11-split-ok-implies-octets))
 :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-framed-of-bytes))))))

(local (defthm fn-lbr11-valid-crlf-append
 (equal (fn-nntp-crlf-validp (append prefix '(13 10) rest) startp)
 (and (fn-nntp-crlf-validp (append prefix '(13 10)) startp) (fn-nntp-crlf-validp rest t)))
 :hints (("Goal" :induct (fn-nntp-crlf-validp prefix startp)
 :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-crlf-validp binary-append))))))

(local (defthm fn-lbr11-reverse-cons
 (implies (true-listp b) (equal (reverse (cons a b)) (append (reverse b) (list a))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(reverse revappend fn-lbr11-revappend-as-append)))) ))

(local (defthm fn-lbr11-valid-at-crlf-once
 (implies (and (syntaxp (not (quotep bytes))) (consp bytes) (consp (cdr bytes)) (equal (car bytes) 13) (equal (cadr bytes) 10))
 (equal (fn-nntp-crlf-validp (append prefix bytes) startp)
 (and (fn-nntp-crlf-validp (append prefix '(13 10)) startp) (fn-nntp-crlf-validp (cddr bytes) t))))
 :hints (("Goal" :do-not-induct t
 :cases ((equal bytes (cons 13 (cons 10 (cddr bytes)))))
 :use ((:instance fn-lbr11-valid-crlf-append (rest (cddr bytes))))
 :in-theory (union-theories (theory 'ground-zero) '(binary-append))))))

(local (defthm fn-lbr11-split-aux-valid-parts
 (implies (and (true-listp rev)
 (fn-nntp-split-okp (fn-nntp-split-article-aux bytes rev))
 (fn-nntp-crlf-validp (append (reverse rev) bytes) t))
 (and (fn-nntp-crlf-validp (fn-nntp-split-head (fn-nntp-split-article-aux bytes rev)) t)
      (fn-nntp-crlf-validp (fn-nntp-split-body (fn-nntp-split-article-aux bytes rev)) t)))
 :hints (("Goal" :induct (fn-nntp-split-article-aux bytes rev)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-split-article-aux fn-nntp-split-okp fn-nntp-split-head fn-nntp-split-body
 fn-lbr11-reverse-cons fn-lbr11-reverse-append fn-lbr11-valid-at-crlf-once fn-lbr11-valid-crlf-append
 fn-lbr11-append-associative fn-nntp-crlf-validp binary-append true-listp))))))

(local (defthm fn-lbr11-octet-revappend
 (implies (and (fn-octet-listp a) (fn-octet-listp b)) (fn-octet-listp (revappend a b)))
 :hints (("Goal" :induct (revappend a b) :in-theory (union-theories (theory 'ground-zero) '(revappend fn-octet-listp))))))

(local (defthm fn-lbr11-split-aux-octets
 (implies (and (fn-octet-listp bytes) (fn-octet-listp rev) (fn-nntp-split-okp (fn-nntp-split-article-aux bytes rev)))
 (and (fn-octet-listp (fn-nntp-split-head (fn-nntp-split-article-aux bytes rev)))
      (fn-octet-listp (fn-nntp-split-body (fn-nntp-split-article-aux bytes rev)))))
 :hints (("Goal" :induct (fn-nntp-split-article-aux bytes rev)
 :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-split-article-aux fn-nntp-split-okp fn-nntp-split-head fn-nntp-split-body fn-octet-listp reverse fn-lbr11-octet-revappend fn-lbr11-octet-append))))))

(local (defthm fn-lbr11-octet-nil (fn-octet-listp nil)
 :hints (("Goal" :in-theory (enable fn-octet-listp)))))

(local (defthm fn-lbr11-framed-section-exists
 (implies (fn-nntp-framed-of-bytes payload)
 (equal (car (fn-nntp-section-of-bytes payload kind)) :ok))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-split-aux-valid-parts (bytes payload) (rev nil))
       (:instance fn-lbr11-split-aux-octets (bytes payload) (rev nil))
       (:instance fn-nntp-crlf-validp-is-crlf-lines-ok (bytes (fn-nntp-split-head (fn-nntp-split-article-aux payload nil))))
       (:instance fn-nntp-crlf-validp-is-crlf-lines-ok (bytes (fn-nntp-split-body (fn-nntp-split-article-aux payload nil))))
       (:instance fn-nntp-crlf-validp-is-crlf-lines-ok (bytes payload)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr11-framed-as-valid-split fn-nntp-split-article fn-nntp-section-of-bytes fn-lbr11-octet-nil))))))

(local (defthm fn-lbr11-octet-crlf
 (equal (fn-octet-listp (cons 13 (cons 10 payload))) (fn-octet-listp payload))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-octet-listp fn-octetp))))))

(local (defthm fn-lbr11-clean-line-framed
 (implies (and (fn-nov-clean-fieldp field) (fn-nntp-framed-of-bytes payload))
 (fn-nntp-framed-of-bytes (append field '(13 10) payload)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-clean-line-split) (:instance fn-lbr11-clean-line-valid (startp t)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr11-framed-as-valid-split fn-nntp-split-okp fn-lbr11-clean-line-valid
 fn-lbr11-octet-append fn-lbr11-clean-field-octets fn-lbr11-octet-crlf))))))

(local (defthm fn-lbr11-clean-prefix-stuffed-head
 (implies (and (fn-nov-clean-fieldp field) (not (equal (car field) 46)) (fn-nntp-framed-of-bytes payload))
 (equal (fn-nntp-stuffed-section :head (append field '(13 10) payload))
 (append field '(13 10)
   (if (and (consp payload) (consp (cdr payload)) (equal (car payload) 13) (equal (cadr payload) 10))
       nil (fn-nntp-stuffed-section :head payload)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-clean-line-split)
       (:instance fn-lbr11-clean-line-framed)
       (:instance fn-lbr11-framed-section-exists (kind :head))
       (:instance fn-lbr11-framed-section-exists (kind :head) (payload (append field '(13 10) payload)))
       (:instance fn-lb-log-model-stuffed-head-is-wire)
       (:instance fn-lb-log-model-stuffed-head-is-wire (payload (append field '(13 10) payload)))
       (:instance fn-lbr11-clean-field-wire (startp t) (payload (fn-nntp-split-head (fn-nntp-split-article payload))))
       (:instance fn-lbr11-clean-field-wire (startp t) (payload nil)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr11-framed-as-valid-split fn-nntp-split-head fn-nntp-split-body
 fn-la-payload-wire fn-lb-log-model-wire binary-append))))))

(local (defthm fn-lbr11-clean-prefix-stuffed-body
 (implies (and (fn-nov-clean-fieldp field) (fn-nntp-framed-of-bytes payload))
 (equal (fn-nntp-stuffed-section :body (append field '(13 10) payload))
   (if (and (consp payload) (consp (cdr payload)) (equal (car payload) 13) (equal (cadr payload) 10))
       (fn-la-payload-wire (cddr payload)) (fn-nntp-stuffed-section :body payload))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-clean-line-split)
       (:instance fn-lbr11-clean-line-framed)
       (:instance fn-lbr11-framed-section-exists (kind :body))
       (:instance fn-lbr11-framed-section-exists (kind :body) (payload (append field '(13 10) payload)))
       (:instance fn-lb-log-model-stuffed-body-is-wire)
       (:instance fn-lb-log-model-stuffed-body-is-wire (payload (append field '(13 10) payload))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr11-framed-as-valid-split fn-nntp-split-head fn-nntp-split-body))))))

(local (defthm fn-lbr11-leading-split-head
 (implies (and (fn-nntp-split-okp (fn-nntp-split-article payload))
 (consp payload) (consp (cdr payload)) (equal (car payload) 13) (equal (cadr payload) 10))
 (and (consp (fn-nntp-split-head (fn-nntp-split-article payload)))
 (consp (cdr (fn-nntp-split-head (fn-nntp-split-article payload))))
 (equal (car (fn-nntp-split-head (fn-nntp-split-article payload))) 13)
 (equal (cadr (fn-nntp-split-head (fn-nntp-split-article payload))) 10)))
 :hints (("Goal" :do-not-induct t
 :cases ((equal payload (cons 13 (cons 10 (cddr payload)))))
 :use ((:instance fn-lbr11-clean-line-split (field nil) (payload (cddr payload)))
       (:instance fn-lbr11-split-ok-implies-octets (bytes payload)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-split-okp fn-nntp-split-head fn-lbr11-octet-nil fn-nov-clean-fieldp fn-octet-listp binary-append))))))

(local (defthm fn-lbr11-leading-wire
 (implies (and (consp bytes) (consp (cdr bytes)) (equal (car bytes) 13) (equal (cadr bytes) 10))
 (equal (fn-lb-log-model-wire bytes startp) (cons 13 (cons 10 (fn-lb-log-model-wire (cddr bytes) t)))))
 :hints (("Goal" :expand ((fn-lb-log-model-wire bytes startp) (fn-lb-log-model-wire (cdr bytes) nil))
 :in-theory (union-theories (theory 'ground-zero) '(binary-append))))))

(local (defthm fn-lbr11-leading-stuffed-head
 (implies (and (fn-nntp-framed-of-bytes payload)
 (consp payload) (consp (cdr payload)) (equal (car payload) 13) (equal (cadr payload) 10))
 (and (consp (fn-nntp-stuffed-section :head payload))
 (consp (cdr (fn-nntp-stuffed-section :head payload)))
 (equal (car (fn-nntp-stuffed-section :head payload)) 13)
 (equal (cadr (fn-nntp-stuffed-section :head payload)) 10)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-leading-split-head)
       (:instance fn-lbr11-leading-wire (bytes (fn-nntp-split-head (fn-nntp-split-article payload))) (startp t))
       (:instance fn-lbr11-framed-section-exists (kind :head))
       (:instance fn-lb-log-model-stuffed-head-is-wire))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr11-framed-as-valid-split fn-la-payload-wire binary-append))))))

(local (defthm fn-lbr11-leading-body-decomposition
 (implies (and (fn-nntp-framed-of-bytes payload)
 (consp payload) (consp (cdr payload)) (equal (car payload) 13) (equal (cadr payload) 10))
 (equal (fn-la-payload-wire (cddr payload))
 (append (cddr (fn-nntp-stuffed-section :head payload)) '(13 10) (fn-nntp-stuffed-section :body payload))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-leading-stuffed-head)
       (:instance fn-lbr11-leading-wire (bytes payload) (startp t))
       (:instance fn-lb-log-model-wire-split-decomposition)
       (:instance fn-lbr11-framed-section-exists (kind :head))
       (:instance fn-lbr11-framed-section-exists (kind :body))
       (:instance fn-lb-log-model-stuffed-head-is-wire)
       (:instance fn-lb-log-model-stuffed-body-is-wire))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr11-framed-as-valid-split fn-la-payload-wire binary-append))))))

(local (defthm fn-lbr11-clean-line-framed-iff
 (implies (and (fn-nov-clean-fieldp field) (fn-nntp-split-okp (fn-nntp-split-article payload)))
 (equal (fn-nntp-framed-of-bytes (append field '(13 10) payload)) (fn-nntp-framed-of-bytes payload)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-clean-line-framed)
       (:instance fn-lbr11-clean-line-valid (startp t))
       (:instance fn-lbr11-split-ok-implies-octets (bytes payload)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr11-framed-as-valid-split fn-nntp-split-okp))))))

(local (defthm fn-lbr11-clean-prefix-stuffed-article
 (implies (and (fn-nov-clean-fieldp field) (not (equal (car field) 46)) (fn-nntp-framed-of-bytes payload))
 (equal (fn-nntp-stuffed-section :article (append field '(13 10) payload))
 (append field '(13 10) (fn-nntp-stuffed-section :article payload))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-clean-line-framed)
       (:instance fn-lbr11-framed-section-exists (kind :article))
       (:instance fn-lbr11-framed-section-exists (kind :article) (payload (append field '(13 10) payload)))
       (:instance fn-lb-log-model-stuffed-article-is-wire)
       (:instance fn-lb-log-model-stuffed-article-is-wire (payload (append field '(13 10) payload)))
       (:instance fn-lbr11-clean-field-wire (startp t)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-la-payload-wire))))))

(local (defthm fn-lbr11-clean-prefix-stuffed-body-shift
 (implies (and (fn-nov-clean-fieldp field) (fn-nntp-framed-of-bytes payload))
 (equal (fn-nntp-stuffed-section :body (append field '(13 10) payload))
 (append (fn-lb-xref-shift-prefix payload) (fn-nntp-stuffed-section :body payload))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-clean-prefix-stuffed-body) (:instance fn-lbr11-leading-body-decomposition))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-xref-shift-prefix fn-lbr11-append-associative))))))

(local (defthm fn-lbr11-append-crlf-consp
 (consp (append x '(13 10)))
 :hints (("Goal" :induct (len x) :in-theory (union-theories (theory 'ground-zero) '(binary-append))))))

(local (defthm fn-lbr11-shift-prefix-present
 (iff (fn-lb-xref-shift-prefix payload)
 (and (consp payload) (consp (cdr payload)) (equal (car payload) 13) (equal (cadr payload) 10)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-xref-shift-prefix fn-lbr11-append-crlf-consp))))))

(local (defthm fn-lbr11-xref-field-starts-x
 (and (consp (fn-xref-field server pairs)) (equal (car (fn-xref-field server pairs)) 88))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-xref-field binary-append))))))

(local (defthm fn-lbr11-nonzero-first-not-tombstone
 (implies (and (consp bytes) (not (equal (car bytes) 0))) (not (fn-rcl-tombstonep bytes)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-rcl-tombstonep fn-rcl-prefixp))))))

(local (defthm fn-lbr11-xref-prefixed-not-tombstone
 (not (fn-rcl-tombstonep (append (fn-xref-field server pairs) '(13 10) payload)))
 :hints (("Goal" :use ((:instance fn-lbr11-nonzero-first-not-tombstone (bytes (append (fn-xref-field server pairs) '(13 10) payload))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-xref-field binary-append))))))

(local (defthm fn-lbr11-served-payload-response-ok-unchanged
 (implies (or (null server) (fn-xref-serverp server))
 (equal (fn-nntp-response-okp-of-bytes article (fn-rcompat-served-payload-of-bytes server article payload) kind)
        (fn-nntp-response-okp-of-bytes article payload kind)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-xref-prefixed-not-tombstone (pairs (fn-xref-pairs article)))
       (:instance fn-lbr11-clean-line-framed-iff (field (fn-xref-field server (fn-xref-pairs article))))
       (:instance fn-lbr11-framed-section-exists)
       (:instance fn-lbr11-framed-section-exists (payload (append (fn-xref-field server (fn-xref-pairs article)) '(13 10) payload))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-rcompat-served-payload-of-bytes fn-nntp-response-okp-of-bytes
 fn-xref-field-is-clean fn-lbr11-xref-field-null-server-clean))))))

(local (defthm fn-lbr11-response-of-bytes-stuffed
 (equal (fn-nntp-article-response-of-bytes session article bytes number kind updatep group)
 (cond ((not (fn-nntp-article-idp article)) (fn-nntp-single session "503 stored article identifier unavailable"))
       ((fn-rcl-tombstonep bytes) (fn-nntp-single session (if updatep "423 article reclaimed" "430 article reclaimed")))
       ((equal kind :stat) (fn-nntp-make-result (if updatep (fn-nntp-set-cursor session group number) session)
        (list (fn-nntp-reply-effect (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))))))
       ((and (fn-nntp-framed-of-bytes bytes) (equal (car (fn-nntp-section-of-bytes bytes kind)) :ok))
        (fn-nntp-make-result (if updatep (fn-nntp-set-cursor session group number) session)
        (list (fn-nntp-reply-effect (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))
         (fn-nntp-stuffed-section kind bytes) '(46 13 10))))))
       (t (fn-nntp-single session "503 stored article framing unavailable"))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-article-response-of-bytes fn-nntp-stuffed-section))))))

(defthm fn-lb-rcompat-typed-reply-is-prefixed-response
 (implies (or (null server) (fn-xref-serverp server))
 (equal (fn-rcompat-article-reply-exec session article number kind updatep group server fn-arena)
 (fn-nntp-article-response-of-bytes session article
 (fn-rcompat-served-payload-of-bytes server article (fn-nntp-article-bytes article fn-arena)) number kind updatep group)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-nntp-response-of-bytes-session
 (bytes (fn-rcompat-served-payload-of-bytes server article (fn-nntp-article-bytes article fn-arena)))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-rcompat-article-reply-exec fn-lbr11-served-payload-response-ok-unchanged)))))

(local (defthm fn-lbr11-framed-has-split
 (implies (fn-nntp-framed-of-bytes payload) (fn-nntp-split-okp (fn-nntp-split-article payload)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-framed-of-bytes))))))

(local (defthm fn-lbr11-served-payload-framed-unchanged
 (implies (or (null server) (fn-xref-serverp server))
 (equal (fn-nntp-framed-of-bytes (fn-rcompat-served-payload-of-bytes server article payload)) (fn-nntp-framed-of-bytes payload)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-clean-line-framed-iff (field (fn-xref-field server (fn-xref-pairs article)))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-rcompat-served-payload-of-bytes fn-xref-field-is-clean fn-lbr11-xref-field-null-server-clean))))))

(defthm fn-lb-rcompat-served-payload-preserves-tombstone
 (equal (fn-rcl-tombstonep (fn-rcompat-served-payload-of-bytes server article payload)) (fn-rcl-tombstonep payload))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-xref-prefixed-not-tombstone (pairs (fn-xref-pairs article))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-rcompat-served-payload-of-bytes)))))

(local (defthm fn-lbr11-other-kind-is-body
 (implies (and (not (equal kind :article)) (not (equal kind :head)))
 (equal (fn-nntp-stuffed-section kind payload) (fn-nntp-stuffed-section :body payload)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-stuffed-section fn-nntp-section-of-bytes))))))

(local (defthm fn-lbr11-served-stuffed-is-resident-section
 (implies (and (or (null server) (fn-xref-serverp server)) (fn-nntp-framed-of-bytes payload) (not (fn-rcl-tombstonep payload)))
 (equal (fn-nntp-stuffed-section kind (fn-rcompat-served-payload-of-bytes server article payload))
 (let* ((section-kind (if (member-equal kind '(:article :head)) kind :body))
                 (shift (and (not (equal section-kind :article)) (consp (fn-xref-pairs article)) (fn-lb-xref-shift-prefix payload)))
                 (section (if (and shift (equal section-kind :head)) nil (fn-nntp-stuffed-section section-kind payload)))
                 (section (if (and shift (equal section-kind :body)) (append shift section) section))
                 (prefix (if (and (not (equal section-kind :body)) (consp (fn-xref-pairs article)))
                         (append (fn-xref-field server (fn-xref-pairs article)) '(13 10)) nil)))
        (append prefix section))))
 :hints (("Goal" :do-not-induct t :cases ((equal kind :article) (equal kind :head))
 :use ((:instance fn-lbr11-clean-prefix-stuffed-article (field (fn-xref-field server (fn-xref-pairs article))))
       (:instance fn-lbr11-clean-prefix-stuffed-head (field (fn-xref-field server (fn-xref-pairs article))))
       (:instance fn-lbr11-clean-prefix-stuffed-body-shift (field (fn-xref-field server (fn-xref-pairs article))))
       (:instance fn-lbr11-xref-field-starts-x (pairs (fn-xref-pairs article)))
       (:instance fn-lbr11-shift-prefix-present)
       (:instance fn-lbr11-other-kind-is-body)
       (:instance fn-lbr11-other-kind-is-body (payload (append (fn-xref-field server (fn-xref-pairs article)) '(13 10) payload))))

 :in-theory (union-theories (theory 'ground-zero)
 '(fn-rcompat-served-payload-of-bytes fn-lbr11-framed-has-split member-equal
 fn-xref-field-is-clean fn-lbr11-xref-field-null-server-clean fn-lbr11-append-associative))))))

(defthm fn-lb-rcompat-prefixed-response-is-resident-construction
 (implies (or (null server) (fn-xref-serverp server))
 (equal (fn-nntp-article-response-of-bytes session article (fn-rcompat-served-payload-of-bytes server article payload) number kind updatep group)
 (cond ((not (fn-nntp-article-idp article)) (fn-nntp-single session "503 stored article identifier unavailable"))
       ((fn-rcl-tombstonep payload) (fn-nntp-single session (if updatep "423 article reclaimed" "430 article reclaimed")))
       ((equal kind :stat) (fn-nntp-make-result (if updatep (fn-nntp-set-cursor session group number) session)
        (list (fn-nntp-reply-effect (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))))))
       ((not (fn-nntp-framed-of-bytes payload)) (fn-nntp-single session "503 stored article framing unavailable"))
       (t (let* ((section-kind (if (member-equal kind '(:article :head)) kind :body))
                 (shift (and (not (equal section-kind :article)) (consp (fn-xref-pairs article)) (fn-lb-xref-shift-prefix payload)))
                 (section (if (and shift (equal section-kind :head)) nil (fn-nntp-stuffed-section section-kind payload)))
                 (section (if (and shift (equal section-kind :body)) (append shift section) section))
                 (prefix (if (and (not (equal section-kind :body)) (consp (fn-xref-pairs article)))
                         (append (fn-xref-field server (fn-xref-pairs article)) '(13 10)) nil)))
        (fn-nntp-make-result (if updatep (fn-nntp-set-cursor session group number) session)
        (list (fn-nntp-reply-effect (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article)) prefix section '(46 13 10))))))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr11-served-payload-framed-unchanged)
       (:instance fn-lb-rcompat-served-payload-preserves-tombstone)
       (:instance fn-lbr11-framed-section-exists (payload (fn-rcompat-served-payload-of-bytes server article payload)))
       (:instance fn-lbr11-served-stuffed-is-resident-section))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr11-response-of-bytes-stuffed fn-lbr11-append-associative)))))
