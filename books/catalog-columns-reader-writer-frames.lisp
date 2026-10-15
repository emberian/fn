; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-flag-properties")

(make-event
 (let* ((fs (getpropc 'fn-lbc-msgid-pool-append 'formals nil (w state)))
        (out (getpropc 'fn-lbc-msgid-pool-append 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-msgid-pool-append fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-msgid-pool-append (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-msgid-pool-append
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-msgid-pool-append
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-msgid-pool-append
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-msgid-pool-append
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-msgid-pool-append
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-msgid-pool-append
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-msgid-pool-append
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-msgid-pool-append
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-msgid-pool-append
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-msgid-pool-append
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-msgid-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-overview-pool-append 'formals nil (w state)))
        (out (getpropc 'fn-lbc-overview-pool-append 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-overview-pool-append fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-overview-pool-append (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-overview-pool-append
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-overview-pool-append
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-overview-pool-append
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-overview-pool-append
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-overview-pool-append
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-overview-pool-append
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-overview-pool-append
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-overview-pool-append
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-overview-pool-append
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-overview-pool-append
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-overview-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov-texts 'formals nil (w state)))
        (out (getpropc 'fn-lbc-append-nov-texts 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-append-nov-texts fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-append-nov-texts (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-append-nov-texts
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-append-nov-texts
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-append-nov-texts
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-append-nov-texts
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-append-nov-texts
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-append-nov-texts
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-append-nov-texts
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-append-nov-texts
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-append-nov-texts
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-append-nov-texts
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-append-nov-texts."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov 'formals nil (w state)))
        (out (getpropc 'fn-lbc-append-nov 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-append-nov fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-append-nov (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-append-nov
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-append-nov
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-append-nov
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-append-nov
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-append-nov
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-append-nov
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-append-nov
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-append-nov
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-append-nov
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-append-nov
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-append-nov."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-memberships 'formals nil (w state)))
        (out (getpropc 'fn-lbc-append-memberships 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-append-memberships fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-append-memberships (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-append-memberships
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-append-memberships
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-append-memberships
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-append-memberships
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-append-memberships
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-append-memberships
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-append-memberships
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-append-memberships
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-append-memberships
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-append-memberships
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-append-memberships."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-escape-store-put 'formals nil (w state)))
        (out (getpropc 'fn-lbc-escape-store-put 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-escape-store-put fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-escape-store-put (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-escape-store-put
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-escape-store-put
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-escape-store-put
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-escape-store-put
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-escape-store-put
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-escape-store-put
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-escape-store-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-first 'formals nil (w state)))
        (out (getpropc 'fn-lbc-number-put-first 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-number-put-first fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-number-put-first (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-number-put-first
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-number-put-first
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-number-put-first
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-number-put-first
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-number-put-first
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-number-put-first
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-number-put-first
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-number-put-first
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-number-put-first
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-number-put-first
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-number-put-first."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-row-seen 'formals nil (w state)))
        (out (getpropc 'fn-lbc-number-put-row-seen 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-number-put-row-seen fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-number-put-row-seen (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-number-put-row-seen
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-number-put-row-seen
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-number-put-row-seen
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-number-put-row-seen
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-number-put-row-seen
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-number-put-row-seen
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-number-put-row-seen
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-number-put-row-seen
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-number-put-row-seen
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-number-put-row-seen
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-number-put-row-seen."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-row 'formals nil (w state)))
        (out (getpropc 'fn-lbc-number-put-row 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-number-put-row fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-number-put-row (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-number-put-row
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-number-put-row
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-number-put-row
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-number-put-row
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-number-put-row
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-number-put-row
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-number-put-row
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-number-put-row
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-number-put-row
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-number-put-row
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-number-put-row."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-summary-put 'formals nil (w state)))
        (out (getpropc 'fn-lbc-summary-put 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-summary-put fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-summary-put (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-summary-put
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-summary-put
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-summary-put
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-summary-put
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-summary-put
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-summary-put
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-summary-put
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-summary-put
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-summary-put
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-summary-put
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-summary-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-rebuild-summaries 'formals nil (w state)))
        (out (getpropc 'fn-lbc-rebuild-summaries 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-rebuild-summaries fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-rebuild-summaries (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-rebuild-summaries
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-rebuild-summaries
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-rebuild-summaries
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-rebuild-summaries
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-rebuild-summaries
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-rebuild-summaries
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-rebuild-summaries
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-rebuild-summaries
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-rebuild-summaries
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-rebuild-summaries
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-rebuild-summaries."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-reserve-slots 'formals nil (w state)))
        (out (getpropc 'fn-lbc-reserve-slots 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-reserve-slots fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-reserve-slots (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-reserve-slots
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-reserve-slots
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-reserve-slots
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-reserve-slots
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-reserve-slots
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-store-get-of-reserve-slots
 (equal (fn-lbc-escape-store-get read-i ,value) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-escape-of-reserve-slots
 (equal (fn-lbc-escape read-i read-field ,value) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-value-of-reserve-slots
 (equal (fn-lbc-value read-i read-field ,value) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-value-of-reserve-slots
 (equal (fn-lbc-directory-value read-i read-field ,value) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-value-frame-by-definition (new ,value) (i read-i) (field read-field)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-reserve-slots
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-reserve-slots."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-drop-owner 'formals nil (w state)))
        (out (getpropc 'fn-lbc-slot-drop-owner 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-slot-drop-owner fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-slot-drop-owner (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-count-of-slot-drop-owner
 (equal (fn-lbc-count  ,value) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-word-of-slot-drop-owner
 (equal (fn-lbc-word read-field read-i ,value) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-directory-field-of-slot-drop-owner
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc0-of-slot-drop-owner
 (equal (fn-lbc-loc0 read-i ,value) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc0-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-loc1-of-slot-drop-owner
 (equal (fn-lbc-loc1 read-i ,value) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-loc1-frame-by-definition (new ,value) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-flag-of-slot-drop-owner
 (equal (fn-lbc-flag read-i read-bit ,value) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new ,value) (i read-i) (bit read-bit)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-slot-drop-owner."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-put 'formals nil (w state)))
        (out (getpropc 'fn-lbc-slot-put 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-slot-put fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-slot-put (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-directory-field-of-slot-put
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-slot-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-insert 'formals nil (w state)))
        (out (getpropc 'fn-lbc-slot-insert 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-slot-insert fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-slot-insert (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-directory-field-of-slot-insert
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-slot-insert."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-index-slots 'formals nil (w state)))
        (out (getpropc 'fn-lbc-index-slots 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-index-slots fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-index-slots (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-directory-field-of-index-slots
 (equal (fn-lbc-directory-field read-field read-i ,value) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new ,value) (field read-field) (i read-i)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-index-slots."))))
