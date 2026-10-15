; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-scalar-readback")

(defthm fn-lbc-msgid-pool-count-frame-by-definition
 (implies (equal (nth 1 new) (nth 1 fn-lbc))
  (equal (fn-lbc-msgid-pool-count new) (fn-lbc-msgid-pool-count fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-msgid-pool-count fn-lbc-msgid-store)))))

(defthm fn-lbc-overview-pool-count-frame-by-definition
 (implies (equal (nth 2 new) (nth 2 fn-lbc))
  (equal (fn-lbc-overview-pool-count new) (fn-lbc-overview-pool-count fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-overview-pool-count fn-lbc-overview-store)))))

(defthm fn-lbc-nov-record-count-frame-by-definition
 (implies (equal (nth 7 new) (nth 7 fn-lbc))
  (equal (fn-lbc-nov-record-count new) (fn-lbc-nov-record-count fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-nov-record-count fn-lbc-nov-store)))))

(defthm fn-lbc-membership-record-count-frame-by-definition
 (implies (equal (nth 6 new) (nth 6 fn-lbc))
  (equal (fn-lbc-membership-record-count new) (fn-lbc-membership-record-count fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-membership-record-count fn-lbc-membership-store)))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-msgid-pool-append 'formals nil (w state)))
        (out (getpropc 'fn-lbc-msgid-pool-append 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-msgid-pool-append fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-msgid-pool-append (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-overview-pool-count-frame-of-msgid-pool-append
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-msgid-pool-append
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-msgid-pool-append
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-msgid-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-overview-pool-append 'formals nil (w state)))
        (out (getpropc 'fn-lbc-overview-pool-append 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-overview-pool-append fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-overview-pool-append (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-overview-pool-append
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-overview-pool-append
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-overview-pool-append
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-overview-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov-texts 'formals nil (w state)))
        (out (getpropc 'fn-lbc-append-nov-texts 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-append-nov-texts fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-append-nov-texts (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-append-nov-texts
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-append-nov-texts
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-append-nov-texts
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-append-nov-texts."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov 'formals nil (w state)))
        (out (getpropc 'fn-lbc-append-nov 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-append-nov fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-append-nov (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-append-nov
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-append-nov
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-append-nov."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-memberships 'formals nil (w state)))
        (out (getpropc 'fn-lbc-append-memberships 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-append-memberships fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-append-memberships (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-append-memberships
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-append-memberships
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-append-memberships."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-escape-store-put 'formals nil (w state)))
        (out (getpropc 'fn-lbc-escape-store-put 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-escape-store-put fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-escape-store-put (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-escape-store-put
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-escape-store-put
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-escape-store-put
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-escape-store-put
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-escape-store-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-first 'formals nil (w state)))
        (out (getpropc 'fn-lbc-number-put-first 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-number-put-first fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-number-put-first (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-number-put-first
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-number-put-first
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-number-put-first
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-number-put-first
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-number-put-first."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-row-seen 'formals nil (w state)))
        (out (getpropc 'fn-lbc-number-put-row-seen 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-number-put-row-seen fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-number-put-row-seen (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-number-put-row-seen
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-number-put-row-seen
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-number-put-row-seen
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-number-put-row-seen
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-number-put-row-seen."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-row 'formals nil (w state)))
        (out (getpropc 'fn-lbc-number-put-row 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-number-put-row fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-number-put-row (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-number-put-row
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-number-put-row
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-number-put-row
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-number-put-row
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-number-put-row."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-summary-put 'formals nil (w state)))
        (out (getpropc 'fn-lbc-summary-put 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-summary-put fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-summary-put (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-summary-put
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-summary-put
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-summary-put
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-summary-put
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-summary-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-rebuild-summaries 'formals nil (w state)))
        (out (getpropc 'fn-lbc-rebuild-summaries 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-rebuild-summaries fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-rebuild-summaries (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-rebuild-summaries
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-rebuild-summaries
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-rebuild-summaries
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-rebuild-summaries
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-rebuild-summaries."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-reserve-slots 'formals nil (w state)))
        (out (getpropc 'fn-lbc-reserve-slots 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-reserve-slots fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-reserve-slots (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-reserve-slots
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-reserve-slots
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-reserve-slots
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-reserve-slots
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-reserve-slots."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-drop-owner 'formals nil (w state)))
        (out (getpropc 'fn-lbc-slot-drop-owner 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-slot-drop-owner fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-slot-drop-owner (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-slot-drop-owner
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-slot-drop-owner
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-slot-drop-owner
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-slot-drop-owner
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-slot-drop-owner."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-put 'formals nil (w state)))
        (out (getpropc 'fn-lbc-slot-put 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-slot-put fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-slot-put (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-slot-put
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-slot-put
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-slot-put
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-slot-put
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-slot-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-insert 'formals nil (w state)))
        (out (getpropc 'fn-lbc-slot-insert 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-slot-insert fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-slot-insert (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-slot-insert
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-slot-insert
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-slot-insert
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-slot-insert
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-slot-insert."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-index-slots 'formals nil (w state)))
        (out (getpropc 'fn-lbc-index-slots 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-index-slots fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
  (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
           (eq (symbol-class 'fn-lbc-index-slots (w state)) :common-lisp-compliant))
   (value `(progn (defthm fn-lbc-msgid-pool-count-frame-of-index-slots
 (equal (fn-lbc-msgid-pool-count  ,value) (fn-lbc-msgid-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-overview-pool-count-frame-of-index-slots
 (equal (fn-lbc-overview-pool-count  ,value) (fn-lbc-overview-pool-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-nov-record-count-frame-of-index-slots
 (equal (fn-lbc-nov-record-count  ,value) (fn-lbc-nov-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-nov-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-membership-record-count-frame-of-index-slots
 (equal (fn-lbc-membership-record-count  ,value) (fn-lbc-membership-record-count  fn-lbc))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-membership-record-count-frame-by-definition (new ,value) ))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
   (er soft 'lb-reader-frame "Missing native producer fn-lbc-index-slots."))))
