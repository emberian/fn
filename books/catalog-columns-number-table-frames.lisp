; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-number-map-effects")

(make-event
 (let* ((fs (getpropc 'fn-lbc-msgid-pool-append 'formals nil (w state)))
        (out (getpropc 'fn-lbc-msgid-pool-append 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-msgid-pool-append fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-msgid-pool-append (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-msgid-pool-append
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-msgid-pool-append
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-msgid-pool-append
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-msgid-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-overview-pool-append 'formals nil (w state)))
        (out (getpropc 'fn-lbc-overview-pool-append 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-overview-pool-append fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-overview-pool-append (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-overview-pool-append
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-overview-pool-append
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-overview-pool-append
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-overview-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov-texts 'formals nil (w state)))
        (out (getpropc 'fn-lbc-append-nov-texts 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-append-nov-texts fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-append-nov-texts (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-append-nov-texts
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-append-nov-texts
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-append-nov-texts
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-append-nov-texts."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov 'formals nil (w state)))
        (out (getpropc 'fn-lbc-append-nov 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-append-nov fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-append-nov (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-append-nov
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-append-nov
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-append-nov
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-append-nov."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-memberships 'formals nil (w state)))
        (out (getpropc 'fn-lbc-append-memberships 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-append-memberships fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-append-memberships (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-append-memberships
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-append-memberships
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-append-memberships
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-append-memberships."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-escape-store-put 'formals nil (w state)))
        (out (getpropc 'fn-lbc-escape-store-put 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-escape-store-put fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-escape-store-put (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-escape-store-put
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-escape-store-put
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-escape-store-put
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-escape-store-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-reserve-slots 'formals nil (w state)))
        (out (getpropc 'fn-lbc-reserve-slots 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-reserve-slots fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-reserve-slots (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-reserve-slots
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-reserve-slots
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-reserve-slots
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-reserve-slots."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-drop-owner 'formals nil (w state)))
        (out (getpropc 'fn-lbc-slot-drop-owner 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-slot-drop-owner fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-slot-drop-owner (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-slot-drop-owner
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-slot-drop-owner
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-slot-drop-owner
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-slot-drop-owner."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-put 'formals nil (w state)))
        (out (getpropc 'fn-lbc-slot-put 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-slot-put fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-slot-put (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-slot-put
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-slot-put
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-slot-put
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-slot-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-insert 'formals nil (w state)))
        (out (getpropc 'fn-lbc-slot-insert 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-slot-insert fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-slot-insert (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-slot-insert
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-slot-insert
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-slot-insert
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-slot-insert."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-index-slots 'formals nil (w state)))
        (out (getpropc 'fn-lbc-index-slots 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-index-slots fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-index-slots (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-index-slots
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-index-slots
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-index-slots
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-index-slots."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-row 'formals nil (w state)))
        (out (getpropc 'fn-lbc-append-row 'stobjs-out nil (w state)))
        (call (cons 'fn-lbc-append-row fs))
        (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out)
          (not (intersection-eq fs '(read-group read-number read-field read-rows)))
          (eq (symbol-class 'fn-lbc-append-row (w state)) :common-lisp-compliant))
  (value `(progn (defthm fn-lbc-number-get-of-append-row
 (equal (fn-lbc-number-get read-group read-number ,value) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-get-frame-by-definition (new ,value) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-row-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-summary-word-of-append-row
 (equal (fn-lbc-summary-word read-group read-field ,value) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-word-frame-by-definition (new ,value) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-row-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))) (defthm fn-lbc-tables-corr-of-append-row
 (equal (fn-lbc-tables-corr ,value read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-tables-corr-frame-by-definition (new ,value) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-row-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))))
  (er soft 'lb-number-frame "Missing native producer or reader variable capture: fn-lbc-append-row."))))

(local (defthm fn-lbnf-metadata-field
 (implies (natp k)
 (equal (nth k (update-fn-lbc-summary-groups groups fn-lbc)) (if (equal k 8) groups (nth k fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(update-fn-lbc-summary-groups fn-dm-nth-update-nth))))))

(defthm fn-lbc-number-get-of-summary-groups-update
 (equal (fn-lbc-number-get read-group read-number (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-number-get-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (group read-group) (number read-number)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbnf-metadata-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-summary-word-of-summary-groups-update
 (equal (fn-lbc-summary-word read-group read-field (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-summary-word-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (group read-group) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbnf-metadata-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-tables-corr-of-summary-groups-update
 (equal (fn-lbc-tables-corr (update-fn-lbc-summary-groups groups fn-lbc) read-rows) (fn-lbc-tables-corr fn-lbc read-rows))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-tables-corr-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (rows read-rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbnf-metadata-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-number-store-of-clear-columns
 (equal (fn-lbc-number-store (fn-lbc-clear-columns fn-lbc)) '(nil nil nil))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-clear-columns fn-lbc-number-store fn-lbc-escape-store-clear fn-dmap-clear fn-dmap$a-clear
 fn-dm-nth-update-nth update-fn-lbc-row-store update-fn-lbc-msgid-store update-fn-lbc-overview-store update-fn-lbc-number-store update-fn-lbc-slot-store update-fn-lbc-directory-store update-fn-lbc-membership-store update-fn-lbc-nov-store update-fn-lbc-summary-groups update-fn-lbc-slot-escape-keys nth)))))

(defthm fn-lbc-number-get-of-clear-columns
 (equal (fn-lbc-number-get group number (fn-lbc-clear-columns fn-lbc)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-number-get fn-lbc-number-store-of-clear-columns fn-dmap-get fn-dmap$a-get
 nth hons-assoc-equal assoc-equal)))))
