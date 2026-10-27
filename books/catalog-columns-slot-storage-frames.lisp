; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-index-refinement")

(defun-nx fn-lb-slot-store-model (fn-lbc) (nth 4 fn-lbc))

(local (defthm fn-lbsst-slot-table-frame
 (implies (equal (nth 4 new) (nth 4 fn-lbc))
 (equal (fn-lb-slot-store-model new) (fn-lb-slot-store-model fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-slot-store-model))))))

(local (defthm fn-lbsst-owner-keys-frame
 (implies (equal (nth 10 new) (nth 10 fn-lbc))
 (equal (fn-lbc-slot-escape-keys new) (fn-lbc-slot-escape-keys fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-slot-escape-keys))))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-msgid-pool-append 'formals nil (w state))) (out (getpropc 'fn-lbc-msgid-pool-append 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-msgid-pool-append fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-msgid-pool-append (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-msgid-pool-append (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-msgid-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-overview-pool-append 'formals nil (w state))) (out (getpropc 'fn-lbc-overview-pool-append 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-overview-pool-append fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-overview-pool-append (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-overview-pool-append (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-overview-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov-texts 'formals nil (w state))) (out (getpropc 'fn-lbc-append-nov-texts 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-nov-texts fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-nov-texts (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-append-nov-texts (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-nov-texts."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov 'formals nil (w state))) (out (getpropc 'fn-lbc-append-nov 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-nov fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-nov (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-append-nov (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-nov."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-memberships 'formals nil (w state))) (out (getpropc 'fn-lbc-append-memberships 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-memberships fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-memberships (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-append-memberships (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-memberships."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-escape-store-put 'formals nil (w state))) (out (getpropc 'fn-lbc-escape-store-put 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-escape-store-put fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-escape-store-put (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-escape-store-put (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-escape-store-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-first 'formals nil (w state))) (out (getpropc 'fn-lbc-number-put-first 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-number-put-first fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-number-put-first (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-number-put-first (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-number-put-first."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-row-seen 'formals nil (w state))) (out (getpropc 'fn-lbc-number-put-row-seen 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-number-put-row-seen fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-number-put-row-seen (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-number-put-row-seen (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-number-put-row-seen."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-row 'formals nil (w state))) (out (getpropc 'fn-lbc-number-put-row 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-number-put-row fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-number-put-row (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-number-put-row (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-number-put-row."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-summary-put 'formals nil (w state))) (out (getpropc 'fn-lbc-summary-put 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-summary-put fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-summary-put (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-summary-put (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-summary-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-rebuild-summaries 'formals nil (w state))) (out (getpropc 'fn-lbc-rebuild-summaries 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-rebuild-summaries fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-rebuild-summaries (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-rebuild-summaries (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-rebuild-summaries."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-drop-owner 'formals nil (w state))) (out (getpropc 'fn-lbc-slot-drop-owner 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-slot-drop-owner fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-drop-owner (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-slot-drop-owner (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-slot-drop-owner."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-row 'formals nil (w state))) (out (getpropc 'fn-lbc-append-row 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-row fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-row (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-append-row (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-row-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-row."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-rebuild-rows 'formals nil (w state))) (out (getpropc 'fn-lbc-rebuild-rows 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-rebuild-rows fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-rebuild-rows (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-slot-store-model-of-rebuild-rows (equal (fn-lb-slot-store-model ,value) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-slot-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-rows-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-rebuild-rows."))))

(defthm fn-lb-slot-store-model-of-summary-groups-update
 (equal (fn-lb-slot-store-model (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lb-slot-store-model fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-slot-store-model update-fn-lbc-summary-groups fn-dm-nth-update-nth)))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-msgid-pool-append 'formals nil (w state))) (out (getpropc 'fn-lbc-msgid-pool-append 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-msgid-pool-append fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-msgid-pool-append (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-msgid-pool-append (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-msgid-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-overview-pool-append 'formals nil (w state))) (out (getpropc 'fn-lbc-overview-pool-append 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-overview-pool-append fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-overview-pool-append (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-overview-pool-append (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-overview-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov-texts 'formals nil (w state))) (out (getpropc 'fn-lbc-append-nov-texts 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-nov-texts fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-nov-texts (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-append-nov-texts (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-nov-texts."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov 'formals nil (w state))) (out (getpropc 'fn-lbc-append-nov 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-nov fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-nov (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-append-nov (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-nov."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-memberships 'formals nil (w state))) (out (getpropc 'fn-lbc-append-memberships 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-memberships fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-memberships (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-append-memberships (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-memberships."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-escape-store-put 'formals nil (w state))) (out (getpropc 'fn-lbc-escape-store-put 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-escape-store-put fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-escape-store-put (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-escape-store-put (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-escape-store-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-first 'formals nil (w state))) (out (getpropc 'fn-lbc-number-put-first 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-number-put-first fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-number-put-first (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-number-put-first (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-first-field fn-lbwf-number-put-first-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-number-put-first."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-row-seen 'formals nil (w state))) (out (getpropc 'fn-lbc-number-put-row-seen 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-number-put-row-seen fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-number-put-row-seen (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-number-put-row-seen (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-seen-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-number-put-row-seen."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-number-put-row 'formals nil (w state))) (out (getpropc 'fn-lbc-number-put-row 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-number-put-row fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-number-put-row (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-number-put-row (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-number-put-row-field fn-lbwf-number-put-row-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-number-put-row."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-summary-put 'formals nil (w state))) (out (getpropc 'fn-lbc-summary-put 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-summary-put fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-summary-put (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-summary-put (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-summary-put-field fn-lbwf-summary-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-summary-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-rebuild-summaries 'formals nil (w state))) (out (getpropc 'fn-lbc-rebuild-summaries 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-rebuild-summaries fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-rebuild-summaries (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-rebuild-summaries (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-summaries-field fn-lbwf-rebuild-summaries-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-rebuild-summaries."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-reserve-slots 'formals nil (w state))) (out (getpropc 'fn-lbc-reserve-slots 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-reserve-slots fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-reserve-slots (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-reserve-slots (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-reserve-slots."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-drop-owner 'formals nil (w state))) (out (getpropc 'fn-lbc-slot-drop-owner 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-slot-drop-owner fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-drop-owner (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-slot-drop-owner (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-slot-drop-owner."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-row 'formals nil (w state))) (out (getpropc 'fn-lbc-append-row 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-row fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-row (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-append-row (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-row-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-row."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-rebuild-rows 'formals nil (w state))) (out (getpropc 'fn-lbc-rebuild-rows 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-rebuild-rows fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-rebuild-rows (w state)) :common-lisp-compliant))
 (value `(defthm fn-lbc-slot-escape-keys-of-rebuild-rows (equal (fn-lbc-slot-escape-keys ,value) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsst-owner-keys-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-rebuild-rows-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-rebuild-rows."))))

(defthm fn-lbc-slot-escape-keys-of-summary-groups-update
 (equal (fn-lbc-slot-escape-keys (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-escape-keys update-fn-lbc-summary-groups fn-dm-nth-update-nth)))))

(defthm fn-lb-slot-store-model-of-clear-columns
 (equal (fn-lb-slot-store-model (fn-lbc-clear-columns fn-lbc)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-slot-store-model fn-lbc-clear-columns update-fn-lbc-row-store update-fn-lbc-msgid-store update-fn-lbc-overview-store update-fn-lbc-number-store update-fn-lbc-slot-store update-fn-lbc-directory-store update-fn-lbc-membership-store update-fn-lbc-nov-store update-fn-lbc-summary-groups update-fn-lbc-slot-escape-keys fn-lbc-slot-store fn-lbc-msgid-slots-clear
 fn-lbc-msgid-slots$a-clear fn-lbc-escape-store-clear fn-dm-nth-update-nth (:executable-counterpart nfix) (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-slot-escape-keys-of-clear-columns
 (equal (fn-lbc-slot-escape-keys (fn-lbc-clear-columns fn-lbc)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-slot-escape-keys fn-lbc-clear-columns update-fn-lbc-row-store update-fn-lbc-msgid-store update-fn-lbc-overview-store update-fn-lbc-number-store update-fn-lbc-slot-store update-fn-lbc-directory-store update-fn-lbc-membership-store update-fn-lbc-nov-store update-fn-lbc-summary-groups update-fn-lbc-slot-escape-keys fn-lbc-slot-store fn-lbc-msgid-slots-clear
 fn-lbc-msgid-slots$a-clear fn-lbc-escape-store-clear fn-dm-nth-update-nth (:executable-counterpart nfix) (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-slot-escape-of-clear-columns
 (equal (fn-lbc-escape key :msgid-slot (fn-lbc-clear-columns fn-lbc)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-escape fn-lbc-escape-store-get fn-lbc-clear-columns fn-lbc-escape-store-clear
 update-fn-lbc-summary-groups update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth (:executable-counterpart nfix) (:executable-counterpart natp) (:executable-counterpart equal) assoc-eq assoc-equal hons-assoc-equal (:executable-counterpart cdr))))))
