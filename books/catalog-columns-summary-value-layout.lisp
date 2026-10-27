; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-summary-lookup")

(defun-nx fn-lb-summary-table (fn-lbc) (nth 1 (nth 3 fn-lbc)))

(defun-nx fn-lb-summary-valuesp (table)
 (if (consp table) (and (consp (car table)) (natp (cdar table)) (fn-lb-summary-valuesp (cdr table))) (null table)))

(local (defthm fn-lbsvl-table-frame
 (implies (equal (nth 3 new) (nth 3 fn-lbc)) (equal (fn-lb-summary-table new) (fn-lb-summary-table fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-summary-table))))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-msgid-pool-append 'formals nil (w state))) (out (getpropc 'fn-lbc-msgid-pool-append 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-msgid-pool-append fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-msgid-pool-append (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-msgid-pool-append (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-msgid-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-overview-pool-append 'formals nil (w state))) (out (getpropc 'fn-lbc-overview-pool-append 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-overview-pool-append fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-overview-pool-append (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-overview-pool-append (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-overview-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov-texts 'formals nil (w state))) (out (getpropc 'fn-lbc-append-nov-texts 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-nov-texts fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-nov-texts (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-append-nov-texts (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-nov-texts."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov 'formals nil (w state))) (out (getpropc 'fn-lbc-append-nov 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-nov fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-nov (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-append-nov (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-nov."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-memberships 'formals nil (w state))) (out (getpropc 'fn-lbc-append-memberships 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-memberships fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-memberships (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-append-memberships (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-memberships."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-escape-store-put 'formals nil (w state))) (out (getpropc 'fn-lbc-escape-store-put 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-escape-store-put fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-escape-store-put (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-escape-store-put (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-escape-store-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-reserve-slots 'formals nil (w state))) (out (getpropc 'fn-lbc-reserve-slots 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-reserve-slots fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-reserve-slots (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-reserve-slots (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-reserve-slots."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-drop-owner 'formals nil (w state))) (out (getpropc 'fn-lbc-slot-drop-owner 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-slot-drop-owner fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-drop-owner (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-slot-drop-owner (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-slot-drop-owner."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-put 'formals nil (w state))) (out (getpropc 'fn-lbc-slot-put 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-slot-put fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-put (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-slot-put (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-slot-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-insert 'formals nil (w state))) (out (getpropc 'fn-lbc-slot-insert 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-slot-insert fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-insert (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-slot-insert (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-slot-insert."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-index-slots 'formals nil (w state))) (out (getpropc 'fn-lbc-index-slots 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-index-slots fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-index-slots (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-index-slots (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-index-slots."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-row 'formals nil (w state))) (out (getpropc 'fn-lbc-append-row 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-row fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-row (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-summary-table-of-append-row (equal (fn-lb-summary-table ,value) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsvl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-row-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-map-frame "Missing actual native writer fn-lbc-append-row."))))

(defthm fn-lb-summary-table-of-summary-groups-update
 (equal (fn-lb-summary-table (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-summary-table update-fn-lbc-summary-groups fn-dm-nth-update-nth)))))

(defthm fn-lb-summary-table-of-clear-columns
 (equal (fn-lb-summary-table (fn-lbc-clear-columns fn-lbc)) nil)
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-store-of-clear-columns))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-summary-table fn-lbc-number-store)))))

(defthm fn-lb-summary-table-of-number-put-first
 (equal (fn-lb-summary-table (fn-lbc-number-put-first group number i fn-lbc)) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-summary-table fn-lbc-number-put-first fn-lbc-number-store update-fn-lbc-number-store
 fn-dmap-put fn-dmap$a-put fn-dm-nth-update-nth)))))

(defthm fn-lb-summary-table-of-number-put-row-seen
 (equal (fn-lb-summary-table (fn-lbc-number-put-row-seen numbers seen i fn-lbc)) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :induct (fn-lbc-number-put-row-seen numbers seen i fn-lbc) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-number-put-row-seen fn-lb-summary-table-of-number-put-first)))))

(defthm fn-lb-summary-table-of-number-put-row
 (equal (fn-lb-summary-table (fn-lbc-number-put-row numbers i fn-lbc)) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-number-put-row fn-lb-summary-table-of-number-put-row-seen)))))

(defthm fn-lb-summary-table-of-rebuild-rows
 (equal (fn-lb-summary-table (fn-lbc-rebuild-rows rows log fn-lbc)) (fn-lb-summary-table fn-lbc))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-rebuild-rows fn-lb-summary-table-of-append-row fn-lb-summary-table-of-number-put-row)))))

(defthm fn-lb-summary-valuesp-of-four-cell-put
 (implies (and (fn-lb-summary-valuesp (fn-lb-summary-table fn-lbc))
               (natp count) (natp low) (natp high) (natp next))
 (fn-lb-summary-valuesp (fn-lb-summary-table (fn-lbc-summary-put group (list count low high next) 1 fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-summary-table fn-lb-summary-valuesp fn-lbc-summary-put fn-lbc-number-store update-fn-lbc-number-store
 fn-dmap-put fn-dmap$a-put fn-dm-nth-update-nth)))))

(defthm fn-lb-summary-valuesp-of-rebuild-summaries
 (implies (fn-lb-summary-valuesp (fn-lb-summary-table fn-lbc))
 (fn-lb-summary-valuesp (fn-lb-summary-table (fn-lbc-rebuild-summaries groups rows fn-lbc))))
 :hints (("Goal" :induct (fn-lbc-rebuild-summaries groups rows fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-rebuild-summaries fn-lb-summary-valuesp-of-four-cell-put fn-lbc-summary-reference-values-natural)))))

(defthm fn-lb-summary-valuesp-of-open-rebuild
 (fn-lb-summary-valuesp (fn-lb-summary-table (fn-lbc-open-rebuild rows log fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lb-summary-table-of-index-slots fn-lb-summary-table-of-reserve-slots
 fn-lb-summary-table-of-summary-groups-update fn-lb-summary-valuesp-of-rebuild-summaries
 fn-lb-summary-table-of-rebuild-rows fn-lb-summary-table-of-clear-columns fn-lb-summary-valuesp)))))
