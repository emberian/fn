; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-number-lookup")

(defun-nx fn-lb-number-table (fn-lbc) (nth 0 (nth 3 fn-lbc)))

(defun-nx fn-lb-number-keysp (table)
 (if (consp table) (and (consp (car table)) (consp (caar table)) (fn-lb-number-keysp (cdr table))) (null table)))

(local (defthm fn-lbnkl-table-frame
 (implies (equal (nth 3 new) (nth 3 fn-lbc)) (equal (fn-lb-number-table new) (fn-lb-number-table fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-number-table))))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-msgid-pool-append 'formals nil (w state))) (out (getpropc 'fn-lbc-msgid-pool-append 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-msgid-pool-append fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-msgid-pool-append (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-msgid-pool-append (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-msgid-pool-append-field fn-lbwf-msgid-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-msgid-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-overview-pool-append 'formals nil (w state))) (out (getpropc 'fn-lbc-overview-pool-append 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-overview-pool-append fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-overview-pool-append (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-overview-pool-append (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-overview-pool-append-field fn-lbwf-overview-pool-append-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-overview-pool-append."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov-texts 'formals nil (w state))) (out (getpropc 'fn-lbc-append-nov-texts 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-nov-texts fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-nov-texts (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-append-nov-texts (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-texts-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-append-nov-texts."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-nov 'formals nil (w state))) (out (getpropc 'fn-lbc-append-nov 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-nov fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-nov (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-append-nov (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-nov-field fn-lbwf-append-nov-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-append-nov."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-memberships 'formals nil (w state))) (out (getpropc 'fn-lbc-append-memberships 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-memberships fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-memberships (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-append-memberships (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-memberships-field fn-lbwf-append-memberships-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-append-memberships."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-escape-store-put 'formals nil (w state))) (out (getpropc 'fn-lbc-escape-store-put 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-escape-store-put fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-escape-store-put (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-escape-store-put (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-escape-store-put-field fn-lbwf-escape-store-put-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-escape-store-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-reserve-slots 'formals nil (w state))) (out (getpropc 'fn-lbc-reserve-slots 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-reserve-slots fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-reserve-slots (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-reserve-slots (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-reserve-slots-field fn-lbwf-reserve-slots-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-reserve-slots."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-drop-owner 'formals nil (w state))) (out (getpropc 'fn-lbc-slot-drop-owner 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-slot-drop-owner fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-drop-owner (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-slot-drop-owner (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-slot-drop-owner."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-put 'formals nil (w state))) (out (getpropc 'fn-lbc-slot-put 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-slot-put fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-put (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-slot-put (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-slot-put."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-slot-insert 'formals nil (w state))) (out (getpropc 'fn-lbc-slot-insert 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-slot-insert fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-insert (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-slot-insert (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-slot-insert."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-index-slots 'formals nil (w state))) (out (getpropc 'fn-lbc-index-slots 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-index-slots fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-index-slots (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-index-slots (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-index-slots."))))

(make-event
 (let* ((fs (getpropc 'fn-lbc-append-row 'formals nil (w state))) (out (getpropc 'fn-lbc-append-row 'stobjs-out nil (w state)))
 (call (cons 'fn-lbc-append-row fs)) (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-row (w state)) :common-lisp-compliant))
 (value `(defthm fn-lb-number-table-of-append-row (equal (fn-lb-number-table ,value) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbnkl-table-frame (new ,value)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbwf-append-row-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal)))))))
 (er soft 'lb-key-layout "Missing actual native writer fn-lbc-append-row."))))

(defthm fn-lb-number-table-of-summary-groups-update
 (equal (fn-lb-number-table (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-number-table update-fn-lbc-summary-groups fn-dm-nth-update-nth)))))

(defthm fn-lb-number-table-of-clear-columns
 (equal (fn-lb-number-table (fn-lbc-clear-columns fn-lbc)) nil)
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-store-of-clear-columns))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-number-table fn-lbc-number-store)))))

(defthm fn-lb-number-table-of-number-put-first
 (equal (fn-lb-number-table (fn-lbc-number-put-first group number i fn-lbc))
 (if (natp (fn-lbc-number-get group number fn-lbc)) (fn-lb-number-table fn-lbc)
     (cons (cons (cons group number) i) (fn-lb-number-table fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-number-table fn-lbc-number-put-first fn-lbc-number-get fn-lbc-number-store update-fn-lbc-number-store
 fn-dmap-put fn-dmap$a-put fn-dm-nth-update-nth)))))

(defthm fn-lb-number-table-of-summary-put
 (equal (fn-lb-number-table (fn-lbc-summary-put group values field fn-lbc)) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :induct (fn-lbc-summary-put group values field fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-number-table fn-lbc-summary-put fn-lbc-number-store update-fn-lbc-number-store
 fn-dmap-put fn-dmap$a-put fn-dm-nth-update-nth)))))

(defthm fn-lb-number-table-of-rebuild-summaries
 (equal (fn-lb-number-table (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lb-number-table fn-lbc))
 :hints (("Goal" :induct (fn-lbc-rebuild-summaries groups rows fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-rebuild-summaries fn-lb-number-table-of-summary-put)))))

(defthm fn-lb-number-keysp-of-number-put-first
 (implies (fn-lb-number-keysp (fn-lb-number-table fn-lbc))
 (fn-lb-number-keysp (fn-lb-number-table (fn-lbc-number-put-first group number i fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-number-keysp fn-lb-number-table-of-number-put-first)))))

(defthm fn-lb-number-keysp-of-number-put-row-seen
 (implies (fn-lb-number-keysp (fn-lb-number-table fn-lbc)) (fn-lb-number-keysp (fn-lb-number-table (fn-lbc-number-put-row-seen numbers seen i fn-lbc))))
 :hints (("Goal" :induct (fn-lbc-number-put-row-seen numbers seen i fn-lbc) :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-number-put-row-seen fn-lb-number-keysp-of-number-put-first)))))

(defthm fn-lb-number-keysp-of-number-put-row
 (implies (fn-lb-number-keysp (fn-lb-number-table fn-lbc)) (fn-lb-number-keysp (fn-lb-number-table (fn-lbc-number-put-row numbers i fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-number-put-row fn-lb-number-keysp-of-number-put-row-seen)))))

(defthm fn-lb-number-keysp-of-rebuild-rows
 (implies (fn-lb-number-keysp (fn-lb-number-table fn-lbc)) (fn-lb-number-keysp (fn-lb-number-table (fn-lbc-rebuild-rows rows log fn-lbc))))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc) :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-rebuild-rows fn-lb-number-table-of-append-row fn-lb-number-keysp-of-number-put-row)))))

(defthm fn-lb-number-keysp-of-open-rebuild
 (fn-lb-number-keysp (fn-lb-number-table (fn-lbc-open-rebuild rows log fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lb-number-table-of-index-slots fn-lb-number-table-of-reserve-slots
 fn-lb-number-table-of-summary-groups-update fn-lb-number-table-of-rebuild-summaries
 fn-lb-number-keysp-of-rebuild-rows fn-lb-number-table-of-clear-columns fn-lb-number-keysp)))))
