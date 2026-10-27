; Field frames proved from actual native writer bodies and world formals.
; Modified-field annotations are obligations, never assumed effects.
(in-package "ACL2")
(include-book "catalog-columns-guards")

(local (defthm fn-lbwf-nth-of-cons
 (equal (nth i (cons value xs))
        (if (zp i) value (nth (- (nfix i) 1) xs)))
 :hints (("Goal" :in-theory (enable nth)))))

(local (defthm fn-lbwf-nth-of-cdr
 (implies (natp i) (equal (nth i (cdr xs)) (nth (+ 1 i) xs)))
 :hints (("Goal" :in-theory (enable nth)))))

(make-event
(let* ((fs (getpropc 'fn-lbc-msgid-pool-append 'formals nil (w state)))
       (out (getpropc 'fn-lbc-msgid-pool-append 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-msgid-pool-append fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-msgid-pool-append (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-msgid-pool-append-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(1))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-msgid-pool-append update-fn-lbc-msgid-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-msgid-pool-append-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-msgid-pool-append-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-msgid-pool-append."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-overview-pool-append 'formals nil (w state)))
       (out (getpropc 'fn-lbc-overview-pool-append 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-overview-pool-append fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-overview-pool-append (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-overview-pool-append-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(2))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-overview-pool-append update-fn-lbc-overview-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-overview-pool-append-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-overview-pool-append-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-overview-pool-append."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-append-nov-texts 'formals nil (w state)))
       (out (getpropc 'fn-lbc-append-nov-texts 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-append-nov-texts fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-nov-texts (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-append-nov-texts-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(2))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-append-nov-texts update-fn-lbc-overview-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-append-nov-texts-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-append-nov-texts-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-append-nov-texts."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-append-nov 'formals nil (w state)))
       (out (getpropc 'fn-lbc-append-nov 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-append-nov fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-nov (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-append-nov-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(2 7))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :do-not-induct t
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-append-nov update-fn-lbc-overview-store update-fn-lbc-nov-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-append-nov-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-append-nov-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-append-nov."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-append-memberships 'formals nil (w state)))
       (out (getpropc 'fn-lbc-append-memberships 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-append-memberships fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-memberships (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-append-memberships-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(2 6))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-append-memberships update-fn-lbc-overview-store update-fn-lbc-membership-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-append-memberships-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-append-memberships-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-append-memberships."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-escape-store-put 'formals nil (w state)))
       (out (getpropc 'fn-lbc-escape-store-put 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-escape-store-put fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-escape-store-put (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-escape-store-put-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(9))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :do-not-induct t
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-escape-store-put fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-escape-store-put-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-escape-store-put-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-escape-store-put."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-number-put-first 'formals nil (w state)))
       (out (getpropc 'fn-lbc-number-put-first 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-number-put-first fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-number-put-first (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-number-put-first-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(3))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :do-not-induct t
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-number-put-first update-fn-lbc-number-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-number-put-first-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-number-put-first-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-number-put-first."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-number-put-row-seen 'formals nil (w state)))
       (out (getpropc 'fn-lbc-number-put-row-seen 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-number-put-row-seen fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-number-put-row-seen (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-number-put-row-seen-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(3))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-number-put-row-seen update-fn-lbc-number-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-number-put-row-seen-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-number-put-row-seen-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-number-put-row-seen."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-number-put-row 'formals nil (w state)))
       (out (getpropc 'fn-lbc-number-put-row 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-number-put-row fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-number-put-row (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-number-put-row-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(3))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :do-not-induct t
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-number-put-row update-fn-lbc-number-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-lbwf-number-put-row-seen-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-number-put-row-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-number-put-row-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-number-put-row."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-summary-put 'formals nil (w state)))
       (out (getpropc 'fn-lbc-summary-put 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-summary-put fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-summary-put (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-summary-put-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(3))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-summary-put update-fn-lbc-number-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-summary-put-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-summary-put-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-summary-put."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-rebuild-summaries 'formals nil (w state)))
       (out (getpropc 'fn-lbc-rebuild-summaries 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-rebuild-summaries fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-rebuild-summaries (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-rebuild-summaries-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(3))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-rebuild-summaries update-fn-lbc-number-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-field fn-lbwf-summary-put-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-rebuild-summaries-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-rebuild-summaries-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-rebuild-summaries."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-reserve-slots 'formals nil (w state)))
       (out (getpropc 'fn-lbc-reserve-slots 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-reserve-slots fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-reserve-slots (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-reserve-slots-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(4))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-reserve-slots update-fn-lbc-slot-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-field fn-lbwf-summary-put-field fn-lbwf-rebuild-summaries-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-reserve-slots-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-reserve-slots-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-reserve-slots."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-slot-drop-owner 'formals nil (w state)))
       (out (getpropc 'fn-lbc-slot-drop-owner 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-slot-drop-owner fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-drop-owner (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-slot-drop-owner-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(9))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-slot-drop-owner fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-field fn-lbwf-summary-put-field fn-lbwf-rebuild-summaries-field fn-lbwf-reserve-slots-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    (defthm fn-lbwf-slot-drop-owner-field-car
     (equal (car ,value) (car fn-lbc))
     :hints (("Goal" :do-not-induct t
      :use ((:instance fn-lbwf-slot-drop-owner-field (lb-field 0))) :in-theory (union-theories (theory 'ground-zero) '(nth natp member-equal nfix)))))))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-slot-drop-owner."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-slot-put 'formals nil (w state)))
       (out (getpropc 'fn-lbc-slot-put 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-slot-put fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-put (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-slot-put-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(0 4 9 10))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :do-not-induct t
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-slot-put update-fn-lbc-row-store update-fn-lbc-slot-store update-fn-lbc-slot-escape-keys fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-field fn-lbwf-summary-put-field fn-lbwf-rebuild-summaries-field fn-lbwf-reserve-slots-field fn-lbwf-slot-drop-owner-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    ))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-slot-put."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-slot-insert 'formals nil (w state)))
       (out (getpropc 'fn-lbc-slot-insert 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-slot-insert fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-slot-insert (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-slot-insert-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(0 4 9 10))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-slot-insert update-fn-lbc-row-store update-fn-lbc-slot-store update-fn-lbc-slot-escape-keys fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-field fn-lbwf-summary-put-field fn-lbwf-rebuild-summaries-field fn-lbwf-reserve-slots-field fn-lbwf-slot-drop-owner-field fn-lbwf-slot-put-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    ))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-slot-insert."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-index-slots 'formals nil (w state)))
       (out (getpropc 'fn-lbc-index-slots 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-index-slots fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-index-slots (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-index-slots-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(0 4 9 10))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-index-slots update-fn-lbc-row-store update-fn-lbc-slot-store update-fn-lbc-slot-escape-keys fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-field fn-lbwf-summary-put-field fn-lbwf-rebuild-summaries-field fn-lbwf-reserve-slots-field fn-lbwf-slot-drop-owner-field fn-lbwf-slot-put-field fn-lbwf-slot-insert-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    ))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-index-slots."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-append-row 'formals nil (w state)))
       (out (getpropc 'fn-lbc-append-row 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-append-row fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-append-row (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-append-row-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(0 1 2 5 6 7 9))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :do-not-induct t
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-append-row update-fn-lbc-row-store update-fn-lbc-msgid-store update-fn-lbc-overview-store update-fn-lbc-directory-store update-fn-lbc-membership-store update-fn-lbc-nov-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-field fn-lbwf-summary-put-field fn-lbwf-rebuild-summaries-field fn-lbwf-reserve-slots-field fn-lbwf-slot-drop-owner-field fn-lbwf-slot-put-field fn-lbwf-slot-insert-field fn-lbwf-index-slots-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    ))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-append-row."))))

(make-event
(let* ((fs (getpropc 'fn-lbc-rebuild-rows 'formals nil (w state)))
       (out (getpropc 'fn-lbc-rebuild-rows 'stobjs-out nil (w state)))
       (call (cons 'fn-lbc-rebuild-rows fs))
       (value (if (cdr out) (list 'mv-nth (- (len out) (len (member-eq 'fn-lbc out))) call) call)))
 (if (and (member-eq 'fn-lbc fs) (member-eq 'fn-lbc out) (eq (symbol-class 'fn-lbc-rebuild-rows (w state)) :common-lisp-compliant))
  (value
   `(progn
    (defthm fn-lbwf-rebuild-rows-field
     (implies (and (natp lb-field) (not (member-equal lb-field '(0 1 2 3 5 6 7 9))))
      (equal (nth lb-field ,value) (nth lb-field fn-lbc)))
     :hints (("Goal" :do-not '(preprocess) :induct ,call
      :in-theory (set-difference-theories
        (union-theories (theory 'ground-zero) '(fn-lbc-rebuild-rows update-fn-lbc-row-store update-fn-lbc-msgid-store update-fn-lbc-overview-store update-fn-lbc-number-store update-fn-lbc-directory-store update-fn-lbc-membership-store update-fn-lbc-nov-store fn-lbwf-nth-of-cons fn-lbwf-nth-of-cdr fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field fn-lbwf-number-put-first-field fn-lbwf-number-put-row-seen-field fn-lbwf-number-put-row-field fn-lbwf-summary-put-field fn-lbwf-rebuild-summaries-field fn-lbwf-reserve-slots-field fn-lbwf-slot-drop-owner-field fn-lbwf-slot-put-field fn-lbwf-slot-insert-field fn-lbwf-index-slots-field fn-lbwf-append-row-field fn-dm-nth-update-nth member-equal natp nfix ,@(and (cdr out) '(mv-nth))))
        ',(append '((tau-system) binary-logior lognot ifix) (if (cdr out) nil '(mv-nth)))))))
    ))
  (er soft 'lb-frame-schema "Missing or non-native actual function fn-lbc-rebuild-rows."))))
