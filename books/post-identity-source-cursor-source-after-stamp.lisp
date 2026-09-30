; Proof-only v1/v2 inverse composition after the captured Injection-Date.

(in-package "ACL2")

(include-book "post-identity-source-cursor-source-date")

(local (include-book "arithmetic/top" :dir :system))

(defun fn-psc-model-source-simple-complete (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-source-info-complete pos :source-info-simple c incoming held)))
  (if (equal (fn-psc-get phase d) :control) (fn-psc-step d nil) d)))

(defun fn-psc-model-source-v1-date-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-step (fn-psc-model-source-date-complete
               (fn-psc-get k c) :source-v1-date c incoming held) nil))

(defun fn-psc-model-source-v1-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((m (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-v1-msgid c incoming held))
        (d (fn-psc-step m nil)))
  (if (equal (fn-psc-get phase d) :compare)
      (fn-psc-model-source-v1-date-complete d incoming held) d)))

(defun fn-psc-model-source-v2-date-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-source-date-complete
            (fn-psc-get pos c) :source-optional-date c incoming held))
        (e (fn-psc-step d nil)))
  (fn-psc-model-source-simple-complete (fn-psc-get pos e) e incoming held)))

(defun fn-psc-model-source-v2-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((m (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held))
        (d (fn-psc-step m nil)))
  (fn-psc-model-source-v2-date-complete d incoming held)))

(defun fn-psc-model-source-after-stamp-complete (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held)))
  (if (equal (fn-psc-get phase d) :control)
   (let ((e (fn-psc-step d nil)))
    (if (fn-psc-get ok d) (fn-psc-model-source-v1-complete e incoming held)
      (fn-psc-model-source-v2-complete e incoming held))) d)))

(local (defthm fn-psc-source-tail-control-preserves-date-context
 (implies (and (fn-psc-source-date-contextp c incoming held)
               (equal (fn-psc-get phase c) :control)
               (member-eq (fn-psc-get resume c)
                '(:source-info-simple :source-info-v1 :source-v1-msgid :source-v1-date
                  :source-optional-msgid :source-optional-date)))
  (fn-psc-source-date-contextp (fn-psc-step c byte) incoming held))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source
        fn-psc-step fn-psc-control fn-psc-return fn-psc-finish fn-psc-msgid-compare
        fn-psc-date-compare fn-psc-info-compare fn-psc-agent-compare fn-psc-literal fn-psc-compare)
       (nth len update-nth nfix))))))

(local (defthm fn-psc-comparison-complete-preserves-source-date-context
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-model-comparison-complete c incoming held) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source)
  (fn-psc-model-comparison-complete nth len))))))

(local (defthm fn-psc-compare-preserves-source-date-context
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-compare pos ref start count resume c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-compare)
  (nth len update-nth nfix))))))

(local (defthm fn-psc-msgid-compare-preserves-source-date-context
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-msgid-compare pos resume c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-msgid-compare fn-psc-literal fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source)
  (fn-psc-compare nth len update-nth nfix))))))

(local (defthm fn-psc-msgid-control-preserves-source-date-context
 (implies (and (fn-psc-source-date-contextp c incoming held)
               (equal (fn-psc-get phase c) :control)
               (member-eq (fn-psc-get resume c) '(:msgid-field :msgid-content :msgid-tail)))
  (fn-psc-source-date-contextp (fn-psc-step c byte) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source
                                 fn-psc-step fn-psc-control fn-psc-return fn-psc-literal fn-psc-compare)
  (nth len update-nth nfix))))))

(local (defthm fn-psc-source-msgid-field-preserves-context-at-any-position
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-model-msgid-field-complete pos resume c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-msgid-compare pos resume c)))
        (:instance fn-psc-msgid-compare-preserves-source-date-context)
        (:instance fn-psc-comparison-complete-preserves-source-date-context (c (fn-psc-msgid-compare pos resume c)))
        (:instance fn-psc-msgid-control-preserves-source-date-context
         (c (fn-psc-model-comparison-complete (fn-psc-msgid-compare pos resume c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-msgid-field-complete fn-psc-msgid-compare fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-step fn-psc-model-comparison-complete
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth nfix))))))

(local (defthm fn-psc-source-msgid-content-preserves-context-at-any-position
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-model-msgid-content-complete pos c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control
         (c (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c)))
        (:instance fn-psc-compare-preserves-source-date-context (ref :msgid) (start 0) (count (length (fn-psc-get msgid c))) (resume :msgid-content))
        (:instance fn-psc-comparison-complete-preserves-source-date-context (c (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c)))
        (:instance fn-psc-msgid-control-preserves-source-date-context
         (c (fn-psc-model-comparison-complete (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-msgid-content-complete fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-step fn-psc-model-comparison-complete
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth nfix))))))

(local (defthm fn-psc-source-msgid-tail-preserves-context-at-any-position
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-model-msgid-tail-complete pos c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos '(13 10) :msgid-tail c)))
        (:instance fn-psc-compare-preserves-source-date-context (ref '(13 10)) (start 0) (count 2) (resume :msgid-tail))
        (:instance fn-psc-comparison-complete-preserves-source-date-context (c (fn-psc-literal pos '(13 10) :msgid-tail c)))
        (:instance fn-psc-msgid-control-preserves-source-date-context
         (c (fn-psc-model-comparison-complete (fn-psc-literal pos '(13 10) :msgid-tail c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-msgid-tail-complete fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-step fn-psc-model-comparison-complete
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth nfix))))))

(local (defthm fn-psc-source-msgid-complete-preserves-date-context
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-model-msgid-complete pos resume c incoming held) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-msgid-complete)
  (fn-psc-model-msgid-field-complete fn-psc-model-msgid-content-complete fn-psc-model-msgid-tail-complete
   fn-psc-msgid-field-complete-is-actual-paid-steps fn-psc-msgid-content-stage-is-actual-paid-steps
   fn-psc-msgid-tail-stage-is-actual-paid-steps fn-psc-msgid-complete-is-actual-paid-steps
   fn-psc-model-byte-run fn-psc-model-comparison-cost
   fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source nth len))))))

(local (defthm fn-psc-inj-append-is-append
 (equal (fn-inj-append xs ys) (append xs ys))
 :hints (("Goal" :induct (len xs) :in-theory (enable fn-inj-append append len)))))

(local (defthm fn-psc-source-append-length
 (equal (len (append xs ys)) (+ (len xs) (len ys)))
 :hints (("Goal" :induct (len xs) :in-theory (enable append len)))))

(local (defthm fn-psc-record-string-octets-length
 (equal (len (fn-record-string-octets-aux chars)) (len chars))
 :hints (("Goal" :induct (fn-record-string-octets-aux chars)
          :in-theory (enable fn-record-string-octets-aux len)))))

(local (defthm fn-psc-record-string-octets-proper
 (true-listp (fn-record-string-octets-aux chars))
 :hints (("Goal" :induct (fn-record-string-octets-aux chars)
                 :in-theory (enable fn-record-string-octets-aux)))))

(local (defthm fn-psc-source-message-id-line-is-proper-length
 (implies (stringp text)
  (and (true-listp (fn-inj-message-id-line (fn-record-string-octets text)))
       (equal (len (fn-inj-message-id-line (fn-record-string-octets text))) (+ 14 (length text)))))
 :hints (("Goal" :in-theory (e/d (fn-inj-message-id-line fn-record-string-octets length) (fn-inj-append))))))

(local (defthm fn-psc-source-buffer-strip-success-index
 (implies (and (natp i) (true-listp prefix)
               (not (equal (fn-pbb-strip-at prefix i xs) :no)))
  (equal (fn-pbb-strip-at prefix i xs) (+ i (len prefix))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (e/d (fn-pbb-strip-at) (nth))))))

(local (defthm fn-psc-msgid-control-preserves-slot
 (implies (and (equal (fn-psc-get phase c) :control)
               (member-eq (fn-psc-get resume c) '(:msgid-field :msgid-content :msgid-tail))
               (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15))))
  (equal (nth slot (fn-psc-step c byte)) (nth slot c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control fn-psc-return fn-psc-literal fn-psc-compare nfix)
  (nth len update-nth))))))

(local (defthm fn-psc-source-msgid-field-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 18 20))))
  (equal (nth slot (fn-psc-model-msgid-field-complete pos resume c incoming held)) (nth slot c)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-msgid-compare pos resume c)))
        (:instance fn-psc-msgid-control-preserves-slot
          (c (fn-psc-model-comparison-complete (fn-psc-msgid-compare pos resume c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-msgid-field-complete fn-psc-msgid-compare fn-psc-literal fn-psc-compare fn-psc-comparison-statep nfix)
   (fn-psc-model-comparison-complete fn-psc-step fn-psc-msgid-control-preserves-slot
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-msgid-content-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 18 20))))
  (equal (nth slot (fn-psc-model-msgid-content-complete pos c incoming held)) (nth slot c)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c)))
        (:instance fn-psc-msgid-control-preserves-slot
          (c (fn-psc-model-comparison-complete (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-msgid-content-complete  fn-psc-compare fn-psc-comparison-statep nfix)
   (fn-psc-model-comparison-complete fn-psc-step fn-psc-msgid-control-preserves-slot
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-msgid-tail-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 18 20))))
  (equal (nth slot (fn-psc-model-msgid-tail-complete pos c incoming held)) (nth slot c)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos '(13 10) :msgid-tail c)))
        (:instance fn-psc-msgid-control-preserves-slot
          (c (fn-psc-model-comparison-complete (fn-psc-literal pos '(13 10) :msgid-tail c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-msgid-tail-complete fn-psc-literal fn-psc-compare fn-psc-comparison-statep nfix)
   (fn-psc-model-comparison-complete fn-psc-step fn-psc-msgid-control-preserves-slot
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-msgid-complete-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 18 20))))
  (equal (nth slot (fn-psc-model-msgid-complete pos resume c incoming held)) (nth slot c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-msgid-complete)
  (fn-psc-model-msgid-field-complete fn-psc-model-msgid-content-complete fn-psc-model-msgid-tail-complete
   fn-psc-msgid-field-complete-is-actual-paid-steps fn-psc-msgid-content-stage-is-actual-paid-steps
   fn-psc-msgid-tail-stage-is-actual-paid-steps fn-psc-msgid-complete-is-actual-paid-steps
   fn-psc-model-byte-run fn-psc-model-comparison-cost nth len))))))

(local (defthm fn-psc-source-msgid-complete-keeps-captured-date
 (equal (fn-psc-model-captured-date (fn-psc-model-msgid-complete pos resume c incoming held) incoming held)
        (fn-psc-model-captured-date c incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-captured-date fn-psc-model-source)
  (fn-psc-model-msgid-complete nth nthcdr len))))))

(local (defthm fn-psc-source-msgid-complete-keeps-source
 (equal (fn-psc-model-source (fn-psc-model-msgid-complete pos resume c incoming held) incoming held)
        (fn-psc-model-source c incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source)
  (fn-psc-model-msgid-complete fn-psc-msgid-complete-is-actual-paid-steps nth len))))))

(local (defthm fn-psc-source-msgid-complete-is-current-buffer-strip
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-msgid-complete pos resume c incoming held))
         (p (fn-pbb-strip-at (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c)))
                              pos (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) resume)
        (iff (fn-psc-get ok d) (not (equal p :no)))
        (implies (not (equal p :no)) (equal (fn-psc-get pos d) p))
        (fn-psc-source-date-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-msgid-complete-is-current-message-id-strip
        fn-psc-source-msgid-complete-preserves-date-context
        (:instance fn-psc-source-message-id-line-is-proper-length (text (fn-psc-get msgid c)))
        (:instance fn-pbb-strip-at-is-inj-strip
         (prefix (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))))
         (i pos) (fn-octets (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp)
   (fn-psc-model-msgid-complete fn-psc-model-source fn-record-string-octets fn-inj-message-id-line
    fn-pbb-strip-at fn-pbb-strip-at-is-inj-strip fn-inj-strip fn-psc-model-byte-run
    fn-psc-msgid-complete-is-current-message-id-strip fn-psc-source-msgid-complete-preserves-date-context
    fn-psc-source-message-id-line-is-proper-length nth nthcdr len))))))

(local (defthm fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-msgid-complete pos resume c incoming held))
         (p (fn-pbb-strip-at (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c)))
                              pos (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) resume)
        (iff (fn-psc-get ok d) (not (equal p :no)))
        (implies (not (equal p :no)) (equal (fn-psc-get pos d) p))
        (fn-psc-source-date-contextp d incoming held)
        (equal (fn-psc-get k d) pos)
        (equal (fn-psc-model-captured-date d incoming held) (fn-psc-model-captured-date c incoming held))
        (equal (fn-psc-model-source d incoming held) (fn-psc-model-source c incoming held))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-msgid-complete-is-current-message-id-strip
        fn-psc-source-msgid-complete-preserves-date-context
        (:instance fn-psc-source-message-id-line-is-proper-length (text (fn-psc-get msgid c)))
        (:instance fn-pbb-strip-at-is-inj-strip
         (prefix (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))))
         (i pos) (fn-octets (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp)
   (fn-psc-msgid-complete-is-actual-paid-steps fn-psc-model-msgid-complete fn-record-string-octets fn-inj-message-id-line
    fn-pbb-strip-at fn-pbb-strip-at-is-inj-strip fn-inj-strip fn-psc-model-byte-run
    fn-psc-msgid-complete-is-current-message-id-strip fn-psc-source-msgid-complete-preserves-date-context
    fn-psc-source-message-id-line-is-proper-length nth nthcdr len))))))

(local (defthm fn-psc-date-compare-preserves-source-date-context
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-date-compare pos resume c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-date-compare fn-psc-literal fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source)
  (fn-psc-compare nth len update-nth nfix))))))

(local (defthm fn-psc-source-date-constructor-frame
 (and (equal (fn-psc-get phase (fn-psc-date-compare pos resume c)) :compare)
      (equal (fn-psc-get k (fn-psc-date-compare pos resume c)) (nfix pos))
      (equal (fn-psc-get pos (fn-psc-date-compare pos resume c)) (nfix pos))
      (equal (fn-psc-model-source (fn-psc-date-compare pos resume c) incoming held)
             (fn-psc-model-source c incoming held))
      (equal (fn-psc-model-captured-date (fn-psc-date-compare pos resume c) incoming held)
             (fn-psc-model-captured-date c incoming held)))
 :hints (("Goal" :in-theory (e/d (fn-psc-date-compare fn-psc-literal fn-psc-compare
                                 fn-psc-model-source fn-psc-model-captured-date)
  (nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-date-control-preserves-slot
 (implies (and (equal (fn-psc-get phase c) :control)
               (member-eq (fn-psc-get resume c) '(:date-field :date-content :date-tail))
               (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15))))
  (equal (nth slot (fn-psc-step c byte)) (nth slot c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control fn-psc-return fn-psc-literal fn-psc-compare nfix)
  (nth len update-nth))))))

(local (defthm fn-psc-source-date-field-k-frame
 (equal (nth 18 (fn-psc-model-source-date-field-complete pos resume c incoming held)) (nfix pos))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-date-compare pos resume c)))
        (:instance fn-psc-date-control-preserves-slot
          (c (fn-psc-model-comparison-complete (fn-psc-date-compare pos resume c) incoming held)) (byte nil) (slot 18)))
  :in-theory (e/d (fn-psc-model-source-date-field-complete fn-psc-date-compare fn-psc-literal fn-psc-compare fn-psc-comparison-statep nfix)
   (fn-psc-model-comparison-complete fn-psc-step fn-psc-date-control-preserves-slot
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-date-content-k-frame
 (equal (nth 18 (fn-psc-model-source-date-content-complete pos c incoming held)) (nth 18 c))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c)))
        (:instance fn-psc-date-control-preserves-slot
          (c (fn-psc-model-comparison-complete (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c) incoming held)) (byte nil) (slot 18)))
  :in-theory (e/d (fn-psc-model-source-date-content-complete  fn-psc-compare fn-psc-comparison-statep nfix)
   (fn-psc-model-comparison-complete fn-psc-step fn-psc-date-control-preserves-slot
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-date-tail-k-frame
 (equal (nth 18 (fn-psc-model-source-date-tail-complete pos c incoming held)) (nth 18 c))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos '(13 10) :date-tail c)))
        (:instance fn-psc-date-control-preserves-slot
          (c (fn-psc-model-comparison-complete (fn-psc-literal pos '(13 10) :date-tail c) incoming held)) (byte nil) (slot 18)))
  :in-theory (e/d (fn-psc-model-source-date-tail-complete fn-psc-literal fn-psc-compare fn-psc-comparison-statep nfix)
   (fn-psc-model-comparison-complete fn-psc-step fn-psc-date-control-preserves-slot
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-date-complete-k-frame
 (equal (fn-psc-get k (fn-psc-model-source-date-complete pos resume c incoming held)) (nfix pos))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source-date-complete)
  (fn-psc-model-source-date-field-complete fn-psc-model-source-date-content-complete fn-psc-model-source-date-tail-complete
   fn-psc-source-date-complete-is-actual-paid-steps
   
   fn-psc-model-byte-run fn-psc-model-comparison-cost nth len))))))

(local (defthm fn-psc-source-natural-fix
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix natp)))))

(local (defthm fn-psc-source-v1-date-complete-is-current-date-rejection
 (implies (and (fn-psc-source-date-contextp c incoming held)
               (natp (fn-psc-get k c))
               (<= (fn-psc-get k c) (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-source-v1-date-complete c incoming held))
         (p (fn-pbb-strip-at (fn-inj-date-line (fn-psc-model-captured-date c incoming held))
                             (fn-psc-get k c) (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-get phase d) (if (equal p :no) :control :done))
        (implies (equal p :no)
         (and (equal (fn-psc-get resume d) :source-found)
              (equal (fn-psc-get pos d) (fn-psc-get k c)) (fn-psc-get ok d)))
        (implies (not (equal p :no)) (equal (fn-psc-get result d) :no-source))
        (fn-psc-source-date-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-natural-fix (x (fn-psc-get k c)))
        (:instance fn-psc-source-date-complete-k-frame (pos (fn-psc-get k c)) (resume :source-v1-date))
        (:instance fn-psc-source-date-complete-is-current-buffer-strip
          (pos (fn-psc-get k c)) (resume :source-v1-date))
        (:instance fn-psc-source-tail-control-preserves-date-context
          (c (fn-psc-model-source-date-complete (fn-psc-get k c) :source-v1-date c incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-v1-date-complete fn-psc-step fn-psc-control fn-psc-return fn-psc-finish)
   (fn-psc-model-source-date-complete fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source
    fn-pbb-strip-at fn-inj-date-line fn-psc-model-captured-date fn-psc-source-date-complete-is-current-buffer-strip
    fn-psc-source-date-complete-is-actual-paid-steps fn-psc-model-byte-run nth len update-nth nfix))))))

(local (defthm fn-psc-source-v1-msgid-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-v1-msgid))
  (equal (fn-psc-step c nil)
   (if (fn-psc-get ok c) (fn-psc-finish :no-source c)
       (fn-psc-date-compare (fn-psc-get k c) :source-v1-date c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-finish fn-psc-date-compare nth nfix len update-nth))))))

(local (defthm fn-psc-source-v1-complete-is-current-ambiguity-rejection
 (implies (and (fn-psc-source-date-contextp c incoming held)
               (natp (fn-psc-get pos c))
               (<= (fn-psc-get pos c) (len (fn-psc-model-source c incoming held))))
  (let* ((pos (fn-psc-get pos c))
         (xs (fn-psc-model-source c incoming held))
         (m (fn-pbb-strip-at (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))) pos xs))
         (dt (fn-pbb-strip-at (fn-inj-date-line (fn-psc-model-captured-date c incoming held)) pos xs))
         (d (fn-psc-model-source-v1-complete c incoming held)))
   (and (equal (fn-psc-get phase d) (if (or (not (equal m :no)) (not (equal dt :no))) :done :control))
        (implies (and (equal m :no) (equal dt :no))
         (and (equal (fn-psc-get resume d) :source-found)
              (equal (fn-psc-get pos d) pos) (fn-psc-get ok d)))
        (implies (or (not (equal m :no)) (not (equal dt :no)))
         (equal (fn-psc-get result d) :no-source)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame
          (pos (fn-psc-get pos c)) (resume :source-v1-msgid))
        (:instance fn-psc-source-v1-msgid-callback
          (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-v1-msgid c incoming held)))
        (:instance fn-psc-source-v1-date-complete-is-current-date-rejection
          (c (fn-psc-date-compare (fn-psc-get pos c) :source-v1-date
                (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-v1-msgid c incoming held)))))
  :in-theory (e/d (fn-psc-model-source-v1-complete fn-psc-finish)
   (fn-psc-model-msgid-complete fn-psc-model-source-v1-date-complete fn-psc-step fn-psc-date-compare
    fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-model-captured-date
    fn-pbb-strip-at fn-inj-date-line fn-inj-message-id-line fn-record-string-octets
    fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame fn-psc-source-v1-msgid-callback
    fn-psc-source-v1-date-complete-is-current-date-rejection fn-psc-msgid-complete-is-actual-paid-steps
    fn-psc-model-byte-run nth len update-nth nfix))))))

(local (defthm fn-psc-source-info-complete-preserves-date-context
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (fn-psc-source-date-contextp (fn-psc-model-source-info-complete pos resume c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-complete-is-current-buffer-strip
        (:instance fn-psc-source-info-complete-keeps-source-slots (slot 1))
        (:instance fn-psc-source-info-complete-keeps-source-slots (slot 17)))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-model-source)
   (fn-psc-source-contextp fn-psc-model-source-info-complete fn-psc-source-info-complete-is-current-buffer-strip
    fn-psc-source-info-complete-keeps-source-slots fn-psc-source-info-complete-is-actual-paid-steps
    fn-psc-model-byte-run fn-pbb-strip-info-at nth len))))))

(local (defthm fn-psc-source-info-complete-keeps-date-and-source
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (and (equal (fn-psc-model-source (fn-psc-model-source-info-complete pos resume c incoming held) incoming held)
              (fn-psc-model-source c incoming held))
       (equal (fn-psc-model-captured-date (fn-psc-model-source-info-complete pos resume c incoming held) incoming held)
              (fn-psc-model-captured-date c incoming held))
       (equal (fn-psc-model-retained-agent (fn-psc-model-source-info-complete pos resume c incoming held) incoming)
              (fn-psc-model-retained-agent c incoming))))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source fn-psc-model-captured-date fn-psc-model-retained-agent)
  (fn-psc-model-source-info-complete fn-psc-source-contextp fn-psc-source-info-complete-is-actual-paid-steps
   fn-inj-take nth nthcdr len))))))

(local (defthm fn-psc-source-simple-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-info-simple))
  (equal (fn-psc-step c nil)
   (if (fn-psc-get ok c)
       (fn-psc-return t (fn-psc-set resume :source-found c))
       (fn-psc-finish :no-source c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-return fn-psc-finish nth len update-nth nfix))))))

(local (defthm fn-psc-source-simple-callback-preserves-context
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-info-simple))
  (fn-psc-source-contextp (fn-psc-step c nil) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-model-source fn-psc-return fn-psc-finish)
  (fn-psc-step nth len update-nth))))))

(local (defthm fn-psc-source-simple-complete-is-current-info-strip
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-source-simple-complete pos c incoming held))
         (p (fn-pbb-strip-info-at (fn-psc-model-retained-agent c incoming) pos
                                  (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-get phase d) (if (equal p :no) :done :control))
        (implies (not (equal p :no))
         (and (equal (fn-psc-get resume d) :source-found)
              (equal (fn-psc-get pos d) p) (fn-psc-get ok d)))
        (implies (equal p :no) (equal (fn-psc-result d) :no-source))
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-info-complete-is-current-buffer-strip (resume :source-info-simple))
        (:instance fn-psc-source-info-complete-resume-frame (resume :source-info-simple))
        (:instance fn-psc-source-simple-callback
         (c (fn-psc-model-source-info-complete pos :source-info-simple c incoming held)))
        (:instance fn-psc-source-simple-callback-preserves-context
         (c (fn-psc-model-source-info-complete pos :source-info-simple c incoming held))))
  :in-theory (e/d (fn-psc-model-source-simple-complete fn-psc-return fn-psc-finish fn-psc-result)
   (fn-psc-model-source-info-complete fn-psc-source-contextp fn-psc-model-source fn-psc-model-retained-agent
    fn-psc-step fn-psc-source-simple-callback fn-psc-source-simple-callback-preserves-context
    fn-psc-source-info-complete-is-current-buffer-strip fn-psc-source-info-complete-resume-frame
    fn-psc-source-info-complete-is-actual-paid-steps fn-psc-model-byte-run fn-pbb-strip-info-at
    nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-source-date-field-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 18 20))))
  (equal (nth slot (fn-psc-model-source-date-field-complete pos resume c incoming held)) (nth slot c)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-date-compare pos resume c)))
        (:instance fn-psc-date-control-preserves-slot
          (c (fn-psc-model-comparison-complete (fn-psc-date-compare pos resume c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-date-field-complete fn-psc-date-compare fn-psc-literal fn-psc-compare fn-psc-comparison-statep nfix)
   (fn-psc-model-comparison-complete fn-psc-step fn-psc-date-control-preserves-slot
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-date-content-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 18 20))))
  (equal (nth slot (fn-psc-model-source-date-content-complete pos c incoming held)) (nth slot c)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c)))
        (:instance fn-psc-date-control-preserves-slot
          (c (fn-psc-model-comparison-complete (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-date-content-complete  fn-psc-compare fn-psc-comparison-statep nfix)
   (fn-psc-model-comparison-complete fn-psc-step fn-psc-date-control-preserves-slot
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-date-tail-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 18 20))))
  (equal (nth slot (fn-psc-model-source-date-tail-complete pos c incoming held)) (nth slot c)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos '(13 10) :date-tail c)))
        (:instance fn-psc-date-control-preserves-slot
          (c (fn-psc-model-comparison-complete (fn-psc-literal pos '(13 10) :date-tail c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-date-tail-complete fn-psc-literal fn-psc-compare fn-psc-comparison-statep nfix)
   (fn-psc-model-comparison-complete fn-psc-step fn-psc-date-control-preserves-slot
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-date-complete-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 18 20))))
  (equal (nth slot (fn-psc-model-source-date-complete pos resume c incoming held)) (nth slot c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source-date-complete)
  (fn-psc-model-source-date-field-complete fn-psc-model-source-date-content-complete fn-psc-model-source-date-tail-complete
   fn-psc-source-date-complete-is-actual-paid-steps fn-psc-model-byte-run fn-psc-model-comparison-cost nth len))))))

(local (defthm fn-psc-source-date-complete-keeps-source-and-agent
 (and (equal (fn-psc-model-source (fn-psc-model-source-date-complete pos resume c incoming held) incoming held)
              (fn-psc-model-source c incoming held))
      (equal (fn-psc-model-retained-agent (fn-psc-model-source-date-complete pos resume c incoming held) incoming)
              (fn-psc-model-retained-agent c incoming)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source fn-psc-model-retained-agent)
  (fn-psc-model-source-date-complete fn-psc-source-date-complete-is-actual-paid-steps fn-inj-take nth nthcdr len))))))

(local (defthm fn-psc-source-simple-complete-preserves-date-context
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (fn-psc-source-date-contextp (fn-psc-model-source-simple-complete pos c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-info-complete-preserves-date-context (resume :source-info-simple))
        (:instance fn-psc-source-info-complete-resume-frame (resume :source-info-simple))
        (:instance fn-psc-source-tail-control-preserves-date-context
         (c (fn-psc-model-source-info-complete pos :source-info-simple c incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-simple-complete fn-psc-source-date-contextp)
   (fn-psc-model-source-info-complete fn-psc-step fn-psc-source-contextp fn-psc-model-source
    fn-psc-source-info-complete-is-actual-paid-steps fn-psc-model-byte-run nth len))))))

(local (defthm fn-psc-info-compare-preserves-source-date-context
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-info-compare pos resume c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare fn-psc-literal fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source)
  (fn-psc-compare nth len update-nth nfix))))))

(local (defthm fn-psc-source-info-constructor-frame
 (and (equal (fn-psc-get phase (fn-psc-info-compare pos resume c)) :compare)
      (equal (fn-psc-get pos (fn-psc-info-compare pos resume c)) (nfix pos))
      (equal (fn-psc-model-source (fn-psc-info-compare pos resume c) incoming held)
             (fn-psc-model-source c incoming held))
      (equal (fn-psc-model-retained-agent (fn-psc-info-compare pos resume c) incoming)
             (fn-psc-model-retained-agent c incoming))
      (equal (fn-psc-model-captured-date (fn-psc-info-compare pos resume c) incoming held)
             (fn-psc-model-captured-date c incoming held)))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare fn-psc-literal fn-psc-compare
                                 fn-psc-model-source fn-psc-model-captured-date fn-psc-model-retained-agent)
  (nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-source-optional-date-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-optional-date))
  (equal (fn-psc-step c nil)
   (fn-psc-info-compare (if (fn-psc-get ok c) (nfix (fn-psc-get pos c)) (nfix (fn-psc-get k c)))
                         :source-info-simple c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-info-compare nth len update-nth nfix))))))

(local (defthm fn-psc-source-date-context-has-source-unfolds
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-contextp c incoming held))
 :hints (("Goal" :in-theory (enable fn-psc-source-date-contextp)))))

(local (defthm fn-psc-source-v2-date-complete-is-current-optional-date
 (implies (and (fn-psc-source-date-contextp c incoming held)
               (natp (fn-psc-get pos c))
               (<= (fn-psc-get pos c) (len (fn-psc-model-source c incoming held))))
  (let* ((pos (fn-psc-get pos c)) (xs (fn-psc-model-source c incoming held))
         (k (fn-pbb-strip-optional-at (fn-inj-date-line (fn-psc-model-captured-date c incoming held)) pos xs))
         (p (fn-pbb-strip-info-at (fn-psc-model-retained-agent c incoming) k xs))
         (d (fn-psc-model-source-v2-date-complete c incoming held)))
   (and (equal (fn-psc-get phase d) (if (equal p :no) :done :control))
        (implies (not (equal p :no))
         (and (equal (fn-psc-get resume d) :source-found)
              (equal (fn-psc-get pos d) p) (fn-psc-get ok d)))
        (implies (equal p :no) (equal (fn-psc-result d) :no-source))
        (fn-psc-source-date-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-tail-control-preserves-date-context (c (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held)) (byte nil))
        (:instance fn-psc-source-date-complete-is-current-buffer-strip (pos (fn-psc-get pos c)) (resume :source-optional-date))
        (:instance fn-psc-source-optional-date-callback (c (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held)))
        (:instance fn-pbb-strip-optional-at-bounds (line (fn-inj-date-line (fn-psc-model-captured-date c incoming held))) (i (fn-psc-get pos c)) (fn-octets (fn-psc-model-source c incoming held)))
        (:instance fn-psc-source-natural-fix (x (fn-pbb-strip-optional-at (fn-inj-date-line (fn-psc-model-captured-date c incoming held)) (fn-psc-get pos c) (fn-psc-model-source c incoming held))))
        (:instance fn-psc-source-simple-complete-is-current-info-strip (pos (fn-psc-get pos (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil))) (c (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil)))
        (:instance fn-psc-source-simple-complete-preserves-date-context (pos (fn-psc-get pos (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil))) (c (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil))))
  :in-theory (e/d (fn-psc-model-source-v2-date-complete fn-pbb-strip-optional-at)
   (fn-psc-model-source-date-complete fn-psc-model-source-simple-complete fn-psc-step fn-psc-info-compare
    fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-model-captured-date fn-psc-model-retained-agent
    fn-pbb-strip-at fn-pbb-strip-info-at fn-inj-date-line
    fn-psc-source-date-complete-is-current-buffer-strip fn-psc-source-optional-date-callback
    fn-psc-source-simple-complete-is-current-info-strip fn-psc-source-simple-complete-preserves-date-context
    fn-psc-source-date-complete-is-actual-paid-steps fn-psc-model-byte-run nth len update-nth nfix))))))

(local (defthm fn-psc-source-optional-msgid-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-optional-msgid))
  (equal (fn-psc-step c nil)
   (fn-psc-date-compare (if (fn-psc-get ok c) (nfix (fn-psc-get pos c)) (nfix (fn-psc-get k c)))
                         :source-optional-date c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-date-compare nth len update-nth nfix))))))

(local (defthm fn-psc-source-msgid-complete-keeps-agent
 (equal (fn-psc-model-retained-agent (fn-psc-model-msgid-complete pos resume c incoming held) incoming)
        (fn-psc-model-retained-agent c incoming))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-retained-agent)
  (fn-psc-model-msgid-complete fn-psc-msgid-complete-is-actual-paid-steps nth len))))))

(local (defthm fn-psc-source-date-constructor-keeps-agent
 (equal (fn-psc-model-retained-agent (fn-psc-date-compare pos resume c) incoming)
        (fn-psc-model-retained-agent c incoming))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-retained-agent fn-psc-date-compare fn-psc-literal fn-psc-compare)
  (nth len update-nth nfix))))))

(local (defthm fn-psc-source-v2-complete-is-current-optional-msgid-date-info
 (implies (and (fn-psc-source-date-contextp c incoming held)
               (natp (fn-psc-get pos c))
               (<= (fn-psc-get pos c) (len (fn-psc-model-source c incoming held))))
  (let* ((pos (fn-psc-get pos c)) (xs (fn-psc-model-source c incoming held))
         (q (fn-pbb-strip-optional-at (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))) pos xs))
         (r (fn-pbb-strip-optional-at (fn-inj-date-line (fn-psc-model-captured-date c incoming held)) q xs))
         (p (fn-pbb-strip-info-at (fn-psc-model-retained-agent c incoming) r xs))
         (d (fn-psc-model-source-v2-complete c incoming held)))
   (and (equal (fn-psc-get phase d) (if (equal p :no) :done :control))
        (implies (not (equal p :no))
         (and (equal (fn-psc-get resume d) :source-found)
              (equal (fn-psc-get pos d) p) (fn-psc-get ok d)))
        (implies (equal p :no) (equal (fn-psc-result d) :no-source))
        (fn-psc-source-date-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame (pos (fn-psc-get pos c)) (resume :source-optional-msgid))
        (:instance fn-psc-source-optional-msgid-callback (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held)))
        (:instance fn-psc-source-tail-control-preserves-date-context (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held)) (byte nil))
        (:instance fn-pbb-strip-optional-at-bounds (line (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c)))) (i (fn-psc-get pos c)) (fn-octets (fn-psc-model-source c incoming held)))
        (:instance fn-psc-source-natural-fix (x (fn-pbb-strip-optional-at (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))) (fn-psc-get pos c) (fn-psc-model-source c incoming held))))
        (:instance fn-psc-source-v2-date-complete-is-current-optional-date (c (fn-psc-step (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held) nil)))
        (:instance fn-psc-date-compare-preserves-source-date-context (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held)) (pos (fn-pbb-strip-optional-at (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))) (fn-psc-get pos c) (fn-psc-model-source c incoming held))) (resume :source-optional-date))
        (:instance fn-psc-source-date-constructor-frame (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held)) (pos (fn-pbb-strip-optional-at (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))) (fn-psc-get pos c) (fn-psc-model-source c incoming held))) (resume :source-optional-date))
        (:instance fn-psc-source-msgid-complete-keeps-source (pos (fn-psc-get pos c)) (resume :source-optional-msgid)))
  :in-theory (e/d (fn-psc-model-source-v2-complete fn-pbb-strip-optional-at fn-psc-source-optional-msgid-callback fn-psc-source-date-constructor-frame)
   (fn-psc-model-msgid-complete fn-psc-model-source-v2-date-complete fn-psc-step fn-psc-date-compare
    fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-model-captured-date fn-psc-model-retained-agent
    fn-pbb-strip-at fn-pbb-strip-info-at fn-inj-date-line fn-inj-message-id-line fn-record-string-octets
    fn-psc-source-v2-date-complete-is-current-optional-date
    fn-psc-msgid-complete-is-actual-paid-steps fn-psc-model-byte-run nth len update-nth nfix))))))

(local (defthm fn-psc-source-info-v1-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-info-v1))
  (equal (fn-psc-step c nil)
   (if (fn-psc-get ok c)
    (fn-psc-msgid-compare (nfix (fn-psc-get pos c)) :source-v1-msgid
     (fn-psc-set k (nfix (fn-psc-get pos c)) c))
    (fn-psc-msgid-compare (fn-psc-get k c) :source-optional-msgid c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-msgid-compare nth len update-nth nfix))))))

(local (defthm fn-psc-source-set-k-preserves-date-context
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-set k value c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source)
  (nth len update-nth))))))

(local (defthm fn-psc-source-set-k-keeps-denotation
 (and (equal (fn-psc-model-source (fn-psc-set k value c) incoming held) (fn-psc-model-source c incoming held))
      (equal (fn-psc-model-captured-date (fn-psc-set k value c) incoming held) (fn-psc-model-captured-date c incoming held))
      (equal (fn-psc-model-retained-agent (fn-psc-set k value c) incoming) (fn-psc-model-retained-agent c incoming)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source fn-psc-model-captured-date fn-psc-model-retained-agent)
  (nth nthcdr len update-nth))))))

(local (defthm fn-psc-source-msgid-constructor-frame
 (and (equal (fn-psc-get phase (fn-psc-msgid-compare pos resume c)) :compare)
      (equal (fn-psc-get pos (fn-psc-msgid-compare pos resume c)) (nfix pos))
      (equal (fn-psc-model-source (fn-psc-msgid-compare pos resume c) incoming held) (fn-psc-model-source c incoming held))
      (equal (fn-psc-model-captured-date (fn-psc-msgid-compare pos resume c) incoming held) (fn-psc-model-captured-date c incoming held))
      (equal (fn-psc-get msgid (fn-psc-msgid-compare pos resume c)) (fn-psc-get msgid c))
      (equal (fn-psc-model-retained-agent (fn-psc-msgid-compare pos resume c) incoming) (fn-psc-model-retained-agent c incoming)))
 :hints (("Goal" :in-theory (e/d (fn-psc-msgid-compare fn-psc-literal fn-psc-compare fn-psc-model-source fn-psc-model-captured-date fn-psc-model-retained-agent)
  (nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-source-context-has-proper-source-unfolds
 (implies (fn-psc-source-contextp c incoming held)
  (true-listp (fn-psc-model-source c incoming held)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp) (fn-psc-model-source nth len))))))

(local (defthm fn-psc-source-strip-success-has-first-byte
 (implies (and (consp prefix) (not (equal (fn-inj-strip prefix xs) :no)))
  (and (consp xs) (equal (car xs) (car prefix))))
 :hints (("Goal" :expand ((fn-inj-strip prefix xs)) :in-theory (disable fn-inj-strip)))))

(local (defthm fn-psc-source-info-prefix-excludes-optional-fields-general
 (implies (and (true-listp xs) (natp pos) (<= pos (len xs))
               (not (equal (fn-pbb-strip-at (fn-inj-append *fn-inj-injection-info-field* agent) pos xs) :no)))
  (and (equal (fn-pbb-strip-at (fn-inj-message-id-line msgid) pos xs) :no)
       (equal (fn-pbb-strip-at (fn-inj-date-line date) pos xs) :no)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-strip-success-has-first-byte (prefix (fn-inj-append *fn-inj-injection-info-field* agent)) (xs (nthcdr pos xs)))
        (:instance fn-psc-source-strip-success-has-first-byte (prefix (fn-inj-message-id-line msgid)) (xs (nthcdr pos xs)))
        (:instance fn-psc-source-strip-success-has-first-byte (prefix (fn-inj-date-line date)) (xs (nthcdr pos xs)))
        (:instance fn-pbb-strip-at-is-inj-strip (prefix (fn-inj-append *fn-inj-injection-info-field* agent)) (i pos) (fn-octets xs))
        (:instance fn-pbb-strip-at-is-inj-strip (prefix (fn-inj-message-id-line msgid)) (i pos) (fn-octets xs))
        (:instance fn-pbb-strip-at-is-inj-strip (prefix (fn-inj-date-line date)) (i pos) (fn-octets xs)))
  :in-theory (e/d (fn-inj-message-id-line fn-inj-date-line fn-inj-append)
   (fn-pbb-strip-at fn-inj-strip fn-pbb-strip-at-is-inj-strip fn-psc-source-strip-success-has-first-byte
    nthcdr len))))))

(local (defthm fn-psc-source-info-failed-prefix-forces-after-stamp-failure
 (implies (and (true-listp xs) (natp pos) (<= pos (len xs))
               (not (equal (fn-pbb-strip-at (fn-inj-append *fn-inj-injection-info-field* agent) pos xs) :no))
               (equal (fn-pbb-strip-info-at agent pos xs) :no))
  (equal (fn-pbb-source-after-stamp pos date agent msgid xs) nil))
 :hints (("Goal" :do-not-induct t
  :use fn-psc-source-info-prefix-excludes-optional-fields-general
  :in-theory (e/d (fn-pbb-source-after-stamp fn-pbb-strip-optional-at)
   (fn-pbb-strip-at fn-pbb-strip-info-at fn-inj-append fn-inj-message-id-line fn-inj-date-line
    fn-psc-source-info-prefix-excludes-optional-fields-general nth len))))))

(defthm fn-psc-source-after-stamp-complete-is-current-buffer-inverse
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (let* ((p (fn-pbb-source-after-stamp pos (fn-psc-model-captured-date c incoming held)
              (fn-psc-model-retained-agent c incoming)
              (fn-record-string-octets (fn-psc-get msgid c)) (fn-psc-model-source c incoming held)))
         (d (fn-psc-model-source-after-stamp-complete pos c incoming held)))
   (and (equal (fn-psc-get phase d) (if p :control :done))
        (implies p (and (equal (fn-psc-get resume d) :source-found)
                        (equal (fn-psc-get pos d) p) (fn-psc-get ok d)))
        (implies (not p) (equal (fn-psc-result d) :no-source)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-psc-source-info-done-has-current-prefix (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-info-failed-prefix-forces-after-stamp-failure (xs (fn-psc-model-source c incoming held)) (agent (fn-psc-model-retained-agent c incoming)) (msgid (fn-record-string-octets (fn-psc-get msgid c))) (date (fn-psc-model-captured-date c incoming held)))
        (:instance fn-psc-source-info-complete-is-current-buffer-strip (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-info-complete-resume-frame (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-info-complete-preserves-date-context (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-info-complete-keeps-date-and-source (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-info-complete-keeps-source-slots (c (fn-psc-set k pos c)) (resume :source-info-v1) (slot 18))
        (:instance fn-psc-source-info-complete-keeps-source-slots (c (fn-psc-set k pos c)) (resume :source-info-v1) (slot 4))
        (:instance fn-psc-source-v1-complete-is-current-ambiguity-rejection (c (fn-psc-step (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held) nil)))
        (:instance fn-psc-source-v2-complete-is-current-optional-msgid-date-info (c (fn-psc-step (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held) nil)))
        (:instance fn-pbb-strip-info-at-bounds (agent (fn-psc-model-retained-agent c incoming)) (i pos) (fn-octets (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-model-source-after-stamp-complete fn-pbb-source-after-stamp
                   fn-psc-source-info-v1-callback fn-psc-source-msgid-constructor-frame)
   (fn-psc-model-source-info-complete fn-psc-model-source-v1-complete fn-psc-model-source-v2-complete
    fn-psc-step fn-psc-msgid-compare fn-psc-source-date-contextp fn-psc-source-contextp
    fn-psc-model-source fn-psc-model-captured-date fn-psc-model-retained-agent fn-record-string-octets
    fn-pbb-strip-info-at fn-pbb-strip-at fn-pbb-strip-optional-at fn-inj-message-id-line fn-inj-date-line
    fn-psc-source-v1-complete-is-current-ambiguity-rejection fn-psc-source-v2-complete-is-current-optional-msgid-date-info
    fn-psc-source-info-complete-is-current-buffer-strip fn-psc-source-info-complete-is-actual-paid-steps
    fn-psc-model-byte-run nth len update-nth nfix)))))

(local (defthm fn-psc-source-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-source-control-one-paid-step
 (implies (equal (fn-psc-get phase c) :control)
  (equal (fn-psc-model-byte-run 1 c incoming held) (fn-psc-step c nil)))
 :hints (("Goal" :expand ((fn-psc-model-byte-run 1 c incoming held)
                         (:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-demanded-byte fn-psc-demand)
   (fn-psc-model-byte-run fn-psc-model-source fn-psc-step nth len nfix))))))

(defun fn-psc-model-source-simple-cost (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (+ (fn-psc-model-source-info-cost pos :source-info-simple c incoming held)
    (if (equal (fn-psc-get phase (fn-psc-model-source-info-complete pos :source-info-simple c incoming held)) :control) 1 0)))

(local (defthm fn-psc-source-simple-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-source-simple-complete pos c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-simple-cost pos c incoming held)
                         (fn-psc-info-compare pos :source-info-simple c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-info-complete-is-actual-paid-steps (resume :source-info-simple))
        (:instance fn-psc-source-byte-run-addition (a (fn-psc-model-source-info-cost pos :source-info-simple c incoming held))
         (b (if (equal (fn-psc-get phase (fn-psc-model-source-info-complete pos :source-info-simple c incoming held)) :control) 1 0))
         (c (fn-psc-info-compare pos :source-info-simple c))))
  :expand ((:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-simple-complete fn-psc-model-source-simple-cost)
   (fn-psc-model-source-info-complete fn-psc-model-source-info-cost fn-psc-info-compare fn-psc-step
    fn-psc-source-info-complete-is-actual-paid-steps fn-psc-source-byte-run-addition fn-psc-source-simple-callback fn-psc-model-byte-run nth len nfix))))))

(defun fn-psc-model-source-v1-date-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (+ 1 (fn-psc-model-source-date-cost (fn-psc-get k c) :source-v1-date c incoming held)))

(local (defthm fn-psc-source-v1-date-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp (fn-psc-get k c))
               (<= (fn-psc-get k c) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-source-v1-date-complete c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-v1-date-cost c incoming held)
    (fn-psc-date-compare (fn-psc-get k c) :source-v1-date c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-date-complete-is-actual-paid-steps (pos (fn-psc-get k c)) (resume :source-v1-date))
        (:instance fn-psc-source-date-complete-is-current-buffer-strip (pos (fn-psc-get k c)) (resume :source-v1-date))
        (:instance fn-psc-source-byte-run-addition
         (a (fn-psc-model-source-date-cost (fn-psc-get k c) :source-v1-date c incoming held)) (b 1)
         (c (fn-psc-date-compare (fn-psc-get k c) :source-v1-date c))))
  :in-theory (e/d (fn-psc-model-source-v1-date-complete fn-psc-model-source-v1-date-cost)
   (fn-psc-model-source-date-complete fn-psc-model-source-date-cost fn-psc-date-compare fn-psc-step
    fn-psc-source-date-complete-is-current-buffer-strip fn-psc-source-date-complete-is-actual-paid-steps
    fn-psc-source-byte-run-addition
    fn-psc-model-byte-run nth len nfix))))))

(local (defthm fn-psc-source-date-and-control-is-actual-paid-steps
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-step (fn-psc-model-source-date-complete pos resume c incoming held) nil)
   (fn-psc-model-byte-run (+ 1 (fn-psc-model-source-date-cost pos resume c incoming held))
    (fn-psc-date-compare pos resume c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-date-complete-is-actual-paid-steps (pos pos) (resume resume))
        (:instance fn-psc-source-date-complete-is-current-buffer-strip (pos pos) (resume resume))
        (:instance fn-psc-source-byte-run-addition
         (a (fn-psc-model-source-date-cost pos resume c incoming held)) (b 1)
         (c (fn-psc-date-compare pos resume c))))
  :in-theory (e/d ()
   (fn-psc-model-source-date-complete fn-psc-model-source-date-cost fn-psc-date-compare fn-psc-step
    fn-psc-source-date-complete-is-current-buffer-strip fn-psc-source-date-complete-is-actual-paid-steps
    fn-psc-source-byte-run-addition
    fn-psc-model-byte-run nth len nfix))))))

(local (defthm fn-psc-source-optional-date-prefix-frame
 (implies (and (fn-psc-source-date-contextp c incoming held)
               (natp (fn-psc-get pos c))
               (<= (fn-psc-get pos c) (len (fn-psc-model-source c incoming held))))
  (let ((e (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil)))
   (and (fn-psc-source-contextp e incoming held)
        (natp (fn-psc-get pos e))
        (<= (fn-psc-get pos e) (len (fn-psc-model-source e incoming held))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-tail-control-preserves-date-context (c (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held)) (byte nil))
        (:instance fn-psc-source-date-complete-is-current-buffer-strip (pos (fn-psc-get pos c)) (resume :source-optional-date))
        (:instance fn-psc-source-optional-date-callback (c (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held)))
        (:instance fn-pbb-strip-optional-at-bounds (line (fn-inj-date-line (fn-psc-model-captured-date c incoming held))) (i (fn-psc-get pos c)) (fn-octets (fn-psc-model-source c incoming held)))
        (:instance fn-psc-source-natural-fix (x (fn-pbb-strip-optional-at (fn-inj-date-line (fn-psc-model-captured-date c incoming held)) (fn-psc-get pos c) (fn-psc-model-source c incoming held))))
        (:instance fn-psc-source-simple-complete-is-current-info-strip (pos (fn-psc-get pos (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil))) (c (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil)))
        (:instance fn-psc-source-simple-complete-preserves-date-context (pos (fn-psc-get pos (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil))) (c (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil))))
  :in-theory (e/d (fn-psc-source-optional-date-callback fn-psc-source-info-constructor-frame fn-pbb-strip-optional-at)
   (fn-psc-model-source-date-complete fn-psc-model-source-simple-complete fn-psc-step fn-psc-info-compare
    fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-model-captured-date fn-psc-model-retained-agent
    fn-pbb-strip-at fn-pbb-strip-info-at fn-inj-date-line
    fn-psc-source-date-complete-is-current-buffer-strip
    fn-psc-source-simple-complete-is-current-info-strip fn-psc-source-simple-complete-preserves-date-context
    fn-psc-source-date-complete-is-actual-paid-steps fn-psc-model-byte-run nth len update-nth nfix))))))

(local (defthm fn-psc-source-cdr-update-positive
 (implies (posp i)
  (equal (cdr (update-nth i value c)) (update-nth (1- i) value (cdr c))))
 :hints (("Goal" :expand ((update-nth i value c)) :in-theory (enable posp nfix)))))

(local (defthm fn-psc-source-update-overwrites
 (implies (natp i)
  (equal (update-nth i a (update-nth i b c)) (update-nth i a c)))
 :hints (("Goal" :induct (update-nth i b c) :in-theory (enable update-nth)))))

(local (defun fn-psc-source-update-induct (i j c)
 (declare (xargs :guard t :verify-guards nil :measure (nfix i)))
 (if (or (zp i) (zp j)) c (fn-psc-source-update-induct (1- i) (1- j) (cdr c)))))

(local (defthm fn-psc-source-update-order
 (implies (and (natp i) (natp j) (< i j))
  (equal (update-nth j b (update-nth i a c)) (update-nth i a (update-nth j b c))))
 :hints (("Goal" :induct (fn-psc-source-update-induct i j c)
  :in-theory (enable fn-psc-source-update-induct update-nth)))))

(local (defthm fn-psc-source-update-order-by-index
 (implies (and (natp i) (natp j) (< i j))
  (equal (update-nth j b (update-nth i a c)) (update-nth i a (update-nth j b c))))
 :rule-classes ((:rewrite :loop-stopper nil))
 :hints (("Goal" :use fn-psc-source-update-order :in-theory (disable fn-psc-source-update-order update-nth)))))

(local (defthm fn-psc-source-info-constructor-is-idempotent
 (equal (fn-psc-info-compare (fn-psc-get pos (fn-psc-info-compare pos resume c)) resume
          (fn-psc-info-compare pos resume c))
        (fn-psc-info-compare pos resume c))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare fn-psc-literal fn-psc-compare nfix)
  (nth len update-nth))))))

(local (defthm fn-psc-source-info-constructor-natural-is-idempotent
 (implies (natp pos)
  (equal (fn-psc-info-compare pos resume (fn-psc-info-compare pos resume c))
         (fn-psc-info-compare pos resume c)))
 :hints (("Goal" :use fn-psc-source-info-constructor-is-idempotent
  :in-theory (disable fn-psc-info-compare fn-psc-source-info-constructor-is-idempotent nth len nfix)))))

(local (defthm fn-psc-source-date-constructor-natural-is-idempotent
 (implies (natp pos)
  (equal (fn-psc-date-compare pos resume (fn-psc-date-compare pos resume c))
         (fn-psc-date-compare pos resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-date-compare fn-psc-literal fn-psc-compare nfix)
  (nth len update-nth))))))

(local (defthm fn-psc-source-msgid-constructor-natural-is-idempotent
 (implies (natp pos)
  (equal (fn-psc-msgid-compare pos resume (fn-psc-msgid-compare pos resume c))
         (fn-psc-msgid-compare pos resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-msgid-compare fn-psc-literal fn-psc-compare nfix)
  (nth len update-nth))))))

(local (defthm fn-psc-source-msgid-and-control-is-actual-paid-steps
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-step (fn-psc-model-msgid-complete pos resume c incoming held) nil)
   (fn-psc-model-byte-run (+ 1 (fn-psc-model-msgid-cost pos resume c incoming held))
    (fn-psc-msgid-compare pos resume c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-msgid-complete-is-actual-paid-steps (pos pos) (resume resume))
        (:instance fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame (pos pos) (resume resume))
        (:instance fn-psc-source-byte-run-addition
         (a (fn-psc-model-msgid-cost pos resume c incoming held)) (b 1)
         (c (fn-psc-msgid-compare pos resume c))))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp)
   (fn-psc-model-msgid-complete fn-psc-model-msgid-cost fn-psc-msgid-compare fn-psc-step
    fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame fn-psc-msgid-complete-is-actual-paid-steps
    fn-psc-source-byte-run-addition
    fn-record-string-octets fn-inj-message-id-line fn-psc-model-source fn-psc-model-byte-run nth len nfix))))))

(local (defthm fn-psc-source-optional-msgid-prefix-frame
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp (fn-psc-get pos c))
               (<= (fn-psc-get pos c) (len (fn-psc-model-source c incoming held))))
  (let ((e (fn-psc-step (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held) nil)))
   (and (fn-psc-source-date-contextp e incoming held) (natp (fn-psc-get pos e))
        (<= (fn-psc-get pos e) (len (fn-psc-model-source e incoming held))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame (pos (fn-psc-get pos c)) (resume :source-optional-msgid))
        (:instance fn-psc-source-optional-msgid-callback (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held)))
        (:instance fn-psc-source-tail-control-preserves-date-context (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held)) (byte nil))
        (:instance fn-pbb-strip-optional-at-bounds (line (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c)))) (i (fn-psc-get pos c)) (fn-octets (fn-psc-model-source c incoming held)))
        (:instance fn-psc-source-natural-fix (x (fn-pbb-strip-optional-at (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))) (fn-psc-get pos c) (fn-psc-model-source c incoming held))))
        (:instance fn-psc-source-v2-date-complete-is-current-optional-date (c (fn-psc-step (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held) nil)))
        (:instance fn-psc-date-compare-preserves-source-date-context (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held)) (pos (fn-pbb-strip-optional-at (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))) (fn-psc-get pos c) (fn-psc-model-source c incoming held))) (resume :source-optional-date))
        (:instance fn-psc-source-date-constructor-frame (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held)) (pos (fn-pbb-strip-optional-at (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c))) (fn-psc-get pos c) (fn-psc-model-source c incoming held))) (resume :source-optional-date))
        (:instance fn-psc-source-msgid-complete-keeps-source (pos (fn-psc-get pos c)) (resume :source-optional-msgid)))
  :in-theory (e/d (fn-psc-model-source-v2-complete fn-pbb-strip-optional-at fn-psc-source-optional-msgid-callback fn-psc-source-date-constructor-frame)
   (fn-psc-model-msgid-complete fn-psc-model-source-v2-date-complete fn-psc-step fn-psc-date-compare
    fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-model-captured-date fn-psc-model-retained-agent
    fn-pbb-strip-at fn-pbb-strip-info-at fn-inj-date-line fn-inj-message-id-line fn-record-string-octets
    fn-psc-source-v2-date-complete-is-current-optional-date
    fn-psc-msgid-complete-is-actual-paid-steps fn-psc-model-byte-run nth len update-nth nfix))))))

(defun fn-psc-model-source-v2-date-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((pos (fn-psc-get pos c))
        (d (fn-psc-model-source-date-complete pos :source-optional-date c incoming held))
        (e (fn-psc-step d nil)))
  (+ (fn-psc-model-source-date-cost pos :source-optional-date c incoming held) 1
     (fn-psc-model-source-simple-cost (fn-psc-get pos e) e incoming held))))

(local (defthm fn-psc-source-v2-date-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp (fn-psc-get pos c))
               (<= (fn-psc-get pos c) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-source-v2-date-complete c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-v2-date-cost c incoming held)
    (fn-psc-date-compare (fn-psc-get pos c) :source-optional-date c) incoming held)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-psc-source-date-and-control-is-actual-paid-steps (pos (fn-psc-get pos c)) (resume :source-optional-date))
        fn-psc-source-optional-date-prefix-frame
        (:instance fn-psc-source-optional-date-callback (c (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held)))
        (:instance fn-psc-source-date-complete-is-current-buffer-strip (pos (fn-psc-get pos c)) (resume :source-optional-date))
        (:instance fn-psc-source-simple-complete-is-actual-paid-steps (pos (fn-psc-get pos (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil))) (c (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil)))
        (:instance fn-psc-source-byte-run-addition (a (+ 1 (fn-psc-model-source-date-cost (fn-psc-get pos c) :source-optional-date c incoming held))) (b (fn-psc-model-source-simple-cost (fn-psc-get pos (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil)) (fn-psc-step (fn-psc-model-source-date-complete (fn-psc-get pos c) :source-optional-date c incoming held) nil) incoming held)) (c (fn-psc-date-compare (fn-psc-get pos c) :source-optional-date c))))
  :in-theory (e/d (fn-psc-model-source-v2-date-complete fn-psc-model-source-v2-date-cost fn-psc-source-optional-date-callback fn-psc-source-info-constructor-frame)
   (fn-psc-model-source-date-complete fn-psc-model-source-date-cost fn-psc-model-source-simple-complete
    fn-psc-model-source-simple-cost fn-psc-date-compare fn-psc-info-compare fn-psc-step
    fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-model-captured-date
    fn-pbb-strip-at fn-inj-date-line fn-psc-source-byte-run-addition
    fn-psc-source-date-complete-is-current-buffer-strip fn-psc-source-date-complete-is-actual-paid-steps
    fn-psc-source-simple-complete-is-actual-paid-steps fn-psc-source-date-and-control-is-actual-paid-steps fn-psc-model-byte-run nth len nfix))))))

(defun fn-psc-model-source-v2-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((pos (fn-psc-get pos c))
        (d (fn-psc-model-msgid-complete pos :source-optional-msgid c incoming held))
        (e (fn-psc-step d nil)))
  (+ (fn-psc-model-msgid-cost pos :source-optional-msgid c incoming held) 1
     (fn-psc-model-source-v2-date-cost e incoming held))))

(local (defthm fn-psc-source-v2-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp (fn-psc-get pos c))
               (<= (fn-psc-get pos c) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-source-v2-complete c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-v2-cost c incoming held)
    (fn-psc-msgid-compare (fn-psc-get pos c) :source-optional-msgid c) incoming held)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-psc-source-msgid-and-control-is-actual-paid-steps (pos (fn-psc-get pos c)) (resume :source-optional-msgid))
        fn-psc-source-optional-msgid-prefix-frame
        (:instance fn-psc-source-optional-msgid-callback (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held)))
        (:instance fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame (pos (fn-psc-get pos c)) (resume :source-optional-msgid))
        (:instance fn-psc-source-v2-date-complete-is-actual-paid-steps (c (fn-psc-step (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held) nil)))
        (:instance fn-psc-source-byte-run-addition (a (+ 1 (fn-psc-model-msgid-cost (fn-psc-get pos c) :source-optional-msgid c incoming held))) (b (fn-psc-model-source-v2-date-cost (fn-psc-step (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-optional-msgid c incoming held) nil) incoming held)) (c (fn-psc-msgid-compare (fn-psc-get pos c) :source-optional-msgid c))))
  :in-theory (e/d (fn-psc-model-source-v2-complete fn-psc-model-source-v2-cost fn-psc-source-optional-msgid-callback fn-psc-source-date-constructor-frame)
   (fn-psc-model-msgid-complete fn-psc-model-msgid-cost fn-psc-model-source-v2-date-complete
    fn-psc-model-source-v2-date-cost fn-psc-msgid-compare fn-psc-date-compare fn-psc-step
    fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-model-captured-date
    fn-pbb-strip-at fn-inj-date-line fn-psc-source-byte-run-addition
    fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame fn-psc-msgid-complete-is-actual-paid-steps
    fn-psc-source-v2-date-complete-is-actual-paid-steps fn-psc-source-msgid-and-control-is-actual-paid-steps fn-psc-model-byte-run nth len nfix))))))

(defun fn-psc-model-source-v1-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((pos (fn-psc-get pos c))
        (d (fn-psc-model-msgid-complete pos :source-v1-msgid c incoming held))
        (e (fn-psc-step d nil)))
  (+ (fn-psc-model-msgid-cost pos :source-v1-msgid c incoming held) 1
     (if (equal (fn-psc-get phase e) :compare) (fn-psc-model-source-v1-date-cost e incoming held) 0))))

(local (defthm fn-psc-source-v1-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp (fn-psc-get pos c))
               (<= (fn-psc-get pos c) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-source-v1-complete c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-v1-cost c incoming held)
    (fn-psc-msgid-compare (fn-psc-get pos c) :source-v1-msgid c) incoming held)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-psc-source-msgid-and-control-is-actual-paid-steps (pos (fn-psc-get pos c)) (resume :source-v1-msgid))
        (:instance fn-psc-source-tail-control-preserves-date-context (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-v1-msgid c incoming held)) (byte nil))
        (:instance fn-psc-source-v1-msgid-callback (c (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-v1-msgid c incoming held)))
        (:instance fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame (pos (fn-psc-get pos c)) (resume :source-v1-msgid))
        (:instance fn-psc-source-v1-date-complete-is-actual-paid-steps (c (fn-psc-step (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-v1-msgid c incoming held) nil)))
        (:instance fn-psc-source-byte-run-addition (a (+ 1 (fn-psc-model-msgid-cost (fn-psc-get pos c) :source-v1-msgid c incoming held))) (b (if (equal (fn-psc-get phase (fn-psc-step (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-v1-msgid c incoming held) nil)) :compare) (fn-psc-model-source-v1-date-cost (fn-psc-step (fn-psc-model-msgid-complete (fn-psc-get pos c) :source-v1-msgid c incoming held) nil) incoming held) 0)) (c (fn-psc-msgid-compare (fn-psc-get pos c) :source-v1-msgid c))))
  :expand ((:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-v1-complete fn-psc-model-source-v1-cost fn-psc-source-v1-msgid-callback fn-psc-source-date-constructor-frame fn-psc-finish)
   (fn-psc-model-msgid-complete fn-psc-model-msgid-cost fn-psc-model-source-v1-date-complete
    fn-psc-model-source-v1-date-cost fn-psc-msgid-compare fn-psc-date-compare fn-psc-step
    fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-model-captured-date
    fn-pbb-strip-at fn-inj-date-line fn-psc-source-byte-run-addition
    fn-psc-source-msgid-complete-is-current-buffer-strip-full-frame fn-psc-msgid-complete-is-actual-paid-steps
    fn-psc-source-v1-date-complete-is-actual-paid-steps fn-psc-source-msgid-and-control-is-actual-paid-steps fn-psc-model-byte-run nth len nfix))))))

(defun fn-psc-model-source-after-stamp-cost (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((c (fn-psc-set k pos c))
        (d (fn-psc-model-source-info-complete pos :source-info-v1 c incoming held))
        (e (fn-psc-step d nil)))
  (+ (fn-psc-model-source-info-cost pos :source-info-v1 c incoming held)
     (if (equal (fn-psc-get phase d) :control) 1 0)
     (if (equal (fn-psc-get phase d) :control)
      (if (fn-psc-get ok d) (fn-psc-model-source-v1-cost e incoming held)
       (fn-psc-model-source-v2-cost e incoming held)) 0))))

(defthm fn-psc-source-after-stamp-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-source-after-stamp-complete pos c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-after-stamp-cost pos c incoming held)
    (fn-psc-info-compare pos :source-info-v1 (fn-psc-set k pos c)) incoming held)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-psc-source-info-complete-is-current-buffer-strip (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-info-complete-resume-frame (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-info-complete-preserves-date-context (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-info-complete-keeps-date-and-source (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-info-complete-keeps-source-slots (c (fn-psc-set k pos c)) (resume :source-info-v1) (slot 18))
        (:instance fn-psc-source-info-complete-keeps-source-slots (c (fn-psc-set k pos c)) (resume :source-info-v1) (slot 4))
        (:instance fn-pbb-strip-info-at-bounds (agent (fn-psc-model-retained-agent c incoming)) (i pos) (fn-octets (fn-psc-model-source c incoming held)))
        (:instance fn-psc-source-info-complete-is-actual-paid-steps (c (fn-psc-set k pos c)) (resume :source-info-v1))
        (:instance fn-psc-source-v1-complete-is-actual-paid-steps (c (fn-psc-step (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held) nil)))
        (:instance fn-psc-source-v2-complete-is-actual-paid-steps (c (fn-psc-step (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held) nil)))
        (:instance fn-psc-source-byte-run-addition (a (fn-psc-model-source-info-cost pos :source-info-v1 (fn-psc-set k pos c) incoming held)) (b (if (equal (fn-psc-get phase (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held)) :control) 1 0)) (c (fn-psc-info-compare pos :source-info-v1 (fn-psc-set k pos c))))
        (:instance fn-psc-source-byte-run-addition (a (+ (fn-psc-model-source-info-cost pos :source-info-v1 (fn-psc-set k pos c) incoming held) (if (equal (fn-psc-get phase (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held)) :control) 1 0))) (b (if (equal (fn-psc-get phase (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held)) :control) (if (fn-psc-get ok (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held)) (fn-psc-model-source-v1-cost (fn-psc-step (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held) nil) incoming held) (fn-psc-model-source-v2-cost (fn-psc-step (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held) nil) incoming held)) 0)) (c (fn-psc-info-compare pos :source-info-v1 (fn-psc-set k pos c))))
        (:instance fn-psc-source-info-v1-callback (c (fn-psc-model-source-info-complete pos :source-info-v1 (fn-psc-set k pos c) incoming held))))
  :expand ((:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-after-stamp-complete fn-psc-model-source-after-stamp-cost
                  fn-psc-source-info-v1-callback fn-psc-source-msgid-constructor-frame)
   (fn-psc-model-source-info-complete fn-psc-model-source-info-cost fn-psc-model-source-v1-complete fn-psc-model-source-v2-complete
    fn-psc-model-source-v1-cost fn-psc-model-source-v2-cost fn-psc-info-compare fn-psc-msgid-compare fn-psc-step
    fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-model-captured-date fn-psc-model-retained-agent
    fn-record-string-octets fn-pbb-strip-at fn-pbb-strip-info-at fn-inj-message-id-line fn-inj-date-line
    fn-psc-source-info-complete-is-current-buffer-strip fn-psc-source-info-complete-is-actual-paid-steps fn-psc-source-v1-complete-is-actual-paid-steps
    fn-psc-source-v2-complete-is-actual-paid-steps fn-psc-source-byte-run-addition
    fn-psc-source-date-and-control-is-actual-paid-steps fn-psc-source-msgid-and-control-is-actual-paid-steps
    fn-psc-model-byte-run nth len update-nth nfix)))))

(in-theory (disable fn-psc-model-source-simple-complete fn-psc-model-source-v1-date-complete fn-psc-model-source-v1-complete fn-psc-model-source-v2-date-complete fn-psc-model-source-v2-complete fn-psc-model-source-after-stamp-complete fn-psc-model-source-simple-cost fn-psc-model-source-v1-date-cost fn-psc-model-source-v2-date-cost fn-psc-model-source-v2-cost fn-psc-model-source-v1-cost fn-psc-model-source-after-stamp-cost))
