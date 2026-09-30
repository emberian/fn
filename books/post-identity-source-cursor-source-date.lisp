; Proof-only captured-date source inverse and actual paid byte trace.
(in-package "ACL2")
(include-book "post-identity-source-cursor-source-info")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-psc-source-date-contextp (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-psc-source-contextp c incoming held)
      (natp (fn-psc-get date c))
      (<= (+ 31 (fn-psc-get date c)) (len (fn-psc-model-source c incoming held)))))

(defun fn-psc-model-captured-date (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-inj-take 31 (nthcdr (fn-psc-get date c) (fn-psc-model-source c incoming held))))

(defun fn-psc-model-source-date-field-complete (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-date-compare pos resume c) incoming held) nil))

(defun fn-psc-model-source-date-content-complete (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-step (fn-psc-model-comparison-complete
              (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c) incoming held) nil))

(defun fn-psc-model-source-date-tail-complete (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-step (fn-psc-model-comparison-complete (fn-psc-literal pos '(13 10) :date-tail c) incoming held) nil))

(defun fn-psc-model-source-date-complete (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-source-date-field-complete pos resume c incoming held)))
  (if (equal (fn-psc-get phase d) :compare)
   (let ((e (fn-psc-model-source-date-content-complete (fn-psc-get pos d) d incoming held)))
    (if (equal (fn-psc-get phase e) :compare)
     (fn-psc-model-source-date-tail-complete (fn-psc-get pos e) e incoming held) e)) d)))

(local (defthm fn-psc-self-reference-octets-are-incoming-view
 (implies (equal (fn-psc-get ref c) :self)
  (equal (fn-psc-model-reference-octets count index c incoming held)
         (fn-psc-model-reference-octets count index (fn-psc-set ref :incoming c)
                                      (fn-psc-model-source c incoming held) held)))
 :hints (("Goal" :induct (fn-psc-model-reference-octets count index c incoming held)
  :in-theory (e/d (fn-psc-model-reference-octets fn-psc-model-reference-byte)
   (fn-psc-model-source nth len update-nth nfix))))))

(local (defthm fn-psc-self-reference-octets
 (implies (and (equal (fn-psc-get ref c) :self)
               (natp (fn-psc-get ref-start c)) (natp index) (natp count)
               (true-listp (fn-psc-model-source c incoming held))
               (<= (+ (fn-psc-get ref-start c) index count) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-reference-octets count index c incoming held)
         (fn-inj-take count (nthcdr (+ (fn-psc-get ref-start c) index) (fn-psc-model-source c incoming held)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-incoming-reference-octets
         (c (fn-psc-set ref :incoming c)) (incoming (fn-psc-model-source c incoming held))))
  :in-theory (disable fn-psc-model-reference-octets fn-psc-model-source fn-inj-take nth nthcdr len update-nth)))))

(local (defthm fn-psc-self-comparison-is-source-span-strip
 (implies (and (natp pos) (natp off) (natp count)
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
               (<= (+ off count) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-compare-value (fn-psc-compare pos :self off count resume c) incoming held)
         (not (equal (fn-inj-strip (fn-inj-take count (nthcdr off (fn-psc-model-source c incoming held)))
                                  (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-prefix-is-actual-strip (remaining count) (index 0)
          (c (fn-psc-compare pos :self off count resume c)))
        (:instance fn-psc-self-reference-octets (count count) (index 0)
          (c (fn-psc-compare pos :self off count resume c))))
  :in-theory (e/d (fn-psc-compare fn-psc-model-compare-value fn-psc-model-source nfix)
   (fn-psc-prefix-is-actual-strip fn-psc-self-reference-octets fn-psc-self-reference-octets-are-incoming-view
    fn-psc-model-prefix fn-psc-model-reference-octets fn-inj-strip fn-inj-take nth nthcdr len update-nth))))))

(local (defthm fn-psc-comparison-complete-preserves-natural-position
 (implies (natp (fn-psc-get pos c))
  (natp (fn-psc-get pos (fn-psc-model-comparison-complete c incoming held))))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
  :in-theory (e/d (fn-psc-model-comparison-complete fn-psc-step fn-psc-return nfix)
   (fn-psc-control fn-psc-expected fn-psc-model-demanded-byte nth len update-nth))))))

(local (defthm fn-psc-source-comparison-step-natural-position
 (implies (and (natp (fn-psc-get pos c)) (member-eq (fn-psc-get phase c) '(:compare :target)))
  (natp (fn-psc-get pos (fn-psc-step c byte))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-return nfix)
  (fn-psc-control fn-psc-expected nth len update-nth))))))

(local (defthm fn-psc-source-date-field-complete-full-frame
 (implies (and (natp pos) (fn-psc-source-date-contextp c incoming held))
  (let* ((d (fn-psc-model-source-date-field-complete pos resume c incoming held))
         (ok (not (equal (fn-inj-strip *fn-inj-date-field*
                             (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
   (and (equal (fn-psc-get phase d) (if ok :compare :control))
        (equal (fn-psc-get resume d) (if ok :date-content resume))
        (implies ok (equal (fn-psc-get pos d) (+ pos 6)))
        (equal (fn-psc-get base d) (if ok (+ pos 6) pos))
        (equal (fn-psc-get aux d) resume) (equal (fn-psc-get k d) pos)
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get n d) (fn-psc-get n c))
        (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (implies ok (and (equal (fn-psc-get ref d) :self)
                         (equal (fn-psc-get ref-start d) (fn-psc-get date c))
                         (equal (fn-psc-get ref-len d) 31)
                         (equal (fn-psc-get index d) 0)))
        (implies (not ok) (not (fn-psc-get ok d))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-preserves-natural-position (c (fn-psc-date-compare pos resume c)))
        (:instance fn-psc-comparison-complete-returns-control (c (fn-psc-date-compare pos resume c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-date-compare pos resume c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-date-compare pos resume c)))
        (:instance fn-psc-literal-comparison-is-actual-strip
         (bytes *fn-inj-date-field*) (resume :date-field)
         (c (fn-psc-set k pos (fn-psc-set aux resume c)))))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source-date-field-complete fn-psc-date-compare fn-psc-model-source
                   fn-psc-step fn-psc-control fn-psc-compare fn-psc-literal fn-psc-return
                   fn-psc-comparison-statep fn-psc-comparison-positionp nfix)
   (fn-psc-model-comparison-complete fn-psc-model-compare-value
    fn-psc-comparison-complete-returns-control fn-psc-comparison-complete-exact-flag
    fn-psc-comparison-complete-exact-position fn-psc-literal-comparison-is-actual-strip
    fn-psc-comparison-complete-preserves-natural-position fn-psc-comparison-next-is-actual-paid-trace fn-psc-model-byte-run fn-inj-strip nth nthcdr len update-nth))))))

(local (defthm fn-psc-source-date-content-complete-full-frame
 (implies (and (natp pos) (fn-psc-source-date-contextp c incoming held))
  (let* ((d (fn-psc-model-source-date-content-complete pos c incoming held))
         (ok (not (equal (fn-inj-strip (fn-psc-model-captured-date c incoming held)
                           (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
   (and (equal (fn-psc-get phase d) (if ok :compare :control))
        (equal (fn-psc-get resume d) (if ok :date-tail (fn-psc-get aux c)))
        (equal (fn-psc-get aux d) (fn-psc-get aux c))
        (equal (fn-psc-get k d) (fn-psc-get k c))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get n d) (fn-psc-get n c))
        (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (implies ok (and (equal (fn-psc-get pos d) (+ pos 31))
                         (equal (fn-psc-get base d) (+ pos 31))
                         (equal (fn-psc-get ref-start d) 0)
                         (equal (fn-psc-get ref d) '(13 10))
                         (equal (fn-psc-get ref-len d) 2)
                         (equal (fn-psc-get index d) 0)))
        (implies (not ok) (not (fn-psc-get ok d))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-preserves-natural-position (c (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c)))
        (:instance fn-psc-comparison-complete-returns-control
         (c (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c)))
        (:instance fn-psc-comparison-complete-exact-flag
         (c (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c)))
        (:instance fn-psc-comparison-complete-exact-position
         (c (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c)))
        (:instance fn-psc-self-comparison-is-source-span-strip (off (fn-psc-get date c)) (count 31) (resume :date-content)))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-captured-date fn-psc-model-source-date-content-complete fn-psc-model-source
                   fn-psc-step fn-psc-control fn-psc-compare fn-psc-literal fn-psc-return
                   fn-psc-comparison-statep fn-psc-comparison-positionp nfix)
   (fn-psc-model-comparison-complete fn-psc-model-compare-value
    fn-psc-comparison-complete-returns-control fn-psc-comparison-complete-exact-flag
    fn-psc-comparison-complete-exact-position fn-psc-self-comparison-is-source-span-strip fn-psc-comparison-complete-preserves-natural-position fn-psc-comparison-next-is-actual-paid-trace fn-psc-model-byte-run
    fn-inj-strip nth nthcdr len update-nth))))))

(local (defthm fn-psc-source-date-tail-complete-frame
 (implies (and (natp pos)
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-source-date-tail-complete pos c incoming held))
         (ok (not (equal (fn-inj-strip '(13 10)
                           (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) (fn-psc-get aux c))
        (equal (if (fn-psc-get ok d) t nil) ok)
        (equal (fn-psc-get aux d) (fn-psc-get aux c))
        (equal (fn-psc-get k d) (fn-psc-get k c))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get n d) (fn-psc-get n c))
        (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (implies ok (equal (fn-psc-get pos d) (+ pos 2))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos '(13 10) :date-tail c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-literal pos '(13 10) :date-tail c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-literal pos '(13 10) :date-tail c)))
        (:instance fn-psc-literal-comparison-is-actual-strip (bytes '(13 10)) (resume :date-tail)))
  :in-theory (e/d (fn-psc-model-source-date-tail-complete fn-psc-model-source
                   fn-psc-step fn-psc-control fn-psc-compare fn-psc-literal fn-psc-return
                   fn-psc-comparison-statep fn-psc-comparison-positionp nfix)
   (fn-psc-model-comparison-complete fn-psc-model-compare-value
    fn-psc-comparison-complete-returns-control fn-psc-comparison-complete-exact-flag
    fn-psc-comparison-complete-exact-position fn-psc-literal-comparison-is-actual-strip
    fn-psc-comparison-next-is-actual-paid-trace fn-psc-model-byte-run fn-inj-strip nth nthcdr len update-nth))))))

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

(local (defthm fn-psc-date-compare-preserves-source-date-context
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-date-compare pos resume c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-date-compare fn-psc-literal fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source)
  (fn-psc-compare nth len update-nth nfix))))))

(local (defthm fn-psc-date-control-preserves-source-date-context
 (implies (and (fn-psc-source-date-contextp c incoming held)
               (equal (fn-psc-get phase c) :control)
               (member-eq (fn-psc-get resume c) '(:date-field :date-content :date-tail)))
  (fn-psc-source-date-contextp (fn-psc-step c byte) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source
                                 fn-psc-step fn-psc-control fn-psc-return fn-psc-literal fn-psc-compare)
  (nth len update-nth nfix))))))

(local (defthm fn-psc-source-date-field-preserves-context
 (implies (and (natp pos) (fn-psc-source-date-contextp c incoming held))
  (fn-psc-source-date-contextp (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-date-compare pos resume c)))
        (:instance fn-psc-date-compare-preserves-source-date-context)
        (:instance fn-psc-comparison-complete-preserves-source-date-context (c (fn-psc-date-compare pos resume c)))
        (:instance fn-psc-date-control-preserves-source-date-context
         (c (fn-psc-model-comparison-complete (fn-psc-date-compare pos resume c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-date-field-complete fn-psc-date-compare fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-step fn-psc-model-comparison-complete
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth nfix))))))

(local (defthm fn-psc-source-date-content-preserves-context
 (implies (and (natp pos) (fn-psc-source-date-contextp c incoming held))
  (fn-psc-source-date-contextp (fn-psc-model-source-date-content-complete pos c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control
         (c (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c)))
        (:instance fn-psc-compare-preserves-source-date-context (ref :self) (start (fn-psc-get date c)) (count 31) (resume :date-content))
        (:instance fn-psc-comparison-complete-preserves-source-date-context (c (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c)))
        (:instance fn-psc-date-control-preserves-source-date-context
         (c (fn-psc-model-comparison-complete (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-date-content-complete fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-step fn-psc-model-comparison-complete
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth nfix))))))

(local (defthm fn-psc-date-control-preserves-slot
 (implies (and (equal (fn-psc-get phase c) :control)
               (member-eq (fn-psc-get resume c) '(:date-field :date-content :date-tail))
               (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15))))
  (equal (nth slot (fn-psc-step c byte)) (nth slot c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control fn-psc-return fn-psc-literal fn-psc-compare nfix)
  (nth len update-nth))))))

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

(local (defthm fn-psc-source-date-field-keeps-captured-date
 (equal (fn-psc-model-captured-date (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held)
        (fn-psc-model-captured-date c incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-captured-date fn-psc-model-source)
  (fn-psc-model-source-date-field-complete fn-inj-take nth nthcdr len))))))

(local (defthm fn-psc-source-date-content-keeps-captured-date
 (equal (fn-psc-model-captured-date (fn-psc-model-source-date-content-complete pos c incoming held) incoming held)
        (fn-psc-model-captured-date c incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-captured-date fn-psc-model-source)
  (fn-psc-model-source-date-content-complete fn-inj-take nth nthcdr len))))))

(local (defthm fn-psc-source-date-tail-keeps-captured-date
 (equal (fn-psc-model-captured-date (fn-psc-model-source-date-tail-complete pos c incoming held) incoming held)
        (fn-psc-model-captured-date c incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-captured-date fn-psc-model-source)
  (fn-psc-model-source-date-tail-complete fn-inj-take nth nthcdr len))))))

(local (defthm fn-psc-strip-append-composes
 (implies (true-listp prefix)
  (equal (fn-inj-strip (fn-inj-append prefix suffix) xs)
         (fn-inj-strip suffix (fn-inj-strip prefix xs))))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip fn-inj-append true-listp)))))

(local (defthm fn-psc-strip-success-is-exact-drop
 (implies (and (true-listp prefix) (not (equal (fn-inj-strip prefix xs) :no)))
  (equal (fn-inj-strip prefix xs) (nthcdr (len prefix) xs)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip nthcdr len true-listp)))))

(local (defthm fn-psc-nthcdr-composes-offsets
 (implies (and (natp a) (natp b))
  (equal (nthcdr b (nthcdr a xs)) (nthcdr (+ a b) xs)))
 :hints (("Goal" :induct (nthcdr a xs) :in-theory (enable nthcdr)))))

(local (defthm fn-psc-block-strip-success-bound
 (implies (and (true-listp prefix) (true-listp xs)
               (not (equal (fn-inj-strip prefix xs) :no)))
  (<= (len prefix) (len xs)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip len true-listp)))))

(local (defthm fn-psc-block-nthcdr-length
 (implies (and (true-listp xs) (natp start) (<= start (len xs)))
  (equal (len (nthcdr start xs)) (- (len xs) start)))
 :hints (("Goal" :induct (nthcdr start xs) :in-theory (enable nthcdr len true-listp)))))

(local (defthm fn-psc-length-of-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (len a) :in-theory (enable append len)))))

(local (defthm fn-psc-date-line-strip-is-three-indexed-stages
 (implies (and (true-listp date) (equal (len date) 31) (natp pos))
  (equal (not (equal (fn-inj-strip (fn-inj-date-line date) (nthcdr pos source)) :no))
   (and (not (equal (fn-inj-strip *fn-inj-date-field* (nthcdr pos source)) :no))
        (not (equal (fn-inj-strip date (nthcdr (+ pos 6) source)) :no))
        (not (equal (fn-inj-strip '(13 10) (nthcdr (+ pos 37) source)) :no)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-strip-success-is-exact-drop (prefix *fn-inj-date-field*) (xs (nthcdr pos source)))
        (:instance fn-psc-strip-success-is-exact-drop (prefix date) (xs (nthcdr (+ pos 6) source)))
        (:instance fn-psc-strip-append-composes (prefix *fn-inj-date-field*) (suffix (fn-inj-append date '(13 10))) (xs (nthcdr pos source)))
        (:instance fn-psc-strip-append-composes (prefix date) (suffix '(13 10)) (xs (nthcdr (+ pos 6) source))))
  :in-theory (e/d (fn-inj-date-line)
   (fn-psc-strip-success-is-exact-drop fn-psc-strip-append-composes fn-inj-append fn-inj-strip nth nthcdr len))))))

(local (defthm fn-psc-source-date-tail-preserves-context
 (implies (and (natp pos) (fn-psc-source-date-contextp c incoming held))
  (fn-psc-source-date-contextp (fn-psc-model-source-date-tail-complete pos c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos '(13 10) :date-tail c)))
        (:instance fn-psc-compare-preserves-source-date-context (ref '(13 10)) (start 0) (count 2) (resume :date-tail))
        (:instance fn-psc-comparison-complete-preserves-source-date-context (c (fn-psc-literal pos '(13 10) :date-tail c)))
        (:instance fn-psc-date-control-preserves-source-date-context
         (c (fn-psc-model-comparison-complete (fn-psc-literal pos '(13 10) :date-tail c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-date-tail-complete fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-step fn-psc-model-comparison-complete
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth nfix))))))

(local (defthm fn-psc-captured-date-is-proper-length31
 (implies (fn-psc-source-date-contextp c incoming held)
  (and (true-listp (fn-psc-model-captured-date c incoming held))
       (equal (len (fn-psc-model-captured-date c incoming held)) 31)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-date-contextp fn-psc-model-captured-date)
  (fn-psc-source-contextp fn-psc-model-source fn-inj-take nth nthcdr len))))))

(local (defthm fn-psc-source-date-complete-is-current-date-strip
 (implies (and (natp pos) (fn-psc-source-date-contextp c incoming held))
  (let* ((d (fn-psc-model-source-date-complete pos resume c incoming held))
         (ok (not (equal (fn-inj-strip
                  (fn-inj-date-line (fn-psc-model-captured-date c incoming held))
                  (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) resume)
        (equal (if (fn-psc-get ok d) t nil) ok)
        (equal (fn-psc-get k d) pos) (equal (fn-psc-get aux d) resume)
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get n d) (fn-psc-get n c))
        (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (implies ok (equal (fn-psc-get pos d) (+ pos 39))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-date-field-preserves-context)
        (:instance fn-psc-source-date-content-preserves-context
          (pos (fn-psc-get pos (fn-psc-model-source-date-field-complete pos resume c incoming held)))
          (c (fn-psc-model-source-date-field-complete pos resume c incoming held)))
        (:instance fn-psc-source-date-field-complete-full-frame)
        (:instance fn-psc-source-date-content-complete-full-frame
         (pos (fn-psc-get pos (fn-psc-model-source-date-field-complete pos resume c incoming held)))
         (c (fn-psc-model-source-date-field-complete pos resume c incoming held)))
        (:instance fn-psc-source-date-tail-complete-frame
         (pos (fn-psc-get pos (fn-psc-model-source-date-content-complete
                (fn-psc-get pos (fn-psc-model-source-date-field-complete pos resume c incoming held))
                (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held)))
         (c (fn-psc-model-source-date-content-complete
                (fn-psc-get pos (fn-psc-model-source-date-field-complete pos resume c incoming held))
                (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held)))
        (:instance fn-psc-date-line-strip-is-three-indexed-stages
         (date (fn-psc-model-captured-date c incoming held)) (source (fn-psc-model-source c incoming held)))
        fn-psc-captured-date-is-proper-length31)
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source-date-complete fn-psc-model-source)
   (fn-psc-model-source-date-field-complete fn-psc-model-source-date-content-complete fn-psc-model-source-date-tail-complete
    fn-psc-source-date-field-complete-full-frame fn-psc-source-date-content-complete-full-frame
    fn-psc-source-date-tail-complete-frame fn-psc-date-line-strip-is-three-indexed-stages
    fn-psc-strip-success-is-exact-drop fn-inj-strip fn-psc-model-captured-date
    fn-inj-date-line nth nthcdr len update-nth length nfix))))))

(local (defthm fn-psc-inj-append-is-append
 (equal (fn-inj-append xs ys) (append xs ys))
 :hints (("Goal" :induct (len xs) :in-theory (enable fn-inj-append append len)))))

(local (defthm fn-psc-captured-date-line-is-proper-length39
 (implies (fn-psc-source-date-contextp c incoming held)
  (and (true-listp (fn-inj-date-line (fn-psc-model-captured-date c incoming held)))
       (equal (len (fn-inj-date-line (fn-psc-model-captured-date c incoming held))) 39)))
 :hints (("Goal" :use fn-psc-captured-date-is-proper-length31
  :in-theory (e/d (fn-inj-date-line)
   (fn-psc-source-date-contextp fn-psc-model-captured-date len))))))

(local (defthm fn-psc-source-buffer-strip-success-index
 (implies (and (natp i) (true-listp prefix)
               (not (equal (fn-pbb-strip-at prefix i xs) :no)))
  (equal (fn-pbb-strip-at prefix i xs) (+ i (len prefix))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (e/d (fn-pbb-strip-at) (nth))))))

(local (defthm fn-psc-source-date-field-preserves-context-at-any-position
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-date-compare pos resume c)))
        (:instance fn-psc-date-compare-preserves-source-date-context)
        (:instance fn-psc-comparison-complete-preserves-source-date-context (c (fn-psc-date-compare pos resume c)))
        (:instance fn-psc-date-control-preserves-source-date-context
         (c (fn-psc-model-comparison-complete (fn-psc-date-compare pos resume c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-date-field-complete fn-psc-date-compare fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-step fn-psc-model-comparison-complete
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth nfix))))))

(local (defthm fn-psc-source-date-content-preserves-context-at-any-position
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-model-source-date-content-complete pos c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control
         (c (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c)))
        (:instance fn-psc-compare-preserves-source-date-context (ref :self) (start (fn-psc-get date c)) (count 31) (resume :date-content))
        (:instance fn-psc-comparison-complete-preserves-source-date-context (c (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c)))
        (:instance fn-psc-date-control-preserves-source-date-context
         (c (fn-psc-model-comparison-complete (fn-psc-compare pos :self (fn-psc-get date c) 31 :date-content c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-date-content-complete fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-step fn-psc-model-comparison-complete
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth nfix))))))

(local (defthm fn-psc-source-date-tail-preserves-context-at-any-position
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-model-source-date-tail-complete pos c incoming held) incoming held))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos '(13 10) :date-tail c)))
        (:instance fn-psc-compare-preserves-source-date-context (ref '(13 10)) (start 0) (count 2) (resume :date-tail))
        (:instance fn-psc-comparison-complete-preserves-source-date-context (c (fn-psc-literal pos '(13 10) :date-tail c)))
        (:instance fn-psc-date-control-preserves-source-date-context
         (c (fn-psc-model-comparison-complete (fn-psc-literal pos '(13 10) :date-tail c) incoming held)) (byte nil)))
  :in-theory (e/d (fn-psc-model-source-date-tail-complete fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
   (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-model-source fn-psc-step fn-psc-model-comparison-complete
    fn-psc-comparison-complete-returns-control fn-psc-comparison-next-is-actual-paid-trace nth len update-nth nfix))))))

(local (defthm fn-psc-source-date-complete-preserves-context
 (implies (fn-psc-source-date-contextp c incoming held)
  (fn-psc-source-date-contextp (fn-psc-model-source-date-complete pos resume c incoming held) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source-date-complete)
  (fn-psc-source-date-contextp fn-psc-model-source-date-field-complete fn-psc-model-source-date-content-complete
   fn-psc-model-source-date-tail-complete nth len))))))

(local (defthm fn-psc-source-date-complete-keeps-captured-date
 (equal (fn-psc-model-captured-date (fn-psc-model-source-date-complete pos resume c incoming held) incoming held)
        (fn-psc-model-captured-date c incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source-date-complete)
  (fn-psc-model-captured-date fn-psc-model-source-date-field-complete fn-psc-model-source-date-content-complete
   fn-psc-model-source-date-tail-complete nth len))))))

(local (defthm fn-psc-proper-tail-not-sentinel
 (implies (true-listp xs) (not (equal (nthcdr p xs) :no)))
 :hints (("Goal" :induct (nthcdr p xs) :in-theory (enable nthcdr true-listp)))))

(defthm fn-psc-source-date-complete-is-current-buffer-strip
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-source-date-complete pos resume c incoming held))
         (p (fn-pbb-strip-at (fn-inj-date-line (fn-psc-model-captured-date c incoming held))
                              pos (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) resume)
        (iff (fn-psc-get ok d) (not (equal p :no)))
        (implies (not (equal p :no)) (equal (fn-psc-get pos d) p))
        (fn-psc-source-date-contextp d incoming held)
        (equal (fn-psc-model-captured-date d incoming held) (fn-psc-model-captured-date c incoming held)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-date-complete-is-current-date-strip fn-psc-source-date-complete-preserves-context
        fn-psc-captured-date-line-is-proper-length39
        (:instance fn-pbb-strip-at-is-inj-strip
         (prefix (fn-inj-date-line (fn-psc-model-captured-date c incoming held)))
         (i pos) (fn-octets (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp)
   (fn-psc-model-source-date-complete fn-psc-model-source fn-psc-model-captured-date fn-inj-date-line
    fn-pbb-strip-at fn-pbb-strip-at-is-inj-strip fn-inj-strip
    fn-psc-source-date-complete-is-current-date-strip fn-psc-source-date-complete-preserves-context
    fn-psc-captured-date-line-is-proper-length39 fn-psc-strip-success-is-exact-drop nth nthcdr len)))))

(local (defthm fn-psc-update-current-slot-is-same
 (implies (and (natp slot) (< slot (len c)) (true-listp c))
  (equal (update-nth slot (nth slot c) c) c))
 :hints (("Goal" :induct (nth slot c)
  :in-theory (enable nth update-nth len true-listp)))))

(local (defthm fn-psc-compare-current-fields-is-same
 (implies (and (true-listp c) (equal (len c) 24)
               (equal (fn-psc-get phase c) :compare)
               (equal (fn-psc-get index c) 0)
               (equal (fn-psc-get base c) (fn-psc-get pos c))
               (natp (fn-psc-get pos c)) (natp (fn-psc-get ref-start c))
               (natp (fn-psc-get ref-len c)))
  (equal (fn-psc-compare (fn-psc-get pos c) (fn-psc-get ref c)
          (fn-psc-get ref-start c) (fn-psc-get ref-len c) (fn-psc-get resume c) c) c))
 :hints (("Goal" :use ((:instance fn-psc-update-current-slot-is-same (slot 0))
                         (:instance fn-psc-update-current-slot-is-same (slot 8))
                         (:instance fn-psc-update-current-slot-is-same (slot 12)))
  :in-theory (e/d (fn-psc-compare nfix)
                                (nth update-nth len true-listp))))))

(local (defthm fn-psc-source-date-field-success-is-actual-content-entry
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (equal (fn-psc-get phase (fn-psc-model-source-date-field-complete pos resume c incoming held)) :compare))
  (let ((d (fn-psc-model-source-date-field-complete pos resume c incoming held)))
   (equal (fn-psc-compare (fn-psc-get pos d) :self (fn-psc-get date d) 31 :date-content d) d)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-date-field-complete-full-frame fn-psc-source-date-field-preserves-context-at-any-position
        (:instance fn-psc-compare-current-fields-is-same
          (c (fn-psc-model-source-date-field-complete pos resume c incoming held))))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp)
   (fn-psc-model-source-date-field-complete fn-psc-compare fn-psc-compare-current-fields-is-same
    fn-psc-source-date-field-complete-full-frame fn-psc-source-date-field-preserves-context fn-psc-source-date-field-preserves-context-at-any-position
    fn-psc-model-source fn-inj-strip nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-source-date-content-success-is-actual-tail-entry
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (equal (fn-psc-get phase (fn-psc-model-source-date-content-complete pos c incoming held)) :compare))
  (let ((d (fn-psc-model-source-date-content-complete pos c incoming held)))
   (equal (fn-psc-literal (fn-psc-get pos d) '(13 10) :date-tail d) d)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-date-content-complete-full-frame fn-psc-source-date-content-preserves-context-at-any-position
        (:instance fn-psc-compare-current-fields-is-same
          (c (fn-psc-model-source-date-content-complete pos c incoming held))))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-source-contextp fn-psc-literal)
   (fn-psc-model-source-date-content-complete fn-psc-compare fn-psc-compare-current-fields-is-same
    fn-psc-source-date-content-complete-full-frame fn-psc-source-date-content-preserves-context fn-psc-source-date-content-preserves-context-at-any-position
    fn-psc-model-source fn-inj-strip nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-source-date-field-complete-is-actual-paid-steps
 (equal (fn-psc-model-source-date-field-complete pos resume c incoming held)
        (fn-psc-model-byte-run
         (+ 1 (fn-psc-model-comparison-cost (fn-psc-date-compare pos resume c) incoming held))
         (fn-psc-date-compare pos resume c) incoming held))
 :hints (("Goal" :use ((:instance fn-psc-comparison-next-is-actual-paid-trace
                        (c (fn-psc-date-compare pos resume c))))
  :in-theory (e/d (fn-psc-model-source-date-field-complete fn-psc-date-compare
                   fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
    (fn-psc-step fn-psc-model-comparison-complete fn-psc-model-byte-run
     fn-psc-model-comparison-cost fn-psc-comparison-next-is-actual-paid-trace nth nfix len update-nth))))))

(local (defthm fn-psc-source-date-content-stage-is-actual-paid-steps
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (equal (fn-psc-get phase (fn-psc-model-source-date-field-complete pos resume c incoming held)) :compare))
  (let ((d (fn-psc-model-source-date-field-complete pos resume c incoming held)))
   (equal (fn-psc-model-source-date-content-complete (fn-psc-get pos d) d incoming held)
          (fn-psc-model-byte-run (+ 1 (fn-psc-model-comparison-cost d incoming held)) d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-date-field-complete-full-frame fn-psc-source-date-field-success-is-actual-content-entry
        (:instance fn-psc-comparison-next-is-actual-paid-trace
         (c (fn-psc-model-source-date-field-complete pos resume c incoming held))))
  :in-theory (e/d (fn-psc-model-source-date-content-complete fn-psc-comparison-statep length)
   (fn-psc-model-source-date-field-complete fn-psc-compare fn-psc-step fn-psc-model-comparison-complete
    fn-psc-model-byte-run fn-psc-model-comparison-cost fn-psc-source-date-field-complete-full-frame
    fn-psc-source-date-field-success-is-actual-content-entry fn-psc-comparison-next-is-actual-paid-trace
    nth nfix len update-nth fn-psc-model-source fn-inj-strip))))))

(local (defthm fn-psc-source-date-tail-stage-is-actual-paid-steps
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos)
               (equal (fn-psc-get phase (fn-psc-model-source-date-content-complete pos c incoming held)) :compare))
  (let ((d (fn-psc-model-source-date-content-complete pos c incoming held)))
   (equal (fn-psc-model-source-date-tail-complete (fn-psc-get pos d) d incoming held)
          (fn-psc-model-byte-run (+ 1 (fn-psc-model-comparison-cost d incoming held)) d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-date-content-complete-full-frame fn-psc-source-date-content-success-is-actual-tail-entry
        (:instance fn-psc-comparison-next-is-actual-paid-trace
         (c (fn-psc-model-source-date-content-complete pos c incoming held))))
  :in-theory (e/d (fn-psc-model-source-date-tail-complete fn-psc-comparison-statep)
   (fn-psc-model-source-date-content-complete fn-psc-literal fn-psc-step fn-psc-model-comparison-complete
    fn-psc-model-byte-run fn-psc-model-comparison-cost fn-psc-source-date-content-complete-full-frame
    fn-psc-source-date-content-success-is-actual-tail-entry fn-psc-comparison-next-is-actual-paid-trace
    nth nfix len update-nth fn-psc-model-source fn-inj-strip))))))

(defun fn-psc-model-source-date-cost (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((entry (fn-psc-date-compare pos resume c))
        (d (fn-psc-model-source-date-field-complete pos resume c incoming held)))
  (+ 1 (fn-psc-model-comparison-cost entry incoming held)
     (if (equal (fn-psc-get phase d) :compare)
         (let ((e (fn-psc-model-source-date-content-complete (fn-psc-get pos d) d incoming held)))
          (+ 1 (fn-psc-model-comparison-cost d incoming held)
             (if (equal (fn-psc-get phase e) :compare)
                 (+ 1 (fn-psc-model-comparison-cost e incoming held)) 0))) 0))))

(defthm fn-psc-source-date-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-date-contextp c incoming held) (natp pos))
  (equal (fn-psc-model-source-date-complete pos resume c incoming held)
         (fn-psc-model-byte-run (fn-psc-model-source-date-cost pos resume c incoming held)
                               (fn-psc-date-compare pos resume c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-date-field-preserves-context-at-any-position
        fn-psc-source-date-field-complete-full-frame
        fn-psc-source-date-field-complete-is-actual-paid-steps
        fn-psc-source-date-content-stage-is-actual-paid-steps
        (:instance fn-psc-source-date-tail-stage-is-actual-paid-steps
         (c (fn-psc-model-source-date-field-complete pos resume c incoming held))
         (pos (fn-psc-get pos (fn-psc-model-source-date-field-complete pos resume c incoming held))))
        (:instance fn-psc-byte-run-addition
         (c (fn-psc-date-compare pos resume c))
         (a (+ 1 (fn-psc-model-comparison-cost (fn-psc-date-compare pos resume c) incoming held)))
         (b (if (equal (fn-psc-get phase (fn-psc-model-source-date-field-complete pos resume c incoming held)) :compare)
                (+ 1 (fn-psc-model-comparison-cost (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held)
                 (if (equal (fn-psc-get phase (fn-psc-model-source-date-content-complete
                     (fn-psc-get pos (fn-psc-model-source-date-field-complete pos resume c incoming held))
                     (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held)) :compare)
                     (+ 1 (fn-psc-model-comparison-cost (fn-psc-model-source-date-content-complete
                     (fn-psc-get pos (fn-psc-model-source-date-field-complete pos resume c incoming held))
                     (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held) incoming held)) 0)) 0)))
        (:instance fn-psc-byte-run-addition
         (c (fn-psc-model-source-date-field-complete pos resume c incoming held))
         (a (+ 1 (fn-psc-model-comparison-cost
                   (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held)))
         (b (if (equal (fn-psc-get phase (fn-psc-model-source-date-content-complete
                     (fn-psc-get pos (fn-psc-model-source-date-field-complete pos resume c incoming held))
                     (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held)) :compare)
                     (+ 1 (fn-psc-model-comparison-cost (fn-psc-model-source-date-content-complete
                     (fn-psc-get pos (fn-psc-model-source-date-field-complete pos resume c incoming held))
                     (fn-psc-model-source-date-field-complete pos resume c incoming held) incoming held) incoming held)) 0))))
  :expand ((:free (c) (fn-psc-model-byte-run 0 c incoming held)))
  :in-theory (e/d (fn-psc-model-source-date-complete fn-psc-model-source-date-cost fn-psc-model-source)
   (fn-psc-model-source-date-field-complete fn-psc-model-source-date-content-complete fn-psc-model-source-date-tail-complete
    fn-psc-model-byte-run fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-step fn-psc-date-compare fn-psc-source-date-field-complete-full-frame
    fn-psc-source-date-field-complete-is-actual-paid-steps fn-psc-source-date-content-stage-is-actual-paid-steps
    fn-psc-source-date-tail-stage-is-actual-paid-steps fn-psc-byte-run-addition
    fn-psc-source-date-field-preserves-context-at-any-position
    fn-psc-source-date-field-preserves-context
    fn-inj-strip nth nthcdr len update-nth nfix)))))

(in-theory (disable fn-psc-model-captured-date fn-psc-model-source-date-complete fn-psc-model-source-date-content-complete fn-psc-model-source-date-cost fn-psc-model-source-date-field-complete fn-psc-model-source-date-tail-complete fn-psc-source-date-contextp))
