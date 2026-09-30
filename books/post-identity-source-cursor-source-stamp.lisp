; Proof-only exact Stamp geometry, including short clamped dates.
(in-package "ACL2")
(include-book "post-identity-source-cursor-source-after-stamp")
(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-psc-source-tail-past-end-is-nil
 (implies (and (true-listp xs) (natp i) (<= (len xs) i))
  (equal (nthcdr i xs) nil))
 :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr len true-listp)))))

(local (defthm fn-psc-source-tail-head-is-index-byte
 (implies (natp i) (equal (car (nthcdr i xs)) (nth i xs)))
 :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr nth)))))

(local (defthm fn-psc-source-nonempty-strip-mismatch-is-no
 (implies (and (consp prefix) (or (not (consp xs)) (not (equal (car xs) (car prefix)))))
  (equal (fn-inj-strip prefix xs) :no))
 :hints (("Goal" :expand ((fn-inj-strip prefix xs)) :in-theory (disable fn-inj-strip)))))

(local (defthm fn-psc-source-buffer-strip-at-is-current-list-strip-all-positions
 (implies (and (natp i) (true-listp xs))
  (equal (fn-inj-strip prefix (nthcdr i xs))
   (if (equal (fn-pbb-strip-at prefix i xs) :no) :no
    (nthcdr (fn-pbb-strip-at prefix i xs) xs))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (enable fn-pbb-strip-at fn-inj-strip)))))

(local (defthm fn-psc-source-buffer-strip-success-index
 (implies (and (natp i) (true-listp prefix)
               (not (equal (fn-pbb-strip-at prefix i xs) :no)))
  (equal (fn-pbb-strip-at prefix i xs) (+ i (len prefix))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (e/d (fn-pbb-strip-at) (nth))))))

(local (defthm fn-psc-source-strip-self-take-is-drop
 (implies (true-listp xs)
  (equal (fn-inj-strip (fn-inj-take k xs) xs) (fn-inj-drop k xs)))
 :hints (("Goal" :induct (fn-inj-take k xs)
  :in-theory (enable fn-inj-take fn-inj-drop fn-inj-strip true-listp)))))

(local (defthm fn-psc-source-drop-keeps-proper-list
 (implies (true-listp xs) (true-listp (fn-inj-drop k xs)))
 :hints (("Goal" :induct (fn-inj-drop k xs) :in-theory (enable fn-inj-drop true-listp)))))

(local (defthm fn-psc-source-self-take-prefix-strip-succeeds
 (implies (and (natp i) (true-listp xs))
  (not (equal (fn-pbb-strip-at (fn-inj-take k (nthcdr i xs)) i xs) :no)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-buffer-strip-at-is-current-list-strip-all-positions
         (prefix (fn-inj-take k (nthcdr i xs))))
        (:instance fn-psc-source-drop-keeps-proper-list (xs (nthcdr i xs))))
  :in-theory (disable fn-pbb-strip-at fn-inj-drop fn-inj-take fn-inj-strip nthcdr len
    fn-psc-source-buffer-strip-at-is-current-list-strip-all-positions)))))

(local (defthm fn-psc-source-tail-length
 (implies (and (natp j) (<= j (len xs)))
  (equal (len (nthcdr j xs)) (- (len xs) j)))
 :hints (("Goal" :induct (nthcdr j xs) :in-theory (enable nthcdr len)))))

(local (defthm fn-psc-source-take-is-clamped-take
 (implies (true-listp xs)
  (equal (fn-inj-take k xs) (take (min (nfix k) (len xs)) xs)))
 :hints (("Goal" :induct (fn-inj-take k xs) :in-theory (enable fn-inj-take)))))

(local (defthm fn-psc-source-clamped-date-is-self-prefix
 (implies (and (natp j) (<= j (len xs)) (true-listp xs))
  (equal (fn-oct-slice-list j (min (+ j 31) (len xs)) xs)
         (fn-inj-take 31 (nthcdr j xs))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-oct-slice-list-is-take-nthcdr
          (i j) (n (min (+ j 31) (len xs))) (fn-octets xs)))
  :in-theory (disable fn-oct-slice-list fn-inj-take nthcdr take)))))

(local (defthm fn-psc-source-self-take-prefix-strip-index
 (implies (and (natp i) (true-listp xs))
  (equal (fn-pbb-strip-at (fn-inj-take k (nthcdr i xs)) i xs)
         (+ i (len (fn-inj-take k (nthcdr i xs))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-buffer-strip-success-index
         (prefix (fn-inj-take k (nthcdr i xs))))
        fn-psc-source-self-take-prefix-strip-succeeds)
  :in-theory (disable fn-psc-source-buffer-strip-success-index
   fn-psc-source-self-take-prefix-strip-succeeds fn-pbb-strip-at fn-inj-take nthcdr len)))))

(local (defthm fn-psc-source-take-length
 (equal (len (fn-inj-take k xs)) (min (nfix k) (len xs)))
 :hints (("Goal" :induct (fn-inj-take k xs) :in-theory (enable fn-inj-take len)))))

(local (defthm fn-psc-source-crlf-past-end-is-no
 (implies (and (natp i) (<= (len xs) i))
  (equal (fn-pbb-strip-at '(13 10) i xs) :no))
 :hints (("Goal" :in-theory (enable fn-pbb-strip-at)))))

(local (defthm fn-psc-source-buffer-strip-compose
 (implies (and (true-listp prefix) (natp i))
  (equal (fn-pbb-strip-at (fn-inj-append prefix suffix) i xs)
   (let ((p (fn-pbb-strip-at prefix i xs)))
    (if (equal p :no) :no (fn-pbb-strip-at suffix p xs)))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (e/d (fn-pbb-strip-at fn-inj-append)
   (nth len  fn-psc-source-buffer-strip-success-index))))))

(local (defthm fn-psc-source-copied-date-crlf-is-fixed-skip
 (implies (and (natp j) (<= j (len xs)) (true-listp xs))
  (equal (fn-pbb-strip-at (fn-inj-append (fn-inj-take 31 (nthcdr j xs)) '(13 10)) j xs)
         (fn-pbb-strip-at '(13 10) (+ j 31) xs)))
 :hints (("Goal" :do-not-induct t
  :in-theory (disable fn-pbb-strip-at fn-inj-take fn-inj-append nthcdr len
                      fn-psc-source-take-is-clamped-take)))))

(defthm fn-psc-source-stamp-reference-is-fixed-skip
 (implies (and (natp pos) (<= pos (len xs)) (true-listp xs)
  (not (equal (fn-pbb-strip-at *fn-inj-injection-date-field* pos xs) :no)))
  (let* ((j (fn-pbb-strip-at *fn-inj-injection-date-field* pos xs))
         (date (fn-oct-slice-list j (min (+ j 31) (len xs)) xs)))
   (equal (fn-pbb-strip-at (fn-inj-injection-date-line date) pos xs)
          (fn-pbb-strip-at '(13 10) (+ j 31) xs))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-clamped-date-is-self-prefix
         (j (fn-pbb-strip-at *fn-inj-injection-date-field* pos xs)))
        (:instance fn-psc-source-copied-date-crlf-is-fixed-skip
         (j (fn-pbb-strip-at *fn-inj-injection-date-field* pos xs)))
        (:instance fn-psc-source-buffer-strip-success-index (i pos) (prefix *fn-inj-injection-date-field*))
        (:instance fn-pbb-strip-at-bounds
         (i pos) (prefix *fn-inj-injection-date-field*) (fn-octets xs)))
  :in-theory (e/d (fn-inj-injection-date-line)
    (min fn-pbb-strip-at fn-inj-append fn-oct-slice-list fn-inj-take nthcdr len
     fn-psc-source-buffer-strip-success-index
     fn-psc-source-clamped-date-is-self-prefix fn-psc-source-copied-date-crlf-is-fixed-skip)))))

(defun fn-psc-model-source-literal-complete (pos bytes resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-comparison-complete (fn-psc-literal pos bytes resume c) incoming held))

(defthm fn-psc-source-literal-complete-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (true-listp bytes))
  (let* ((d (fn-psc-model-source-literal-complete pos bytes resume c incoming held))
         (p (fn-pbb-strip-at bytes pos (fn-psc-model-source c incoming held))))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) resume)
        (equal (fn-psc-get base d) pos)
        (iff (fn-psc-get ok d) (not (equal p :no)))
        (implies (not (equal p :no)) (equal (fn-psc-get pos d) p))
        (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-model-source d incoming held) (fn-psc-model-source c incoming held))
        (equal (fn-psc-model-retained-agent d incoming) (fn-psc-model-retained-agent c incoming))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos bytes resume c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-literal pos bytes resume c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-literal pos bytes resume c)))
        (:instance fn-psc-literal-comparison-is-actual-strip (bytes bytes) (resume resume))
        (:instance fn-psc-source-buffer-strip-at-is-current-list-strip-all-positions (prefix bytes) (i pos) (xs (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-model-source-literal-complete fn-psc-source-contextp fn-psc-model-source
                   fn-psc-model-retained-agent fn-psc-literal fn-psc-compare fn-psc-comparison-statep fn-psc-comparison-positionp nfix)
   (fn-psc-model-comparison-complete fn-inj-strip fn-pbb-strip-at
    fn-psc-comparison-complete-returns-control fn-psc-comparison-complete-exact-flag
    fn-psc-comparison-complete-exact-position fn-psc-literal-comparison-is-actual-strip
    fn-psc-source-buffer-strip-at-is-current-list-strip-all-positions fn-psc-comparison-next-is-actual-paid-trace nth nthcdr len update-nth)))))

(local (defthm fn-psc-source-nonempty-strip-success-is-before-end
 (implies (and (consp prefix) (not (equal (fn-pbb-strip-at prefix i xs) :no)))
  (< i (len xs)))
 :hints (("Goal" :expand ((fn-pbb-strip-at prefix i xs))
  :in-theory (disable fn-pbb-strip-at nth len)))))

(defthm fn-psc-source-crlf-complete-establishes-captured-date
 (implies (and (fn-psc-source-contextp c incoming held) (natp j)
               (equal (fn-psc-get date c) j))
  (let ((d (fn-psc-model-source-literal-complete (+ j 31) '(13 10) :source-stamp-tail c incoming held)))
   (implies (fn-psc-get ok d) (fn-psc-source-date-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-literal-complete-frame (pos (+ j 31)) (bytes '(13 10)) (resume :source-stamp-tail)))
  :in-theory (e/d (fn-psc-source-date-contextp fn-psc-model-source-literal-complete fn-psc-literal fn-psc-compare)
   (fn-psc-source-literal-complete-frame fn-psc-model-comparison-complete
    fn-psc-source-contextp fn-psc-model-source fn-pbb-strip-at nth len update-nth)))))

(defthm fn-psc-source-stamp-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-stamp))
  (equal (fn-psc-step c nil)
   (if (fn-psc-get ok c)
    (fn-psc-literal (+ 31 (nfix (fn-psc-get pos c))) '(13 10) :source-stamp-tail
       (fn-psc-set date (nfix (fn-psc-get pos c)) c))
    (fn-psc-info-compare (nfix (fn-psc-get base c)) :source-info-simple c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-literal fn-psc-info-compare nth len update-nth nfix)))))

(defthm fn-psc-source-stamp-tail-callback
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :source-stamp-tail))
  (equal (fn-psc-step c nil)
   (if (fn-psc-get ok c)
    (fn-psc-info-compare (nfix (fn-psc-get pos c)) :source-info-v1
       (fn-psc-set k (nfix (fn-psc-get pos c)) c))
    (fn-psc-finish :no-source c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-finish fn-psc-info-compare nth len update-nth nfix)))))

(in-theory (disable fn-psc-model-source-literal-complete))
