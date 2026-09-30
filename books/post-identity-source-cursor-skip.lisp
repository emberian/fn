; Proof-only exact Cancel-Lock/Key skip over either leased source.
(in-package "ACL2")
(include-book "post-identity-source-cursor-block")
(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-psc-skip-tail-consp
 (implies (and (natp pos) (< pos (len xs))) (consp (nthcdr pos xs)))
 :hints (("Goal" :induct (nthcdr pos xs) :in-theory (enable nthcdr len)))))

(local (defthm fn-psc-skip-tail-head
 (implies (natp pos) (equal (car (nthcdr pos xs)) (nth pos xs)))
 :hints (("Goal" :induct (nthcdr pos xs) :in-theory (enable nthcdr nth)))))

(local (defthm fn-psc-skip-tail-next
 (implies (natp pos) (equal (cdr (nthcdr pos xs)) (nthcdr (+ 1 pos) xs)))
 :hints (("Goal" :induct (nthcdr pos xs) :in-theory (enable nthcdr)))))

(local (defthm fn-psc-skip-tail-at-end
 (implies (true-listp xs) (equal (nthcdr (len xs) xs) nil))
 :hints (("Goal" :induct (len xs) :in-theory (enable nthcdr len true-listp)))))

(local (defthm fn-psc-skip-line-end-is-first-line-length
 (implies (and (true-listp incoming) (natp pos) (<= pos (len incoming)))
  (equal (fn-oct-line-end pos incoming)
         (+ pos (len (fn-pb-line (nthcdr pos incoming))))))
 :hints (("Goal" :induct (fn-oct-line-end pos incoming)
  :in-theory (enable fn-oct-line-end fn-pb-line nthcdr len)))))

(local (defthm fn-psc-line-of-prefix-without-lf
 (implies (and (true-listp prefix) (not (member-equal 10 prefix)))
  (equal (fn-pb-line (append prefix xs)) (append prefix (fn-pb-line xs))))
 :hints (("Goal" :induct (len prefix)
  :in-theory (enable fn-pb-line append len true-listp member-equal)))))

(local (defthm fn-psc-strip-success-reconstructs
 (implies (and (true-listp prefix) (true-listp xs)
               (not (equal (fn-inj-strip prefix xs) :no)))
  (equal (append prefix (fn-inj-strip prefix xs)) xs))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip append true-listp)))))

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

(local (defthm fn-psc-skip-field-does-not-change-line-end
 (implies (and (true-listp incoming) (natp pos) (<= pos (len incoming))
               (true-listp field) (not (member-equal 10 field))
               (not (equal (fn-inj-strip field (nthcdr pos incoming)) :no)))
  (equal (fn-oct-line-end (+ pos (len field)) incoming) (fn-oct-line-end pos incoming)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-strip-success-reconstructs (prefix field) (xs (nthcdr pos incoming)))
        (:instance fn-psc-strip-success-is-exact-drop (prefix field) (xs (nthcdr pos incoming)))
        (:instance fn-psc-block-strip-success-bound (prefix field) (xs (nthcdr pos incoming)))
        (:instance fn-psc-nthcdr-composes-offsets (a pos) (b (len field)) (xs incoming))
        (:instance fn-psc-line-of-prefix-without-lf
         (prefix field) (xs (fn-inj-strip field (nthcdr pos incoming))))
        (:instance fn-psc-skip-line-end-is-first-line-length)
        (:instance fn-psc-skip-line-end-is-first-line-length (pos (+ pos (len field)))))
  :in-theory (disable fn-oct-line-end fn-pb-line fn-inj-strip nthcdr len binary-append
    fn-psc-strip-success-reconstructs fn-psc-strip-success-is-exact-drop
    fn-psc-block-strip-success-bound fn-psc-nthcdr-composes-offsets
    fn-psc-line-of-prefix-without-lf fn-psc-skip-line-end-is-first-line-length)))))

(defun fn-psc-model-skip-literal-complete (pos bytes resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-comparison-complete (fn-psc-literal pos bytes resume c) incoming held))

(local (defthm fn-psc-skip-literal-complete-frame
 (implies (and (natp pos) (true-listp bytes)
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let ((d (fn-psc-model-skip-literal-complete pos bytes resume c incoming held)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) resume)
        (equal (fn-psc-get base d) pos)
        (equal (if (fn-psc-get ok d) t nil)
               (not (equal (fn-inj-strip bytes (nthcdr pos (fn-psc-model-source c incoming held))) :no)))
        (implies (fn-psc-get ok d) (equal (fn-psc-get pos d) (+ pos (len bytes))))
        (equal (fn-psc-get n d) (fn-psc-get n c)) (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get agent-start d) (fn-psc-get agent-start c))
        (equal (fn-psc-get agent-end d) (fn-psc-get agent-end c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos bytes resume c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-literal pos bytes resume c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-literal pos bytes resume c)))
        (:instance fn-psc-literal-comparison-is-actual-strip))
  :in-theory (e/d (fn-psc-model-skip-literal-complete fn-psc-literal fn-psc-compare
                   fn-psc-comparison-statep fn-psc-comparison-positionp nfix)
   (fn-psc-model-comparison-complete fn-psc-model-source fn-psc-comparison-complete-returns-control
    fn-psc-comparison-complete-exact-flag fn-psc-comparison-complete-exact-position
    fn-psc-literal-comparison-is-actual-strip fn-inj-strip nth nthcdr len update-nth))))))

(defun fn-psc-skip-statep (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (and (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :start)
      (true-listp (fn-psc-model-source c incoming held))
      (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))))

(defun fn-psc-model-skip-lock-field (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-skip-literal-complete 0 *fn-cll-lock-field* :skip-lock c incoming held))

(defun fn-psc-model-skip-lock (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-skip-lock-field c incoming held)) (e (fn-psc-step d nil)))
  (if (fn-psc-get ok d) (fn-psc-step (fn-psc-model-line-complete e incoming held) nil) e)))

(defun fn-psc-model-skip-key-field (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-comparison-complete (fn-psc-model-skip-lock c incoming held) incoming held))

(defun fn-psc-model-skip-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-skip-key-field c incoming held)) (e (fn-psc-step d nil)))
  (if (fn-psc-get ok d) (fn-psc-model-line-complete e incoming held) e)))

(local (defthm fn-psc-skip-lock-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :skip-lock))
  (equal (fn-psc-step c byte)
   (if (fn-psc-get ok c) (fn-psc-set phase :line (fn-psc-set resume :after-lock c))
     (fn-psc-literal 0 *fn-cll-key-field* :skip-key c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control) (fn-psc-literal nth len update-nth))))))

(local (defthm fn-psc-after-lock-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :after-lock)
               (natp (fn-psc-get pos c)))
  (equal (fn-psc-step c byte) (fn-psc-literal (fn-psc-get pos c) *fn-cll-key-field* :skip-key c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control nfix) (fn-psc-literal nth len update-nth))))))

(local (defthm fn-psc-skip-key-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :skip-key)
               (natp (fn-psc-get base c)))
  (equal (fn-psc-step c byte)
   (if (fn-psc-get ok c) (fn-psc-set phase :line (fn-psc-set resume :after-key c))
     (fn-psc-return t (fn-psc-set resume :after-key (fn-psc-set pos (fn-psc-get base c) c))))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control nfix) (fn-psc-literal fn-psc-return nth len update-nth))))))

(local (defthm fn-psc-line-step-preserves-slot
 (implies (and (equal (fn-psc-get phase c) :line) (natp slot)
               (not (member-equal slot '(0 7 15 21 22))))
  (equal (nth slot (fn-psc-step c byte)) (nth slot c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-return nfix)
                               (nth update-nth len))))))

(local (defthm fn-psc-line-complete-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 15 21 22))))
  (equal (nth slot (fn-psc-model-line-complete c incoming held)) (nth slot c)))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held)
  :in-theory (e/d (fn-psc-model-line-complete)
                  (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-line-complete-preserves-state
 (implies (and (fn-psc-line-statep c incoming held)
               (equal (fn-psc-get phase c) :line))
  (fn-psc-line-statep (fn-psc-model-line-complete c incoming held) incoming held))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held)
  :in-theory (e/d (fn-psc-model-line-complete)
                  (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-line-complete-exact-position
 (implies (and (fn-psc-line-statep c incoming held)
               (equal (fn-psc-get phase c) :line))
  (equal (fn-psc-get pos (fn-psc-model-line-complete c incoming held))
         (+ (fn-psc-get pos c)
            (len (fn-pb-line (nthcdr (fn-psc-get pos c) (fn-psc-model-source c incoming held)))))))
 :hints (("Goal" :use (fn-psc-line-complete-preserves-value fn-psc-line-complete-returns-control fn-psc-line-complete-preserves-state)
  :in-theory (e/d (fn-psc-model-line-end fn-psc-line-statep nfix)
   (fn-psc-line-complete-preserves-value fn-psc-line-complete-returns-control fn-psc-line-complete-preserves-state
    fn-psc-model-line-complete nth nthcdr len))))))

(local (defthm fn-psc-skip-line-complete-frame
 (implies (and (equal (fn-psc-get phase c) :line) (fn-psc-line-statep c incoming held)
               (true-listp (fn-psc-model-source c incoming held)))
  (let ((d (fn-psc-model-line-complete c incoming held)))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) (fn-psc-get resume c))
        (equal (fn-psc-get pos d) (fn-oct-line-end (fn-psc-get pos c) (fn-psc-model-source c incoming held)))
        (natp (fn-psc-get pos d)) (<= (fn-psc-get pos d) (fn-psc-get n c))
        (equal (fn-psc-get n d) (fn-psc-get n c)) (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get agent-start d) (fn-psc-get agent-start c))
        (equal (fn-psc-get agent-end d) (fn-psc-get agent-end c)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-line-complete-returns-control fn-psc-line-complete-exact-position
        fn-psc-line-complete-preserves-state
        (:instance fn-psc-skip-line-end-is-first-line-length
         (pos (fn-psc-get pos c)) (incoming (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-line-statep fn-psc-model-line-end nfix)
   (fn-psc-model-line-complete fn-psc-model-source fn-pb-line fn-oct-line-end nth len
    fn-psc-line-complete-returns-control fn-psc-line-complete-exact-position
    fn-psc-line-complete-preserves-state fn-psc-skip-line-end-is-first-line-length))))))

(local (defthm fn-psc-skip-lock-complete-frame
 (implies (fn-psc-skip-statep c incoming held)
  (let* ((source (fn-psc-model-source c incoming held))
         (p (fn-pbb-skip-one-at *fn-cll-lock-field* 0 source))
         (d (fn-psc-model-skip-lock c incoming held)))
   (and (equal (fn-psc-get phase d) :compare) (equal (fn-psc-get resume d) :skip-key)
        (equal (fn-psc-get pos d) p) (equal (fn-psc-get base d) p)
        (equal (fn-psc-get index d) 0) (equal (fn-psc-get ref d) *fn-cll-key-field*)
        (equal (fn-psc-get ref-start d) 0) (equal (fn-psc-get ref-len d) (len *fn-cll-key-field*))
        (natp p) (<= p (len source))
        (equal (fn-psc-get n d) (fn-psc-get n c)) (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get agent-start d) (fn-psc-get agent-start c))
        (equal (fn-psc-get agent-end d) (fn-psc-get agent-end c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pbb-strip-at-is-inj-strip (prefix *fn-cll-lock-field*) (i 0) (fn-octets (fn-psc-model-source c incoming held)))
        (:instance fn-psc-skip-literal-complete-frame (pos 0) (bytes *fn-cll-lock-field*) (resume :skip-lock))
        (:instance fn-psc-skip-line-complete-frame (c (fn-psc-step (fn-psc-model-skip-lock-field c incoming held) nil)))
        (:instance fn-psc-skip-field-does-not-change-line-end
         (pos 0) (field *fn-cll-lock-field*) (incoming (fn-psc-model-source c incoming held)))
        (:instance fn-psc-block-strip-success-bound
         (prefix *fn-cll-lock-field*) (xs (fn-psc-model-source c incoming held))))
  :expand ((:free (xs) (nthcdr 0 xs)))
  :in-theory (e/d (fn-psc-skip-statep fn-psc-model-skip-lock fn-psc-model-skip-lock-field
                   fn-psc-line-statep fn-psc-model-source fn-pbb-skip-one-at fn-psc-literal fn-psc-compare nfix)
   (fn-psc-step fn-psc-control fn-psc-model-line-complete fn-psc-model-skip-literal-complete
    fn-psc-skip-literal-complete-frame fn-psc-skip-line-complete-frame
    fn-psc-skip-field-does-not-change-line-end fn-psc-block-strip-success-bound
    fn-pbb-strip-at-is-inj-strip fn-oct-line-end fn-pb-line fn-inj-strip nth nthcdr len update-nth))))))

(local (defthm fn-psc-skip-literal-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-literal pos bytes resume c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-compare) (nth update-nth nfix len))))))

(local (defthm fn-psc-skip-literal-preserves-proper-state
 (implies (true-listp c) (true-listp (fn-psc-literal pos bytes resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-compare) (nth update-nth nfix len))))))

(local (defthm fn-psc-skip-literal-complete-shape
 (and (implies (equal (len c) 24) (equal (len (fn-psc-model-skip-literal-complete pos bytes resume c incoming held)) 24))
      (implies (true-listp c) (true-listp (fn-psc-model-skip-literal-complete pos bytes resume c incoming held))))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-skip-literal-complete)
    (fn-psc-literal fn-psc-model-comparison-complete nth len update-nth))))))

(local (defthm fn-psc-skip-line-complete-shape
 (and (implies (equal (len c) 24) (equal (len (fn-psc-model-line-complete c incoming held)) 24))
      (implies (true-listp c) (true-listp (fn-psc-model-line-complete c incoming held))))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held)
  :in-theory (e/d (fn-psc-model-line-complete)
    (fn-psc-step fn-psc-model-demanded-byte nth len update-nth))))))

(local (defthm fn-psc-skip-lock-complete-shape
 (and (implies (equal (len c) 24) (equal (len (fn-psc-model-skip-lock c incoming held)) 24))
      (implies (true-listp c) (true-listp (fn-psc-model-skip-lock c incoming held))))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-skip-lock fn-psc-model-skip-lock-field)
   (fn-psc-step fn-psc-model-line-complete fn-psc-model-skip-literal-complete nth len update-nth))))))

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

(local (defthm fn-psc-skip-key-entry-is-actual-literal
 (implies (and (fn-psc-skip-statep c incoming held) (true-listp c) (equal (len c) 24))
  (let* ((d (fn-psc-model-skip-lock c incoming held))
         (p (fn-pbb-skip-one-at *fn-cll-lock-field* 0 (fn-psc-model-source c incoming held))))
   (equal (fn-psc-literal p *fn-cll-key-field* :skip-key d) d)))
 :hints (("Goal" :do-not-induct t :use (fn-psc-skip-lock-complete-frame
  (:instance fn-psc-compare-current-fields-is-same (c (fn-psc-model-skip-lock c incoming held))))
  :in-theory (e/d (fn-psc-literal)
   (fn-psc-compare fn-psc-model-skip-lock fn-psc-skip-lock-complete-frame
    fn-psc-compare-current-fields-is-same fn-pbb-skip-one-at fn-psc-model-source nth len))))))

(local (defthm fn-psc-skip-key-field-complete-frame
 (implies (and (fn-psc-skip-statep c incoming held) (true-listp c) (equal (len c) 24))
  (let* ((source (fn-psc-model-source c incoming held))
         (p (fn-pbb-skip-one-at *fn-cll-lock-field* 0 source))
         (d (fn-psc-model-skip-key-field c incoming held)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) :skip-key)
        (equal (fn-psc-get base d) p)
        (equal (if (fn-psc-get ok d) t nil)
               (not (equal (fn-inj-strip *fn-cll-key-field* (nthcdr p source)) :no)))
        (implies (fn-psc-get ok d) (equal (fn-psc-get pos d) (+ p (len *fn-cll-key-field*))))
        (equal (fn-psc-get n d) (fn-psc-get n c)) (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get agent-start d) (fn-psc-get agent-start c))
        (equal (fn-psc-get agent-end d) (fn-psc-get agent-end c)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-skip-lock-complete-frame fn-psc-skip-key-entry-is-actual-literal
        (:instance fn-psc-skip-literal-complete-frame
         (c (fn-psc-model-skip-lock c incoming held))
         (pos (fn-pbb-skip-one-at *fn-cll-lock-field* 0 (fn-psc-model-source c incoming held)))
         (bytes *fn-cll-key-field*) (resume :skip-key)))
  :in-theory (e/d (fn-psc-model-skip-key-field fn-psc-model-skip-literal-complete fn-psc-skip-statep fn-psc-model-source)
   (fn-psc-model-skip-lock fn-psc-model-comparison-complete fn-psc-literal
    fn-psc-skip-lock-complete-frame fn-psc-skip-key-entry-is-actual-literal fn-psc-skip-literal-complete-frame
    fn-inj-strip fn-pbb-skip-one-at nth nthcdr len update-nth))))))

(defthm fn-psc-skip-complete-is-current-buffer-skip
 (implies (and (fn-psc-skip-statep c incoming held) (true-listp c) (equal (len c) 24))
  (let* ((source (fn-psc-model-source c incoming held)) (p (fn-pbb-skip-at source))
         (d (fn-psc-model-skip-complete c incoming held)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) :after-key)
        (equal (fn-psc-get pos d) p) (natp p) (<= p (len source))
        (equal (fn-psc-get n d) (fn-psc-get n c)) (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get agent-start d) (fn-psc-get agent-start c))
        (equal (fn-psc-get agent-end d) (fn-psc-get agent-end c)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-skip-key-field-complete-frame
        (:instance fn-psc-skip-line-complete-frame (c (fn-psc-step (fn-psc-model-skip-key-field c incoming held) nil)))
        (:instance fn-psc-skip-field-does-not-change-line-end
         (pos (fn-pbb-skip-one-at *fn-cll-lock-field* 0 (fn-psc-model-source c incoming held)))
         (field *fn-cll-key-field*) (incoming (fn-psc-model-source c incoming held)))
        (:instance fn-psc-block-strip-success-bound (prefix *fn-cll-key-field*)
         (xs (nthcdr (fn-pbb-skip-one-at *fn-cll-lock-field* 0 (fn-psc-model-source c incoming held))
                     (fn-psc-model-source c incoming held))))
        (:instance fn-pbb-strip-at-is-inj-strip (prefix *fn-cll-key-field*)
         (i (fn-pbb-skip-one-at *fn-cll-lock-field* 0 (fn-psc-model-source c incoming held)))
         (fn-octets (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-skip-statep fn-psc-model-skip-complete
                   fn-psc-line-statep fn-psc-model-source fn-pbb-skip-at fn-pbb-skip-one-at fn-psc-return nfix)
   (fn-psc-step fn-psc-control fn-psc-model-line-complete fn-psc-model-skip-key-field
    fn-psc-skip-key-field-complete-frame fn-psc-skip-line-complete-frame
    fn-psc-skip-field-does-not-change-line-end fn-psc-block-strip-success-bound
    fn-pbb-strip-at-is-inj-strip fn-oct-line-end fn-pb-line fn-inj-strip nth nthcdr len update-nth)))))

(local (defthm fn-psc-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(defun fn-psc-model-skip-lock-field-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (+ 1 (fn-psc-model-comparison-cost (fn-psc-literal 0 *fn-cll-lock-field* :skip-lock c) incoming held)))

(defun fn-psc-model-skip-lock-finish-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-skip-lock-field c incoming held)) (e (fn-psc-step d nil)))
  (if (fn-psc-get ok d) (+ 2 (fn-psc-model-line-cost e incoming held)) 1)))

(defun fn-psc-model-skip-key-field-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-comparison-cost (fn-psc-model-skip-lock c incoming held) incoming held))

(defun fn-psc-model-skip-key-finish-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-skip-key-field c incoming held)) (e (fn-psc-step d nil)))
  (+ 1 (if (fn-psc-get ok d) (fn-psc-model-line-cost e incoming held) 0))))

(defun fn-psc-model-skip-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (+ (fn-psc-model-skip-lock-field-cost c incoming held) (fn-psc-model-skip-lock-finish-cost c incoming held)
    (fn-psc-model-skip-key-field-cost c incoming held) (fn-psc-model-skip-key-finish-cost c incoming held)))

(local (defthm fn-psc-skip-start-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :start))
  (equal (fn-psc-step c byte) (fn-psc-literal 0 *fn-cll-lock-field* :skip-lock c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control) (fn-psc-literal nth len update-nth))))))

(local (defthm fn-psc-skip-lock-field-is-paid-trace
 (implies (fn-psc-skip-statep c incoming held)
  (equal (fn-psc-model-skip-lock-field c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-skip-lock-field-cost c incoming held) c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-is-actual-steps
         (c (fn-psc-literal 0 *fn-cll-lock-field* :skip-lock c)))
        (:instance fn-psc-byte-run-addition (a 1)
         (b (fn-psc-model-comparison-cost (fn-psc-literal 0 *fn-cll-lock-field* :skip-lock c) incoming held))))
  :expand ((fn-psc-model-byte-run 1 c incoming held) (:free (c) (fn-psc-model-byte-run 0 c incoming held)))
  :in-theory (e/d (fn-psc-skip-statep fn-psc-model-skip-lock-field fn-psc-model-skip-lock-field-cost
                   fn-psc-model-skip-literal-complete fn-psc-demand fn-psc-model-demanded-byte)
   (fn-psc-step fn-psc-literal fn-psc-model-byte-run fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-comparison-complete-is-actual-steps fn-psc-byte-run-addition nth len))))))

(local (defthm fn-psc-skip-line-and-control-is-paid-trace
 (implies (and (equal (fn-psc-get phase c) :line) (fn-psc-line-statep c incoming held))
  (equal (fn-psc-step (fn-psc-model-line-complete c incoming held) nil)
   (fn-psc-model-byte-run (+ 1 (fn-psc-model-line-cost c incoming held)) c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-line-complete-returns-control fn-psc-line-complete-is-actual-steps
        (:instance fn-psc-byte-run-addition (a (fn-psc-model-line-cost c incoming held)) (b 1)))
  :expand ((:free (c) (fn-psc-model-byte-run 1 c incoming held)) (:free (c) (fn-psc-model-byte-run 0 c incoming held)))
  :in-theory (e/d (fn-psc-demand fn-psc-model-demanded-byte)
   (fn-psc-step fn-psc-model-byte-run fn-psc-model-line-complete fn-psc-model-line-cost
    fn-psc-line-complete-returns-control fn-psc-line-complete-is-actual-steps fn-psc-byte-run-addition nth len))))))

(local (defthm fn-psc-skip-lock-finish-is-paid-trace
 (implies (fn-psc-skip-statep c incoming held)
  (equal (fn-psc-model-skip-lock c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-skip-lock-finish-cost c incoming held)
                         (fn-psc-model-skip-lock-field c incoming held) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-skip-literal-complete-frame (pos 0) (bytes *fn-cll-lock-field*) (resume :skip-lock))
        (:instance fn-psc-block-strip-success-bound (prefix *fn-cll-lock-field*) (xs (fn-psc-model-source c incoming held)))
        (:instance fn-psc-skip-line-and-control-is-paid-trace
         (c (fn-psc-step (fn-psc-model-skip-lock-field c incoming held) nil)))
        (:instance fn-psc-byte-run-addition (a 1)
         (c (fn-psc-model-skip-lock-field c incoming held))
         (b (+ 1 (fn-psc-model-line-cost (fn-psc-step (fn-psc-model-skip-lock-field c incoming held) nil) incoming held)))))
  :expand ((:free (c) (fn-psc-model-byte-run 1 c incoming held)) (:free (c) (fn-psc-model-byte-run 0 c incoming held))
           (:free (xs) (nthcdr 0 xs)))
  :in-theory (e/d (fn-psc-skip-statep fn-psc-model-skip-lock fn-psc-model-skip-lock-finish-cost
                   fn-psc-model-skip-lock-field fn-psc-demand fn-psc-model-demanded-byte
                   fn-psc-line-statep fn-psc-model-source nfix)
   (fn-psc-step fn-psc-control fn-psc-model-line-complete fn-psc-model-line-cost
    fn-psc-model-skip-literal-complete fn-psc-model-byte-run fn-psc-byte-run-addition
    fn-psc-skip-lock-field-is-paid-trace fn-psc-skip-literal-complete-frame
    fn-psc-block-strip-success-bound fn-psc-skip-line-and-control-is-paid-trace
    fn-inj-strip nth nthcdr len update-nth))))))

(local (defthm fn-psc-skip-key-field-is-paid-trace
 (equal (fn-psc-model-skip-key-field c incoming held)
  (fn-psc-model-byte-run (fn-psc-model-skip-key-field-cost c incoming held) (fn-psc-model-skip-lock c incoming held) incoming held))
 :hints (("Goal" :use ((:instance fn-psc-comparison-complete-is-actual-steps (c (fn-psc-model-skip-lock c incoming held))))
  :in-theory (e/d (fn-psc-model-skip-key-field fn-psc-model-skip-key-field-cost)
   (fn-psc-model-skip-lock fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-model-byte-run fn-psc-comparison-complete-is-actual-steps))))))

(local (defthm fn-psc-skip-key-finish-is-paid-trace
 (implies (and (fn-psc-skip-statep c incoming held) (true-listp c) (equal (len c) 24))
  (equal (fn-psc-model-skip-complete c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-skip-key-finish-cost c incoming held)
                         (fn-psc-model-skip-key-field c incoming held) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-skip-key-field-complete-frame
        (:instance fn-psc-line-complete-is-actual-steps (c (fn-psc-step (fn-psc-model-skip-key-field c incoming held) nil)))
        (:instance fn-psc-byte-run-addition (a 1)
         (c (fn-psc-model-skip-key-field c incoming held))
         (b (if (fn-psc-get ok (fn-psc-model-skip-key-field c incoming held))
                (fn-psc-model-line-cost (fn-psc-step (fn-psc-model-skip-key-field c incoming held) nil) incoming held) 0))))
  :expand ((:free (c) (fn-psc-model-byte-run 1 c incoming held)) (:free (c) (fn-psc-model-byte-run 0 c incoming held)))
  :in-theory (e/d (fn-psc-model-skip-complete fn-psc-model-skip-key-finish-cost fn-psc-demand fn-psc-model-demanded-byte)
   (fn-psc-step fn-psc-control fn-psc-model-line-complete fn-psc-model-line-cost fn-psc-model-skip-key-field
    fn-psc-model-byte-run fn-psc-byte-run-addition fn-psc-skip-key-field-complete-frame
    fn-psc-line-complete-is-actual-steps fn-psc-model-skip-lock fn-psc-model-skip-lock-field
    fn-psc-skip-lock-field-is-paid-trace fn-psc-skip-lock-finish-is-paid-trace fn-psc-skip-key-field-is-paid-trace
    fn-psc-model-skip-literal-complete nth len update-nth))))))

(defthm fn-psc-skip-complete-is-actual-paid-steps
 (implies (and (fn-psc-skip-statep c incoming held) (true-listp c) (equal (len c) 24))
  (equal (fn-psc-model-skip-complete c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-skip-cost c incoming held) c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-skip-lock-field-is-paid-trace fn-psc-skip-lock-finish-is-paid-trace
        fn-psc-skip-key-field-is-paid-trace fn-psc-skip-key-finish-is-paid-trace
        (:instance fn-psc-byte-run-addition
         (a (fn-psc-model-skip-lock-field-cost c incoming held))
         (b (+ (fn-psc-model-skip-lock-finish-cost c incoming held)
               (fn-psc-model-skip-key-field-cost c incoming held)
               (fn-psc-model-skip-key-finish-cost c incoming held))))
        (:instance fn-psc-byte-run-addition (c (fn-psc-model-skip-lock-field c incoming held))
         (a (fn-psc-model-skip-lock-finish-cost c incoming held))
         (b (+ (fn-psc-model-skip-key-field-cost c incoming held) (fn-psc-model-skip-key-finish-cost c incoming held))))
        (:instance fn-psc-byte-run-addition (c (fn-psc-model-skip-lock c incoming held))
         (a (fn-psc-model-skip-key-field-cost c incoming held))
         (b (fn-psc-model-skip-key-finish-cost c incoming held))))
  :in-theory (e/d (fn-psc-model-skip-cost)
   (fn-psc-model-skip-lock-field fn-psc-model-skip-lock fn-psc-model-skip-key-field fn-psc-model-skip-complete
    fn-psc-model-skip-literal-complete fn-psc-model-skip-lock-field-cost fn-psc-model-skip-lock-finish-cost
    fn-psc-model-skip-key-field-cost fn-psc-model-skip-key-finish-cost fn-psc-model-byte-run fn-psc-step
    fn-psc-byte-run-addition fn-psc-skip-lock-field-is-paid-trace fn-psc-skip-lock-finish-is-paid-trace
    fn-psc-skip-key-field-is-paid-trace fn-psc-skip-key-finish-is-paid-trace nth len nfix update-nth)))))

(in-theory (disable fn-psc-model-skip-complete fn-psc-model-skip-cost fn-psc-model-skip-key-field fn-psc-model-skip-key-field-cost fn-psc-model-skip-key-finish-cost fn-psc-model-skip-literal-complete fn-psc-model-skip-lock fn-psc-model-skip-lock-field fn-psc-model-skip-lock-field-cost fn-psc-model-skip-lock-finish-cost fn-psc-skip-statep))
