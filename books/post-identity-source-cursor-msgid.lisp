; Proof-only exact retained Message-ID string comparison composition.
; Runtime remains the original leased byte-demand cursor.
(in-package "ACL2")
(include-book "post-identity-source-cursor-refinement")
(include-book "records-shape")
(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-psc-record-string-octets-length
 (equal (len (fn-record-string-octets-aux chars)) (len chars))
 :hints (("Goal" :induct (fn-record-string-octets-aux chars)
          :in-theory (enable fn-record-string-octets-aux len)))))

(local (defthm fn-psc-record-string-octets-nth
 (implies (and (natp index) (< index (len chars)))
  (equal (nth index (fn-record-string-octets-aux chars))
         (char-code (nth index chars))))
 :hints (("Goal" :induct (nth index chars)
  :in-theory (enable nth fn-record-string-octets-aux len)))))

(defthm fn-psc-msgid-reference-byte-is-record-octet
 (implies (and (equal (fn-psc-get ref c) :msgid)
               (stringp (fn-psc-get msgid c))
               (natp index) (natp (fn-psc-get ref-start c))
               (< (+ index (fn-psc-get ref-start c)) (length (fn-psc-get msgid c))))
  (equal (fn-psc-model-reference-byte c index incoming held)
         (nth (+ index (fn-psc-get ref-start c))
              (fn-record-string-octets (fn-psc-get msgid c)))))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-reference-byte fn-record-string-octets
                                  length char nfix)
                                 (nth len)))))

(local (defthm fn-psc-record-string-octets-proper
 (true-listp (fn-record-string-octets-aux chars))
 :hints (("Goal" :induct (fn-record-string-octets-aux chars)
                 :in-theory (enable fn-record-string-octets-aux)))))

(local (defthm fn-psc-tail-consp-unfolds
 (implies (natp index) (equal (consp (nthcdr index xs)) (< index (len xs))))
 :hints (("Goal" :induct (nthcdr index xs) :do-not (quote (generalize eliminate-destructors)) :in-theory (enable nthcdr len)) ("Subgoal *1/2.2'" :cases ((< index (+ 1 (len (cdr xs)))))))))

(local (defthm fn-psc-tail-head-unfolds
 (implies (natp index) (equal (car (nthcdr index xs)) (nth index xs)))
 :hints (("Goal" :induct (nthcdr index xs) :in-theory (enable nthcdr nth)))))

(local (defthm fn-psc-tail-successor-unfolds
 (implies (natp index) (equal (cdr (nthcdr index xs)) (nthcdr (+ 1 index) xs)))
 :hints (("Goal" :induct (nthcdr index xs) :in-theory (enable nthcdr)))))

(defthm fn-psc-msgid-reference-octets-is-record-span
 (implies (and (equal (fn-psc-get ref c) :msgid)
               (stringp (fn-psc-get msgid c))
               (natp index) (natp count) (natp (fn-psc-get ref-start c))
               (<= (+ index count (fn-psc-get ref-start c)) (length (fn-psc-get msgid c))))
  (equal (fn-psc-model-reference-octets count index c incoming held)
         (fn-inj-take count (nthcdr (+ index (fn-psc-get ref-start c))
                                   (fn-record-string-octets (fn-psc-get msgid c))))))
 :hints (("Goal" :induct (fn-psc-model-reference-octets count index c incoming held)
  :in-theory (e/d (fn-psc-model-reference-octets fn-inj-take fn-record-string-octets length nfix)
   (fn-psc-model-reference-byte nth nthcdr len)))))

(local (defthm fn-psc-take-length-of-proper-list
 (implies (true-listp xs) (equal (fn-inj-take (len xs) xs) xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable fn-inj-take len true-listp nfix)))))

(defthm fn-psc-msgid-content-comparison-is-record-string-strip
 (implies (and (natp pos) (stringp (fn-psc-get msgid c))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let ((entry (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c)))
   (equal (fn-psc-model-compare-value entry incoming held)
          (not (equal (fn-inj-strip (fn-record-string-octets (fn-psc-get msgid c))
                                    (nthcdr pos (fn-psc-model-source c incoming held))) :no)))))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (xs) (nthcdr 0 xs)))
  :use ((:instance fn-psc-take-length-of-proper-list
         (xs (fn-record-string-octets-aux (coerce (fn-psc-get msgid c) 'list))))
        (:instance fn-psc-prefix-is-actual-strip
         (remaining (length (fn-psc-get msgid c))) (index 0)
         (c (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c)))
        (:instance fn-psc-msgid-reference-octets-is-record-span
         (count (length (fn-psc-get msgid c))) (index 0)
         (c (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c))))
  :in-theory (e/d (fn-psc-compare fn-psc-model-compare-value fn-psc-model-source
                   fn-record-string-octets length nfix)
   (fn-psc-prefix-is-actual-strip fn-psc-msgid-reference-octets-is-record-span
    fn-psc-model-reference-octets fn-psc-model-prefix fn-inj-strip nth nthcdr len update-nth)))))

(defun fn-psc-model-msgid-field-complete (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-step (fn-psc-model-comparison-complete
               (fn-psc-msgid-compare pos resume c) incoming held) nil))

(defthm fn-psc-msgid-field-complete-full-frame
 (implies (and (natp pos) (stringp (fn-psc-get msgid c))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-msgid-field-complete pos resume c incoming held))
         (ok (not (equal (fn-inj-strip *fn-inj-message-id-field*
                             (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
   (and (equal (fn-psc-get phase d) (if ok :compare :control))
        (equal (fn-psc-get resume d) (if ok :msgid-content resume))
        (equal (fn-psc-get pos d) (if ok (+ pos 12) pos))
        (equal (fn-psc-get base d) (if ok (+ pos 12) pos))
        (equal (fn-psc-get aux d) resume) (equal (fn-psc-get k d) pos)
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get n d) (fn-psc-get n c))
        (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (implies ok (and (equal (fn-psc-get ref d) :msgid)
                         (equal (fn-psc-get ref-start d) 0)
                         (equal (fn-psc-get ref-len d) (length (fn-psc-get msgid c)))
                         (equal (fn-psc-get index d) 0)))
        (implies (not ok) (not (fn-psc-get ok d))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-msgid-compare pos resume c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-msgid-compare pos resume c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-msgid-compare pos resume c)))
        (:instance fn-psc-literal-comparison-is-actual-strip
         (bytes *fn-inj-message-id-field*) (resume :msgid-field)
         (c (fn-psc-set k pos (fn-psc-set aux resume c)))))
  :in-theory (e/d (fn-psc-model-msgid-field-complete fn-psc-msgid-compare fn-psc-model-source
                   fn-psc-step fn-psc-control fn-psc-compare fn-psc-literal fn-psc-return
                   fn-psc-comparison-statep fn-psc-comparison-positionp nfix)
   (fn-psc-model-comparison-complete fn-psc-model-compare-value
    fn-psc-comparison-complete-returns-control fn-psc-comparison-complete-exact-flag
    fn-psc-comparison-complete-exact-position fn-psc-literal-comparison-is-actual-strip
    fn-inj-strip nth nthcdr len update-nth)))))

(defun fn-psc-model-msgid-content-complete (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-step (fn-psc-model-comparison-complete
  (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c)
   incoming held) nil))

(defthm fn-psc-msgid-content-complete-full-frame
 (implies (and (natp pos) (stringp (fn-psc-get msgid c))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-msgid-content-complete pos c incoming held))
         (ok (not (equal (fn-inj-strip (fn-record-string-octets (fn-psc-get msgid c))
                           (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
   (and (equal (fn-psc-get phase d) (if ok :compare :control))
        (equal (fn-psc-get resume d) (if ok :msgid-tail (fn-psc-get aux c)))
        (equal (fn-psc-get aux d) (fn-psc-get aux c))
        (equal (fn-psc-get k d) (fn-psc-get k c))
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get n d) (fn-psc-get n c))
        (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (implies ok (and (equal (fn-psc-get pos d) (+ pos (length (fn-psc-get msgid c))))
                         (equal (fn-psc-get base d) (+ pos (length (fn-psc-get msgid c))))
                         (equal (fn-psc-get ref-start d) 0)
                         (equal (fn-psc-get ref d) '(13 10))
                         (equal (fn-psc-get ref-len d) 2)
                         (equal (fn-psc-get index d) 0)))
        (implies (not ok) (not (fn-psc-get ok d))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control
         (c (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c)))
        (:instance fn-psc-comparison-complete-exact-flag
         (c (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c)))
        (:instance fn-psc-comparison-complete-exact-position
         (c (fn-psc-compare pos :msgid 0 (length (fn-psc-get msgid c)) :msgid-content c)))
        (:instance fn-psc-msgid-content-comparison-is-record-string-strip))
  :in-theory (e/d (fn-psc-model-msgid-content-complete fn-psc-model-source
                   fn-psc-step fn-psc-control fn-psc-compare fn-psc-literal fn-psc-return
                   fn-psc-comparison-statep fn-psc-comparison-positionp nfix)
   (fn-psc-model-comparison-complete fn-psc-model-compare-value
    fn-psc-comparison-complete-returns-control fn-psc-comparison-complete-exact-flag
    fn-psc-comparison-complete-exact-position fn-psc-msgid-content-comparison-is-record-string-strip
    fn-inj-strip nth nthcdr len update-nth)))))

(defun fn-psc-model-msgid-tail-complete (pos c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-step (fn-psc-model-comparison-complete
               (fn-psc-literal pos '(13 10) :msgid-tail c) incoming held) nil))

(defthm fn-psc-msgid-tail-complete-frame
 (implies (and (natp pos)
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-msgid-tail-complete pos c incoming held))
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
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos '(13 10) :msgid-tail c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-literal pos '(13 10) :msgid-tail c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-literal pos '(13 10) :msgid-tail c)))
        (:instance fn-psc-literal-comparison-is-actual-strip (bytes '(13 10)) (resume :msgid-tail)))
  :in-theory (e/d (fn-psc-model-msgid-tail-complete fn-psc-model-source
                   fn-psc-step fn-psc-control fn-psc-compare fn-psc-literal fn-psc-return
                   fn-psc-comparison-statep fn-psc-comparison-positionp nfix)
   (fn-psc-model-comparison-complete fn-psc-model-compare-value
    fn-psc-comparison-complete-returns-control fn-psc-comparison-complete-exact-flag
    fn-psc-comparison-complete-exact-position fn-psc-literal-comparison-is-actual-strip
    fn-inj-strip nth nthcdr len update-nth)))))

(local (defthm fn-psc-strip-success-reconstructs
 (implies (and (true-listp prefix) (true-listp xs)
               (not (equal (fn-inj-strip prefix xs) :no)))
  (equal (append prefix (fn-inj-strip prefix xs)) xs))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip append true-listp)))))

(local (defthm fn-psc-strip-append-prefix
 (implies (true-listp a)
  (equal (fn-inj-strip (append a b) xs)
         (fn-inj-strip b (fn-inj-strip a xs))))
 :hints (("Goal" :induct (fn-inj-strip a xs)
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

(local (local (defthm fn-psc-inj-append-is-append
 (equal (fn-inj-append xs ys) (append xs ys))
 :hints (("Goal" :induct (len xs) :in-theory (enable fn-inj-append append len))))))

(local (defthm fn-psc-strip-failure-is-absorbing
 (equal (fn-inj-strip bytes :no) :no)
 :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local (defthm fn-psc-message-id-line-strip-is-three-indexed-stages
 (implies (and (stringp text) (natp pos))
  (equal
   (not (equal (fn-inj-strip (fn-inj-message-id-line (fn-record-string-octets text))
                             (nthcdr pos source)) :no))
   (and (not (equal (fn-inj-strip *fn-inj-message-id-field* (nthcdr pos source)) :no))
        (not (equal (fn-inj-strip (fn-record-string-octets text) (nthcdr (+ pos 12) source)) :no))
        (not (equal (fn-inj-strip '(13 10) (nthcdr (+ pos 12 (length text)) source)) :no)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-strip-success-is-exact-drop
         (prefix *fn-inj-message-id-field*) (xs (nthcdr pos source)))
        (:instance fn-psc-strip-success-is-exact-drop
         (prefix (fn-record-string-octets text)) (xs (nthcdr (+ pos 12) source)))
        (:instance fn-psc-strip-append-prefix
         (a *fn-inj-message-id-field*)
         (b (append (fn-record-string-octets text) '(13 10))) (xs (nthcdr pos source)))
        (:instance fn-psc-strip-append-prefix
         (a (fn-record-string-octets text)) (b '(13 10))
         (xs (fn-inj-strip *fn-inj-message-id-field* (nthcdr pos source)))))
  :in-theory (e/d (fn-inj-message-id-line fn-record-string-octets length)
   (fn-psc-strip-success-is-exact-drop binary-append fn-psc-strip-append-prefix fn-inj-strip fn-inj-take nth nthcdr len fn-record-string-octets-aux))))))

(defun fn-psc-model-msgid-complete (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-msgid-field-complete pos resume c incoming held)))
  (if (equal (fn-psc-get phase d) :compare)
      (let ((e (fn-psc-model-msgid-content-complete (fn-psc-get pos d) d incoming held)))
       (if (equal (fn-psc-get phase e) :compare)
           (fn-psc-model-msgid-tail-complete (fn-psc-get pos e) e incoming held) e)) d)))

(defthm fn-psc-msgid-complete-is-current-message-id-strip
 (implies (and (natp pos) (stringp (fn-psc-get msgid c))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-msgid-complete pos resume c incoming held))
         (ok (not (equal (fn-inj-strip
                  (fn-inj-message-id-line (fn-record-string-octets (fn-psc-get msgid c)))
                  (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) resume)
        (equal (if (fn-psc-get ok d) t nil) ok)
        (equal (fn-psc-get k d) pos) (equal (fn-psc-get aux d) resume)
        (equal (fn-psc-get msgid d) (fn-psc-get msgid c))
        (equal (fn-psc-get n d) (fn-psc-get n c))
        (equal (fn-psc-get mode d) (fn-psc-get mode c))
        (implies ok (equal (fn-psc-get pos d) (+ pos 14 (length (fn-psc-get msgid c))))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-msgid-field-complete-full-frame)
        (:instance fn-psc-msgid-content-complete-full-frame
         (pos (fn-psc-get pos (fn-psc-model-msgid-field-complete pos resume c incoming held)))
         (c (fn-psc-model-msgid-field-complete pos resume c incoming held)))
        (:instance fn-psc-msgid-tail-complete-frame
         (pos (fn-psc-get pos (fn-psc-model-msgid-content-complete
                (fn-psc-get pos (fn-psc-model-msgid-field-complete pos resume c incoming held))
                (fn-psc-model-msgid-field-complete pos resume c incoming held) incoming held)))
         (c (fn-psc-model-msgid-content-complete
                (fn-psc-get pos (fn-psc-model-msgid-field-complete pos resume c incoming held))
                (fn-psc-model-msgid-field-complete pos resume c incoming held) incoming held)))
        (:instance fn-psc-message-id-line-strip-is-three-indexed-stages
         (text (fn-psc-get msgid c)) (source (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-model-msgid-complete fn-psc-model-source)
   (fn-psc-model-msgid-field-complete fn-psc-model-msgid-content-complete fn-psc-model-msgid-tail-complete
    fn-psc-msgid-field-complete-full-frame fn-psc-msgid-content-complete-full-frame
    fn-psc-msgid-tail-complete-frame fn-psc-message-id-line-strip-is-three-indexed-stages
    fn-psc-strip-success-is-exact-drop fn-inj-strip fn-record-string-octets
    fn-inj-message-id-line nth nthcdr len update-nth length nfix)))))

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

(defthm fn-psc-comparison-complete-preserves-layout
 (implies (equal (len c) 24)
  (equal (len (fn-psc-model-comparison-complete c incoming held)) 24))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
  :in-theory (e/d (fn-psc-model-comparison-complete)
    (fn-psc-step fn-psc-model-demanded-byte fn-psc-comparison-statep fn-psc-comparison-rank len nth nfix)))))

(defthm fn-psc-comparison-complete-preserves-proper-state
 (implies (true-listp c)
  (true-listp (fn-psc-model-comparison-complete c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
  :in-theory (e/d (fn-psc-model-comparison-complete)
    (fn-psc-step fn-psc-model-demanded-byte fn-psc-comparison-statep fn-psc-comparison-rank len nth nfix)))))

(local (defthm fn-psc-msgid-compare-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-msgid-compare pos resume c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-msgid-compare fn-psc-literal fn-psc-compare)
                                (nth update-nth len nfix))))))

(local (defthm fn-psc-msgid-compare-preserves-proper-state
 (implies (true-listp c) (true-listp (fn-psc-msgid-compare pos resume c)))
 :hints (("Goal" :in-theory (enable fn-psc-msgid-compare fn-psc-literal fn-psc-compare)))))

(defthm fn-psc-msgid-field-complete-preserves-layout
 (implies (equal (len c) 24)
  (equal (len (fn-psc-model-msgid-field-complete pos resume c incoming held)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-msgid-field-complete)
                                (fn-psc-step fn-psc-msgid-compare fn-psc-model-comparison-complete len)))))

(defthm fn-psc-msgid-field-complete-preserves-proper-state
 (implies (true-listp c)
  (true-listp (fn-psc-model-msgid-field-complete pos resume c incoming held)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-msgid-field-complete)
                                (fn-psc-step fn-psc-msgid-compare fn-psc-model-comparison-complete)))))

(local (defthm fn-psc-compare-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-compare pos ref start count resume c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-compare) (nth update-nth nfix len))))))

(local (defthm fn-psc-compare-preserves-proper-state
 (implies (true-listp c) (true-listp (fn-psc-compare pos ref start count resume c)))
 :hints (("Goal" :in-theory (enable fn-psc-compare)))))

(defthm fn-psc-msgid-content-complete-preserves-layout
 (implies (equal (len c) 24)
  (equal (len (fn-psc-model-msgid-content-complete pos c incoming held)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-msgid-content-complete)
                                (fn-psc-step fn-psc-compare fn-psc-model-comparison-complete len)))))

(defthm fn-psc-msgid-content-complete-preserves-proper-state
 (implies (true-listp c)
  (true-listp (fn-psc-model-msgid-content-complete pos c incoming held)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-msgid-content-complete)
                                (fn-psc-step fn-psc-compare fn-psc-model-comparison-complete)))))

(local (defthm fn-psc-msgid-field-success-is-actual-content-entry
 (implies (and (true-listp c) (equal (len c) 24)
               (natp pos) (stringp (fn-psc-get msgid c))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get phase (fn-psc-model-msgid-field-complete pos resume c incoming held)) :compare))
  (let ((d (fn-psc-model-msgid-field-complete pos resume c incoming held)))
   (equal (fn-psc-compare (fn-psc-get pos d) :msgid 0
                         (length (fn-psc-get msgid d)) :msgid-content d) d)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-msgid-field-complete-full-frame
        (:instance fn-psc-compare-current-fields-is-same
         (c (fn-psc-model-msgid-field-complete pos resume c incoming held))))
  :in-theory (e/d (length)
    (fn-psc-model-msgid-field-complete fn-psc-compare fn-psc-compare-current-fields-is-same
     fn-psc-msgid-field-complete-full-frame fn-inj-strip fn-psc-model-source
     nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-msgid-content-success-is-actual-tail-entry
 (implies (and (true-listp c) (equal (len c) 24)
               (natp pos) (stringp (fn-psc-get msgid c))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get phase (fn-psc-model-msgid-content-complete pos c incoming held)) :compare))
  (let ((d (fn-psc-model-msgid-content-complete pos c incoming held)))
   (equal (fn-psc-literal (fn-psc-get pos d) '(13 10) :msgid-tail d) d)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-msgid-content-complete-full-frame
        (:instance fn-psc-compare-current-fields-is-same
         (c (fn-psc-model-msgid-content-complete pos c incoming held))))
  :in-theory (e/d (fn-psc-literal length)
    (fn-psc-model-msgid-content-complete fn-psc-compare fn-psc-compare-current-fields-is-same
     fn-psc-msgid-content-complete-full-frame fn-inj-strip fn-psc-model-source
     nth nthcdr len update-nth nfix))))))

(local (defthm fn-psc-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(defthm fn-psc-comparison-next-is-actual-paid-trace
 (implies (and (fn-psc-comparison-statep c)
               (member-eq (fn-psc-get phase c) '(:compare :target)))
  (equal (fn-psc-step (fn-psc-model-comparison-complete c incoming held) nil)
         (fn-psc-model-byte-run (+ 1 (fn-psc-model-comparison-cost c incoming held)) c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-comparison-complete-returns-control fn-psc-comparison-complete-is-actual-steps
        (:instance fn-psc-byte-run-addition (a (fn-psc-model-comparison-cost c incoming held)) (b 1)))
  :expand ((:free (c) (fn-psc-model-byte-run 1 c incoming held))
           (:free (c) (fn-psc-model-byte-run 0 c incoming held)))
  :in-theory (e/d (fn-psc-model-demanded-byte fn-psc-demand)
   (fn-psc-model-byte-run fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-comparison-complete-returns-control fn-psc-comparison-complete-is-actual-steps
    fn-psc-byte-run-addition fn-psc-step fn-psc-comparison-statep nth nfix len)))))

(defthm fn-psc-msgid-field-complete-is-actual-paid-steps
 (equal (fn-psc-model-msgid-field-complete pos resume c incoming held)
        (fn-psc-model-byte-run
         (+ 1 (fn-psc-model-comparison-cost (fn-psc-msgid-compare pos resume c) incoming held))
         (fn-psc-msgid-compare pos resume c) incoming held))
 :hints (("Goal" :use ((:instance fn-psc-comparison-next-is-actual-paid-trace
                        (c (fn-psc-msgid-compare pos resume c))))
  :in-theory (e/d (fn-psc-model-msgid-field-complete fn-psc-msgid-compare
                   fn-psc-literal fn-psc-compare fn-psc-comparison-statep)
    (fn-psc-step fn-psc-model-comparison-complete fn-psc-model-byte-run
     fn-psc-model-comparison-cost fn-psc-comparison-next-is-actual-paid-trace nth nfix len update-nth)))))

(defthm fn-psc-msgid-content-stage-is-actual-paid-steps
 (implies (and (true-listp c) (equal (len c) 24)
               (natp pos) (stringp (fn-psc-get msgid c))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get phase (fn-psc-model-msgid-field-complete pos resume c incoming held)) :compare))
  (let ((d (fn-psc-model-msgid-field-complete pos resume c incoming held)))
   (equal (fn-psc-model-msgid-content-complete (fn-psc-get pos d) d incoming held)
          (fn-psc-model-byte-run (+ 1 (fn-psc-model-comparison-cost d incoming held)) d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-msgid-field-complete-full-frame fn-psc-msgid-field-success-is-actual-content-entry
        (:instance fn-psc-comparison-next-is-actual-paid-trace
         (c (fn-psc-model-msgid-field-complete pos resume c incoming held))))
  :in-theory (e/d (fn-psc-model-msgid-content-complete fn-psc-comparison-statep length)
   (fn-psc-model-msgid-field-complete fn-psc-compare fn-psc-step fn-psc-model-comparison-complete
    fn-psc-model-byte-run fn-psc-model-comparison-cost fn-psc-msgid-field-complete-full-frame
    fn-psc-msgid-field-success-is-actual-content-entry fn-psc-comparison-next-is-actual-paid-trace
    nth nfix len update-nth fn-psc-model-source fn-inj-strip)))))

(defthm fn-psc-msgid-tail-stage-is-actual-paid-steps
 (implies (and (true-listp c) (equal (len c) 24)
               (natp pos) (stringp (fn-psc-get msgid c))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get phase (fn-psc-model-msgid-content-complete pos c incoming held)) :compare))
  (let ((d (fn-psc-model-msgid-content-complete pos c incoming held)))
   (equal (fn-psc-model-msgid-tail-complete (fn-psc-get pos d) d incoming held)
          (fn-psc-model-byte-run (+ 1 (fn-psc-model-comparison-cost d incoming held)) d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-msgid-content-complete-full-frame fn-psc-msgid-content-success-is-actual-tail-entry
        (:instance fn-psc-comparison-next-is-actual-paid-trace
         (c (fn-psc-model-msgid-content-complete pos c incoming held))))
  :in-theory (e/d (fn-psc-model-msgid-tail-complete fn-psc-comparison-statep)
   (fn-psc-model-msgid-content-complete fn-psc-literal fn-psc-step fn-psc-model-comparison-complete
    fn-psc-model-byte-run fn-psc-model-comparison-cost fn-psc-msgid-content-complete-full-frame
    fn-psc-msgid-content-success-is-actual-tail-entry fn-psc-comparison-next-is-actual-paid-trace
    nth nfix len update-nth fn-psc-model-source fn-inj-strip)))))

(defun fn-psc-model-msgid-cost (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((entry (fn-psc-msgid-compare pos resume c))
        (d (fn-psc-model-msgid-field-complete pos resume c incoming held)))
  (+ 1 (fn-psc-model-comparison-cost entry incoming held)
     (if (equal (fn-psc-get phase d) :compare)
         (let ((e (fn-psc-model-msgid-content-complete (fn-psc-get pos d) d incoming held)))
          (+ 1 (fn-psc-model-comparison-cost d incoming held)
             (if (equal (fn-psc-get phase e) :compare)
                 (+ 1 (fn-psc-model-comparison-cost e incoming held)) 0))) 0))))

(defthm fn-psc-msgid-complete-is-actual-paid-steps
 (implies (and (true-listp c) (equal (len c) 24)
               (natp pos) (stringp (fn-psc-get msgid c))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-msgid-complete pos resume c incoming held)
         (fn-psc-model-byte-run (fn-psc-model-msgid-cost pos resume c incoming held)
                               (fn-psc-msgid-compare pos resume c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-msgid-field-complete-full-frame
        fn-psc-msgid-field-complete-is-actual-paid-steps
        fn-psc-msgid-content-stage-is-actual-paid-steps
        (:instance fn-psc-msgid-tail-stage-is-actual-paid-steps
         (c (fn-psc-model-msgid-field-complete pos resume c incoming held))
         (pos (fn-psc-get pos (fn-psc-model-msgid-field-complete pos resume c incoming held))))
        (:instance fn-psc-byte-run-addition
         (c (fn-psc-msgid-compare pos resume c))
         (a (+ 1 (fn-psc-model-comparison-cost (fn-psc-msgid-compare pos resume c) incoming held)))
         (b (if (equal (fn-psc-get phase (fn-psc-model-msgid-field-complete pos resume c incoming held)) :compare)
                (+ 1 (fn-psc-model-comparison-cost (fn-psc-model-msgid-field-complete pos resume c incoming held) incoming held)
                 (if (equal (fn-psc-get phase (fn-psc-model-msgid-content-complete
                     (fn-psc-get pos (fn-psc-model-msgid-field-complete pos resume c incoming held))
                     (fn-psc-model-msgid-field-complete pos resume c incoming held) incoming held)) :compare)
                     (+ 1 (fn-psc-model-comparison-cost (fn-psc-model-msgid-content-complete
                     (fn-psc-get pos (fn-psc-model-msgid-field-complete pos resume c incoming held))
                     (fn-psc-model-msgid-field-complete pos resume c incoming held) incoming held) incoming held)) 0)) 0)))
        (:instance fn-psc-byte-run-addition
         (c (fn-psc-model-msgid-field-complete pos resume c incoming held))
         (a (+ 1 (fn-psc-model-comparison-cost
                   (fn-psc-model-msgid-field-complete pos resume c incoming held) incoming held)))
         (b (if (equal (fn-psc-get phase (fn-psc-model-msgid-content-complete
                     (fn-psc-get pos (fn-psc-model-msgid-field-complete pos resume c incoming held))
                     (fn-psc-model-msgid-field-complete pos resume c incoming held) incoming held)) :compare)
                     (+ 1 (fn-psc-model-comparison-cost (fn-psc-model-msgid-content-complete
                     (fn-psc-get pos (fn-psc-model-msgid-field-complete pos resume c incoming held))
                     (fn-psc-model-msgid-field-complete pos resume c incoming held) incoming held) incoming held)) 0))))
  :expand ((:free (c) (fn-psc-model-byte-run 0 c incoming held)))
  :in-theory (e/d (fn-psc-model-msgid-complete fn-psc-model-msgid-cost fn-psc-model-source)
   (fn-psc-model-msgid-field-complete fn-psc-model-msgid-content-complete fn-psc-model-msgid-tail-complete
    fn-psc-model-byte-run fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-step fn-psc-msgid-compare fn-psc-msgid-field-complete-full-frame
    fn-psc-msgid-field-complete-is-actual-paid-steps fn-psc-msgid-content-stage-is-actual-paid-steps
    fn-psc-msgid-tail-stage-is-actual-paid-steps fn-psc-byte-run-addition
    fn-inj-strip nth nthcdr len update-nth nfix)))))

(in-theory (disable fn-psc-model-msgid-field-complete fn-psc-model-msgid-content-complete fn-psc-model-msgid-tail-complete fn-psc-model-msgid-complete fn-psc-model-msgid-cost))
