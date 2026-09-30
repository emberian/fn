; Proof-only source Injection-Info inverse and exact paid virtual-byte trace.
(in-package "ACL2")
(include-book "post-identity-source-cursor-skip")
(include-book "post-identity-source-cursor-source-context")
(local (include-book "arithmetic/top" :dir :system))





(defun fn-psc-model-source-info-field (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-comparison-complete (fn-psc-info-compare pos resume c) incoming held))

(defun fn-psc-model-source-info-agent (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-source-info-field pos resume c incoming held))
        (e (fn-psc-step d nil)))
  (if (fn-psc-get ok d) (fn-psc-model-comparison-complete e incoming held) e)))

(defun fn-psc-model-source-info-choice (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-source-info-agent pos resume c incoming held)))
  (if (equal (fn-psc-get resume d) :info-agent) (fn-psc-step d nil) d)))

(defun fn-psc-model-source-info-complete (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-model-source-info-choice pos resume c incoming held)))
  (if (equal (fn-psc-get phase d) :info-choice)
   (let ((e (fn-psc-model-byte-run 1 d incoming held)))
    (cond ((equal (fn-psc-get phase e) :compare)
           (fn-psc-step (fn-psc-model-comparison-complete e incoming held) nil))
          ((equal (fn-psc-get phase e) :params)
           (fn-psc-step (fn-psc-model-param-complete e incoming held) nil))
          (t e))) d)))

(local (defthm fn-psc-source-info-field-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos))
  (let ((d (fn-psc-model-source-info-field pos resume c incoming held)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) :info-field)
        (equal (fn-psc-get aux d) resume)
        (iff (fn-psc-get ok d)
         (not (equal (fn-inj-strip *fn-inj-injection-info-field* (nthcdr pos (fn-psc-model-source c incoming held))) :no)))
        (implies (fn-psc-get ok d) (equal (fn-psc-get pos d) (+ pos 16)))
        (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-get k d) (fn-psc-get k c)) (equal (fn-psc-get date d) (fn-psc-get date c))
        (equal (fn-psc-get has-path d) (fn-psc-get has-path c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-info-compare pos resume c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-info-compare pos resume c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-info-compare pos resume c)))
        (:instance fn-psc-literal-comparison-is-actual-strip
         (c (fn-psc-set aux resume c)) (bytes *fn-inj-injection-info-field*) (resume :info-field)))
  :in-theory (e/d (fn-psc-model-source-info-field fn-psc-source-contextp fn-psc-info-compare fn-psc-literal fn-psc-compare
                   fn-psc-comparison-statep fn-psc-comparison-positionp fn-psc-model-source nfix)
   (fn-psc-model-comparison-complete fn-psc-comparison-complete-returns-control
    fn-psc-comparison-complete-exact-flag fn-psc-comparison-complete-exact-position
    fn-psc-literal-comparison-is-actual-strip fn-inj-strip nth nthcdr len update-nth))))))

(local (defthm fn-psc-source-agent-comparison-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos))
  (let ((d (fn-psc-model-comparison-complete (fn-psc-agent-compare pos resume c) incoming held)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) resume)
        (iff (fn-psc-get ok d)
         (not (equal (fn-inj-strip (fn-psc-model-retained-agent c incoming)
                                  (nthcdr pos (fn-psc-model-source c incoming held))) :no)))
        (implies (fn-psc-get ok d)
         (equal (fn-psc-get pos d) (+ pos (- (fn-psc-get agent-end c) (fn-psc-get agent-start c)))))
        (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-get k d) (fn-psc-get k c)) (equal (fn-psc-get date d) (fn-psc-get date c))
        (equal (fn-psc-get has-path d) (fn-psc-get has-path c))
        (equal (fn-psc-get aux d) (fn-psc-get aux c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-agent-compare pos resume c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-agent-compare pos resume c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-agent-compare pos resume c)))
        fn-psc-agent-comparison-is-incoming-span-strip)
  :in-theory (e/d (fn-psc-model-retained-agent fn-psc-source-contextp fn-psc-agent-compare fn-psc-compare
                   fn-psc-comparison-statep fn-psc-comparison-positionp fn-psc-model-source nfix)
   (fn-psc-model-comparison-complete fn-psc-comparison-complete-returns-control
    fn-psc-comparison-complete-exact-flag fn-psc-comparison-complete-exact-position
    fn-psc-agent-comparison-is-incoming-span-strip fn-inj-strip fn-inj-take nth nthcdr len update-nth))))))

(local (defthm fn-psc-info-field-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :info-field)
               (natp (fn-psc-get pos c)))
  (equal (fn-psc-step c byte)
   (if (fn-psc-get ok c) (fn-psc-agent-compare (fn-psc-get pos c) :info-agent c)
    (fn-psc-return nil (fn-psc-set resume (fn-psc-get aux c) c)))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-agent-compare fn-psc-return nth len update-nth))))))

(local (defthm fn-psc-info-agent-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control) (equal (fn-psc-get resume c) :info-agent))
  (equal (fn-psc-step c byte)
   (if (fn-psc-get ok c) (fn-psc-set phase :info-choice c)
    (fn-psc-return nil (fn-psc-set resume (fn-psc-get aux c) c)))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-return nth len update-nth))))))

(local (defthm fn-psc-source-info-field-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 20))))
  (equal (nth slot (fn-psc-model-source-info-field pos resume c incoming held)) (nth slot c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source-info-field fn-psc-info-compare fn-psc-literal fn-psc-compare nfix)
  (fn-psc-model-comparison-complete nth len update-nth))))))

(local (defthm fn-psc-source-agent-complete-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15))))
  (equal (nth slot (fn-psc-model-comparison-complete (fn-psc-agent-compare pos resume c) incoming held)) (nth slot c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-agent-compare fn-psc-compare nfix)
  (fn-psc-model-comparison-complete nth len update-nth))))))

(local (defthm fn-psc-comparison-complete-preserves-natural-position
 (implies (natp (fn-psc-get pos c))
  (natp (fn-psc-get pos (fn-psc-model-comparison-complete c incoming held))))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
  :in-theory (e/d (fn-psc-model-comparison-complete fn-psc-step fn-psc-return nfix)
   (fn-psc-control fn-psc-expected fn-psc-model-demanded-byte nth len update-nth))))))

(local (defthm fn-psc-source-info-field-keeps-agent
 (equal (fn-psc-model-retained-agent (fn-psc-model-source-info-field pos resume c incoming held) incoming)
        (fn-psc-model-retained-agent c incoming))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-retained-agent)
  (fn-psc-model-source-info-field fn-inj-take nthcdr len))))))

(local (defthm fn-psc-source-info-field-keeps-source
 (equal (fn-psc-model-source (fn-psc-model-source-info-field pos resume c incoming held) incoming held)
        (fn-psc-model-source c incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source)
  (fn-psc-model-source-info-field nth len))))))

(local (defthm fn-psc-source-info-field-natural-position
 (natp (fn-psc-get pos (fn-psc-model-source-info-field pos resume c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-preserves-natural-position (c (fn-psc-info-compare pos resume c))))
  :in-theory (e/d (fn-psc-model-source-info-field fn-psc-info-compare fn-psc-literal fn-psc-compare nfix)
   (fn-psc-model-comparison-complete fn-psc-comparison-complete-preserves-natural-position nth len update-nth))))))

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

(local (defthm fn-psc-source-info-prefix-strip
 (implies (natp pos)
  (equal (fn-inj-strip (fn-inj-append *fn-inj-injection-info-field* agent) (nthcdr pos xs))
   (if (equal (fn-inj-strip *fn-inj-injection-info-field* (nthcdr pos xs)) :no) :no
    (fn-inj-strip agent (nthcdr (+ 16 pos) xs)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-strip-append-composes (prefix *fn-inj-injection-info-field*) (suffix agent) (xs (nthcdr pos xs)))
        (:instance fn-psc-strip-success-is-exact-drop (prefix *fn-inj-injection-info-field*) (xs (nthcdr pos xs)))
        (:instance fn-psc-nthcdr-composes-offsets (a pos) (b 16)))
  :in-theory (disable fn-inj-strip fn-inj-append nthcdr len
   fn-psc-strip-append-composes fn-psc-strip-success-is-exact-drop fn-psc-nthcdr-composes-offsets)))))

(local (defthm fn-psc-return-preserves-source-context
 (implies (fn-psc-source-contextp c incoming held)
  (fn-psc-source-contextp (fn-psc-return ok c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-return fn-psc-model-source)
  (nth len update-nth))))))

(local (defthm fn-psc-source-resume-update-preserves-context
 (implies (fn-psc-source-contextp c incoming held)
  (fn-psc-source-contextp (fn-psc-set resume resume c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-model-source)
  (nth len update-nth))))))

(local (defthm fn-psc-return-slot-value
 (equal (nth slot (fn-psc-return ok c))
  (cond ((equal (nfix slot) 0) :control)
        ((equal (nfix slot) 15) ok)
        (t (nth slot c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-return nfix) (nth update-nth))))))

(local (defthm fn-psc-source-info-agent-prefix-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos))
  (let* ((field (fn-psc-model-source-info-field pos resume c incoming held))
         (d (fn-psc-model-source-info-agent pos resume c incoming held)))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) (if (fn-psc-get ok field) :info-agent resume))
        (equal (fn-psc-get aux d) resume)
        (iff (fn-psc-get ok d)
         (not (equal (fn-inj-strip (fn-inj-append *fn-inj-injection-info-field* (fn-psc-model-retained-agent c incoming))
                                  (nthcdr pos (fn-psc-model-source c incoming held))) :no)))
        (implies (fn-psc-get ok d)
         (equal (fn-psc-get pos d) (+ pos 16 (- (fn-psc-get agent-end c) (fn-psc-get agent-start c)))))
        (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-get k d) (fn-psc-get k c)) (equal (fn-psc-get date d) (fn-psc-get date c))
        (equal (fn-psc-get has-path d) (fn-psc-get has-path c)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-field-frame
        (:instance fn-psc-source-agent-comparison-frame
         (c (fn-psc-model-source-info-field pos resume c incoming held))
         (pos (fn-psc-get pos (fn-psc-model-source-info-field pos resume c incoming held))) (resume :info-agent))
        (:instance fn-psc-source-info-prefix-strip (agent (fn-psc-model-retained-agent c incoming))
         (xs (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-model-source-info-agent nfix)
   (fn-psc-return fn-psc-source-contextp fn-psc-model-source-info-field fn-psc-model-comparison-complete fn-psc-agent-compare
    fn-psc-source-info-field-frame fn-psc-source-agent-comparison-frame fn-psc-source-info-prefix-strip
    fn-psc-model-retained-agent fn-psc-model-source fn-psc-step fn-inj-strip fn-inj-append fn-inj-take
    fn-psc-strip-success-is-exact-drop nth nthcdr len update-nth))))))

(local (defthm fn-psc-source-phase-update-preserves-context
 (implies (fn-psc-source-contextp c incoming held)
  (fn-psc-source-contextp (fn-psc-set phase phase c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-model-source)
  (nth len update-nth))))))

(local (defthm fn-psc-source-info-choice-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos))
  (let* ((d (fn-psc-model-source-info-agent pos resume c incoming held))
         (e (fn-psc-model-source-info-choice pos resume c incoming held)))
   (and (equal (fn-psc-get phase e) (if (fn-psc-get ok d) :info-choice :control))
        (implies (not (fn-psc-get ok d)) (equal (fn-psc-get resume e) resume))
        (equal (fn-psc-get pos e) (fn-psc-get pos d))
        (equal (fn-psc-get aux e) resume)
        (fn-psc-source-contextp e incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-agent-prefix-frame fn-psc-source-info-field-frame)
  :in-theory (e/d (fn-psc-model-source-info-choice nfix)
   (fn-psc-model-source-info-field fn-psc-model-retained-agent fn-psc-model-source-info-agent fn-psc-source-contextp fn-psc-step fn-psc-return
    fn-psc-source-info-agent-prefix-frame nth len update-nth))))))

(local (defthm fn-psc-source-info-choice-byte-unfolds
 (implies (and (equal (fn-psc-get phase c) :info-choice)
               (natp (fn-psc-get n c)) (natp (fn-psc-get pos c)) (< (fn-psc-get pos c) (fn-psc-get n c)))
  (equal (fn-psc-step c byte)
   (cond ((equal byte 13) (fn-psc-literal (+ (fn-psc-get pos c) 1) '(10) :info-tail c))
         ((equal byte 59) (fn-psc-set phase :params (fn-psc-set resume :info-tail c)))
         (t (fn-psc-return nil (fn-psc-set resume (fn-psc-get aux c) c))))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step)
  (fn-psc-literal fn-psc-return fn-psc-control fn-psc-finish nth len update-nth))))))

(local (defthm fn-psc-source-info-tail-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :info-tail))
  (equal (fn-psc-step c byte)
   (fn-psc-return (fn-psc-get ok c) (fn-psc-set resume (fn-psc-get aux c) c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control)
  (fn-psc-return nth len update-nth))))))

(local (defthm fn-psc-source-info-lf-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos))
  (let ((d (fn-psc-model-comparison-complete (fn-psc-literal pos '(10) :info-tail c) incoming held)))
   (and (equal (fn-psc-get phase d) :control) (equal (fn-psc-get resume d) :info-tail)
        (equal (fn-psc-get aux d) (fn-psc-get aux c))
        (iff (fn-psc-get ok d)
         (not (equal (fn-inj-strip '(10) (nthcdr pos (fn-psc-model-source c incoming held))) :no)))
        (implies (fn-psc-get ok d) (equal (fn-psc-get pos d) (+ pos 1)))
        (fn-psc-source-contextp d incoming held)
        (equal (fn-psc-get k d) (fn-psc-get k c)) (equal (fn-psc-get date d) (fn-psc-get date c))
        (equal (fn-psc-get has-path d) (fn-psc-get has-path c)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-complete-returns-control (c (fn-psc-literal pos '(10) :info-tail c)))
        (:instance fn-psc-comparison-complete-exact-flag (c (fn-psc-literal pos '(10) :info-tail c)))
        (:instance fn-psc-comparison-complete-exact-position (c (fn-psc-literal pos '(10) :info-tail c)))
        (:instance fn-psc-literal-comparison-is-actual-strip
         (c c) (bytes '(10)) (resume :info-tail)))
  :in-theory (e/d (fn-psc-source-contextp fn-psc-info-compare fn-psc-literal fn-psc-compare
                   fn-psc-comparison-statep fn-psc-comparison-positionp fn-psc-model-source nfix)
   (fn-psc-model-comparison-complete fn-psc-comparison-complete-returns-control
    fn-psc-comparison-complete-exact-flag fn-psc-comparison-complete-exact-position
    fn-psc-literal-comparison-is-actual-strip fn-inj-strip nth nthcdr len update-nth))))))

(local (defthm fn-psc-source-param-step-preserves-context
 (implies (and (fn-psc-source-contextp c incoming held)
               (member-eq (fn-psc-get phase c) '(:params :params-lf)))
  (fn-psc-source-contextp (fn-psc-step c byte) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-model-source fn-psc-step fn-psc-return)
  (fn-psc-control fn-psc-expected nth len update-nth))))))

(local (defthm fn-psc-source-param-complete-preserves-context
 (implies (fn-psc-source-contextp c incoming held)
  (fn-psc-source-contextp (fn-psc-model-param-complete c incoming held) incoming held))
 :hints (("Goal" :induct (fn-psc-model-param-complete c incoming held)
  :in-theory (e/d (fn-psc-model-param-complete)
   (fn-psc-source-contextp fn-psc-step fn-psc-model-demanded-byte fn-psc-line-statep nth len))))))

(local (defthm fn-psc-source-param-complete-frame
 (implies (and (fn-psc-source-contextp c incoming held)
               (fn-psc-line-statep c incoming held)
               (equal (fn-psc-get phase c) :params))
  (let ((d (fn-psc-model-param-complete c incoming held)))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) (fn-psc-get resume c))
        (equal (fn-psc-get aux d) (fn-psc-get aux c))
        (iff (fn-psc-get ok d)
         (not (equal (fn-inj-param-rest (nthcdr (fn-psc-get pos c)
                        (fn-psc-model-source c incoming held))) :no)))
        (implies (fn-psc-get ok d)
         (equal (nthcdr (nfix (fn-psc-get pos d)) (fn-psc-model-source d incoming held))
                (fn-inj-param-rest (nthcdr (fn-psc-get pos c)
                        (fn-psc-model-source c incoming held)))))
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-param-complete-returns-control fn-psc-param-complete-exact-flag
        fn-psc-param-complete-preserves-value)
  :in-theory (e/d (fn-psc-model-param-value fn-psc-source-contextp fn-psc-line-statep fn-psc-model-source nfix)
   (fn-psc-model-param-complete fn-psc-param-complete-returns-control fn-psc-param-complete-exact-flag
    fn-psc-param-complete-preserves-value fn-psc-step fn-inj-param-rest nth nthcdr len))))))

(local (defthm fn-psc-source-buffer-strip-compose
 (implies (and (true-listp prefix) (natp i))
  (equal (fn-pbb-strip-at (fn-inj-append prefix suffix) i xs)
   (let ((p (fn-pbb-strip-at prefix i xs)))
    (if (equal p :no) :no (fn-pbb-strip-at suffix p xs)))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (e/d (fn-pbb-strip-at fn-inj-append) (nth len))))))

(local (defthm fn-psc-source-append-associates
 (equal (fn-inj-append a (fn-inj-append b c)) (fn-inj-append (fn-inj-append a b) c))
 :hints (("Goal" :induct (fn-inj-append a b) :in-theory (enable fn-inj-append)))))

(local (defthm fn-psc-source-append-is-proper
 (implies (true-listp b) (true-listp (fn-inj-append a b)))
 :hints (("Goal" :induct (fn-inj-append a b) :in-theory (enable fn-inj-append)))))

(local (defthm fn-psc-source-info-reference-choice-unfolds
 (implies (and (true-listp agent) (natp i) (<= i (len xs)))
  (let ((p (fn-pbb-strip-at (fn-inj-append *fn-inj-injection-info-field* agent) i xs)))
   (equal (fn-pbb-strip-info-at agent i xs)
    (if (equal p :no) :no
     (cond ((and (< p (len xs)) (equal (nth p xs) 13))
            (fn-pbb-strip-at '(10) (+ p 1) xs))
           ((and (< p (len xs)) (equal (nth p xs) 59))
            (fn-pbb-param-rest-at p xs))
           (t :no))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-buffer-strip-compose (prefix (fn-inj-append *fn-inj-injection-info-field* agent)) (suffix '(13 10))))
  :expand ((:free (j) (fn-pbb-strip-at '(13 10) j xs)))
  :in-theory (e/d (fn-pbb-strip-info-at fn-inj-injection-info-line)
   (fn-inj-append fn-pbb-strip-at fn-pbb-param-rest-at nth len))))))

(local (defthm fn-psc-source-buffer-strip-success-index
 (implies (and (natp i) (true-listp prefix)
               (not (equal (fn-pbb-strip-at prefix i xs) :no)))
  (equal (fn-pbb-strip-at prefix i xs) (+ i (len prefix))))
 :hints (("Goal" :induct (fn-pbb-strip-at prefix i xs)
  :in-theory (e/d (fn-pbb-strip-at) (nth))))))

(local (defthm fn-psc-source-info-agent-is-buffer-prefix
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-source-info-agent pos resume c incoming held))
         (p (fn-pbb-strip-at (fn-inj-append *fn-inj-injection-info-field*
                            (fn-psc-model-retained-agent c incoming))
                          pos (fn-psc-model-source c incoming held))))
   (and (iff (fn-psc-get ok d) (not (equal p :no)))
        (implies (fn-psc-get ok d) (equal (fn-psc-get pos d) p)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-agent-prefix-frame
        (:instance fn-pbb-strip-at-is-inj-strip
         (prefix (fn-inj-append *fn-inj-injection-info-field* (fn-psc-model-retained-agent c incoming)))
         (i pos) (fn-octets (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-source-contextp fn-psc-model-retained-agent)
   (fn-psc-model-source fn-psc-model-source-info-agent fn-psc-model-source-info-field
    fn-psc-source-info-agent-prefix-frame fn-inj-append fn-inj-take fn-inj-strip
    fn-pbb-strip-at-is-inj-strip fn-pbb-strip-at nth nthcdr len))))))

(local (defthm fn-psc-source-param-complete-preserves-line-state
 (implies (fn-psc-line-statep c incoming held)
  (fn-psc-line-statep (fn-psc-model-param-complete c incoming held) incoming held))
 :hints (("Goal" :induct (fn-psc-model-param-complete c incoming held)
  :in-theory (e/d (fn-psc-model-param-complete)
   (fn-psc-line-statep fn-psc-step fn-psc-model-demanded-byte nth len))))))

(local (defthm fn-psc-source-equal-tails-have-equal-bounded-indices
 (implies (and (true-listp xs) (natp a) (natp b) (<= a (len xs)) (<= b (len xs))
               (equal (nthcdr a xs) (nthcdr b xs)))
  (equal a b))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-block-nthcdr-length (start a))
        (:instance fn-psc-block-nthcdr-length (start b)))
  :in-theory (disable fn-psc-block-nthcdr-length nthcdr len)))))

(local (defthm fn-psc-source-param-complete-is-buffer-index
 (implies (and (fn-psc-source-contextp c incoming held)
               (fn-psc-line-statep c incoming held)
               (equal (fn-psc-get phase c) :params))
  (let* ((d (fn-psc-model-param-complete c incoming held))
         (p (fn-pbb-param-rest-at (fn-psc-get pos c) (fn-psc-model-source c incoming held))))
   (and (iff (fn-psc-get ok d) (not (equal p :no)))
        (implies (fn-psc-get ok d) (equal (fn-psc-get pos d) p)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-param-complete-frame fn-psc-source-param-complete-preserves-line-state
        (:instance fn-psc-source-equal-tails-have-equal-bounded-indices
          (a (fn-psc-get pos (fn-psc-model-param-complete c incoming held)))
          (b (fn-pbb-param-rest-at (fn-psc-get pos c) (fn-psc-model-source c incoming held)))
          (xs (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-source-contextp fn-psc-line-statep fn-psc-model-source nfix)
   (fn-psc-source-param-complete-frame fn-psc-source-param-complete-preserves-line-state
    fn-psc-model-param-complete fn-pbb-param-rest-at fn-inj-param-rest nth nthcdr len))))))

(defun fn-psc-model-source-info-tail (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((e (fn-psc-model-byte-run 1 c incoming held)))
  (cond ((equal (fn-psc-get phase e) :compare)
         (fn-psc-step (fn-psc-model-comparison-complete e incoming held) nil))
        ((equal (fn-psc-get phase e) :params)
         (fn-psc-step (fn-psc-model-param-complete e incoming held) nil))
        (t e))))

(local (defthm fn-psc-source-info-choice-one-byte
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :info-choice)
               (natp (fn-psc-get pos c)) (< (fn-psc-get pos c) (fn-psc-get n c)))
  (equal (fn-psc-model-byte-run 1 c incoming held)
   (let ((byte (nth (fn-psc-get pos c) (fn-psc-model-source c incoming held))))
    (cond ((equal byte 13) (fn-psc-literal (+ (fn-psc-get pos c) 1) '(10) :info-tail c))
          ((equal byte 59) (fn-psc-set phase :params (fn-psc-set resume :info-tail c)))
          (t (fn-psc-return nil (fn-psc-set resume (fn-psc-get aux c) c)))))))
 :hints (("Goal" :expand ((fn-psc-model-byte-run 1 c incoming held)
 (:free (d) (fn-psc-model-byte-run 0 d incoming held))) :in-theory (e/d (fn-psc-model-byte-run fn-psc-model-demanded-byte fn-psc-demand
                                 fn-psc-source-contextp fn-psc-model-source nfix)
   (fn-psc-step fn-psc-control fn-psc-return fn-psc-literal
    fn-psc-comparison-next-is-actual-paid-trace nth len update-nth))))))

(local (defthm fn-psc-source-info-tail-frame
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :info-choice)
               (natp (fn-psc-get pos c)) (< (fn-psc-get pos c) (fn-psc-get n c)))
  (let* ((d (fn-psc-model-source-info-tail c incoming held))
         (pos (fn-psc-get pos c)) (xs (fn-psc-model-source c incoming held))
         (p (cond ((equal (nth pos xs) 13) (fn-pbb-strip-at '(10) (+ pos 1) xs))
                  ((equal (nth pos xs) 59) (fn-pbb-param-rest-at pos xs)) (t :no))))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) (fn-psc-get aux c))
        (iff (fn-psc-get ok d) (not (equal p :no)))
        (implies (fn-psc-get ok d) (equal (fn-psc-get pos d) p))
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-info-lf-frame (pos (+ (fn-psc-get pos c) 1)))
        (:instance fn-psc-source-param-complete-frame
         (c (fn-psc-set phase :params (fn-psc-set resume :info-tail c))))
        (:instance fn-psc-source-param-complete-is-buffer-index
         (c (fn-psc-set phase :params (fn-psc-set resume :info-tail c)))))
  :in-theory (e/d (fn-psc-model-source-info-tail fn-psc-source-contextp fn-psc-line-statep fn-psc-literal fn-psc-compare fn-psc-model-source nfix)
   (fn-psc-step fn-psc-return fn-psc-model-byte-run
    fn-psc-model-comparison-complete fn-psc-model-param-complete fn-inj-strip fn-inj-param-rest
    fn-pbb-strip-at fn-pbb-param-rest-at nth nthcdr len update-nth
    fn-psc-source-info-lf-frame fn-psc-source-param-complete-frame
    fn-psc-source-param-complete-is-buffer-index))))))

(local (defthm fn-psc-source-info-tail-at-end
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :info-choice)
               (equal (fn-psc-get pos c) (fn-psc-get n c)))
  (let ((d (fn-psc-model-source-info-tail c incoming held)))
   (and (equal (fn-psc-get phase d) :done)
        (equal (fn-psc-result d) :no-source)
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :expand ((fn-psc-model-byte-run 1 c incoming held)
                        (:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-info-tail fn-psc-step fn-psc-finish fn-psc-result
                   fn-psc-source-contextp fn-psc-model-source nfix)
   (fn-psc-control fn-psc-expected fn-psc-model-demanded-byte fn-psc-model-byte-run
    fn-psc-model-comparison-complete fn-psc-model-param-complete nth len update-nth))))))

(local (defthm fn-psc-source-info-agent-preserves-slot
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (natp slot)
               (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 20))))
  (equal (nth slot (fn-psc-model-source-info-agent pos resume c incoming held)) (nth slot c)))
 :hints (("Goal" :do-not-induct t :use fn-psc-source-info-field-frame
  :in-theory (e/d (fn-psc-model-source-info-agent nfix)
   (fn-psc-model-source-info-field fn-psc-model-comparison-complete fn-psc-step fn-psc-agent-compare
    fn-psc-return fn-psc-source-contextp nth len update-nth))))))

(local (defthm fn-psc-source-info-choice-preserves-slot
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos) (natp slot)
               (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 20))))
  (equal (nth slot (fn-psc-model-source-info-choice pos resume c incoming held)) (nth slot c)))
 :hints (("Goal" :do-not-induct t :use fn-psc-source-info-agent-prefix-frame
  :in-theory (e/d (fn-psc-model-source-info-choice nfix)
   (fn-psc-model-source-info-agent fn-psc-model-source-info-field fn-psc-model-comparison-complete
    fn-psc-step fn-psc-agent-compare fn-psc-return fn-psc-source-contextp nth len update-nth))))))

(local (defthm fn-psc-source-info-choice-is-buffer-prefix
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-source-info-choice pos resume c incoming held))
         (p (fn-pbb-strip-at (fn-inj-append *fn-inj-injection-info-field*
                            (fn-psc-model-retained-agent c incoming))
                          pos (fn-psc-model-source c incoming held))))
   (and (iff (equal (fn-psc-get phase d) :info-choice) (not (equal p :no)))
        (implies (not (equal p :no)) (equal (fn-psc-get pos d) p))
        (equal (fn-psc-model-source d incoming held) (fn-psc-model-source c incoming held))
        (equal (fn-psc-get aux d) resume)
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-choice-frame fn-psc-source-info-agent-is-buffer-prefix)
  :in-theory (e/d (fn-psc-model-source)
   (fn-psc-source-info-choice-frame fn-psc-source-info-agent-is-buffer-prefix
    fn-psc-source-contextp fn-psc-model-retained-agent fn-psc-model-source-info-agent
    fn-psc-model-source-info-choice fn-inj-append fn-inj-take fn-inj-strip
    fn-psc-strip-success-is-exact-drop fn-psc-source-info-prefix-strip fn-psc-source-buffer-strip-compose fn-pbb-strip-at nth nthcdr len))))))

(local (defthm fn-psc-source-info-completion-composes-unfolds
 (equal (fn-psc-model-source-info-complete pos resume c incoming held)
  (let ((d (fn-psc-model-source-info-choice pos resume c incoming held)))
   (if (equal (fn-psc-get phase d) :info-choice)
       (fn-psc-model-source-info-tail d incoming held) d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source-info-complete fn-psc-model-source-info-tail)
  (fn-psc-model-source-info-choice fn-psc-model-byte-run fn-psc-model-comparison-complete
   fn-psc-model-param-complete fn-psc-step nth len))))))

(local (defthm fn-psc-source-info-choice-preserves-prefix-flag
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos))
  (equal (fn-psc-get ok (fn-psc-model-source-info-choice pos resume c incoming held))
         (fn-psc-get ok (fn-psc-model-source-info-agent pos resume c incoming held))))
 :hints (("Goal" :do-not-induct t :use fn-psc-source-info-agent-prefix-frame
  :in-theory (e/d (fn-psc-model-source-info-choice nfix)
   (fn-psc-model-source-info-agent fn-psc-source-contextp fn-psc-step fn-psc-return nth len update-nth))))))

(defthm fn-psc-source-info-complete-is-current-buffer-strip
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (let* ((d (fn-psc-model-source-info-complete pos resume c incoming held))
         (p (fn-pbb-strip-info-at (fn-psc-model-retained-agent c incoming) pos
                                  (fn-psc-model-source c incoming held))))
   (and (member-eq (fn-psc-get phase d) '(:control :done))
        (iff (and (equal (fn-psc-get phase d) :control) (fn-psc-get ok d)) (not (equal p :no)))
        (implies (not (equal p :no)) (equal (fn-psc-get pos d) p))
        (implies (equal (fn-psc-get phase d) :done) (equal (fn-psc-result d) :no-source))
        (fn-psc-source-contextp d incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-choice-preserves-prefix-flag fn-psc-source-info-choice-is-buffer-prefix fn-psc-source-info-choice-frame
        fn-psc-source-info-agent-is-buffer-prefix
        (:instance fn-psc-source-info-tail-frame
         (c (fn-psc-model-source-info-choice pos resume c incoming held)))
        (:instance fn-psc-source-info-tail-at-end
         (c (fn-psc-model-source-info-choice pos resume c incoming held)))
        (:instance fn-psc-source-info-reference-choice-unfolds
         (agent (fn-psc-model-retained-agent c incoming)) (i pos) (xs (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-source-contextp fn-psc-model-retained-agent)
   (fn-psc-model-source-info-complete fn-psc-model-source-info-choice fn-psc-model-source-info-agent
    fn-psc-model-source-info-tail fn-psc-model-source fn-inj-take fn-inj-append fn-inj-strip
    fn-pbb-strip-at fn-pbb-strip-info-at fn-pbb-param-rest-at nth nthcdr len
    fn-psc-source-info-choice-is-buffer-prefix fn-psc-source-info-choice-frame
    fn-psc-source-info-agent-is-buffer-prefix fn-psc-source-info-tail-frame fn-psc-source-info-tail-at-end
    fn-psc-source-info-reference-choice-unfolds fn-psc-strip-success-is-exact-drop
    fn-psc-source-info-prefix-strip fn-psc-source-buffer-strip-compose)))))

(local (defthm fn-psc-source-info-choice-success-position-is-bounded
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get phase (fn-psc-model-source-info-choice pos resume c incoming held)) :info-choice))
  (let ((d (fn-psc-model-source-info-choice pos resume c incoming held)))
   (and (natp (fn-psc-get pos d)) (<= (fn-psc-get pos d) (fn-psc-get n d)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-choice-is-buffer-prefix
        (:instance fn-pbb-strip-at-bounds
         (prefix (fn-inj-append *fn-inj-injection-info-field* (fn-psc-model-retained-agent c incoming)))
         (i pos) (fn-octets (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-source-contextp)
   (fn-psc-model-source-info-choice fn-psc-model-source-info-agent fn-psc-model-source
    fn-psc-model-retained-agent fn-inj-append fn-pbb-strip-at fn-pbb-strip-at-bounds
    fn-psc-source-info-choice-is-buffer-prefix fn-psc-source-info-choice-frame
    fn-psc-source-info-agent-is-buffer-prefix fn-psc-source-buffer-strip-success-index
    fn-pbb-strip-at-is-inj-strip nth len))))))

(defun fn-psc-model-source-info-agent-cost (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((f (fn-psc-model-source-info-field pos resume c incoming held)) (e (fn-psc-step f nil)))
  (+ 1 (fn-psc-model-comparison-cost (fn-psc-info-compare pos resume c) incoming held)
     (if (fn-psc-get ok f) (fn-psc-model-comparison-cost e incoming held) 0))))

(defun fn-psc-model-source-info-choice-cost (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (+ (fn-psc-model-source-info-agent-cost pos resume c incoming held)
    (if (equal (fn-psc-get resume (fn-psc-model-source-info-agent pos resume c incoming held)) :info-agent) 1 0)))

(defun fn-psc-model-source-info-tail-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((e (fn-psc-model-byte-run 1 c incoming held)))
  (+ 1 (cond ((equal (fn-psc-get phase e) :compare) (+ 1 (fn-psc-model-comparison-cost e incoming held)))
             ((equal (fn-psc-get phase e) :params) (+ 1 (fn-psc-model-param-cost e incoming held)))
             (t 0)))))

(defun fn-psc-model-source-info-cost (pos resume c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (+ (fn-psc-model-source-info-choice-cost pos resume c incoming held)
    (let ((d (fn-psc-model-source-info-choice pos resume c incoming held)))
     (if (equal (fn-psc-get phase d) :info-choice) (fn-psc-model-source-info-tail-cost d incoming held) 0))))

(local (defthm fn-psc-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-source-info-agent-is-actual-paid-steps
 (implies (natp pos)
  (equal (fn-psc-model-source-info-agent pos resume c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-info-agent-cost pos resume c incoming held)
                         (fn-psc-info-compare pos resume c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-next-is-actual-paid-trace (c (fn-psc-info-compare pos resume c)))
        (:instance fn-psc-comparison-complete-is-actual-steps
         (c (fn-psc-step (fn-psc-model-source-info-field pos resume c incoming held) nil)))
        (:instance fn-psc-byte-run-addition
         (c (fn-psc-info-compare pos resume c))
         (a (+ 1 (fn-psc-model-comparison-cost (fn-psc-info-compare pos resume c) incoming held)))
         (b (if (fn-psc-get ok (fn-psc-model-source-info-field pos resume c incoming held))
                (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-source-info-field pos resume c incoming held) nil) incoming held) 0))))
  :expand ((:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-info-agent fn-psc-model-source-info-agent-cost fn-psc-model-source-info-field
                   fn-psc-info-compare fn-psc-literal fn-psc-compare fn-psc-comparison-statep nfix)
   (fn-psc-step fn-psc-model-byte-run fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-byte-run-addition fn-psc-comparison-next-is-actual-paid-trace fn-psc-comparison-complete-is-actual-steps
    nth len update-nth))))))

(local (defthm fn-psc-source-control-is-one-paid-step
 (implies (equal (fn-psc-get phase c) :control)
  (equal (fn-psc-model-byte-run 1 c incoming held) (fn-psc-step c nil)))
 :hints (("Goal" :expand ((fn-psc-model-byte-run 1 c incoming held)
                         (:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-demanded-byte fn-psc-demand)
   (fn-psc-model-byte-run fn-psc-model-source fn-psc-step nth len nfix))))))

(local (defthm fn-psc-source-info-choice-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos))
  (equal (fn-psc-model-source-info-choice pos resume c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-info-choice-cost pos resume c incoming held)
                         (fn-psc-info-compare pos resume c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-agent-is-actual-paid-steps fn-psc-source-info-agent-prefix-frame
        (:instance fn-psc-byte-run-addition
         (c (fn-psc-info-compare pos resume c))
         (a (fn-psc-model-source-info-agent-cost pos resume c incoming held))
         (b (if (equal (fn-psc-get resume (fn-psc-model-source-info-agent pos resume c incoming held)) :info-agent) 1 0))))
  :expand ((:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-info-choice fn-psc-model-source-info-choice-cost)
   (fn-psc-model-source-info-agent fn-psc-model-source-info-agent-cost fn-psc-model-byte-run
    fn-psc-model-source-info-field fn-psc-info-compare fn-psc-source-contextp fn-psc-step
    fn-psc-source-info-agent-is-actual-paid-steps fn-psc-source-info-agent-prefix-frame
    fn-psc-byte-run-addition nth len update-nth))))))

(local (defthm fn-psc-params-and-control-is-paid-trace
 (implies (and (equal (fn-psc-get phase c) :params) (fn-psc-line-statep c incoming held))
  (equal (fn-psc-step (fn-psc-model-param-complete c incoming held) nil)
         (fn-psc-model-byte-run (+ 1 (fn-psc-model-param-cost c incoming held)) c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-param-complete-returns-control fn-psc-param-complete-is-actual-steps
        (:instance fn-psc-byte-run-addition (a (fn-psc-model-param-cost c incoming held)) (b 1)))
  :expand ((:free (c) (fn-psc-model-byte-run 1 c incoming held))
           (:free (c) (fn-psc-model-byte-run 0 c incoming held)))
  :in-theory (e/d (fn-psc-demand fn-psc-model-demanded-byte)
   (fn-psc-step fn-psc-model-byte-run fn-psc-model-param-complete fn-psc-model-param-cost
    fn-psc-param-complete-returns-control fn-psc-param-complete-is-actual-steps fn-psc-byte-run-addition))))))

(local (defthm fn-psc-source-info-tail-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :info-choice)
               (natp (fn-psc-get pos c)) (< (fn-psc-get pos c) (fn-psc-get n c)))
  (equal (fn-psc-model-source-info-tail c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-info-tail-cost c incoming held) c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-comparison-next-is-actual-paid-trace
         (c (fn-psc-model-byte-run 1 c incoming held)))
        (:instance fn-psc-params-and-control-is-paid-trace
         (c (fn-psc-model-byte-run 1 c incoming held)))
        (:instance fn-psc-byte-run-addition (a 1)
         (b (let ((e (fn-psc-model-byte-run 1 c incoming held)))
              (cond ((equal (fn-psc-get phase e) :compare) (+ 1 (fn-psc-model-comparison-cost e incoming held)))
                    ((equal (fn-psc-get phase e) :params) (+ 1 (fn-psc-model-param-cost e incoming held)))
                    (t 0))))))
  :expand ((:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-info-tail fn-psc-model-source-info-tail-cost
                   fn-psc-source-contextp fn-psc-line-statep fn-psc-comparison-statep
                   fn-psc-model-source fn-psc-literal fn-psc-compare nfix)
   (fn-psc-model-byte-run fn-psc-model-comparison-complete fn-psc-model-comparison-cost
    fn-psc-model-param-complete fn-psc-model-param-cost fn-psc-step fn-psc-return
    fn-psc-comparison-next-is-actual-paid-trace fn-psc-params-and-control-is-paid-trace
    fn-psc-byte-run-addition nth len update-nth))))))

(local (defthm fn-psc-source-info-tail-at-end-is-actual-paid-step
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :info-choice)
               (equal (fn-psc-get pos c) (fn-psc-get n c)))
  (equal (fn-psc-model-source-info-tail c incoming held)
         (fn-psc-model-byte-run (fn-psc-model-source-info-tail-cost c incoming held) c incoming held)))
 :hints (("Goal" :expand ((fn-psc-model-byte-run 1 c incoming held)
                        (:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-info-tail fn-psc-model-source-info-tail-cost fn-psc-step fn-psc-finish fn-psc-result
                   fn-psc-source-contextp fn-psc-model-source nfix)
   (fn-psc-control fn-psc-expected fn-psc-model-demanded-byte fn-psc-model-byte-run
    fn-psc-model-comparison-complete fn-psc-model-param-complete nth len update-nth))))))

(defthm fn-psc-source-info-complete-is-actual-paid-steps
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-source-info-complete pos resume c incoming held)
   (fn-psc-model-byte-run (fn-psc-model-source-info-cost pos resume c incoming held)
                         (fn-psc-info-compare pos resume c) incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-choice-success-position-is-bounded fn-psc-source-info-choice-is-actual-paid-steps fn-psc-source-info-choice-is-buffer-prefix
        (:instance fn-psc-source-info-tail-is-actual-paid-steps
         (c (fn-psc-model-source-info-choice pos resume c incoming held)))
        (:instance fn-psc-source-info-tail-at-end-is-actual-paid-step
         (c (fn-psc-model-source-info-choice pos resume c incoming held)))
        (:instance fn-psc-byte-run-addition
         (c (fn-psc-info-compare pos resume c))
         (a (fn-psc-model-source-info-choice-cost pos resume c incoming held))
         (b (let ((d (fn-psc-model-source-info-choice pos resume c incoming held)))
               (if (equal (fn-psc-get phase d) :info-choice) (fn-psc-model-source-info-tail-cost d incoming held) 0)))))
  :expand ((:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-source-contextp fn-psc-model-source-info-cost)
   (fn-psc-source-info-choice-frame fn-psc-source-info-agent-is-buffer-prefix fn-psc-source-info-choice-success-position-is-bounded fn-psc-model-source-info-agent fn-psc-source-buffer-strip-success-index fn-pbb-strip-at-is-inj-strip fn-psc-model-source-info-complete fn-psc-model-source-info-choice fn-psc-model-source-info-tail
    fn-psc-model-source-info-agent-cost fn-psc-model-source-info-field fn-psc-source-info-agent-is-actual-paid-steps fn-psc-source-info-choice-preserves-prefix-flag fn-psc-model-source-info-choice-cost fn-psc-model-source-info-tail-cost fn-psc-model-retained-agent fn-psc-model-source
    fn-psc-model-byte-run fn-psc-info-compare fn-psc-step fn-psc-byte-run-addition
    fn-psc-source-info-choice-is-actual-paid-steps fn-psc-source-info-choice-is-buffer-prefix
    fn-psc-source-info-tail-is-actual-paid-steps fn-psc-source-info-tail-at-end-is-actual-paid-step
    fn-inj-append fn-pbb-strip-at fn-psc-strip-success-is-exact-drop
    fn-psc-source-info-prefix-strip fn-psc-source-buffer-strip-compose nth len update-nth)))))

(defthm fn-psc-source-info-complete-resume-frame
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (implies (equal (fn-psc-get phase (fn-psc-model-source-info-complete pos resume c incoming held)) :control)
   (equal (fn-psc-get resume (fn-psc-model-source-info-complete pos resume c incoming held)) resume)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-choice-frame fn-psc-source-info-completion-composes-unfolds
        (:instance fn-psc-source-info-tail-frame (c (fn-psc-model-source-info-choice pos resume c incoming held)))
        (:instance fn-psc-source-info-tail-at-end (c (fn-psc-model-source-info-choice pos resume c incoming held)))
        fn-psc-source-info-choice-success-position-is-bounded)
  :in-theory (e/d (fn-psc-source-contextp)
   (fn-psc-model-source-info-complete fn-psc-model-source-info-choice fn-psc-model-source-info-agent
    fn-psc-model-source-info-tail fn-psc-model-source fn-psc-source-info-complete-is-actual-paid-steps
    fn-psc-model-byte-run fn-psc-source-info-agent-is-actual-paid-steps
    fn-psc-source-info-choice-is-actual-paid-steps fn-psc-source-info-tail-is-actual-paid-steps
    fn-psc-source-info-completion-composes-unfolds
    fn-psc-source-info-choice-frame fn-psc-source-info-tail-frame fn-psc-source-info-tail-at-end
    nth nthcdr len)))))

(local (defthm fn-psc-source-info-tail-keeps-source-slots
 (implies (and (fn-psc-source-contextp c incoming held)
               (equal (fn-psc-get phase c) :info-choice)
               (natp (fn-psc-get pos c)) (<= (fn-psc-get pos c) (fn-psc-get n c))
               (member-equal slot '(1 2 3 4 5 6 17 18 19)))
  (equal (nth slot (fn-psc-model-source-info-tail c incoming held)) (nth slot c)))
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-psc-get pos c) (fn-psc-get n c)))
  :use ((:instance fn-psc-comparison-complete-returns-control
         (c (fn-psc-literal (+ 1 (fn-psc-get pos c)) '(10) :info-tail c)))
        (:instance fn-psc-source-param-complete-frame
         (c (fn-psc-set phase :params (fn-psc-set resume :info-tail c)))))
  :expand ((fn-psc-model-byte-run 1 c incoming held)
           (:free (d) (fn-psc-model-byte-run 0 d incoming held)))
  :in-theory (e/d (fn-psc-model-source-info-tail fn-psc-step fn-psc-control fn-psc-return fn-psc-finish
                   fn-psc-source-contextp fn-psc-model-source fn-psc-line-statep fn-psc-comparison-statep
                   fn-psc-literal fn-psc-compare nfix)
   (fn-psc-model-comparison-complete fn-psc-model-param-complete fn-psc-model-byte-run
    fn-psc-model-demanded-byte fn-psc-expected
    fn-psc-comparison-next-is-actual-paid-trace fn-psc-source-param-complete-frame
    fn-psc-comparison-complete-returns-control fn-psc-source-info-tail-is-actual-paid-steps
    fn-psc-source-info-tail-at-end-is-actual-paid-step fn-psc-params-and-control-is-paid-trace nth nthcdr len update-nth))))))

(defthm fn-psc-source-info-complete-keeps-source-slots
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held)))
               (member-equal slot '(1 2 3 4 5 6 17 18 19)))
  (equal (nth slot (fn-psc-model-source-info-complete pos resume c incoming held)) (nth slot c)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-choice-preserves-slot fn-psc-source-info-choice-frame
        fn-psc-source-info-choice-success-position-is-bounded
        fn-psc-source-info-completion-composes-unfolds
        (:instance fn-psc-source-info-tail-keeps-source-slots
         (c (fn-psc-model-source-info-choice pos resume c incoming held))))
  :in-theory (e/d (fn-psc-source-contextp)
   (fn-psc-model-source-info-complete fn-psc-model-source-info-choice fn-psc-model-source-info-agent
    fn-psc-model-source-info-tail fn-psc-model-source fn-psc-source-info-complete-is-actual-paid-steps
    fn-psc-model-byte-run fn-psc-source-info-agent-is-actual-paid-steps
    fn-psc-source-info-choice-is-actual-paid-steps fn-psc-source-info-tail-is-actual-paid-steps
    fn-psc-source-info-completion-composes-unfolds fn-psc-source-info-choice-preserves-slot
    fn-psc-source-info-choice-frame fn-psc-source-info-tail-keeps-source-slots
    nth nthcdr len)))))

(defthm fn-psc-source-info-done-has-current-prefix
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get phase (fn-psc-model-source-info-complete pos resume c incoming held)) :done))
  (not (equal (fn-pbb-strip-at (fn-inj-append *fn-inj-injection-info-field* (fn-psc-model-retained-agent c incoming))
              pos (fn-psc-model-source c incoming held)) :no)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-source-info-choice-is-buffer-prefix fn-psc-source-info-choice-frame
        fn-psc-source-info-completion-composes-unfolds)
  :in-theory (disable fn-psc-model-source-info-complete fn-psc-model-source-info-choice
    fn-psc-model-source-info-tail fn-psc-model-source-info-agent fn-psc-source-contextp
    fn-psc-model-source fn-psc-model-retained-agent fn-inj-append fn-pbb-strip-at nth len
    fn-psc-source-info-complete-is-actual-paid-steps fn-psc-source-info-choice-is-buffer-prefix
    fn-psc-source-info-choice-frame fn-psc-source-info-completion-composes-unfolds))))

(in-theory (disable fn-psc-model-retained-agent fn-psc-model-source-info-agent fn-psc-model-source-info-agent-cost fn-psc-model-source-info-choice fn-psc-model-source-info-choice-cost fn-psc-model-source-info-complete fn-psc-model-source-info-cost fn-psc-model-source-info-field fn-psc-model-source-info-tail fn-psc-model-source-info-tail-cost fn-psc-source-contextp))
