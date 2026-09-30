; Proof-only residual for the actual virtual-source byte comparison machine.
; General recipe composition to fn-pb/fn-pbb remains OPEN.
(in-package "ACL2")
(include-book "post-identity-source-cursor-source-invariants")
(include-book "poster-bytes-source-buffer")
(local (include-book "arithmetic/top" :dir :system))
(defun fn-psc-model-source (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-psc-get mode c) :source-held) held incoming))
(defun fn-psc-model-reference-byte (c index incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((ref (fn-psc-get ref c))
        (offset (+ (nfix (fn-psc-get ref-start c)) (nfix index))))
  (cond ((equal ref :incoming) (nth offset incoming))
        ((equal ref :self) (nth offset (fn-psc-model-source c incoming held)))
        ((equal ref :msgid)
         (let ((text (fn-psc-get msgid c)))
          (if (and (stringp text) (< offset (length text)))
              (char-code (char text offset)) nil)))
        ((equal ref :path) (nth offset '(112 97 116 104 58 32)))
        (t (if (true-listp ref) (nth offset ref) nil)))))
(defun fn-psc-model-target-byte (c index pos incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((byte (nth (nfix pos) (fn-psc-model-source c incoming held))))
  (if (and (equal (fn-psc-get ref c) :path) (< (nfix index) 4)
           (integerp byte) (<= 65 byte) (<= byte 90)) (+ byte 32) byte)))
(defun fn-psc-model-prefix (remaining index pos c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (nfix remaining)))
 (if (zp remaining) t
  (and (< (nfix pos) (nfix (fn-psc-get n c)))
       (equal (fn-psc-model-reference-byte c index incoming held)
              (fn-psc-model-target-byte c index pos incoming held))
       (fn-psc-model-prefix (1- remaining) (1+ (nfix index))
                            (1+ (nfix pos)) c incoming held))))
(defun fn-psc-model-compare-value (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((phase (fn-psc-get phase c)) (i (nfix (fn-psc-get index c)))
        (p (nfix (fn-psc-get pos c)))
        (remaining (nfix (- (nfix (fn-psc-get ref-len c)) i))))
  (cond ((equal phase :control) (if (fn-psc-get ok c) t nil))
        ((equal phase :target)
         (and (< p (nfix (fn-psc-get n c)))
              (equal (fn-psc-get cached c)
                     (fn-psc-model-target-byte c i p incoming held))
              (fn-psc-model-prefix (nfix (1- remaining)) (1+ i) (1+ p)
                                   c incoming held)))
        (t (fn-psc-model-prefix remaining i p c incoming held)))))
(defun fn-psc-model-demanded-byte (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-demand c)))
  (if (consp d) (nth (cadr d) (if (equal (car d) :held) held incoming)) nil)))
(in-theory (disable fn-psc-model-source fn-psc-model-reference-byte
                    fn-psc-model-target-byte fn-psc-model-prefix
                    fn-psc-model-compare-value fn-psc-model-demanded-byte))

(local (defthm fn-psc-natural-nfix-unfolds (implies (natp x) (equal (nfix x) x)) :hints (("Goal" :in-theory (enable nfix)))))
(local (defthm fn-psc-model-reference-update-other
 (implies (and (natp slot) (not (member-equal slot '(1 2 4 9 10))))
  (equal (fn-psc-model-reference-byte (update-nth slot value c) index incoming held)
         (fn-psc-model-reference-byte c index incoming held)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-reference-byte fn-psc-model-source)
                               (nth update-nth nfix))))))
(local (defthm fn-psc-model-target-update-other
 (implies (and (natp slot) (not (member-equal slot '(1 2 4 9 10))))
  (equal (fn-psc-model-target-byte (update-nth slot value c) index pos incoming held)
         (fn-psc-model-target-byte c index pos incoming held)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-target-byte fn-psc-model-source)
                               (nth update-nth nfix))))))
(local (defthm fn-psc-model-prefix-update-other
 (implies (and (natp slot) (not (member-equal slot '(1 2 4 9 10))))
  (equal (fn-psc-model-prefix remaining index pos (update-nth slot value c) incoming held)
         (fn-psc-model-prefix remaining index pos c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-prefix remaining index pos c incoming held)
          :in-theory (e/d (fn-psc-model-prefix) (nth update-nth nfix))))))
(local (defthm fn-psc-model-prefix-unfolds
 (equal (fn-psc-model-prefix remaining index pos c incoming held)
  (if (zp remaining) t
   (and (< (nfix pos) (nfix (fn-psc-get n c)))
        (equal (fn-psc-model-reference-byte c index incoming held)
               (fn-psc-model-target-byte c index pos incoming held))
        (fn-psc-model-prefix (1- remaining) (1+ (nfix index))
                            (1+ (nfix pos)) c incoming held))))
 :rule-classes nil
 :hints (("Goal" :expand ((fn-psc-model-prefix remaining index pos c incoming held))))))
(local (defthm fn-psc-model-reference-is-expected
 (implies (not (member-eq (fn-psc-get ref c) '(:incoming :self)))
  (equal (fn-psc-model-reference-byte c (fn-psc-get index c) incoming held)
         (fn-psc-expected c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-expected fn-psc-model-reference-byte)
                               (nth nfix len ))))))
(local (defthm fn-psc-demanded-span-byte
 (implies
  (and (equal (fn-psc-get phase c) :compare)
       (< (nfix (fn-psc-get index c)) (nfix (fn-psc-get ref-len c)))
       (< (nfix (fn-psc-get pos c)) (nfix (fn-psc-get n c)))
       (member-eq (fn-psc-get ref c) '(:incoming :self)))
  (equal (fn-psc-model-demanded-byte c incoming held)
         (fn-psc-model-reference-byte c (fn-psc-get index c) incoming held)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-model-demanded-byte fn-psc-demand fn-psc-model-reference-byte
        fn-psc-model-source) (nth nfix len))))))
(local (defthm fn-psc-demanded-target-byte
 (implies
  (and (member-eq (fn-psc-get phase c) '(:compare :target))
       (< (nfix (fn-psc-get index c)) (nfix (fn-psc-get ref-len c)))
       (< (nfix (fn-psc-get pos c)) (nfix (fn-psc-get n c)))
       (or (equal (fn-psc-get phase c) :target)
           (not (member-eq (fn-psc-get ref c) '(:incoming :self)))))
  (equal (fn-psc-model-demanded-byte c incoming held)
         (nth (nfix (fn-psc-get pos c)) (fn-psc-model-source c incoming held))))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-model-demanded-byte fn-psc-demand fn-psc-model-source)
       (nth nfix len))))))
(defthm fn-psc-compare-step-preserves-prefix
 (implies
  (and (member-eq (fn-psc-get phase c) '(:compare :target))
       (natp (fn-psc-get index c)) (natp (fn-psc-get ref-len c))
       (<= (fn-psc-get index c) (fn-psc-get ref-len c))
       (or (equal (fn-psc-get phase c) :compare)
           (< (fn-psc-get index c) (fn-psc-get ref-len c)))
       (equal byte (fn-psc-model-demanded-byte c incoming held)))
  (equal (fn-psc-model-compare-value (fn-psc-step c byte) incoming held)
         (fn-psc-model-compare-value c incoming held)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step fn-psc-return fn-psc-model-compare-value
        fn-psc-model-target-byte)
       (nth update-nth len nfix ))
  :use ((:instance fn-psc-model-prefix-unfolds
          (remaining (nfix (- (nfix (fn-psc-get ref-len c))
                              (nfix (fn-psc-get index c)))))
          (index (nfix (fn-psc-get index c)))
          (pos (nfix (fn-psc-get pos c))))))))
(defun fn-psc-comparison-statep (c)
 (declare (xargs :guard t :verify-guards nil))
 (let ((phase (fn-psc-get phase c)) (i (fn-psc-get index c))
       (count (fn-psc-get ref-len c)))
  (or (not (member-eq phase '(:compare :target)))
      (and (natp i) (natp count) (<= i count)
           (or (equal phase :compare) (< i count))))))
(local (defthm fn-psc-compare-establishes-comparison-state
 (fn-psc-comparison-statep (fn-psc-compare pos ref start count resume c))
 :hints (("Goal" :in-theory (e/d (fn-psc-comparison-statep fn-psc-compare)
                               (nth update-nth))))))
(local (defthm fn-psc-return-establishes-comparison-state
 (fn-psc-comparison-statep (fn-psc-return ok c))
 :hints (("Goal" :in-theory (e/d (fn-psc-comparison-statep fn-psc-return)
                               (nth update-nth))))))
(local (defthm fn-psc-finish-establishes-comparison-state
 (fn-psc-comparison-statep (fn-psc-finish result c))
 :hints (("Goal" :in-theory (e/d (fn-psc-comparison-statep fn-psc-finish)
                               (nth update-nth))))))
(local (defthm fn-psc-literal-establishes-comparison-state
 (fn-psc-comparison-statep (fn-psc-literal pos bytes resume c))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-comparison-statep) (nth update-nth nfix len))))))
(local (defthm fn-psc-agent-compare-establishes-comparison-state
 (fn-psc-comparison-statep (fn-psc-agent-compare pos resume c))
 :hints (("Goal" :in-theory (e/d (fn-psc-agent-compare fn-psc-comparison-statep) (nth update-nth nfix len))))))
(local (defthm fn-psc-msgid-compare-establishes-comparison-state
 (fn-psc-comparison-statep (fn-psc-msgid-compare pos resume c))
 :hints (("Goal" :in-theory (e/d (fn-psc-msgid-compare fn-psc-comparison-statep) (nth update-nth nfix len))))))
(local (defthm fn-psc-date-compare-establishes-comparison-state
 (fn-psc-comparison-statep (fn-psc-date-compare pos resume c))
 :hints (("Goal" :in-theory (e/d (fn-psc-date-compare fn-psc-comparison-statep) (nth update-nth nfix len))))))
(local (defthm fn-psc-info-compare-establishes-comparison-state
 (fn-psc-comparison-statep (fn-psc-info-compare pos resume c))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare fn-psc-comparison-statep) (nth update-nth nfix len))))))
(local (defthm fn-psc-control-establishes-comparison-state
 (fn-psc-comparison-statep (fn-psc-control c))
 :hints (("Goal" :in-theory (e/d (fn-psc-control fn-psc-comparison-statep) (nth update-nth nfix len))))))
(defthm fn-psc-step-preserves-comparison-state
 (implies (fn-psc-comparison-statep c)
          (fn-psc-comparison-statep (fn-psc-step c byte)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step fn-psc-comparison-statep) (nth update-nth nfix len)))))
(in-theory (disable fn-psc-comparison-statep))
(defun fn-psc-model-comparison-run (fuel c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (not (member-eq (fn-psc-get phase c) '(:compare :target)))) c
  (fn-psc-model-comparison-run
   (1- fuel) (fn-psc-step c (fn-psc-model-demanded-byte c incoming held))
   incoming held)))
(defthm fn-psc-comparison-run-preserves-prefix
 (implies (fn-psc-comparison-statep c)
  (equal (fn-psc-model-compare-value
           (fn-psc-model-comparison-run fuel c incoming held) incoming held)
         (fn-psc-model-compare-value c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-comparison-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-run fn-psc-comparison-statep)
              (nth nfix fn-psc-model-demanded-byte fn-psc-step
               fn-psc-compare-step-preserves-prefix)))
         ("Subgoal *1/2" :use ((:instance fn-psc-compare-step-preserves-prefix
                         (byte (fn-psc-model-demanded-byte c incoming held)))))))
(in-theory (disable fn-psc-model-comparison-run))
(defun fn-psc-comparison-rank (c)
 (declare (xargs :guard t :verify-guards nil))
 (let ((remaining (nfix (- (nfix (fn-psc-get ref-len c))
                          (nfix (fn-psc-get index c))))))
  (case (fn-psc-get phase c)
   (:compare (+ 1 (* 2 remaining)))
   (:target (* 2 remaining))
   (otherwise 0))))
(defthm fn-psc-comparison-rank-natural-by-definition
 (natp (fn-psc-comparison-rank c))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn-psc-comparison-rank))))
(defthm fn-psc-comparison-step-productive
 (implies (and (fn-psc-comparison-statep c)
               (member-eq (fn-psc-get phase c) '(:compare :target)))
  (< (fn-psc-comparison-rank (fn-psc-step c byte))
     (fn-psc-comparison-rank c)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-comparison-rank fn-psc-comparison-statep fn-psc-step fn-psc-return)
       (nth update-nth len)))))
(in-theory (disable fn-psc-comparison-rank))

(local (defthm fn-psc-active-comparison-rank-positive
 (implies (and (fn-psc-comparison-statep c)
               (member-eq (fn-psc-get phase c) '(:compare :target)))
          (< 0 (fn-psc-comparison-rank c)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-comparison-statep fn-psc-comparison-rank) (nth len update-nth))))))
(local (defthm fn-psc-comparison-zero-rank-inactive
 (implies (and (fn-psc-comparison-statep c)
               (equal (fn-psc-comparison-rank c) 0))
          (and (not (equal (fn-psc-get phase c) :compare))
               (not (equal (fn-psc-get phase c) :target))))
 :hints (("Goal" :use ((:instance fn-psc-active-comparison-rank-positive))
          :in-theory (disable fn-psc-active-comparison-rank-positive)))))
(defthm fn-psc-comparison-run-finishes
 (implies (and (fn-psc-comparison-statep c) (natp fuel)
               (<= (fn-psc-comparison-rank c) fuel))
  (not (member-eq
        (fn-psc-get phase (fn-psc-model-comparison-run fuel c incoming held))
        '(:compare :target))))
 :hints (("Goal" :induct (fn-psc-model-comparison-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-run)
              (nth nfix fn-psc-model-demanded-byte fn-psc-step
               fn-psc-comparison-step-productive)))
         ("Subgoal *1/2" :use ((:instance fn-psc-comparison-step-productive
                         (byte (fn-psc-model-demanded-byte c incoming held)))))))

; Exact first-line residual and resumable endpoint over actual fn-pb-line.
(local (defthm fn-psc-line-tail-unfolds
 (implies (and (natp p) (< p (len xs)))
  (equal (fn-pb-line (nthcdr p xs))
         (if (equal (nth p xs) 10) (list 10)
          (cons (nth p xs) (fn-pb-line (nthcdr (+ 1 p) xs))))))
 :hints (("Goal" :induct (nthcdr p xs)
          :in-theory (enable nthcdr nth fn-pb-line)))))
(local (defthm fn-psc-line-at-end-empty
 (equal (fn-pb-line (nthcdr (len xs) xs)) nil)
 :hints (("Goal" :induct (len xs) :in-theory (enable nthcdr len fn-pb-line)))))

(local (defthm fn-psc-line-length-cons-unfolds
 (equal (len (cons x xs)) (+ 1 (len xs)))
 :hints (("Goal" :in-theory (enable len)))))

(defun fn-psc-model-line-end (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((p (nfix (fn-psc-get pos c))))
  (if (equal (fn-psc-get phase c) :line)
      (+ p (len (fn-pb-line (nthcdr p (fn-psc-model-source c incoming held)))))
   p)))
(local (defthm fn-psc-model-source-update-line-fields
 (implies (not (member-equal field '(1 2 4 9 10)))
  (equal (fn-psc-model-source (update-nth field value c) incoming held)
         (fn-psc-model-source c incoming held)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source) (nth update-nth len))))))
(local (defthm fn-psc-line-demanded-byte
 (implies (and (equal (fn-psc-get phase c) :line)
               (< (nfix (fn-psc-get pos c)) (nfix (fn-psc-get n c))))
  (equal (fn-psc-model-demanded-byte c incoming held)
         (nth (nfix (fn-psc-get pos c)) (fn-psc-model-source c incoming held))))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-model-demanded-byte fn-psc-demand fn-psc-model-source)
       (nth nfix len))))))
(defthm fn-psc-line-step-preserves-end
 (implies (and (equal (fn-psc-get phase c) :line)
               (natp (fn-psc-get pos c))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
               (<= (fn-psc-get pos c) (fn-psc-get n c))
               (equal byte (fn-psc-model-demanded-byte c incoming held)))
  (equal (fn-psc-model-line-end (fn-psc-step c byte) incoming held)
         (fn-psc-model-line-end c incoming held)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step fn-psc-return fn-psc-model-line-end)
       (nth update-nth nfix len fn-pb-line nthcdr))
  :use ((:instance fn-psc-line-tail-unfolds
          (p (fn-psc-get pos c)) (xs (fn-psc-model-source c incoming held)))))))
(in-theory (disable fn-psc-model-line-end))
(defun fn-psc-line-statep (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (and (natp (fn-psc-get pos c))
      (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
      (<= (fn-psc-get pos c) (fn-psc-get n c))))
(defthm fn-psc-line-step-preserves-state
 (implies (and (equal (fn-psc-get phase c) :line)
               (fn-psc-line-statep c incoming held))
  (fn-psc-line-statep (fn-psc-step c byte) incoming held))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-line-statep fn-psc-step fn-psc-return)
       (nth update-nth len nfix)))))
(in-theory (disable fn-psc-line-statep))
(defun fn-psc-model-line-run (fuel c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (not (equal (fn-psc-get phase c) :line))) c
  (fn-psc-model-line-run (1- fuel)
   (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held)))
(defthm fn-psc-line-run-preserves-end
 (implies (fn-psc-line-statep c incoming held)
  (equal (fn-psc-model-line-end (fn-psc-model-line-run fuel c incoming held) incoming held)
         (fn-psc-model-line-end c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-line-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-line-run fn-psc-line-statep)
             (nth nfix fn-psc-step fn-psc-model-demanded-byte
              fn-psc-line-step-preserves-end)))
         ("Subgoal *1/2" :use ((:instance fn-psc-line-step-preserves-end
          (byte (fn-psc-model-demanded-byte c incoming held)))))))

(defun fn-psc-line-rank (c)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-psc-get phase c) :line)
  (+ 1 (nfix (- (nfix (fn-psc-get n c)) (nfix (fn-psc-get pos c))))) 0))
(defthm fn-psc-line-step-productive
 (implies (and (equal (fn-psc-get phase c) :line)
               (fn-psc-line-statep c incoming held))
  (< (fn-psc-line-rank (fn-psc-step c byte)) (fn-psc-line-rank c)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-line-rank fn-psc-line-statep fn-psc-step fn-psc-return)
       (nth update-nth len)))))
(local (defthm fn-psc-zero-line-rank-inactive
 (implies (equal (fn-psc-line-rank c) 0)
          (not (equal (fn-psc-get phase c) :line)))
 :hints (("Goal" :in-theory (enable fn-psc-line-rank)))))
(in-theory (disable fn-psc-line-rank))
(defthm fn-psc-line-run-finishes
 (implies (and (fn-psc-line-statep c incoming held) (natp fuel)
               (<= (fn-psc-line-rank c) fuel))
  (not (equal (fn-psc-get phase (fn-psc-model-line-run fuel c incoming held)) :line)))
 :hints (("Goal" :induct (fn-psc-model-line-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-line-run)
             (nth nfix fn-psc-step fn-psc-model-demanded-byte
              fn-psc-line-step-productive)))
         ("Subgoal *1/2" :use ((:instance fn-psc-line-step-productive
          (byte (fn-psc-model-demanded-byte c incoming held)))))))

(defthm fn-psc-line-run-exact-end
 (implies (and (equal (fn-psc-get phase c) :line)
               (fn-psc-line-statep c incoming held) (natp fuel)
               (<= (fn-psc-line-rank c) fuel))
  (equal (nfix (fn-psc-get pos (fn-psc-model-line-run fuel c incoming held)))
         (+ (fn-psc-get pos c)
            (len (fn-pb-line (nthcdr (fn-psc-get pos c)
                         (fn-psc-model-source c incoming held)))))))
 :hints (("Goal" :use ((:instance fn-psc-line-run-preserves-end)
                       (:instance fn-psc-line-run-finishes))
          :in-theory (e/d (fn-psc-model-line-end fn-psc-line-statep)
             (nth nfix len fn-psc-model-line-run fn-pb-line nthcdr
              fn-psc-line-run-preserves-end fn-psc-line-run-finishes)))))


; Exact parameter-tail residual for both source inverse and agent discovery.
(local (defthm fn-psc-tail-successor-unfolds
 (implies (natp p) (equal (cdr (nthcdr p xs)) (nthcdr (+ 1 p) xs)))
 :hints (("Goal" :induct (nthcdr p xs) :in-theory (enable nthcdr)))))
(local (defthm fn-psc-tail-head-unfolds
 (implies (natp p) (equal (car (nthcdr p xs)) (nth p xs)))
 :hints (("Goal" :induct (nthcdr p xs) :in-theory (enable nthcdr nth)))))
(local (defthm fn-psc-tail-consp-unfolds
 (implies (natp p) (equal (consp (nthcdr p xs)) (< p (len xs))))
 :hints (("Goal" :induct (nthcdr p xs) :do-not (quote (generalize eliminate-destructors)) :in-theory (enable nthcdr len)) ("Subgoal *1/2.2'" :cases ((< p (+ 1 (len (cdr xs)))))))))
(local (defthm fn-psc-param-rest-tail-unfolds
 (implies (natp p)
  (equal (fn-inj-param-rest (nthcdr p xs))
   (if (>= p (len xs)) :no
    (if (equal (nth p xs) 13)
        (if (and (< (+ 1 p) (len xs)) (equal (nth (+ 1 p) xs) 10))
            (nthcdr (+ 2 p) xs) :no)
     (if (equal (nth p xs) 10) :no
      (fn-inj-param-rest (nthcdr (+ 1 p) xs)))))))
 :rule-classes nil
 :hints (("Goal" :expand ((fn-inj-param-rest (nthcdr p xs)))
          :in-theory (disable fn-inj-param-rest nthcdr nth len)))))
(defun fn-psc-model-param-value (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((p (nfix (fn-psc-get pos c))) (xs (fn-psc-model-source c incoming held)))
  (case (fn-psc-get phase c)
   (:params (fn-inj-param-rest (nthcdr p xs)))
   (:params-lf (if (and (< p (len xs)) (equal (nth p xs) 10)) (nthcdr (+ 1 p) xs) :no))
   (otherwise (if (fn-psc-get ok c) (nthcdr p xs) :no)))))
(local (defthm fn-psc-param-demanded-byte
 (implies (and (member-eq (fn-psc-get phase c) '(:params :params-lf))
               (< (nfix (fn-psc-get pos c)) (nfix (fn-psc-get n c))))
  (equal (fn-psc-model-demanded-byte c incoming held)
         (nth (nfix (fn-psc-get pos c)) (fn-psc-model-source c incoming held))))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-model-demanded-byte fn-psc-demand fn-psc-model-source)
       (nth nfix len))))))
(defthm fn-psc-param-step-preserves-value
 (implies (and (member-eq (fn-psc-get phase c) '(:params :params-lf))
               (fn-psc-line-statep c incoming held)
               (equal byte (fn-psc-model-demanded-byte c incoming held)))
  (equal (fn-psc-model-param-value (fn-psc-step c byte) incoming held)
         (fn-psc-model-param-value c incoming held)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step fn-psc-return fn-psc-model-param-value fn-psc-line-statep)
       (nth update-nth nfix len fn-inj-param-rest nthcdr))
  :use ((:instance fn-psc-param-rest-tail-unfolds
          (p (fn-psc-get pos c)) (xs (fn-psc-model-source c incoming held)))))))

(in-theory (disable fn-psc-model-param-value))
(defthm fn-psc-param-step-preserves-state
 (implies (and (member-eq (fn-psc-get phase c) '(:params :params-lf))
               (fn-psc-line-statep c incoming held))
  (fn-psc-line-statep (fn-psc-step c byte) incoming held))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-line-statep fn-psc-step fn-psc-return)
       (nth update-nth len nfix)))))
(defun fn-psc-model-param-run (fuel c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (not (member-eq (fn-psc-get phase c) '(:params :params-lf)))) c
  (fn-psc-model-param-run (1- fuel)
   (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held)))
(defthm fn-psc-param-run-preserves-value
 (implies (fn-psc-line-statep c incoming held)
  (equal (fn-psc-model-param-value (fn-psc-model-param-run fuel c incoming held) incoming held)
         (fn-psc-model-param-value c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-param-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-param-run fn-psc-line-statep)
             (nth nfix fn-psc-step fn-psc-model-demanded-byte
              fn-psc-param-step-preserves-value)))
         ("Subgoal *1/2" :use ((:instance fn-psc-param-step-preserves-value
          (byte (fn-psc-model-demanded-byte c incoming held)))))))
(defun fn-psc-param-rank (c)
 (declare (xargs :guard t :verify-guards nil))
 (if (member-eq (fn-psc-get phase c) '(:params :params-lf))
  (+ 1 (nfix (- (nfix (fn-psc-get n c)) (nfix (fn-psc-get pos c))))) 0))
(defthm fn-psc-param-step-productive
 (implies (and (member-eq (fn-psc-get phase c) '(:params :params-lf))
               (fn-psc-line-statep c incoming held))
  (< (fn-psc-param-rank (fn-psc-step c byte)) (fn-psc-param-rank c)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-param-rank fn-psc-line-statep fn-psc-step fn-psc-return)
       (nth update-nth len)))))
(local (defthm fn-psc-zero-param-rank-inactive
 (implies (equal (fn-psc-param-rank c) 0)
          (not (member-eq (fn-psc-get phase c) '(:params :params-lf))))
 :hints (("Goal" :in-theory (enable fn-psc-param-rank)))))
(in-theory (disable fn-psc-param-rank))
(defthm fn-psc-param-run-finishes
 (implies (and (fn-psc-line-statep c incoming held) (natp fuel)
               (<= (fn-psc-param-rank c) fuel))
  (not (member-eq (fn-psc-get phase (fn-psc-model-param-run fuel c incoming held)) '(:params :params-lf))))
 :hints (("Goal" :induct (fn-psc-model-param-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-param-run)
             (nth nfix fn-psc-step fn-psc-model-demanded-byte
              fn-psc-param-step-productive)))
         ("Subgoal *1/2" :use ((:instance fn-psc-param-step-productive
          (byte (fn-psc-model-demanded-byte c incoming held)))))))

; Exact comparison exit flag, consumed position, and actual strip correspondence.
(local (defthm fn-psc-comparison-step-phase
 (implies (member-eq (fn-psc-get phase c) '(:compare :target))
  (member-eq (fn-psc-get phase (fn-psc-step c byte)) '(:compare :target :control)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-return)
                                     (nth update-nth len nfix))))))
(local (defthm fn-psc-comparison-run-phase
 (implies (member-eq (fn-psc-get phase c) '(:compare :target :control))
  (member-eq (fn-psc-get phase (fn-psc-model-comparison-run fuel c incoming held))
             '(:compare :target :control)))
 :hints (("Goal" :induct (fn-psc-model-comparison-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-run)
                   (nth len nfix fn-psc-step fn-psc-model-demanded-byte))))))
(defthm fn-psc-comparison-run-returns-control
 (implies (and (member-eq (fn-psc-get phase c) '(:compare :target))
               (fn-psc-comparison-statep c) (natp fuel)
               (<= (fn-psc-comparison-rank c) fuel))
  (equal (fn-psc-get phase (fn-psc-model-comparison-run fuel c incoming held)) :control))
 :hints (("Goal" :use ((:instance fn-psc-comparison-run-finishes)
                       (:instance fn-psc-comparison-run-phase))
          :in-theory (disable fn-psc-comparison-run-finishes fn-psc-comparison-run-phase
             nth nfix len fn-psc-step fn-psc-model-comparison-run))))
(defthm fn-psc-comparison-run-exact-flag
 (implies (and (member-eq (fn-psc-get phase c) '(:compare :target))
               (fn-psc-comparison-statep c) (natp fuel)
               (<= (fn-psc-comparison-rank c) fuel))
  (equal (if (fn-psc-get ok (fn-psc-model-comparison-run fuel c incoming held)) t nil)
         (fn-psc-model-compare-value c incoming held)))
 :hints (("Goal" :use ((:instance fn-psc-comparison-run-preserves-prefix)
                       (:instance fn-psc-comparison-run-returns-control))
          :in-theory (e/d (fn-psc-model-compare-value)
             (nth nfix len fn-psc-model-prefix fn-psc-model-comparison-run
              fn-psc-comparison-run-preserves-prefix fn-psc-comparison-run-returns-control)))))

(defun fn-psc-comparison-positionp (c)
 (declare (xargs :guard t :verify-guards nil))
 (and (natp (fn-psc-get base c)) (natp (fn-psc-get pos c))
  (if (member-eq (fn-psc-get phase c) '(:compare :target))
      (equal (fn-psc-get pos c) (+ (fn-psc-get base c) (fn-psc-get index c)))
   (if (fn-psc-get ok c)
       (equal (fn-psc-get pos c) (+ (fn-psc-get base c) (fn-psc-get ref-len c))) t))))
(defthm fn-psc-comparison-step-preserves-position
 (implies (and (member-eq (fn-psc-get phase c) '(:compare :target))
               (fn-psc-comparison-statep c) (fn-psc-comparison-positionp c))
  (fn-psc-comparison-positionp (fn-psc-step c byte)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step fn-psc-return fn-psc-comparison-statep fn-psc-comparison-positionp)
       (nth update-nth len nfix)))))
(in-theory (disable fn-psc-comparison-positionp))
(defthm fn-psc-comparison-run-preserves-position
 (implies (and (fn-psc-comparison-statep c) (fn-psc-comparison-positionp c))
  (fn-psc-comparison-positionp (fn-psc-model-comparison-run fuel c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-comparison-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-run)
                   (nth len nfix fn-psc-step fn-psc-model-demanded-byte)))))
(defthm fn-psc-compare-establishes-position
 (fn-psc-comparison-positionp (fn-psc-compare pos ref start count resume c))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-comparison-positionp fn-psc-compare) (nth update-nth len)))))

(defun fn-psc-comparison-origin (c)
 (declare (xargs :guard t :verify-guards nil))
 (list (fn-psc-get base c) (fn-psc-get ref-len c)))
(local (defthm fn-psc-comparison-step-preserves-origin
 (implies (member-eq (fn-psc-get phase c) '(:compare :target))
  (equal (fn-psc-comparison-origin (fn-psc-step c byte)) (fn-psc-comparison-origin c)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-comparison-origin fn-psc-step fn-psc-return) (nth update-nth len nfix))))))
(defthm fn-psc-comparison-run-preserves-origin
 (equal (fn-psc-comparison-origin (fn-psc-model-comparison-run fuel c incoming held))
        (fn-psc-comparison-origin c))
 :hints (("Goal" :induct (fn-psc-model-comparison-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-run)
                   (nth len nfix fn-psc-step fn-psc-model-demanded-byte)))))
(in-theory (disable fn-psc-comparison-origin))
(defthm fn-psc-comparison-run-exact-position
 (implies (and (fn-psc-comparison-statep c) (fn-psc-comparison-positionp c)
               (member-eq (fn-psc-get phase c) '(:compare :target))
               (natp fuel) (<= (fn-psc-comparison-rank c) fuel)
               (fn-psc-get ok (fn-psc-model-comparison-run fuel c incoming held)))
  (equal (fn-psc-get pos (fn-psc-model-comparison-run fuel c incoming held))
         (+ (fn-psc-get base c) (fn-psc-get ref-len c))))
 :hints (("Goal" :use ((:instance fn-psc-comparison-run-preserves-position)
                       (:instance fn-psc-comparison-run-returns-control)
                       (:instance fn-psc-comparison-run-preserves-origin))
          :in-theory (e/d (fn-psc-comparison-positionp fn-psc-comparison-origin)
             (nth nfix len fn-psc-model-comparison-run
              fn-psc-comparison-run-preserves-position fn-psc-comparison-run-returns-control
              fn-psc-comparison-run-preserves-origin)))))

(defun fn-psc-model-reference-octets (remaining index c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (nfix remaining)))
 (if (zp remaining) nil
  (cons (fn-psc-model-reference-byte c index incoming held)
        (fn-psc-model-reference-octets (1- remaining) (1+ (nfix index)) c incoming held))))
(defthm fn-psc-prefix-is-actual-strip
 (implies (and (not (equal (fn-psc-get ref c) :path))
               (natp pos) (natp index)
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-prefix remaining index pos c incoming held)
         (not (equal (fn-inj-strip (fn-psc-model-reference-octets remaining index c incoming held)
                                  (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
 :hints (("Goal" :induct (fn-psc-model-prefix remaining index pos c incoming held)
          :in-theory (e/d (fn-psc-model-prefix fn-psc-model-reference-octets
                            fn-psc-model-target-byte fn-inj-strip)
                         (nth nthcdr len true-listp fn-pbb-strip-at-is-inj-strip fn-psc-model-reference-byte fn-psc-model-source)))))

(defthm fn-psc-comparison-run-exact-strip
 (implies (and (equal (fn-psc-get phase c) :compare)
               (fn-psc-comparison-statep c) (natp (fn-psc-get pos c))
               (not (equal (fn-psc-get ref c) :path))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
               (natp fuel) (<= (fn-psc-comparison-rank c) fuel))
  (equal (if (fn-psc-get ok (fn-psc-model-comparison-run fuel c incoming held)) t nil)
   (not (equal
    (fn-inj-strip
      (fn-psc-model-reference-octets
        (nfix (- (fn-psc-get ref-len c) (fn-psc-get index c)))
        (fn-psc-get index c) c incoming held)
      (nthcdr (fn-psc-get pos c) (fn-psc-model-source c incoming held))) :no))))
 :hints (("Goal" :use ((:instance fn-psc-comparison-run-exact-flag)
                      (:instance fn-psc-prefix-is-actual-strip
                       (remaining (nfix (- (fn-psc-get ref-len c) (fn-psc-get index c))))
                       (index (fn-psc-get index c)) (pos (fn-psc-get pos c))))
          :in-theory (e/d (fn-psc-model-compare-value fn-psc-comparison-statep)
             (nth nfix len fn-psc-model-prefix fn-psc-model-reference-octets
              fn-psc-model-comparison-run fn-inj-strip fn-pbb-strip-at-is-inj-strip
              fn-psc-comparison-run-exact-flag fn-psc-prefix-is-actual-strip)))))

; Proof-only macro traces consume exactly the actual paid byte/control steps.
(defun fn-psc-model-comparison-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (fn-psc-comparison-rank c)
  :hints (("Goal" :use ((:instance fn-psc-comparison-step-productive
       (byte (fn-psc-model-demanded-byte c incoming held))))
   :in-theory (disable fn-psc-step fn-psc-model-demanded-byte fn-psc-comparison-rank
                        fn-psc-comparison-statep fn-psc-comparison-step-productive)))))
 (if (and (fn-psc-comparison-statep c)
          (member-eq (fn-psc-get phase c) '(:compare :target)))
  (fn-psc-model-comparison-complete
   (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held)
  c))
(defthm fn-psc-comparison-complete-preserves-prefix
 (implies (fn-psc-comparison-statep c)
  (equal (fn-psc-model-compare-value (fn-psc-model-comparison-complete c incoming held) incoming held)
         (fn-psc-model-compare-value c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-complete fn-psc-comparison-statep)
             (nth nfix len fn-psc-step fn-psc-model-demanded-byte
              fn-psc-compare-step-preserves-prefix)))
         ("Subgoal *1/1" :use ((:instance fn-psc-compare-step-preserves-prefix
          (byte (fn-psc-model-demanded-byte c incoming held)))))))
(defthm fn-psc-comparison-complete-returns-control
 (implies (and (fn-psc-comparison-statep c)
               (member-eq (fn-psc-get phase c) '(:compare :target :control)))
  (equal (fn-psc-get phase (fn-psc-model-comparison-complete c incoming held)) :control))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-complete)
             (nth nfix len fn-psc-step fn-psc-model-demanded-byte)))))
(defthm fn-psc-comparison-complete-preserves-origin
 (equal (fn-psc-comparison-origin (fn-psc-model-comparison-complete c incoming held))
        (fn-psc-comparison-origin c))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-complete)
                   (nth len nfix fn-psc-step fn-psc-model-demanded-byte)))))
(defthm fn-psc-comparison-complete-preserves-position
 (implies (and (fn-psc-comparison-statep c) (fn-psc-comparison-positionp c))
  (fn-psc-comparison-positionp (fn-psc-model-comparison-complete c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-complete)
                   (nth len nfix fn-psc-step fn-psc-model-demanded-byte)))))
(defthm fn-psc-comparison-complete-exact-flag
 (implies (and (member-eq (fn-psc-get phase c) '(:compare :target))
               (fn-psc-comparison-statep c))
  (equal (if (fn-psc-get ok (fn-psc-model-comparison-complete c incoming held)) t nil)
         (fn-psc-model-compare-value c incoming held)))
 :hints (("Goal" :use ((:instance fn-psc-comparison-complete-preserves-prefix)
                       (:instance fn-psc-comparison-complete-returns-control))
          :in-theory (e/d (fn-psc-model-compare-value)
             (nth nfix len fn-psc-model-prefix fn-psc-model-comparison-complete
              fn-psc-comparison-complete-preserves-prefix fn-psc-comparison-complete-returns-control)))))
(defthm fn-psc-comparison-complete-exact-position
 (implies (and (fn-psc-comparison-statep c) (fn-psc-comparison-positionp c)
               (member-eq (fn-psc-get phase c) '(:compare :target))
               (fn-psc-get ok (fn-psc-model-comparison-complete c incoming held)))
  (equal (fn-psc-get pos (fn-psc-model-comparison-complete c incoming held))
         (+ (fn-psc-get base c) (fn-psc-get ref-len c))))
 :hints (("Goal" :use ((:instance fn-psc-comparison-complete-preserves-position)
                       (:instance fn-psc-comparison-complete-returns-control)
                       (:instance fn-psc-comparison-complete-preserves-origin))
          :in-theory (e/d (fn-psc-comparison-positionp fn-psc-comparison-origin)
             (nth nfix len fn-psc-model-comparison-complete
              fn-psc-comparison-complete-preserves-position fn-psc-comparison-complete-returns-control
              fn-psc-comparison-complete-preserves-origin)))))
(defun fn-psc-model-comparison-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (fn-psc-comparison-rank c)
  :hints (("Goal" :use ((:instance fn-psc-comparison-step-productive
       (byte (fn-psc-model-demanded-byte c incoming held))))
   :in-theory (disable fn-psc-step fn-psc-model-demanded-byte fn-psc-comparison-rank
                        fn-psc-comparison-statep fn-psc-comparison-step-productive)))))
 (if (and (fn-psc-comparison-statep c)
          (member-eq (fn-psc-get phase c) '(:compare :target)))
  (+ 1 (fn-psc-model-comparison-cost
   (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held))
  0))
(defthm fn-psc-comparison-cost-bounded
 (<= (fn-psc-model-comparison-cost c incoming held) (fn-psc-comparison-rank c))
 :hints (("Goal" :induct (fn-psc-model-comparison-cost c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-cost)
             (nth nfix len fn-psc-step fn-psc-model-demanded-byte
              fn-psc-comparison-step-productive)))
         ("Subgoal *1/1" :use ((:instance fn-psc-comparison-step-productive
          (byte (fn-psc-model-demanded-byte c incoming held)))))))
(defun fn-psc-model-byte-run (fuel c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) c
  (fn-psc-model-byte-run (1- fuel)
   (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held)))
(defthm fn-psc-comparison-complete-is-actual-steps
 (equal (fn-psc-model-byte-run (fn-psc-model-comparison-cost c incoming held) c incoming held)
        (fn-psc-model-comparison-complete c incoming held))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-complete fn-psc-model-comparison-cost
                            fn-psc-model-byte-run)
             (nth nfix len fn-psc-step fn-psc-model-demanded-byte)))))
(defun fn-psc-model-line-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (fn-psc-line-rank c) :hints (("Goal" :use ((:instance fn-psc-line-step-productive (byte (fn-psc-model-demanded-byte c incoming held)))) :in-theory (disable fn-psc-step fn-psc-model-demanded-byte fn-psc-line-rank fn-psc-line-statep fn-psc-line-step-productive)))))
 (if (and (fn-psc-line-statep c incoming held) (member-eq (fn-psc-get phase c) '(:line))) (fn-psc-model-line-complete (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held) c))
(defun fn-psc-model-line-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (fn-psc-line-rank c) :hints (("Goal" :use ((:instance fn-psc-line-step-productive (byte (fn-psc-model-demanded-byte c incoming held)))) :in-theory (disable fn-psc-step fn-psc-model-demanded-byte fn-psc-line-rank fn-psc-line-statep fn-psc-line-step-productive)))))
 (if (and (fn-psc-line-statep c incoming held) (member-eq (fn-psc-get phase c) '(:line))) (+ 1 (fn-psc-model-line-cost (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held)) 0))
(local (defthm fn-psc-line-step-phase
 (implies (member-eq (fn-psc-get phase c) '(:line)) (member-eq (fn-psc-get phase (fn-psc-step c byte)) '(:line :control)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-return) (nth update-nth len nfix))))))
(defthm fn-psc-line-complete-preserves-value
 (implies (fn-psc-line-statep c incoming held) (equal (fn-psc-model-line-end (fn-psc-model-line-complete c incoming held) incoming held) (fn-psc-model-line-end c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held) :in-theory (e/d (fn-psc-model-line-complete fn-psc-line-statep) (nth nfix len fn-psc-step fn-psc-model-demanded-byte fn-psc-line-step-preserves-end)))
 ("Subgoal *1/1" :use ((:instance fn-psc-line-step-preserves-end (byte (fn-psc-model-demanded-byte c incoming held)))))))
(defthm fn-psc-line-complete-returns-control
 (implies (and (fn-psc-line-statep c incoming held) (member-eq (fn-psc-get phase c) '(:line :control))) (equal (fn-psc-get phase (fn-psc-model-line-complete c incoming held)) :control))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held) :in-theory (e/d (fn-psc-model-line-complete) (nth nfix len fn-psc-step fn-psc-model-demanded-byte)))))
(defthm fn-psc-line-cost-bounded
 (<= (fn-psc-model-line-cost c incoming held) (fn-psc-line-rank c))
 :hints (("Goal" :induct (fn-psc-model-line-cost c incoming held) :in-theory (e/d (fn-psc-model-line-cost) (nth nfix len fn-psc-step fn-psc-model-demanded-byte fn-psc-line-step-productive)))
 ("Subgoal *1/1" :use ((:instance fn-psc-line-step-productive (byte (fn-psc-model-demanded-byte c incoming held)))))))
(defthm fn-psc-line-complete-is-actual-steps
 (equal (fn-psc-model-byte-run (fn-psc-model-line-cost c incoming held) c incoming held) (fn-psc-model-line-complete c incoming held))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held) :in-theory (e/d (fn-psc-model-line-complete fn-psc-model-line-cost fn-psc-model-byte-run) (nth nfix len fn-psc-step fn-psc-model-demanded-byte)))))
(defun fn-psc-model-param-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (fn-psc-param-rank c) :hints (("Goal" :use ((:instance fn-psc-param-step-productive (byte (fn-psc-model-demanded-byte c incoming held)))) :in-theory (disable fn-psc-step fn-psc-model-demanded-byte fn-psc-param-rank fn-psc-line-statep fn-psc-param-step-productive)))))
 (if (and (fn-psc-line-statep c incoming held) (member-eq (fn-psc-get phase c) '(:params :params-lf))) (fn-psc-model-param-complete (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held) c))
(defun fn-psc-model-param-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (fn-psc-param-rank c) :hints (("Goal" :use ((:instance fn-psc-param-step-productive (byte (fn-psc-model-demanded-byte c incoming held)))) :in-theory (disable fn-psc-step fn-psc-model-demanded-byte fn-psc-param-rank fn-psc-line-statep fn-psc-param-step-productive)))))
 (if (and (fn-psc-line-statep c incoming held) (member-eq (fn-psc-get phase c) '(:params :params-lf))) (+ 1 (fn-psc-model-param-cost (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held)) 0))
(local (defthm fn-psc-param-step-phase
 (implies (member-eq (fn-psc-get phase c) '(:params :params-lf)) (member-eq (fn-psc-get phase (fn-psc-step c byte)) '(:params :params-lf :control)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-return) (nth update-nth len nfix))))))
(defthm fn-psc-param-complete-preserves-value
 (implies (fn-psc-line-statep c incoming held) (equal (fn-psc-model-param-value (fn-psc-model-param-complete c incoming held) incoming held) (fn-psc-model-param-value c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-param-complete c incoming held) :in-theory (e/d (fn-psc-model-param-complete fn-psc-line-statep) (nth nfix len fn-psc-step fn-psc-model-demanded-byte fn-psc-param-step-preserves-value)))
 ("Subgoal *1/1" :use ((:instance fn-psc-param-step-preserves-value (byte (fn-psc-model-demanded-byte c incoming held)))))))
(defthm fn-psc-param-complete-returns-control
 (implies (and (fn-psc-line-statep c incoming held) (member-eq (fn-psc-get phase c) '(:params :params-lf :control))) (equal (fn-psc-get phase (fn-psc-model-param-complete c incoming held)) :control))
 :hints (("Goal" :induct (fn-psc-model-param-complete c incoming held) :in-theory (e/d (fn-psc-model-param-complete) (nth nfix len fn-psc-step fn-psc-model-demanded-byte)))))
(defthm fn-psc-param-cost-bounded
 (<= (fn-psc-model-param-cost c incoming held) (fn-psc-param-rank c))
 :hints (("Goal" :induct (fn-psc-model-param-cost c incoming held) :in-theory (e/d (fn-psc-model-param-cost) (nth nfix len fn-psc-step fn-psc-model-demanded-byte fn-psc-param-step-productive)))
 ("Subgoal *1/1" :use ((:instance fn-psc-param-step-productive (byte (fn-psc-model-demanded-byte c incoming held)))))))
(defthm fn-psc-param-complete-is-actual-steps
 (equal (fn-psc-model-byte-run (fn-psc-model-param-cost c incoming held) c incoming held) (fn-psc-model-param-complete c incoming held))
 :hints (("Goal" :induct (fn-psc-model-param-complete c incoming held) :in-theory (e/d (fn-psc-model-param-complete fn-psc-model-param-cost fn-psc-model-byte-run) (nth nfix len fn-psc-step fn-psc-model-demanded-byte)))))
(local (defthm fn-psc-byte-run-zero-unfolds
 (equal (fn-psc-model-byte-run 0 c incoming held) c)
 :hints (("Goal" :in-theory (enable fn-psc-model-byte-run)))))
(defun fn-psc-model-macro-step (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((phase (fn-psc-get phase c)))
  (cond ((equal phase :done) c)
        ((member-eq phase '(:compare :target))
         (fn-psc-model-comparison-complete c incoming held))
        ((equal phase :line) (fn-psc-model-line-complete c incoming held))
        ((member-eq phase '(:params :params-lf)) (fn-psc-model-param-complete c incoming held))
        (t (fn-psc-step c (fn-psc-model-demanded-byte c incoming held))))))
(defun fn-psc-model-macro-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((phase (fn-psc-get phase c)))
  (cond ((equal phase :done) 0)
        ((member-eq phase '(:compare :target))
         (fn-psc-model-comparison-cost c incoming held))
        ((equal phase :line) (fn-psc-model-line-cost c incoming held))
        ((member-eq phase '(:params :params-lf)) (fn-psc-model-param-cost c incoming held))
        (t 1))))
(defthm fn-psc-macro-step-is-actual-steps
 (equal (fn-psc-model-byte-run (fn-psc-model-macro-cost c incoming held) c incoming held)
        (fn-psc-model-macro-step c incoming held))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-model-macro-step fn-psc-model-macro-cost fn-psc-model-byte-run)
       (nth nfix len fn-psc-step fn-psc-model-demanded-byte
        fn-psc-model-comparison-complete fn-psc-model-comparison-cost
        fn-psc-model-line-complete fn-psc-model-line-cost
        fn-psc-model-param-complete fn-psc-model-param-cost)))))
(local (defthm fn-psc-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))
(defun fn-psc-model-macro-run (fuel c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (equal (fn-psc-get phase c) :done)) c
  (fn-psc-model-macro-run (1- fuel) (fn-psc-model-macro-step c incoming held) incoming held)))
(defun fn-psc-model-macro-charge (fuel c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (equal (fn-psc-get phase c) :done)) 0
  (+ (fn-psc-model-macro-cost c incoming held)
     (fn-psc-model-macro-charge (1- fuel) (fn-psc-model-macro-step c incoming held) incoming held))))
(defthm fn-psc-macro-run-is-actual-steps
 (equal (fn-psc-model-byte-run (fn-psc-model-macro-charge fuel c incoming held) c incoming held)
        (fn-psc-model-macro-run fuel c incoming held))
 :hints (("Goal" :induct (fn-psc-model-macro-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-macro-run fn-psc-model-macro-charge)
             (nth nfix len fn-psc-step fn-psc-model-demanded-byte
              fn-psc-model-byte-run fn-psc-model-macro-step fn-psc-model-macro-cost)))))


; Exact callback summaries for the actual byte-step trace.
(defun fn-psc-model-line-last (line previous)
 (declare (xargs :guard t :verify-guards nil))
 (if (or (atom line) (equal (car line) 10)) previous
  (fn-psc-model-line-last (cdr line) (car line))))

(defun fn-psc-model-line-prev (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-psc-get phase c) :line)
  (fn-psc-model-line-last
   (fn-pb-line (nthcdr (nfix (fn-psc-get pos c)) (fn-psc-model-source c incoming held)))
   (fn-psc-get prev c))
  (fn-psc-get prev c)))

(defun fn-psc-model-line-semi (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (if (and (equal (fn-psc-get phase c) :line)
          (equal (fn-psc-get resume c) :agent-info-line)
          (not (fn-psc-get semi c)))
  (let* ((p (nfix (fn-psc-get pos c)))
         (line (fn-pb-line (nthcdr p (fn-psc-model-source c incoming held))))
         (prefix (fn-pb-upto-semicolon line)))
   (if (equal prefix :no) nil (+ p (len prefix))))
  (fn-psc-get semi c)))

(local (defthm fn-psc-line-source-update-other
 (implies (and (natp slot) (not (equal slot 1)))
  (equal (fn-psc-model-source (update-nth slot value c) incoming held)
         (fn-psc-model-source c incoming held)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-source) (nth update-nth len nfix))))))

(local (defthm fn-psc-line-reference-unfolds
 (implies (and (natp p) (< p (len xs)))
  (equal (fn-pb-line (nthcdr p xs))
         (if (equal (nth p xs) 10) (list 10)
          (cons (nth p xs) (fn-pb-line (nthcdr (+ 1 p) xs))))))
 :hints (("Goal" :induct (nthcdr p xs) :in-theory (enable nthcdr nth fn-pb-line)))))

(local (defthm fn-psc-line-reference-at-end
 (equal (fn-pb-line (nthcdr (len xs) xs)) nil)
 :hints (("Goal" :induct (len xs) :in-theory (enable nthcdr len fn-pb-line)))))

(local (defthm fn-psc-line-field-byte
 (implies (and (equal (fn-psc-get phase c) :line)
               (< (nfix (fn-psc-get pos c)) (nfix (fn-psc-get n c))))
  (equal (fn-psc-model-demanded-byte c incoming held)
         (nth (nfix (fn-psc-get pos c)) (fn-psc-model-source c incoming held))))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-model-demanded-byte fn-psc-demand fn-psc-model-source)
       (nth nfix len))))))

(defthm fn-psc-line-step-preserves-prev
 (implies (and (equal (fn-psc-get phase c) :line)
               (fn-psc-line-statep c incoming held)
               (equal byte (fn-psc-model-demanded-byte c incoming held)))
  (equal (fn-psc-model-line-prev (fn-psc-step c byte) incoming held)
         (fn-psc-model-line-prev c incoming held)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step fn-psc-return fn-psc-model-line-prev
        fn-psc-model-line-last fn-psc-line-statep)
       (nth update-nth nfix len fn-pb-line nthcdr))
  :use ((:instance fn-psc-line-reference-unfolds
          (p (fn-psc-get pos c)) (xs (fn-psc-model-source c incoming held)))))))

(defthm fn-psc-line-step-preserves-first-semicolon
 (implies (and (equal (fn-psc-get phase c) :line)
               (fn-psc-line-statep c incoming held)
               (equal byte (fn-psc-model-demanded-byte c incoming held)))
  (equal (fn-psc-model-line-semi (fn-psc-step c byte) incoming held)
         (fn-psc-model-line-semi c incoming held)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step fn-psc-return fn-psc-model-line-semi
        fn-psc-line-statep fn-pb-upto-semicolon)
       (nth update-nth nfix len fn-pb-line nthcdr))
  :use ((:instance fn-psc-line-reference-unfolds
          (p (fn-psc-get pos c)) (xs (fn-psc-model-source c incoming held)))))))

(defun fn-psc-model-line-ok (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-psc-get phase c) :line)
  (if (member-eq (fn-psc-get resume c) '(:agent-info-line :agent-path-line))
      (if (member-equal 10
        (fn-pb-line (nthcdr (nfix (fn-psc-get pos c))
                            (fn-psc-model-source c incoming held)))) t nil)
   t)
  (if (fn-psc-get ok c) t nil)))

(defthm fn-psc-line-step-preserves-ok
 (implies (and (equal (fn-psc-get phase c) :line)
               (fn-psc-line-statep c incoming held)
               (equal byte (fn-psc-model-demanded-byte c incoming held)))
  (equal (fn-psc-model-line-ok (fn-psc-step c byte) incoming held)
         (fn-psc-model-line-ok c incoming held)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step fn-psc-return fn-psc-model-line-ok
        fn-psc-line-statep member-equal)
       (nth update-nth nfix len fn-pb-line nthcdr))
  :use ((:instance fn-psc-line-reference-unfolds
          (p (fn-psc-get pos c)) (xs (fn-psc-model-source c incoming held)))))))

(in-theory (disable fn-psc-model-line-prev fn-psc-model-line-semi fn-psc-model-line-ok))

(defthm fn-psc-line-complete-preserves-prev
 (implies (fn-psc-line-statep c incoming held)
  (equal (fn-psc-model-line-prev (fn-psc-model-line-complete c incoming held) incoming held) (fn-psc-model-line-prev c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held) :in-theory (e/d (fn-psc-model-line-complete fn-psc-line-statep) (nth nfix len fn-psc-step fn-psc-model-demanded-byte fn-psc-line-step-preserves-prev)))
 ("Subgoal *1/1" :use ((:instance fn-psc-line-step-preserves-prev (byte (fn-psc-model-demanded-byte c incoming held)))))))

(defthm fn-psc-line-complete-preserves-first-semicolon
 (implies (fn-psc-line-statep c incoming held)
  (equal (fn-psc-model-line-semi (fn-psc-model-line-complete c incoming held) incoming held) (fn-psc-model-line-semi c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held) :in-theory (e/d (fn-psc-model-line-complete fn-psc-line-statep) (nth nfix len fn-psc-step fn-psc-model-demanded-byte fn-psc-line-step-preserves-first-semicolon)))
 ("Subgoal *1/1" :use ((:instance fn-psc-line-step-preserves-first-semicolon (byte (fn-psc-model-demanded-byte c incoming held)))))))

(defthm fn-psc-line-complete-preserves-ok
 (implies (fn-psc-line-statep c incoming held)
  (equal (fn-psc-model-line-ok (fn-psc-model-line-complete c incoming held) incoming held) (fn-psc-model-line-ok c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held) :in-theory (e/d (fn-psc-model-line-complete fn-psc-line-statep) (nth nfix len fn-psc-step fn-psc-model-demanded-byte fn-psc-line-step-preserves-ok)))
 ("Subgoal *1/1" :use ((:instance fn-psc-line-step-preserves-ok (byte (fn-psc-model-demanded-byte c incoming held)))))))

(defthm fn-psc-line-complete-exact-prev
 (implies (and (fn-psc-line-statep c incoming held) (equal (fn-psc-get phase c) :line))
  (equal (fn-psc-get prev (fn-psc-model-line-complete c incoming held)) (fn-psc-model-line-prev c incoming held)))
 :hints (("Goal" :use ((:instance fn-psc-line-complete-preserves-prev) (:instance fn-psc-line-complete-returns-control))
 :in-theory (e/d (fn-psc-model-line-prev) (nth nfix len fn-psc-model-line-complete fn-psc-line-complete-preserves-prev fn-psc-line-complete-returns-control)))))

(defthm fn-psc-line-complete-exact-first-semicolon
 (implies (and (fn-psc-line-statep c incoming held) (equal (fn-psc-get phase c) :line))
  (equal (fn-psc-get semi (fn-psc-model-line-complete c incoming held)) (fn-psc-model-line-semi c incoming held)))
 :hints (("Goal" :use ((:instance fn-psc-line-complete-preserves-first-semicolon) (:instance fn-psc-line-complete-returns-control))
 :in-theory (e/d (fn-psc-model-line-semi) (nth nfix len fn-psc-model-line-complete fn-psc-line-complete-preserves-first-semicolon fn-psc-line-complete-returns-control)))))

(defthm fn-psc-line-complete-exact-ok
 (implies (and (fn-psc-line-statep c incoming held) (equal (fn-psc-get phase c) :line))
  (equal (if (fn-psc-get ok (fn-psc-model-line-complete c incoming held)) t nil) (fn-psc-model-line-ok c incoming held)))
 :hints (("Goal" :use ((:instance fn-psc-line-complete-preserves-ok) (:instance fn-psc-line-complete-returns-control))
 :in-theory (e/d (fn-psc-model-line-ok) (nth nfix len fn-psc-model-line-complete fn-psc-line-complete-preserves-ok fn-psc-line-complete-returns-control)))))

(defun fn-psc-model-equivalent (c d)
 (declare (xargs :guard t :verify-guards nil))
 (and
  (equal (fn-psc-get phase c) (fn-psc-get phase d))
  (equal (fn-psc-get mode c) (fn-psc-get mode d))
  (equal (fn-psc-get n c) (fn-psc-get n d))
  (equal (fn-psc-get incoming-n c) (fn-psc-get incoming-n d))
  (equal (fn-psc-get msgid c) (fn-psc-get msgid d))
  (equal (fn-psc-get agent-start c) (fn-psc-get agent-start d))
  (equal (fn-psc-get agent-end c) (fn-psc-get agent-end d))
  (equal (fn-psc-get pos c) (fn-psc-get pos d))
  (equal (fn-psc-get base c) (fn-psc-get base d))
  (equal (fn-psc-get ref c) (fn-psc-get ref d))
  (equal (fn-psc-get ref-start c) (fn-psc-get ref-start d))
  (equal (fn-psc-get ref-len c) (fn-psc-get ref-len d))
  (equal (fn-psc-get resume c) (fn-psc-get resume d))
  (equal (fn-psc-get ok c) (fn-psc-get ok d))
  (equal (fn-psc-get skip c) (fn-psc-get skip d))
  (equal (fn-psc-get date c) (fn-psc-get date d))
  (equal (fn-psc-get k c) (fn-psc-get k d))
  (equal (fn-psc-get has-path c) (fn-psc-get has-path d))
  (equal (fn-psc-get aux c) (fn-psc-get aux d))
  (equal (fn-psc-get prev c) (fn-psc-get prev d))
  (equal (fn-psc-get semi c) (fn-psc-get semi d))
  (equal (fn-psc-get result c) (fn-psc-get result d))
  (implies (member-eq (fn-psc-get phase c) (quote (:compare :target)))
           (equal (fn-psc-get index c) (fn-psc-get index d)))
  (implies (equal (fn-psc-get phase c) :target)
           (equal (fn-psc-get cached c) (fn-psc-get cached d)))))

(local (defthm fn-psc-equivalent-update-visible
 (implies (and (fn-psc-model-equivalent c d) (natp slot)
               (not (member-equal slot (quote (0 12 13)))))
  (fn-psc-model-equivalent (update-nth slot value c) (update-nth slot value d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-equivalent) (nth update-nth nfix len))))))

(local (defthm fn-psc-finish-equivalent
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-finish result c) (fn-psc-finish result d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-finish fn-psc-model-equivalent) (nth update-nth nfix len))))))

(local (defthm fn-psc-compare-equivalent
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-compare pos ref start count resume c) (fn-psc-compare pos ref start count resume d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-compare fn-psc-model-equivalent) (nth update-nth nfix len))))))

(local (defthm fn-psc-literal-equivalent
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-literal pos bytes resume c) (fn-psc-literal pos bytes resume d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-model-equivalent) (nth update-nth nfix len))))))

(local (defthm fn-psc-return-equivalent
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-return ok c) (fn-psc-return ok d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-return fn-psc-model-equivalent) (nth update-nth nfix len))))))

(local (defthm fn-psc-agent-compare-equivalent
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-agent-compare pos resume c) (fn-psc-agent-compare pos resume d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-agent-compare fn-psc-model-equivalent) (nth update-nth nfix len))))))

(local (defthm fn-psc-msgid-compare-equivalent
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-msgid-compare pos resume c) (fn-psc-msgid-compare pos resume d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-msgid-compare fn-psc-model-equivalent) (nth update-nth nfix len))))))

(local (defthm fn-psc-date-compare-equivalent
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-date-compare pos resume c) (fn-psc-date-compare pos resume d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-date-compare fn-psc-model-equivalent) (nth update-nth nfix len))))))

(local (defthm fn-psc-info-compare-equivalent
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-info-compare pos resume c) (fn-psc-info-compare pos resume d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare fn-psc-model-equivalent) (nth update-nth nfix len))))))

(local (defthm fn-psc-control-equivalent
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-control c) (fn-psc-control d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-control fn-psc-model-equivalent) (nth update-nth nfix len))))))

(local (defthm fn-psc-expected-equivalent
 (implies (and (fn-psc-model-equivalent c d)
               (member-eq (fn-psc-get phase c) '(:compare :target)))
  (equal (fn-psc-expected c) (fn-psc-expected d)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-expected fn-psc-model-equivalent) (nth nfix len))))))

(defthm fn-psc-step-preserves-equivalence
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-step c byte) (fn-psc-step d byte)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-model-equivalent) (nth update-nth nfix len)) :use ((:instance fn-psc-expected-equivalent)))))

(defthm fn-psc-equivalent-demands
 (implies (fn-psc-model-equivalent c d) (equal (fn-psc-demand c) (fn-psc-demand d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-demand fn-psc-model-equivalent) (nth nfix len)))))

(defthm fn-psc-equivalent-results
 (implies (fn-psc-model-equivalent c d) (equal (fn-psc-result c) (fn-psc-result d)))
 :hints (("Goal" :in-theory (e/d (fn-psc-result fn-psc-model-equivalent) (nth nfix len)))))

(in-theory (disable fn-psc-model-equivalent))

(local (defthm fn-psc-equivalent-demanded-bytes
 (implies (fn-psc-model-equivalent c d)
  (equal (fn-psc-model-demanded-byte c incoming held)
         (fn-psc-model-demanded-byte d incoming held)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-psc-equivalent-demands))
          :in-theory (e/d (fn-psc-model-demanded-byte)
             (fn-psc-demand fn-psc-model-equivalent nth nfix len))))))

(local (defun fn-psc-paired-byte-induct (fuel c d incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (list c d incoming held)
  (fn-psc-paired-byte-induct (1- fuel)
   (fn-psc-step c (fn-psc-model-demanded-byte c incoming held))
   (fn-psc-step d (fn-psc-model-demanded-byte d incoming held)) incoming held))))

(defthm fn-psc-byte-run-preserves-equivalence
 (implies (fn-psc-model-equivalent c d)
  (fn-psc-model-equivalent (fn-psc-model-byte-run fuel c incoming held)
                           (fn-psc-model-byte-run fuel d incoming held)))
 :hints (("Goal" :induct (fn-psc-paired-byte-induct fuel c d incoming held)
          :in-theory (e/d (fn-psc-paired-byte-induct fn-psc-model-byte-run)
             (nth nfix len fn-psc-step fn-psc-model-demanded-byte fn-psc-model-equivalent)))
          ("Subgoal *1/2" :use ((:instance fn-psc-equivalent-demanded-bytes)))))

(defthm fn-psc-equivalent-byte-run-results
 (implies (fn-psc-model-equivalent c d)
  (equal (fn-psc-result (fn-psc-model-byte-run fuel c incoming held))
         (fn-psc-result (fn-psc-model-byte-run fuel d incoming held))))
 :hints (("Goal" :use ((:instance fn-psc-byte-run-preserves-equivalence)
                       (:instance fn-psc-equivalent-results
                         (c (fn-psc-model-byte-run fuel c incoming held))
                         (d (fn-psc-model-byte-run fuel d incoming held))))
          :in-theory (disable fn-psc-byte-run-preserves-equivalence fn-psc-equivalent-results
             fn-psc-model-equivalent fn-psc-model-byte-run fn-psc-result))))

(defun fn-psc-failed-direct-resumep (r)
 (declare (xargs :guard t :verify-guards nil))
 (if (member-eq r
 '(:start :skip-lock :skip-key :agent-path-field :agent-path-tail :agent-stamp
   :agent-msgid :agent-date :agent-info-field :agent-info-line :agent-params
   :source-path-field :source-path-agent :source-path-tail :source-stamp
   :source-stamp-tail :source-info-simple :source-info-v1 :source-v1-msgid
   :source-v1-date :source-optional-msgid :source-optional-date
   :unsplice-field :unsplice-agent :unsplice-tail)) t nil))

(defthm fn-psc-failed-control-position-normalizes
 (implies (and (equal (fn-psc-get phase c) :control)
               (not (fn-psc-get ok c))
               (fn-psc-failed-direct-resumep (fn-psc-get resume c)))
  (let ((a (fn-psc-step c byte))
        (b (fn-psc-step (fn-psc-set pos position c) byte)))
   (or (fn-psc-model-equivalent a b)
       (and (equal (fn-psc-get phase a) :done) (equal (fn-psc-get phase b) :done)
            (equal (fn-psc-result a) (fn-psc-result b))))))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step fn-psc-control fn-psc-failed-direct-resumep
        fn-psc-model-equivalent fn-psc-result fn-psc-finish fn-psc-compare
        fn-psc-literal fn-psc-return fn-psc-agent-compare fn-psc-msgid-compare
        fn-psc-date-compare fn-psc-info-compare)
       (nth update-nth nfix len)))))

(local (defthm fn-psc-control-demanded-byte-is-none
 (implies (equal (fn-psc-get phase c) :control)
  (equal (fn-psc-model-demanded-byte c incoming held) nil))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-model-demanded-byte fn-psc-demand) (nth nfix len))))))

(local (defthm fn-psc-done-byte-run-stays-done
 (implies (equal (fn-psc-get phase c) :done)
  (equal (fn-psc-model-byte-run fuel c incoming held) c))
 :hints (("Goal" :induct (fn-psc-model-byte-run fuel c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run fn-psc-step)
             (nth nfix len update-nth fn-psc-model-demanded-byte))))))

(defthm fn-psc-failed-control-position-preserves-future-result
 (implies (and (equal (fn-psc-get phase c) :control)
               (not (fn-psc-get ok c))
               (fn-psc-failed-direct-resumep (fn-psc-get resume c)))
  (equal (fn-psc-result (fn-psc-model-byte-run fuel c incoming held))
         (fn-psc-result (fn-psc-model-byte-run fuel (fn-psc-set pos position c) incoming held))))
 :rule-classes nil
 :hints (("Goal" :cases ((zp fuel))
          :use ((:instance fn-psc-failed-control-position-normalizes (byte nil))
                (:instance fn-psc-equivalent-byte-run-results
                  (c (fn-psc-step c nil))
                  (d (fn-psc-step (fn-psc-set pos position c) nil))
                  (fuel (1- fuel))))
          :expand ((fn-psc-model-byte-run fuel c incoming held)
                   (fn-psc-model-byte-run fuel (fn-psc-set pos position c) incoming held))
          :do-not-induct t
          :in-theory (e/d (fn-psc-result)
             (fn-psc-model-byte-run fn-psc-equivalent-results nth nfix len update-nth fn-psc-step fn-psc-model-demanded-byte
              fn-psc-failed-direct-resumep fn-psc-model-equivalent
              fn-psc-failed-control-position-normalizes fn-psc-equivalent-byte-run-results)))))

(defthm fn-psc-failed-pair-preserves-future-result
 (implies (and (equal (fn-psc-get phase c) :control)
               (not (fn-psc-get ok c))
               (fn-psc-failed-direct-resumep (fn-psc-get resume c))
               (fn-psc-model-equivalent (fn-psc-set pos 0 c) (fn-psc-set pos 0 d)))
  (equal (fn-psc-result (fn-psc-model-byte-run fuel c incoming held))
         (fn-psc-result (fn-psc-model-byte-run fuel d incoming held))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-psc-failed-control-position-preserves-future-result (position 0))
                       (:instance fn-psc-failed-control-position-preserves-future-result (c d) (position 0))
                       (:instance fn-psc-equivalent-byte-run-results
                         (c (fn-psc-set pos 0 c)) (d (fn-psc-set pos 0 d))))
          :in-theory (e/d (fn-psc-model-equivalent)
             (nth nfix len update-nth fn-psc-model-byte-run fn-psc-result
              fn-psc-failed-direct-resumep
               fn-psc-equivalent-byte-run-results)))))

(defun fn-psc-failed-wrapper-resumep (r)
 (declare (xargs :guard t :verify-guards nil))
 (if (member-eq r '(:msgid-field :msgid-content :msgid-tail :date-field :date-content :date-tail
                    :info-field :info-agent :info-tail)) t nil))

(local (defthm fn-psc-failed-wrapper-next-pair
 (implies (and (equal (fn-psc-get phase c) :control)
               (not (fn-psc-get ok c))
               (fn-psc-failed-wrapper-resumep (fn-psc-get resume c))
               (fn-psc-failed-direct-resumep (fn-psc-get aux c)))
  (let ((a (fn-psc-step c byte))
        (b (fn-psc-step (fn-psc-set pos position c) byte)))
   (and (equal (fn-psc-get phase a) :control) (not (fn-psc-get ok a))
        (fn-psc-failed-direct-resumep (fn-psc-get resume a))
        (fn-psc-model-equivalent (fn-psc-set pos 0 a) (fn-psc-set pos 0 b)))))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step fn-psc-control fn-psc-failed-wrapper-resumep
        fn-psc-model-equivalent fn-psc-return)
       (nth update-nth nfix len fn-psc-failed-direct-resumep))))))

(defthm fn-psc-failed-wrapper-position-preserves-future-result
 (implies (and (equal (fn-psc-get phase c) :control)
               (not (fn-psc-get ok c))
               (fn-psc-failed-wrapper-resumep (fn-psc-get resume c))
               (fn-psc-failed-direct-resumep (fn-psc-get aux c)))
  (equal (fn-psc-result (fn-psc-model-byte-run fuel c incoming held))
         (fn-psc-result (fn-psc-model-byte-run fuel (fn-psc-set pos position c) incoming held))))
 :rule-classes nil
 :hints (("Goal" :cases ((zp fuel))
          :use ((:instance fn-psc-failed-wrapper-next-pair (byte nil))
                (:instance fn-psc-failed-pair-preserves-future-result
                  (c (fn-psc-step c nil))
                  (d (fn-psc-step (fn-psc-set pos position c) nil))
                  (fuel (1- fuel))))
          :expand ((fn-psc-model-byte-run fuel c incoming held)
                   (fn-psc-model-byte-run fuel (fn-psc-set pos position c) incoming held))
          :do-not-induct t
          :in-theory (e/d (fn-psc-result)
             (fn-psc-model-byte-run fn-psc-equivalent-results nth nfix len update-nth
              fn-psc-step fn-psc-model-demanded-byte fn-psc-failed-wrapper-resumep
              fn-psc-failed-direct-resumep fn-psc-model-equivalent
              fn-psc-failed-wrapper-next-pair 
              
              fn-psc-failed-control-position-normalizes)))))


(defthm fn-psc-comparison-complete-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 12 13 15))))
  (equal (nth slot (fn-psc-model-comparison-complete c incoming held))
         (nth slot c)))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-complete fn-psc-step fn-psc-return)
                         (nth update-nth len fn-psc-model-demanded-byte fn-psc-expected)))))
(defthm fn-psc-comparison-complete-callback-shape
 (implies (and (fn-psc-comparison-statep c)
               (member-eq (fn-psc-get phase c) '(:compare :target)))
  (let ((done (fn-psc-model-comparison-complete c incoming held)))
   (fn-psc-model-equivalent done
    (fn-psc-return (fn-psc-get ok done) (fn-psc-set pos (fn-psc-get pos done) c)))))
 :hints (("Goal" :use ((:instance fn-psc-comparison-complete-returns-control))
          :in-theory (e/d (fn-psc-model-equivalent fn-psc-return)
            (fn-psc-model-comparison-complete fn-psc-comparison-statep nth nfix len update-nth)))))

(local (defthm fn-psc-comparison-step-output-branch
 (implies (member-eq (fn-psc-get phase c) '(:compare :target))
  (let ((d (fn-psc-step c byte)))
   (or (member-eq (fn-psc-get phase d) '(:compare :target))
       (and (equal (fn-psc-get phase d) :control) (booleanp (fn-psc-get ok d))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-return) (nth update-nth len fn-psc-expected))))))

(defthm fn-psc-comparison-complete-ok-boolean
 (implies (and (fn-psc-comparison-statep c)
               (member-eq (fn-psc-get phase c) '(:compare :target)))
  (booleanp (fn-psc-get ok (fn-psc-model-comparison-complete c incoming held))))
 :hints (("Goal" :induct (fn-psc-model-comparison-complete c incoming held)
          :in-theory (e/d (fn-psc-model-comparison-complete)
                         (nth update-nth len fn-psc-step fn-psc-model-demanded-byte fn-psc-expected)))
         ("Subgoal *1/2" :use ((:instance fn-psc-step-preserves-comparison-state (byte (fn-psc-model-demanded-byte c incoming held)))
                               (:instance fn-psc-comparison-step-output-branch (byte (fn-psc-model-demanded-byte c incoming held)))))
         ("Subgoal *1/1" :use ((:instance fn-psc-step-preserves-comparison-state (byte (fn-psc-model-demanded-byte c incoming held)))
                               (:instance fn-psc-comparison-step-output-branch (byte (fn-psc-model-demanded-byte c incoming held)))))))

(local (defthm fn-psc-cdr-update-positive
 (implies (posp i)
  (equal (cdr (update-nth i value c)) (update-nth (1- i) value (cdr c))))
 :hints (("Goal" :expand ((update-nth i value c)) :in-theory (enable posp nfix)))))

(local (defthm fn-psc-return-position-overwrites
 (equal (fn-psc-set pos p (fn-psc-return ok (fn-psc-set pos q c)))
        (fn-psc-return ok (fn-psc-set pos p c)))
 :hints (("Goal" :expand ((:free (i value c) (update-nth i value c))) :in-theory (enable fn-psc-return update-nth)))))

(defun fn-psc-model-comparison-callback (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((ok (fn-psc-model-compare-value c incoming held)))
  (fn-psc-return ok
   (fn-psc-set pos (if ok (+ (fn-psc-get base c) (fn-psc-get ref-len c))
                         (fn-psc-get pos c)) c))))

(defthm fn-psc-comparison-complete-canonical-future-result
 (implies (and (fn-psc-comparison-statep c) (fn-psc-comparison-positionp c)
               (member-eq (fn-psc-get phase c) '(:compare :target))
               (fn-psc-failed-direct-resumep (fn-psc-get resume c)))
  (equal (fn-psc-result (fn-psc-model-byte-run fuel
           (fn-psc-model-comparison-complete c incoming held) incoming held))
         (fn-psc-result (fn-psc-model-byte-run fuel
           (fn-psc-model-comparison-callback c incoming held) incoming held))))
 :rule-classes nil
 :hints (("Goal"
  :cases ((fn-psc-get ok (fn-psc-model-comparison-complete c incoming held)))
  :use ((:instance fn-psc-return-position-overwrites (p (fn-psc-get pos c)) (q (fn-psc-get pos (fn-psc-model-comparison-complete c incoming held))) (ok nil))
        (:instance fn-psc-comparison-complete-callback-shape)
        (:instance fn-psc-comparison-complete-ok-boolean)
        (:instance fn-psc-comparison-complete-exact-flag)
        (:instance fn-psc-comparison-complete-exact-position)
        (:instance fn-psc-equivalent-byte-run-results
          (c (fn-psc-model-comparison-complete c incoming held))
          (d (fn-psc-return
               (fn-psc-get ok (fn-psc-model-comparison-complete c incoming held))
               (fn-psc-set pos (fn-psc-get pos (fn-psc-model-comparison-complete c incoming held)) c))))
        (:instance fn-psc-failed-control-position-preserves-future-result
          (c (fn-psc-return nil
               (fn-psc-set pos (fn-psc-get pos (fn-psc-model-comparison-complete c incoming held)) c)))
          (position (fn-psc-get pos c))))
  :do-not-induct t
  :in-theory (e/d (booleanp fn-psc-model-comparison-callback fn-psc-return)
    (fn-psc-model-byte-run fn-psc-model-comparison-complete fn-psc-result
     fn-psc-model-equivalent fn-psc-model-compare-value fn-psc-comparison-statep
     fn-psc-comparison-positionp fn-psc-failed-direct-resumep nth len nfix update-nth
     fn-psc-comparison-complete-ok-boolean
     fn-psc-equivalent-byte-run-results fn-psc-comparison-complete-callback-shape
     fn-psc-comparison-complete-exact-flag fn-psc-comparison-complete-exact-position)))))

(defthm fn-psc-literal-reference-byte
 (implies (true-listp bytes)
 (equal (fn-psc-model-reference-byte (fn-psc-literal pos bytes resume c) index incoming held)
        (nth (nfix index) bytes)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-reference-byte fn-psc-literal fn-psc-compare)
                         (nth update-nth len nfix fn-psc-model-source)))))

(defthm fn-psc-literal-reference-octets
 (implies (and (true-listp bytes) (natp count) (natp index)
               (<= (+ count index) (len bytes)))
  (equal (fn-psc-model-reference-octets count index
           (fn-psc-literal pos bytes resume c) incoming held)
         (fn-inj-take count (nthcdr index bytes))))
 :hints (("Goal" :induct (fn-psc-model-reference-octets count index
                          (fn-psc-literal pos bytes resume c) incoming held)
          :in-theory (e/d (fn-psc-model-reference-octets fn-inj-take nfix)
             (fn-psc-literal fn-psc-compare fn-psc-model-reference-byte nth nthcdr len)))))

(local (defthm fn-psc-take-full-list
 (implies (true-listp xs) (equal (fn-inj-take (len xs) xs) xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable fn-inj-take len true-listp)))))

(defthm fn-psc-literal-comparison-is-actual-strip
 (implies (and (true-listp bytes) (natp pos)
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-compare-value (fn-psc-literal pos bytes resume c) incoming held)
         (not (equal (fn-inj-strip bytes (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
 :hints (("Goal"
  :use ((:instance fn-psc-literal-reference-octets (count (len bytes)) (index 0))
        (:instance fn-psc-take-full-list (xs bytes))
        (:instance fn-psc-prefix-is-actual-strip
          (c (fn-psc-literal pos bytes resume c)) (remaining (len bytes)) (index 0)))
  :expand ((nthcdr 0 bytes)) :do-not-induct t
  :in-theory (e/d (fn-psc-model-compare-value fn-psc-literal fn-psc-compare fn-psc-model-source nfix)
    (nth nthcdr len fn-psc-model-prefix fn-psc-model-reference-octets fn-inj-strip fn-psc-prefix-is-actual-strip)))))

(local (defthm fn-psc-inj-drop-is-nthcdr
 (implies (true-listp xs) (equal (fn-inj-drop k xs) (nthcdr (nfix k) xs)))
 :hints (("Goal" :induct (fn-inj-drop k xs) :in-theory (enable fn-inj-drop nthcdr nfix true-listp)))))

(local (defthm fn-psc-take-drop-reconstruct
 (implies (true-listp xs)
  (equal (append (fn-inj-take k xs) (fn-inj-drop k xs)) xs))
 :hints (("Goal" :induct (fn-inj-take k xs) :in-theory (enable fn-inj-take fn-inj-drop append true-listp)))))

(local (defthm fn-psc-line-of-prefixed-source
 (implies (and (true-listp prefix) (not (member-equal 10 prefix)))
  (equal (fn-pb-line (append prefix xs)) (append prefix (fn-pb-line xs))))
 :hints (("Goal" :induct (len prefix) :in-theory (enable fn-pb-line append len true-listp member-equal)))))

(local (defthm fn-psc-strip-prefixed-source
 (implies (true-listp prefix)
  (equal (fn-inj-strip prefix (append prefix xs)) xs))
 :hints (("Goal" :induct (len prefix) :in-theory (enable fn-inj-strip append len true-listp)))))

(local (defthm fn-psc-param-rest-first-line
 (implies (true-listp xs)
 (equal (fn-inj-param-rest (fn-pb-line xs))
        (if (equal (fn-inj-param-rest xs) :no) :no nil)))
 :hints (("Goal" :induct (fn-inj-param-rest xs)
                 :in-theory (enable fn-inj-param-rest fn-pb-line true-listp)))))

(local (defthm fn-psc-semicolon-of-prefix
 (implies (and (true-listp prefix) (not (member-equal 59 prefix))
               (consp tail) (equal (car tail) 59))
  (equal (fn-pb-upto-semicolon (append prefix tail)) prefix))
 :hints (("Goal" :induct (len prefix)
                 :in-theory (enable fn-pb-upto-semicolon append len true-listp member-equal)))))

(local (defthm fn-psc-line-start
 (and (equal (car (fn-pb-line xs)) (car xs))
      (equal (consp (fn-pb-line xs)) (consp xs)))
 :hints (("Goal" :expand ((fn-pb-line xs))))))

(local (defthm fn-psc-inj-append-is-append
 (equal (fn-inj-append xs ys) (append xs ys))
 :hints (("Goal" :induct (len xs) :in-theory (enable fn-inj-append append len)))))

(local (defthm fn-psc-strip-shared-prefix
 (implies (true-listp prefix)
  (equal (fn-inj-strip (append prefix a) (append prefix b)) (fn-inj-strip a b)))
 :hints (("Goal" :induct (len prefix) :in-theory (enable fn-inj-strip append len true-listp)))))

(defthm fn-psc-reference-parameter-agent
 (implies (and (consp agent) (true-listp agent)
               (not (member-equal 10 agent)) (not (member-equal 59 agent))
               (true-listp params) (consp params) (equal (car params) 59))
  (equal (fn-pb-params-line-agent
           (fn-pb-line (append *fn-inj-injection-info-field* (append agent params))))
         (if (equal (fn-inj-param-rest params) :no) nil agent)))
 :hints (("Goal" :do-not-induct t :expand ((fn-inj-strip (quote (13 10)) (fn-pb-line params)))
  :in-theory (e/d (fn-pb-params-line-agent fn-inj-strip-info fn-inj-injection-info-line)
            (fn-pb-line fn-pb-upto-semicolon fn-inj-strip fn-inj-param-rest append)))))

(defthm fn-psc-param-complete-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 15))))
  (equal (nth slot (fn-psc-model-param-complete c incoming held)) (nth slot c)))
 :hints (("Goal" :induct (fn-psc-model-param-complete c incoming held)
          :in-theory (e/d (fn-psc-model-param-complete fn-psc-step fn-psc-return)
                         (nth update-nth len fn-psc-model-demanded-byte fn-psc-expected)))))

(local (defthm fn-psc-proper-tail-not-sentinel
 (implies (true-listp xs) (not (equal (nthcdr p xs) :no)))
 :hints (("Goal" :induct (nthcdr p xs) :in-theory (enable nthcdr true-listp)))))

(defthm fn-psc-param-complete-exact-flag
 (implies (and (equal (fn-psc-get phase c) :params)
               (fn-psc-line-statep c incoming held)
               (true-listp (fn-psc-model-source c incoming held)))
  (equal (if (fn-psc-get ok (fn-psc-model-param-complete c incoming held)) t nil)
         (not (equal (fn-inj-param-rest
                       (nthcdr (fn-psc-get pos c) (fn-psc-model-source c incoming held))) :no))))
 :hints (("Goal" :use ((:instance fn-psc-param-complete-preserves-value)
                       (:instance fn-psc-param-complete-returns-control))
          :in-theory (e/d (fn-psc-model-param-value fn-psc-model-source fn-psc-line-statep nfix)
            (fn-psc-model-param-complete fn-psc-param-complete-preserves-value
             fn-psc-param-complete-returns-control nth nthcdr len fn-inj-param-rest)))))

(defthm fn-psc-agent-parameter-result
 (implies (and (equal (fn-psc-get phase c) :params)
               (equal (fn-psc-get resume c) :agent-params)
               (fn-psc-line-statep c incoming held)
               (true-listp (fn-psc-model-source c incoming held)))
  (let ((done (fn-psc-step (fn-psc-model-param-complete c incoming held) nil)))
   (and (equal (fn-psc-get phase done) :done)
        (equal (fn-psc-result done)
         (if (equal (fn-inj-param-rest (nthcdr (fn-psc-get pos c)
                         (fn-psc-model-source c incoming held))) :no)
             :no-source
           (list :agent (fn-psc-get agent-start c) (fn-psc-get agent-end c)))))))
 :hints (("Goal" :use ((:instance fn-psc-param-complete-exact-flag)
                       (:instance fn-psc-param-complete-returns-control))
  :in-theory (e/d (fn-psc-step fn-psc-control fn-psc-finish fn-psc-result)
    (fn-psc-model-param-complete fn-psc-model-source fn-psc-line-statep
     fn-psc-param-complete-exact-flag fn-psc-param-complete-returns-control
     fn-inj-param-rest nth nthcdr len update-nth nfix)))))

(defthm fn-psc-source-byte-run-preserves-incoming-agent
 (implies (fn-psc-source-resumep c)
  (let ((done (fn-psc-model-byte-run fuel c incoming held)))
   (and (fn-psc-source-resumep done)
        (equal (fn-psc-get agent-start done) (fn-psc-get agent-start c))
        (equal (fn-psc-get agent-end done) (fn-psc-get agent-end c)))))
 :hints (("Goal" :induct (fn-psc-model-byte-run fuel c incoming held)
                 :in-theory (e/d (fn-psc-model-byte-run)
                   (fn-psc-source-resumep fn-psc-step fn-psc-model-demanded-byte nth len nfix)))))

(defthm fn-psc-source-begin-byte-run-keeps-supplied-agent
 (implies (member-eq mode '(:source-incoming :source-held))
  (let ((done (fn-psc-model-byte-run fuel
                (fn-psc-begin mode n msgid agent-span incoming-n) incoming held)))
   (and (equal (fn-psc-get agent-start done) (nfix (cadr agent-span)))
        (equal (fn-psc-get agent-end done) (nfix (caddr agent-span))))))
 :hints (("Goal" :use ((:instance fn-psc-begin-establishes-source-resumes)
                       (:instance fn-psc-source-byte-run-preserves-incoming-agent
                        (c (fn-psc-begin mode n msgid agent-span incoming-n))))
                 :in-theory (e/d (fn-psc-begin fn-psc-finish)
                   (fn-psc-source-resumep fn-psc-model-byte-run fn-psc-step
                    fn-psc-begin-establishes-source-resumes fn-psc-source-byte-run-preserves-incoming-agent nth len nfix update-nth)))))

; V3 Path discovery: exact existing parser result over actual paid steps.
; The logical completion/rank functions are proof-only; the served subject
; remains fn-psc-step, with one demanded byte or bounded control per call.

(defthm fn-psc-path-field-comparison-is-current-buffer-parser
 (implies (and (natp p) (true-listp (fn-psc-model-source c incoming held))
               (<= p (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-compare-value (fn-psc-compare p :path 0 6 :unsplice-field c) incoming held)
         (fn-pbb-path-openp p (fn-psc-model-source c incoming held))))
 :hints (("Goal" :use ((:instance fn-pbb-path-openp-is-inj-path-openp
                       (i p) (fn-octets (fn-psc-model-source c incoming held))))
  :expand ((:free (pos c) (fn-psc-model-prefix 0 6 pos c incoming held))
           (:free (pos c) (fn-psc-model-prefix 1 5 pos c incoming held))
           (:free (pos c) (fn-psc-model-prefix 2 4 pos c incoming held))
           (:free (pos c) (fn-psc-model-prefix 3 3 pos c incoming held))
           (:free (pos c) (fn-psc-model-prefix 4 2 pos c incoming held))
           (:free (pos c) (fn-psc-model-prefix 5 1 pos c incoming held))
           (:free (pos c) (fn-psc-model-prefix 6 0 pos c incoming held))
           (:free (x) (fn-inj-take-n 0 x))
           (:free (x) (fn-inj-take-n 1 x))
           (:free (x) (fn-inj-take-n 2 x))
           (:free (x) (fn-inj-take-n 3 x))
           (:free (x) (fn-inj-take-n 4 x))
           (:free (x) (fn-inj-take-n 5 x))
           (:free (x) (fn-inj-take-n 6 x))
           (:free (a) (fn-inj-downcase (list a)))
           (:free (a b) (fn-inj-downcase (list a b)))
           (:free (a b c) (fn-inj-downcase (list a b c)))
           (:free (a b c d) (fn-inj-downcase (list a b c d))))
  :in-theory (e/d (fn-psc-model-compare-value fn-psc-compare fn-psc-model-prefix
                   fn-psc-model-reference-byte fn-psc-model-target-byte fn-psc-model-source
                   fn-inj-path-openp fn-inj-take-n fn-inj-downcase nfix)
   (fn-pbb-path-openp fn-pbb-path-openp-is-inj-path-openp nth nthcdr len update-nth)))))

(defun fn-psc-model-reference-path-index (p bol xs)
 (declare (xargs :guard t :verify-guards nil))
 (let ((offset (fn-inj-path-scan (nthcdr p xs) bol)))
  (if offset (+ p offset) nil)))
(defthm fn-psc-reference-path-index-is-current-buffer-parser
 (implies (and (natp p) (<= p (len xs)) (true-listp xs))
  (equal (fn-psc-model-reference-path-index p bol xs) (fn-pbb-path-scan p bol xs)))
 :hints (("Goal" :use ((:instance fn-pbb-path-scan-is-inj-path-scan (i p) (fn-octets xs))
                       (:instance fn-pbb-path-scan-bounds (i p) (fn-octets xs)))
  :in-theory (e/d (fn-psc-model-reference-path-index)
                 (fn-inj-path-scan fn-pbb-path-scan fn-pbb-path-scan-is-inj-path-scan
                  fn-pbb-path-scan-bounds nthcdr len)))))
(defun fn-psc-model-path-skip-index (p bol xs)
 (declare (xargs :guard t :verify-guards nil))
 (cond ((>= p (len xs)) nil)
       ((and bol (equal (nth p xs) 13)) nil)
       ((and (equal (nth p xs) 13) (< (+ p 1) (len xs)) (equal (nth (+ p 1) xs) 10))
        (fn-psc-model-reference-path-index (+ p 2) t xs))
       (t (fn-psc-model-reference-path-index (+ p 1) nil xs))))
(defun fn-psc-model-path-finder-value (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let ((p (fn-psc-get pos c)) (base (fn-psc-get base c))
       (xs (fn-psc-model-source c incoming held))
       (bol (equal (fn-psc-get prev c) :bol)))
  (case (fn-psc-get phase c)
   (:path-scan (if (fn-psc-get aux c)
                   (fn-psc-model-reference-path-index p t xs)
                 (fn-psc-model-path-skip-index p bol xs)))
   (:path-cr (if (and (< p (len xs)) (equal (nth p xs) 10))
                  (fn-psc-model-reference-path-index (+ p 1) t xs)
                (fn-psc-model-reference-path-index p nil xs)))
   (:compare (if (fn-psc-model-compare-value c incoming held) (+ base 6)
               (fn-psc-model-path-skip-index base bol xs)))
   (:control (if (fn-psc-get ok c) (+ base 6)
               (fn-psc-model-path-skip-index base bol xs)))
   (otherwise nil))))
(defun fn-psc-path-finder-statep (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-psc-line-statep c incoming held)
      (true-listp (fn-psc-model-source c incoming held))
      (member-eq (fn-psc-get prev c) '(nil :bol))
      (case (fn-psc-get phase c)
       (:path-scan (and (member-eq (fn-psc-get resume c) '(:source-found :unsplice-field))
                       (implies (fn-psc-get aux c) (equal (fn-psc-get prev c) :bol))))
       (:path-cr (and (< 0 (fn-psc-get pos c)) (member-eq (fn-psc-get resume c) '(:source-found :unsplice-field))
                     (not (fn-psc-get aux c)) (equal (fn-psc-get prev c) nil)))
       ((:compare :control)
        (and (equal (fn-psc-get resume c) :unsplice-field)
             (equal (fn-psc-get ref c) :path) (equal (fn-psc-get ref-start c) 0)
             (equal (fn-psc-get ref-len c) 6)
             (natp (fn-psc-get base c)) (<= (fn-psc-get base c) (fn-psc-get pos c))
             (natp (fn-psc-get index c)) (<= (fn-psc-get index c) 6)
             (if (equal (fn-psc-get phase c) :compare)
                 (equal (fn-psc-get pos c) (+ (fn-psc-get base c) (fn-psc-get index c)))
               (implies (fn-psc-get ok c)
                        (equal (fn-psc-get pos c) (+ (fn-psc-get base c) 6))))))
       (:done (equal (fn-psc-get result c) :no-source))
       (otherwise nil))))
(in-theory (disable fn-psc-model-reference-path-index fn-psc-model-path-skip-index
                    fn-psc-model-path-finder-value fn-psc-path-finder-statep))

(defthm fn-psc-reference-path-index-unfolds
 (implies (and (natp p) (<= p (len xs)) (true-listp xs))
  (equal (fn-psc-model-reference-path-index p bol xs)
   (if (>= p (len xs)) nil
    (if (and bol (fn-pbb-path-openp p xs)) (+ p 6)
     (fn-psc-model-path-skip-index p bol xs)))))
 :hints (("Goal" :do-not-induct t
  :expand ((fn-pbb-path-scan p bol xs))
  :in-theory (e/d (fn-psc-model-path-skip-index fn-octets-len fn-octets-get)
   (fn-pbb-path-scan fn-pbb-path-openp fn-psc-model-reference-path-index nthcdr len)))))

(defthm fn-psc-control-compare-value-unfolds
 (implies (equal (fn-psc-get phase c) :control)
  (equal (fn-psc-model-compare-value c incoming held) (if (fn-psc-get ok c) t nil)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-compare-value) (nth nfix)))))

(defthm fn-psc-path-comparison-step-preserves-value
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (equal (fn-psc-get phase c) :compare)
               (equal byte (fn-psc-model-demanded-byte c incoming held)))
  (equal (fn-psc-model-path-finder-value (fn-psc-step c byte) incoming held)
         (fn-psc-model-path-finder-value c incoming held)))
 :hints (("Goal" :use fn-psc-compare-step-preserves-prefix
  :in-theory (e/d (fn-psc-path-finder-statep fn-psc-line-statep
                   fn-psc-model-path-finder-value fn-psc-step fn-psc-return
                   fn-psc-model-source nfix)
   (fn-psc-model-compare-value fn-psc-compare-step-preserves-prefix
    fn-psc-model-path-skip-index nth update-nth len)))))

(defthm fn-psc-path-launch-step-preserves-value
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (equal (fn-psc-get phase c) :path-scan)
               (fn-psc-get aux c))
  (equal (fn-psc-model-path-finder-value (fn-psc-step c byte) incoming held)
         (fn-psc-model-path-finder-value c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-path-field-comparison-is-current-buffer-parser
           (p (fn-psc-get pos c))))
  :in-theory (e/d (fn-psc-path-finder-statep fn-psc-line-statep
                   fn-psc-model-path-finder-value fn-psc-step fn-psc-compare
                   fn-psc-finish fn-psc-model-source nfix)
   (fn-psc-model-compare-value fn-pbb-path-openp fn-psc-model-path-skip-index
    fn-psc-path-field-comparison-is-current-buffer-parser
    fn-pbb-path-scan nth update-nth len)))))

(defthm fn-psc-path-byte-step-preserves-value
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (member-eq (fn-psc-get phase c) '(:path-scan :path-cr))
               (not (and (equal (fn-psc-get phase c) :path-scan) (fn-psc-get aux c)))
               (equal byte (fn-psc-model-demanded-byte c incoming held)))
  (equal (fn-psc-model-path-finder-value (fn-psc-step c byte) incoming held)
         (fn-psc-model-path-finder-value c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-reference-path-index-unfolds
           (p (fn-psc-get pos c)) (bol nil)
           (xs (fn-psc-model-source c incoming held)))
         (:instance fn-psc-reference-path-index-unfolds
           (p (+ 1 (fn-psc-get pos c))) (bol nil)
           (xs (fn-psc-model-source c incoming held))))
  :in-theory (e/d (fn-psc-path-finder-statep fn-psc-line-statep
                   fn-psc-model-path-finder-value fn-psc-model-path-skip-index
                   fn-psc-model-demanded-byte fn-psc-demand
                   fn-psc-step fn-psc-finish fn-psc-model-source nfix)
   (fn-psc-model-compare-value fn-pbb-path-openp
    fn-psc-reference-path-index-unfolds fn-pbb-path-scan nth update-nth len)))))

(defthm fn-psc-path-failed-control-preserves-value
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (equal (fn-psc-get phase c) :control) (not (fn-psc-get ok c)))
  (equal (fn-psc-model-path-finder-value (fn-psc-step c byte) incoming held)
         (fn-psc-model-path-finder-value c incoming held)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-path-finder-statep fn-psc-line-statep fn-psc-model-path-finder-value
        fn-psc-step fn-psc-control fn-psc-model-source nfix)
       (fn-psc-model-path-skip-index nth update-nth len)))))

(defthm fn-psc-path-finder-step-preserves-state
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (not (and (equal (fn-psc-get phase c) :control) (fn-psc-get ok c))))
  (fn-psc-path-finder-statep (fn-psc-step c byte) incoming held))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-path-finder-statep fn-psc-line-statep fn-psc-step fn-psc-control
        fn-psc-compare fn-psc-return fn-psc-finish fn-psc-model-source nfix)
       (nth update-nth len)))))

(defthm fn-psc-path-finder-step-preserves-value
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (not (and (equal (fn-psc-get phase c) :control) (fn-psc-get ok c)))
               (equal byte (fn-psc-model-demanded-byte c incoming held)))
  (equal (fn-psc-model-path-finder-value (fn-psc-step c byte) incoming held)
         (fn-psc-model-path-finder-value c incoming held)))
 :hints (("Goal" :use (fn-psc-path-comparison-step-preserves-value
         fn-psc-path-launch-step-preserves-value
         fn-psc-path-byte-step-preserves-value
         fn-psc-path-failed-control-preserves-value)
  :cases ((equal (fn-psc-get phase c) :compare)
                        (equal (fn-psc-get phase c) :control)
                        (equal (fn-psc-get phase c) :path-scan))
  :in-theory (e/d (fn-psc-path-finder-statep fn-psc-model-path-finder-value
                   fn-psc-step fn-psc-finish)
                  (nth update-nth nfix len fn-psc-model-source)))))

(defun fn-psc-path-finder-activep (c)
 (declare (xargs :guard t :verify-guards nil))
 (and (not (equal (fn-psc-get phase c) :done))
      (not (and (equal (fn-psc-get phase c) :control) (fn-psc-get ok c)))))
(defun fn-psc-path-finder-rank (c)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (fn-psc-path-finder-activep c)) 0
  (let* ((phase (fn-psc-get phase c))
         (p (case phase ((:compare :control) (nfix (fn-psc-get base c)))
              (:path-cr (nfix (1- (nfix (fn-psc-get pos c)))))
              (otherwise (nfix (fn-psc-get pos c)))))
         (weight (case phase (:path-scan (if (fn-psc-get aux c) 11 2))
                    (:compare (+ 4 (nfix (- 6 (nfix (fn-psc-get index c))))))
                    (:control 3) (:path-cr 1) (otherwise 0))))
   (+ (* 13 (nfix (- (nfix (fn-psc-get n c)) p))) weight))))
(defthm fn-psc-path-finder-rank-natural-by-definition
 (natp (fn-psc-path-finder-rank c))
 :hints (("Goal" :in-theory (enable fn-psc-path-finder-rank))))
(defthm fn-psc-path-finder-step-productive
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (fn-psc-path-finder-activep c))
  (< (fn-psc-path-finder-rank (fn-psc-step c byte)) (fn-psc-path-finder-rank c)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-path-finder-statep fn-psc-line-statep fn-psc-path-finder-activep
        fn-psc-path-finder-rank fn-psc-step fn-psc-control
        fn-psc-compare fn-psc-return fn-psc-finish fn-psc-model-source nfix)
       (nth update-nth len)))))
(in-theory (disable fn-psc-path-finder-activep fn-psc-path-finder-rank))

(defun fn-psc-model-path-finder-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (fn-psc-path-finder-rank c)
  :hints (("Goal" :use ((:instance fn-psc-path-finder-step-productive
    (byte (fn-psc-model-demanded-byte c incoming held))))
   :in-theory (disable fn-psc-path-finder-step-productive fn-psc-path-finder-rank)))))
 (if (or (not (fn-psc-path-finder-statep c incoming held))
         (not (fn-psc-path-finder-activep c))) c
  (fn-psc-model-path-finder-complete
   (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held)))
(defthm fn-psc-path-finder-complete-preserves-state
 (implies (fn-psc-path-finder-statep c incoming held)
  (fn-psc-path-finder-statep (fn-psc-model-path-finder-complete c incoming held) incoming held))
 :hints (("Goal" :induct (fn-psc-model-path-finder-complete c incoming held)
  :in-theory (e/d (fn-psc-model-path-finder-complete fn-psc-path-finder-activep)
                  (fn-psc-step fn-psc-model-demanded-byte)))))
(defthm fn-psc-path-finder-complete-preserves-value
 (implies (fn-psc-path-finder-statep c incoming held)
  (equal (fn-psc-model-path-finder-value
           (fn-psc-model-path-finder-complete c incoming held) incoming held)
         (fn-psc-model-path-finder-value c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-path-finder-complete c incoming held)
  :in-theory (e/d (fn-psc-model-path-finder-complete fn-psc-path-finder-activep)
                  (fn-psc-step fn-psc-model-demanded-byte)))))
(defthm fn-psc-path-finder-complete-finishes
 (implies (fn-psc-path-finder-statep c incoming held)
  (not (fn-psc-path-finder-activep (fn-psc-model-path-finder-complete c incoming held))))
 :hints (("Goal" :induct (fn-psc-model-path-finder-complete c incoming held)
  :in-theory (e/d (fn-psc-model-path-finder-complete fn-psc-path-finder-activep)
                  (fn-psc-step fn-psc-model-demanded-byte)))))
(in-theory (disable fn-psc-model-path-finder-complete))

(defun fn-psc-model-path-finder-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil :measure (fn-psc-path-finder-rank c)
  :hints (("Goal" :use ((:instance fn-psc-path-finder-step-productive
    (byte (fn-psc-model-demanded-byte c incoming held))))
   :in-theory (disable fn-psc-path-finder-step-productive fn-psc-path-finder-rank)))))
 (if (or (not (fn-psc-path-finder-statep c incoming held))
         (not (fn-psc-path-finder-activep c))) 0
  (+ 1 (fn-psc-model-path-finder-cost
   (fn-psc-step c (fn-psc-model-demanded-byte c incoming held)) incoming held))))
(defthm fn-psc-path-finder-complete-is-actual-steps
 (equal (fn-psc-model-path-finder-complete c incoming held)
        (fn-psc-model-byte-run (fn-psc-model-path-finder-cost c incoming held) c incoming held))
 :hints (("Goal" :induct (fn-psc-model-path-finder-cost c incoming held)
  :in-theory (e/d (fn-psc-model-path-finder-cost fn-psc-model-path-finder-complete
                   fn-psc-model-byte-run)
                  (fn-psc-step fn-psc-model-demanded-byte fn-psc-path-finder-activep
                   fn-psc-path-finder-statep)))))
(in-theory (disable fn-psc-model-path-finder-cost))

(defun fn-psc-model-path-finder-result (c)
 (declare (xargs :guard t :verify-guards nil))
 (if (and (equal (fn-psc-get phase c) :control) (fn-psc-get ok c))
     (fn-psc-get pos c) nil))
(defthm fn-psc-path-finder-terminal-result
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (not (fn-psc-path-finder-activep c)))
  (equal (fn-psc-model-path-finder-result c)
         (fn-psc-model-path-finder-value c incoming held)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-path-finder-statep fn-psc-path-finder-activep
        fn-psc-model-path-finder-result fn-psc-model-path-finder-value)
       (nth nfix len fn-psc-model-source)))))
(defthm fn-psc-path-finder-complete-is-current-buffer-parser
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (equal (fn-psc-get phase c) :path-scan) (fn-psc-get aux c))
  (equal (fn-psc-model-path-finder-result
           (fn-psc-model-path-finder-complete c incoming held))
         (fn-pbb-path-scan (fn-psc-get pos c) t (fn-psc-model-source c incoming held))))
 :hints (("Goal" :use (fn-psc-path-finder-complete-preserves-state
                        fn-psc-path-finder-complete-preserves-value
                        fn-psc-path-finder-complete-finishes
                  (:instance fn-psc-path-finder-terminal-result
                    (c (fn-psc-model-path-finder-complete c incoming held))))
  :in-theory (e/d (fn-psc-model-path-finder-value fn-psc-path-finder-statep fn-psc-line-statep)
   (fn-psc-path-finder-complete-preserves-state fn-psc-path-finder-complete-preserves-value
    fn-psc-path-finder-complete-finishes fn-psc-path-finder-terminal-result
    fn-psc-model-path-finder-result fn-psc-model-path-finder-complete
    fn-pbb-path-scan fn-psc-reference-path-index-unfolds nth nfix len)))))
(in-theory (disable fn-psc-model-path-finder-result))

; Actual incoming-span comparison and v3 descriptor composition.

(defthm fn-psc-incoming-reference-byte
 (implies (and (equal (fn-psc-get ref c) :incoming)
               (natp (fn-psc-get ref-start c)) (natp index))
  (equal (fn-psc-model-reference-byte c index incoming held)
         (nth (+ (fn-psc-get ref-start c) index) incoming)))
 :hints (("Goal" :in-theory (e/d (fn-psc-model-reference-byte nfix) (nth len)))))
(defthm fn-psc-incoming-reference-octets
 (implies (and (equal (fn-psc-get ref c) :incoming)
               (natp (fn-psc-get ref-start c)) (natp index) (natp count)
               (true-listp incoming)
               (<= (+ (fn-psc-get ref-start c) index count) (len incoming)))
  (equal (fn-psc-model-reference-octets count index c incoming held)
         (fn-inj-take count (nthcdr (+ (fn-psc-get ref-start c) index) incoming))))
 :hints (("Goal" :induct (fn-psc-model-reference-octets count index c incoming held)
  :in-theory (e/d (fn-psc-model-reference-octets fn-inj-take nfix)
                  (fn-psc-model-reference-byte nth nthcdr len)))))

(defthm fn-psc-agent-comparison-is-incoming-span-strip
 (implies (and (natp pos) (true-listp incoming)
               (natp (fn-psc-get agent-start c)) (natp (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-start c) (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-end c) (len incoming))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-model-compare-value (fn-psc-agent-compare pos resume c) incoming held)
         (not (equal (fn-inj-strip
          (fn-inj-take (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))
                       (nthcdr (fn-psc-get agent-start c) incoming))
          (nthcdr pos (fn-psc-model-source c incoming held))) :no))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-prefix-is-actual-strip
          (remaining (- (fn-psc-get agent-end c) (fn-psc-get agent-start c)))
          (index 0) (c (fn-psc-agent-compare pos resume c)))
         (:instance fn-psc-incoming-reference-octets
          (count (- (fn-psc-get agent-end c) (fn-psc-get agent-start c)))
          (index 0) (c (fn-psc-agent-compare pos resume c))))
  :in-theory (e/d (fn-psc-agent-compare fn-psc-compare fn-psc-model-compare-value
                   fn-psc-model-source nfix)
   (fn-psc-prefix-is-actual-strip fn-psc-incoming-reference-octets
    fn-psc-model-prefix fn-psc-model-reference-octets fn-inj-strip fn-inj-take
    nth nthcdr len update-nth)))))

(defthm fn-psc-agent-complete-future-is-incoming-span-strip
 (implies (and (natp pos) (true-listp incoming)
               (natp (fn-psc-get agent-start c)) (natp (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-start c) (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-end c) (len incoming))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
               (fn-psc-failed-direct-resumep resume))
  (let* ((agent (fn-inj-take (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))
                           (nthcdr (fn-psc-get agent-start c) incoming)))
         (ok (not (equal (fn-inj-strip agent (nthcdr pos (fn-psc-model-source c incoming held))) :no)))
         (entry (fn-psc-agent-compare pos resume c)))
   (equal (fn-psc-result (fn-psc-model-byte-run fuel
            (fn-psc-model-comparison-complete entry incoming held) incoming held))
          (fn-psc-result (fn-psc-model-byte-run fuel
            (fn-psc-return ok (fn-psc-set pos
             (if ok (+ pos (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))) pos) entry))
            incoming held)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-psc-comparison-complete-canonical-future-result
           (c (fn-psc-agent-compare pos resume c)))
                       (:instance fn-psc-agent-comparison-is-incoming-span-strip))
  :in-theory (e/d (fn-psc-model-comparison-callback fn-psc-comparison-statep
                   fn-psc-comparison-positionp fn-psc-agent-compare fn-psc-compare nfix)
   (fn-psc-agent-comparison-is-incoming-span-strip fn-psc-model-compare-value
    fn-psc-model-comparison-complete fn-psc-model-byte-run fn-psc-return
    fn-psc-model-source nth update-nth len nthcdr fn-inj-strip fn-inj-take)))))

(defthm fn-psc-unsplice-control-four-steps
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :unsplice-agent)
               (natp (fn-psc-get pos c))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-result (fn-psc-model-byte-run 4 c incoming held))
   (if (and (fn-psc-get ok c)
            (< (fn-psc-get pos c) (len (fn-psc-model-source c incoming held)))
            (equal (nth (fn-psc-get pos c) (fn-psc-model-source c incoming held)) 33))
       (list :source (fn-psc-get k c) (fn-psc-get date c) (+ 1 (fn-psc-get pos c)))
     :no-source)))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (c) (fn-psc-model-byte-run 0 c incoming held))
           (:free (c) (fn-psc-model-byte-run 1 c incoming held))
           (:free (c) (fn-psc-model-byte-run 2 c incoming held))
           (:free (c) (fn-psc-model-byte-run 3 c incoming held))
           (:free (c) (fn-psc-model-byte-run 4 c incoming held)))
  :in-theory (e/d (fn-psc-step fn-psc-control fn-psc-literal fn-psc-compare
                   fn-psc-return fn-psc-finish fn-psc-result
                   fn-psc-model-demanded-byte fn-psc-demand fn-psc-expected
                   fn-psc-model-source nfix)
   (fn-psc-model-byte-run nth nthcdr len update-nth)))))

(defthm fn-psc-unsplice-agent-and-bang-result
 (implies (and (natp pos) (true-listp incoming)
               (natp (fn-psc-get agent-start c)) (natp (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-start c) (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-end c) (len incoming))
               (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let* ((agent (fn-inj-take (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))
                           (nthcdr (fn-psc-get agent-start c) incoming)))
         (end (+ pos (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))))
         (source (fn-psc-model-source c incoming held))
         (entry (fn-psc-agent-compare pos :unsplice-agent (fn-psc-set date pos c))))
   (equal (fn-psc-result (fn-psc-model-byte-run 4
            (fn-psc-model-comparison-complete entry incoming held) incoming held))
    (if (and (not (equal (fn-inj-strip agent (nthcdr pos source)) :no))
             (< end (len source)) (equal (nth end source) 33))
        (list :source (fn-psc-get k c) pos (+ end 1)) :no-source))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-agent-complete-future-is-incoming-span-strip
           (c (fn-psc-set date pos c)) (resume :unsplice-agent) (fuel 4)))
  :in-theory (e/d (fn-psc-agent-compare fn-psc-compare fn-psc-return
                   fn-psc-model-source nfix)
   (fn-psc-model-comparison-complete fn-psc-model-byte-run fn-inj-strip fn-inj-take
    fn-psc-step fn-psc-result nth nthcdr len update-nth)))))

(defthm fn-psc-path-insertion-strip-is-current-buffer-parser
 (implies (and (true-listp agent) (true-listp xs) (natp pos) (<= pos (len xs)))
  (equal (fn-pbb-strip-at (fn-inj-path-insert agent) pos xs)
   (if (and (not (equal (fn-inj-strip agent (nthcdr pos xs)) :no))
            (< (+ pos (len agent)) (len xs))
            (equal (nth (+ pos (len agent)) xs) 33))
       (+ pos (len agent) 1) :no)))
 :hints (("Goal" :induct (fn-pbb-strip-at agent pos xs)
  :in-theory (e/d (fn-pbb-strip-at fn-inj-path-insert fn-inj-strip true-list-fix)
                  (nth nthcdr len)))))

(defthm fn-psc-incoming-span-length
 (implies (and (natp count) (natp start) (<= (+ start count) (len xs)))
  (equal (len (fn-inj-take count (nthcdr start xs))) count))
 :hints (("Goal" :induct (fn-psc-model-reference-octets count start nil xs nil)
  :in-theory (e/d (fn-inj-take nfix) (nth nthcdr len)))))
(defthm fn-psc-incoming-span-true-list
 (true-listp (fn-inj-take count xs))
 :hints (("Goal" :induct (fn-inj-take count xs) :in-theory (enable fn-inj-take))))

(defthm fn-psc-unsplice-agent-result-is-current-buffer-strip
 (implies (and (natp pos) (true-listp incoming)
               (natp (fn-psc-get agent-start c)) (natp (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-start c) (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-end c) (len incoming))
               (true-listp (fn-psc-model-source c incoming held))
               (<= pos (len (fn-psc-model-source c incoming held)))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let* ((agent (fn-inj-take (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))
                           (nthcdr (fn-psc-get agent-start c) incoming)))
         (b (fn-pbb-strip-at (fn-inj-path-insert agent) pos (fn-psc-model-source c incoming held)))
         (entry (fn-psc-agent-compare pos :unsplice-agent (fn-psc-set date pos c))))
   (equal (fn-psc-result (fn-psc-model-byte-run 4
            (fn-psc-model-comparison-complete entry incoming held) incoming held))
          (if (equal b :no) :no-source (list :source (fn-psc-get k c) pos b)))))
 :hints (("Goal" :use (fn-psc-unsplice-agent-and-bang-result)
  :in-theory (e/d (nfix)
    (fn-psc-unsplice-agent-and-bang-result fn-pbb-strip-at-is-inj-strip
     fn-psc-model-comparison-complete fn-psc-model-byte-run fn-psc-agent-compare
     fn-psc-model-source fn-psc-result fn-inj-path-insert fn-pbb-strip-at
     fn-inj-strip fn-inj-take nth nthcdr len update-nth)))))

(defthm fn-psc-path-finder-step-preserves-slot
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (fn-psc-path-finder-activep c) (natp slot)
               (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 20 21 23))))
  (equal (nth slot (fn-psc-step c byte)) (nth slot c)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-path-finder-statep fn-psc-path-finder-activep fn-psc-step
        fn-psc-control fn-psc-compare fn-psc-return fn-psc-finish nfix)
       (nth update-nth len)))))
(defthm fn-psc-path-finder-complete-preserves-slot
 (implies (and (fn-psc-path-finder-statep c incoming held) (natp slot)
               (not (member-equal slot '(0 7 8 9 10 11 12 13 14 15 20 21 23))))
  (equal (nth slot (fn-psc-model-path-finder-complete c incoming held)) (nth slot c)))
 :hints (("Goal" :induct (fn-psc-model-path-finder-complete c incoming held)
  :in-theory (e/d (fn-psc-model-path-finder-complete fn-psc-path-finder-activep)
    (nth nfix len fn-psc-step fn-psc-model-demanded-byte fn-psc-path-finder-complete-is-actual-steps)))))

(defthm fn-psc-done-step-stays-done
 (implies (equal (fn-psc-get phase c) :done) (equal (fn-psc-step c byte) c))
 :hints (("Goal" :in-theory (enable fn-psc-step))))
(defthm fn-psc-done-comparison-stays-done
 (implies (equal (fn-psc-get phase c) :done)
  (equal (fn-psc-model-comparison-complete c incoming held) c))
 :hints (("Goal" :in-theory (enable fn-psc-model-comparison-complete))))

(defun fn-psc-model-v3-unsplice-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-path-finder-complete c incoming held))
        (entry (fn-psc-step d nil))
        (agent-done (fn-psc-model-comparison-complete entry incoming held)))
  (fn-psc-model-byte-run 4 agent-done incoming held)))
(defthm fn-psc-unsplice-field-enters-agent-comparison
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :unsplice-field) (fn-psc-get ok c)
               (natp (fn-psc-get pos c)))
  (equal (fn-psc-step c byte)
         (fn-psc-agent-compare (fn-psc-get pos c) :unsplice-agent
                             (fn-psc-set date (fn-psc-get pos c) c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control nfix)
                               (fn-psc-agent-compare nth len update-nth)))))

(defthm fn-psc-done-result-is-stored
 (implies (equal (fn-psc-get phase c) :done)
  (equal (fn-psc-result c) (fn-psc-get result c)))
 :hints (("Goal" :in-theory (enable fn-psc-result))))
(defun fn-psc-model-v3-terminal-complete (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-byte-run 4
  (fn-psc-model-comparison-complete (fn-psc-step c nil) incoming held) incoming held))
(defthm fn-psc-v3-terminal-result-is-current-buffer-strip
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (not (fn-psc-path-finder-activep c))
               (true-listp incoming)
               (natp (fn-psc-get agent-start c)) (natp (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-start c) (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-end c) (len incoming)))
  (let* ((agent (fn-inj-take (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))
                           (nthcdr (fn-psc-get agent-start c) incoming)))
         (b (fn-pbb-strip-at (fn-inj-path-insert agent) (fn-psc-get pos c)
                            (fn-psc-model-source c incoming held))))
   (equal (fn-psc-result (fn-psc-model-v3-terminal-complete c incoming held))
    (if (and (equal (fn-psc-get phase c) :control) (not (equal b :no)))
        (list :source (fn-psc-get k c) (fn-psc-get pos c) b) :no-source))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-unsplice-agent-result-is-current-buffer-strip
           (pos (fn-psc-get pos c))))
  :in-theory (e/d (fn-psc-model-v3-terminal-complete fn-psc-path-finder-statep
                   fn-psc-path-finder-activep fn-psc-line-statep)
   (fn-psc-unsplice-agent-result-is-current-buffer-strip fn-psc-unsplice-agent-and-bang-result
    fn-pbb-strip-at-is-inj-strip fn-psc-path-insertion-strip-is-current-buffer-parser
    fn-psc-model-byte-run fn-psc-model-comparison-complete fn-psc-step fn-psc-result
    fn-psc-agent-compare fn-psc-model-source fn-inj-path-insert fn-pbb-strip-at
    nth nthcdr len nfix update-nth)))))

(defthm fn-psc-model-v3-unsplice-unfolds
 (equal (fn-psc-model-v3-unsplice-complete c incoming held)
  (fn-psc-model-v3-terminal-complete (fn-psc-model-path-finder-complete c incoming held) incoming held))
 :hints (("Goal" :in-theory (enable fn-psc-model-v3-unsplice-complete fn-psc-model-v3-terminal-complete))))
(defthm fn-psc-model-v3-unsplice-is-current-buffer-parser
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (equal (fn-psc-get phase c) :path-scan) (fn-psc-get aux c)
               (equal (fn-psc-get k c) (fn-psc-get pos c))
               (true-listp incoming)
               (natp (fn-psc-get agent-start c)) (natp (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-start c) (fn-psc-get agent-end c))
               (<= (fn-psc-get agent-end c) (len incoming)))
  (let* ((agent (fn-inj-take (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))
                           (nthcdr (fn-psc-get agent-start c) incoming)))
         (desc (fn-pbb-unsplice-at (fn-psc-get k c) agent (fn-psc-model-source c incoming held))))
   (equal (fn-psc-result (fn-psc-model-v3-unsplice-complete c incoming held))
          (if desc (cons :source desc) :no-source))))
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-psc-get phase (fn-psc-model-path-finder-complete c incoming held)) :control))
  :use (fn-psc-path-finder-complete-preserves-state fn-psc-path-finder-complete-finishes
        fn-psc-path-finder-complete-is-current-buffer-parser
        (:instance fn-psc-v3-terminal-result-is-current-buffer-strip
         (c (fn-psc-model-path-finder-complete c incoming held))))
  :in-theory (e/d (fn-pbb-unsplice-at fn-psc-model-path-finder-result
                   fn-psc-path-finder-statep fn-psc-line-statep fn-psc-path-finder-activep
                   fn-psc-model-source)
   (fn-psc-model-path-finder-complete fn-psc-path-finder-complete-is-actual-steps
    fn-psc-path-finder-complete-preserves-state fn-psc-path-finder-complete-finishes
    fn-psc-path-finder-complete-is-current-buffer-parser
    fn-psc-v3-terminal-result-is-current-buffer-strip
    fn-psc-unsplice-agent-and-bang-result fn-pbb-strip-at-is-inj-strip
    fn-psc-unsplice-agent-result-is-current-buffer-strip
    fn-psc-model-v3-unsplice-complete fn-psc-model-v3-terminal-complete
    fn-psc-model-comparison-complete fn-psc-model-byte-run fn-psc-step
    fn-psc-result fn-psc-agent-compare fn-pbb-path-scan fn-pbb-strip-at fn-inj-path-insert
    fn-psc-path-insertion-strip-is-current-buffer-parser
    nth nthcdr len update-nth nfix)))))

(defthm fn-psc-terminal-path-demand-is-control
 (implies (and (fn-psc-path-finder-statep c incoming held)
               (not (fn-psc-path-finder-activep c)))
  (equal (fn-psc-model-demanded-byte c incoming held) nil))
 :hints (("Goal" :in-theory (e/d (fn-psc-path-finder-statep fn-psc-path-finder-activep
                     fn-psc-model-demanded-byte fn-psc-demand) (nth nfix len)))))
(defun fn-psc-model-v3-unsplice-cost (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-psc-model-path-finder-complete c incoming held))
        (entry (fn-psc-step d nil)))
  (+ (fn-psc-model-path-finder-cost c incoming held) 1
     (fn-psc-model-comparison-cost entry incoming held) 4)))
(defthm fn-psc-v3-unsplice-complete-is-actual-steps
 (implies (fn-psc-path-finder-statep c incoming held)
  (equal (fn-psc-model-v3-unsplice-complete c incoming held)
         (fn-psc-model-byte-run (fn-psc-model-v3-unsplice-cost c incoming held) c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-path-finder-complete-preserves-state fn-psc-path-finder-complete-finishes
         fn-psc-path-finder-complete-is-actual-steps
        (:instance fn-psc-comparison-complete-is-actual-steps
          (c (fn-psc-step (fn-psc-model-path-finder-complete c incoming held) nil)))
         (:instance fn-psc-byte-run-addition
          (a (fn-psc-model-path-finder-cost c incoming held))
          (b (+ 5 (fn-psc-model-comparison-cost
             (fn-psc-step (fn-psc-model-path-finder-complete c incoming held) nil) incoming held))))
         (:instance fn-psc-byte-run-addition (a 1)
          (b (+ 4 (fn-psc-model-comparison-cost
             (fn-psc-step (fn-psc-model-path-finder-complete c incoming held) nil) incoming held)))
          (c (fn-psc-model-path-finder-complete c incoming held)))
         (:instance fn-psc-byte-run-addition
          (a (fn-psc-model-comparison-cost
             (fn-psc-step (fn-psc-model-path-finder-complete c incoming held) nil) incoming held))
          (b 4) (c (fn-psc-step (fn-psc-model-path-finder-complete c incoming held) nil))))
  :expand ((:free (c) (fn-psc-model-byte-run 0 c incoming held))
           (:free (c) (fn-psc-model-byte-run 1 c incoming held)))
  :in-theory (e/d (fn-psc-model-v3-unsplice-cost fn-psc-model-v3-unsplice-complete)
    (fn-psc-byte-run-addition fn-psc-model-v3-unsplice-unfolds fn-psc-model-byte-run fn-psc-step
     fn-psc-path-finder-complete-preserves-state fn-psc-path-finder-complete-finishes
     fn-psc-path-finder-complete-is-actual-steps fn-psc-model-path-finder-complete
     fn-psc-model-comparison-complete fn-psc-comparison-complete-is-actual-steps
     fn-psc-model-comparison-cost fn-psc-model-path-finder-cost nth nfix len)))))

(in-theory (disable fn-psc-model-v3-unsplice-complete fn-psc-model-v3-terminal-complete fn-psc-model-v3-unsplice-cost))

; Exact leading generated Path agent and bounded block fallback.


(local (in-theory (disable fn-psc-inj-drop-is-nthcdr)))

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

(local (defthm fn-psc-append-prefix-cancels
 (implies (true-listp prefix)
  (equal (equal (append prefix a) (append prefix b)) (equal a b)))
 :hints (("Goal" :induct (len prefix) :in-theory (enable append len true-listp)))))

(local (defthm fn-psc-strip-take-is-drop
 (implies (true-listp xs)
  (equal (fn-inj-strip (fn-inj-take k xs) xs) (fn-inj-drop k xs)))
 :hints (("Goal" :induct (fn-inj-take k xs)
  :in-theory (enable fn-inj-take fn-inj-drop fn-inj-strip true-listp)))))

(local (defthm fn-psc-take-and-fixed-tail-equality
 (implies (true-listp xs)
  (equal (equal (append (fn-inj-take k xs) tail) xs)
         (equal tail (fn-inj-drop k xs))))
 :hints (("Goal" :induct (fn-inj-take k xs)
  :in-theory (enable fn-inj-take fn-inj-drop append true-listp)))))

(local (defthm fn-psc-reference-path-agent-is-exact-tail
 (equal (fn-pb-path-line-agent xs)
  (let* ((line (fn-pb-line xs)) (r (fn-inj-strip *fn-inj-path-field* line))
         (count (- (len r) 15)))
   (if (and (true-listp r) (< 15 (len r))
            (equal (fn-inj-drop count r) '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)))
       (fn-inj-take count r) nil)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-strip-success-reconstructs
            (prefix *fn-inj-path-field*) (xs (fn-pb-line xs))))
  :in-theory (e/d (fn-pb-path-line-agent fn-inj-path-line)
   (fn-inj-strip fn-pb-line fn-inj-drop fn-inj-take fn-inj-append len))))))

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

(local (defthm fn-psc-successful-prefix-fits-source
 (implies (and (not (zp remaining))
               (fn-psc-model-prefix remaining index pos c incoming held))
  (<= (+ (nfix remaining) (nfix pos)) (nfix (fn-psc-get n c))))
 :hints (("Goal" :induct (fn-psc-model-prefix remaining index pos c incoming held)
  :in-theory (e/d (fn-psc-model-prefix nfix) (nth len))))))

(local (defthm fn-psc-successful-literal-comparison-fits-source
 (implies (and (natp pos) (consp bytes) (true-listp bytes)
               (fn-psc-model-compare-value (fn-psc-literal pos bytes resume c) incoming held))
  (<= (+ pos (len bytes)) (nfix (fn-psc-get n c))))
 :hints (("Goal" :do-not-induct t :expand ((len bytes))
  :use ((:instance fn-psc-successful-prefix-fits-source
    (remaining (len bytes)) (index 0) (c (fn-psc-literal pos bytes resume c))))
  :in-theory (e/d (fn-psc-model-compare-value fn-psc-literal fn-psc-compare nfix)
                  (fn-psc-model-prefix fn-psc-successful-prefix-fits-source nth len update-nth))))))

(local (defthm fn-psc-line-take-within-first-line
 (implies (and (natp count) (<= count (len (fn-pb-line xs))))
  (equal (fn-inj-take count (fn-pb-line xs)) (fn-inj-take count xs)))
 :hints (("Goal" :induct (fn-inj-take count xs)
  :in-theory (enable fn-inj-take fn-pb-line len nfix)))))

(local (defthm fn-psc-strip-succeeds-iff-take-equal
 (implies (and (true-listp prefix) (true-listp xs))
  (equal (not (equal (fn-inj-strip prefix xs) :no))
         (equal (fn-inj-take (len prefix) xs) prefix)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip fn-inj-take len true-listp nfix)))))

(local (defthm fn-psc-line-drop-within-first-line
 (implies (and (natp off) (< off (len (fn-pb-line xs))))
  (equal (fn-pb-line (nthcdr off xs)) (fn-inj-drop off (fn-pb-line xs))))
 :hints (("Goal" :induct (nthcdr off xs)
  :in-theory (enable nthcdr fn-pb-line fn-inj-drop len nfix)))))

(local (defthm fn-psc-drop-length-within-list
 (implies (and (natp off) (<= off (len xs)))
  (equal (len (fn-inj-drop off xs)) (- (len xs) off)))
 :hints (("Goal" :induct (fn-inj-drop off xs) :in-theory (enable fn-inj-drop len nfix)))))

(local (defthm fn-psc-take-length-of-proper-list
 (implies (true-listp xs) (equal (fn-inj-take (len xs) xs) xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable fn-inj-take len true-listp nfix)))))

(local (defthm fn-psc-first-line-fixed-tail-slice
 (implies (and (true-listp xs) (natp count) (<= count (len (fn-pb-line xs)))
               (not (zp count)))
  (equal (fn-inj-take count (nthcdr (- (len (fn-pb-line xs)) count) xs))
         (fn-inj-drop (- (len (fn-pb-line xs)) count) (fn-pb-line xs))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-drop-length-within-list
          (xs (fn-pb-line xs)) (off (- (len (fn-pb-line xs)) count)))
         (:instance fn-psc-take-length-of-proper-list
          (xs (fn-inj-drop (- (len (fn-pb-line xs)) count) (fn-pb-line xs))))
         (:instance fn-psc-line-drop-within-first-line
          (off (- (len (fn-pb-line xs)) count)))
         (:instance fn-psc-line-take-within-first-line
          (xs (nthcdr (- (len (fn-pb-line xs)) count) xs))))
  :in-theory (disable fn-psc-inj-drop-is-nthcdr fn-psc-drop-length-within-list fn-pb-line fn-inj-take fn-inj-drop nthcdr len
                      fn-psc-take-length-of-proper-list fn-psc-line-drop-within-first-line fn-psc-line-take-within-first-line)))))

(local (defthm fn-psc-first-line-true-list
 (true-listp (fn-pb-line xs))
 :hints (("Goal" :induct (fn-pb-line xs) :in-theory (enable fn-pb-line)))))

(local (defthm fn-psc-drop-preserves-true-list
 (implies (true-listp xs) (true-listp (fn-inj-drop k xs)))
 :hints (("Goal" :induct (fn-inj-drop k xs) :in-theory (enable fn-inj-drop)))))

(local (defthm fn-psc-first-line-path-tail-is-full-source-strip
 (implies (and (true-listp xs) (< 15 (len (fn-pb-line xs))))
  (equal (equal (fn-inj-drop (- (len (fn-pb-line xs)) 15) (fn-pb-line xs))
                '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10))
         (not (equal (fn-inj-strip '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)
                                   (nthcdr (- (len (fn-pb-line xs)) 15) xs)) :no))))
 :hints (("Goal" :use ((:instance fn-psc-first-line-fixed-tail-slice (count 15))
                       (:instance fn-psc-strip-succeeds-iff-take-equal
                        (prefix '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10))
                        (xs (nthcdr (- (len (fn-pb-line xs)) 15) xs))))
  :in-theory (disable fn-psc-first-line-fixed-tail-slice fn-psc-strip-succeeds-iff-take-equal
                      fn-inj-strip fn-inj-take fn-inj-drop fn-pb-line nthcdr len)))))

(local (defthm fn-psc-strip-field-from-first-line
 (implies (and (true-listp prefix) (not (member-equal 10 prefix)) (true-listp xs))
  (equal (fn-inj-strip prefix (fn-pb-line xs))
   (if (equal (fn-inj-strip prefix xs) :no) :no
     (fn-pb-line (fn-inj-strip prefix xs)))))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip fn-pb-line member-equal true-listp)))))

(local (defthm fn-psc-strip-preserves-proper-list-or-fails
 (implies (and (true-listp xs) (not (equal (fn-inj-strip prefix xs) :no)))
  (true-listp (fn-inj-strip prefix xs)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs) :in-theory (enable fn-inj-strip)))))

(local (defthm fn-psc-reference-leading-path-agent-from-residual
 (implies (true-listp xs)
  (equal (fn-pb-path-line-agent xs)
   (let* ((r (fn-inj-strip *fn-inj-path-field* xs))
          (count (- (len (fn-pb-line r)) 15)))
    (if (and (not (equal r :no)) (< 15 (len (fn-pb-line r)))
             (not (equal (fn-inj-strip '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)
                                       (nthcdr count r)) :no)))
        (fn-inj-take count r) nil))))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-reference-path-agent-is-exact-tail
        (:instance fn-psc-strip-field-from-first-line (prefix *fn-inj-path-field*))
        (:instance fn-psc-first-line-path-tail-is-full-source-strip
          (xs (fn-inj-strip *fn-inj-path-field* xs)))
        (:instance fn-psc-line-take-within-first-line
          (xs (fn-inj-strip *fn-inj-path-field* xs))
          (count (- (len (fn-pb-line (fn-inj-strip *fn-inj-path-field* xs))) 15))))
  :in-theory (disable fn-pb-path-line-agent fn-psc-reference-path-agent-is-exact-tail
                      fn-psc-strip-field-from-first-line fn-psc-first-line-path-tail-is-full-source-strip
                      fn-psc-line-take-within-first-line fn-pb-line fn-inj-take fn-inj-drop
                      fn-inj-strip fn-psc-strip-succeeds-iff-take-equal len nthcdr)))))

(local (defthm fn-psc-strip-success-is-exact-drop
 (implies (and (true-listp prefix) (not (equal (fn-inj-strip prefix xs) :no)))
  (equal (fn-inj-strip prefix xs) (nthcdr (len prefix) xs)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip nthcdr len true-listp)))))

(local (defthm fn-psc-nthcdr-composes-offsets
 (implies (and (natp a) (natp b))
  (equal (nthcdr b (nthcdr a xs)) (nthcdr (+ a b) xs)))
 :hints (("Goal" :induct (nthcdr a xs) :in-theory (enable nthcdr)))))

(local (defthm fn-psc-reference-leading-path-agent-from-indices
 (implies (and (true-listp xs) (natp start) (natp a)
               (equal a (+ start 6)) (<= a (len xs))
               (not (equal (fn-inj-strip *fn-inj-path-field* (nthcdr start xs)) :no)))
  (let* ((r (nthcdr a xs)) (count (- (len (fn-pb-line r)) 15)))
   (equal (fn-pb-path-line-agent (nthcdr start xs))
    (if (and (< 15 (len (fn-pb-line r)))
             (not (equal (fn-inj-strip '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)
                                       (nthcdr (+ a count) xs)) :no)))
        (fn-inj-take count r) nil))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-reference-leading-path-agent-from-residual (xs (nthcdr start xs))))
  :in-theory (disable fn-psc-reference-leading-path-agent-from-residual
                      fn-psc-reference-path-agent-is-exact-tail fn-pb-path-line-agent
                      fn-pb-line fn-inj-strip fn-inj-take len nthcdr)))))

(local (defthm fn-psc-agent-path-tail-control-result
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :agent-path-tail))
  (equal (fn-psc-result (fn-psc-model-byte-run 1 c incoming held))
         (if (fn-psc-get ok c)
             (list :agent (fn-psc-get agent-start c) (fn-psc-get agent-end c)) :pending)))
 :hints (("Goal"
  :expand ((fn-psc-model-byte-run 1 c incoming held)
           (:free (c) (fn-psc-model-byte-run 0 c incoming held)))
  :in-theory (e/d (fn-psc-step fn-psc-control fn-psc-finish fn-psc-literal
                   fn-psc-compare fn-psc-result)
   (fn-psc-model-byte-run nth update-nth nfix len fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-agent-path-tail-complete-result
 (implies (and (natp pos) (true-listp (fn-psc-model-source c incoming held))
               (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held))))
  (let ((entry (fn-psc-literal pos '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)
                             :agent-path-tail c)))
   (equal (fn-psc-result (fn-psc-model-byte-run 1
            (fn-psc-model-comparison-complete entry incoming held) incoming held))
    (if (not (equal (fn-inj-strip '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)
                                 (nthcdr pos (fn-psc-model-source c incoming held))) :no))
        (list :agent (fn-psc-get agent-start c) (fn-psc-get agent-end c)) :pending))))
 :hints (("Goal" :use ((:instance fn-psc-comparison-complete-canonical-future-result
        (c (fn-psc-literal pos '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)
                             :agent-path-tail c)) (fuel 1))
                       (:instance fn-psc-literal-comparison-is-actual-strip
                        (bytes '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10))
                        (resume :agent-path-tail)))
  :in-theory (e/d (fn-psc-model-comparison-callback fn-psc-literal fn-psc-compare
                   fn-psc-return fn-psc-comparison-statep fn-psc-comparison-positionp
                   fn-psc-failed-direct-resumep nfix)
   (fn-psc-model-compare-value fn-psc-model-comparison-complete fn-psc-model-byte-run
    fn-psc-literal-comparison-is-actual-strip fn-inj-strip nth nthcdr len update-nth))))))

(defun fn-psc-leading-path-statep (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (and (equal (fn-psc-get mode c) :agent) (equal (fn-psc-get phase c) :control)
      (equal (fn-psc-get resume c) :agent-path-field) (fn-psc-get ok c)
      (true-listp incoming) (equal (fn-psc-get n c) (len incoming))
      (natp (fn-psc-get pos c)) (<= (fn-psc-get pos c) (len incoming))
      (natp (fn-psc-get skip c))
      (equal (fn-psc-get pos c) (+ 6 (fn-psc-get skip c)))
      (not (equal (fn-inj-strip *fn-inj-path-field* (nthcdr (fn-psc-get skip c) incoming)) :no))))

(defun fn-psc-model-leading-path-scan (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-line-complete (fn-psc-step c nil) incoming nil))

(defun fn-psc-model-leading-path-complete (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((tail-entry (fn-psc-step (fn-psc-model-leading-path-scan c incoming) nil)))
  (if (equal (fn-psc-get resume tail-entry) :agent-path-tail)
      (fn-psc-model-byte-run 1 (fn-psc-model-comparison-complete tail-entry incoming nil) incoming nil)
    tail-entry)))

(local (defthm fn-psc-agent-path-field-starts-content-line-unfolds
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :agent-path-field) (fn-psc-get ok c)
               (natp (fn-psc-get pos c)))
  (equal (fn-psc-step c byte)
   (fn-psc-set phase :line (fn-psc-set resume :agent-path-line
                         (fn-psc-set agent-start (fn-psc-get pos c) c)))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control nfix)
                               (nth len update-nth))))))

(defthm fn-psc-leading-path-scan-frame
 (implies (fn-psc-leading-path-statep c incoming)
  (let ((d (fn-psc-model-leading-path-scan c incoming)))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) :agent-path-line)
        (equal (fn-psc-get mode d) :agent)
        (equal (fn-psc-get agent-start d) (fn-psc-get pos c))
        (equal (fn-psc-get skip d) (fn-psc-get skip c))
        (equal (fn-psc-get n d) (len incoming))
        (natp (fn-psc-get pos d)) (<= (fn-psc-get pos d) (len incoming))
        (equal (fn-psc-get pos d)
               (+ (fn-psc-get pos c) (len (fn-pb-line (nthcdr (fn-psc-get pos c) incoming))))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-line-complete-returns-control (c (fn-psc-step c nil)) (held nil))
        (:instance fn-psc-line-complete-preserves-state (c (fn-psc-step c nil)) (held nil))
        (:instance fn-psc-line-complete-exact-position (c (fn-psc-step c nil)) (held nil)))
  :in-theory (e/d (fn-psc-leading-path-statep fn-psc-model-leading-path-scan
                   fn-psc-line-statep fn-psc-model-source)
   (fn-psc-line-complete-returns-control fn-psc-line-complete-preserves-state
    fn-psc-line-complete-exact-position fn-psc-model-line-complete fn-psc-step
    fn-inj-strip nth nthcdr len update-nth nfix)))))

(defthm fn-psc-leading-path-complete-result
 (implies (fn-psc-leading-path-statep c incoming)
  (let* ((a (fn-psc-get pos c))
         (l (len (fn-pb-line (nthcdr a incoming))))
         (end (+ a l -15)))
   (equal (fn-psc-result (fn-psc-model-leading-path-complete c incoming))
    (if (and (< 15 l)
             (not (equal (fn-inj-strip '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)
                                       (nthcdr end incoming)) :no)))
        (list :agent a end) :pending))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-leading-path-scan-frame)
        (:instance fn-psc-agent-path-tail-complete-result
         (c (fn-psc-set agent-end
              (- (fn-psc-get pos (fn-psc-model-leading-path-scan c incoming)) 15)
              (fn-psc-model-leading-path-scan c incoming)))
         (pos (- (fn-psc-get pos (fn-psc-model-leading-path-scan c incoming)) 15))
         (held nil)))
  :in-theory (e/d (fn-psc-model-leading-path-complete fn-psc-leading-path-statep
                   fn-psc-step fn-psc-control fn-psc-model-source fn-psc-literal
                   fn-psc-compare fn-psc-result nfix)
   (fn-psc-model-leading-path-scan fn-psc-model-comparison-complete
    fn-psc-model-byte-run fn-psc-leading-path-scan-frame
    fn-psc-agent-path-tail-complete-result fn-inj-strip nthcdr nth len update-nth)))))

(local (defthm fn-psc-take-positive-first-line-nonempty
 (implies (and (natp k) (< 0 k) (<= k (len (fn-pb-line xs))))
          (consp (fn-inj-take k xs)))
 :hints (("Goal" :in-theory (enable fn-inj-take fn-pb-line)))))

(defthm fn-psc-leading-path-result-is-current-path-agent
 (implies (fn-psc-leading-path-statep c incoming)
  (let* ((a (fn-psc-get pos c))
         (end (+ a (len (fn-pb-line (nthcdr a incoming))) -15))
         (agent (fn-pb-path-line-agent (nthcdr (fn-psc-get skip c) incoming))))
   (and
    (equal (fn-psc-result (fn-psc-model-leading-path-complete c incoming))
           (if agent (list :agent a end) :pending))
    (implies agent
     (equal (fn-inj-take (- end a) (nthcdr a incoming)) agent)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-reference-leading-path-agent-from-indices
         (xs incoming) (start (fn-psc-get skip c)) (a (fn-psc-get pos c)))
        (:instance fn-psc-take-positive-first-line-nonempty
         (k (- (len (fn-pb-line (nthcdr (fn-psc-get pos c) incoming))) 15))
         (xs (nthcdr (fn-psc-get pos c) incoming))))
  :in-theory (e/d (fn-psc-leading-path-statep)
   (fn-psc-reference-leading-path-agent-from-indices
    fn-psc-reference-path-agent-is-exact-tail fn-psc-reference-leading-path-agent-from-residual
    fn-psc-strip-field-from-first-line fn-psc-strip-success-is-exact-drop
    fn-psc-strip-succeeds-iff-take-equal fn-pbb-strip-at-is-inj-strip fn-pb-path-line-agent
    fn-psc-model-leading-path-complete fn-pb-line fn-inj-strip fn-inj-take
    nthcdr len nth update-nth)))))

(defthm fn-psc-agent-path-tail-failure-starts-block
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :agent-path-tail)
               (not (fn-psc-get ok c)))
  (let ((d (fn-psc-step c byte)))
   (and (equal (fn-psc-get phase d) :compare)
        (equal (fn-psc-get resume d) :agent-stamp)
        (equal (fn-psc-get pos d) (nfix (fn-psc-get skip c)))
        (equal (fn-psc-get ref d) *fn-inj-injection-date-field*)
        (equal (fn-psc-get ref-len d) 16)
        (equal (fn-psc-get index d) 0))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control fn-psc-literal fn-psc-compare nfix)
                                (nth update-nth len)))))

(in-theory (disable fn-psc-leading-path-statep fn-psc-model-leading-path-scan fn-psc-model-leading-path-complete))
(defun fn-psc-model-leading-path-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((scan (fn-psc-model-leading-path-scan c incoming))
        (tail (fn-psc-step scan nil)))
  (+ 2 (fn-psc-model-line-cost (fn-psc-step c nil) incoming nil)
     (if (equal (fn-psc-get resume tail) :agent-path-tail)
         (+ 1 (fn-psc-model-comparison-cost tail incoming nil)) 0))))
(defthm fn-psc-leading-path-scan-is-actual-steps
 (implies (fn-psc-leading-path-statep c incoming)
  (equal (fn-psc-model-leading-path-scan c incoming)
         (fn-psc-model-byte-run
          (+ 1 (fn-psc-model-line-cost (fn-psc-step c nil) incoming nil))
          c incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-line-complete-is-actual-steps
         (c (fn-psc-step c nil)) (held nil))
        (:instance fn-psc-byte-run-addition (a 1)
         (b (fn-psc-model-line-cost (fn-psc-step c nil) incoming nil)) (held nil)))
  :expand ((fn-psc-model-byte-run 1 c incoming nil)
           (:free (c) (fn-psc-model-byte-run 0 c incoming nil)))
  :in-theory (e/d (fn-psc-leading-path-statep fn-psc-model-leading-path-scan
                   fn-psc-model-demanded-byte fn-psc-demand)
    (fn-psc-step fn-psc-model-byte-run fn-psc-model-line-complete
     fn-psc-model-line-cost fn-psc-byte-run-addition fn-psc-line-complete-is-actual-steps
     nth len nfix update-nth)))))
(defthm fn-psc-leading-path-complete-is-actual-steps
 (implies (fn-psc-leading-path-statep c incoming)
  (equal (fn-psc-model-leading-path-complete c incoming)
         (fn-psc-model-byte-run (fn-psc-model-leading-path-cost c incoming) c incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-leading-path-scan-frame fn-psc-leading-path-scan-is-actual-steps
        (:instance fn-psc-comparison-complete-is-actual-steps
         (c (fn-psc-step (fn-psc-model-leading-path-scan c incoming) nil)) (held nil))
        (:instance fn-psc-byte-run-addition (held nil)
         (a (+ 1 (fn-psc-model-line-cost (fn-psc-step c nil) incoming nil)))
         (b (+ 1 (if (equal (fn-psc-get resume (fn-psc-step (fn-psc-model-leading-path-scan c incoming) nil)) :agent-path-tail)
                       (+ 1 (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-leading-path-scan c incoming) nil) incoming nil)) 0))))
        (:instance fn-psc-byte-run-addition (held nil) (a 1)
         (c (fn-psc-model-leading-path-scan c incoming))
         (b (+ 1 (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-leading-path-scan c incoming) nil) incoming nil))))
        (:instance fn-psc-byte-run-addition (held nil) (b 1)
         (c (fn-psc-step (fn-psc-model-leading-path-scan c incoming) nil))
         (a (fn-psc-model-comparison-cost (fn-psc-step (fn-psc-model-leading-path-scan c incoming) nil) incoming nil))))
  :expand ((:free (c) (fn-psc-model-byte-run 0 c incoming nil))
           (:free (c) (fn-psc-model-byte-run 1 c incoming nil)))
  :in-theory (e/d (fn-psc-model-leading-path-complete fn-psc-model-leading-path-cost
                   fn-psc-model-demanded-byte fn-psc-demand)
   (fn-psc-line-demanded-byte fn-psc-demanded-span-byte fn-psc-demanded-target-byte
    fn-psc-line-field-byte fn-psc-param-demanded-byte
    fn-psc-model-leading-path-scan fn-psc-model-line-cost fn-psc-model-comparison-cost
    fn-psc-model-comparison-complete fn-psc-step fn-psc-byte-run-addition
    fn-psc-model-byte-run fn-psc-leading-path-scan-is-actual-steps
    fn-psc-comparison-complete-is-actual-steps fn-psc-leading-path-scan-frame
    nth len nfix update-nth)))))
(in-theory (disable fn-psc-model-leading-path-cost))
