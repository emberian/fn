; PRF-1261: suspend the existing Wildmat work recursions one cell/frame at a time.
(in-package "ACL2")
(include-book "wildmat-work")
(include-book "nntp-responses")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable (tau-system))))
(local (deftheory fn-wmc-entry-base (current-theory :here)))

(defun fn-wmc-at (n x)
  (declare (xargs :guard (natp n)))
  (if (consp x) (if (zp n) (car x) (fn-wmc-at (1- n) (cdr x))) nil))

; Tasks and frames have exactly five cells; the outer state has two.
(defun fn-wmc-node (tag a b c d)
  (declare (xargs :guard t))
  (list tag a b c d))
(defun fn-wmc-state (task frames)
  (declare (xargs :guard t))
  (list task frames))
(defun fn-wmc-return (value cost)
  (declare (xargs :guard t))
  (fn-wmc-node :return value cost nil nil))
(defun fn-wmc-call (tag a b c frame frames)
  (declare (xargs :guard t))
  (fn-wmc-state (fn-wmc-node tag a b c nil) (cons frame frames)))

(defun fn-wmc-core-start (patterns group)
  (declare (xargs :guard t))
  ; Invoke only after the caller reserves the seven-cell fixed envelope.
  (fn-wmc-state (fn-wmc-node :decode patterns group 0 nil) nil))

(defun fn-wmc-start-codepoints (patterns target)
  (declare (xargs :guard t))
  (fn-wmc-state (fn-wmc-node :match patterns target nil nil) nil))

(defun fn-wmc-decidedp (s)
  (declare (xargs :guard t))
  (and (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :return)
       (not (consp (fn-wmc-at 1 s)))))
(defun fn-wmc-matchedp (s)
  (declare (xargs :guard t))
  (if (and (fn-wmc-decidedp s) (fn-wmc-at 1 (fn-wmc-at 0 s))) t nil))

(defun fn-wmc-core-one (s)
  (declare (xargs :guard t))
  (let* ((task (fn-wmc-at 0 s)) (frames (fn-wmc-at 1 s))
         (tag (fn-wmc-at 0 task)) (a (fn-wmc-at 1 task))
         (b (fn-wmc-at 2 task)) (c (fn-wmc-at 3 task)) (d (fn-wmc-at 4 task)))
    (cond
     ((eq tag :decode)
      (if (and (stringp b) (natp c) (< c (length b)))
          (fn-wmc-state (fn-wmc-node :decode a b (1+ c) (cons (char-code (char b c)) d)) frames)
        (fn-wmc-state (fn-wmc-node :reverse a d nil nil) frames)))
     ((eq tag :reverse)
      (if (consp b)
          (fn-wmc-state (fn-wmc-node :reverse a (cdr b) (cons (car b) c) nil) frames)
        (fn-wmc-state (fn-wmc-node :match a c nil nil) frames)))
     ((eq tag :match)
      (fn-wmc-call :right a b nil (fn-wmc-node :match nil nil nil nil) frames))
     ((eq tag :right)
      (if (consp a)
          (fn-wmc-call :right (cdr a) b nil (fn-wmc-node :right (car a) b nil nil) frames)
        (fn-wmc-state (fn-wmc-return nil 0) frames)))
     ((eq tag :pattern)
      (fn-wmc-call :initial b nil nil (fn-wmc-node :initial-pattern a b nil nil) frames))
     ((eq tag :initial)
      (fn-wmc-call :false a nil nil (fn-wmc-node :cons t nil nil nil) frames))
     ((eq tag :false)
      (if (consp a)
          (fn-wmc-call :false (cdr a) nil nil (fn-wmc-node :cons nil nil nil nil) frames)
        (fn-wmc-state (fn-wmc-return nil 0) frames)))
     ((eq tag :row)
      (if (consp a)
          (fn-wmc-call (if (equal (car a) 42) :star :character) b c (car a)
                       (fn-wmc-node :row-step (cdr a) b nil nil) frames)
        (fn-wmc-state (fn-wmc-return c 0) frames)))
     ((eq tag :star)
      (fn-wmc-call :star-aux a (fn-ag-cdr b) (fn-ag-car b)
                   (fn-wmc-node :cons (fn-ag-car b) nil nil nil) frames))
     ((eq tag :star-aux)
      (if (consp a)
          (let ((carry (if (or (fn-ag-car b) c) t nil)))
            (fn-wmc-call :star-aux (cdr a) (fn-ag-cdr b) carry
                         (fn-wmc-node :cons carry nil nil nil) frames))
        (fn-wmc-state (fn-wmc-return nil 0) frames)))
     ((eq tag :character)
      (fn-wmc-call :char-aux a b c (fn-wmc-node :cons nil nil nil nil) frames))
     ((eq tag :char-aux)
      (if (consp a)
          (fn-wmc-call :char-aux (cdr a) (fn-ag-cdr b) c
                       (fn-wmc-node :cons
                                    (if (and (consp b)
                                             (fn-wildmat-item-character-matchp c (car a)))
                                        (if (car b) t nil) nil) nil nil nil) frames)
        (fn-wmc-state (fn-wmc-return nil 0) frames)))
     ((eq tag :last)
      (if (consp (fn-ag-cdr a))
          (fn-wmc-call :last (fn-ag-cdr a) nil nil (fn-wmc-node :last nil nil nil nil) frames)
        (fn-wmc-state (fn-wmc-return (fn-ag-car a) (if (consp a) 1 0)) frames)))
     ((eq tag :return)
      (if (not (consp frames)) s
        (let* ((frame (car frames)) (rest (cdr frames))
               (kind (fn-wmc-at 0 frame)) (x (fn-wmc-at 1 frame)) (y (fn-wmc-at 2 frame)))
          (cond
           ((eq kind :cons) (fn-wmc-state (fn-wmc-return (cons x a) (1+ (nfix b))) rest))
           ((eq kind :match)
            (fn-wmc-state (fn-wmc-return (if a (eq (fn-ag-car a) :positive) nil) (1+ (nfix b))) rest))
           ((eq kind :right)
            (if a (fn-wmc-state (fn-wmc-return a (1+ (nfix b))) rest)
              (fn-wmc-call :pattern (fn-ag-car (fn-ag-cdr x)) y nil
                           (fn-wmc-node :right-pattern x (1+ (nfix b)) nil nil) rest)))
           ((eq kind :right-pattern)
            (fn-wmc-state (fn-wmc-return (if a x nil) (+ (nfix y) (nfix b))) rest))
           ((eq kind :initial-pattern)
            (fn-wmc-call :row x y a (fn-wmc-node :pattern-row (nfix b) nil nil nil) rest))
           ((eq kind :pattern-row)
            (fn-wmc-call :last a nil nil (fn-wmc-node :pattern-last (+ (nfix x) (nfix b)) nil nil nil) rest))
           ((eq kind :pattern-last)
            (fn-wmc-state (fn-wmc-return (if a t nil) (+ (nfix x) (nfix b))) rest))
           ((eq kind :row-step)
            (fn-wmc-call :row x y a (fn-wmc-node :row-tail (1+ (nfix b)) nil nil nil) rest))
           ((eq kind :row-tail)
            (fn-wmc-state (fn-wmc-return a (+ (nfix x) (nfix b))) rest))
           ((eq kind :last) (fn-wmc-state (fn-wmc-return a (1+ (nfix b))) rest))
           (t (fn-wmc-state (fn-wmc-return a b) rest))))))
     (t (fn-wmc-state (fn-wmc-return nil 0) frames)))))

(defun fn-wmc-core-demand (s)
  (declare (xargs :guard t))
  (if (fn-wmc-decidedp s) 0 13))
(defun fn-wmc-core-acceptedp (s work cons-grant)
  (declare (xargs :guard t))
  (and (not (fn-wmc-decidedp s)) (posp work) (<= 13 (nfix cons-grant))))
(defun fn-wmc-core-step (s work cons-grant)
  (declare (xargs :guard t))
  (if (fn-wmc-core-acceptedp s work cons-grant) (fn-wmc-core-one s) s))
(defun fn-wmc-core-consumed-work (s work cons-grant)
  (declare (xargs :guard t))
  (if (fn-wmc-core-acceptedp s work cons-grant) 1 0))
(defun fn-wmc-core-consumed-cons (s work cons-grant)
  (declare (xargs :guard t))
  ; Conservative charge, not a physical-byte tariff or heap settlement.
  (if (fn-wmc-core-acceptedp s work cons-grant) 13 0))

(defun fn-wmc-core-work-left (s work cons-grant)
  (declare (xargs :guard t))
  (- (nfix work) (fn-wmc-core-consumed-work s work cons-grant)))
(defun fn-wmc-core-cons-left (s work cons-grant)
  (declare (xargs :guard t))
  (- (nfix cons-grant) (fn-wmc-core-consumed-cons s work cons-grant)))
(defthm fn-wmc-core-work-left-natural
  (natp (fn-wmc-core-work-left s work cons-grant)) :rule-classes :type-prescription)
(defthm fn-wmc-core-cons-left-natural
  (natp (fn-wmc-core-cons-left s work cons-grant)) :rule-classes :type-prescription)
(defthm fn-wmc-core-work-conservation
  (equal (+ (fn-wmc-core-consumed-work s work cons-grant) (fn-wmc-core-work-left s work cons-grant))
         (nfix work)))
(defthm fn-wmc-core-cons-conservation
  (equal (+ (fn-wmc-core-consumed-cons s work cons-grant) (fn-wmc-core-cons-left s work cons-grant))
         (nfix cons-grant)))

 ; Proof-only cumulative charge recurrence; the served caller uses ONE STEP.
(defun fn-wmc-core-run-cons (s work cons-grant)
  (declare (xargs :verify-guards nil :measure (nfix work)))
  (if (fn-wmc-core-acceptedp s work cons-grant)
      (+ (fn-wmc-core-consumed-cons s work cons-grant)
         (fn-wmc-core-run-cons (fn-wmc-core-step s work cons-grant)
                          (fn-wmc-core-work-left s work cons-grant)
                          (fn-wmc-core-cons-left s work cons-grant))) 0))
(defthm fn-wmc-core-cumulative-cons-bound
  (<= (fn-wmc-core-run-cons s work cons-grant) (nfix cons-grant))
  :hints (("Goal" :induct (fn-wmc-core-run-cons s work cons-grant)
           :in-theory (disable fn-wmc-core-step fn-wmc-core-one fn-wmc-decidedp))))

; The interpreter below is a proof residual, never called by ONE or STEP.
(defun fn-wmc-task-result (task)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tag (fn-wmc-at 0 task)) (a (fn-wmc-at 1 task)) (b (fn-wmc-at 2 task))
        (c (fn-wmc-at 3 task)) (d (fn-wmc-at 4 task)))
    (cond
     ((eq tag :decode)
      (fn-wm-match-codepoints-work a
       (revappend d (if (stringp b)
                        (fn-nntp-string-octets-aux (nthcdr (nfix c) (coerce b 'list))) nil))))
     ((eq tag :reverse) (fn-wm-match-codepoints-work a (revappend b c)))
     ((eq tag :match) (fn-wm-match-codepoints-work a b))
     ((eq tag :right) (fn-wm-rightmost-match-work a b))
     ((eq tag :pattern) (fn-wm-pattern-match-work a b))
     ((eq tag :initial) (fn-wm-initial-row-work a))
     ((eq tag :false) (fn-wm-false-row-work a))
     ((eq tag :row) (fn-wm-pattern-row-work a b c))
     ((eq tag :star) (fn-wm-step-star-work a b))
     ((eq tag :star-aux) (fn-wm-step-star-aux-work a b c))
     ((eq tag :character) (fn-wm-step-character-work a b c))
     ((eq tag :char-aux) (fn-wm-step-character-aux-work a b c))
     ((eq tag :last) (fn-wm-row-last-work a))
     ((eq tag :return) (fn-wm-work-result a b))
     (t (fn-wm-work-result nil 0)))))

(defun fn-wmc-frame-result (frame result)
  (declare (xargs :guard t :verify-guards nil))
  (let ((kind (fn-wmc-at 0 frame)) (x (fn-wmc-at 1 frame)) (y (fn-wmc-at 2 frame))
        (a (fn-wm-work-value result)) (b (fn-wm-work-cost result)))
    (cond
     ((eq kind :cons) (fn-wm-work-result (cons x a) (1+ (nfix b))))
     ((eq kind :match) (fn-wm-work-result (if a (eq (fn-ag-car a) :positive) nil) (1+ (nfix b))))
     ((eq kind :right)
      (if a (fn-wm-work-result a (1+ (nfix b)))
        (let ((p (fn-wm-pattern-match-work (fn-ag-car (fn-ag-cdr x)) y)))
          (fn-wm-work-result (if (fn-wm-work-value p) x nil)
                             (+ 1 (nfix b) (fn-wm-work-cost p))))))
     ((eq kind :right-pattern) (fn-wm-work-result (if a x nil) (+ (nfix y) (nfix b))))
     ((eq kind :initial-pattern)
      (let* ((row (fn-wm-pattern-row-work x y a)) (last (fn-wm-row-last-work (fn-wm-work-value row))))
        (fn-wm-work-result (if (fn-wm-work-value last) t nil)
                           (+ (nfix b) (fn-wm-work-cost row) (fn-wm-work-cost last)))))
     ((eq kind :pattern-row)
      (let ((last (fn-wm-row-last-work a)))
        (fn-wm-work-result (if (fn-wm-work-value last) t nil) (+ (nfix x) (nfix b) (fn-wm-work-cost last)))))
     ((eq kind :pattern-last) (fn-wm-work-result (if a t nil) (+ (nfix x) (nfix b))))
     ((eq kind :row-step)
      (let ((tail (fn-wm-pattern-row-work x y a)))
        (fn-wm-work-result (fn-wm-work-value tail) (+ 1 (nfix b) (fn-wm-work-cost tail)))))
     ((eq kind :row-tail) (fn-wm-work-result a (+ (nfix x) (nfix b))))
     ((eq kind :last) (fn-wm-work-result a (1+ (nfix b))))
     (t (fn-wm-work-result a b)))))

(defun fn-wmc-resume (frames result)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp frames)
      (fn-wmc-resume (cdr frames) (fn-wmc-frame-result (car frames) result)) result))
(defun fn-wmc-core-result (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-wmc-resume (fn-wmc-at 1 s) (fn-wmc-task-result (fn-wmc-at 0 s))))
(defun fn-wmc-core-value (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-wm-work-value (fn-wmc-core-result s)))

(defthm fn-wmc-core-unfunded-step-is-identical
  (implies (not (fn-wmc-core-acceptedp s work cons-grant))
           (equal (fn-wmc-core-step s work cons-grant) s)))
(defthm fn-wmc-core-step-work-bound
  (<= (fn-wmc-core-consumed-work s work cons-grant) (nfix work))
  :rule-classes :linear)
(defthm fn-wmc-core-step-cons-bound
  (<= (fn-wmc-core-consumed-cons s work cons-grant) (nfix cons-grant))
  :rule-classes :linear)

(local
 (defthm fn-wmc-right-cost-natp
   (natp (fn-wm-work-cost (fn-wm-rightmost-match-work patterns target)))
   :hints (("Goal" :induct (fn-wm-pattern-list-induct patterns)
            :in-theory (e/d (fn-wm-rightmost-match-work fn-wm-work-cost fn-wm-work-value)
                             (fn-wm-pattern-match-work))))))

(local
 (defthm fn-wmc-match-cost-natp
   (natp (fn-wm-work-cost (fn-wm-match-codepoints-work patterns target)))
   :hints (("Goal" :use (fn-wm-match-codepoints-work-cost-decomposition fn-wmc-right-cost-natp)
            :in-theory (disable fn-wm-work-cost fn-wm-match-codepoints-work
                                fn-wm-rightmost-match-work fn-wmc-right-cost-natp)))))

(local
 (defthm fn-wmc-right-cost-cadr-natp
   (natp (cadr (fn-wm-rightmost-match-work patterns target)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :use fn-wmc-right-cost-natp
            :in-theory (e/d (fn-wm-work-cost)
                             (fn-wmc-right-cost-natp fn-wm-rightmost-match-work))))))

(local
 (defthm fn-wmc-pattern-cost-cadr-natp
   (natp (cadr (fn-wm-pattern-match-work items target)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :use fn-wm-pattern-match-work-cost
            :in-theory (e/d (fn-wm-work-cost)
                             (fn-wm-pattern-match-work fn-wm-pattern-match-work-cost))))))

(local
 (defthm fn-wmc-resume-cons
   (equal (fn-wmc-resume (cons frame frames) result)
          (fn-wmc-resume frames (fn-wmc-frame-result frame result)))
   :hints (("Goal" :expand ((fn-wmc-resume (cons frame frames) result))
            :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))))))

(local
 (defthm fn-wmc-resume-open
   (implies (consp frames)
            (equal (fn-wmc-resume frames result)
                   (fn-wmc-resume (cdr frames) (fn-wmc-frame-result (car frames) result))))
   :hints (("Goal" :expand ((fn-wmc-resume frames result))
            :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))))))

(local
 (defthm fn-wmc-nthcdr-open
   (implies (and (natp k) (< k (len xs)))
            (equal (nthcdr k xs) (cons (nth k xs) (nthcdr (1+ k) xs))))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-wmc-octets-at-offset
   (implies (and (stringp text) (natp k) (< k (length text)))
            (equal (fn-nntp-string-octets-aux (nthcdr k (coerce text 'list)))
                   (cons (char-code (char text k))
                         (fn-nntp-string-octets-aux (nthcdr (1+ k) (coerce text 'list))))))
   :hints (("Goal" :in-theory (e/d (char fn-nntp-string-octets-aux) (nthcdr))
            :use ((:instance fn-wmc-nthcdr-open (xs (coerce text 'list))))))))

(local
 (defthm fn-wmc-octets-past-offset
   (implies (and (natp k) (<= (len xs) k))
            (equal (fn-nntp-string-octets-aux (nthcdr k xs)) nil))
   :hints (("Goal" :in-theory (enable nthcdr fn-nntp-string-octets-aux)))))

(local
 (defthm fn-wmc-distribute-left
   (equal (* (+ 1 x) y) (+ y (* x y)))
   :hints (("Goal" :in-theory (enable distributivity commutativity-of-*)))))

(defthm fn-wmc-core-one-preserves-result
  (implies (or (not (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode))
               (natp (fn-wmc-at 3 (fn-wmc-at 0 s))))
           (equal (fn-wmc-core-result (fn-wmc-core-one s)) (fn-wmc-core-result s)))
  :hints (("Goal" :in-theory
           (e/d (fn-wmc-core-result fn-wmc-task-result fn-wmc-frame-result fn-wmc-core-one
                  fn-wm-work-result fn-wm-work-value fn-wm-work-cost
                  fn-ag-car fn-ag-cdr revappend
                  fn-wm-match-codepoints-work fn-wm-rightmost-match-work
                  fn-wm-pattern-match-work fn-wm-pattern-row-work
                  fn-wm-initial-row-work fn-wm-false-row-work
                  fn-wm-step-character-work fn-wm-step-character-aux-work
                  fn-wm-step-star-work fn-wm-step-star-aux-work fn-wm-row-last-work)
                 (fn-wmc-resume fn-nntp-string-octets-aux nthcdr char revappend-removal fn-wmc-nthcdr-open
                  fn-wildmat-item-character-matchp fn-wildmat-text-exactp)))))

(defun fn-wmc-framesp (frames)
  (declare (xargs :guard t))
  (if (consp frames)
      (and (true-listp (car frames)) (equal (len (car frames)) 5)
           (fn-wmc-framesp (cdr frames))) (null frames)))
(defun fn-wmc-core-shapedp (s)
  (declare (xargs :guard t))
  (let ((task (fn-wmc-at 0 s)))
    (and (true-listp s) (equal (len s) 2)
         (true-listp task) (equal (len task) 5)
         (fn-wmc-framesp (fn-wmc-at 1 s))
         (or (not (eq (fn-wmc-at 0 task) :decode)) (natp (fn-wmc-at 3 task))))))

(defthm fn-wmc-core-start-has-shape
  (fn-wmc-core-shapedp (fn-wmc-core-start patterns group)))
(defthm fn-wmc-core-one-preserves-shape
  (implies (fn-wmc-core-shapedp s) (fn-wmc-core-shapedp (fn-wmc-core-one s))))
(defthm fn-wmc-core-step-preserves-shape
  (implies (fn-wmc-core-shapedp s) (fn-wmc-core-shapedp (fn-wmc-core-step s work cons-grant)))
  :hints (("Goal" :in-theory (disable fn-wmc-core-one fn-wmc-core-shapedp))))

(defthm fn-wmc-core-step-preserves-result
  (implies (fn-wmc-core-shapedp s)
           (equal (fn-wmc-core-result (fn-wmc-core-step s work cons-grant)) (fn-wmc-core-result s)))
  :hints (("Goal" :in-theory (disable fn-wmc-core-one fn-wmc-core-result))))

(defthm fn-wmc-core-step-preserves-value
  (implies (fn-wmc-core-shapedp s)
           (equal (fn-wmc-core-value (fn-wmc-core-step s work cons-grant)) (fn-wmc-core-value s)))
  :hints (("Goal" :in-theory (e/d (fn-wmc-core-value) (fn-wmc-core-result fn-wmc-core-step fn-wmc-core-shapedp)))))

(defthm fn-wmc-core-codepoints-result-is-work
  (equal (fn-wmc-core-result (fn-wmc-start-codepoints patterns target))
         (fn-wm-match-codepoints-work patterns target))
  :hints (("Goal" :in-theory (enable fn-wmc-core-result fn-wmc-resume fn-wmc-task-result))))

(defthm fn-wmc-core-decided-value
  (implies (fn-wmc-decidedp s)
           (equal (fn-wmc-matchedp s) (if (fn-wmc-core-value s) t nil)))
  :hints (("Goal" :in-theory (enable fn-wmc-core-value fn-wmc-core-result fn-wmc-task-result fn-wmc-resume))))

; Constructor-level logical cell recurrence. At most one call frame is pushed
; in a microstep: state2 + task5 + frame5 + stack-link1. Decode/row cons steps
; allocate state2 + task5 + one data cell. This excludes caller/mux/collector
; envelopes and integer storage; it is not a physical heap-byte guarantee.
(defun fn-wmc-core-one-cons-cells (s)
  (declare (xargs :guard t))
  (let* ((task (fn-wmc-at 0 s)) (tag (fn-wmc-at 0 task))
         (a (fn-wmc-at 1 task)) (b (fn-wmc-at 2 task)) (c (fn-wmc-at 3 task))
         (frames (fn-wmc-at 1 s)) (frame (fn-ag-car frames)) (kind (fn-wmc-at 0 frame)))
    (cond
     ((eq tag :decode) (if (and (stringp b) (natp c) (< c (length b))) 8 7))
     ((eq tag :reverse) (if (consp b) 8 7))
     ((member-eq tag '(:match :pattern :initial :star :character)) 13)
     ((member-eq tag '(:right :false :row :star-aux :char-aux)) (if (consp a) 13 7))
     ((eq tag :last) (if (consp (fn-ag-cdr a)) 13 7))
     ((eq tag :return)
      (cond ((not (consp frames)) 0)
            ((eq kind :cons) 8)
            ((and (eq kind :right) (not a)) 13)
            ((member-eq kind '(:initial-pattern :pattern-row :row-step)) 13)
            (t 7)))
     (t 7))))

(defthm fn-wmc-core-one-cons-cells-bound
  (<= (fn-wmc-core-one-cons-cells s) (fn-wmc-core-demand s))
  :rule-classes :linear)
(defthm fn-wmc-core-accepted-cons-cells-covered
  (implies (fn-wmc-core-acceptedp s work cons-grant)
           (<= (fn-wmc-core-one-cons-cells s) (fn-wmc-core-consumed-cons s work cons-grant)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-wmc-core-one-cons-cells))))

(defun fn-wmc-ascii-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (< (car xs) 128) (fn-wmc-ascii-octetsp (cdr xs))) (null xs)))

(local
 (defthm fn-wmc-printable-is-ascii
   (implies (and (fn-nntp-printable-tokenp xs) (true-listp xs)) (fn-wmc-ascii-octetsp xs))
   :hints (("Goal" :induct (fn-nntp-printable-tokenp xs)
            :in-theory (enable fn-nntp-printable-tokenp)))))

(local
 (defthm fn-wmc-ascii-is-octets
   (implies (fn-wmc-ascii-octetsp xs) (fn-wildmat-octet-listp xs))
   :hints (("Goal" :induct (fn-wmc-ascii-octetsp xs)
            :in-theory (enable fn-wildmat-octet-listp fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-wmc-ascii-decode-aux
   (implies (and (fn-wmc-ascii-octetsp xs) (true-listp acc))
            (equal (fn-wildmat-decode-aux xs acc) (fn-wildmat-ok (revappend acc xs))))
   :hints (("Goal" :induct (fn-wildmat-decode-aux xs acc)
            :in-theory (e/d (fn-wildmat-decode-aux fn-wildmat-utf8-next
                             fn-wildmat-octetp fn-cbor-octetp fn-wildmat-utf8-ok
                             fn-wildmat-result-okp fn-wildmat-result-value
                             fn-wildmat-utf8-rest fn-wildmat-ok reverse revappend)
                            (revappend-removal reverse-removal))))))

(local
 (defthm fn-wmc-length-preflight
   (implies (and (natp bound) (true-listp xs) (<= (len xs) bound))
            (fn-wildmat-at-mostp xs bound))
   :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
            :in-theory (enable fn-wildmat-at-mostp fn-cbor-at-mostp)))))

(defthm fn-wmc-ascii-decoded-value
  (implies (and (fn-wmc-ascii-octetsp xs) (true-listp xs)
                (<= (len xs) *fn-wildmat-max-octets*))
           (equal (fn-wildmat-decode xs) (fn-wildmat-ok xs)))
  :hints (("Goal" :in-theory (e/d (fn-wildmat-decode) (fn-wildmat-decode-aux)))))

(local
 (defthm fn-wmc-string-octets-true-listp
   (true-listp (fn-nntp-string-octets group))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets fn-nntp-string-octets-aux)))))

(defthm fn-wmc-core-start-value-is-group-match
  (implies (fn-nntp-safe-group-namep group)
           (equal (fn-wmc-core-value (fn-wmc-core-start patterns group))
                  (fn-nntp-group-matches-parsed-wildmatp patterns group)))
  :hints (("Goal" :in-theory
           (e/d (fn-wmc-core-value fn-wmc-core-result fn-wmc-task-result fn-wmc-resume
                  fn-nntp-group-matches-parsed-wildmatp fn-nntp-safe-group-namep
                  fn-nntp-string-octets fn-wildmat-result-okp fn-wildmat-result-value fn-wildmat-ok)
                 (fn-nntp-string-octets-aux fn-wildmat-decode fn-wm-match-codepoints-work)))))

; Exact future machine work, separate from the frozen DP worker's work cost.
; These are logical potential functions: no runtime LEN, matcher or stack walk.
(defun fn-wmc-row-steps (items target)
  (+ 1 (* (len items) (+ 6 (* 2 (len target))))))
(defun fn-wmc-last-steps (row)
  (if (consp row) (1- (* 2 (len row))) 1))
(defun fn-wmc-pattern-steps (items target)
  (+ 9 (* 4 (len target)) (* (len items) (+ 6 (* 2 (len target))))))
(defun fn-wmc-right-steps (patterns target)
  (if (consp patterns)
      (+ (fn-wmc-right-steps (cdr patterns) target)
         (if (fn-wildmat-rightmost-match (cdr patterns) target) 2
           (+ 3 (fn-wmc-pattern-steps (fn-wildmat-pattern-items (car patterns)) target))))
    1))
(defun fn-wmc-match-steps (patterns target)
  (+ 2 (fn-wmc-right-steps patterns target)))

(defun fn-wmc-task-steps (task)
  (let ((tag (fn-wmc-at 0 task)) (a (fn-wmc-at 1 task)) (b (fn-wmc-at 2 task))
        (c (fn-wmc-at 3 task)) (d (fn-wmc-at 4 task)))
    (cond
     ((eq tag :decode)
      (+ (* 2 (if (stringp b) (nfix (- (length b) (nfix c))) 0)) (len d) 2
         (fn-wmc-match-steps a (revappend d
          (if (stringp b) (fn-nntp-string-octets-aux (nthcdr (nfix c) (coerce b 'list))) nil)))))
     ((eq tag :reverse) (+ (len b) 1 (fn-wmc-match-steps a (revappend b c))))
     ((eq tag :match) (fn-wmc-match-steps a b))
     ((eq tag :right) (fn-wmc-right-steps a b))
     ((eq tag :pattern) (fn-wmc-pattern-steps a b))
     ((member-eq tag '(:initial :star :character)) (+ 3 (* 2 (len a))))
     ((member-eq tag '(:false :star-aux :char-aux)) (+ 1 (* 2 (len a))))
     ((eq tag :row) (fn-wmc-row-steps a b))
     ((eq tag :last) (fn-wmc-last-steps a))
     ((eq tag :return) 0)
     (t 1))))

(defun fn-wmc-frame-steps (frame result)
  (let ((kind (fn-wmc-at 0 frame)) (x (fn-wmc-at 1 frame)) (y (fn-wmc-at 2 frame))
        (value (fn-wm-work-value result)))
    (cond
     ((eq kind :right)
      (if value 1 (+ 2 (fn-wmc-pattern-steps (fn-wildmat-pattern-items x) y))))
     ((eq kind :initial-pattern)
      (+ 3 (fn-wmc-row-steps x y)
         (fn-wmc-last-steps (fn-wm-work-value (fn-wm-pattern-row-work x y value)))))
     ((eq kind :pattern-row) (+ 2 (fn-wmc-last-steps value)))
     ((eq kind :row-step) (+ 2 (fn-wmc-row-steps x y)))
     (t 1))))
(defun fn-wmc-stack-steps (frames result)
  (if (consp frames)
      (+ (fn-wmc-frame-steps (car frames) result)
         (fn-wmc-stack-steps (cdr frames) (fn-wmc-frame-result (car frames) result))) 0))
(defun fn-wmc-core-remaining (s)
  (+ (fn-wmc-task-steps (fn-wmc-at 0 s))
     (fn-wmc-stack-steps (fn-wmc-at 1 s) (fn-wmc-task-result (fn-wmc-at 0 s)))))

(local
 (defthm fn-wmc-positive-len
   (implies (consp x) (< 0 (len x)))
   :rule-classes :linear))
(local
 (defthm fn-wmc-stack-steps-open
   (implies (consp frames)
            (equal (fn-wmc-stack-steps frames result)
                   (+ (fn-wmc-frame-steps (car frames) result)
                      (fn-wmc-stack-steps (cdr frames) (fn-wmc-frame-result (car frames) result)))))
   :hints (("Goal" :expand ((fn-wmc-stack-steps frames result))
            :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))))))

(local
 (defthm fn-wmc-stack-steps-cons
   (equal (fn-wmc-stack-steps (cons frame frames) result)
          (+ (fn-wmc-frame-steps frame result)
             (fn-wmc-stack-steps frames (fn-wmc-frame-result frame result))))
   :hints (("Goal" :expand ((fn-wmc-stack-steps (cons frame frames) result))
            :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))))))

(local
 (defthm fn-wmc-character-row-length
   (equal (len (fn-wildmat-step-character-aux target previous item)) (len target))
   :hints (("Goal" :induct (fn-wildmat-step-character-aux target previous item)
            :in-theory (e/d (fn-wildmat-step-character-aux)
                             (fn-wildmat-item-character-matchp))))))
(local
 (defthm fn-wmc-star-row-length
   (equal (len (fn-wildmat-step-star-aux target previous carry)) (len target))
   :hints (("Goal" :induct (fn-wildmat-step-star-aux target previous carry)
            :in-theory (enable fn-wildmat-step-star-aux)))))
(local
 (defthm fn-wmc-pattern-row-length
   (equal (len (fn-wildmat-pattern-row items target row))
          (if (consp items) (1+ (len target)) (len row)))
   :hints (("Goal" :induct (fn-wildmat-pattern-row items target row)
            :in-theory (e/d (fn-wildmat-pattern-row fn-wildmat-step-star fn-wildmat-step-character)
                             (fn-wildmat-step-star-aux fn-wildmat-step-character-aux))))))

(local
 (defthm fn-wmc-pattern-row-consp
   (implies (consp items) (consp (fn-wildmat-pattern-row items target row)))
   :hints (("Goal" :induct (fn-wildmat-pattern-row items target row)
            :in-theory (e/d (fn-wildmat-pattern-row fn-wildmat-step-star fn-wildmat-step-character)
                             (fn-wildmat-step-star-aux fn-wildmat-step-character-aux))))))

(local
 (defthm fn-wmc-len-cdr-fact
   (equal (len (cdr x)) (if (consp x) (1- (len x)) 0))
   :rule-classes nil))
(local
 (defthm fn-wmc-pattern-row-cdr-length
   (equal (len (cdr (fn-wildmat-pattern-row items target row)))
          (if (consp items) (len target) (len (cdr row))))
   :hints (("Goal" :use ((:instance fn-wmc-pattern-row-length)
                                 (:instance fn-wmc-len-cdr-fact (x (fn-wildmat-pattern-row items target row))))
            :in-theory (e/d (len) (fn-wildmat-pattern-row))))))

(defthm fn-wmc-core-one-progress
  (implies (and (fn-wmc-core-shapedp s) (not (fn-wmc-decidedp s)))
           (equal (fn-wmc-core-remaining (fn-wmc-core-one s)) (1- (fn-wmc-core-remaining s))))
  :hints (("Goal" :cases ((eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :return))
           :in-theory
           (e/d (fn-wmc-core-remaining fn-wmc-task-steps fn-wmc-frame-steps fn-wmc-core-one
                  fn-wmc-task-result fn-wmc-frame-result fn-wm-work-result
                  fn-wm-work-value fn-wm-work-cost fn-ag-car fn-ag-cdr revappend
                  fn-wm-match-codepoints-work fn-wm-rightmost-match-work
                  fn-wm-pattern-match-work fn-wm-pattern-row-work
                  fn-wm-initial-row-work fn-wm-false-row-work
                  fn-wm-step-character-work fn-wm-step-character-aux-work
                  fn-wm-step-star-work fn-wm-step-star-aux-work fn-wm-row-last-work)
                 (fn-wmc-stack-steps fn-wmc-stack-steps-open fn-nntp-string-octets-aux nthcdr char
                  revappend-removal fn-wmc-nthcdr-open
                  fn-wildmat-item-character-matchp fn-wildmat-text-exactp)))
          ("Subgoal 1" :in-theory (e/d (fn-wmc-stack-steps-open fn-wmc-task-result fn-wmc-frame-result)
                                       (fn-wmc-stack-steps fn-wildmat-item-character-matchp
                                        fn-wildmat-text-exactp)))))

(local
 (defthm fn-wmc-frame-steps-natural
   (natp (fn-wmc-frame-steps frame result))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (e/d (fn-wmc-frame-steps fn-wmc-last-steps)
                                   (fn-wm-pattern-row-work))))))
(local
 (defthm fn-wmc-stack-steps-natural
   (natp (fn-wmc-stack-steps frames result))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (fn-wmc-stack-steps frames result)
            :in-theory (e/d (fn-wmc-stack-steps)
                            (fn-wmc-frame-steps fn-wmc-frame-result))))))
(local
 (defthm fn-wmc-task-steps-natural
   (natp (fn-wmc-task-steps task))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-wmc-task-steps fn-wmc-last-steps)))))

(defthm fn-wmc-core-remaining-natural
  (natp (fn-wmc-core-remaining s))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-wmc-core-remaining fn-wmc-task-steps fn-wmc-frame-steps
                                   fn-wmc-stack-steps fn-wmc-row-steps fn-wmc-last-steps
                                   fn-wmc-pattern-steps fn-wmc-right-steps fn-wmc-match-steps)
                                  (fn-wmc-task-result fn-wmc-frame-result fn-wmc-core-one
                                   fn-wildmat-rightmost-match fn-wm-pattern-row-work)))))
(defthm fn-wmc-core-live-remaining-positive
  (implies (and (fn-wmc-core-shapedp s) (not (fn-wmc-decidedp s)))
           (< 0 (fn-wmc-core-remaining s)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-wmc-core-remaining fn-wmc-task-steps fn-wmc-frame-steps
                                   fn-wmc-stack-steps fn-wmc-row-steps fn-wmc-last-steps
                                   fn-wmc-pattern-steps fn-wmc-right-steps fn-wmc-match-steps)
                                  (fn-wmc-task-result fn-wmc-frame-result fn-wmc-core-one
                                   fn-wildmat-rightmost-match fn-wm-pattern-row-work)))))
(defthm fn-wmc-core-funded-step-progress
  (implies (fn-wmc-core-shapedp s)
           (equal (fn-wmc-core-remaining (fn-wmc-core-step s work cons-grant))
                  (- (fn-wmc-core-remaining s) (fn-wmc-core-consumed-work s work cons-grant))))
  :hints (("Goal" :in-theory (disable fn-wmc-core-one fn-wmc-core-remaining fn-wmc-core-shapedp))))

(defthm fn-wmc-right-steps-bound
  (<= (fn-wmc-right-steps patterns target)
      (+ 1 (* 12 (len patterns)) (* 4 (len patterns) (len target))
         (* (fn-wm-total-items patterns) (+ 6 (* 2 (len target))))))
  :hints (("Goal" :induct (fn-wmc-right-steps patterns target)
           :in-theory (e/d (fn-wmc-right-steps fn-wmc-pattern-steps fn-wm-total-items)
                            (fn-wildmat-rightmost-match)))))
(defthm fn-wmc-core-codepoint-start-work-bound
  (<= (fn-wmc-core-remaining (fn-wmc-start-codepoints patterns target))
      (+ 3 (* 12 (len patterns)) (* 4 (len patterns) (len target))
         (* (fn-wm-total-items patterns) (+ 6 (* 2 (len target))))))
  :hints (("Goal" :use ((:instance fn-wmc-right-steps-bound)) :in-theory
           (e/d (fn-wmc-core-remaining fn-wmc-task-steps fn-wmc-match-steps fn-wmc-stack-steps)
                 (fn-wmc-right-steps fn-wmc-task-result fn-wmc-right-steps-bound fn-wm-total-items)))))

(defthm fn-wmc-core-start-work-bound
  (implies (stringp group)
           (<= (fn-wmc-core-remaining (fn-wmc-core-start patterns group))
               (+ 5 (* 2 (length group)) (* 12 (len patterns))
                  (* 4 (len patterns) (len (fn-nntp-string-octets group)))
                  (* (fn-wm-total-items patterns)
                     (+ 6 (* 2 (len (fn-nntp-string-octets group))))))))
  :hints (("Goal" :use ((:instance fn-wmc-right-steps-bound
                                  (target (fn-nntp-string-octets group))))
           :in-theory (e/d (fn-wmc-core-remaining fn-wmc-task-steps fn-wmc-match-steps
                             fn-wmc-stack-steps fn-nntp-string-octets revappend)
                            (fn-wmc-right-steps fn-wmc-task-result fn-wmc-right-steps-bound
                             fn-nntp-string-octets-aux fn-wm-total-items)))))
(defthm fn-wmc-supported-name-profile
  (implies (fn-nntp-safe-group-namep group)
           (and (stringp group)
                (fn-wmc-ascii-octetsp (fn-nntp-string-octets group))
                (<= (len (fn-nntp-string-octets group)) *fn-nntp-max-group-octets*)
                (< *fn-nntp-max-group-octets* *fn-wildmat-max-octets*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nntp-safe-group-namep))))

(in-theory (disable fn-wmc-core-run-cons fn-wmc-task-result fn-wmc-frame-result fn-wmc-resume fn-wmc-core-result fn-wmc-core-value
                    fn-wmc-task-steps fn-wmc-frame-steps fn-wmc-stack-steps fn-wmc-core-remaining
                    fn-wmc-right-steps fn-wmc-match-steps fn-wmc-row-steps fn-wmc-pattern-steps fn-wmc-last-steps))

(local (include-book "arithmetic/top" :dir :system))
; Total entry extension: retain a string reference and materialize <=4 octets
; for the existing UTF8 decoder. Core DP/refinement remains unchanged above.
(defun fn-wmc-window (text offset fuel)
  (declare (xargs :guard (and (natp offset) (natp fuel)) :measure (nfix fuel)))
  (if (and (not (zp fuel)) (stringp text) (< offset (length text)))
      (cons (char-code (char text offset))
            (fn-wmc-window text (1+ offset) (1- fuel))) nil))
(defun fn-wmc-start (patterns group)
  (declare (xargs :guard t))
  (cond ((not (stringp group)) (fn-wmc-start-codepoints patterns nil))
        ((< *fn-wildmat-max-octets* (length group))
         (fn-wmc-state (fn-wmc-return nil 0) nil))
        (t (fn-wmc-state (fn-wmc-node :utf8 patterns group 0 nil) nil))))
(defun fn-wmc-utf8-one (s)
  (declare (xargs :guard t))
  (let* ((task (fn-wmc-at 0 s)) (patterns (fn-wmc-at 1 task))
         (text (fn-wmc-at 2 task)) (offset (nfix (fn-wmc-at 3 task)))
         (acc (fn-wmc-at 4 task)) (frames (fn-wmc-at 1 s)))
    (if (and (stringp text) (< offset (length text)))
        (let* ((window (fn-wmc-window text offset 4)) (next (fn-wildmat-utf8-next window)))
          (if (fn-wildmat-result-okp next)
              (fn-wmc-state
               (fn-wmc-node :utf8 patterns text
                            (+ offset (- (len window) (len (fn-wildmat-utf8-rest next))))
                            (cons (fn-wildmat-result-value next) acc)) frames)
            (fn-wmc-state (fn-wmc-return nil 0) frames)))
      (fn-wmc-state (fn-wmc-node :reverse patterns acc nil nil) frames))))
(defun fn-wmc-normalize-decode (s)
  (declare (xargs :guard t))
  (let ((task (fn-wmc-at 0 s)))
    (fn-wmc-state (fn-wmc-node :decode (fn-wmc-at 1 task) (fn-wmc-at 2 task)
                              (nfix (fn-wmc-at 3 task)) (fn-wmc-at 4 task))
                  (fn-wmc-at 1 s))))
(defun fn-wmc-one (s)
  (declare (xargs :guard t))
  (let ((task (fn-wmc-at 0 s)))
    (cond ((eq (fn-wmc-at 0 task) :utf8) (fn-wmc-utf8-one s))
          ((eq (fn-wmc-at 0 task) :decode)
           (fn-wmc-core-one (fn-wmc-normalize-decode s)))
          (t (fn-wmc-core-one s)))))
(defun fn-wmc-demand (s)
  (declare (xargs :guard t))
  (if (member-eq (fn-wmc-at 0 (fn-wmc-at 0 s)) '(:utf8 :decode)) 15 (fn-wmc-core-demand s)))
(defun fn-wmc-acceptedp (s work cons-grant)
  (declare (xargs :guard t))
  (and (not (fn-wmc-decidedp s)) (posp work) (<= (fn-wmc-demand s) (nfix cons-grant))))
(defun fn-wmc-step (s work cons-grant)
  (declare (xargs :guard t))
  (if (fn-wmc-acceptedp s work cons-grant) (fn-wmc-one s) s))
(defun fn-wmc-consumed-work (s work cons-grant)
  (declare (xargs :guard t))
  (if (fn-wmc-acceptedp s work cons-grant) 1 0))
(defun fn-wmc-consumed-cons (s work cons-grant)
  (declare (xargs :guard t))
  (if (fn-wmc-acceptedp s work cons-grant) (fn-wmc-demand s) 0))
(defun fn-wmc-work-left (s work cons-grant)
  (declare (xargs :guard t))
  (- (nfix work) (fn-wmc-consumed-work s work cons-grant)))
(defun fn-wmc-cons-left (s work cons-grant)
  (declare (xargs :guard t))
  (- (nfix cons-grant) (fn-wmc-consumed-cons s work cons-grant)))
(defun fn-wmc-shapedp (s)
  (declare (xargs :guard t))
  (and (fn-wmc-core-shapedp s)
       (or (not (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8))
           (and (natp (fn-wmc-at 3 (fn-wmc-at 0 s)))
                (true-listp (fn-wmc-at 4 (fn-wmc-at 0 s)))
                (not (consp (fn-wmc-at 1 s)))))))
(defun fn-wmc-utf8-result (patterns text offset acc)
  (declare (xargs :verify-guards nil))
  (let ((decoded (fn-wildmat-decode-aux
                  (if (stringp text)
                      (fn-nntp-string-octets-aux (nthcdr (nfix offset) (coerce text 'list))) nil) (true-list-fix acc))))
    (if (fn-wildmat-result-okp decoded)
        (fn-wm-match-codepoints-work patterns (fn-wildmat-result-value decoded))
      (fn-wm-work-result nil 0))))
(defun fn-wmc-result (s)
  (declare (xargs :verify-guards nil))
  (let ((task (fn-wmc-at 0 s)))
    (if (eq (fn-wmc-at 0 task) :utf8)
        (fn-wmc-resume (fn-wmc-at 1 s)
                       (fn-wmc-utf8-result (fn-wmc-at 1 task) (fn-wmc-at 2 task)
                                           (fn-wmc-at 3 task) (fn-wmc-at 4 task)))
      (fn-wmc-core-result s))))
(defun fn-wmc-value (s)
  (declare (xargs :verify-guards nil))
  (fn-wm-work-value (fn-wmc-result s)))

(defun fn-wmc-list-window (xs fuel)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (and (not (zp fuel)) (consp xs))
      (cons (car xs) (fn-wmc-list-window (cdr xs) (1- fuel))) nil))
(local
 (defthm fn-wmc-next-window
   (let* ((window (fn-wmc-list-window xs 4)) (next (fn-wildmat-utf8-next window))
          (width (- (len window) (len (fn-wildmat-utf8-rest next)))))
     (equal (fn-wildmat-utf8-next xs)
            (if (fn-wildmat-result-okp next)
                (fn-wildmat-utf8-ok (fn-wildmat-result-value next) (nthcdr width xs)) next)))
   :hints (("Goal" :in-theory (union-theories (theory 'fn-wmc-entry-base) '( fn-wmc-list-window fn-wildmat-utf8-next
                                      fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                                      fn-wildmat-utf8-4-tailsp fn-wildmat-utf8-2-value
                                      fn-wildmat-utf8-3-value fn-wildmat-utf8-4-value
                                      fn-wildmat-result-okp fn-wildmat-result-value
                                      fn-wildmat-utf8-rest fn-wildmat-utf8-ok fn-wildmat-error nthcdr))))))
(local
 (defthm fn-wmc-offset-open
   (implies (and (natp k) (< k (len xs)))
            (equal (nthcdr k xs) (cons (nth k xs) (nthcdr (1+ k) xs))))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))
(local
 (defthm fn-wmc-string-tail-empty
   (implies (and (natp k) (<= (len xs) k))
            (equal (fn-nntp-string-octets-aux (nthcdr k xs)) nil))
   :hints (("Goal" :in-theory (enable nthcdr fn-nntp-string-octets-aux)))))
(local
 (defthm fn-wmc-string-window-is-list-window
   (implies (and (stringp text) (natp offset) (natp fuel))
            (equal (fn-wmc-window text offset fuel)
                   (fn-wmc-list-window
                    (fn-nntp-string-octets-aux (nthcdr offset (coerce text 'list))) fuel)))
   :hints (("Goal" :induct (fn-wmc-window text offset fuel)
            :in-theory (e/d (fn-wmc-window fn-wmc-list-window char fn-nntp-string-octets-aux)
                             (nthcdr))))))
(local (in-theory (disable fn-wmc-next-window)))
(local
 (defthm fn-wmc-next-window-width
   (let* ((window (fn-wmc-list-window xs 4)) (next (fn-wildmat-utf8-next window))
          (width (- (len window) (len (fn-wildmat-utf8-rest next)))))
     (implies (fn-wildmat-result-okp next) (and (natp width) (< 0 width) (<= width 4))))
   :hints (("Goal" :in-theory (enable fn-wmc-list-window fn-wildmat-utf8-next
                                      fn-wildmat-result-okp fn-wildmat-utf8-rest
                                      fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                                      fn-wildmat-utf8-4-tailsp fn-wildmat-utf8-ok fn-wildmat-error)))))
(local
 (defthm fn-wmc-decode-on-window
   (implies (consp xs)
    (let* ((window (fn-wmc-list-window xs 4)) (next (fn-wildmat-utf8-next window))
           (width (- (len window) (len (fn-wildmat-utf8-rest next)))))
      (equal (fn-wildmat-decode-aux xs acc)
             (if (fn-wildmat-result-okp next)
                 (fn-wildmat-decode-aux (nthcdr width xs)
                                       (cons (fn-wildmat-result-value next) acc)) next))))
   :hints (("Goal" :use fn-wmc-next-window
            :expand ((fn-wildmat-decode-aux xs acc))
            :in-theory (enable fn-wildmat-result-okp fn-wildmat-result-value fn-wildmat-utf8-rest
                                fn-wildmat-utf8-ok)))))
(local
 (defthm fn-wmc-nthcdr-octets
   (implies (natp k)
            (equal (nthcdr k (fn-nntp-string-octets-aux chars))
                   (fn-nntp-string-octets-aux (nthcdr k chars))))
   :hints (("Goal" :in-theory (enable nthcdr fn-nntp-string-octets-aux)))))
(local
 (defthm fn-wmc-nthcdr-sum
   (implies (and (natp i) (natp j))
            (equal (nthcdr i (nthcdr j xs)) (nthcdr (+ i j) xs)))
   :hints (("Goal" :in-theory (enable nthcdr)))))
(local
 (defthm fn-wmc-octet-tail-consp
   (implies (and (stringp text) (natp offset) (< offset (length text)))
            (consp (fn-nntp-string-octets-aux (nthcdr offset (coerce text 'list)))))
   :hints (("Goal" :in-theory (e/d (fn-nntp-string-octets-aux) (nthcdr))))))
(local
 (defthm fn-wmc-decode-empty
   (implies (true-listp acc)
            (equal (fn-wildmat-decode-aux nil acc) (fn-wildmat-ok (revappend acc nil))))
   :hints (("Goal" :in-theory (e/d (fn-wildmat-decode-aux reverse revappend)
                                  (revappend-removal reverse-removal))))))
(local (defthm fn-wmc-ok-value (equal (fn-wildmat-result-value (fn-wildmat-ok xs)) xs)))
(local (defthm fn-wmc-ok-ok (fn-wildmat-result-okp (fn-wildmat-ok xs))))

(local
 (defthm fn-wmc-revappend-fixed
   (equal (revappend (true-list-fix acc) tail) (revappend acc tail))
   :hints (("Goal" :induct (true-list-fix acc)
            :in-theory (e/d (true-list-fix revappend) (revappend-removal))))))
(defthm fn-wmc-utf8-one-preserves-result
  (implies (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8)
           (equal (fn-wmc-result (fn-wmc-utf8-one s)) (fn-wmc-result s)))
  :hints (("Goal" :use ((:instance fn-wmc-decode-on-window
                            (xs (fn-nntp-string-octets-aux
                                 (nthcdr (nfix (fn-wmc-at 3 (fn-wmc-at 0 s)))
                                          (coerce (fn-wmc-at 2 (fn-wmc-at 0 s)) 'list))))
                            (acc (true-list-fix (fn-wmc-at 4 (fn-wmc-at 0 s)))))
                            (:instance fn-wmc-next-window-width
                             (xs (fn-nntp-string-octets-aux
                                  (nthcdr (nfix (fn-wmc-at 3 (fn-wmc-at 0 s)))
                                           (coerce (fn-wmc-at 2 (fn-wmc-at 0 s)) 'list))))))
           :in-theory
           (e/d (fn-wmc-result fn-wmc-utf8-result fn-wmc-utf8-one fn-wmc-shapedp
                  fn-wmc-core-shapedp fn-wmc-core-result fn-wmc-task-result true-list-fix
                  fn-wm-work-result fn-wm-work-value fn-wm-work-cost
                  fn-wildmat-ok fn-wildmat-error fn-wildmat-result-okp fn-wildmat-result-value fn-wildmat-utf8-rest reverse revappend)
                 (fn-wmc-resume fn-wmc-decode-on-window fn-wildmat-decode-aux
                  fn-wildmat-utf8-next fn-wmc-window fn-wmc-list-window
                  fn-nntp-string-octets-aux nthcdr char revappend-removal reverse-removal
                  fn-wm-match-codepoints-work fn-wmc-next-window fn-wmc-offset-open fn-wmc-nthcdr-open fn-wmc-octets-at-offset)))))
(local
 (defthm fn-wmc-core-one-not-utf8
   (not (eq (fn-wmc-at 0 (fn-wmc-at 0 (fn-wmc-core-one s))) :utf8))
   :hints (("Goal" :in-theory (enable fn-wmc-core-one)))))
(local
 (defthm fn-wmc-normalize-decode-result
   (implies (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode)
            (equal (fn-wmc-core-result (fn-wmc-normalize-decode s)) (fn-wmc-core-result s)))
   :hints (("Goal" :in-theory (e/d (fn-wmc-normalize-decode fn-wmc-core-result fn-wmc-task-result)
                                   (fn-wmc-resume fn-wm-match-codepoints-work))))))
(local
 (defthm fn-wmc-normalize-decode-shaped
   (implies (and (fn-wmc-core-shapedp s) (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode))
            (fn-wmc-core-shapedp (fn-wmc-normalize-decode s)))
   :hints (("Goal" :in-theory (enable fn-wmc-normalize-decode fn-wmc-core-shapedp fn-wmc-at)))))
(local
 (defthm fn-wmc-normalize-decode-remaining
   (implies (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode)
            (equal (fn-wmc-core-remaining (fn-wmc-normalize-decode s)) (fn-wmc-core-remaining s)))
   :hints (("Goal" :in-theory (e/d (fn-wmc-normalize-decode fn-wmc-core-remaining
                                   fn-wmc-task-steps fn-wmc-task-result)
                                  (fn-wmc-stack-steps fn-wmc-resume fn-wmc-match-steps
                                   fn-wm-match-codepoints-work))))))
(local (defthm fn-wmc-normalize-decode-tag
  (equal (fn-wmc-at 0 (fn-wmc-at 0 (fn-wmc-normalize-decode s))) :decode)))
(local (defthm fn-wmc-normalize-decode-index
  (natp (fn-wmc-at 3 (fn-wmc-at 0 (fn-wmc-normalize-decode s))))))
(defthm fn-wmc-one-preserves-result
  (equal (fn-wmc-result (fn-wmc-one s)) (fn-wmc-result s))
  :hints (("Goal" :cases ((eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8)
                           (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode))
           :use (fn-wmc-core-one-not-utf8 fn-wmc-core-one-preserves-result
                 (:instance fn-wmc-core-one-not-utf8 (s (fn-wmc-normalize-decode s)))
                 (:instance fn-wmc-core-one-preserves-result (s (fn-wmc-normalize-decode s))))
           :in-theory (e/d (fn-wmc-one fn-wmc-result)
                            (fn-wmc-normalize-decode fn-wmc-at fn-wmc-utf8-one fn-wmc-core-one fn-wmc-core-result
                             fn-wmc-core-one-not-utf8 fn-wmc-core-one-preserves-result
                             fn-wmc-utf8-result)))))
(local
 (defthm fn-wmc-string-octets-length
   (equal (len (fn-nntp-string-octets-aux chars)) (len chars))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))
(local
 (defthm fn-wmc-characters-are-octets
   (implies (character-listp chars)
            (fn-wildmat-octet-listp (fn-nntp-string-octets-aux chars)))
   :hints (("Goal" :induct (fn-nntp-string-octets-aux chars)
            :in-theory (enable fn-nntp-string-octets-aux fn-wildmat-octet-listp
                                fn-cbor-octet-listp fn-cbor-octetp character-listp)))))
(local
 (defthm fn-wmc-list-limit-iff
   (implies (and (true-listp xs) (natp bound))
            (equal (fn-wildmat-at-mostp xs bound) (<= (len xs) bound)))
   :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
            :in-theory (enable fn-wildmat-at-mostp fn-cbor-at-mostp)))))
(defthm fn-wmc-start-value-is-group-match
  (equal (fn-wmc-value (fn-wmc-start patterns group))
         (fn-nntp-group-matches-parsed-wildmatp patterns group))
  :hints (("Goal" :in-theory
           (e/d (fn-wmc-start fn-wmc-value fn-wmc-result fn-wmc-utf8-result
                  fn-wmc-core-result fn-wmc-task-result fn-wmc-resume
                  fn-nntp-group-matches-parsed-wildmatp fn-nntp-string-octets
                  fn-wildmat-decode fn-wildmat-result-okp fn-wildmat-result-value
                  fn-wildmat-ok fn-wildmat-error nthcdr)
                 (fn-wildmat-decode-aux fn-nntp-string-octets-aux fn-wildmat-at-mostp
                  fn-wildmat-octet-listp fn-wm-match-codepoints-work)))))
(defthm fn-wmc-start-has-shape
  (fn-wmc-shapedp (fn-wmc-start patterns group))
  :hints (("Goal" :in-theory (enable fn-wmc-shapedp fn-wmc-core-shapedp))))
(defthm fn-wmc-utf8-one-preserves-shape
  (implies (and (fn-wmc-shapedp s) (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8))
           (fn-wmc-shapedp (fn-wmc-utf8-one s)))
  :hints (("Goal" :use ((:instance fn-wmc-next-window-width
                              (xs (fn-nntp-string-octets-aux
                                   (nthcdr (fn-wmc-at 3 (fn-wmc-at 0 s))
                                            (coerce (fn-wmc-at 2 (fn-wmc-at 0 s)) 'list))))))
           :in-theory
           (e/d (fn-wmc-utf8-one fn-wmc-shapedp fn-wmc-core-shapedp)
                 (fn-wmc-next-window-width nthcdr fn-wmc-nthcdr-open fn-wmc-octets-at-offset fn-wmc-offset-open fn-wmc-window fn-wmc-list-window fn-wildmat-utf8-next
                  fn-wildmat-result-okp fn-wildmat-result-value fn-wildmat-utf8-rest)))))
(defthm fn-wmc-one-preserves-shape
  (implies (fn-wmc-shapedp s) (fn-wmc-shapedp (fn-wmc-one s)))
  :hints (("Goal" :use (fn-wmc-core-one-not-utf8
                 (:instance fn-wmc-core-one-not-utf8 (s (fn-wmc-normalize-decode s))))
           :in-theory (e/d (fn-wmc-one fn-wmc-shapedp)
                            (fn-wmc-normalize-decode fn-wmc-utf8-one fn-wmc-core-one fn-wmc-at
                             fn-wmc-core-one-not-utf8 fn-wmc-core-shapedp)))))
(defthm fn-wmc-step-preserves-shape
  (implies (fn-wmc-shapedp s) (fn-wmc-shapedp (fn-wmc-step s work cons-grant)))
  :hints (("Goal" :in-theory (disable fn-wmc-one fn-wmc-shapedp))))
(defthm fn-wmc-step-preserves-result
  (equal (fn-wmc-result (fn-wmc-step s work cons-grant)) (fn-wmc-result s))
  :hints (("Goal" :in-theory (disable fn-wmc-one fn-wmc-result fn-wmc-shapedp))))
(defthm fn-wmc-step-preserves-value
  (equal (fn-wmc-value (fn-wmc-step s work cons-grant)) (fn-wmc-value s))
  :hints (("Goal" :in-theory (e/d (fn-wmc-value) (fn-wmc-result fn-wmc-step fn-wmc-shapedp)))))
(defthm fn-wmc-decided-value
  (implies (fn-wmc-decidedp s)
           (equal (fn-wmc-matchedp s) (if (fn-wmc-value s) t nil)))
  :hints (("Goal" :in-theory (enable fn-wmc-value fn-wmc-result fn-wmc-core-result fn-wmc-core-value
                                      fn-wmc-task-result fn-wmc-resume))))

(local
 (defthm fn-wmc-utf8-rest-count-less
   (implies (fn-wildmat-result-okp (fn-wildmat-utf8-next xs))
            (< (acl2-count (fn-wildmat-utf8-rest (fn-wildmat-utf8-next xs))) (acl2-count xs)))
   :hints (("Goal" :in-theory (enable fn-wildmat-utf8-next fn-wildmat-result-okp
                                      fn-wildmat-utf8-rest fn-wildmat-utf8-ok fn-wildmat-error)))))
(defun fn-wmc-utf8-count (xs)
  (declare (xargs :measure (acl2-count xs) :verify-guards nil
                  :hints (("Goal" :use fn-wmc-utf8-rest-count-less
                           :in-theory (disable fn-wmc-utf8-rest-count-less fn-wildmat-result-okp
                                               fn-wildmat-utf8-rest acl2-count)))))
  (if (consp xs)
      (let ((next (fn-wildmat-utf8-next xs)))
        (if (fn-wildmat-result-okp next)
            (1+ (fn-wmc-utf8-count (fn-wildmat-utf8-rest next))) 1)) 1))
(local
 (defthm fn-wmc-count-on-window
   (implies (consp xs)
    (let* ((window (fn-wmc-list-window xs 4)) (next (fn-wildmat-utf8-next window))
           (width (- (len window) (len (fn-wildmat-utf8-rest next)))))
      (equal (fn-wmc-utf8-count xs)
             (if (fn-wildmat-result-okp next) (1+ (fn-wmc-utf8-count (nthcdr width xs))) 1))))
   :hints (("Goal" :use fn-wmc-next-window
            :expand ((fn-wmc-utf8-count xs))
            :in-theory (enable fn-wildmat-result-okp fn-wildmat-result-value fn-wildmat-utf8-rest
                                fn-wildmat-utf8-ok)))))
(defun fn-wmc-remaining (s)
  (declare (xargs :verify-guards nil))
  (let ((task (fn-wmc-at 0 s)))
    (if (eq (fn-wmc-at 0 task) :utf8)
        (let* ((text (fn-wmc-at 2 task)) (offset (nfix (fn-wmc-at 3 task)))
               (xs (if (stringp text) (fn-nntp-string-octets-aux
                                      (nthcdr offset (coerce text 'list))) nil))
               (decoded (fn-wildmat-decode-aux xs (fn-wmc-at 4 task))))
          (+ (fn-wmc-utf8-count xs)
             (if (fn-wildmat-result-okp decoded)
                 (+ (len (fn-wildmat-result-value decoded)) 1
                    (fn-wmc-match-steps (fn-wmc-at 1 task) (fn-wildmat-result-value decoded))) 0)))
      (fn-wmc-core-remaining s))))
(local
 (defthm fn-wmc-revappend-length
   (equal (len (revappend xs ys)) (+ (len xs) (len ys)))
   :hints (("Goal" :induct (revappend xs ys)
            :in-theory (e/d (revappend) (revappend-removal))))))
(local (defthm fn-wmc-count-empty (equal (fn-wmc-utf8-count nil) 1)))
(defthm fn-wmc-utf8-one-progress
  (implies (and (fn-wmc-shapedp s) (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8))
           (equal (fn-wmc-remaining (fn-wmc-utf8-one s)) (1- (fn-wmc-remaining s))))
  :hints (("Goal"
           :use ((:instance fn-wmc-decode-on-window
                  (xs (fn-nntp-string-octets-aux
                       (nthcdr (fn-wmc-at 3 (fn-wmc-at 0 s))
                                (coerce (fn-wmc-at 2 (fn-wmc-at 0 s)) 'list))))
                  (acc (fn-wmc-at 4 (fn-wmc-at 0 s))))
                 (:instance fn-wmc-count-on-window
                  (xs (fn-nntp-string-octets-aux
                       (nthcdr (fn-wmc-at 3 (fn-wmc-at 0 s))
                                (coerce (fn-wmc-at 2 (fn-wmc-at 0 s)) 'list)))))
                 (:instance fn-wmc-next-window-width
                  (xs (fn-nntp-string-octets-aux
                       (nthcdr (fn-wmc-at 3 (fn-wmc-at 0 s))
                                (coerce (fn-wmc-at 2 (fn-wmc-at 0 s)) 'list))))))
           :in-theory
           (e/d (fn-wmc-remaining fn-wmc-utf8-one fn-wmc-shapedp fn-wmc-core-shapedp
                  fn-wmc-core-remaining fn-wmc-task-steps fn-wmc-stack-steps
                  fn-wildmat-ok fn-wildmat-error fn-wildmat-result-okp fn-wildmat-result-value
                  fn-wildmat-utf8-rest reverse revappend)
                 (fn-wmc-decode-on-window fn-wmc-count-on-window fn-wmc-utf8-count
                  fn-wildmat-decode-aux fn-wmc-window fn-wmc-list-window
                  fn-nntp-string-octets-aux nthcdr char revappend-removal reverse-removal
                  fn-wmc-match-steps fn-wmc-task-result fn-wildmat-utf8-next
                  fn-wmc-next-window fn-wmc-nthcdr-open fn-wmc-octets-at-offset fn-wmc-offset-open)))))
(defthm fn-wmc-one-progress
  (implies (and (fn-wmc-shapedp s) (not (fn-wmc-decidedp s)))
           (equal (fn-wmc-remaining (fn-wmc-one s)) (1- (fn-wmc-remaining s))))
  :hints (("Goal" :cases ((eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8))
           :use (fn-wmc-core-one-not-utf8 fn-wmc-core-one-progress
                 (:instance fn-wmc-core-one-not-utf8 (s (fn-wmc-normalize-decode s)))
                 (:instance fn-wmc-core-one-progress (s (fn-wmc-normalize-decode s))))
           :in-theory (e/d (fn-wmc-one fn-wmc-shapedp fn-wmc-remaining)
                            (fn-wmc-normalize-decode fn-wmc-at fn-wmc-utf8-one fn-wmc-core-one fn-wmc-core-remaining
                             fn-wmc-core-one-not-utf8 fn-wmc-core-one-progress
                             fn-wmc-core-shapedp fn-wmc-utf8-count fn-wildmat-decode-aux
                             fn-wildmat-result-okp fn-wildmat-result-value fn-wmc-match-steps)))))
(defthm fn-wmc-unfunded-step-is-identical
  (implies (not (fn-wmc-acceptedp s work cons-grant))
           (equal (fn-wmc-step s work cons-grant) s)))
(defthm fn-wmc-step-work-bound
  (<= (fn-wmc-consumed-work s work cons-grant) (nfix work)) :rule-classes :linear)
(defthm fn-wmc-step-cons-bound
  (<= (fn-wmc-consumed-cons s work cons-grant) (nfix cons-grant)) :rule-classes :linear)
(defthm fn-wmc-work-left-natural
  (natp (fn-wmc-work-left s work cons-grant)) :rule-classes :type-prescription)
(defthm fn-wmc-cons-left-natural
  (natp (fn-wmc-cons-left s work cons-grant)) :rule-classes :type-prescription)
(defthm fn-wmc-work-conservation
  (equal (+ (fn-wmc-consumed-work s work cons-grant) (fn-wmc-work-left s work cons-grant))
         (nfix work)))
(defthm fn-wmc-cons-conservation
  (equal (+ (fn-wmc-consumed-cons s work cons-grant) (fn-wmc-cons-left s work cons-grant))
         (nfix cons-grant)))
(defun fn-wmc-run-cons (s work cons-grant)
  (declare (xargs :verify-guards nil :measure (nfix work)))
  (if (fn-wmc-acceptedp s work cons-grant)
      (+ (fn-wmc-consumed-cons s work cons-grant)
         (fn-wmc-run-cons (fn-wmc-step s work cons-grant)
                          (fn-wmc-work-left s work cons-grant)
                          (fn-wmc-cons-left s work cons-grant))) 0))
(defthm fn-wmc-cumulative-cons-bound
  (<= (fn-wmc-run-cons s work cons-grant) (nfix cons-grant))
  :hints (("Goal" :induct (fn-wmc-run-cons s work cons-grant)
           :in-theory (disable fn-wmc-step fn-wmc-one fn-wmc-decidedp))))
(defun fn-wmc-one-cons-cells (s)
  (declare (xargs :guard t))
  (if (member-eq (fn-wmc-at 0 (fn-wmc-at 0 s)) '(:utf8 :decode)) 15
    (fn-wmc-core-one-cons-cells s)))
(defthm fn-wmc-one-cons-cells-bound
  (<= (fn-wmc-one-cons-cells s) (fn-wmc-demand s))
  :rule-classes :linear)
(defthm fn-wmc-accepted-cons-cells-covered
  (implies (fn-wmc-acceptedp s work cons-grant)
           (<= (fn-wmc-one-cons-cells s) (fn-wmc-consumed-cons s work cons-grant)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-wmc-one-cons-cells))))
(local
 (defthm fn-wmc-utf8-count-positive
   (< 0 (fn-wmc-utf8-count xs)) :rule-classes :linear
   :hints (("Goal" :induct (fn-wmc-utf8-count xs)
            :in-theory (e/d (fn-wmc-utf8-count) (fn-wildmat-utf8-next))))))
(defthm fn-wmc-remaining-natural
  (natp (fn-wmc-remaining s)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-wmc-remaining) (fn-wildmat-decode-aux fn-wmc-match-steps
                                                   fn-wmc-core-remaining fn-wmc-utf8-count)))))
(defthm fn-wmc-live-remaining-positive
  (implies (and (fn-wmc-shapedp s) (not (fn-wmc-decidedp s)))
           (< 0 (fn-wmc-remaining s)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-wmc-remaining fn-wmc-shapedp)
                                  (fn-wildmat-decode-aux fn-wmc-match-steps fn-wmc-core-remaining
                                   fn-wmc-utf8-count fn-wmc-core-shapedp)))))
(defthm fn-wmc-funded-step-progress
  (implies (fn-wmc-shapedp s)
           (equal (fn-wmc-remaining (fn-wmc-step s work cons-grant))
                  (- (fn-wmc-remaining s) (fn-wmc-consumed-work s work cons-grant))))
  :hints (("Goal" :in-theory (disable fn-wmc-one fn-wmc-remaining fn-wmc-shapedp))))
(in-theory (disable fn-wmc-utf8-result fn-wmc-result fn-wmc-value fn-wmc-remaining
                    fn-wmc-utf8-count fn-wmc-run-cons fn-wmc-list-window))
