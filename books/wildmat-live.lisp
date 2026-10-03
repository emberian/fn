; Matcher live control/row peak. Logical models, never runtime validation.
(in-package "ACL2")
(include-book "wildmat-cursor")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable (tau-system))))

(defun fn-wml-pattern-room (items target)
  (+ 25 (* 6 (len items)) (* 9 (len target))))
(defun fn-wml-element-extent (row)
  (if (consp row) (max (len (car row)) (fn-wml-element-extent (cdr row))) 0))
(defun fn-wml-row-room (items target row)
  (+ (fn-wml-element-extent row)
     (max (+ 7 (* 6 (len row))) (+ 19 (* 6 (len items)) (* 9 (len target))))))
(defun fn-wml-last-room (row) (+ 1 (* 6 (len row)) (fn-wml-element-extent row)))
(defun fn-wml-right-room (patterns target)
  (if (consp patterns)
      (max (+ 6 (fn-wml-right-room (cdr patterns) target))
           (max (len (car patterns))
                (+ 6 (fn-wml-pattern-room (fn-wildmat-pattern-items (car patterns)) target)))) 0))
(defun fn-wml-match-room (patterns target) (+ 6 (fn-wml-right-room patterns target)))
(defun fn-wml-task-room (task)
  (let ((tag (fn-wmc-at 0 task)) (a (fn-wmc-at 1 task)) (b (fn-wmc-at 2 task))
        (c (fn-wmc-at 3 task)) (d (fn-wmc-at 4 task)))
    (cond
     ((eq tag :decode)
      (let ((target (revappend d (if (stringp b)
                                  (fn-nntp-string-octets-aux (nthcdr (nfix c) (coerce b 'list))) nil))))
        (+ (len target) (fn-wml-match-room a target))))
     ((eq tag :reverse)
      (+ (len b) (len c) (fn-wml-match-room a (revappend b c))))
     ((eq tag :match) (fn-wml-match-room a b))
     ((eq tag :right) (fn-wml-right-room a b))
     ((eq tag :pattern) (fn-wml-pattern-room a b))
     ((eq tag :initial) (+ 13 (* 7 (len a))))
     ((eq tag :false) (+ 7 (* 7 (len a))))
     ((eq tag :row) (fn-wml-row-room a b c))
     ((member-eq tag '(:star :character)) (+ 13 (* 7 (len a)) (len b) (fn-wml-element-extent b)))
     ((member-eq tag '(:star-aux :char-aux)) (+ 7 (* 7 (len a)) (len b) (fn-wml-element-extent b)))
     ((eq tag :last) (fn-wml-last-room a))
     ((eq tag :return) (len a))
     (t 0))))
(defun fn-wml-frame-room (frame value)
  (let ((kind (fn-wmc-at 0 frame)) (x (fn-wmc-at 1 frame)) (y (fn-wmc-at 2 frame)))
    (cond
     ((eq kind :cons) (1+ (len value)))
     ((eq kind :match) 0)
     ((eq kind :right) (max (len x) (+ 6 (fn-wml-pattern-room (fn-wildmat-pattern-items x) y))))
     ((eq kind :right-pattern) (len x))
     ((eq kind :initial-pattern) (+ 6 (fn-wml-row-room x y value)))
     ((eq kind :pattern-row) (+ 6 (fn-wml-last-room value)))
     ((eq kind :pattern-last) 0)
     ((eq kind :row-step) (+ 6 (fn-wml-row-room x y value)))
     (t (len value)))))
(defun fn-wml-frame-value (frame value)
  (fn-wm-work-value (fn-wmc-frame-result frame (fn-wm-work-result value 0))))
(defun fn-wml-frames-room (frames value)
  (if (consp frames)
      (max (+ (* 6 (len frames)) (len value))
           (max (+ (* 6 (len (cdr frames))) (fn-wml-frame-room (car frames) value))
                (fn-wml-frames-room (cdr frames) (fn-wml-frame-value (car frames) value))))
    (len value)))
(defun fn-wml-core-room (s)
  (+ 7 (max (+ (* 6 (len (fn-wmc-at 1 s))) (fn-wml-task-room (fn-wmc-at 0 s)))
            (fn-wml-frames-room (fn-wmc-at 1 s) (fn-wm-work-value (fn-wmc-task-result (fn-wmc-at 0 s)))))))

; Control envelopes are owned; parsed patterns and common decoded-target tails
; are borrowed regions. This projection counts current row payload once.
(defun fn-wml-task-row-cells (task)
  (let ((tag (fn-wmc-at 0 task)))
    (cond ((eq tag :decode) (len (fn-wmc-at 4 task)))
          ((eq tag :reverse) (+ (len (fn-wmc-at 2 task)) (len (fn-wmc-at 3 task))))
          ((eq tag :row) (len (fn-wmc-at 3 task)))
          ((member-eq tag '(:star :character :star-aux :char-aux)) (len (fn-wmc-at 2 task)))
          ((member-eq tag '(:last :return)) (len (fn-wmc-at 1 task)))
          (t 0))))
(defun fn-wml-core-cells (s)
  (+ 7 (* 6 (len (fn-wmc-at 1 s))) (fn-wml-task-row-cells (fn-wmc-at 0 s))))

(local (defthm fn-wml-match-room-natural (natp (fn-wml-match-room p target))
         :rule-classes :type-prescription))
(local (defthm fn-wml-len-append (equal (len (append x y)) (+ (len x) (len y)))))
(local (defthm fn-wml-len-revappend (equal (len (revappend x y)) (+ (len x) (len y)))
 :hints (("Goal" :in-theory (enable revappend)))))
(local (defthm fn-wml-task-room-covers-row
  (<= (fn-wml-task-row-cells task) (fn-wml-task-room task))
  :hints (("Goal" :in-theory (enable fn-wml-task-row-cells fn-wml-task-room)))))
(defthm fn-wml-core-room-covers-live-cells
  (<= (fn-wml-core-cells s) (fn-wml-core-room s))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-wml-task-room-covers-row (task (fn-wmc-at 0 s))))
           :in-theory (disable fn-wml-task-row-cells fn-wml-task-room fn-wml-frames-room fn-wmc-at fn-wml-task-room-covers-row))))

(local (defthm fn-wml-frames-room-cons
  (equal (fn-wml-frames-room (cons frame frames) value)
         (max (+ (* 6 (1+ (len frames))) (len value))
              (max (+ (* 6 (len frames)) (fn-wml-frame-room frame value))
                   (fn-wml-frames-room frames (fn-wml-frame-value frame value)))))
  :hints (("Goal" :expand ((fn-wml-frames-room (cons frame frames) value))))))
(local (defthm fn-wml-frames-room-open
  (implies (consp frames)
   (equal (fn-wml-frames-room frames value)
          (max (+ (* 6 (len frames)) (len value))
               (max (+ (* 6 (len (cdr frames))) (fn-wml-frame-room (car frames) value))
                    (fn-wml-frames-room (cdr frames) (fn-wml-frame-value (car frames) value))))))
  :hints (("Goal" :expand ((fn-wml-frames-room frames value))))))

(local (defthm fn-wml-right-room-covers-value
 (<= (len (fn-wildmat-rightmost-match p target)) (fn-wml-right-room p target))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-wml-right-room p target)
          :in-theory (e/d (fn-wml-right-room fn-wildmat-rightmost-match)
                           (fn-wildmat-pattern-matchp fn-wml-pattern-room))))))
(local (defthm fn-wml-element-extent-car
 (<= (len (car row)) (fn-wml-element-extent row))
 :rule-classes :linear))
(local (defthm fn-wml-element-extent-cdr
 (<= (fn-wml-element-extent (cdr row)) (fn-wml-element-extent row))
 :rule-classes :linear))
(local (defthm fn-wml-element-extent-last
 (<= (len (fn-wildmat-row-last row)) (fn-wml-element-extent row))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-wildmat-row-last row)
          :in-theory (enable fn-wildmat-row-last fn-wml-element-extent)))))
(local (defthm fn-wml-row-length
 (equal (len (fn-wildmat-pattern-row items target row))
        (if (consp items) (1+ (len target)) (len row)))
 :hints (("Goal" :induct (fn-wildmat-pattern-row items target row)
          :in-theory (e/d (fn-wildmat-pattern-row) (fn-wildmat-step-character fn-wildmat-step-star))))))
(local (defthm fn-wml-extent-false
 (equal (fn-wml-element-extent (fn-wildmat-false-row x)) 0)
 :hints (("Goal" :induct (fn-wildmat-false-row x)
          :in-theory (enable fn-wildmat-false-row fn-wml-element-extent)))))
(local (defthm fn-wml-extent-initial
 (equal (fn-wml-element-extent (fn-wildmat-initial-row x)) 0)
 :hints (("Goal" :in-theory (enable fn-wildmat-initial-row fn-wml-element-extent)))))
(local (defthm fn-wml-extent-character-aux
 (equal (fn-wml-element-extent (fn-wildmat-step-character-aux target previous item)) 0)
 :hints (("Goal" :induct (fn-wildmat-step-character-aux target previous item)
          :in-theory (enable fn-wildmat-step-character-aux fn-wml-element-extent)))))
(local (defthm fn-wml-extent-star-aux
 (equal (fn-wml-element-extent (fn-wildmat-step-star-aux target previous carry)) 0)
 :hints (("Goal" :induct (fn-wildmat-step-star-aux target previous carry)
          :in-theory (enable fn-wildmat-step-star-aux fn-wml-element-extent)))))
(local (defthm fn-wml-extent-character
 (equal (fn-wml-element-extent (fn-wildmat-step-character target previous item)) 0)
 :hints (("Goal" :in-theory (enable fn-wildmat-step-character fn-wml-element-extent)))))
(local (defthm fn-wml-extent-star
 (<= (fn-wml-element-extent (fn-wildmat-step-star target previous))
     (fn-wml-element-extent previous))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-wildmat-step-star fn-wml-element-extent)))))
(local (defthm fn-wml-extent-row
 (<= (fn-wml-element-extent (fn-wildmat-pattern-row items target row))
     (fn-wml-element-extent row))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-wildmat-pattern-row items target row)
          :in-theory (e/d (fn-wildmat-pattern-row) (fn-wildmat-step-star fn-wildmat-step-character))))))
(local (defthm fn-wml-rightmost-empty
 (implies (not (consp p)) (equal (fn-wildmat-rightmost-match p target) nil))
 :hints (("Goal" :in-theory (enable fn-wildmat-rightmost-match)))))
(local (defthm fn-wml-rightmost-open
 (implies (consp p)
  (equal (fn-wildmat-rightmost-match p target)
         (let ((right (fn-wildmat-rightmost-match (cdr p) target)))
           (if right right
               (if (fn-wildmat-pattern-matchp (fn-wildmat-pattern-items (car p)) target)
                   (car p) nil)))))
 :hints (("Goal" :expand ((fn-wildmat-rightmost-match p target))))))
(defthm fn-wml-core-one-retained-room
  (implies (and (fn-wmc-core-shapedp s)
                (not (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode)))
           (<= (fn-wml-core-room (fn-wmc-core-one s)) (fn-wml-core-room s)))
  :hints (("Goal" :in-theory
           (e/d (fn-wml-core-room fn-wml-task-room fn-wml-frame-room
                  fn-wml-match-room fn-wml-pattern-room fn-wml-row-room fn-wml-last-room fn-wml-frame-value fn-wml-frames-room-open
                  fn-wmc-core-one fn-wmc-node fn-wmc-state fn-wmc-return fn-wmc-call
                  fn-wmc-task-result fn-wmc-frame-result
                  fn-wm-work-value-result fn-wm-false-row-work-value fn-wm-initial-row-work-value
                  fn-wm-step-character-aux-work-value fn-wm-step-character-work-value
                  fn-wm-step-star-aux-work-value fn-wm-step-star-work-value
                  fn-wm-pattern-row-work-value fn-wm-row-last-work-value
                  fn-wm-pattern-match-work-value fn-wm-rightmost-match-work-value fn-wm-match-codepoints-work-value
                  fn-wildmat-step-character fn-wildmat-step-star fn-wildmat-false-row fn-wildmat-pattern-matchp
                  fn-ag-car fn-ag-cdr revappend)
                 (revappend-removal fn-wm-work-value fn-wm-work-result fn-wm-work-cost fn-wml-frames-room fn-wm-pattern-row-work fn-wm-initial-row-work fn-wm-false-row-work fn-wm-step-character-work fn-wm-step-character-aux-work fn-wm-step-star-work fn-wm-step-star-aux-work fn-wm-row-last-work fn-wm-pattern-match-work fn-wm-rightmost-match-work fn-wm-match-codepoints-work fn-wildmat-item-character-matchp
                  fn-wildmat-rightmost-match fn-nntp-string-octets-aux nthcdr)))
          ("Subgoal 1" :in-theory (enable fn-wml-frames-room-open))))

; Numeric carried extent; no runtime pattern walk is required by the consumer.
(defun fn-wml-capacity (patterns tokens octets)
  (declare (xargs :guard (and (natp patterns) (natp tokens) (natp octets))))
  (+ 38 (* 6 patterns) (* 6 tokens) (* 10 octets)))
(defthm fn-wml-right-room-linear
 (implies (fn-wildmat-pattern-listp patterns)
  (<= (fn-wml-right-room patterns target)
      (+ 25 (* 6 (len patterns)) (* 6 (fn-wm-total-items patterns)) (* 9 (len target)))))
 :hints (("Goal" :induct (fn-wml-right-room patterns target)
          :in-theory (e/d (fn-wml-right-room fn-wml-pattern-room fn-wm-total-items
                            fn-wildmat-pattern-listp fn-wildmat-patternp)
                           (fn-wildmat-text-items-p fn-wildmat-pattern-items)))))
(defthm fn-wml-codepoints-live-bound
 (implies (fn-wildmat-pattern-listp patterns)
  (<= (fn-wml-core-room (fn-wmc-start-codepoints patterns target))
      (fn-wml-capacity (len patterns) (fn-wm-total-items patterns) (len target))))
 :hints (("Goal" :use ((:instance fn-wml-right-room-linear))
          :in-theory (e/d (fn-wml-core-room fn-wml-task-room fn-wml-match-room
                            fn-wmc-start-codepoints fn-wmc-state fn-wmc-node
                            fn-wmc-task-result fn-wml-frames-room fn-wml-capacity fn-wm-match-codepoints-work-value)
                           (fn-wml-right-room fn-wml-right-room-linear fn-wm-work-value fn-wm-match-codepoints-work fn-wildmat-match-codepoints fn-wm-total-items fn-wildmat-pattern-listp)))))

(defun fn-wml-utf8-budget (task)
 (+ (len (fn-wmc-at 4 task))
    (if (stringp (fn-wmc-at 2 task))
        (nfix (- (length (fn-wmc-at 2 task)) (nfix (fn-wmc-at 3 task)))) 0)))
(defun fn-wml-room (s)
 (if (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8)
     (fn-wml-capacity (len (fn-wmc-at 1 (fn-wmc-at 0 s)))
                      (fn-wm-total-items (fn-wmc-at 1 (fn-wmc-at 0 s)))
                      (fn-wml-utf8-budget (fn-wmc-at 0 s)))
   (fn-wml-core-room s)))
(defun fn-wml-live-cells (s)
 (if (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8)
     (+ 7 (len (fn-wmc-at 4 (fn-wmc-at 0 s))))
   (fn-wml-core-cells s)))
(defthm fn-wml-room-covers-live-cells
 (<= (fn-wml-live-cells s) (fn-wml-room s))
 :rule-classes :linear
 :hints (("Goal" :in-theory (e/d (fn-wml-room fn-wml-live-cells fn-wml-capacity fn-wml-utf8-budget)
                                  (fn-wml-core-room fn-wml-core-cells fn-wm-total-items)))))
(defthm fn-wml-reverse-live-bound
 (implies (fn-wildmat-pattern-listp patterns)
  (<= (fn-wml-core-room (fn-wmc-state (fn-wmc-node :reverse patterns left right nil) nil))
      (fn-wml-capacity (len patterns) (fn-wm-total-items patterns) (+ (len left) (len right)))))
 :hints (("Goal" :use ((:instance fn-wml-right-room-linear (target (revappend left right))))
          :in-theory (e/d (fn-wml-core-room fn-wml-task-room fn-wml-match-room fn-wmc-state fn-wmc-node
                            fn-wmc-task-result fn-wml-frames-room fn-wml-capacity fn-wm-match-codepoints-work-value)
                           (fn-wml-right-room fn-wml-right-room-linear fn-wm-work-value fn-wm-match-codepoints-work
                            fn-wildmat-match-codepoints fn-wm-total-items fn-wildmat-pattern-listp)))))
(local (defthm fn-wml-codepoint-start-tag
 (equal (fn-wmc-at 0 (fn-wmc-at 0 (fn-wmc-start-codepoints p target))) :match)))
(local (defthm fn-wml-done-room
 (equal (fn-wml-core-room (fn-wmc-state (fn-wmc-return nil 0) nil)) 7)))
(defthm fn-wml-start-live-bound
 (implies (fn-wildmat-pattern-listp patterns)
  (<= (fn-wml-room (fn-wmc-start patterns group))
      (fn-wml-capacity (len patterns) (fn-wm-total-items patterns) (if (stringp group) (length group) 0))))
 :hints (("Goal" :use ((:instance fn-wml-codepoints-live-bound (target nil))
                         (:instance fn-wml-codepoint-start-tag (p patterns) (target nil)))
          :in-theory (e/d (fn-wml-room fn-wmc-start fn-wml-utf8-budget fn-wmc-state fn-wmc-node fn-wml-capacity)
                                 (fn-wmc-start-codepoints fn-wm-total-items fn-wildmat-pattern-listp
                                  fn-wml-core-room fn-wml-codepoints-live-bound fn-wml-codepoint-start-tag fn-wmc-return)))))

(local (defthm fn-wml-next-width-positive
 (let* ((next (fn-wildmat-utf8-next xs))
        (width (- (len xs) (len (fn-wildmat-utf8-rest next)))))
  (implies (fn-wildmat-result-okp next) (and (natp width) (< 0 width))))
 :hints (("Goal" :in-theory (enable fn-wildmat-utf8-next fn-wildmat-result-okp
                                    fn-wildmat-utf8-rest fn-wildmat-utf8-2p fn-wildmat-utf8-3-tailsp
                                    fn-wildmat-utf8-4-tailsp fn-wildmat-utf8-ok fn-wildmat-error)))))
(defthm fn-wml-utf8-one-retained-room
 (implies (and (fn-wmc-shapedp s)
               (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8)
               (fn-wildmat-pattern-listp (fn-wmc-at 1 (fn-wmc-at 0 s))))
          (<= (fn-wml-room (fn-wmc-utf8-one s)) (fn-wml-room s)))
 :hints (("Goal" :use ((:instance fn-wml-reverse-live-bound
                                 (patterns (fn-wmc-at 1 (fn-wmc-at 0 s)))
                                 (left (fn-wmc-at 4 (fn-wmc-at 0 s))) (right nil))
                           (:instance fn-wml-next-width-positive
                                 (xs (fn-wmc-window (fn-wmc-at 2 (fn-wmc-at 0 s))
                                                    (nfix (fn-wmc-at 3 (fn-wmc-at 0 s))) 4))))
          :in-theory (e/d (fn-wml-room fn-wmc-utf8-one fn-wml-utf8-budget fn-wml-capacity
                            fn-wmc-shapedp fn-wmc-core-shapedp fn-wmc-framesp fn-wmc-state fn-wmc-node fn-wmc-return)
                           (fn-wml-reverse-live-bound fn-wml-core-room fn-wml-next-width-positive
                            fn-wmc-window fn-wildmat-utf8-next fn-wildmat-result-okp
                            fn-wildmat-result-value fn-wildmat-utf8-rest
                            fn-wm-total-items fn-wildmat-pattern-listp)))))

; Carried logical profile; never revalidate it on the served path.
(defun fn-wml-livep (s)
 (and (fn-wmc-shapedp s)
      (not (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode))
      (or (not (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8))
          (fn-wildmat-pattern-listp (fn-wmc-at 1 (fn-wmc-at 0 s))))))
(local (defthm fn-wml-core-next-tags
 (and (not (eq (fn-wmc-at 0 (fn-wmc-at 0 (fn-wmc-core-one s))) :utf8))
      (implies (not (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode))
               (not (eq (fn-wmc-at 0 (fn-wmc-at 0 (fn-wmc-core-one s))) :decode))))
 :hints (("Goal" :in-theory (enable fn-wmc-core-one)))))
(defthm fn-wml-start-livep
 (implies (fn-wildmat-pattern-listp patterns) (fn-wml-livep (fn-wmc-start patterns group)))
 :hints (("Goal" :use fn-wmc-start-has-shape
          :in-theory (e/d (fn-wml-livep fn-wmc-start fn-wmc-start-codepoints)
                           (fn-wmc-shapedp fn-wildmat-pattern-listp fn-wmc-start-has-shape)))))
(defthm fn-wml-one-livep
 (implies (fn-wml-livep s) (fn-wml-livep (fn-wmc-one s)))
 :hints (("Goal" :use (fn-wmc-one-preserves-shape fn-wml-core-next-tags)
          :in-theory (e/d (fn-wml-livep fn-wmc-one fn-wmc-utf8-one)
                           (fn-wmc-shapedp fn-wmc-core-one fn-wmc-one-preserves-shape
                            fn-wml-core-next-tags fn-wmc-window fn-wildmat-utf8-next
                            fn-wildmat-result-okp fn-wildmat-result-value fn-wildmat-utf8-rest
                            fn-wildmat-pattern-listp)))))
(defthm fn-wml-one-retained-room
 (implies (fn-wml-livep s) (<= (fn-wml-room (fn-wmc-one s)) (fn-wml-room s)))
 :hints (("Goal" :use (fn-wml-core-one-retained-room fn-wml-utf8-one-retained-room fn-wml-core-next-tags)
          :in-theory (e/d (fn-wml-livep fn-wml-room fn-wmc-one fn-wmc-shapedp)
                           (fn-wml-core-room fn-wmc-utf8-one fn-wmc-core-one fn-wmc-at
                            fn-wmc-core-shapedp fn-wml-core-one-retained-room
                            fn-wml-utf8-one-retained-room fn-wml-core-next-tags)))))
(defun fn-wml-coveredp (s patterns tokens octets)
 (and (fn-wml-livep s) (<= (fn-wml-room s) (fn-wml-capacity patterns tokens octets))))
(defthm fn-wml-start-coveredp
 (implies (fn-wildmat-pattern-listp patterns)
  (fn-wml-coveredp (fn-wmc-start patterns group) (len patterns) (fn-wm-total-items patterns)
                    (if (stringp group) (length group) 0)))
 :hints (("Goal" :use (fn-wml-start-livep fn-wml-start-live-bound)
          :in-theory (e/d (fn-wml-coveredp) (fn-wml-livep fn-wml-room fn-wml-capacity fn-wmc-start
                                            fn-wml-start-livep fn-wml-start-live-bound fn-wm-total-items fn-wildmat-pattern-listp)))))
(defthm fn-wml-one-coveredp
 (implies (fn-wml-coveredp s patterns tokens octets)
          (fn-wml-coveredp (fn-wmc-one s) patterns tokens octets))
 :hints (("Goal" :use (fn-wml-one-retained-room fn-wml-one-livep)
          :in-theory (e/d (fn-wml-coveredp) (fn-wml-livep fn-wml-room fn-wml-capacity fn-wmc-one
                                           fn-wml-one-retained-room fn-wml-one-livep)))))
(defthm fn-wml-step-coveredp
 (implies (fn-wml-coveredp s patterns tokens octets)
          (fn-wml-coveredp (fn-wmc-step s work grant) patterns tokens octets))
 :hints (("Goal" :in-theory (e/d (fn-wmc-step) (fn-wml-coveredp fn-wmc-one fn-wmc-acceptedp)))))
(defthm fn-wml-covered-live-bound
 (implies (fn-wml-coveredp s patterns tokens octets)
          (<= (fn-wml-live-cells s) (fn-wml-capacity patterns tokens octets)))
 :hints (("Goal" :use fn-wml-room-covers-live-cells
          :in-theory (e/d (fn-wml-coveredp) (fn-wml-room fn-wml-live-cells fn-wml-capacity
                                           fn-wml-room-covers-live-cells)))))
(verify-guards fn-wml-capacity)
(in-theory (disable fn-wml-task-room fn-wml-frame-room fn-wml-frame-value fn-wml-frames-room
                    fn-wml-core-room fn-wml-core-cells fn-wml-room fn-wml-live-cells
                    fn-wml-livep fn-wml-coveredp fn-wml-utf8-budget))

; All core target references point into one decoded target region. The metric
; takes maximum referenced suffix extent, not a sum charging each alias.
; UTF8/reverse charge both growing/split target spines before sharing begins.
(defun fn-wml-task-target (task)
 (let ((tag (fn-wmc-at 0 task)))
  (cond ((eq tag :reverse) (+ (len (fn-wmc-at 2 task)) (len (fn-wmc-at 3 task))))
        ((member-eq tag '(:match :right :pattern :row)) (len (fn-wmc-at 2 task)))
        ((member-eq tag '(:initial :false :star :character :star-aux :char-aux)) (len (fn-wmc-at 1 task)))
        (t 0))))
(defun fn-wml-frame-target (frame)
 (if (member-eq (fn-wmc-at 0 frame) '(:right :initial-pattern :row-step))
     (len (fn-wmc-at 2 frame)) 0))
(defun fn-wml-frames-target (frames)
 (if (consp frames) (max (fn-wml-frame-target (car frames)) (fn-wml-frames-target (cdr frames))) 0))
(defun fn-wml-core-target (s)
 (max (fn-wml-task-target (fn-wmc-at 0 s)) (fn-wml-frames-target (fn-wmc-at 1 s))))
(defun fn-wml-target (s)
 (if (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8)
     (fn-wml-utf8-budget (fn-wmc-at 0 s)) (fn-wml-core-target s)))
(local (defthm fn-wml-frames-target-cons
 (equal (fn-wml-frames-target (cons frame frames))
        (max (fn-wml-frame-target frame) (fn-wml-frames-target frames)))))
(local (defthm fn-wml-frames-target-car
 (<= (fn-wml-frame-target (car frames)) (fn-wml-frames-target frames)) :rule-classes :linear))
(local (defthm fn-wml-frames-target-cdr
 (<= (fn-wml-frames-target (cdr frames)) (fn-wml-frames-target frames)) :rule-classes :linear))
(local (defthm fn-wml-frames-target-open
 (implies (consp frames)
  (equal (fn-wml-frames-target frames)
         (max (fn-wml-frame-target (car frames)) (fn-wml-frames-target (cdr frames)))))
 :hints (("Goal" :expand ((fn-wml-frames-target frames))))))
(defthm fn-wml-core-one-target
 (implies (not (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode))
          (<= (fn-wml-core-target (fn-wmc-core-one s)) (fn-wml-core-target s)))
 :hints (("Goal" :in-theory (e/d (fn-wmc-core-one fn-wml-core-target fn-wml-task-target fn-wml-frame-target)
                                  (fn-wml-frames-target)))))
(defthm fn-wml-utf8-one-target
 (implies (and (fn-wmc-shapedp s) (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :utf8))
          (<= (fn-wml-target (fn-wmc-utf8-one s)) (fn-wml-target s)))
 :hints (("Goal" :use ((:instance fn-wml-next-width-positive
                                 (xs (fn-wmc-window (fn-wmc-at 2 (fn-wmc-at 0 s))
                                                    (nfix (fn-wmc-at 3 (fn-wmc-at 0 s))) 4))))
          :in-theory (e/d (fn-wml-target fn-wml-core-target fn-wml-task-target fn-wml-utf8-budget
                            fn-wmc-utf8-one fn-wmc-shapedp fn-wmc-core-shapedp fn-wmc-framesp)
                           (fn-wml-next-width-positive fn-wmc-window fn-wildmat-utf8-next fn-wildmat-result-okp
                            fn-wildmat-result-value fn-wildmat-utf8-rest)))))
(defthm fn-wml-one-target
 (implies (fn-wml-livep s) (<= (fn-wml-target (fn-wmc-one s)) (fn-wml-target s)))
 :hints (("Goal" :use (fn-wml-core-one-target fn-wml-utf8-one-target fn-wml-core-next-tags)
          :in-theory (e/d (fn-wml-livep fn-wml-target fn-wmc-one)
                           (fn-wml-core-target fn-wmc-utf8-one fn-wmc-core-one fn-wmc-at fn-wmc-shapedp
                            fn-wml-core-one-target fn-wml-utf8-one-target fn-wml-core-next-tags)))))
(defthm fn-wml-start-target
 (<= (fn-wml-target (fn-wmc-start patterns group)) (if (stringp group) (length group) 0))
 :hints (("Goal" :in-theory (enable fn-wml-target fn-wml-core-target fn-wml-task-target
                                    fn-wml-utf8-budget fn-wmc-start fn-wmc-start-codepoints))))
(defun fn-wml-retainedp (s patterns tokens octets)
 (and (fn-wml-coveredp s patterns tokens octets) (<= (fn-wml-target s) (nfix octets))))
(defun fn-wml-owned-capacity (patterns tokens octets)
 (declare (xargs :guard (and (natp patterns) (natp tokens) (natp octets))))
 (+ (fn-wml-capacity patterns tokens octets) octets))
(defthm fn-wml-start-retainedp
 (implies (fn-wildmat-pattern-listp patterns)
  (fn-wml-retainedp (fn-wmc-start patterns group) (len patterns) (fn-wm-total-items patterns)
                     (if (stringp group) (length group) 0)))
 :hints (("Goal" :use (fn-wml-start-coveredp fn-wml-start-target)
          :in-theory (e/d (fn-wml-retainedp) (fn-wml-coveredp fn-wml-target fn-wmc-start
                                             fn-wml-start-coveredp fn-wml-start-target)))))
(defthm fn-wml-one-retainedp
 (implies (fn-wml-retainedp s patterns tokens octets)
          (fn-wml-retainedp (fn-wmc-one s) patterns tokens octets))
 :hints (("Goal" :use (fn-wml-one-coveredp fn-wml-one-target)
          :in-theory (e/d (fn-wml-retainedp fn-wml-coveredp)
                           (fn-wml-livep fn-wml-room fn-wml-capacity fn-wml-target fn-wmc-one
                            fn-wml-one-coveredp fn-wml-one-target)))))
(defthm fn-wml-step-retainedp
 (implies (fn-wml-retainedp s patterns tokens octets)
          (fn-wml-retainedp (fn-wmc-step s work grant) patterns tokens octets))
 :hints (("Goal" :in-theory (e/d (fn-wmc-step) (fn-wml-retainedp fn-wmc-one fn-wmc-acceptedp)))))
(defthm fn-wml-retained-owned-bound
 (implies (and (natp octets) (fn-wml-retainedp s patterns tokens octets))
          (<= (+ (fn-wml-live-cells s) (fn-wml-target s)) (fn-wml-owned-capacity patterns tokens octets)))
 :hints (("Goal" :use fn-wml-covered-live-bound
          :in-theory (e/d (fn-wml-retainedp fn-wml-owned-capacity)
                           (fn-wml-coveredp fn-wml-target fn-wml-live-cells fn-wml-capacity
                            fn-wml-covered-live-bound)))))
(verify-guards fn-wml-owned-capacity)
(in-theory (disable fn-wml-task-target fn-wml-frame-target fn-wml-frames-target fn-wml-core-target
                    fn-wml-target fn-wml-retainedp))

; Input parsed graph is borrowed, counted once by its owner (not per frame).
(defun fn-wml-tree-cells (x)
 (if (consp x) (+ 1 (fn-wml-tree-cells (car x)) (fn-wml-tree-cells (cdr x))) 0))
(local (defthm fn-wml-scalar-item-cells
 (implies (fn-wildmat-text-itemp item) (equal (fn-wml-tree-cells item) 0))
 :hints (("Goal" :in-theory (enable fn-wildmat-text-itemp fn-wildmat-text-exactp)))))
(local (defthm fn-wml-scalar-items-cells
 (implies (fn-wildmat-text-items-p items) (equal (fn-wml-tree-cells items) (len items)))
 :hints (("Goal" :induct (fn-wildmat-text-items-p items)
          :in-theory (e/d (fn-wildmat-text-items-p) (fn-wildmat-text-itemp))))))
(local (defthm fn-wml-pattern-record-cells
 (implies (fn-wildmat-patternp pattern)
          (equal (fn-wml-tree-cells pattern) (+ 2 (len (fn-wildmat-pattern-items pattern)))))
 :hints (("Goal" :in-theory (enable fn-wildmat-patternp fn-wildmat-pattern-sign fn-wildmat-pattern-items true-listp len)))))
(defthm fn-wml-borrowed-pattern-cells
 (implies (fn-wildmat-pattern-listp patterns)
          (equal (fn-wml-tree-cells patterns) (+ (* 3 (len patterns)) (fn-wm-total-items patterns))))
 :hints (("Goal" :induct (fn-wildmat-pattern-listp patterns)
          :in-theory (e/d (fn-wildmat-pattern-listp fn-wm-total-items)
                           (fn-wildmat-patternp fn-wildmat-pattern-items)))))
(in-theory (disable fn-wml-tree-cells))
