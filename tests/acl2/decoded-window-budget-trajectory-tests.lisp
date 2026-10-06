; Part 1 of the decoded-window budget-trajectory teeth (codec carry and loop
; charge); parts 2 and 3 are decoded-window-budget-trajectory-{2,3}-tests,
; split so each certifies inside the per-book ACL2 timeout.
(in-package "ACL2")
(include-book "../../books/decoded-window-budget-trajectory")

; Actual source-produced pending-copy fixture, no native authority.
(defun-nx pwb-initial ()
  (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
(defun-nx pwb-first-chunk ()
  (let ((init (pwb-initial)))
    (fn-pzw-stored-chunk 1024 (fn-pzd-budget 6 251) 0 6 6 251
                         (car init) '(115 116 28 177 0 0)
                         (mv-nth 1 init) (mv-nth 2 init) (mv-nth 3 init))))

(defun-nx pwb-codec-state ()
  (let ((r (pwb-first-chunk)))
    (fn-ewz-state :codec '(:trailer 7 100 9 8 0 0 9 23 47 59 102 6 6)
                  251 0 251 (fn-pzw-budget-left 1024 (fn-pzd-budget 6 251) (mv-nth 1 r))
                  (mv-nth 2 r) 6 (car r))))


(defun-nx pwb-codec-result ()
  (let ((r (pwb-first-chunk)))
    (fn-ewz-codec-tick (pwb-codec-state) '(115 116 28 177 0 0)
                       (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (create-fn-ew-buffer))))
(defun-nx pwb-loop-bound-conclusion (b ip s r)
  (and (fn-pwz-progress-statep (mv-nth 3 r))
       (<= (- b (mv-nth 1 r))
           (+ (* 9 (- (mv-nth 2 r) ip))
              (* 2 (- (fn-zin-tout (mv-nth 3 r)) (fn-zin-tout s)))
              (fn-pwz-progress-phase s) (fn-zin-nbits s) 259))))
(defun-nx pwb-init-controller ()
  (fn-ewz-begin 7 100 8 102 6 251 0 23 47 59 0 nil
                (create-pgs-digest-state) (create-fn-zin-st) nil nil nil))

(local
 (defthm pwb-actual-codec-carry-positive
   (let* ((before (pwb-first-chunk)) (s (mv-nth 3 before))
          (z (pwb-codec-state)) (r (pwb-codec-result)) (next (mv-nth 1 r)))
     (and (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) s)
          (not (consp (nth 8 next)))
          (fn-pwz-budget-carryp (nth 12 (nth 1 next)) (nth 2 next) (nth 5 next) (mv-nth 2 r))))
   :rule-classes nil))

; Corrupted grant: all retained hypotheses true, incoming carry is false.
(local
 (defthm pwb-codec-incoming-carry-removal
   (let* ((before (pwb-first-chunk)) (s (mv-nth 3 before))
          (z (update-nth 5 0 (pwb-codec-state)))
          (r (fn-ewz-codec-tick z '(115 116 28 177 0 0) s
                                (mv-nth 4 before) (mv-nth 5 before) (mv-nth 6 before) (create-fn-ew-buffer)))
          (next (mv-nth 1 r)))
     (and (not (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) s))
          (not (consp (nth 8 next)))
          (not (fn-pwz-budget-carryp (nth 12 (nth 1 next)) (nth 2 next) (nth 5 next) (mv-nth 2 r)))))
   :rule-classes nil))

; Corrupted terminal control with zero consumed input. Terminal refusal has
; a separate final charge and must not be silently treated as success.
(local
 (defthm pwb-codec-nonrefusal-removal
   (let* ((init (pwb-initial)) (s (fn-zin-set 0 13 (car init)))
          (z (fn-ewz-state :codec '(:trailer 7 100 8 0 0 0 8 23 47 59 102 6 6)
                           251 0 251 (fn-pzd-budget 6 251) 0 0 :more))
          (r (fn-ewz-codec-tick z nil s (mv-nth 1 init) (mv-nth 2 init) (mv-nth 3 init) (create-fn-ew-buffer)))
          (next (mv-nth 1 r)))
     (and (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) s)
          (consp (nth 8 next))
          (equal (nth 8 next) '(:refused :stream-ended))
          (not (fn-pwz-budget-carryp (nth 12 (nth 1 next)) (nth 2 next) (nth 5 next) (mv-nth 2 r)))))
   :rule-classes nil))

(local
 (defthm pwb-actual-loop-copy-charge-positive
   (let* ((before (pwb-first-chunk)) (s (mv-nth 3 before))
          (ip (mv-nth 2 before))
          (r (fn-zin-loop 1 ip 6 64 s '(115 116 28 177 0 0) (mv-nth 4 before) (mv-nth 5 before) nil)))
     (and (natp 1) (natp ip) (fn-pwz-progress-statep s)
          (equal (car r) :yield) (pwb-loop-bound-conclusion 1 ip s r)))
   :rule-classes nil))

(local
 (defthm pwb-actual-loop-terminal-charge-positive
   (let* ((init (pwb-initial)) (s (fn-zin-set 0 13 (car init)))
          (r (fn-zin-loop 100 0 0 64 s nil (mv-nth 1 init) (mv-nth 2 init) nil)))
     (and (natp 100) (natp 0) (fn-pwz-progress-statep s)
          (equal (car r) '(:refused :stream-ended))
          (pwb-loop-bound-conclusion 100 0 s r)))
   :rule-classes nil))

; Corrupted grammar carry: mode12's pending length was not produced by
; the actual length-code parser. This does not restrict stored LEN16.
(local
 (defthm pwb-loop-progress-state-removal
   (let* ((init (pwb-initial)) (s (fn-zin-set 3 10000 (fn-zin-set 0 12 (car init))))
          (r (fn-zin-loop 1 0 0 64 s nil (mv-nth 1 init) (mv-nth 2 init) nil)))
     (and (natp 1) (natp 0) (not (fn-pwz-progress-statep s))
          (not (pwb-loop-bound-conclusion 1 0 s r))))
   :rule-classes nil))
