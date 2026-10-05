; Part 2 of decoded-window-budget-trajectory-tests: split from it so each part
; certifies inside the per-book ACL2 timeout (the whole book took ~540 s of
; proof on hbox and timed out at 600 s under batch load,
; certify-20261005T010803Z-1318278).  The fixtures are the same.
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
 (defthm pwb-loop-natural-budget-removal
   (let* ((init (pwb-initial)) (s (car init))
          (r (fn-zin-loop 20001/2 0 0 64 s nil (mv-nth 1 init) (mv-nth 2 init) nil)))
     (and (not (natp 20001/2)) (natp 0) (fn-pwz-progress-statep s)
          (not (pwb-loop-bound-conclusion 20001/2 0 s r))))
   :rule-classes nil))

(local
 (defthm pwb-actual-initializer-carry-positive
   (let ((r (pwb-init-controller)))
     (fn-pwz-budget-carryp 6 251 (nth 5 (car r)) (mv-nth 2 r)))
   :rule-classes nil))

(local
 (defthm pwb-budget-positive-remaining-positive
   (let* ((r (pwb-codec-result)) (next (mv-nth 1 r)) (s (mv-nth 2 r)) (remaining (nth 5 next)))
     (and (natp 6) (natp 251) (fn-pwz-budget-carryp 6 251 remaining s)
          (<= (fn-zin-tin s) 6) (<= (fn-zin-tout s) (+ 1 251))
          (posp remaining) (<= (+ 3838 (* 7 6)) remaining)))
   :rule-classes nil))

(local
 (defthm pwb-budget-incoming-carry-removal
   (let ((s (car (pwb-initial))))
     (and (natp 6) (natp 251) (not (fn-pwz-budget-carryp 6 251 0 s))
          (<= (fn-zin-tin s) 6) (<= (fn-zin-tout s) (+ 1 251))
          (not (and (posp 0) (<= (+ 3838 (* 7 6)) 0)))))
   :rule-classes nil))

(local
 (defthm pwb-budget-input-frontier-removal
   (let ((s (fn-zin-set 7 10000 (car (pwb-initial)))))
     (and (natp 6) (natp 251) (fn-pwz-budget-carryp 6 251 0 s)
          (not (<= (fn-zin-tin s) 6)) (<= (fn-zin-tout s) (+ 1 251))
          (not (and (posp 0) (<= (+ 3838 (* 7 6)) 0)))))
   :rule-classes nil))

(local
 (defthm pwb-budget-output-frontier-removal
   (let ((s (fn-zin-set 6 10000 (car (pwb-initial)))))
     (and (natp 6) (natp 251) (fn-pwz-budget-carryp 6 251 0 s)
          (<= (fn-zin-tin s) 6) (not (<= (fn-zin-tout s) (+ 1 251)))
          (not (and (posp 0) (<= (+ 3838 (* 7 6)) 0)))))
   :rule-classes nil))

(local
 (defthm pwb-budget-natural-compressed-removal
   (let* ((s0 (car (pwb-initial)))
          (s (fn-zin-set 7 4 (fn-zin-set 6 252 (fn-zin-set 3 258 (fn-zin-set 0 12 s0))))))
     (and (not (natp 9/2)) (natp 251) (fn-pwz-budget-carryp 9/2 251 3838 s)
          (<= (fn-zin-tin s) 9/2) (<= (fn-zin-tout s) (+ 1 251))
          (not (and (posp 3838) (<= (+ 3838 (* 7 9/2)) 3838)))))
   :rule-classes nil))

(local
 (defthm pwb-budget-natural-decoded-removal
   (let* ((s0 (car (pwb-initial)))
          (s (fn-zin-set 7 6 (fn-zin-set 6 252 (fn-zin-set 3 258 (fn-zin-set 0 12 s0))))))
     (and (natp 6) (not (natp 503/2)) (fn-pwz-budget-carryp 6 503/2 3378 s)
          (<= (fn-zin-tin s) 6) (<= (fn-zin-tout s) (+ 1 503/2))
          (not (and (posp 3378) (<= (+ 3838 (* 7 6)) 3378)))))
   :rule-classes nil))

