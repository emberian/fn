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

(local
 (defthm pwb-real-stored-length16-not-restricted
   (let* ((init (pwb-initial))
          (r (fn-pzw-stored-chunk 1024 (fn-pzd-budget 65540 65535) 0 5 65540 65535
                                  (car init) '(1 255 255 0 0) (mv-nth 1 init) (mv-nth 2 init) nil))
          (s (mv-nth 3 r)))
     (and (equal (car r) :more) (equal (fn-zin-mode s) 3) (equal (fn-zin-n s) 65535)
          (fn-pwz-progress-statep s)))
   :rule-classes nil))

(local
 (defthm pwb-actual-controller-initial-carry-positive
   (let ((r (pwb-init-controller)))
     (and (natp 102) (fn-pwz-controller-budget-carryp (car r) (mv-nth 2 r))))
   :rule-classes nil))

(local
 (defthm pwb-controller-natural-payload-offset-removal
   (let ((r (fn-ewz-begin 7 1 10 3/2 6 251 0 23 47 59 0 nil
                         (create-pgs-digest-state) (create-fn-zin-st) nil nil nil)))
     (and (not (natp 3/2))
          (not (fn-pwz-controller-budget-carryp (car r) (mv-nth 2 r)))))
   :rule-classes nil))

(local
 (defthm pwb-actual-active-controller-budget-positive
   (let* ((r (pwb-codec-result)) (next (mv-nth 1 r)) (s (mv-nth 2 r)))
     (and (fn-pwz-controller-budget-carryp next s)
          (member-eq (nth 0 next) '(:scan :codec :drain :decoded))
          (posp (nth 5 next)) (<= (+ 3840 (* 7 (nth 12 (nth 1 next)))) (nth 5 next))))
   :rule-classes nil))

(local
 (defthm pwb-actual-empty-controller-budget-positive
   (let* ((r (fn-ewz-begin 7 100 2 102 0 0 0 23 47 59 0 nil
                          (create-pgs-digest-state) (create-fn-zin-st) nil nil nil))
          (z (car r)) (s (mv-nth 2 r)))
     (and (fn-pwz-controller-budget-carryp z s)
          (member-eq (nth 0 z) '(:scan :codec :drain :decoded))
          (equal (nth 0 z) :drain)
          (posp (nth 5 z)) (<= (+ 3840 (* 7 (nth 12 (nth 1 z)))) (nth 5 z))))
   :rule-classes nil))

; Corrupted remaining budget. Keep the real active source coordinates.
(local
 (defthm pwb-active-controller-carry-removal
   (let* ((r (pwb-codec-result)) (z (update-nth 5 0 (mv-nth 1 r))) (s (mv-nth 2 r)))
     (and (not (fn-pwz-controller-budget-carryp z s))
          (member-eq (nth 0 z) '(:scan :codec :drain :decoded))
          (not (and (posp (nth 5 z))
                    (<= (+ 3840 (* 7 (nth 12 (nth 1 z)))) (nth 5 z))))))
   :rule-classes nil))

; Corrupted inactive failure state: active output bound is deliberately
; vacuous, and this does not become a scheduling/publication permission.
(local
 (defthm pwb-controller-active-mode-removal
   (let* ((init (pwb-initial)) (s (fn-zin-set 6 10000 (car init)))
          (z (fn-ewz-state :codec-error '(:trailer 7 100 8 0 0 0 8 23 47 59 102 6 6)
                           251 0 251 0 0 0 :state)))
     (and (fn-pwz-controller-budget-carryp z s)
          (not (member-eq (nth 0 z) '(:scan :codec :drain :decoded)))
          (not (and (posp (nth 5 z))
                    (<= (+ 3840 (* 7 (nth 12 (nth 1 z)))) (nth 5 z))))))
   :rule-classes nil))
