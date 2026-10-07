; Part 3 of decoded-window-budget-trajectory-tests: split from it so each part
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
