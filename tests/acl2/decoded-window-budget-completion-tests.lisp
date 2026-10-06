; Part 1 of the decoded-window budget-completion teeth (terminal codec, begin
; and codec envelopes); part 2 is decoded-window-budget-completion-2-tests,
; split so each certifies inside the per-book ACL2 timeout.
(in-package "ACL2")
(include-book "../../books/decoded-window-budget-completion")

; Actual source-produced pending-copy fixture, no native authority.
(defun-nx pwc-initial ()
  (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
(defun-nx pwc-first-chunk ()
  (let ((init (pwc-initial)))
    (fn-pzw-stored-chunk 1024 (fn-pzd-budget 6 251) 0 6 6 251
                         (car init) '(115 116 28 177 0 0)
                         (mv-nth 1 init) (mv-nth 2 init) (mv-nth 3 init))))

(defun-nx pwc-codec-state ()
  (let ((r (pwc-first-chunk)))
    (fn-ewz-state :codec '(:trailer 7 100 9 8 0 0 9 23 47 59 102 6 6)
                  251 0 251 (fn-pzw-budget-left 1024 (fn-pzd-budget 6 251) (mv-nth 1 r))
                  (mv-nth 2 r) 6 (car r))))


(defun-nx pwc-codec-result ()
  (let ((r (pwc-first-chunk)))
    (fn-ewz-codec-tick (pwc-codec-state) '(115 116 28 177 0 0)
                       (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (create-fn-ew-buffer))))
(defun-nx pwc-init-controller ()
  (fn-ewz-begin 7 100 8 102 6 251 0 23 47 59 0 nil
                (create-pgs-digest-state) (create-fn-zin-st) nil nil nil))


(defun-nx pwc-next-codec-result (r)
 (if (equal (nth 0 (mv-nth 1 r)) :codec)
  (fn-ewz-codec-tick (mv-nth 1 r) '(115 116 28 177 0 0)
                    (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))
  r))
(defun-nx pwc-actual-terminal-ticks ()
 (pwc-next-codec-result (pwc-next-codec-result (pwc-next-codec-result (pwc-codec-result)))))

(local
 (defthm pwc-actual-terminal-codec-envelope-positive
  (let* ((before (pwc-first-chunk)) (z (pwc-codec-state))
         (r (pwc-actual-terminal-ticks)) (next (mv-nth 1 r)))
   (and (fn-pwz-controller-final-budget-envelopep z (mv-nth 3 before))
        (equal (nth 0 next) :decoded)
        (equal (nth 8 next) '(:refused :stream-ended))
        (equal (fn-zin-tin (mv-nth 2 r)) 6)
        (equal (fn-zin-tout (mv-nth 2 r)) 251)
        (fn-pwz-controller-final-budget-envelopep next (mv-nth 2 r))
        (member-eq (nth 0 next) '(:scan :codec :drain :decoded))
        (posp (nth 5 next))
        (<= (+ 3839 (* 7 6)) (nth 5 next))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pwc-next-codec-result)))))
(local
 (defthm pwc-actual-begin-envelope-positive
  (let ((r (pwc-init-controller)))
   (and (natp 102) (equal (nth 0 (car r)) :scan)
        (fn-pwz-controller-final-budget-envelopep (car r) (mv-nth 2 r))))
  :rule-classes nil))
(local
 (defthm pwc-begin-natural-offset-removal
  (let ((r (fn-ewz-begin 7 1 10 3/2 6 251 0 23 47 59 0 nil
                         (create-pgs-digest-state) (create-fn-zin-st) nil nil nil)))
   (and (not (natp 3/2))
        (not (fn-pwz-controller-final-budget-envelopep (car r) (mv-nth 2 r)))))
  :rule-classes nil))
(local
 (defthm pwc-codec-envelope-removal
  (let* ((before (pwc-first-chunk)) (z (update-nth 6 -1 (pwc-codec-state)))
         (s (mv-nth 3 before))
         (r (fn-ewz-codec-tick z '(115 116 28 177 0 0) s
                              (mv-nth 4 before) (mv-nth 5 before) (mv-nth 6 before) (create-fn-ew-buffer))))
   (and (not (fn-pwz-controller-final-budget-envelopep z s))
        (equal (car r) :state)
        (not (fn-pwz-controller-final-budget-envelopep (mv-nth 1 r) (mv-nth 2 r)))))
  :rule-classes nil))
