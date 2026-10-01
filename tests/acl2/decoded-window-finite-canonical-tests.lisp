(in-package "ACL2")
(include-book "../../books/decoded-window-canonical-trajectory")

(defun-nx pwfc-test-case (turns dict wire n)
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) nil nil nil))
        (c (len wire))
        (s (fn-pwf-actual-output-turns turns 0 c (fn-zin-set 7 c (car init))
                     wire (mv-nth 1 init) (mv-nth 2 init) nil))
        (r (mv-nth 0 s))
        (answer (if (and (zp n) (atom wire)) (list :ok nil)
                  (fn-pzd-answer (fn-zin-stored-status (car r) c (mv-nth 3 r)) (mv-nth 6 r) n))))
  (list r (fn-zin-stored-limit c (+ 1 (nfix n)))
        (fn-pzd-decode dict wire n) answer)))

(local
 (defthm pwfc-actual-four-windows-and-yields-canonical-positive
  (let* ((c (pwfc-test-case '((64 1 1 1 1024) (128 1024) (192 1024) (252 1024))
                             nil '(115 116 28 177 0 0) 251)) (r (car c)))
   (and (not (equal (car r) :full)) (not (equal (car r) :yield))
        (< (len (mv-nth 6 r)) (cadr c))
        (equal (caddr c) (cadddr c)) (equal (car (caddr c)) :ok)
        (equal (len (cadr (caddr c))) 251)))
  :rule-classes nil))

(local
 (defthm pwfc-actual-nonempty-dictionary-canonical-positive
  (let* ((c (pwfc-test-case '((4 1024)) '(9 8 7) (fn-pzd-stored '(65 66 67)) 3)) (r (car c)))
   (and (not (equal (car r) :full)) (not (equal (car r) :yield))
        (< (len (mv-nth 6 r)) (cadr c))
        (equal (caddr c) (cadddr c)) (equal (caddr c) '(:ok (65 66 67)))))
  :rule-classes nil))

(local
 (defthm pwfc-full-output-frontier-removal
  (let* ((c (pwfc-test-case '((2 1024)) nil (fn-pzd-stored '(65 66 67)) 3)) (r (car c)))
   (and (equal (car r) :full) (not (equal (car r) :yield))
        (< (len (mv-nth 6 r)) (cadr c))
        (not (equal (caddr c) (cadddr c)))))
  :rule-classes nil))

(local
 (defthm pwfc-yielded-completion-removal
  (let* ((c (pwfc-test-case '((4 1)) nil (fn-pzd-stored '(65 66 67)) 3)) (r (car c)))
   (and (not (equal (car r) :full)) (equal (car r) :yield)
        (< (len (mv-nth 6 r)) (cadr c))
        (not (equal (caddr c) (cadddr c)))))
  :rule-classes nil))

; Logical declared-length/frontier mutation, not a native job admission.
(local
 (defthm pwfc-declared-length-margin-mutation-removal
  (let* ((c (pwfc-test-case '((4 1024)) nil (fn-pzd-stored '(65 66 67)) 1)) (r (car c)))
   (and (not (equal (car r) :full)) (not (equal (car r) :yield))
        (not (< (len (mv-nth 6 r)) (cadr c)))
        (not (equal (caddr c) (cadddr c)))))
  :rule-classes nil))
