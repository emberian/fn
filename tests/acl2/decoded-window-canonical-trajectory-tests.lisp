; Complete actual canonical boundary teeth. Requested5 exercises the actual
; general stored wrapper, not a fixed1024 composed CODEC-TICK yield claim.
; The65-byte stored-wire witness calls the actual wrapper over its full span;
; it is not a native64-byte input-window fixture. No supplied-demand activation.
(in-package "ACL2")
(include-book "../../books/decoded-window-canonical-trajectory")

(defun-nx pwd-test-canonical-windows (dict input n q1 q2)
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) nil nil nil))
        (c (len input)) (budget (fn-pzd-budget c n))
        (r1 (fn-pzw-stored-chunk q1 budget 0 c c n (car init) input (mv-nth 1 init) (mv-nth 2 init) nil))
        (remaining (fn-pzw-budget-left q1 budget (mv-nth 1 r1)))
        (r2 (fn-pzw-stored-chunk q2 remaining (mv-nth 2 r1) c c n (mv-nth 3 r1) input
                                (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (out (append (mv-nth 6 r1) (mv-nth 6 r2)))
        (bound (fn-zin-stored-limit c (+ 1 (nfix n))))
        (old (fn-pzd-decode dict input n))
        (new (if (and (zp n) (atom input)) (list :ok nil)
               (fn-pzd-answer (fn-zin-stored-status (car r2) c (mv-nth 3 r2)) out n))))
  (list r1 r2 out bound old new)))

(local
 (defthm pwd-canonical-two-full-window-positive
  (let* ((case (pwd-test-canonical-windows nil (fn-pzd-stored (make-list 65 :initial-element 65)) 65 1024 1024))
         (r1 (car case)) (r2 (cadr case)) (out (caddr case)) (bound (cadddr case)))
   (and (equal (car r1) :full) (member-equal (car r1) '(:yield :full))
        (not (equal (car r2) :yield)) (not (equal (car r2) :full))
        (< (len out) bound) (equal (nth 4 case) (nth 5 case))
        (equal out (make-list 65 :initial-element 65)) (equal (car (nth 4 case)) :ok)))
  :rule-classes nil))

(local
 (defthm pwd-canonical-quantum-window-positive
  (let* ((case (pwd-test-canonical-windows '(65 66) (fn-pzd-stored '(65 66 67 68 69 70 71 72 73 74)) 10 5 1024))
         (r1 (car case)) (r2 (cadr case)) (out (caddr case)) (bound (cadddr case)))
   (and (equal (car r1) :yield) (member-equal (car r1) '(:yield :full))
        (not (equal (car r2) :yield)) (not (equal (car r2) :full))
        (< (len out) bound) (equal (nth 4 case) (nth 5 case))
        (equal out '(65 66 67 68 69 70 71 72 73 74)) (equal (car (nth 4 case)) :ok)))
  :rule-classes nil))

(local
 (defthm pwd-canonical-empty-window-positive
  (let* ((case (pwd-test-canonical-windows nil nil 0 0 1024))
         (r1 (car case)) (r2 (cadr case)) (out (caddr case)) (bound (cadddr case)))
   (and (equal (car r1) :yield) (member-equal (car r1) '(:yield :full))
        (not (equal (car r2) :yield)) (not (equal (car r2) :full))
        (< (len out) bound) (equal (nth 4 case) (nth 5 case))
        (equal out nil) (equal (nth 4 case) '(:ok nil))))
  :rule-classes nil))

(local
 (defthm pwd-canonical-first-boundary-removal
  (let* ((case (pwd-test-canonical-windows nil '(6 1 1 0 254 255 65) 1 1024 1024))
         (r1 (car case)) (r2 (cadr case)) (out (caddr case)) (bound (cadddr case)))
   (and (not (member-equal (car r1) '(:yield :full)))
        (not (equal (car r2) :yield)) (not (equal (car r2) :full))
        (< (len out) bound) (not (equal (nth 4 case) (nth 5 case)))))
  :rule-classes nil))

(local
 (defthm pwd-canonical-second-yield-removal
  (let* ((case (pwd-test-canonical-windows nil (fn-pzd-stored (make-list 65 :initial-element 65)) 65 1024 0))
         (r1 (car case)) (r2 (cadr case)) (out (caddr case)) (bound (cadddr case)))
   (and (member-equal (car r1) '(:yield :full))
        (equal (car r2) :yield) (not (equal (car r2) :full))
        (< (len out) bound) (not (equal (nth 4 case) (nth 5 case)))))
  :rule-classes nil))

(local
 (defthm pwd-canonical-second-full-removal
  (let* ((case (pwd-test-canonical-windows nil '(115 116 28 177 0 0) 251 1024 1024))
         (r1 (car case)) (r2 (cadr case)) (out (caddr case)) (bound (cadddr case)))
   (and (member-equal (car r1) '(:yield :full))
        (not (equal (car r2) :yield)) (equal (car r2) :full)
        (< (len out) bound) (not (equal (nth 4 case) (nth 5 case)))))
  :rule-classes nil))

(local
 (defthm pwd-canonical-output-frontier-removal
  (let* ((case (pwd-test-canonical-windows nil (fn-pzd-stored '(65 66)) 1 1024 1024))
         (r1 (car case)) (r2 (cadr case)) (out (caddr case)) (bound (cadddr case)))
   (and (member-equal (car r1) '(:yield :full))
        (not (equal (car r2) :yield)) (not (equal (car r2) :full))
        (not (< (len out) bound)) (not (equal (nth 4 case) (nth 5 case)))))
  :rule-classes nil))
