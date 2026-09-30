(in-package "ACL2")
(include-book "../../books/decoded-window-stored-trajectory")

; Real initialized pools and fixed Huffman wire; no native funding fixture.
(defun-nx pwc-test-stored-case (b0 requested1 requested2)
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (st (car init)) (input '(115 116 28 177 0 0))
        (r1 (fn-pzw-stored-chunk requested1 4694 0 6 6 251 st input (mv-nth 1 init) (mv-nth 2 init) nil))
        (r2 (fn-pzw-stored-chunk requested2 (mv-nth 1 r1) (mv-nth 2 r1) 6 6 251
                                (mv-nth 3 r1) input (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (credited (fn-zin-set 7 (+ 6 (fn-zin-tin st)) st))
        (a1 (fn-zin-feed (fn-pzw-quantum requested1 4694) credited 0 6 (fn-pzw-room 251 (fn-zin-tout credited)) input (mv-nth 1 init) (mv-nth 2 init) nil))
        (a2 (fn-zin-feed (fn-pzw-quantum requested2 (mv-nth 1 r1)) (mv-nth 3 a1) (mv-nth 2 a1) 6
                         (fn-pzw-room 251 (fn-zin-tout (mv-nth 3 a1))) input (mv-nth 4 a1) (mv-nth 5 a1) nil))
        (whole (fn-zin-feed b0 credited 0 6 (+ (len (mv-nth 6 r1)) (fn-pzw-room 251 (fn-zin-tout (mv-nth 3 r1)))) input (mv-nth 1 init) (mv-nth 2 init) nil)))
  (list r1 r2 a1 a2 whole)))

(local
 (defthm pwc-actual-two-stored-full-tuple-positive
  (let* ((case (pwc-test-stored-case 4694 1024 1024)) (r1 (car case)) (r2 (cadr case)) (a1 (caddr case)) (a2 (cadddr case)))
   (and (equal (car r1) :full) (equal (car r2) :full)
        (equal (len (mv-nth 6 r1)) 64) (equal (len (mv-nth 6 r2)) 64)
        (equal (list (car r1) (mv-nth 1 r1) (mv-nth 2 r1)
                     (fn-zin-set 7 (+ 6 (fn-zin-tin (mv-nth 3 r1))) (mv-nth 3 r1))
                     (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)) a1)
        (equal (list (car r2) (mv-nth 1 r2) (mv-nth 2 r2)
                     (fn-zin-set 7 (+ 6 (fn-zin-tin (mv-nth 3 r2))) (mv-nth 3 r2))
                     (mv-nth 4 r2) (mv-nth 5 r2) (mv-nth 6 r2)) a2)))
  :rule-classes nil))

(defun-nx pwc-test-stored-window-case (b0 requested1 requested2 bad)
 (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
        (st (car init)) (input (if bad '(6 115 116 28 177 0 0) '(115 116 28 177 0 0)))
        (c (len input))
        (r1 (fn-pzw-stored-chunk requested1 4694 0 c c 251 st input (mv-nth 1 init) (mv-nth 2 init) nil))
        (r2 (fn-pzw-stored-chunk requested2 (mv-nth 1 r1) (mv-nth 2 r1) c c 251
                                (mv-nth 3 r1) input (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (credited (fn-zin-set 7 (+ c (fn-zin-tin st)) st))
        (whole (fn-zin-feed b0 credited 0 c (+ (len (mv-nth 6 r1)) (fn-pzw-room 251 (fn-zin-tout (mv-nth 3 r1)))) input (mv-nth 1 init) (mv-nth 2 init) nil)))
  (list r1 r2 whole)))

(local
 (defthm pwc-actual-stored-positive
  (let* ((case (pwc-test-stored-window-case 4694 1024 1024 nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (equal (car r1) :full) (not (equal (car r2) :yield)) (not (equal (car whole) :yield)) (equal (fn-pwz-semantic-observation whole)
               (list (car r2) (mv-nth 2 r2)
                     (fn-zin-set 7 (+ (if nil 7 6) (fn-zin-tin (mv-nth 3 r2))) (mv-nth 3 r2))
                     (mv-nth 4 r2) (mv-nth 5 r2)
                     (append (mv-nth 6 r1) (mv-nth 6 r2))))))
  :rule-classes nil))

(local
 (defthm pwc-actual-stored-first-full-removal
  (let* ((case (pwc-test-stored-window-case 4694 1024 1024 t))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (not (equal (car r1) :full)) (not (equal (car r2) :yield)) (not (equal (car whole) :yield)) (not (equal (fn-pwz-semantic-observation whole)
               (list (car r2) (mv-nth 2 r2)
                     (fn-zin-set 7 (+ (if t 7 6) (fn-zin-tin (mv-nth 3 r2))) (mv-nth 3 r2))
                     (mv-nth 4 r2) (mv-nth 5 r2)
                     (append (mv-nth 6 r1) (mv-nth 6 r2)))))))
  :rule-classes nil))

(local
 (defthm pwc-actual-stored-second-completion-removal
  (let* ((case (pwc-test-stored-window-case 4694 1024 0 nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (equal (car r1) :full) (not (not (equal (car r2) :yield))) (not (equal (car whole) :yield)) (not (equal (fn-pwz-semantic-observation whole)
               (list (car r2) (mv-nth 2 r2)
                     (fn-zin-set 7 (+ (if nil 7 6) (fn-zin-tin (mv-nth 3 r2))) (mv-nth 3 r2))
                     (mv-nth 4 r2) (mv-nth 5 r2)
                     (append (mv-nth 6 r1) (mv-nth 6 r2)))))))
  :rule-classes nil))

(local
 (defthm pwc-actual-stored-whole-completion-removal
  (let* ((case (pwc-test-stored-window-case 0 1024 1024 nil))
         (r1 (car case)) (r2 (cadr case)) (whole (caddr case)))
   (and (equal (car r1) :full) (not (equal (car r2) :yield)) (not (not (equal (car whole) :yield))) (not (equal (fn-pwz-semantic-observation whole)
               (list (car r2) (mv-nth 2 r2)
                     (fn-zin-set 7 (+ (if nil 7 6) (fn-zin-tin (mv-nth 3 r2))) (mv-nth 3 r2))
                     (mv-nth 4 r2) (mv-nth 5 r2)
                     (append (mv-nth 6 r1) (mv-nth 6 r2)))))))
  :rule-classes nil))

(local
 (defthm pwc-actual-buffer-refusal-full-tuple-positive
  (let* ((st (create-fn-zin-st))
         (r (fn-pzw-stored-chunk 10 20 0 0 0 0 st nil nil nil '(65)))
         (a (fn-zin-feed 10 (fn-zin-set 7 (fn-zin-tin st) st) 0 0 1 nil nil nil nil)))
   (and (equal (car r) '(:refused :buffers))
        (equal (list (car r) (mv-nth 1 r) (mv-nth 2 r)
                     (fn-zin-set 7 (fn-zin-tin (mv-nth 3 r)) (mv-nth 3 r))
                     (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)) a)))
  :rule-classes nil))

; Mutation: omitting the recredit changes the complete state; ledger or getter
; equality alone would not authorize substituting that external state.
(local
 (defthm pwc-omitted-recredit-state-mutation
  (let* ((case (pwc-test-stored-case 4694 1024 1024))
         (r1 (car case)) (r2 (cadr case)) (a1 (caddr case)) (a2 (cadddr case)))
   (and (equal (car r1) :full) (equal (car r2) :full)
        (not (equal r1 a1)) (not (equal r2 a2))))
  :rule-classes nil))
