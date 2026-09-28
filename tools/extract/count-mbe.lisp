; How many mbe's the front end resolved in a list of extracted functions:
; occurrences of (return-last 'mbe1-raw ...) in their unnormalized bodies.
(in-package "ACL2")
(program)
(mutual-recursion
 (defun xt-count-mbe (term)
   (cond ((or (variablep term) (fquotep term)) 0)
         ((flambda-applicationp term)
          (+ (xt-count-mbe (lambda-body (ffn-symb term))) (xt-count-mbe-list (fargs term))))
         (t (+ (if (and (eq (ffn-symb term) 'return-last) (equal (fargn term 1) ''mbe1-raw)) 1 0)
               (xt-count-mbe-list (fargs term))))))
 (defun xt-count-mbe-list (terms)
   (if (consp terms) (+ (xt-count-mbe (car terms)) (xt-count-mbe-list (cdr terms))) 0)))
(defun xt-count-mbe-fns (fns w acc nfns)
  (if (endp fns) (list acc nfns)
    (let ((k (xt-count-mbe (getpropc (car fns) 'unnormalized-body nil w))))
      (xt-count-mbe-fns (cdr fns) w (+ k acc) (if (> k 0) (1+ nfns) nfns)))))
