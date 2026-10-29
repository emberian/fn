; E2 pass 2: fold/summary statements generated from semantic contract roles.
; This template never reads a theorem property. Proofs are supplied separately.
(in-package "ACL2")
(include-book "defsquare")

(defun sq-fs-kind-formula (case recognizer)
  (if (eq case :malformed)
      `(not (,recognizer e))
    `(and (,recognizer e) (eq (car e) ,case))))

(defun sq-fs-formula (case contract)
  (let* ((rel (sq-get :relation contract))
         (ok1 (car (sq-get :admissible contract)))
         (ok2 (cadr (sq-get :admissible contract)))
         (step1 (car (sq-get :step contract)))
         (step2 (cadr (sq-get :step contract)))
         (fold1 (car (sq-get :fold contract)))
         (fold2 (cadr (sq-get :fold contract)))
         (obs1 (car (sq-get :observation contract)))
         (obs2 (cadr (sq-get :observation contract)))
         (convert (sq-get :converter contract))
         (pre `(and (,ok1 h) (,ok2 s) (,rel h s))))
    (cond
     ((eq case :converter)
      `(implies (,ok1 h)
                (and (,ok2 (,convert h)) (,rel h (,convert h)))))
     ((eq case :composition)
      `(implies ,pre
                (and (,rel (,fold1 h j) (,fold2 s j))
                     (equal (,obs1 (,fold1 h j) q)
                            (,obs2 (,fold2 s j) q)))))
     (t
      `(implies (and (,ok1 h) (,ok2 s) (,rel h s)
                     ,(sq-fs-kind-formula case (sq-get :recognizer contract)))
                (and (,ok1 (,step1 h e)) (,ok2 (,step2 s e))
                     (,rel (,step1 h e) (,step2 s e))))))))

(defun sq-fs-vars (case)
  (cond ((eq case :converter) '(h))
        ((eq case :composition) '(h s j q))
        (t '(h s e))))
