; PRF-1132 / SCN-1039: complete literal source projection/count teeth.
; Universal source equalities have no removable hypotheses.
(in-package "ACL2")
(include-book "../../books/payload-action-source-counts")

(defthm pat-t-emit-success-literal-positive
 (let ((r (fn-pat-zin-emit 65 (fn-zin-reset (create-fn-zin-st)) (make-list 65536 :initial-element 23) nil)))
  (and (equal (car r) (fn-zin-emit 65 (fn-zin-reset (create-fn-zin-st)) (make-list 65536 :initial-element 23) nil))
       (equal (car (car r)) nil)
       (equal (fn-pzt-count :multiply (cdr r)) 1)
       (equal (fn-pzt-count :negate (cdr r)) 0)
       (equal (fn-pzt-count :add (cdr r)) 4)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pat-emit-arithmetic-counts
                  (o 65) (fn-zin-st (fn-zin-reset (create-fn-zin-st)))
                  (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil)))
         :in-theory (e/d (fn-pat-match-count fn-zin-emit)
                 (fn-pat-zin-emit fn-pzt-count fn-zin-copy fn-zin-win-put
                  fn-zin-out-append-octet fn-zin-wrap)))))

(defthm pat-t-emit-refusal-literal-positive
 (let ((r (fn-pat-zin-emit 65 (fn-zin-set 6 65536 (fn-zin-reset (create-fn-zin-st))) (make-list 65536 :initial-element 23) nil)))
  (and (equal (car r) (fn-zin-emit 65 (fn-zin-set 6 65536 (fn-zin-reset (create-fn-zin-st))) (make-list 65536 :initial-element 23) nil))
       (equal (car (car r)) :bomb)
       (equal (fn-pzt-count :multiply (cdr r)) 1)
       (equal (fn-pzt-count :negate (cdr r)) 0)
       (equal (fn-pzt-count :add (cdr r)) 2)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pat-emit-arithmetic-counts
                  (o 65) (fn-zin-st (fn-zin-set 6 65536 (fn-zin-reset (create-fn-zin-st))))
                  (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil)))
         :in-theory (e/d (fn-pat-match-count fn-zin-emit)
                 (fn-pat-zin-emit fn-pzt-count fn-zin-copy fn-zin-win-put
                  fn-zin-out-append-octet fn-zin-wrap)))))

(defthm pat-t-match-success-literal-positive
 (let ((r (fn-pat-zin-match 2 (fn-zin-set 3 2 (fn-zin-set 4 1 (fn-zin-reset (create-fn-zin-st)))) (make-list 65536 :initial-element 23) nil)))
  (and (equal (car r) (fn-zin-match 2 (fn-zin-set 3 2 (fn-zin-set 4 1 (fn-zin-reset (create-fn-zin-st)))) (make-list 65536 :initial-element 23) nil))
       (equal (car (car r)) nil)
       (equal (fn-pat-match-count 2 (fn-zin-set 3 2 (fn-zin-set 4 1 (fn-zin-reset (create-fn-zin-st))))) 2)
       (equal (fn-pzt-count :multiply (cdr r)) 1)
       (equal (fn-pzt-count :negate (cdr r)) 4)
       (equal (fn-pzt-count :add (cdr r)) 8)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pat-match-arithmetic-counts
                  (room 2) (fn-zin-st (fn-zin-set 3 2 (fn-zin-set 4 1 (fn-zin-reset (create-fn-zin-st)))))
                  (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil)))
         :in-theory (e/d (fn-pat-match-count fn-zin-match)
                 (fn-pat-zin-match fn-pzt-count fn-zin-copy fn-zin-win-put
                  fn-zin-out-append-octet fn-zin-wrap)))))

(defthm pat-t-match-refusal-literal-positive
 (let ((r (fn-pat-zin-match 2 (fn-zin-reset (create-fn-zin-st)) (make-list 65536 :initial-element 23) nil)))
  (and (equal (car r) (fn-zin-match 2 (fn-zin-reset (create-fn-zin-st)) (make-list 65536 :initial-element 23) nil))
       (equal (car (car r)) :bomb)
       (equal (fn-pat-match-count 2 (fn-zin-reset (create-fn-zin-st))) 0)
       (equal (fn-pzt-count :multiply (cdr r)) 1)
       (equal (fn-pzt-count :negate (cdr r)) 1)
       (equal (fn-pzt-count :add (cdr r)) 2)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pat-match-arithmetic-counts
                  (room 2) (fn-zin-st (fn-zin-reset (create-fn-zin-st)))
                  (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil)))
         :in-theory (e/d (fn-pat-match-count fn-zin-match)
                 (fn-pat-zin-match fn-pzt-count fn-zin-copy fn-zin-win-put
                  fn-zin-out-append-octet fn-zin-wrap)))))

(defthm pat-t-pull-literal-positive
 (let ((r (fn-pat-zin-pull 0 (fn-zin-reset (create-fn-zin-st)) (list 65))))
  (and (equal (car r) (fn-zin-pull 0 (fn-zin-reset (create-fn-zin-st)) (list 65)))
       (equal (fn-pzt-count :multiply (cdr r)) 0)
       (equal (fn-pzt-count :negate (cdr r)) 0)
       (equal (fn-pzt-count :add (cdr r)) 2)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pat-pull-arithmetic-counts
                  (ip 0) (fn-zin-st (fn-zin-reset (create-fn-zin-st))) (fn-octets (list 65))))
         :in-theory (disable fn-pat-zin-pull fn-pzt-count))))

(defthm pat-t-match-omitted-negation-mutation
 (let ((trace (cdr (fn-pat-zin-match 2 (fn-zin-set 3 2 (fn-zin-set 4 1 (fn-zin-reset (create-fn-zin-st)))) (make-list 65536 :initial-element 23) nil))))
  (and (equal (fn-pat-match-count 2 (fn-zin-set 3 2 (fn-zin-set 4 1 (fn-zin-reset (create-fn-zin-st))))) 2)
       (equal (fn-pzt-count :multiply trace) 1)
       (equal (fn-pzt-count :negate trace) 4)
       (equal (fn-pzt-count :add trace) 8)
       (not (equal (+ (fn-pzt-count :negate trace)
                      (fn-pzt-count :add trace))
                   (fn-pzt-count :add trace)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pat-match-arithmetic-counts
                  (room 2) (fn-zin-st (fn-zin-set 3 2 (fn-zin-set 4 1 (fn-zin-reset (create-fn-zin-st)))))
                  (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil)))
         :in-theory (e/d (fn-pat-match-count)
                         (fn-pat-zin-match fn-pzt-count)))))
