(in-package "ACL2")
(include-book "../../books/history-image-census")

; Complete boundary antecedent and conclusion, actual existing codec/model.
(assert-event
 (let* ((h '(t)) (ev '(1 2 3)) (count (len h))
        (pool (fn-hp-pes-len h)) (encoded (len (fn-scc-encode ev)))
        (r (mv-list 3 (fn-hcc-row count pool count encoded))))
   (and (equal count (len h)) (equal pool (fn-hp-pes-len h))
        (equal encoded (len (fn-scc-encode ev))) (equal (nth 0 r) :counted)
        (equal (nth 1 r) (len (append h (list ev))))
        (equal (nth 2 r) (fn-hp-pes-len (append h (list ev)))))))
(assert-event
 (let* ((h '(t)) (salt 0) (count (len h)) (pool (fn-hp-pes-len h)))
  (and (fn-hp-okp h salt) (equal count (len h))
       (equal pool (fn-hp-pes-len h))
       (equal (fn-hcc-lens count pool) (fn-hp-lens h salt)))))
; Stale ordinal and representability refusal preserve both scalar totals.
(assert-event
 (let ((r (mv-list 3 (fn-hcc-row 1 8 0 1))))
  (and (not (equal (nth 0 r) :counted))
       (equal (nth 1 r) 1) (equal (nth 2 r) 8))))
(assert-event
 (equal (mv-list 3 (fn-hcc-row 0 0 0 18446744073709551616))
        '(:out-of-range 0 0)))
; Hypothesis removal for the exact codec count; retained census premises hold.
(assert-event
 (let* ((h nil) (ev t) (count 0) (pool 0) (encoded 9)
        (r (mv-list 3 (fn-hcc-row count pool count encoded))))
  (and (equal count (len h)) (equal pool (fn-hp-pes-len h))
       (not (equal encoded (len (fn-scc-encode ev)))) (equal (nth 0 r) :counted)
       (not (and (equal (nth 1 r) (len (append h (list ev))))
                 (equal (nth 2 r) (fn-hp-pes-len (append h (list ev)))))))))
; Residual and terminal capacity boundaries, plus empty capacity.
(assert-event
 (let ((r (mv-list 2 (fn-hcc-cap-tick 3 1))))
  (and (natp 3) (posp 1) (equal (car r) :continue)
       (equal (adt-pow2-at-least 3 (cadr r)) (adt-pow2-at-least 3 1)))))
(assert-event
 (let ((r (mv-list 2 (fn-hcc-cap-tick 3 4))))
  (and (natp 3) (posp 4) (equal (car r) :done)
       (equal (cadr r) (adt-pow2-at-least 3 4)))))
(assert-event (equal (mv-list 2 (fn-hcc-cap-begin 0)) '(0 0)))
(assert-event (equal (mv-list 2 (fn-hcc-cap-tick 0 0)) '(:done 0)))
(assert-event
 (let* ((used 32769) (r (mv-list 2 (fn-hcc-cap-begin used))))
  (and (posp used)
       (equal (adt-pow2-at-least (car r) (cadr r)) (adt-cap used)))))
(assert-event
 (and (natp 2) (natp 24) (equal 1 (adt-cap (* 8 2)))
      (equal (fn-hcc-starts 1) (adt-starts-l (fn-hcc-lens 2 24) 1))
      (equal 1 (adt-cap 24))
      (equal (fn-hcc-pages 1 1) (adt-end-l (fn-hcc-lens 2 24) 1))))
; Mutation: dropping independent row padding undercounts payload region.
(assert-event
 (let* ((h '(t t)) (encoded (len (fn-scc-encode t))))
  (and (equal (fn-hp-pes-len h) 16)
       (not (equal (* 2 encoded) (fn-hp-pes-len h))))))
; Corrupted census count, pool, and stale source ordinal each break exactly
; their omitted boundary premise while retaining the other literal premises.
(assert-event
 (let* ((h nil) (ev t) (count 1) (pool 0) (encoded (len (fn-scc-encode ev)))
        (r (mv-list 3 (fn-hcc-row count pool count encoded))))
  (and (not (equal count (len h))) (equal pool (fn-hp-pes-len h))
       (equal encoded (len (fn-scc-encode ev))) (equal (car r) :counted)
       (not (and (equal (nth 1 r) (len (append h (list ev))))
                 (equal (nth 2 r) (fn-hp-pes-len (append h (list ev)))))))))
(assert-event
 (let* ((h nil) (ev t) (count 0) (pool 8) (encoded (len (fn-scc-encode ev)))
        (r (mv-list 3 (fn-hcc-row count pool count encoded))))
  (and (equal count (len h)) (not (equal pool (fn-hp-pes-len h)))
       (equal encoded (len (fn-scc-encode ev))) (equal (car r) :counted)
       (not (and (equal (nth 1 r) (len (append h (list ev))))
                 (equal (nth 2 r) (fn-hp-pes-len (append h (list ev)))))))))
(assert-event
 (let* ((h nil) (ev t) (count 0) (pool 0) (encoded (len (fn-scc-encode ev)))
        (r (mv-list 3 (fn-hcc-row count pool 1 encoded))))
  (and (equal count (len h)) (equal pool (fn-hp-pes-len h))
       (equal encoded (len (fn-scc-encode ev))) (not (equal (car r) :counted))
       (not (and (equal (nth 1 r) (len (append h (list ev))))
                 (equal (nth 2 r) (fn-hp-pes-len (append h (list ev)))))))))
