(in-package "ACL2")
(include-book "../../books/assumptions-selected-runtime-allocation-geometry")
; MODEL ONLY: local witness, not a native allocator trajectory or attestation.
(encapsulate ()
 (local
  (defun srag-t-coordinate () *fn-srag-coordinate*))
 (local
  (defun srag-t-growth (n p g c)
   (if (fn-srag-request-domain-p n p g c)
       (fn-srag-request-prefix-demand n p g)
     (+ 1 (fn-srag-request-prefix-demand n p g)))))
 (local (assert-event
  (let ((c (srag-t-coordinate)))
   (and (fn-srag-request-domain-p 16 32768 0 c)
        (equal (fn-srag-request-prefix-demand 16 32768 0) 65664)
        (<= (srag-t-growth 16 32768 0 c)
            (fn-srag-request-prefix-demand 16 32768 0))))))
 ; Coordinate removal: all numeric domain clauses affirmatively retained.
 (local (assert-event
  (let ((c :different-runtime))
   (and (posp 16) (< 16 (expt 2 44)) (equal 32768 32768) (equal 0 0)
        (not (fn-srag-coordinate-p c))
        (not (<= (srag-t-growth 16 32768 0 c)
                 (fn-srag-request-prefix-demand 16 32768 0)))))))
 ; Positive-request removal.
 (local (assert-event
  (let ((c (srag-t-coordinate)))
   (and (fn-srag-coordinate-p c) (< 0 (expt 2 44))
        (equal 32768 32768) (equal 0 0) (not (posp 0))
        (not (<= (srag-t-growth 0 32768 0 c)
                 (fn-srag-request-prefix-demand 0 32768 0)))))))
 ; Request-size domain removal, remaining domain retained.
 (local (assert-event
  (let ((n (expt 2 44)) (c (srag-t-coordinate)))
   (and (fn-srag-coordinate-p c) (posp n) (equal 32768 32768) (equal 0 0)
        (not (< n (expt 2 44)))
        (not (<= (srag-t-growth n 32768 0 c)
                 (fn-srag-request-prefix-demand n 32768 0)))))))
 ; Exact observed page removal.
 (local (assert-event
  (let ((c (srag-t-coordinate)))
   (and (fn-srag-coordinate-p c) (posp 16) (< 16 (expt 2 44)) (equal 0 0)
        (not (equal 16384 32768))
        (not (<= (srag-t-growth 16 16384 0 c)
                 (fn-srag-request-prefix-demand 16 16384 0)))))))
 ; Exact observed granularity removal.
 (local (assert-event
  (let ((c (srag-t-coordinate)))
   (and (fn-srag-coordinate-p c) (posp 16) (< 16 (expt 2 44)) (equal 32768 32768)
        (not (equal 32768 0))
        (not (<= (srag-t-growth 16 32768 32768 c)
                 (fn-srag-request-prefix-demand 16 32768 32768)))))))
 (local
  (defun srag-t-roster-growth (xs p g c)
   (if (endp xs) 0
     (+ (srag-t-growth (car xs) p g c)
        (srag-t-roster-growth (cdr xs) p g c)))))
 (local (assert-event
  (let ((c (srag-t-coordinate)) (xs '(16 32 4112)))
   (and (fn-srag-roster-domain-p xs 32768 0 c)
        (equal (fn-srag-roster-request-octets xs) 4160)
        (equal (fn-srag-counted-prefix-demand 4160 3 32768 0) 205216)
        (<= (srag-t-roster-growth xs 32768 0 c)
            (fn-srag-counted-prefix-demand 4160 3 32768 0)))))))
