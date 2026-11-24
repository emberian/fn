; The scalar parser consumes exactly the canonical base-128 prefix. At
; byte eight only the final four bits of a 60-bit value may remain.
(in-package "ACL2")
(include-book "runs-page")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(local
 (defthm fn2-run-split-varint-digit
   (implies (natp n)
            (and (equal (+ (mod n 128) (* 128 (floor n 128))) n)
                 (equal (mod (+ 128 (mod n 128)) 128) (mod n 128))))
   :rule-classes nil))

(local
 (defun fn2-run-varint-parser-events (pos)
   (declare (xargs :verify-guards nil :measure (nfix (- 9 pos))))
   (if (or (not (natp pos)) (>= pos 9)) nil
     (let* ((scale (expt 128 pos)) (room (expt 2 (- 60 (* 7 pos))))
            (name (packn-pos (list 'fn2-run-parse-varint-byte- pos) 'fn2-layout-parse-field)))
       (append (fn2-run-varint-parser-events (1+ pos))
         (list
          `(defthm ,name
             (implies (and (or (equal (fn2-layout-kind-code k) 5) (equal (fn2-layout-kind-code k) 8))
                           (not (equal k '(:zero 0))) (natp n) (< n ,room)
                           ,@(and (< 0 pos) '((posp n))) (natp acc))
                      (equal (fn2-layout-parse-field k bytes (append (fn2-layout-varoctets n) suffix)
                                                      ,pos acc 0 0 ref 0 next)
                             (list :ok (+ acc (* ,scale n)) suffix)))
             :hints (("Goal" :do-not-induct t :cases ((< n 128))
                      :use (fn2-run-split-varint-digit
                            ,@(and (< pos 8)
                               `((:instance ,(packn-pos (list 'fn2-run-parse-varint-byte- (1+ pos)) 'fn2-layout-parse-field)
                                   (n (floor n 128)) (acc (+ acc (* ,scale (mod n 128)))) (next (1+ (nfix next)))))))
                      :expand ((fn2-layout-varoctets n)
                               (:free (d rest) (fn2-layout-parse-field k bytes (cons d rest) ,pos acc 0 0 ref 0 next)))
                      :in-theory (e/d (fn2-layout-byte ash)
                                (fn2-layout-kind-code fn2-layout-parse-field fn2-layout-varoctets floor mod))))
             :rule-classes nil)))))))

(local (make-event (cons 'progn (fn2-run-varint-parser-events 0))))

(defthmd fn2-run-parse-header-varint
  (implies (and (or (equal (fn2-layout-kind-code k) 5) (equal (fn2-layout-kind-code k) 8))
                (not (equal k '(:zero 0))) (unsigned-byte-p 60 n))
           (equal (fn2-layout-parse-field k bytes (append (fn2-layout-varoctets n) suffix)
                                           0 0 0 0 0 0 0)
                  (list :ok n suffix)))
  :hints (("Goal" :use ((:instance fn2-run-parse-varint-byte-0 (acc 0) (ref 0) (next 0)))
           :in-theory (disable fn2-layout-kind-code fn2-layout-parse-field fn2-layout-varoctets binary-append))))

(local
 (defun fn2-run-base128-width-walk (n limit)
   (declare (xargs :measure (nfix n)))
   (if (or (not (natp n)) (< n 128)) limit
     (fn2-run-base128-width-walk (floor n 128) (floor limit 128)))))

(local
 (defthm fn2-run-varint-width-monotone
   (implies (and (natp n) (natp limit) (<= n limit))
            (<= (len (fn2-layout-varoctets n)) (len (fn2-layout-varoctets limit))))
   :hints (("Goal" :induct (fn2-run-base128-width-walk n limit)
            :expand ((fn2-layout-varoctets n) (fn2-layout-varoctets limit))
            :in-theory (disable fn2-layout-varoctets)))
   :rule-classes nil))

(defthmd fn2-run-header-varint-fits
  (implies (unsigned-byte-p 60 n) (<= (len (fn2-layout-varoctets n)) 9))
  :hints (("Goal" :use ((:instance fn2-run-varint-width-monotone (limit #xfffffffffffffff)))
           :in-theory (disable fn2-layout-varoctets))))
