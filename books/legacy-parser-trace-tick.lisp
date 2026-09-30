; Source execution observer. Observer storage is not charged as parser storage.
; Events describe operations actually selected; runtime lowering stays assumed.
(in-package "ACL2")
(include-book "legacy-parser-trace")

(defund fn-lpt-stop (s fuel)
 (let* ((length (fn-lpt-at 1 s)) (position (fn-lpt-at 3 s)))
  (if (zp fuel)
      (cons t (list (list :borrow 'zp)))
    (cons (<= (car length) (car position))
      (append (list (list :borrow 'zp)) (cdr length) (cdr position)
        (list (list :borrow '<=)))))))

(defthm fn-lpt-stop-value-projection
 (equal (car (fn-lpt-stop s fuel))
   (or (zp fuel) (<= (fn-lpc-at 1 s) (fn-lpc-at 3 s))))
 :hints (("Goal" :in-theory (enable fn-lpt-stop))))

; Unlike the actual function, this proof-only observer builds a trace. The
; fifth result never enters the served cursor or influences its decision.
(defund fn-lpt-tick (s fuel fn-arena)
 (declare (xargs :stobjs fn-arena :measure (nfix fuel)
   :verify-guards nil :ruler-extenders :all
   :hints (("Goal" :in-theory (enable fn-lpt-stop)))))
 (let ((stop (fn-lpt-stop s fuel)))
  (if (car stop)
   (let ((verdict (fn-lpt-verdict s)))
    (mv s 0 0 (car verdict)
     (cons (list :enter 'fn-lpc-tick)
      (append (cdr stop) (cdr verdict)
       (list (list :constructor 'mv 4) (list :leave 'fn-lpc-tick))))))
   (let* ((handle (fn-lpt-at 0 s)) (position (fn-lpt-at 3 s))
          (byte (fn-arena-get (car handle) (car position) fn-arena))
          (transition (fn-lpt-byte s byte)))
    (mv-let (next consumed work verdict trace)
     (fn-lpt-tick (car transition) (1- fuel) fn-arena)
     (mv next (+ 1 consumed) (+ 1 work) verdict
      (cons (list :enter 'fn-lpc-tick)
       (append (cdr stop) (cdr handle) (cdr position)
        (list (list :arena-read (car handle) (car position)))
        (cdr transition) (list (list :signed '1- (list fuel))) trace
        (list (list :signed '+ (list 1 consumed))
              (list :signed '+ (list 1 work))
              (list :constructor 'mv 4) (list :leave 'fn-lpc-tick))))))))))

(defthm fn-lpt-tick-value-effect-projection
 (and (equal (mv-nth 0 (fn-lpt-tick s fuel fn-arena))
             (mv-nth 0 (fn-lpc-tick s fuel fn-arena)))
      (equal (mv-nth 1 (fn-lpt-tick s fuel fn-arena))
             (mv-nth 1 (fn-lpc-tick s fuel fn-arena)))
      (equal (mv-nth 2 (fn-lpt-tick s fuel fn-arena))
             (mv-nth 2 (fn-lpc-tick s fuel fn-arena)))
      (equal (mv-nth 3 (fn-lpt-tick s fuel fn-arena))
             (mv-nth 3 (fn-lpc-tick s fuel fn-arena))))
 :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
    :in-theory (e/d (fn-lpt-tick fn-lpc-tick)
     (fn-lpc-byte fn-lpc-at fn-lpc-verdict)))))
