(in-package "ACL2")
(include-book "../../books/extent-window-span")

; Test-only archive adapter. SPANP: the host's span drive (fn-ews-span-effect,
; fn-ews-read-span, fn-ews-tick-to-io); otherwise the stream's per-block drive
; (fn-ews-effect, fn-ews-read, fn-ews-tick). CALLS counts host->core calls.
(defun ewsp-run (fuel spanp archive s pgs-digest-state fn-ew-buffer fn-octets reads calls)
  (declare (xargs :stobjs (pgs-digest-state fn-ew-buffer fn-octets)
                  :measure (nfix fuel) :verify-guards nil))
  (cond ((zp fuel) (mv :fuel s pgs-digest-state fn-ew-buffer fn-octets reads calls))
        ((not (member-eq (nth 0 s) '(:scan :trailer)))
         (mv (nth 0 s) s pgs-digest-state fn-ew-buffer fn-octets reads calls))
        (t (let ((effect (if spanp (fn-ews-span-effect s pgs-digest-state)
                           (fn-ews-effect s pgs-digest-state))))
             (if effect
                 (let* ((bytes (fn-b3-firstn (nth 5 effect)
                                   (fn-b3-nthcdrx (- (nth 4 effect) (nth 2 s)) archive)))
                        (fn-octets (fn-octets-from-list bytes fn-octets)))
                   (mv-let (status s pgs-digest-state fn-ew-buffer)
                     (if spanp
                         (fn-ews-read-span effect :ok s fn-octets pgs-digest-state fn-ew-buffer)
                       (fn-ews-read effect :ok s fn-octets pgs-digest-state fn-ew-buffer))
                     (declare (ignore status))
                     (ewsp-run (1- fuel) spanp archive s pgs-digest-state fn-ew-buffer fn-octets
                               (+ reads (len bytes)) (+ calls 2))))
               (mv-let (status s pgs-digest-state)
                 (if spanp (fn-ews-tick-to-io s pgs-digest-state)
                   (fn-ews-tick s pgs-digest-state))
                 (declare (ignore status))
                 (ewsp-run (1- fuel) spanp archive s pgs-digest-state fn-ew-buffer fn-octets
                           reads (+ calls 1))))))))

(defun ewsp-output (n i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer :measure (nfix n) :verify-guards nil))
  (if (zp n) nil
    (cons (fn-ew-bytesi i fn-ew-buffer) (ewsp-output (1- n) (1+ i) fn-ew-buffer))))

; (status publication octets-read window-bytes host-calls)
(defun ewsp-example (spanp msg archive payload-start payload-length offset expected)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (answer pgs-digest-state)
      (with-local-stobj fn-octets
        (mv-let (answer pgs-digest-state fn-octets)
          (with-local-stobj fn-ew-buffer
            (mv-let (answer pgs-digest-state fn-octets fn-ew-buffer)
              (mv-let (s pgs-digest-state)
                (fn-ews-begin 7 100 (len msg) (+ 100 payload-start) payload-length offset
                              23 47 59 expected pgs-digest-state)
                (mv-let (status s pgs-digest-state fn-ew-buffer fn-octets reads calls)
                  (ewsp-run 100000 spanp archive s pgs-digest-state fn-ew-buffer fn-octets 0 0)
                  (mv (list status (fn-ewp-publication s) reads
                            (ewsp-output (nth 5 s) 0 fn-ew-buffer) calls)
                      pgs-digest-state fn-octets fn-ew-buffer)))
              (mv answer pgs-digest-state fn-octets)))
          (mv answer pgs-digest-state)))
      answer)))

; Same verdict, publication, octets read and window bytes; fewer host calls.
(defmacro ewsp-same-answer (msg archive ps pl off expected)
  `(let ((block (ewsp-example nil ,msg ,archive ,ps ,pl ,off ,expected))
         (span (ewsp-example t ,msg ,archive ,ps ,pl ,off ,expected)))
     (and (equal (butlast block 1) (butlast span 1))
          (<= (car (last span)) (car (last block))))))

(assert-event
 (let* ((msg '(0 1 2 3 4 5 6 7 8 9)) (digest (fn-blake3 msg)))
   (and (ewsp-same-answer msg (append msg digest) 2 6 1 (fn-bch-pack digest))
        (equal (butlast (ewsp-example t msg (append msg digest) 2 6 1 (fn-bch-pack digest)) 1)
               '(:verified (23 47 59 7 103 5) 42 (3 4 5 6 7))))))
(assert-event
 (let ((digest (fn-blake3 nil)))
   (ewsp-same-answer nil digest 0 0 0 (fn-bch-pack digest))))
; Partial last block (100 = 64 + 36).
(assert-event
 (let* ((msg (make-list 100 :initial-element 5)) (digest (fn-blake3 msg)))
   (and (ewsp-same-answer msg (append msg digest) 70 30 0 (fn-bch-pack digest))
        (equal (car (ewsp-example t msg (append msg digest) 70 30 0 (fn-bch-pack digest))) :verified))))
(assert-event
 (let* ((msg (append (make-list 1024 :initial-element 9) '(3 4 5)))
        (digest (fn-blake3 msg)))
   (ewsp-same-answer msg (append msg digest) 1022 5 0 (fn-bch-pack digest))))
; Exactly one span, one span plus a block, and two spans plus a 40-octet tail.
(assert-event
 (let* ((msg (make-list 16384 :initial-element 7)) (digest (fn-blake3 msg)))
   (ewsp-same-answer msg (append msg digest) 1 16000 0 (fn-bch-pack digest))))
(assert-event
 (let* ((msg (make-list 16448 :initial-element 7)) (digest (fn-blake3 msg)))
   (ewsp-same-answer msg (append msg digest) 1 16000 0 (fn-bch-pack digest))))
(assert-event
 (let* ((msg (make-list 33000 :initial-element 6)) (digest (fn-blake3 msg))
        (block (ewsp-example nil msg (append msg digest) 3 32000 0 (fn-bch-pack digest)))
        (span (ewsp-example t msg (append msg digest) 3 32000 0 (fn-bch-pack digest))))
   (and (equal (butlast block 1) (butlast span 1))
        (equal (car span) :verified)
        (equal (caddr span) 33032)
        ; 33000/64 -> 516 block reads; 3 spans (16384, 16384, 232) -> 3 reads
        (< (car (last span)) 20)
        (< 1000 (car (last block))))))

; Failures stay distinct and equal under the span drive: damaged prefix,
; wrong commitment, short archive.
(assert-event
 (let* ((msg '(1 2 3)) (digest (fn-blake3 msg)))
   (and (equal (car (ewsp-example t msg (append '(1 2 4) digest) 0 3 0 (fn-bch-pack digest))) :digest)
        (not (cadr (ewsp-example t msg (append '(1 2 4) digest) 0 3 0 (fn-bch-pack digest))))
        (ewsp-same-answer msg (append '(1 2 4) digest) 0 3 0 (fn-bch-pack digest))
        (equal (car (ewsp-example t msg (append msg digest) 0 3 0 0)) :commitment)
        (equal (car (ewsp-example t msg '(1 2) 0 3 0 (fn-bch-pack digest))) :read))))
; A damaged octet in the second span of a long prefix is still caught.
(assert-event
 (let* ((msg (make-list 20000 :initial-element 4)) (digest (fn-blake3 msg))
        (bad (append (make-list 18000 :initial-element 4) '(5) (make-list 1999 :initial-element 4))))
   (and (equal (car (ewsp-example t msg (append bad digest) 0 10 0 (fn-bch-pack digest))) :digest)
        (ewsp-same-answer msg (append bad digest) 0 10 0 (fn-bch-pack digest)))))

; One span call on a 100-octet prefix, with the stream state after it.
(defun ewsp-one-call (mutantp)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (answer pgs-digest-state)
      (with-local-stobj fn-octets
        (mv-let (answer pgs-digest-state fn-octets)
          (with-local-stobj fn-ew-buffer
            (mv-let (answer pgs-digest-state fn-octets fn-ew-buffer)
              (let* ((msg (make-list 100 :initial-element 5))
                     (archive (append msg (fn-blake3 msg))))
                (mv-let (s pgs-digest-state)
                  (fn-ews-begin 7 100 100 100 30 0 23 47 59 (fn-bch-pack (fn-blake3 msg)) pgs-digest-state)
                  (mv-let (status s pgs-digest-state) (fn-ews-tick-to-io s pgs-digest-state)
                    (declare (ignore status))
                    (let* ((effect (fn-ews-span-effect s pgs-digest-state))
                           (fn-octets (fn-octets-from-list
                                       (fn-b3-firstn (nth 5 effect) (fn-b3-nthcdrx (- (nth 4 effect) 100) archive))
                                       fn-octets)))
                      (mv-let (status s pgs-digest-state fn-ew-buffer)
                        (if mutantp
                            ; the span loop without the last partial block: floor, not ceiling
                            (fn-ews-span-loop (floor (fn-ews-span-demand s) 64) 0 s fn-octets
                                              pgs-digest-state fn-ew-buffer)
                          (fn-ews-read-span effect :ok s fn-octets pgs-digest-state fn-ew-buffer))
                        (mv (list status (nth 0 s) (nth 7 s) (nth 5 effect))
                            pgs-digest-state fn-octets fn-ew-buffer))))))
              (mv answer pgs-digest-state fn-octets)))
          (mv answer pgs-digest-state)))
      answer)))

; Must-fail tooth: a span read that skips the last partial block does not
; reach the trailer; the real one consumes all 100 octets (64 + 36).
(assert-event (equal (ewsp-one-call nil) '(:read :trailer 100 100)))
(assert-event (equal (ewsp-one-call t) '(:read :scan 64 100)))
(assert-event (not (equal (ewsp-one-call nil) (ewsp-one-call t))))

; Fuel exhaustion is reachable and resumable: after a block is loaded the
; cursor needs more than one tick, so a one-tick run answers :continue and the
; loop that re-enters it reaches the same stream state as the one run.
(defun ewsp-reenter (n s pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (and (natp n) (true-listp s))
                  :measure (nfix (- 1000 (nfix n))) :verify-guards nil))
  (mv-let (status s pgs-digest-state)
    (fn-ews-tick-run 1 s pgs-digest-state)
    (if (and (eq status :continue) (< (nfix n) 1000))
        (ewsp-reenter (1+ (nfix n)) s pgs-digest-state)
      (mv (1+ (nfix n)) status s pgs-digest-state))))

; N block cycles of the stream's own drive (tick to I/O, read one block).
(defun ewsp-cycles (n archive s pgs-digest-state fn-ew-buffer fn-octets)
  (declare (xargs :stobjs (pgs-digest-state fn-ew-buffer fn-octets)
                  :measure (nfix n) :verify-guards nil))
  (if (zp n)
      (mv s pgs-digest-state fn-ew-buffer fn-octets)
    (mv-let (status s pgs-digest-state) (fn-ews-tick-to-io s pgs-digest-state)
      (declare (ignore status))
      (let ((effect (fn-ews-effect s pgs-digest-state)))
        (if (not effect)
            (mv s pgs-digest-state fn-ew-buffer fn-octets)
          (let ((fn-octets (fn-octets-from-list
                            (fn-b3-firstn (nth 5 effect) (fn-b3-nthcdrx (- (nth 4 effect) 100) archive))
                            fn-octets)))
            (mv-let (status s pgs-digest-state fn-ew-buffer)
              (fn-ews-read effect :ok s fn-octets pgs-digest-state fn-ew-buffer)
              (declare (ignore status))
              (ewsp-cycles (1- n) archive s pgs-digest-state fn-ew-buffer fn-octets))))))))

; Sixteen blocks end a chunk: the cursor then needs several ticks before it asks
; for more input, so a one-tick run exhausts its fuel (:continue) at least once.
(defun ewsp-after-chunk (reenterp)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (answer pgs-digest-state)
      (with-local-stobj fn-octets
        (mv-let (answer pgs-digest-state fn-octets)
          (with-local-stobj fn-ew-buffer
            (mv-let (answer pgs-digest-state fn-octets fn-ew-buffer)
              (let* ((msg (make-list 3000 :initial-element 5))
                     (archive (append msg (fn-blake3 msg))))
                (mv-let (s pgs-digest-state)
                  (fn-ews-begin 7 100 3000 100 30 0 23 47 59 (fn-bch-pack (fn-blake3 msg)) pgs-digest-state)
                  (mv-let (s pgs-digest-state fn-ew-buffer fn-octets)
                    (ewsp-cycles 16 archive s pgs-digest-state fn-ew-buffer fn-octets)
                    (if reenterp
                        (mv-let (n status s pgs-digest-state)
                          (ewsp-reenter 0 s pgs-digest-state)
                          (mv (list n status s) pgs-digest-state fn-octets fn-ew-buffer))
                      (mv-let (status s pgs-digest-state)
                        (fn-ews-tick-to-io s pgs-digest-state)
                        (mv (list 1 status s) pgs-digest-state fn-octets fn-ew-buffer))))))
              (mv answer pgs-digest-state fn-octets)))
          (mv answer pgs-digest-state)))
      answer)))

(assert-event
 (let ((one (ewsp-after-chunk t)) (io (ewsp-after-chunk nil)))
   (and (< 1 (car one))              ; exhausted at least once, re-entered
        (equal (cadr one) :read)
        (equal (cdr one) (cdr io))))) ; same status, same stream state
