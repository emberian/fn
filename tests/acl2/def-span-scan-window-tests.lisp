; K-W1/K-W2/K-W4: live drivers, one workspace, cap 8, fill 2.
; K-W3: the exact requested renderer statement has a checked counterexample.
(in-package "ACL2")
(include-book "../../books/def-span-scan-window")
(include-book "std/testing/assert-bang" :dir :system)

(defun dsw-t-map (o) (declare (xargs :guard t)) o)
(local (defattach fn-dss-copy-f dsw-t-map))

(defun dsw-t-bytes (h i end fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil :measure (nfix (- (nfix end) (nfix i)))))
  (if (and (natp i) (natp end) (< i end))
      (cons (fn-rtc-st-byte h i fn-rtc-st) (dsw-t-bytes h (+ 1 i) end fn-rtc-st))
    nil))

(defun dsw-t-state (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil))
  (list (fn-rtc-st-config fn-rtc-st)
        (list (fn-rtc-st-slot 0 fn-rtc-st) (fn-rtc-st-slot 1 fn-rtc-st))
        (list (list (fn-rtc-st-gen 0 fn-rtc-st) (fn-rtc-st-owner 0 fn-rtc-st)
                    (dsw-t-bytes 0 0 (fn-rtc-st-fill 0 fn-rtc-st) fn-rtc-st)))
        (fn-rtc-st-uses fn-rtc-st)
        (list (fn-rtc-st-mstate 0 fn-rtc-st) (fn-rtc-st-mstate 1 fn-rtc-st))
        (fn-rtc-st-next-op fn-rtc-st)))

(defun dsw-t-seed (cap fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil))
  (let* ((fn-rtc-st (fn-rtc-st-init (list 2 1 0 0 0 1 cap) fn-rtc-st))
         (fn-rtc-st (fn-rtc-st-reset 0 1 '(:workspace 1 1) fn-rtc-st))
         (fn-rtc-st (fn-rtc-st-put 0 0 1 fn-rtc-st)))
    (fn-rtc-st-put 0 1 2 fn-rtc-st)))

(defun dsw-t-write (kind n fn-octets fn-rtc-st)
  (declare (xargs :stobjs (fn-octets fn-rtc-st) :verify-guards nil))
  (case kind
    (:copy (fn-dsw-copy 0 0 3 2 fn-octets fn-rtc-st))
    (:string (fn-dsw-copy-string 0 1 4 2 "x345y" fn-rtc-st))
    (:decimal (fn-dsw-decimal 0 2 n fn-rtc-st))
    (otherwise (fn-dsw-append 0 2 '(3 4 5) fn-rtc-st))))

(defun dsw-t-check (kind cap n fn-octets fn-rtc-st)
  (declare (xargs :stobjs (fn-octets fn-rtc-st) :verify-guards nil))
  (let* ((fn-rtc-st (dsw-t-seed cap fn-rtc-st))
         (fn-octets (fn-octets-from-list '(3 4 5) fn-octets))
         (before (dsw-t-state fn-rtc-st))
         (data (case kind (:string '(51 52 53)) (:decimal (fn-nntp-decimal n)) (otherwise '(3 4 5))))
         (fits (fn-rtc-splice-okp 0 2 data before)))
    (mv-let (sig j fn-rtc-st) (dsw-t-write kind n fn-octets fn-rtc-st)
      (let ((after (dsw-t-state fn-rtc-st)))
        (mv (and (fn-rtc-st$ap before)
                 (equal (fn-rtc-st$a-fill 0 before) 2)
                 (fn-rtc-splice-target-p 0 (fn-rtc-b-owner (fn-rtc-buffer 0 before)) (fn-rtc-uses before))
                 (equal sig (if fits :done :refused))
                 (equal j (if fits (+ 2 (len data)) 2))
                 (equal after (if fits (fn-rtc-st$a-splice 0 2 data before) before))
                 (if fits
                     (and (natp 0) (<= 0 2) (equal 2 (fn-rtc-st$a-fill 0 before))
                          (equal (fn-dsw-view 0 0 j after) (append (fn-dsw-view 0 0 2 before) data)))
                   (and (< cap (+ 2 (len data))) (equal after before))))
            fn-octets fn-rtc-st)))))

(defun dsw-t-value (kind cap n)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (ok fn-octets)
      (with-local-stobj fn-rtc-st
        (mv-let (ok fn-octets fn-rtc-st) (dsw-t-check kind cap n fn-octets fn-rtc-st)
          (mv ok fn-octets)))
      ok)))

(assert-event (dsw-t-value :copy 8 0))
(assert-event (dsw-t-value :string 8 0))
(assert-event (dsw-t-value :append 8 0))
(assert-event (dsw-t-value :decimal 8 123))
(assert-event (dsw-t-value :copy 4 0))
(assert-event (dsw-t-value :string 4 0))
(assert-event (dsw-t-value :append 4 0))
(assert-event (dsw-t-value :decimal 4 123))
(assert-event (dsw-t-value :decimal 8 0))
(assert-event (dsw-t-value :decimal 8 9))
(assert-event (dsw-t-value :decimal 8 10))
(assert-event (dsw-t-value :decimal 8 100))
(assert-event (dsw-t-value :decimal 8 100000))
(assert-event (dsw-t-value :decimal 8 1000000))
(assert-event (dsw-t-value :decimal 8 -1))

(defconst *dsw-t-s* '((2 1 0 0 0 1 8) ((0 :live nil) (1 :live nil))
                     ((1 (:workspace 1 1) (1 2))) nil (nil nil) 0))
; K-W2's J=fill premise is redundant: the view excludes the stale tail.
; Positive below-fill witness, with exactly that premise false.
(assert-event
 (let ((s *dsw-t-s*) (data '(3 4 5)))
   (and (fn-rtc-st$ap s) (natp 0) (<= 0 1) (fn-rtc-splice-okp 0 1 data s)
        (not (equal 1 (fn-rtc-st$a-fill 0 s)))
        (equal (fn-dsw-view 0 0 4 (fn-rtc-st$a-splice 0 1 data s))
               (append (fn-dsw-view 0 0 1 s) data)))))
; K-W1 mutation: writing each octet at J+k+1 first refuses because J+1 is past fill.
(defun dsw-t-shifted-puts (h j data s)
  (declare (xargs :guard t))
  (if (consp data)
      (dsw-t-shifted-puts h (+ 1 (nfix j)) (cdr data) (fn-rtc-st$a-put h (+ 1 (nfix j)) (car data) s))
    s))
(assert-event
 (and (fn-rtc-st$ap *dsw-t-s*) (fn-rtc-splice-okp 0 2 '(3 4 5) *dsw-t-s*)
      (not (equal (dsw-t-shifted-puts 0 2 '(3 4 5) *dsw-t-s*)
                  (fn-rtc-st$a-splice 0 2 '(3 4 5) *dsw-t-s*)))))
; K-W3 counterexample is checked over the actual functions by logical rewriting;
; no MAP evaluation is needed: the logical source slice is empty.
(defthm dsw-t-k-w3-counterexample
  (let ((s *dsw-t-s*) (base 0) (j 2) (i -1) (end 10) (fn-octets '(3 4 5)))
    (and (fn-rtc-st$ap s) (<= base j) (equal j (fn-rtc-st$a-fill 0 s))
         (fn-rtc-splice-target-p 0 (fn-rtc-b-owner (fn-rtc-buffer 0 s)) (fn-rtc-uses s))
         (equal (fn-dss-copy i end (- (fn-rtc-buf-cap 0 (fn-rtc-config s)) base)
                             fn-octets (fn-dsw-view 0 base j s))
                (mv :refused '(1 2)))
         (equal (fn-dsw-copy 0 i end j fn-octets s) (mv :done 2 s))))
  :hints (("Goal" :in-theory (enable fn-dsw-copy fn-oct-slice-list fn-dss-copy-list fn-dsw-append
                                    fn-dsw-roomp fn-dsw-append-loop fn-dsw-view fn-dss-copy)))
  :rule-classes nil)

; K-W2: one removal per remaining hypothesis, all others asserted.
(defthm dsw-t-k-w2-recognizer-tooth
  (let* ((s '((2 1 0 0 0 1 8) (nil nil) nil
             ((:recv 1 1 1 (0 1 0 1))) (nil nil) 0)) (data '(3)))
   (and (not (fn-rtc-st$ap s)) (natp 0) (<= 0 0) (fn-rtc-splice-okp 0 0 data s)
        (equal 0 (fn-rtc-st$a-fill 0 s))
        (not (equal (fn-dsw-view 0 0 1 (fn-rtc-st$a-splice 0 0 data s))
                    (append (fn-dsw-view 0 0 0 s) data)))))
  :hints (("Goal" :in-theory (enable fn-dsw-view take nthcdr)))
  :rule-classes nil)
(defthm dsw-t-k-w2-base-natural-tooth
  (let ((s *dsw-t-s*) (data '(3 4 5)))
   (and (fn-rtc-st$ap s) (not (natp -1)) (<= -1 2) (fn-rtc-splice-okp 0 2 data s)
        (equal 2 (fn-rtc-st$a-fill 0 s))
        (not (equal (fn-dsw-view 0 -1 5 (fn-rtc-st$a-splice 0 2 data s))
                    (append (fn-dsw-view 0 -1 2 s) data)))))
  :hints (("Goal" :in-theory (enable fn-dsw-view take nthcdr)))
  :rule-classes nil)
(defthm dsw-t-k-w2-base-within-view-tooth
  (let ((s *dsw-t-s*) (data '(3 4 5)))
   (and (fn-rtc-st$ap s) (natp 3) (not (<= 3 2)) (fn-rtc-splice-okp 0 2 data s)
        (equal 2 (fn-rtc-st$a-fill 0 s))
        (not (equal (fn-dsw-view 0 3 5 (fn-rtc-st$a-splice 0 2 data s))
                    (append (fn-dsw-view 0 3 2 s) data)))))
  :hints (("Goal" :in-theory (enable fn-dsw-view take nthcdr)))
  :rule-classes nil)
(defthm dsw-t-k-w2-admission-tooth
  (let ((s *dsw-t-s*) (data '(300)))
   (and (fn-rtc-st$ap s) (natp 0) (<= 0 2) (not (fn-rtc-splice-okp 0 2 data s))
        (equal 2 (fn-rtc-st$a-fill 0 s))
        (not (equal (fn-dsw-view 0 0 3 (fn-rtc-st$a-splice 0 2 data s))
                    (append (fn-dsw-view 0 0 2 s) data)))))
  :hints (("Goal" :in-theory (enable fn-dsw-view take nthcdr)))
  :rule-classes nil)

(defthm dsw-t-k-w1-recognizer-tooth
  (let ((s (append *dsw-t-s* '(extra))))
    (and (not (fn-rtc-st$ap s)) (fn-rtc-splice-okp 0 2 nil s)
         (equal (fn-dsw-append 0 2 nil s) (mv :done 2 s))
         (not (equal (fn-dsw-append 0 2 nil s)
                     (mv :done 2 (fn-rtc-st$a-splice 0 2 nil s))))))
  :hints (("Goal" :in-theory (enable fn-dsw-append fn-dsw-roomp fn-dsw-append-loop)))
  :rule-classes nil)

; K-W3 also needs H to name a natural buffer index: its target predicate
; alone is true at H=-1 because fn-rtc-buffer uses nfix, while window admission refuses.
(defthm dsw-t-k-w3-handle-counterexample
  (let ((s *dsw-t-s*) (h -1) (base 0) (j 2) (fn-octets nil))
    (and (fn-rtc-st$ap s) (<= base j) (equal j (fn-rtc-st$a-fill h s))
         (fn-rtc-splice-target-p h (fn-rtc-b-owner (fn-rtc-buffer h s)) (fn-rtc-uses s))
         (equal (fn-dss-copy 0 0 (- (fn-rtc-buf-cap h (fn-rtc-config s)) base)
                             fn-octets (fn-dsw-view h base j s)) (mv :done '(1 2)))
         (equal (fn-dsw-copy h 0 0 j fn-octets s) (mv :refused 2 s))))
  :hints (("Goal" :in-theory (enable fn-dsw-copy fn-oct-slice-list fn-dss-copy-list fn-dsw-append
                                    fn-dsw-roomp fn-dsw-append-loop fn-dsw-view fn-dss-copy fn-dss-copy-loop)))
  :rule-classes nil)

; Satisfiable K-W3 instance: the actual renderer and the actual window writer
; at natural, admitted indices, not merely a comparison of two model expressions.
(defun dsw-t-render-check (fn-octets fn-dss-out fn-rtc-st)
  (declare (xargs :stobjs (fn-octets fn-dss-out fn-rtc-st) :verify-guards nil))
  (let* ((fn-rtc-st (dsw-t-seed 8 fn-rtc-st))
         (fn-octets (fn-octets-from-list '(3 4 5) fn-octets))
         (fn-dss-out (fn-dss-out-from-list '(1 2) fn-dss-out))
         (before (dsw-t-state fn-rtc-st)))
    (mv-let (sig1 fn-dss-out) (fn-dss-copy 0 3 8 fn-octets fn-dss-out)
      (mv-let (sig2 j fn-rtc-st) (fn-dsw-copy 0 0 3 2 fn-octets fn-rtc-st)
        (mv (and (fn-rtc-st$ap before) (<= 0 2) (equal 2 (fn-rtc-st$a-fill 0 before))
                 (fn-rtc-splice-target-p 0 (fn-rtc-b-owner (fn-rtc-buffer 0 before)) (fn-rtc-uses before))
                 (equal sig1 :done) (equal sig1 sig2) (equal j 5)
                 (equal (fn-dss-out-list fn-dss-out) (fn-dsw-view 0 0 j (dsw-t-state fn-rtc-st))))
            fn-octets fn-rtc-st fn-dss-out)))))
(defun dsw-t-render-value ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (ok fn-octets)
      (with-local-stobj fn-rtc-st
        (mv-let (ok fn-octets fn-rtc-st)
          (with-local-stobj fn-dss-out
            (mv-let (ok fn-octets fn-rtc-st fn-dss-out) (dsw-t-render-check fn-octets fn-dss-out fn-rtc-st)
              (mv ok fn-octets fn-rtc-st)))
          (mv ok fn-octets)))
      ok)))
(assert-event (dsw-t-render-value))
