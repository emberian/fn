; Span zero and span copy against their bytewise models: multi-page zeroing,
; copy at nonzero source and destination offsets, fill advancement, and
; refused spans whose written prefix and refusal code are the model's own.
; Each scenario runs once through the span exports and once through the
; models; both runs must agree with each other and with the stated values.
(in-package "ACL2")
(include-book "../books/pool-span")
(include-book "std/util/bstar" :dir :system)

(defun fn2-pst-put (slot gen idx n byte fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix n)))
  (if (zp n) fn2-pool
    (mv-let (code fn2-pool) (fn2-pool-write slot gen idx byte 1 10 3 fn2-pool)
      (declare (ignore code))
      (fn2-pst-put slot gen (+ 1 idx) (- n 1) byte fn2-pool))))
(defun fn2-pst-put-list (slot gen idx bytes fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom bytes) fn2-pool
    (mv-let (code fn2-pool) (fn2-pool-write slot gen idx (car bytes) 1 10 3 fn2-pool)
      (declare (ignore code))
      (fn2-pst-put-list slot gen (+ 1 idx) (cdr bytes) fn2-pool))))
(defun fn2-pst-iota (from n)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) nil (cons from (fn2-pst-iota (+ 1 from) (- n 1)))))
; Raw octets of a slot's extent, read past the fill as well.
(defun fn2-pst-octets (i n fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix n)))
  (if (zp n) nil
    (cons (fn2-pool-datai i fn2-pool) (fn2-pst-octets (+ 1 i) (- n 1) fn2-pool))))
(defun fn2-pst-count (byte xs)
  (declare (xargs :verify-guards nil))
  (cond ((atom xs) 0)
        ((equal (car xs) byte) (+ 1 (fn2-pst-count byte (cdr xs))))
        (t (fn2-pst-count byte (cdr xs)))))
(defun fn2-pst-at (positions xs)
  (declare (xargs :verify-guards nil))
  (if (atom positions) nil
    (cons (nth (car positions) xs) (fn2-pst-at (cdr positions) xs))))

; MODE :span runs the exports, :model the bytewise references.
(defun fn2-pst-zero (mode n slot gen off okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (eq mode :span)
      (fn2-pool-zero-span n slot gen off okind oslot ogen fn2-pool)
    (fn2-pool-zero-bytes n slot gen off okind oslot ogen fn2-pool)))
(defun fn2-pst-copy (mode n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (eq mode :span)
      (fn2-rd-copy-span n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
    (fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)))

; Two 16384-octet slots (four 4096-octet pages each) and three 64-octet ones.
; Every handle below is owned by (1 10 3).
(defun fn2-pst-run (mode fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (b* ((fn2-pool (fn2-pool-init '((2 . 16384) (3 . 64)) 5 20 fn2-pool))
       ((mv & a ag fn2-pool) (fn2-pool-reserve 0 1 10 3 fn2-pool))
       ((mv & c cg fn2-pool) (fn2-pool-reserve 1 1 10 3 fn2-pool))
       ((mv & b bg fn2-pool) (fn2-pool-reserve 1 1 10 3 fn2-pool))
       ((mv & d dg fn2-pool) (fn2-pool-reserve 1 1 10 3 fn2-pool))
       ; Multi-page zero: 13000 octets of #xAB, then three pages zeroed from
       ; offset 512, then the tail from the fill to the capacity.
       (fn2-pool (fn2-pst-put a ag 0 13000 171 fn2-pool))
       ((mv z1 fn2-pool) (fn2-pst-zero mode 12288 a ag 512 1 10 3 fn2-pool))
       (z1-fill (fn2-pool-slot-fill a fn2-pool))
       ((mv z2 fn2-pool) (fn2-pst-zero mode 3384 a ag 13000 1 10 3 fn2-pool))
       ((mv z3 fn2-pool) (fn2-pst-zero mode 0 a ag 99999 1 10 3 fn2-pool))
       ((mv z4 fn2-pool) (fn2-pst-zero mode 8 a ag 0 2 11 4 fn2-pool))          ; not the owner
       ((mv z5 fn2-pool) (fn2-pst-zero mode 8 a (+ 1 ag) 0 1 10 3 fn2-pool))    ; stale generation
       (a-octets (fn2-pst-octets (fn2-pool-slot-base a fn2-pool) 16384 fn2-pool))
       ; Refused zero spans on a 64-octet slot holding 1..60.
       (fn2-pool (fn2-pst-put-list c cg 0 (fn2-pst-iota 1 60) fn2-pool))
       ((mv zc0 fn2-pool) (fn2-pst-zero mode 3 c cg 61 1 10 3 fn2-pool))        ; opens a gap
       ((mv zc1 fn2-pool) (fn2-pst-zero mode 20 c cg 50 1 10 3 fn2-pool))       ; past the capacity
       (zc1-fill (fn2-pool-slot-fill c fn2-pool))
       ; Copies: B holds 100..109, D holds 200..203.
       (fn2-pool (fn2-pst-put-list b bg 0 (fn2-pst-iota 100 10) fn2-pool))
       (fn2-pool (fn2-pst-put-list d dg 0 (fn2-pst-iota 200 4) fn2-pool))
       ((mv k1 fn2-pool) (fn2-pst-copy mode 5 b bg 3 1 10 3 d dg 2 1 10 3 fn2-pool))
       (k1-fill (fn2-pool-slot-fill d fn2-pool))
       ((mv k2 fn2-pool) (fn2-pst-copy mode 6 b bg 7 1 10 3 d dg 7 1 10 3 fn2-pool))   ; source fill
       ((mv k3 fn2-pool) (fn2-pst-copy mode 2 b bg 0 1 10 3 d dg 11 1 10 3 fn2-pool))  ; opens a gap
       ((mv k4 fn2-pool) (fn2-pst-copy mode 5 b bg 0 1 10 3 c cg 62 1 10 3 fn2-pool))  ; capacity
       ((mv k5 fn2-pool) (fn2-pst-copy mode 4 b bg 0 1 10 3 b bg 10 1 10 3 fn2-pool))  ; one slot
       ((mv k6 fn2-pool) (fn2-pst-copy mode 4 b bg 0 2 11 4 d dg 0 1 10 3 fn2-pool))   ; source owner
       ((mv k7 fn2-pool) (fn2-pst-copy mode 0 b bg 0 1 10 3 d dg 99 1 10 3 fn2-pool))
       ((mv k8 fn2-pool) (fn2-pst-copy mode 3 b bg 0 1 10 3 d (+ 1 dg) 0 1 10 3 fn2-pool))) ; stale
    (mv (list :zero (list z1 z1-fill z2 z3 z4 z5 (fn2-pool-slot-fill a fn2-pool)
                          (fn2-pst-count 0 a-octets) (fn2-pst-count 171 a-octets)
                          (fn2-pst-at '(0 511 512 12799 12800 12999 13000 16383) a-octets))
              :zero-refused (list zc0 zc1 zc1-fill)
              :copy (list k1 k1-fill k2 k3 k4 k5 k6 k7 k8)
              :octets (list (fn2-pst-octets (fn2-pool-slot-base b fn2-pool) 14 fn2-pool)
                            (fn2-pool-slot-fill b fn2-pool)
                            (fn2-pst-octets (fn2-pool-slot-base d fn2-pool) 12 fn2-pool)
                            (fn2-pool-slot-fill d fn2-pool)
                            (fn2-pst-octets (fn2-pool-slot-base c fn2-pool) 64 fn2-pool)
                            (fn2-pool-slot-fill c fn2-pool)))
        fn2-pool)))
(defun fn2-pst (mode)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool (mv-let (r fn2-pool) (fn2-pst-run mode fn2-pool) r)))

(defconst *fn2-pst-expected*
  (list :zero (list :ok 13000 :ok :ok :owner :stale 16384
                    (- 16384 712) 712 '(171 171 0 0 171 171 0 0))
        :zero-refused '(:bounds :bounds 64)
        :copy '(:ok 7 :bounds :bounds :bounds :ok :owner :ok :stale)
        :octets (list '(100 101 102 103 104 105 106 107 108 109 100 101 102 103) 14
                      '(200 201 103 104 105 106 107 107 108 109 0 0) 10
                      (append (fn2-pst-iota 1 50) (make-list 12 :initial-element 0) '(100 101))
                      64)))

; The span exports reach the stated octets, fills and codes.
(assert-event (equal (fn2-pst :span) *fn2-pst-expected*))
; And so do the bytewise models: every refusal and every written prefix agree.
(assert-event (equal (fn2-pst :model) (fn2-pst :span)))
(value-triple (cw "POOL SPAN: multi-page zero, offset copy, fill advance, refused-prefix parity with the bytewise models PASS~%"))
