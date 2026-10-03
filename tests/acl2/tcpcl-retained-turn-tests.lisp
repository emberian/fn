(in-package "ACL2")
(include-book "../../books/tcpcl-retained-turn")
; Literal complete positive and each retained hypothesis removal witness.
(assert-event
 (let ((offset 2) (total 5000))
  (and (natp offset) (integerp total) (<= offset total)
   (<= offset (fn-tcrt-write-end offset total))
   (<= (fn-tcrt-write-end offset total) total)
   (<= (- (fn-tcrt-write-end offset total) offset) (fn-tcrt-read-limit)))))
(assert-event
 (let ((offset -1) (total 5000))
  (and (not (natp offset)) (integerp total) (<= offset total)
   (not (<= (- (fn-tcrt-write-end offset total) offset) (fn-tcrt-read-limit))))))
(assert-event
 (let ((offset 1) (total 3/2))
  (and (natp offset) (not (integerp total)) (<= offset total)
   (not (<= offset (fn-tcrt-write-end offset total))))))
(assert-event
 (let ((offset 4) (total 2))
  (and (natp offset) (integerp total) (not (<= offset total))
   (not (<= offset (fn-tcrt-write-end offset total))))))
(assert-event
 (and t (not nil) (not nil) (not nil) (not (equal :established :closed))
  (equal (fn-tcrt-action t t nil nil t t nil :established 0 nil) :source)))
(assert-event
 (and (not nil) (not nil) (not nil) (not (equal :established :closed))
      (not nil)
  (not (equal (fn-tcrt-action nil t nil nil t t nil :established 0 nil) :source))))
(assert-event
 (and t (not nil) (not nil) (not (equal :established :closed)) t
  (not (equal (fn-tcrt-action t t t nil t t nil :established 0 nil) :source))))
(assert-event
 (and t (not nil) (not nil) (not (equal :established :closed)) t
  (not (equal (fn-tcrt-action t t nil t t t nil :established 0 nil) :source))))
(assert-event
 (and t (not nil) (not nil) (not (equal :established :closed)) t
  (not (equal (fn-tcrt-action t t nil nil t t t :established 0 nil) :source))))
(assert-event
 (and t (not nil) (not nil) (not nil) (equal :closed :closed)
  (not (equal (fn-tcrt-action t t nil nil t t nil :closed 0 nil) :source))))
(assert-event
 (and t (not (and (natp 1) (<= 1 (nfix 0))))
  (equal (fn-tcrt-action t t t t t t t :closed 0 1) :write)))
(assert-event
 (and (not nil) (not (and (natp 1) (<= 1 (nfix 0))))
  (not (equal (fn-tcrt-action t t nil t t t t :closed 0 1) :write))))
(assert-event
 (and t (and (natp 0) (<= 0 (nfix 0)))
  (not (equal (fn-tcrt-action t t t t t t t :closed 0 0) :write))))
