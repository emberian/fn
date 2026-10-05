(in-package "ACL2")
(include-book "../../books/tcpcl-retained-turn")
(include-book "../../books/defkeystone")
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

; The literal contact deadline fires only while the peer header is incomplete.
(assert-event
 (and (equal (fn-tcrt-contact-deadline 100) 60100)
      (fn-tcrt-contact-timeout-p :contact 60100 60100 nil)
      (not (fn-tcrt-contact-timeout-p :contact 60099 60100 nil))
      (not (fn-tcrt-contact-timeout-p :contact -1 0 nil))
      (not (fn-tcrt-contact-timeout-p :contact 100 nil nil))
      (not (fn-tcrt-contact-timeout-p :messaging 60100 60100 nil))
      (not (fn-tcrt-contact-timeout-p :established 60100 60100 nil))
      (not (fn-tcrt-contact-timeout-p :ending 60100 60100 nil))))

; Already observed input finishes bounded framing before reception expiration.
(assert-event (not (fn-tcrt-contact-timeout-p :contact 60100 60100 t)))

(assert-event (equal (fn-tcrt-init-deadline :messaging 100 nil) 60100))
(assert-event (equal (fn-tcrt-init-deadline :messaging 60099 60100) 60100))
(assert-event (equal (fn-tcrt-init-deadline :established 70000 60100) nil))
(assert-event (fn-tcrt-init-timeout-p :messaging 60100 60100 nil))
(assert-event (not (fn-tcrt-init-timeout-p :messaging 60099 60100 nil)))
(assert-event (not (fn-tcrt-init-timeout-p :messaging 60100 60100 t)))
(assert-event (not (fn-tcrt-init-timeout-p :established 60100 60100 nil)))
; Positive literal and hypothesis removal for nonrenewal.
(assert-event (and (equal :messaging :messaging) (natp 100)
                  (equal (fn-tcrt-init-deadline :messaging 0 100) 100)))
(assert-event (and (not (equal :contact :messaging)) (natp 100)
                  (not (equal (fn-tcrt-init-deadline :contact 0 100) 100))))
(assert-event (and (equal :messaging :messaging) (not (natp nil))
                  (not (equal (fn-tcrt-init-deadline :messaging 0 nil) nil))))

; TEETH-21 BEGIN
(defteeth fn-tcrt-write-range-is-bounded
  :claim (((offset-natural (natp offset)) (total-integer (integerp total)) (within-total (<= offset total)))
          (and (<= offset (fn-tcrt-write-end offset total))
               (<= (fn-tcrt-write-end offset total) total)
               (<= (- (fn-tcrt-write-end offset total) offset) (fn-tcrt-read-limit))))
  :subject fn-tcrt-write-end
  :witness ((offset 2) (total 5000))
  :breaks ((offset-natural ((offset -1))
                           :logical "a negative offset is outside the guard of fn-tcrt-write-end")
           (total-integer ((offset 1) (total 3/2))
                          :logical "a fractional total is outside the guard of fn-tcrt-write-end")
           (within-total ((offset 4) (total 2))))
  :mutations ((range-past-the-total
               (:conclusion (<= (fn-tcrt-write-end offset total) (- total 1)))
               ((offset 2) (total 5))
               :fault "a write range that may not use the last octet of the total")))
; TEETH-21 END
