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

; S025: the no-progress bounds of an established session.  Reasons: 5 under
; contention (passive-ms), 1 for a stalled transfer (stall-ms).
(assert-event (fn-tcrt-progress-frame-p 1))
(assert-event (fn-tcrt-progress-frame-p 2))
; Teeth: nothing else is transfer advancement.
(assert-event (not (fn-tcrt-progress-frame-p 3)))
(assert-event (not (fn-tcrt-progress-frame-p 4)))
(assert-event (not (fn-tcrt-progress-frame-p 5)))
(assert-event (not (fn-tcrt-progress-frame-p 6)))
(assert-event (not (fn-tcrt-progress-frame-p 7)))
(assert-event (not (fn-tcrt-progress-frame-p nil)))
; The clock is captured once on entering :established and not renewed by capture.
(assert-event (equal (fn-tcrt-progress-clock :established 500 nil) 500))
(assert-event (equal (fn-tcrt-progress-clock :established 900 500) 500))
(assert-event (not (fn-tcrt-progress-clock :messaging 500 nil)))
(assert-event (not (fn-tcrt-progress-clock :ending 500 500)))
; A whole transfer frame renews; a KEEPALIVE or SESS_TERM does not.
(assert-event (equal (fn-tcrt-note-frame 1 900 500) 900))
(assert-event (equal (fn-tcrt-note-frame 2 900 500) 900))
(assert-event (equal (fn-tcrt-note-frame 4 900 500) 500))
(assert-event (equal (fn-tcrt-note-frame 5 900 500) 500))
(assert-event (equal (fn-tcrt-note-frame 1 900 nil) nil))
(assert-event (equal (fn-tcrt-note-frame 1 400 500) 500))
; passive-ms: only under contention, only established, exactly at the deadline.
(assert-event (fn-tcrt-passive-timeout-p :established 5000 1000 4000 t))
(assert-event (not (fn-tcrt-passive-timeout-p :established 4999 1000 4000 t)))
(assert-event (not (fn-tcrt-passive-timeout-p :established 5000 1000 4000 nil)))
(assert-event (not (fn-tcrt-passive-timeout-p :messaging 5000 1000 4000 t)))
(assert-event (not (fn-tcrt-passive-timeout-p :ending 5000 1000 4000 t)))
(assert-event (not (fn-tcrt-passive-timeout-p :established 5000 nil 4000 t)))
(assert-event (not (fn-tcrt-passive-timeout-p :established 5000 1000 0 t)))
; stall-ms: any contention, a transfer in flight, established.
(assert-event (fn-tcrt-stall-timeout-p :established 5000 1000 4000 t))
(assert-event (not (fn-tcrt-stall-timeout-p :established 4999 1000 4000 t)))
(assert-event (not (fn-tcrt-stall-timeout-p :established 5000 1000 4000 nil)))
(assert-event (not (fn-tcrt-stall-timeout-p :messaging 5000 1000 4000 t)))
(assert-event (not (fn-tcrt-stall-timeout-p :established 5000 1000 0 t)))
; The reasons: contention wins and is Resource Exhaustion; a stall alone is Idle timeout.
(assert-event (equal (fn-tcrt-expiry-reason :established 5000 1000 4000 9000 nil t) 5))
(assert-event (equal (fn-tcrt-expiry-reason :established 5000 1000 4000 9000 t t) 5))
(assert-event (equal (fn-tcrt-expiry-reason :established 5000 1000 9000 4000 t nil) 1))
(assert-event (equal (fn-tcrt-expiry-reason :established 5000 1000 9000 4000 t t) 1))
(assert-event (not (fn-tcrt-expiry-reason :established 5000 1000 4000 4000 nil nil)))
(assert-event (equal (fn-tcrt-expiry-reason :established 5000 1000 4000 4000 nil t) 5))
(assert-event (not (fn-tcrt-expiry-reason :established 4999 1000 4000 4000 t t)))
; The host acts only at the :local action: every busy action refuses the bound.
(assert-event (equal (fn-tcrt-expiry :local :established 5000 1000 4000 9000 nil t) 5))
(assert-event (not (fn-tcrt-expiry :write :established 5000 1000 4000 9000 nil t)))
(assert-event (not (fn-tcrt-expiry :encode :established 5000 1000 4000 9000 nil t)))
(assert-event (not (fn-tcrt-expiry :source :established 5000 1000 4000 9000 nil t)))
(assert-event (not (fn-tcrt-expiry :read :established 5000 1000 4000 9000 nil t)))
(assert-event (not (fn-tcrt-expiry :done :established 5000 1000 4000 9000 nil t)))
; ... and fn-tcrt-action reaches :local only with nothing half written or held.
(assert-event (equal (fn-tcrt-action nil nil nil nil nil nil nil :established 5000 nil) :local))
(assert-event (not (equal (fn-tcrt-action nil nil t nil nil nil nil :established 5000 9000) :local)))
(assert-event (not (equal (fn-tcrt-action nil nil nil t nil nil nil :established 5000 nil) :local)))
(assert-event (not (equal (fn-tcrt-action t nil nil nil nil nil nil :established 5000 nil) :local)))
