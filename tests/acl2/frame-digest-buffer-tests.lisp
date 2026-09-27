; Tests for books/frame-digest-buffer.lisp and books/payload-extent-read.lisp
; (lane arena-offheap-3, PRF-295).
;
; 1. The functions the host calls are guard-verified.
; 2. The attachment executes: the buffer digest of "a" then "bc" in the
;    buffer is SHA-256("abc") (FIPS 180-2 appendix B.1), equal to the list
;    frame digest; the entry check accepts the digest and refuses a torn
;    (zero) trailer.
; 3. Teeth for the keystones.

(in-package "ACL2")
(include-book "../../books/payload-extent-read")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (and (eq (symbol-class 'fn-sha256-of-prefixed-buffer-any (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-entry-ok-buffer (w state)) :common-lisp-compliant)))

(defconst *fdbt-abc*
  '(#xba #x78 #x16 #xbf #x8f #x01 #xcf #xea #x41 #x41 #x40 #xde #x5d #xae #x22 #x23
    #xb0 #x03 #x61 #xa3 #x96 #x17 #x7a #x9c #xb4 #x10 #xff #x61 #xf2 #x00 #x15 #xad))

(assert-event
 (let* ((fn-octets-rd (fn-octets-rd-clear fn-octets-rd))
        (fn-octets-rd (fn-octets-rd-append-list '(98 99) fn-octets-rd)))
   (mv (and (equal (fn-frame-digest-buffer '(97) fn-octets-rd) *fdbt-abc*)
            (equal (fn-frame-digest-buffer '(97) fn-octets-rd) (fn-frame-digest '(97 98 99))))
       fn-octets-rd))
 :stobjs-out '(nil fn-octets-rd))

(assert-event
 (let* ((fn-octets-rd (fn-octets-rd-clear fn-octets-rd))
        (fn-octets-rd (fn-octets-rd-append-list '(97 98 99) fn-octets-rd)))
   (mv (and (fn-arx-entry-ok-buffer *fdbt-abc* fn-octets-rd)
            (not (fn-arx-entry-ok-buffer (make-list 32 :initial-element 0) fn-octets-rd))
            (not (fn-arx-entry-ok-buffer (cdr *fdbt-abc*) fn-octets-rd)))
       fn-octets-rd))
 :stobjs-out '(nil fn-octets-rd))

; --- Teeth.
; fn-frame-digest-buffer-is-the-frame-digest: no hypothesis; a ground
; instance (the logical buffer value (98 99)).
(defthm fdbt-digest-witness
  (equal (fn-frame-digest-buffer '(97) '(98 99)) (fn-frame-digest '(97 98 99)))
  :rule-classes nil)

; fn-arx-entry-ok-buffer-is-the-frame-check at the same buffer.
(defthm fdbt-check-witness
  (equal (fn-arx-entry-ok-buffer (fn-frame-digest '(97 98 99)) '(97 98 99)) t)
  :rule-classes nil)

; fn-arx-entry-ok-buffer-of-durable: every hypothesis and the conclusion at a
; ground extent; without the file's trailer being the prefix's digest the read
; is not provably accepted.
(defthm fdbt-durable-witness
  (implies (equal (fn-durable-octets 3 110 32) (fn-frame-digest (fn-durable-octets 3 100 10)))
           (fn-arx-entry-ok-buffer (fn-durable-octets 3 110 32) (fn-durable-octets 3 100 10)))
  :rule-classes nil)

(local
 (must-fail
  (with-prover-step-limit 50000 (defthm fdbt-durable-without-trailer
    (fn-arx-entry-ok-buffer (fn-durable-octets file (+ eoff elen) 32)
                            (fn-durable-octets file eoff elen))))))
