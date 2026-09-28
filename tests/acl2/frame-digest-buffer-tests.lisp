; Tests for books/frame-digest-buffer.lisp and books/payload-extent-read.lisp
; (lane arena-offheap-3, PRF-295).
;
; 1. The functions the host calls are guard-verified.
; 2. The attachment executes: the buffer digest of "a" then "bc" in the
;    buffer is BLAKE3("abc") (the Rust blake3 crate's value; the realiser is
;    BLAKE3 since store format 10), equal to the list
;    frame digest; the entry check accepts the digest and refuses a torn
;    (zero) trailer.
; 3. Teeth for the keystones.

(in-package "ACL2")
(include-book "../../books/payload-extent-read")
(include-book "must-fail-checked")

(assert-event
 (and (eq (symbol-class 'fn-blake3-of-prefixed-buffer-any (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-entry-ok-buffer (w state)) :common-lisp-compliant)))

(defconst *fdbt-abc*
  '(#x64 #x37 #xb3 #xac #x38 #x46 #x51 #x33 #xff #xb6 #x3b #x75 #x27 #x3a #x8d #xb5
    #x48 #xc5 #x58 #x46 #x5d #x79 #xdb #x03 #xfd #x35 #x9c #x6c #xd5 #xbd #x9d #x85))

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
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm fdbt-durable-without-trailer
    (fn-arx-entry-ok-buffer (fn-durable-octets file (+ eoff elen) 32)
                            (fn-durable-octets file eoff elen))))))
