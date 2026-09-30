; Teeth for books/subject-id-buffer.lisp: the served POST's subject identity
; over the octet buffer.
;
; 1. The host's entry is guard-verified with guard T.
; 2. It executes (the attachment): for the payload "hello, world" in the
;    buffer, the identity is the subject label, the separator, version 1,
;    algorithm 2 (BLAKE3) and BLAKE3 of the subject preimage, whose value
;    here is the Rust blake3 crate's, not this tree's; and it equals the list
;    identity `fn-id-subject-of-payload'.
; 3. KEYSTONE fn-sidb-subject-id-is-id-subject-of-payload has no hypothesis:
;    a ground witness.  fn-sidb-subject-id-bounded-unfolds: the bound's two
;    arms, the in-bound arm here, the out-of-bound arm by its conclusion's
;    NIL at a length past the CBOR uint range (stated, not built: 4 GiB).

(in-package "ACL2")
(include-book "../../books/subject-id-buffer")

(defun sidbt-octets (s) (fn-record-string-octets s))

(assert-event
 (eq (symbol-class 'fn-sidb-subject-id-bounded (w state)) :common-lisp-compliant))

(defconst *sidbt-digest*
  '(#xd3 #x18 #x97 #x47 #xe8 #x4b #x25 #xba #x14 #xbe #x28 #xbd #xda #x51 #xaa #xfb
    #x4e #x9c #xd7 #x17 #xd0 #x4d #x0e #x7c #x75 #x16 #x49 #x04 #x15 #xbe #xd4 #xfa))

(assert-event
 (let* ((fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list (sidbt-octets "hello, world") fn-octets)))
   (mv (and (equal (fn-sidb-subject-id-bounded fn-octets)
                   (append (sidbt-octets "fn/subject/v1") (list 0 1 2) *sidbt-digest*))
            (equal (fn-sidb-subject-id-bounded fn-octets)
                   (fn-id-subject-of-payload (sidbt-octets "hello, world"))))
       fn-octets))
 :stobjs-out '(nil fn-octets))

(defthm sidbt-keystone-witness
  (equal (fn-sidb-subject-id '(104 105))
         (fn-id-subject-of-payload '(104 105)))
  :rule-classes nil)

; PRF-106 positive: fn-blake3-of-prefixed-buffer-is-blake3 has no
; hypotheses. Execute its literal conclusion with both a nonempty prefix
; and payload buffer, independently of the fixed external digest above.
(assert-event
 (let* ((prefix '(102 110 0 1))
        (payload '(104 105 0 255))
        (fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list payload fn-octets)))
   (mv (equal (fn-blake3-of-prefixed-buffer prefix fn-octets)
              (fn-blake3 (append prefix payload)))
       fn-octets))
 :stobjs-out '(nil fn-octets))

(defthm sidbt-bounded-in-bound-witness
  (equal (fn-sidb-subject-id-bounded '(104 105))
         (fn-id-subject-of-payload '(104 105)))
  :rule-classes nil)
