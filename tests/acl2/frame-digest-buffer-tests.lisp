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

; -----------------------------------------------------------------------------
; The read decided against the descriptor's COMMITMENT (lane extent-identity,
; PRF-994; GPT-6's warranty-quality-proof-engineering.md section 2): the
; substitution family, every substituted object well formed.  E0 = (97 98 99)
; with its trailer T0 (*fdbt-abc*); E1 = (97 98 100), the same size, with its
; own trailer T1 = digest(E1).

(assert-event
 (eq (symbol-class 'fn-arx-entry-verdict-buffer (w state)) :common-lisp-compliant))

(assert-event
 (and (eq (symbol-class 'fn-arx-trailer-nat-at-buffer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-attach-trailers-buffer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arx-attach-trailers (w state)) :common-lisp-compliant)))

; THE DEFECT, executed: the self-consistent substituted entry (E1, T1) passes
; the old check, which never saw the descriptor's trailer; the verdict against
; the commitment of T0 refuses it by name (:trailer).  The same verdict names
; an entry read at a wrong offset or from another store or generation: its
; recorded trailer is not the descriptor's.
(assert-event
 (let* ((t1 (fn-frame-digest '(97 98 100)))
        (fn-octets-rd (fn-octets-rd-clear fn-octets-rd))
        (fn-octets-rd (fn-octets-rd-append-list '(97 98 100) fn-octets-rd)))
   (mv (and (not (equal t1 *fdbt-abc*))
            (equal (fn-arx-entry-ok-buffer t1 fn-octets-rd) t)
            (eq (fn-arx-entry-verdict-buffer (fn-arx-trailer-nat *fdbt-abc*) t1 fn-octets-rd)
                :trailer)
            ; the substituted entry against its OWN commitment is accepted:
            ; the verdict is about identity, not well-formedness
            (eq (fn-arx-entry-verdict-buffer (fn-arx-trailer-nat t1) t1 fn-octets-rd) :ok))
       fn-octets-rd))
 :stobjs-out '(nil fn-octets-rd))

; The intact entry: :ok against its commitment; a WRONG EXPECTED TRAILER
; (the descriptor's, T1) is :trailer; a trailer recorded after the prefix
; that is not the descriptor's (T1 written over T0) is :trailer; a malformed
; read (31 octets, a non-octet) is :trailer; the prefix damaged in place
; under its own trailer is :digest.
(assert-event
 (let* ((t1 (fn-frame-digest '(97 98 100)))
        (c0 (fn-arx-trailer-nat *fdbt-abc*))
        (fn-octets-rd (fn-octets-rd-clear fn-octets-rd))
        (fn-octets-rd (fn-octets-rd-append-list '(97 98 99) fn-octets-rd)))
   (mv (and (eq (fn-arx-entry-verdict-buffer c0 *fdbt-abc* fn-octets-rd) :ok)
            (eq (fn-arx-entry-verdict-buffer (fn-arx-trailer-nat t1) *fdbt-abc* fn-octets-rd)
                :trailer)
            (eq (fn-arx-entry-verdict-buffer c0 t1 fn-octets-rd) :trailer)
            (eq (fn-arx-entry-verdict-buffer c0 (cdr *fdbt-abc*) fn-octets-rd) :trailer)
            (eq (fn-arx-entry-verdict-buffer c0 (cons 256 (cdr *fdbt-abc*)) fn-octets-rd)
                :trailer)
            (eq (fn-arx-entry-verdict-buffer 0 *fdbt-abc* fn-octets-rd) :trailer))
       fn-octets-rd))
 :stobjs-out '(nil fn-octets-rd))

(assert-event
 (let* ((fn-octets-rd (fn-octets-rd-clear fn-octets-rd))
        (fn-octets-rd (fn-octets-rd-append-list '(97 98 98) fn-octets-rd)))
   (mv (eq (fn-arx-entry-verdict-buffer (fn-arx-trailer-nat *fdbt-abc*) *fdbt-abc* fn-octets-rd)
           :digest)
       fn-octets-rd))
 :stobjs-out '(nil fn-octets-rd))

; The commitment attached to a place, from the buffer and from the list: an
; entry of 40 octets at file offset 100 whose last 32 are T0; the place
; (100 40 110 4) gains T0's commitment; a place of another entry shape keeps
; its four fields.
(assert-event
 (let* ((entry (append (make-list 8 :initial-element 5) *fdbt-abc*))
        (fn-octets-rd (fn-octets-rd-clear fn-octets-rd))
        (fn-octets-rd (fn-octets-rd-append-list entry fn-octets-rd)))
   (mv (and (equal (fn-arx-attach-trailers '((100 40 110 4)) 100 entry)
                   (list (list 100 40 110 4 (fn-arx-trailer-nat *fdbt-abc*))))
            (equal (fn-arx-attach-trailers-buffer '((100 40 110 4) (100 40 114 2)) 100 fn-octets-rd)
                   (fn-arx-attach-trailers '((100 40 110 4) (100 40 114 2)) 100 entry))
            (equal (fn-arx-trailer-nat-at-buffer 8 fn-octets-rd) (fn-arx-trailer-nat *fdbt-abc*))
            (not (equal (fn-arx-trailer-nat *fdbt-abc*) (fn-arx-trailer-nat (cdr *fdbt-abc*)))))
       fn-octets-rd))
 :stobjs-out '(nil fn-octets-rd))

; --- Teeth for the keystones.

; fn-arx-entry-verdict-buffer-ok-is-the-commitment: no hypothesis; a ground
; instance both ways (the logical buffer value (97 98 99)).
(defthm fdbt-verdict-witness
  (and (equal (fn-arx-entry-verdict-buffer (fn-arx-trailer-nat (fn-frame-digest '(97 98 99)))
                                           (fn-frame-digest '(97 98 99)) '(97 98 99))
              :ok)
       (not (equal (fn-arx-entry-verdict-buffer 0 (fn-frame-digest '(97 98 99)) '(97 98 99))
                   :ok)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-arx-trailer-nat)
           :use ((:instance fn-arx-trailer-nat-natp (octets (fn-frame-digest '(97 98 99))))))))

; fn-arx-entry-verdict-buffer-ok-digest-is-the-recorded-trailer at a ground
; extent: the complete antecedent and the conclusion.
(defthm fdbt-commitment-witness
  (implies (equal (fn-arx-entry-verdict-buffer (fn-arx-trailer-nat (fn-durable-octets 3 110 32))
                                               read (fn-durable-octets 3 100 10))
                  :ok)
           (equal (fn-frame-digest (fn-durable-octets 3 100 10)) (fn-durable-octets 3 110 32)))
  :rule-classes nil)

; Hypothesis removal: the OLD check in the verdict's place does not give the
; conclusion (the executed counterexample above: (E1, T1) passes it with a
; digest that is not T0).
(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm fdbt-old-check-is-not-the-commitment
    (implies (fn-arx-entry-ok-buffer read (fn-durable-octets 3 100 10))
             (equal (fn-frame-digest (fn-durable-octets 3 100 10)) (fn-durable-octets 3 110 32)))))))

; fn-arx-entry-verdict-buffer-of-durable: every hypothesis and the conclusion
; at a ground extent; without the file's trailer being the prefix's digest the
; faithful read is not provably :ok.
(defthm fdbt-verdict-durable-witness
  (implies (equal (fn-durable-octets 3 110 32) (fn-frame-digest (fn-durable-octets 3 100 10)))
           (equal (fn-arx-entry-verdict-buffer (fn-arx-trailer-nat (fn-durable-octets 3 110 32))
                                               (fn-durable-octets 3 110 32)
                                               (fn-durable-octets 3 100 10))
                  :ok))
  :rule-classes nil)

(local
 (must-fail-checked
  (with-prover-step-limit 50000 (defthm fdbt-verdict-durable-without-trailer
    (equal (fn-arx-entry-verdict-buffer (fn-arx-trailer-nat (fn-durable-octets file (+ eoff elen) 32))
                                        (fn-durable-octets file (+ eoff elen) 32)
                                        (fn-durable-octets file eoff elen))
           :ok)))))

; fn-arx-trailer-nat-injective at ground octet lists, and its failure without
; the octet hypothesis (a non-octet element packs as 0).
(defthm fdbt-injective-witness
  (implies (equal (fn-arx-trailer-nat '(1 2 3)) (fn-arx-trailer-nat b))
           (implies (fn-cbor-octet-listp b) (equal b '(1 2 3))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arx-trailer-nat-injective (a '(1 2 3)))))))

(assert-event
 (and (equal (fn-arx-trailer-nat '(1 2 3)) (fn-arx-trailer-nat '(1 2 3)))
      (equal (fn-arx-trailer-nat '(0 2 3)) (fn-arx-trailer-nat '(256 2 3)))
      (not (fn-cbor-octet-listp '(256 2 3)))))
