; Ground controls for the physical-stripe support domain, not a RAW theorem.
(in-package "ACL2")
(include-book "../books/blake3-word-frames")

; Constructors and setters are the actual logical functions. The negative
; case deliberately leaves the guarded STORE domain; no raw host mutation.
(local (in-theory (enable fn2-b3-word-stripep fn2-b3-table-init
                         fn2-b3-columns-init fn2-b3-store
                         fn2-b3-set-pos fn2-b3-byte fn2-b3-word
                         fn2-b3-pos fn2-b3-words-length)))

(defthm fn2-b3-word-stripe-store-positive
 (let* ((b (fn2-b3-table-init 2 (create-fn2-b3)))
        (out (fn2-b3-store 1 0 37 b)))
  (and (fn2-b3-word-stripep 1 b) (natp 0) (< 0 16)
       (equal (fn2-b3-words-length out) (fn2-b3-words-length b))
       (equal (fn2-b3-words-length out) 32)
       (equal (fn2-b3-wordsi 16 out) 37)))
 :rule-classes nil)

; Remove exactly the stripe hypothesis of STORE-WORD-FRAME, retaining every
; other conjunct. The actual logical array updater extends an empty buffer.
(defthm fn2-b3-word-stripe-store-hypothesis-removal
 (let* ((b (fn2-b3-table-init 0 (create-fn2-b3)))
        (out (fn2-b3-store 0 0 37 b)))
  (and (natp 0) (< 0 16)
       (not (fn2-b3-word-stripep 0 b))
       (not (equal (fn2-b3-words-length out) (fn2-b3-words-length b)))
       (equal (fn2-b3-words-length b) 0)
       (equal (fn2-b3-words-length out) 1)
       (equal (fn2-b3-wordsi 0 out) 37)))
 :rule-classes nil)

; BYTE must not require input element typing merely to preserve dimensions.
; POS=-1 is outside its u8 column type. MOD normalizes it to63, so byte1
; really writes the high octet of word31 in row1's existing stripe.
(defthm fn2-b3-word-stripe-byte-malformed-pos-positive
 (let* ((b (fn2-b3-set-pos 1 -1 (fn2-b3-table-init 2 (create-fn2-b3))))
        (out (mv-nth 1 (fn2-b3-byte 1 1 (create-fn2-digests) b))))
  (and (fn2-b3-word-stripep 1 b)
       (equal (fn2-b3-pos 1 b) -1)
       (not (unsigned-byte-p 8 (fn2-b3-pos 1 b)))
       (equal (fn2-b3-words-length out) (fn2-b3-words-length b))
       (equal (fn2-b3-words-length out) 32)
       (equal (fn2-b3-wordsi 31 out) 16777216)
       (equal (fn2-b3-pos 1 out) 64)))
 :rule-classes nil)
