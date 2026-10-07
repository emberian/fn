; The decoded payload of a compressed extent as a generated buffer.
;
; `fn-durable-realize-lz' (books/assumptions-durable.lisp) is the host's
; realizer; it answers the decoded octet LIST, and the scalar seam
; `fn-durable-realize-lz-octet' (books/payload-lz-scalar-realizer.lisp) reads
; octet I of it.  An octet at a time off a list is I conses a call; the host
; keeps the list the realizer last answered and reads octets from a buffer
; instead.  The buffer is the generated instance below
; (books/def-representation.lisp, :scalar :octet-seq), its fill a def-loop
; over the append export, so neither the loop nor the buffer is hand-written
; here or in the host.  The correspondence is a theorem, not a host promise:
; filling the buffer from the realized list and reading octet I answers
; exactly the seam's octet.
(in-package "ACL2")
(include-book "payload-lz-scalar-realizer")
(include-book "def-representation")

(def-representation fn-dlz (octet :u8) :scalar (:octet-seq fn-octets))

(defthm fn-durable-realize-lz-octet-is-the-buffer-read
  (implies (and (natp i) (fn-cbor-octet-listp dict))
           (equal (fn-durable-realize-lz-octet
                   file eoff elen poff compressed trailer decoded dict i)
                  (fn-dlz-nth i (fn-dlz-fill-list
                                 (fn-durable-realize-lz file eoff elen poff compressed
                                                        trailer decoded dict)
                                 fn-dlz))))
  :hints (("Goal" :in-theory (enable fn-durable-realize-lz-octet)
                  :use ((:instance fn-dlz-nth-of-fill-list
                                   (xs (fn-durable-realize-lz file eoff elen poff compressed
                                                              trailer decoded dict)))
                        (:instance fn-lzr-lz-value-octets
                                   (c (fn-durable-octets file poff compressed))
                                   (n decoded))))))
