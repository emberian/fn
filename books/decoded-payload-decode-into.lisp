; The decode's target is the generated buffer, not a list.
;
; The host decodes a stored payload with `fn-zpl-decode-bufs' into a pooled
; output buffer (books/deflate-pool.lisp; KEYSTONE
; fn-zpl-decode-bufs-is-the-lz-value: an :ok answer leaves in that buffer
; exactly `fn-lzr-lz-value', the value A-DURABLE-LZ names), and then makes
; `fn-dlz' (books/decoded-payload-buffer.lisp) hold those octets with
; `fn-dlz-fill-from', a generated index loop from one octet buffer to the
; other.  No octet list of the decoded payload exists in that path.  The
; keystone: after an :ok decode, filling `fn-dlz' from the output buffer
; gives the spec value, so reading octet I of `fn-dlz' is `nth' of it
; (fn-dlz-nth-is-nth).
(in-package "ACL2")
(include-book "decoded-payload-buffer")
(include-book "deflate-pool")

(defthm fn-dlz-decode-into-is-the-lz-value
  (implies (and (fn-cbor-octet-listp c) (fn-cbor-octet-listp dict) (natp n)
                (fn-zpl-pool-okp pool fn-zin-win)
                (equal (car (car (fn-zpl-decode-bufs pool dict (len c) n c fn-zin-win
                                                     fn-zin-tab fn-zin-out)))
                       :ok))
           (equal (fn-dlz-fill-from
                   (mv-nth 4 (fn-zpl-decode-bufs pool dict (len c) n c fn-zin-win
                                                 fn-zin-tab fn-zin-out))
                   fn-dlz)
                  (fn-lzr-lz-value dict c n)))
  :hints (("Goal" :use ((:instance fn-zpl-decode-bufs-is-the-lz-value)
                        (:instance fn-lzr-lz-value-octets)
                        (:instance fn-dlz-fill-from-is-the-buffer
                                   (fn-octets (mv-nth 4 (fn-zpl-decode-bufs
                                                         pool dict (len c) n c fn-zin-win
                                                         fn-zin-tab fn-zin-out)))))
           :do-not-induct t
           :in-theory (union-theories '(fn-cbor-octet-listp-implies-true-listp) (theory 'minimal-theory)))))
