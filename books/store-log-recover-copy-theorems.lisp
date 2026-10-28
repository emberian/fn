;; fn: the open keeps every segment name in every image (RL-01), split out of books/store-log-recover-copy.lisp.
;; The keystone below certifies in about 2,830 s, alone; the image needs the definitions book, not this
;; proof, so nothing in the image closure includes this book (OWED.md PRF-273 cost row).
(in-package "ACL2")
(include-book "store-log-recover-copy")

(local
 (defthm fn-lgrc-all-invp-member
   (implies (and (fn-lgrc-all-invp states j k a) (member-equal x states))
            (fn-lgrc-invp x j k a))
   :hints (("Goal" :in-theory (disable fn-lgrc-invp)))))

; KEYSTONE (discoverable).  At every state of the open, in every image a
; power loss can leave, journal/N durably names an inode, and the open's own
; listing still sees N.
(defthm fn-lgrc-open-keeps-every-segment-name-in-every-image
  (implies (and (fn-lgrc-invp s j n nil)
                (fn-bs-dir-idp stg) (fn-bs-namep stage)
                (not (and (equal stg j) (equal stage k)))
                (not (and (equal stg j) (equal stage n)))
                (fn-lgrc-outcomesp outs)
                (member-equal x (fn-bsc-run s (fn-lgrc-open-ops s j k stg stage root parent
                                                                genesis max floor outs))))
           (and (fn-bs-inop (fn-bs-durable-entry (fn-bs-crash (fn-bsc-bs x) choices) j n))
                (fn-bs-inop (fn-bsc-lookup x j n))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgrc-goodp) (fn-lgrc-open-ops fn-bsc-run fn-bs-crash
                                            fn-bs-durable-entry fn-lgrc-all-invp
                                            fn-lgrc-every-image-binds-the-acknowledged-prefix))
           :use ((:instance fn-lgrc-open-unlinks-no-segment)
                 (:instance fn-lgrc-all-invp-member (k n) (a nil)
                            (states (fn-bsc-run s (fn-lgrc-open-ops s j k stg stage root parent
                                                                    genesis max floor outs))))
                 (:instance fn-lgrc-every-image-binds-the-acknowledged-prefix
                            (s x) (k n) (a nil))))))
