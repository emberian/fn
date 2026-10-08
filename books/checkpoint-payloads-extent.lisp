; fn: the payload file's read bridge to the extent realizer (lane s-cpl,
; 2026-10-07; CPL-OPEN-IS-EXTENT-REALIZE).
;
; The extent realizer (host/native/extent.lisp fnn-extent-entry) reads an
; entry's protected prefix [EOFF, EOFF+ELEN) into a buffer and the 32 octets
; after it, and decides fn-arx-entry-verdict-buffer (books/payload-extent-read.lisp):
; :ok exactly when the frame digest of the prefix is the trailer read and the
; trailer is the descriptor's commitment.  A payload frame
; (books/checkpoint-payloads.lisp) is that entry: the prefix is header ++
; payload (EOFF = ref offset - 37, ELEN = 37 + len, POFF = 37, PLEN = len),
; and its trailer is the frame digest of the prefix, because the frame's chain
; is empty.  The keystone: the realizer's verdict on a frame in the file, for
; the commitment of the trailer the append plan returns, is :ok.

(in-package "ACL2")
(include-book "checkpoint-payloads")
(include-book "payload-extent-read")

; KEYSTONE (CPL-OPEN-IS-EXTENT-REALIZE).  For a frame appended after PRE, the
; realizer's reads (the prefix at the ref's frame start, the 32 octets after
; it) pass the realizer's own verdict against the commitment of the trailer
; the plan returns: the verdict is :ok.
(defthm fn-cpl-ref-passes-the-extent-realizer
  (implies (and (true-listp pre) (true-listp post) (fn-cpl-payloadp p)
                (equal fn-octets (take (+ 37 (len p))
                                       (nthcdr (len pre) (append pre (fn-cpl-frame p) post)))))
           (equal (fn-arx-entry-verdict-buffer
                   (fn-arx-trailer-nat (fn-cpl-trailer p))
                   (take 32 (nthcdr (+ (len pre) 37 (len p))
                                    (append pre (fn-cpl-frame p) post)))
                   fn-octets)
                  :ok))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-arx-entry-verdict-buffer-ok-is-the-commitment
                            (expected (fn-arx-trailer-nat (fn-cpl-trailer p)))
                            (read (fn-cpl-trailer p)))
                 fn-cpl-trailer-shape fn-cpl-trailer-is-the-frame-digest fn-cpl-prefix-in-file
                 fn-cpl-trailer-in-file)
           :in-theory (disable fn-arx-entry-verdict-buffer-ok-is-the-commitment
                               fn-cpl-trailer-shape fn-cpl-trailer-is-the-frame-digest
                               fn-cpl-prefix-in-file fn-cpl-trailer-in-file
                               fn-arx-entry-verdict-buffer))))
