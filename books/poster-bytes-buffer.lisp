; fn: the poster-bytes existing-article test over the octet buffer (D27
; boundary 6, wave B; prefix `fn-pbb-').
;
; D25's verdict (books/poster-bytes.lisp `fn-pb-action-over'; the host's
; entry books/store-intern.lisp `fn-store-existing-action') is what the owner
; host asks before a prepare: is this Message-ID already held, and if so is the
; submission the same article (then :duplicate) or a different one (then
; :conflict).  "The same article" reads the injection source out of both
; payloads (`fn-inj-source-of', books/injection.lisp: strip the Path line,
; the Injection-Date line and the Injection-Info line, each a `fn-inj-strip'
; of a prefix off a suffix of the octets) and compares the sources, or the
; whole payloads when either has no readable source.
;
; Here the submitted payload is the octet buffer `fn-octets' instead of a
; list.  Every strip is an index walk (`fn-pbb-strip-at'), the source is a
; description of buffer positions, and the compare against the held
; record's payload (an octet list in the logical store, until wave C) reads
; the buffer in place: nothing of the submitted payload is consed.  A
; recipe v2 record's source is a suffix of the buffer; a recipe v3 record
; (D32, a supplied Path, `fn-inj-unsplice') gives its source back with the
; AGENT! insertion cut out of the Path content, so a source is (K A B):
; st[K..A) followed by st[B..), with K = A = B for a suffix, and the
; compare is `fn-pbb-range-match' over the first piece and
; `fn-oct-suffix-equalp' over the second.  The one keystone,
; `fn-pbb-same-articlep-is-pb-same-articlep', says the buffer comparison
; equals the list comparison on the buffer's logical value; the host's
; buffer verdict (books/post-identity-index.lisp `fn-pidx-existing-action',
; called by host/owner-host.lisp `fn-owner-existing-action-buffer' and
; `fn-owner-prepare-buffer') uses it through its tombstone-aware form
; (books/store-reclaim-buffer.lisp `fn-rclb-same-articlep').

(in-package "ACL2")
(include-book "poster-bytes")
(include-book "poster-bytes-source-buffer")

(defthm fn-pbb-buffer-is-octet-listp
  (implies (fn-octets-p fn-octets)
           (fn-octet-listp fn-octets))
  :hints (("Goal" :induct (fn-cbor-octet-listp fn-octets)
           :in-theory (enable fn-octets-p fn-cbor-octet-listp fn-cbor-octetp
                              fn-octet-listp fn-octetp))))
