; fn: the frame integrity trailer, computed once, by ACL2.
;
; `books/frame-octets.lisp' constrains `fn-frame-digest' to be 32 octets and
; `books/crypto-attach.lisp' attaches `fn-sha256' to it, so a ground call of
; the trailer function EVALUATES.  Before this book nothing used that: the
; trailer was computed by three separate hosts, each with its own SHA-256 --
;
;   * `tools/frame_bridge.py' `FrameSession.seal' and `.digest_of'
;     (`hashlib.sha256' over the protected prefix);
;   * `host/native/io.lisp' `fnn-seal' and `fnn-digest-of' (`fnn-sha256',
;     about fifty lines of hand-written Common Lisp);
;   * `tools/run_owner.py' `feed_frames' and `feed_replay_frame', the FNFD
;     feed trailer, which arrived with `w10/owner-feed' after the digest
;     lane's handoff recorded the first two.
;
; Three owners of one decision is exactly what AGENTS.md's one-owner rule
; forbids, and the three could disagree without any test noticing: each host
; checked its own trailer against its own.  `fn-frame-trailer' is the one
; owner, and the three hosts call it.
;
; WHY A BOOK OF ITS OWN and not a `fn-store-' wrapper in `host/store-host.lisp'
; with the rest of the frame bridge: the owner's ACL2 session loads
; `host/owner-host.lisp' and never loads `host/store-host.lisp', so a host
; wrapper would have had to be written twice -- the twin again, one layer
; out.  A book is included by both, and it lets the function be guard
; verified and its keystones proved.  The registered prefix for the frame
; grammar is `fn-frame-' (docs/prefixes.md), which is what the function
; carries.
;
; WHAT IS PROVED HERE: that a host which asks ACL2 for the protected prefix,
; asks ACL2 for the trailer over it, and concatenates the two has built the
; byte string `fn-frame-seal' specifies, and that handing that byte string
; back with the trailer recomputed over its own protected prefix decodes to
; the record that went in.  WHAT IS NOT PROVED: that SHA-256 is collision or
; preimage resistant.  Those are A-CRYPTO (books/assumptions.lisp), they were
; never consequences of the seam, and the attachment did not make them one.

(in-package "ACL2")
(include-book "frame-invariants")
(include-book "crypto-attach")
(local (include-book "arithmetic/top" :dir :system))

; The frame cluster's own proof vocabulary, which `frame-octets' withdraws on
; export.  Four theorems in this book, all about the frame grammar, so the
; narrow re-opening the parts of `frame' already do is the right one here too.
(local (in-theory (enable fn-frame-octet-vocabulary)))

; The protected prefix is octets, which is what makes `fn-frame-trailer'
; answer a digest rather than `:bad' on it.  Local: it is the shape fact the
; four keystones below need and nothing outside reasons about the prefix.
; The hypotheses are `fn-frame-inputp' spelled out rather than named,
; deliberately: a `max-payload' that appears in no conclusion is a free
; variable the rewriter cannot bind, and the goals below have already opened
; `fn-frame-inputp' by the time they need this.
(local
 (defthm fn-frame-trailer-protected-is-octets
   (implies (and (fn-frame-magicp magic)
                 (fn-cbor-octetp version)
                 (fn-cbor-octetp kind)
                 (fn-cbor-octet-listp payload)
                 (<= (len payload) *fn-cbor-max-uint*))
            (fn-cbor-octet-listp (fn-frame-protected magic version kind payload)))
   :hints (("Goal" :in-theory (e/d (fn-frame-protected fn-frame-header-octets)
                                   (fn-frame-header))))))

; -----------------------------------------------------------------------------
; The one owner.
;
; Total and guard verified at `:guard t', like the other entry points a host
; calls: an argument outside the domain answers `:bad' rather than the digest
; of a coerced value, so a host that sends the wrong thing is refused instead
; of being handed a plausible 32 octets.

(defun fn-frame-trailer (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-octet-listp octets))
      :bad
    (fn-frame-digest octets)))

(verify-guards fn-frame-trailer)

(defthm fn-frame-trailer-of-octets
  (implies (fn-cbor-octet-listp octets)
           (equal (fn-frame-trailer octets) (fn-frame-digest octets))))

(defthm fn-frame-trailer-is-a-digest
  (implies (fn-cbor-octet-listp octets)
           (fn-frame-digestp (fn-frame-trailer octets)))
  :hints (("Goal" :in-theory (enable fn-frame-digestp))))

; The trailer function is now closed: below this point it is read through the
; two facts above, exactly as every other book reads a record.
(in-theory (disable (:d fn-frame-trailer)))

; -----------------------------------------------------------------------------
; KEYSTONE 1: prefix from ACL2, trailer from ACL2, concatenation by the host,
; and the result is the model's sealed frame.
;
; The subject is what the host computes.  `tools/frame_bridge.py'
; `FrameSession.seal' is `prefix + trailer`, where `prefix` came from
; `(fn-store-frame-store-protected record)` and `trailer` now comes from
; `(fn-frame-trailer prefix)`; `host/native/io.lisp' `fnn-seal' is the same
; two calls and the same concatenation.  This theorem says that byte string is
; `fn-frame-seal', the specification encoder, under no host obligation at all.
; Before the trailer moved, the corresponding statement was
; `fn-frame-store-encode-is-protected-plus-digest' -- which holds only for a
; `digest` the theorem cannot name, and so left the host to be trusted for it.

(defthm fn-frame-protected-plus-trailer-is-seal
  (implies (fn-frame-inputp magic version kind payload max-payload)
           (equal (append (fn-frame-protected magic version kind payload)
                          (fn-frame-trailer
                           (fn-frame-protected magic version kind payload)))
                  (fn-frame-seal magic version kind payload)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-seal fn-frame-encode fn-frame-inputp)
                           (fn-frame-protected fn-frame-header)))))

; -----------------------------------------------------------------------------
; KEYSTONE 2: and it opens to what went in.
;
; The second half of every host site is the decode direction: `digest_of'
; (`fnn-digest-of', `feed_replay_frame') re-derives the trailer over the
; frame's own protected prefix and hands it to the decoder.  With the trailer
; owned here, that composition is `fn-frame-open' -- and `fn-frame-open-of-seal'
; already says what `fn-frame-open' does to a sealed frame.

(defthm fn-frame-decode-of-host-framing
  (implies (fn-frame-inputp magic version kind payload max-payload)
           (equal (fn-frame-decode
                   (append (fn-frame-protected magic version kind payload)
                           (fn-frame-trailer
                            (fn-frame-protected magic version kind payload)))
                   (fn-frame-trailer
                    (fn-frame-protected-prefix
                     (append (fn-frame-protected magic version kind payload)
                             (fn-frame-trailer
                              (fn-frame-protected magic version kind payload)))))
                   max-payload)
                  (fn-frame-ok magic version kind payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-open-of-seal)
                 (:instance fn-frame-protected-prefix-of-encode
                            (digest (fn-frame-digest
                                     (fn-frame-protected magic version kind
                                                         payload)))))
           :in-theory (e/d (fn-frame-open fn-frame-seal fn-frame-encode
                            fn-frame-inputp)
                           (fn-frame-protected fn-frame-header
                            fn-frame-protected-prefix fn-frame-decode
                            fn-frame-open-of-seal
                            fn-frame-protected-prefix-of-encode)))))

; -----------------------------------------------------------------------------
; The store instance, which is the line `tools/frame_bridge.py' and
; `host/native/io.lisp' actually execute.
;
; `FrameSession.store_frame' calls `(fn-store-frame-store-protected record)'
; -- `host/store-host.lisp:113', a rename of `fn-frame-store-protected' -- and
; then `(fn-frame-trailer prefix)'.  `FrameSession.store_unframe' calls
; `(fn-store-frame-store-decode framed digest)' with `digest` from
; `(fn-frame-trailer framed[:-32])'.

(defthm fn-frame-store-protected-plus-trailer-is-seal
  (implies (and (fn-cbor-octet-listp record)
                (fn-cbor-at-mostp record *fn-frame-max-store-payload*))
           (equal (append (fn-frame-store-protected record)
                          (fn-frame-trailer (fn-frame-store-protected record)))
                  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                                 *fn-frame-store-kind* record)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-protected-plus-trailer-is-seal
                            (magic *fn-frame-magic-store*)
                            (version *fn-frame-version*)
                            (kind *fn-frame-store-kind*)
                            (payload record)
                            (max-payload *fn-frame-max-store-payload*)))
           :in-theory (e/d (fn-frame-store-protected fn-frame-inputp
                            fn-frame-magicp)
                           (fn-frame-protected fn-frame-seal
                            fn-frame-protected-plus-trailer-is-seal)))))

(defthm fn-frame-store-decode-of-host-framing
  (implies (and (fn-cbor-octet-listp record)
                (fn-cbor-at-mostp record *fn-frame-max-store-payload*))
           (equal (fn-frame-store-decode
                   (append (fn-frame-store-protected record)
                           (fn-frame-trailer (fn-frame-store-protected record)))
                   (fn-frame-trailer
                    (fn-frame-protected-prefix
                     (append (fn-frame-store-protected record)
                             (fn-frame-trailer
                              (fn-frame-store-protected record))))))
                  (fn-frame-ok *fn-frame-magic-store* *fn-frame-version*
                               *fn-frame-store-kind* record)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-of-host-framing
                            (magic *fn-frame-magic-store*)
                            (version *fn-frame-version*)
                            (kind *fn-frame-store-kind*)
                            (payload record)
                            (max-payload *fn-frame-max-store-payload*)))
           :in-theory (e/d (fn-frame-store-decode fn-frame-store-protected
                            fn-frame-inputp fn-frame-magicp fn-frame-item)
                           (fn-frame-protected fn-frame-decode
                            fn-frame-protected-prefix
                            fn-frame-decode-of-host-framing)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; What leaves this book enabled is the four keystones and the two shape facts
; about the trailer.  The definition is already withdrawn above.  Nothing here
; is a `len' backchainer or an accessor equality.

(deftheory fn-frame-trailer-vocabulary
  '((:d fn-frame-trailer)))

(in-theory (disable fn-frame-trailer-vocabulary))
