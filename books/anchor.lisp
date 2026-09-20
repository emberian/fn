; fn: the external freshness anchor.
;
; FLR-003 (specs/failures.md:42) says checksummed checkpoints "do not establish
; freshness against replacement of the whole store by an old valid snapshot",
; and D10 (planning/decisions.md:54) resolves that with "a fresh sequence
; namespace" or an independently validated monotone anchor.  This book is the
; second half of that: the statement a node durably keeps so that a restore can
; be shown to be newer than the history it claims to continue.
;
; The anchor is a Roughtime response (draft-ietf-ntp-roughtime; this tree
; speaks the deployed "RoughTime v1" profile that roughtime.int08h.com:2002
; serves).  Five fields reach the logic:
;
;   key-id     the server's pinned long-term Ed25519 public key, 32 octets
;   midpoint   MIDP, microseconds since the Unix epoch
;   radius     RADI, microseconds of half-width around the midpoint
;   nonce      the 32 octets this node chose, which the server could not have
;              predicted, so the response cannot be a replay of an older one
;   signature  SIG, 64 octets, over the server's signed response
;
; ACL2 owns what the signature covers.  `fn-anchor-srep-octets' rebuilds the
; server's SREP message from midpoint, radius and the Merkle root, and
; `fn-anchor-signed-octets' prefixes the profile's response context; the host
; never tells the logic what was signed, it only supplies the verdict of the
; Ed25519 check over octets ACL2 produced.  A different nonce is a different
; root is a different signed message, so the nonce is load-bearing rather than
; decorative.
;
; Nothing here claims Ed25519 is unforgeable, that SHA-512 is collision
; resistant, or that a Roughtime server is honest.  `fn-anchor-sig-verify' and
; `fn-anchor-leaf-digest' are constrained functions (A-CRYPTO in shape; see
; the note at each encapsulate), and specs/anchor.md carries the trust.
;
; Style: docs/proof-style.md.  The four records here -- the anchor statement,
; the outcome, the node's durable state and a store image -- are opaque: a
; shape predicate, a constructor, total `:guard t' accessors, one
; accessor-of-constructor lemma per field, the three forward-chaining shape
; facts, and then the `:definition' runes withdrawn.  The book ends with an
; export theory; an includer that must open a definition enables
; `fn-anchor-vocabulary' (or `fn-anchor-octet-vocabulary') locally.

(in-package "ACL2")
(include-book "cbor-invariants")
(include-book "clock")
(include-book "defrecord")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

; Local vocabulary re-enable (docs/proof-style.md sec. 2).  This book builds
; octet lists by `append' and reads its own field widths, so it needs cbor's
; withdrawn list arithmetic; the frame grammar and the frame result records
; the FNAN durable record family lives in `books/anchor-record.lisp', which
; is the only book of this cluster that includes `frame' at all.
(local (in-theory (enable fn-cbor-invariants-vocabulary)))

; The clock book contributes only *fn-clock-max* (a constant), so no clock
; vocabulary is enabled here; if the bp deputy's realignment gives clock an
; export theory, this book still needs no edit.

; -----------------------------------------------------------------------------
; Domains

(defconst *fn-anchor-key-octets* 32)
(defconst *fn-anchor-nonce-octets* 32)
(defconst *fn-anchor-sig-octets* 64)
(defconst *fn-anchor-root-octets* 64)

; Roughtime times are microseconds in a uint64 field, the same bound the clock
; book already uses for DTN time.
(defconst *fn-anchor-max-time* *fn-clock-max*)

; "RoughTime v1 response signature" and a terminating NUL: the context string
; the deployed profile prefixes to SREP before signing.
(defconst *fn-anchor-response-context*
  '(82 111 117 103 104 84 105 109 101 32 118 49 32 114 101 115 112 111 110
    115 101 32 115 105 103 110 97 116 117 114 101 0))

; "RoughTime v1 delegation signature--" and a terminating NUL: the context a
; server prefixes to the DELE message when its long-term key authorizes a
; short-lived one.
(defconst *fn-anchor-delegation-context*
  '(82 111 117 103 104 84 105 109 101 32 118 49 32 100 101 108 101 103 97 116
    105 111 110 32 115 105 103 110 97 116 117 114 101 45 45 0))

(defconst *fn-anchor-tag-pubk* '(80 85 66 75))
(defconst *fn-anchor-tag-mint* '(77 73 78 84))
(defconst *fn-anchor-tag-maxt* '(77 65 88 84))
(defconst *fn-anchor-tag-radi* '(82 65 68 73))
(defconst *fn-anchor-tag-midp* '(77 73 68 80))
(defconst *fn-anchor-tag-root* '(82 79 79 84))

(defun fn-anchor-octets-of-lengthp (xs n)
  (declare (xargs :guard (natp n)))
  (and (fn-cbor-octet-listp xs) (equal (len xs) n)))

(defun fn-anchor-timep (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x *fn-anchor-max-time*)))

(verify-guards fn-anchor-octets-of-lengthp)
(verify-guards fn-anchor-timep)

; The width predicate is withdrawn at export: its second conjunct is a `len'
; equality, and a `len'-backchaining rule must not leave a book
; (docs/proof-style.md sec. 8).  What an includer needs from it lands in the
; context by forward chaining instead.
(defthm fn-anchor-octets-of-lengthp-forward
  (implies (fn-anchor-octets-of-lengthp xs n)
           (and (fn-cbor-octet-listp xs) (equal (len xs) n)))
  :rule-classes :forward-chaining)

; -----------------------------------------------------------------------------
; Total selectors
;
; The record accessors below are total (`:guard t') with an `mbe' whose
; `:logic' is the raw selector chain and whose `:exec' is these two helpers,
; exactly as `fn-ag-car'/`fn-ag-cdr' serve the core cluster.  Each helper is
; its logical primitive by `mbe', so opening its definition is the equality
; and no `-is-' twin is exported.

(defun fn-anchor-ag-car (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (if (consp x) (car x) nil)))

(defun fn-anchor-ag-cdr (x)
  (declare (xargs :guard t))
  (mbe :logic (cdr x) :exec (if (consp x) (cdr x) nil)))

; -----------------------------------------------------------------------------
; Little-endian fields
;
; Roughtime is little-endian throughout; every other field grammar in this tree
; is big-endian, so the conversion lives here and nowhere else.

(defun fn-anchor-le-bytes (n k)
  (declare (xargs :guard (and (natp n) (natp k)) :verify-guards nil))
  (if (zp k)
      nil
    (cons (mod (nfix n) 256)
          (fn-anchor-le-bytes (floor (nfix n) 256) (- k 1)))))

(verify-guards fn-anchor-le-bytes
  :hints (("Goal" :in-theory (disable floor))))

(defthm fn-anchor-le-bytes-are-octets
  (fn-cbor-octet-listp (fn-anchor-le-bytes n k))
  :hints (("Goal" :in-theory (disable floor))))

(defthm fn-anchor-le-bytes-len
  (equal (len (fn-anchor-le-bytes n k)) (nfix k))
  :hints (("Goal" :in-theory (disable floor mod))))

(in-theory (disable (:d fn-anchor-le-bytes)))

; `len' distributes over `append'.  frame-octets proves this as
; `fn-frame-len-of-append', but this book no longer includes frame; it is
; proof vocabulary either way, so it is local.
(local
 (defthm fn-anchor-len-of-append
   (equal (len (append x y)) (+ (len x) (len y)))))

; -----------------------------------------------------------------------------
; A-CRYPTO, first seam: the Merkle leaf digest
;
; The host computes SHA-512 of the single octet 0 followed by the nonce, which
; is the Roughtime leaf hash and, for a one-nonce tree with an empty PATH and
; INDX 0, is also the root.  The logic knows only that it is 64 octets.  No
; theorem below claims collision or preimage resistance.

(encapsulate
  (((fn-anchor-leaf-digest *) => *))
  (local (defun fn-anchor-leaf-digest (nonce)
           (declare (ignore nonce))
           '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
  (defthm fn-anchor-leaf-digest-octet-listp
    (fn-cbor-octet-listp (fn-anchor-leaf-digest nonce)))
  (defthm fn-anchor-leaf-digest-length
    (equal (len (fn-anchor-leaf-digest nonce)) *fn-anchor-root-octets*)))

; -----------------------------------------------------------------------------
; A-CRYPTO, second seam: Ed25519 verification
;
; `fn-anchor-sig-verify' takes a public key, the message octets and the
; signature octets to a boolean.  This is the shape the crypto seam another
; lane is building will carry; when that book lands, this encapsulate is the
; one to retire by functional instantiation rather than a second copy.
; `books/crypto-seam.lisp' is now on `dev', but its seam is a digest and a
; tagged-preimage signature over fn's own statements, not an Ed25519 check of
; a foreign server's message; the retirement is an open cross-cluster item and
; is recorded in planning/lanes/HANDOFF-w3-time-anchor.md, not done here.
;
; Two constraints keep the seam from swallowing the theorems that use it: the
; verdict is a boolean, and a key or signature of the wrong length is never
; accepted.  Unforgeability is NOT a constraint and is not claimed anywhere.

(encapsulate
  (((fn-anchor-sig-verify * * *) => *))

  (local (defun fn-anchor-sig-verify (key message signature)
           (declare (xargs :guard t))
           (and (fn-anchor-octets-of-lengthp key *fn-anchor-key-octets*)
                (fn-anchor-octets-of-lengthp signature *fn-anchor-sig-octets*)
                (consp message)
                t)))

  (defthm fn-anchor-sig-verify-booleanp
    (booleanp (fn-anchor-sig-verify key message signature)))

  ; A verdict is about a key of the right size.  Nothing verifies under a
  ; truncated or oversized key.
  (defthm fn-anchor-sig-verify-needs-a-key
    (implies (not (fn-anchor-octets-of-lengthp key *fn-anchor-key-octets*))
             (not (fn-anchor-sig-verify key message signature))))

  ; Nor under anything that is not a 64-octet Ed25519 signature.
  (defthm fn-anchor-sig-verify-needs-a-signature
    (implies (not (fn-anchor-octets-of-lengthp signature *fn-anchor-sig-octets*))
             (not (fn-anchor-sig-verify key message signature)))))

; -----------------------------------------------------------------------------
; The anchor statement, as an opaque record

(fn-defrecord fn-anchor
  :tag :fn-anchor
  :constructor (fn-anchor key-id delegate mint maxt delegation-signature
                          midpoint radius nonce signature)
  :fields ((fn-anchor-key
            (fn-anchor-octets-of-lengthp (fn-anchor-key x)
                                         *fn-anchor-key-octets*))
           (fn-anchor-delegate
            (fn-anchor-octets-of-lengthp (fn-anchor-delegate x)
                                         *fn-anchor-key-octets*))
           (fn-anchor-mint fn-anchor-timep)
           (fn-anchor-maxt fn-anchor-timep)
           (fn-anchor-delegation-signature
            (fn-anchor-octets-of-lengthp (fn-anchor-delegation-signature x)
                                         *fn-anchor-sig-octets*))
           (fn-anchor-midpoint fn-anchor-timep)
           (fn-anchor-radius fn-anchor-timep)
           (fn-anchor-nonce
            (fn-anchor-octets-of-lengthp (fn-anchor-nonce x)
                                         *fn-anchor-nonce-octets*))
           (fn-anchor-signature
            (fn-anchor-octets-of-lengthp (fn-anchor-signature x)
                                         *fn-anchor-sig-octets*)))
  :recognizer fn-anchor-p
  :car-fn fn-anchor-ag-car
  :cdr-fn fn-anchor-ag-cdr)

; -----------------------------------------------------------------------------
; What the server signed
;
; SREP is a Roughtime message with three tags in ascending little-endian tag
; order: RADI (uint32), MIDP (uint64), ROOT.  Its header is the tag count, the
; two value offsets and the three tag words; the values follow in the same
; order.  For the one-nonce tree this node sends, ROOT is the leaf digest of
; its own nonce, PATH is empty and INDX is zero.

(defun fn-anchor-root (a)
  (declare (xargs :guard t))
  (fn-anchor-leaf-digest (fn-anchor-nonce a)))

(defun fn-anchor-srep-from-root (radius midpoint root)
  ; The exact SREP octets, given the root as a value rather than through the
  ; constrained digest, so a captured response can be checked against this
  ; reconstruction by evaluation.
  (declare (xargs :guard (and (fn-anchor-timep radius)
                              (fn-anchor-timep midpoint)
                              (fn-anchor-octets-of-lengthp
                               root *fn-anchor-root-octets*))
                  :verify-guards nil))
  (append (fn-anchor-le-bytes 3 4)
          (append (fn-anchor-le-bytes 4 4)
                  (append (fn-anchor-le-bytes 12 4)
                          (append *fn-anchor-tag-radi*
                                  (append *fn-anchor-tag-midp*
                                          (append *fn-anchor-tag-root*
                                                  (append (fn-anchor-le-bytes radius 4)
                                                          (append (fn-anchor-le-bytes midpoint 8)
                                                                  root)))))))))

(verify-guards fn-anchor-srep-from-root)

(defun fn-anchor-srep-octets (a)
  (declare (xargs :guard (fn-anchor-p a) :verify-guards nil))
  (fn-anchor-srep-from-root (fn-anchor-radius a)
                            (fn-anchor-midpoint a)
                            (fn-anchor-root a)))

; The `mbe'/guard equalities below exist to discharge guards and to record the
; widths of the two reconstructions; they are not rewrite rules
; (docs/proof-style.md sec. 3) and are cited by `:use'.
(defthm fn-anchor-srep-octets-guard
  (implies (fn-anchor-p a)
           (and (fn-anchor-timep (fn-anchor-radius a))
                (fn-anchor-timep (fn-anchor-midpoint a))
                (fn-anchor-octets-of-lengthp (fn-anchor-root a)
                                             *fn-anchor-root-octets*)))
  :rule-classes nil)

(verify-guards fn-anchor-srep-octets
  :hints (("Goal" :use (fn-anchor-srep-octets-guard))))

(defun fn-anchor-signed-from-root (radius midpoint root)
  (declare (xargs :guard (and (fn-anchor-timep radius)
                              (fn-anchor-timep midpoint)
                              (fn-anchor-octets-of-lengthp
                               root *fn-anchor-root-octets*))
                  :verify-guards nil))
  (append *fn-anchor-response-context*
          (fn-anchor-srep-from-root radius midpoint root)))

(verify-guards fn-anchor-signed-from-root)

(defun fn-anchor-signed-octets (a)
  (declare (xargs :guard (fn-anchor-p a) :verify-guards nil))
  (fn-anchor-signed-from-root (fn-anchor-radius a)
                              (fn-anchor-midpoint a)
                              (fn-anchor-root a)))

(verify-guards fn-anchor-signed-octets
  :hints (("Goal" :use (fn-anchor-srep-octets-guard))))

; The delegation message DELE, rebuilt the same way: three tags in ascending
; little-endian order, PUBK then MINT then MAXT, values 32, 8 and 8 octets.
; Rebuilding it here is what keeps the certificate check from becoming a bit
; the host asserts: the octets the long-term key signed are ACL2's.
(defun fn-anchor-dele-octets (a)
  (declare (xargs :guard (fn-anchor-p a) :verify-guards nil))
  (append (fn-anchor-le-bytes 3 4)
          (append (fn-anchor-le-bytes 32 4)
                  (append (fn-anchor-le-bytes 40 4)
                          (append *fn-anchor-tag-pubk*
                                  (append *fn-anchor-tag-mint*
                                          (append *fn-anchor-tag-maxt*
                                                  (append (fn-anchor-delegate a)
                                                          (append (fn-anchor-le-bytes (fn-anchor-mint a) 8)
                                                                  (fn-anchor-le-bytes (fn-anchor-maxt a) 8))))))))))

(verify-guards fn-anchor-dele-octets)

(defun fn-anchor-delegation-signed-octets (a)
  (declare (xargs :guard (fn-anchor-p a) :verify-guards nil))
  (append *fn-anchor-delegation-context* (fn-anchor-dele-octets a)))

(verify-guards fn-anchor-delegation-signed-octets)

(defthm fn-anchor-dele-octets-are-octets
  (implies (fn-anchor-p a)
           (fn-cbor-octet-listp (fn-anchor-dele-octets a))))

(defthm fn-anchor-dele-octets-length
  (implies (fn-anchor-p a)
           (equal (len (fn-anchor-dele-octets a)) 72))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-anchor-len-of-append))))

(defthm fn-anchor-srep-octets-are-octets
  (fn-cbor-octet-listp (fn-anchor-srep-octets a)))

(defthm fn-anchor-srep-octets-length
  (equal (len (fn-anchor-srep-octets a)) 100)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-anchor-len-of-append))))

(defthm fn-anchor-signed-octets-are-octets
  (fn-cbor-octet-listp (fn-anchor-signed-octets a)))

; Equal-length prefixes cancel.  This is the only fact the keystone below
; needs about `append', and it is proof vocabulary, so it is local and
; `:rule-classes nil' (docs/proof-style.md sec. 3).
(local
 (defun fn-anchor-append-induction (a b)
   (declare (xargs :guard t))
   (if (or (atom a) (atom b))
       (list a b)
     (fn-anchor-append-induction (cdr a) (cdr b)))))

(local
 (defthm fn-anchor-append-cancels-equal-length-prefixes
   (implies (and (equal (len a) (len b))
                 (equal (append a x) (append b y)))
            (equal x y))
   :rule-classes nil
   :hints (("Goal" :induct (fn-anchor-append-induction a b)))))

; KEYSTONE.  The signed message determines the nonce's digest: two anchors that
; were signed over the same octets have the same Merkle root.  This is what
; makes the nonce load-bearing without assuming anything about SHA-512.
(defthm fn-anchor-signed-octets-determine-the-root
  (implies (and (fn-anchor-p a)
                (fn-anchor-p b)
                (equal (fn-anchor-signed-octets a) (fn-anchor-signed-octets b)))
           (equal (fn-anchor-root a) (fn-anchor-root b)))
  :hints (("Goal"
           :in-theory (enable fn-anchor-signed-octets
                              fn-anchor-signed-from-root
                              fn-anchor-srep-from-root)
           :use ((:instance fn-anchor-append-cancels-equal-length-prefixes
                            (a (fn-anchor-le-bytes (fn-anchor-radius a) 4))
                            (b (fn-anchor-le-bytes (fn-anchor-radius b) 4))
                            (x (append (fn-anchor-le-bytes
                                        (fn-anchor-midpoint a) 8)
                                       (fn-anchor-leaf-digest
                                        (fn-anchor-nonce a))))
                            (y (append (fn-anchor-le-bytes
                                        (fn-anchor-midpoint b) 8)
                                       (fn-anchor-leaf-digest
                                        (fn-anchor-nonce b)))))
                 (:instance fn-anchor-append-cancels-equal-length-prefixes
                            (a (fn-anchor-le-bytes (fn-anchor-midpoint a) 8))
                            (b (fn-anchor-le-bytes (fn-anchor-midpoint b) 8))
                            (x (fn-anchor-leaf-digest (fn-anchor-nonce a)))
                            (y (fn-anchor-leaf-digest
                                (fn-anchor-nonce b))))))))

; -----------------------------------------------------------------------------
; Validity and pinning

; The whole Roughtime trust chain, in the logic:
;   the pinned long-term key signed a delegation naming a short-lived key and
;   a validity window; that short-lived key signed this response; and the
;   midpoint lies inside the window it was delegated for.  Each signature is
;   checked over octets this book built, never over octets the host described.
(defun fn-anchor-verifiedp (a)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-anchor-p a)
       (fn-anchor-sig-verify (fn-anchor-key a)
                             (fn-anchor-delegation-signed-octets a)
                             (fn-anchor-delegation-signature a))
       (fn-anchor-sig-verify (fn-anchor-delegate a)
                             (fn-anchor-signed-octets a)
                             (fn-anchor-signature a))
       (<= (fn-anchor-mint a) (fn-anchor-midpoint a))
       (<= (fn-anchor-midpoint a) (fn-anchor-maxt a))
       t))

(verify-guards fn-anchor-verifiedp)

(defun fn-anchor-pinnedp (a pinned)
  (declare (xargs :guard t))
  (and (fn-anchor-p a)
       (true-listp pinned)
       (member-equal (fn-anchor-key a) pinned)
       t))

(verify-guards fn-anchor-pinnedp)

(defun fn-anchor-acceptablep (a pinned)
  (declare (xargs :guard t))
  (and (fn-anchor-verifiedp a) (fn-anchor-pinnedp a pinned)))

(verify-guards fn-anchor-acceptablep)

; -----------------------------------------------------------------------------
; Strictly newer
;
; "Later" is not "a bigger midpoint".  A Roughtime response asserts only that
; true time lay in [midpoint - radius, midpoint + radius].  One anchor is
; strictly newer than another exactly when its whole interval lies after the
; other's, so two readings whose intervals overlap are never ordered and a
; restore can never be admitted on an unresolvable difference.  This is the
; same conservatism books/clock.lisp applies to a host wall reading.

(defun fn-anchor-earliest (a)
  (declare (xargs :guard (fn-anchor-p a)))
  (nfix (- (fn-anchor-midpoint a) (fn-anchor-radius a))))

(defun fn-anchor-latest (a)
  (declare (xargs :guard (fn-anchor-p a)))
  (+ (fn-anchor-midpoint a) (fn-anchor-radius a)))

(verify-guards fn-anchor-earliest)
(verify-guards fn-anchor-latest)

(defun fn-anchor-newerp (a b)
  (declare (xargs :guard t))
  (and (fn-anchor-p a)
       (fn-anchor-p b)
       (< (fn-anchor-latest b) (fn-anchor-earliest a))
       t))

(verify-guards fn-anchor-newerp)

; -----------------------------------------------------------------------------
; Outcomes, as an opaque record
;
; Three outcomes stay distinct all the way out (AGENTS.md, D13).  `:uncertain'
; is the answer when no anchor could be obtained at all: the node does not know
; whether the image is stale, and that is not the same as knowing it is.

(fn-defrecord fn-anchor-outcome
  :tag :fn-anchor-outcome
  :constructor (fn-anchor-outcome status reason payload)
  :fields ((fn-anchor-status t)
           (fn-anchor-reason t)
           (fn-anchor-payload t))
  :car-fn fn-anchor-ag-car
  :cdr-fn fn-anchor-ag-cdr)

; -----------------------------------------------------------------------------
; The node's durable anchor state, as an opaque record

(fn-defrecord fn-anchor-node
  :tag :fn-anchor-node
  :constructor (fn-anchor-node pinned latest incarnation)
  :fields ((fn-anchor-node-pinned (true-listp (fn-anchor-node-pinned x)))
           (fn-anchor-node-latest
            (or (null (fn-anchor-node-latest x))
                (fn-anchor-p (fn-anchor-node-latest x))))
           (fn-anchor-node-incarnation natp))
  :car-fn fn-anchor-ag-car
  :cdr-fn fn-anchor-ag-cdr)

; Accepting an anchor into the node's durable state.  A node that already holds
; an anchor accepts only a strictly newer one; the refusal reasons stay apart
; so an operator can tell an unverified response from a stale one.  The guard
; carries `fn-anchor-nodep' rather than re-deciding it (docs/proof-style.md
; sec. 4); the logic body is total and unchanged.
(defun fn-anchor-node-accept (node a)
  (declare (xargs :guard (fn-anchor-nodep node) :verify-guards nil))
  (if (not (fn-anchor-p a))
      (fn-anchor-outcome :uncertain :no-anchor node)
    (if (not (fn-anchor-verifiedp a))
        (fn-anchor-outcome :refused :unverified node)
      (if (not (fn-anchor-pinnedp a (fn-anchor-node-pinned node)))
          (fn-anchor-outcome :refused :unpinned node)
        (if (and (fn-anchor-node-latest node)
                 (not (fn-anchor-newerp a (fn-anchor-node-latest node))))
            (fn-anchor-outcome :refused :stale node)
          (fn-anchor-outcome :accepted nil
                             (fn-anchor-node (fn-anchor-node-pinned node)
                                             a
                                             (fn-anchor-node-incarnation node))))))))

(verify-guards fn-anchor-node-accept)

(defun fn-anchor-node-accept-list (node anchors)
  (declare (xargs :guard (and (fn-anchor-nodep node) (true-listp anchors))
                  :verify-guards nil))
  (if (not (consp anchors))
      node
    (let ((outcome (fn-anchor-node-accept node (car anchors))))
      (fn-anchor-node-accept-list
       (if (equal (fn-anchor-status outcome) :accepted)
           (fn-anchor-payload outcome)
         node)
       (cdr anchors)))))

; -----------------------------------------------------------------------------
; Advancing an incarnation
;
; OBJ-006: an origin's incarnation and counter cannot be reused for a different
; event.  An incarnation advances only under an anchor the node has not already
; seen the like of, so two incarnations of one origin are separated by a
; measured, signed interval rather than by a local decision.

(defun fn-anchor-node-advance (node a)
  (declare (xargs :guard (fn-anchor-nodep node) :verify-guards nil))
  (let ((outcome (fn-anchor-node-accept node a)))
    (if (not (equal (fn-anchor-status outcome) :accepted))
        outcome
      (fn-anchor-outcome
       :accepted nil
       (fn-anchor-node (fn-anchor-node-pinned node)
                       a
                       (+ 1 (fn-anchor-node-incarnation node)))))))

(verify-guards fn-anchor-node-advance)

; -----------------------------------------------------------------------------
; A store image and the restore decision, as an opaque record
;
; An image is a snapshot offered to a node: the incarnation it claims and the
; newest anchor any durable record inside it refers to.  An image that refers
; to no anchor at all carries no freshness evidence of its own; it is admitted
; only under an anchor the node can verify, because there is nothing it could
; be stale with respect to.

(fn-defrecord fn-anchor-image
  :tag :fn-anchor-image
  :constructor (fn-anchor-image incarnation referenced)
  :fields ((fn-anchor-image-incarnation natp)
           (fn-anchor-image-referenced
            (or (null (fn-anchor-image-referenced x))
                (fn-anchor-p (fn-anchor-image-referenced x)))))
  :car-fn fn-anchor-ag-car
  :cdr-fn fn-anchor-ag-cdr)

(defun fn-anchor-restore (node image presented)
  (declare (xargs :guard (and (fn-anchor-nodep node) (fn-anchor-imagep image))
                  :verify-guards nil))
  (if (not (fn-anchor-p presented))
      ; No anchor was obtained.  Whether this image is the newest one is not
      ; known, and an unknown is never reported as a refusal.
      (fn-anchor-outcome :uncertain :no-anchor image)
    (if (not (fn-anchor-verifiedp presented))
        (fn-anchor-outcome :refused :unverified image)
      (if (not (fn-anchor-pinnedp presented (fn-anchor-node-pinned node)))
          (fn-anchor-outcome :refused :unpinned image)
        (if (and (fn-anchor-image-referenced image)
                 (not (fn-anchor-newerp presented
                                        (fn-anchor-image-referenced image))))
            ; Possibly stale: the image refers to an anchor this restore cannot
            ; show it is later than.  The distinct reason is the whole point.
            (fn-anchor-outcome :refused :possibly-stale image)
          (fn-anchor-outcome
           :accepted nil
           (fn-anchor-node (fn-anchor-node-pinned node)
                           presented
                           (+ 1 (fn-anchor-image-incarnation image)))))))))

(verify-guards fn-anchor-restore)

; -----------------------------------------------------------------------------
; Fork evidence
;
; Two images that claim the same incarnation but refer to different newest
; anchors are two histories of one origin.  Neither is admitted as that
; incarnation, and the result carries both so the evidence is preserved rather
; than resolved by a last-writer rule (AGENTS.md: preserve conflicting
; evidence; never last-writer-wins on wall-clock time).

(defun fn-anchor-pair-admit (left right)
  (declare (xargs :guard (and (fn-anchor-imagep left) (fn-anchor-imagep right))
                  :verify-guards nil))
  (if (not (equal (fn-anchor-image-incarnation left)
                  (fn-anchor-image-incarnation right)))
      (fn-anchor-outcome :distinct nil (list left right))
    (if (equal (fn-anchor-image-referenced left)
               (fn-anchor-image-referenced right))
        (fn-anchor-outcome :same nil (list left right))
      (fn-anchor-outcome :refused :fork (list left right)))))

(verify-guards fn-anchor-pair-admit)

(defun fn-anchor-pair-admittedp (outcome)
  (declare (xargs :guard (fn-anchor-outcomep outcome)))
  (equal (fn-anchor-status outcome) :same))

(verify-guards fn-anchor-pair-admittedp)

; -----------------------------------------------------------------------------
; The host-facing entries
;
; `fn-anchor-sig-verify' is constrained, so it cannot be executed; the host
; supplies its value the way `books/frame.lisp' has the host supply the
; integrity trailer.  The host asks ACL2 for the octets that are signed
; (`fn-anchor-signed-from-root'), runs Ed25519 over exactly those octets with
; the pinned key through `tools/crypto_host.py', and passes the verdict here.
; `books/anchor-invariants.lisp' proves these entries EQUAL to the functions
; the theorems are about whenever the verdict is the one the seam names, so
; there is one subject, not two.

(defun fn-anchor-node-accept-observed (node a verdict)
  (declare (xargs :guard (fn-anchor-nodep node) :verify-guards nil))
  (if (not (fn-anchor-p a))
      (fn-anchor-outcome :uncertain :no-anchor node)
    (if (not (and verdict t))
        (fn-anchor-outcome :refused :unverified node)
      (if (not (fn-anchor-pinnedp a (fn-anchor-node-pinned node)))
          (fn-anchor-outcome :refused :unpinned node)
        (if (and (fn-anchor-node-latest node)
                 (not (fn-anchor-newerp a (fn-anchor-node-latest node))))
            (fn-anchor-outcome :refused :stale node)
          (fn-anchor-outcome :accepted nil
                             (fn-anchor-node (fn-anchor-node-pinned node)
                                             a
                                             (fn-anchor-node-incarnation node))))))))

(verify-guards fn-anchor-node-accept-observed)

(defun fn-anchor-node-advance-observed (node a verdict)
  (declare (xargs :guard (fn-anchor-nodep node) :verify-guards nil))
  (let ((outcome (fn-anchor-node-accept-observed node a verdict)))
    (if (not (equal (fn-anchor-status outcome) :accepted))
        outcome
      (fn-anchor-outcome
       :accepted nil
       (fn-anchor-node (fn-anchor-node-pinned node)
                       a
                       (+ 1 (fn-anchor-node-incarnation node)))))))

(verify-guards fn-anchor-node-advance-observed)

(defun fn-anchor-restore-observed (node image presented verdict)
  (declare (xargs :guard (and (fn-anchor-nodep node) (fn-anchor-imagep image))
                  :verify-guards nil))
  (if (not (fn-anchor-p presented))
      (fn-anchor-outcome :uncertain :no-anchor image)
    (if (not (and verdict t))
        (fn-anchor-outcome :refused :unverified image)
      (if (not (fn-anchor-pinnedp presented (fn-anchor-node-pinned node)))
          (fn-anchor-outcome :refused :unpinned image)
        (if (and (fn-anchor-image-referenced image)
                 (not (fn-anchor-newerp presented
                                        (fn-anchor-image-referenced image))))
            (fn-anchor-outcome :refused :possibly-stale image)
          (fn-anchor-outcome
           :accepted nil
           (fn-anchor-node (fn-anchor-node-pinned node)
                           presented
                           (+ 1 (fn-anchor-image-incarnation image)))))))))

(verify-guards fn-anchor-restore-observed)

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md sec. 2)
;
; What leaves this book enabled: the record lemmas of the four records, their
; three forward-chaining shape facts each, the two crypto-seam constraints, and
; `fn-anchor-signed-octets-determine-the-root'.  Everything else -- every
; record accessor, constructor and shape, every recognizer, the reconstruction
; of the signed octets, the interval order, all five transitions, both host
; entries -- is withdrawn here, as `(:d name)' only, so
; ground evaluation and type prescriptions still decide.
;
; An includer that must open one of these enables `fn-anchor-vocabulary'
; locally and says why; a book that reasons about octet widths also enables
; `fn-anchor-octet-vocabulary'.

(deftheory fn-anchor-vocabulary
  '((:d fn-anchor-shapep) (:d fn-anchor) (:d fn-anchor-key)
    (:d fn-anchor-delegate) (:d fn-anchor-mint) (:d fn-anchor-maxt)
    (:d fn-anchor-delegation-signature) (:d fn-anchor-midpoint)
    (:d fn-anchor-radius) (:d fn-anchor-nonce) (:d fn-anchor-signature)
    (:d fn-anchor-outcome-shapep) (:d fn-anchor-outcome)
    (:d fn-anchor-status) (:d fn-anchor-reason) (:d fn-anchor-payload)
    (:d fn-anchor-node-shapep) (:d fn-anchor-node)
    (:d fn-anchor-node-pinned) (:d fn-anchor-node-latest)
    (:d fn-anchor-node-incarnation)
    (:d fn-anchor-image-shapep) (:d fn-anchor-image)
    (:d fn-anchor-image-incarnation) (:d fn-anchor-image-referenced)
    (:d fn-anchor-p) (:d fn-anchor-outcomep) (:d fn-anchor-nodep)
    (:d fn-anchor-imagep) (:d fn-anchor-octets-of-lengthp)
    (:d fn-anchor-timep) (:d fn-anchor-le-bytes)
    (:d fn-anchor-ag-car) (:d fn-anchor-ag-cdr)
    (:d fn-anchor-root) (:d fn-anchor-srep-from-root)
    (:d fn-anchor-srep-octets) (:d fn-anchor-signed-from-root)
    (:d fn-anchor-signed-octets) (:d fn-anchor-dele-octets)
    (:d fn-anchor-delegation-signed-octets)
    (:d fn-anchor-verifiedp) (:d fn-anchor-pinnedp)
    (:d fn-anchor-acceptablep) (:d fn-anchor-earliest)
    (:d fn-anchor-latest) (:d fn-anchor-newerp)
    (:d fn-anchor-node-accept) (:d fn-anchor-node-accept-list)
    (:d fn-anchor-node-advance) (:d fn-anchor-restore)
    (:d fn-anchor-pair-admit) (:d fn-anchor-pair-admittedp)
    (:d fn-anchor-node-accept-observed)
    (:d fn-anchor-node-advance-observed) (:d fn-anchor-restore-observed)
))

(deftheory fn-anchor-octet-vocabulary
  '(fn-anchor-le-bytes-are-octets fn-anchor-le-bytes-len
    fn-anchor-leaf-digest-length fn-anchor-dele-octets-are-octets
    fn-anchor-srep-octets-are-octets fn-anchor-signed-octets-are-octets))

(in-theory (disable (:d fn-anchor-shapep) (:d fn-anchor) (:d fn-anchor-key)
             (:d fn-anchor-delegate) (:d fn-anchor-mint) (:d fn-anchor-maxt)
             (:d fn-anchor-delegation-signature) (:d fn-anchor-midpoint)
             (:d fn-anchor-radius) (:d fn-anchor-nonce)
             (:d fn-anchor-signature)
             (:d fn-anchor-outcome-shapep) (:d fn-anchor-outcome)
             (:d fn-anchor-status) (:d fn-anchor-reason)
             (:d fn-anchor-payload)
             (:d fn-anchor-node-shapep) (:d fn-anchor-node)
             (:d fn-anchor-node-pinned) (:d fn-anchor-node-latest)
             (:d fn-anchor-node-incarnation)
             (:d fn-anchor-image-shapep) (:d fn-anchor-image)
             (:d fn-anchor-image-incarnation)
             (:d fn-anchor-image-referenced)
             (:d fn-anchor-p) (:d fn-anchor-outcomep) (:d fn-anchor-nodep)
             (:d fn-anchor-imagep) (:d fn-anchor-octets-of-lengthp)
             (:d fn-anchor-timep) (:d fn-anchor-le-bytes)
             (:d fn-anchor-ag-car) (:d fn-anchor-ag-cdr)
             (:d fn-anchor-root) (:d fn-anchor-srep-from-root)
             (:d fn-anchor-srep-octets) (:d fn-anchor-signed-from-root)
             (:d fn-anchor-signed-octets) (:d fn-anchor-dele-octets)
             (:d fn-anchor-delegation-signed-octets)
             (:d fn-anchor-verifiedp) (:d fn-anchor-pinnedp)
             (:d fn-anchor-acceptablep) (:d fn-anchor-earliest)
             (:d fn-anchor-latest) (:d fn-anchor-newerp)
             (:d fn-anchor-node-accept) (:d fn-anchor-node-accept-list)
             (:d fn-anchor-node-advance) (:d fn-anchor-restore)
             (:d fn-anchor-pair-admit) (:d fn-anchor-pair-admittedp)
             (:d fn-anchor-node-accept-observed)
             (:d fn-anchor-node-advance-observed)
             (:d fn-anchor-restore-observed)
))

(in-theory (disable fn-anchor-le-bytes-are-octets fn-anchor-le-bytes-len
             fn-anchor-leaf-digest-length fn-anchor-dele-octets-are-octets
             fn-anchor-srep-octets-are-octets
             fn-anchor-signed-octets-are-octets))
