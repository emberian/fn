; fn TCPCLv4 octet grammar (RFC 9174): every message as an exact octet codec.
;
; The convergence layer the native host runs (specs/tcpcl.md).  This book
; turns octets into decoded message records and back.  Every length field is
; compared with the configured cap or MRU before any octet is taken, so a
; peer's claimed length bounds neither the work nor the allocation: the
; decoder walks at most the octets of one maximal message
; (fn-tcl-max-message) and copies at most that many.  A decode returns one
; of three distinct outcomes: (fn-tcl-parse-ok msg rest) with `rest` the
; untouched suffix, (fn-tcl-parse-need) when the buffer holds no complete
; message yet (nothing is copied; the host reads more and retries with the
; same buffer), or (fn-tcl-parse-error reason).
;
; RFC 9174 sections: 4.2 (Contact Header), 4.5 (message header), 4.6 and 4.8
; (SESS_INIT and session extension items), 5.1.1 (KEEPALIVE), 5.1.2
; (MSG_REJECT), 5.2.2 to 5.2.5 (XFER_SEGMENT, XFER_ACK, XFER_REFUSE, transfer
; extension items), 6.1 (SESS_TERM).  All integers are unsigned, network
; byte order.  Flag octets are kept raw in the records so that every
; accepted octet string re-encodes to itself; the reserved bits the RFC says
; a receiver SHALL ignore are ignored by the session book's flag predicates,
; not dropped by the codec.
;
; Local policy caps: a node ID longer than 1024 octets or an extension item
; list longer than 4096 octets is refused at decode time.

(in-package "ACL2")
(include-book "tcpcl-records")

; The base-256 digit facts the codec needs, proved once under the arithmetic
; libraries and exported without them: their :elim and :generalize rules loop
; the list proofs below, so the include is local to this encapsulate.
(encapsulate ()
  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
  (local (include-book "arithmetic/top" :dir :system))

  (defthm fn-tcl-digit-bounds
    (implies (natp n)
             (and (integerp (floor n 256)) (<= 0 (floor n 256))
                  (integerp (mod n 256)) (<= 0 (mod n 256)) (< (mod n 256) 256)))
    :rule-classes ((:rewrite)
                   (:linear :corollary (implies (natp n) (<= 0 (floor n 256))))
                   (:linear :corollary (implies (natp n) (<= 0 (mod n 256))))
                   (:linear :corollary (implies (natp n) (< (mod n 256) 256)))
                   (:type-prescription :corollary (implies (natp n) (natp (floor n 256))))
                   (:type-prescription :corollary (implies (natp n) (natp (mod n 256))))))

  (defthm fn-tcl-digit-decomposition
    (implies (natp n)
             (equal (+ (mod n 256) (* 256 (floor n 256))) n))
    :rule-classes nil)

  (defthm fn-tcl-floor-mod-of-digit
    (implies (and (natp a) (< a 256) (natp r))
             (and (equal (mod (+ a (* 256 r)) 256) a)
                  (equal (floor (+ a (* 256 r)) 256) r)))
    :hints (("Goal" :in-theory (e/d (associativity-of-* distributivity) (floor mod))
             :nonlinearp t))))

(local (in-theory (disable floor mod)))

(local
 (defthm fn-tcl-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-tcl-expt-256-open
  (implies (posp w)
           (equal (expt 256 w) (* 256 (expt 256 (+ -1 w)))))
  :hints (("Goal" :expand ((expt 256 w)))))

(defthm fn-tcl-expt-256-posp
  (implies (natp k)
           (and (integerp (expt 256 k)) (< 0 (expt 256 k))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable expt))))

(defthm fn-tcl-floor-digit-bound
  (implies (and (natp n) (posp w) (< n (expt 256 w)))
           (< (floor n 256) (expt 256 (+ -1 w))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance fn-tcl-digit-decomposition)))))

(defconst *fn-tcl-max-u16* 65535)
(defconst *fn-tcl-max-u32* 4294967295)
(defconst *fn-tcl-max-u64* 18446744073709551615)
(defconst *fn-tcl-node-id-cap* 1024)
(defconst *fn-tcl-ext-cap* 4096)
(defconst *fn-tcl-magic* '(100 116 110 33))   ; "dtn!"

; -----------------------------------------------------------------------------
; Bounded list vocabulary.  fn-tcl-has walks at most n cells and is the
; decoders' own test: every decoder below asks it before it takes, and
; returns (fn-tcl-parse-need) when it fails, so no decode ever runs past its
; buffer.
;
; fn-tcl-take and fn-tcl-drop are GUARD-TOTAL (guard (natp n), the
; fn-wire-ag-car pattern of books/wire.lisp): their logical definitions are
; unchanged -- (car x) and (cdr x) of an atom are nil, so the two functions
; already had a value past the end of the list -- and the mbe below only
; gives the raw-Lisp code a definition there.  The guard was (fn-tcl-has
; octets n) until w11/tcpcl-outbound, and that is why fn-tcl-outboundp had to
; carry (equal (+ sent-len (len remaining)) total): it was the only fact that
; discharged fn-tcl-pump's take and drop, and checking it cost a walk of the
; unsent suffix on every guarded call into the session machine.  See
; planning/decisions.md D20 and specs/tcpcl.md section 6.  What the old guard
; proved at each call site -- that the take is a genuine prefix -- the
; decoders' keystones still prove: an over-take pads with nil, which is not
; fn-cbor-octet-listp, so fn-tcl-decode-message-yields-message and the round
; trip would both fail.

(defun fn-tcl-has (octets n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (consp octets) (fn-tcl-has (cdr octets) (1- n)))))

(defun fn-tcl-take (n octets)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (mbe :logic (cons (car octets) (fn-tcl-take (1- n) (cdr octets)))
         :exec (if (consp octets)
                   (cons (car octets) (fn-tcl-take (1- n) (cdr octets)))
                 (cons nil (fn-tcl-take (1- n) nil))))))

(defun fn-tcl-drop (n octets)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      octets
    (fn-tcl-drop (1- n) (mbe :logic (cdr octets)
                             :exec (if (consp octets) (cdr octets) nil)))))

(defthm fn-tcl-has-is-len-bound
  (equal (fn-tcl-has octets n) (<= (nfix n) (len octets))))

(defthm fn-tcl-len-take
  (implies (and (natp n) (fn-tcl-has octets n))
           (equal (len (fn-tcl-take n octets)) n)))

(defthm fn-tcl-len-drop
  (implies (and (natp n) (fn-tcl-has octets n))
           (equal (len (fn-tcl-drop n octets)) (- (len octets) n))))

(defthm fn-tcl-len-drop-upper
  (<= (len (fn-tcl-drop n octets)) (len octets))
  :rule-classes :linear)

(defthm fn-tcl-len-drop-lower
  (implies (natp n)
           (<= (- (len octets) n) (len (fn-tcl-drop n octets))))
  :rule-classes :linear)

(defthm fn-tcl-take-0
  (equal (fn-tcl-take 0 octets) nil))

(defthm fn-tcl-drop-0
  (equal (fn-tcl-drop 0 octets) octets))

(local (defthm fn-tcl-append-assoc
         (equal (append (append a b) c) (append a (append b c)))))

; Local: the cons facts the codec proofs need from length arithmetic.  A
; consp rule backchained to len is exactly what section 8 of
; docs/proof-style.md keeps out of an export theory, so none of these leave.
(local (defthm fn-tcl-consp-by-len
         (implies (< 0 (len x)) (consp x))))
(local (defthm fn-tcl-cons-car-cadr-cddr
         (implies (<= 2 (len x))
                  (equal (cons (car x) (cons (car (cdr x)) (cdr (cdr x)))) x))))
(local (defthm fn-tcl-drop-2-cons
         (implies (fn-tcl-has x 2)
                  (equal (cons (car x) (cons (car (cdr x)) (fn-tcl-drop 2 x))) x))
         :hints (("Goal" :expand ((fn-tcl-drop 2 x) (fn-tcl-drop 1 (cdr x))
                                  (fn-tcl-drop 0 (cdr (cdr x))))))))

(defthm fn-tcl-take-drop-reconstruct
  (implies (fn-tcl-has octets n)
           (equal (append (fn-tcl-take n octets) (fn-tcl-drop n octets))
                  octets)))

(defthm fn-tcl-take-append
  (implies (fn-tcl-has left n)
           (equal (fn-tcl-take n (append left right))
                  (fn-tcl-take n left))))

(defthm fn-tcl-drop-append
  (implies (fn-tcl-has left n)
           (equal (fn-tcl-drop n (append left right))
                  (append (fn-tcl-drop n left) right))))

(defthm fn-tcl-take-of-own-prefix
  (implies (and (true-listp a) (equal (len a) (nfix n)))
           (equal (fn-tcl-take n (append a b)) a))
  :hints (("Goal" :induct (fn-tcl-take n a)
           :in-theory (disable fn-tcl-take-append fn-tcl-has-is-len-bound))))

(defthm fn-tcl-take-all
  (implies (and (true-listp a) (natp n) (equal (len a) n))
           (equal (fn-tcl-take n a) a))
  :hints (("Goal" :induct (fn-tcl-take n a)
           :in-theory (disable fn-tcl-has-is-len-bound))))

(defthm fn-tcl-drop-of-own-prefix
  (implies (equal (len a) (nfix n))
           (equal (fn-tcl-drop n (append a b)) b))
  :hints (("Goal" :induct (fn-tcl-drop n a)
           :in-theory (disable fn-tcl-drop-append fn-tcl-has-is-len-bound))))

(defthm fn-tcl-octet-listp-take
  (implies (and (fn-cbor-octet-listp octets) (fn-tcl-has octets n))
           (fn-cbor-octet-listp (fn-tcl-take n octets))))

(defthm fn-tcl-octet-listp-drop
  (implies (fn-cbor-octet-listp octets)
           (fn-cbor-octet-listp (fn-tcl-drop n octets))))

(defthm fn-tcl-octet-listp-append
  (implies (and (fn-cbor-octet-listp left) (fn-cbor-octet-listp right))
           (fn-cbor-octet-listp (append left right))))

(defthm fn-tcl-octet-listp-is-true-listp
  (implies (fn-cbor-octet-listp octets) (true-listp octets)))

(defthm fn-tcl-octet-listp-car
  (implies (and (fn-cbor-octet-listp octets) (consp octets))
           (and (integerp (car octets)) (<= 0 (car octets)) (<= (car octets) 255))))

(defthm fn-tcl-octet-listp-cdr
  (implies (fn-cbor-octet-listp octets) (fn-cbor-octet-listp (cdr octets))))

(defthm fn-tcl-drop-cdr
  (implies (and (natp n) (consp octets))
           (equal (fn-tcl-drop n (cdr octets)) (fn-tcl-drop (+ 1 n) octets))))

(in-theory (disable fn-tcl-drop-cdr))

; -----------------------------------------------------------------------------
; Reversal, and the big-endian codec built on a little-endian core.

(defun fn-tcl-rev-aux (x acc)
  (declare (xargs :guard t))
  (if (consp x) (fn-tcl-rev-aux (cdr x) (cons (car x) acc)) acc))

(defun fn-tcl-rev (x)
  (declare (xargs :guard t))
  (fn-tcl-rev-aux x nil))

(local
 (defthm fn-tcl-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

(defthm fn-tcl-rev-aux-of-rev-aux
  (equal (fn-tcl-rev-aux (fn-tcl-rev-aux x a) b)
         (fn-tcl-rev-aux a (append x b))))

(defthm fn-tcl-len-rev-aux
  (equal (len (fn-tcl-rev-aux x acc)) (+ (len x) (len acc))))

(defthm fn-tcl-octet-listp-rev-aux
  (implies (and (fn-cbor-octet-listp x) (fn-cbor-octet-listp acc))
           (fn-cbor-octet-listp (fn-tcl-rev-aux x acc))))

(defthm fn-tcl-true-listp-rev-aux
  (implies (true-listp acc)
           (true-listp (fn-tcl-rev-aux x acc))))

(defthm fn-tcl-rev-rev
  (implies (true-listp x)
           (equal (fn-tcl-rev (fn-tcl-rev x)) x)))

(defthm fn-tcl-len-rev
  (equal (len (fn-tcl-rev x)) (len x)))

(defthm fn-tcl-octet-listp-rev
  (implies (fn-cbor-octet-listp x)
           (fn-cbor-octet-listp (fn-tcl-rev x))))

(defthm fn-tcl-true-listp-rev
  (true-listp (fn-tcl-rev x)))

(in-theory (disable fn-tcl-rev))

(defun fn-tcl-le-bytes (n width)
  (declare (xargs :guard (and (natp n) (natp width))))
  (if (zp width)
      nil
    (cons (mod n 256) (fn-tcl-le-bytes (floor n 256) (1- width)))))

(defun fn-tcl-le-from (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (if (consp octets)
      (+ (car octets) (* 256 (fn-tcl-le-from (cdr octets))))
    0))

(defun fn-tcl-be-bytes (n width)
  (declare (xargs :guard (and (natp n) (natp width))))
  (fn-tcl-rev (fn-tcl-le-bytes n width)))

(defun fn-tcl-be-from (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (fn-tcl-le-from (fn-tcl-rev octets)))

(defthm fn-tcl-le-bytes-octet-listp
  (implies (natp n)
           (fn-cbor-octet-listp (fn-tcl-le-bytes n width))))

(defthm fn-tcl-len-le-bytes
  (equal (len (fn-tcl-le-bytes n width)) (nfix width)))

(defthm fn-tcl-le-from-bound
  (implies (fn-cbor-octet-listp octets)
           (and (integerp (fn-tcl-le-from octets))
                (<= 0 (fn-tcl-le-from octets))
                (< (fn-tcl-le-from octets) (expt 256 (len octets)))))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary
                  (implies (fn-cbor-octet-listp octets) (natp (fn-tcl-le-from octets))))
                 (:linear :corollary
                  (implies (fn-cbor-octet-listp octets)
                           (< (fn-tcl-le-from octets) (expt 256 (len octets))))))
  :hints (("Goal" :induct (fn-tcl-le-from octets))))

(defthm fn-tcl-le-from-of-le-bytes
  (implies (and (natp n) (natp width) (< n (expt 256 width)))
           (equal (fn-tcl-le-from (fn-tcl-le-bytes n width)) n))
  :hints (("Goal" :induct (fn-tcl-le-bytes n width))
          ("Subgoal *1/2" :use ((:instance fn-tcl-digit-decomposition)))))

(defthm fn-tcl-le-bytes-of-le-from
  (implies (fn-cbor-octet-listp octets)
           (equal (fn-tcl-le-bytes (fn-tcl-le-from octets) (len octets)) octets))
  :hints (("Goal" :induct (fn-tcl-le-from octets))))

(defthm fn-tcl-be-bytes-octet-listp
  (implies (natp n)
           (fn-cbor-octet-listp (fn-tcl-be-bytes n width))))

(defthm fn-tcl-be-bytes-true-listp
  (true-listp (fn-tcl-be-bytes n width)))

(defthm fn-tcl-len-be-bytes
  (equal (len (fn-tcl-be-bytes n width)) (nfix width)))

(in-theory (disable fn-tcl-le-bytes fn-tcl-le-from))

(defthm fn-tcl-be-from-of-be-bytes
  (implies (and (natp n) (natp width) (< n (expt 256 width)))
           (equal (fn-tcl-be-from (fn-tcl-be-bytes n width)) n)))

(defthm fn-tcl-be-bytes-of-be-from
  (implies (fn-cbor-octet-listp octets)
           (equal (fn-tcl-be-bytes (fn-tcl-be-from octets) (len octets)) octets))
  :hints (("Goal" :use ((:instance fn-tcl-le-bytes-of-le-from
                                   (octets (fn-tcl-rev octets)))))))

(defthm fn-tcl-be-from-bound
  (implies (fn-cbor-octet-listp octets)
           (and (integerp (fn-tcl-be-from octets))
                (<= 0 (fn-tcl-be-from octets))
                (< (fn-tcl-be-from octets) (expt 256 (len octets)))))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary
                  (implies (fn-cbor-octet-listp octets) (natp (fn-tcl-be-from octets))))
                 (:linear :corollary
                  (implies (fn-cbor-octet-listp octets)
                           (< (fn-tcl-be-from octets) (expt 256 (len octets))))))
  :hints (("Goal" :use ((:instance fn-tcl-le-from-bound (octets (fn-tcl-rev octets)))))))

(in-theory (disable fn-tcl-be-bytes fn-tcl-be-from))

; Reading a fixed-width field: the value of the first `width` octets.
(defun fn-tcl-uint (width octets)
  (declare (xargs :guard (and (natp width) (fn-cbor-octet-listp octets)
                              (fn-tcl-has octets width))))
  (fn-tcl-be-from (fn-tcl-take width octets)))

(defthm fn-tcl-uint-bound
  (implies (and (fn-cbor-octet-listp octets) (natp width) (fn-tcl-has octets width))
           (and (integerp (fn-tcl-uint width octets))
                (rationalp (fn-tcl-uint width octets))
                (acl2-numberp (fn-tcl-uint width octets))
                (<= 0 (fn-tcl-uint width octets))
                (< (fn-tcl-uint width octets) (expt 256 width))))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                  (implies (and (fn-cbor-octet-listp octets) (natp width)
                                (fn-tcl-has octets width))
                           (and (<= 0 (fn-tcl-uint width octets))
                                (< (fn-tcl-uint width octets) (expt 256 width))))))
  :hints (("Goal" :use ((:instance fn-tcl-be-from-bound
                                   (octets (fn-tcl-take width octets))))
           ; The used instance must survive as literals: the rewrite form of
           ; fn-tcl-be-from-bound rewrites its integerp literal to T and drops
           ; it, and type-set cannot relieve the type-prescription's hypothesis.
           :in-theory (disable fn-tcl-be-from-bound))))

(defthm fn-tcl-uint-of-be-bytes
  (implies (and (natp n) (natp width) (< n (expt 256 width)))
           (equal (fn-tcl-uint width (fn-tcl-be-bytes n width)) n)))

(defthm fn-tcl-uint-of-own-prefix
  (implies (and (natp n) (natp width) (< n (expt 256 width)))
           (equal (fn-tcl-uint width (append (fn-tcl-be-bytes n width) rest)) n)))

(defthm fn-tcl-be-bytes-of-uint
  (implies (and (fn-cbor-octet-listp octets) (natp width) (fn-tcl-has octets width))
           (equal (fn-tcl-be-bytes (fn-tcl-uint width octets) width)
                  (fn-tcl-take width octets)))
  :hints (("Goal" :use ((:instance fn-tcl-be-bytes-of-be-from
                                   (octets (fn-tcl-take width octets))))
           :in-theory (disable fn-tcl-be-bytes-of-be-from))))

(defthm fn-tcl-uint-append
  (implies (fn-tcl-has left width)
           (equal (fn-tcl-uint width (append left right))
                  (fn-tcl-uint width left))))

(in-theory (disable fn-tcl-uint))

; The bounds at the three widths the grammar uses, with the modulus
; evaluated: a linear rule keeps (expt 256 width) symbolic.  The bound rule
; is off during each proof so the used integerp fact is not rewritten away
; before linear arithmetic tightens the strict bound.
(defthm fn-tcl-uint-1-bound
  (implies (and (fn-cbor-octet-listp octets) (fn-tcl-has octets 1))
           (<= (fn-tcl-uint 1 octets) 255))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance fn-tcl-uint-bound (width 1)))
           :in-theory (disable fn-tcl-uint-bound))))

(defthm fn-tcl-uint-2-bound
  (implies (and (fn-cbor-octet-listp octets) (fn-tcl-has octets 2))
           (<= (fn-tcl-uint 2 octets) 65535))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance fn-tcl-uint-bound (width 2)))
           :in-theory (disable fn-tcl-uint-bound))))

(defthm fn-tcl-uint-4-bound
  (implies (and (fn-cbor-octet-listp octets) (fn-tcl-has octets 4))
           (<= (fn-tcl-uint 4 octets) 4294967295))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance fn-tcl-uint-bound (width 4)))
           :in-theory (disable fn-tcl-uint-bound))))

(defthm fn-tcl-uint-8-bound
  (implies (and (fn-cbor-octet-listp octets) (fn-tcl-has octets 8))
           (<= (fn-tcl-uint 8 octets) 18446744073709551615))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance fn-tcl-uint-bound (width 8)))
           :in-theory (disable fn-tcl-uint-bound))))

; A ground (fn-tcl-be-bytes 0 2) must stay a term, not become '(0 0): the
; prefix rules above are stated over the constructor.
(local (in-theory (disable (:e fn-tcl-be-bytes) (:e fn-tcl-le-bytes) (:e fn-tcl-rev))))

; -----------------------------------------------------------------------------
; Extension items (sections 4.8 and 5.2.5): flags:U8 type:U16 length:U16 value.

(defun fn-tcl-item-listp (items)
  (declare (xargs :guard t))
  (if (consp items)
      (and (fn-tcl-item-shapep (car items))
           (fn-cbor-octetp (fn-tcl-item-flags (car items)))
           (natp (fn-tcl-item-type (car items)))
           (<= (fn-tcl-item-type (car items)) *fn-tcl-max-u16*)
           (fn-cbor-octet-listp (fn-tcl-item-value (car items)))
           (<= (len (fn-tcl-item-value (car items))) *fn-tcl-max-u16*)
           (fn-tcl-item-listp (cdr items)))
    (null items)))

; A shaped item is its constructor applied to its accessors: the one
; place the record is opened, for the item round trip below.
(defthm fn-tcl-make-item-of-accessors
  (implies (fn-tcl-item-shapep x)
           (equal (fn-tcl-make-item (fn-tcl-item-flags x) (fn-tcl-item-type x)
                                    (fn-tcl-item-value x))
                  x))
  :hints (("Goal" :in-theory (enable fn-tcl-item-shapep fn-tcl-make-item fn-tcl-item-flags
                                     fn-tcl-item-type fn-tcl-item-value)
           :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
                    (len (cddddr x))
                    (true-listp x) (true-listp (cdr x)) (true-listp (cddr x))
                    (true-listp (cdddr x)) (true-listp (cddddr x))))))

; The same fact with the fields as free variables, so it applies after one
; of them has been simplified (a nil value, say) in the round-trip proof.
(local (defthm fn-tcl-make-item-of-accessors-free
         (implies (and (fn-tcl-item-shapep x)
                       (equal f (fn-tcl-item-flags x))
                       (equal ty (fn-tcl-item-type x))
                       (equal v (fn-tcl-item-value x)))
                  (equal (fn-tcl-make-item f ty v) x))))

(defun fn-tcl-encode-items (items)
  (declare (xargs :guard (fn-tcl-item-listp items)))
  (if (consp items)
      (append (list (fn-tcl-item-flags (car items)))
              (fn-tcl-be-bytes (fn-tcl-item-type (car items)) 2)
              (fn-tcl-be-bytes (len (fn-tcl-item-value (car items))) 2)
              (fn-tcl-item-value (car items))
              (fn-tcl-encode-items (cdr items)))
    nil))

; Parse a list of items that must exactly fill `octets`.  Returns
; (fn-tcl-parse-ok items nil) or (fn-tcl-parse-error :extension-items).
(defun fn-tcl-decode-items (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :measure (len octets)))
  (if (not (consp octets))
      (fn-tcl-parse-ok nil nil)
    (if (not (fn-tcl-has octets 5))
        (fn-tcl-parse-error :extension-items)
      (let* ((flags (car octets))
             (type (fn-tcl-uint 2 (cdr octets)))
             (vlen (fn-tcl-uint 2 (fn-tcl-drop 2 (cdr octets))))
             (body (fn-tcl-drop 2 (fn-tcl-drop 2 (cdr octets)))))
        (if (not (fn-tcl-has body vlen))
            (fn-tcl-parse-error :extension-items)
          (let ((rest (fn-tcl-decode-items (fn-tcl-drop vlen body))))
            (if (not (fn-tcl-parse-okp rest))
                rest
              (fn-tcl-parse-ok (cons (fn-tcl-make-item flags type (fn-tcl-take vlen body))
                                     (fn-tcl-parse-msg rest))
                               nil))))))))

(defthm fn-tcl-encode-items-octet-listp
  (implies (fn-tcl-item-listp items)
           (fn-cbor-octet-listp (fn-tcl-encode-items items))))

(defthm fn-tcl-encode-items-true-listp
  (true-listp (fn-tcl-encode-items items)))

(defthm fn-tcl-decode-items-of-encode-items
  (implies (fn-tcl-item-listp items)
           (equal (fn-tcl-decode-items (fn-tcl-encode-items items))
                  (fn-tcl-parse-ok items nil)))
  :hints (("Goal" :induct (fn-tcl-item-listp items))))

(defthm fn-tcl-decode-items-yields-items
  (implies (and (fn-cbor-octet-listp octets)
                (fn-tcl-parse-okp (fn-tcl-decode-items octets)))
           (fn-tcl-item-listp (fn-tcl-parse-msg (fn-tcl-decode-items octets))))
  :hints (("Goal" :induct (fn-tcl-decode-items octets))))

(defthm fn-tcl-accepted-items-are-canonical
  (implies (and (fn-cbor-octet-listp octets)
                (fn-tcl-parse-okp (fn-tcl-decode-items octets)))
           (equal (fn-tcl-encode-items (fn-tcl-parse-msg (fn-tcl-decode-items octets)))
                  octets))
  :hints (("Goal" :induct (fn-tcl-decode-items octets))))

(defthm fn-tcl-encode-items-nil
  (equal (fn-tcl-encode-items nil) nil))

(defthm fn-tcl-decode-items-nil
  (equal (fn-tcl-decode-items nil) (fn-tcl-parse-ok nil nil)))

(defthm fn-tcl-decode-items-rest-is-nil
  (implies (fn-tcl-parse-okp (fn-tcl-decode-items octets))
           (equal (fn-tcl-parse-rest (fn-tcl-decode-items octets)) nil))
  :hints (("Goal" :induct (fn-tcl-decode-items octets))))

(in-theory (disable fn-tcl-decode-items fn-tcl-encode-items))

; -----------------------------------------------------------------------------
; Flag predicates.  Reserved bits are ignored here, as section 4.2 and
; Table 5, 8 require of a receiver; the codec keeps them.

(defun fn-tcl-flag-end (flags)
  (declare (xargs :guard (fn-cbor-octetp flags)))
  (logbitp 0 flags))

(defun fn-tcl-flag-start (flags)
  (declare (xargs :guard (fn-cbor-octetp flags)))
  (logbitp 1 flags))

(defun fn-tcl-flag-reply (flags)
  (declare (xargs :guard (fn-cbor-octetp flags)))
  (logbitp 0 flags))

(defun fn-tcl-flag-can-tls (flags)
  (declare (xargs :guard (fn-cbor-octetp flags)))
  (logbitp 0 flags))

(defun fn-tcl-flag-critical (flags)
  (declare (xargs :guard (fn-cbor-octetp flags)))
  (logbitp 0 flags))

; -----------------------------------------------------------------------------
; Message well-formedness, relative to the segment MRU under which a segment
; is acceptable.

(defun fn-tcl-messagep (m segment-mru)
  (declare (xargs :guard (natp segment-mru)))
  (let ((kind (fn-tcl-msg-kind m)))
    (cond ((equal kind :contact)
           (and (fn-tcl-contact-shapep m)
                (fn-cbor-octetp (fn-tcl-contact-version m))
                (fn-cbor-octetp (fn-tcl-contact-flags m))))
          ((equal kind :sess-init)
           (and (fn-tcl-sess-init-shapep m)
                (natp (fn-tcl-sess-init-keepalive m))
                (<= (fn-tcl-sess-init-keepalive m) *fn-tcl-max-u16*)
                (natp (fn-tcl-sess-init-segment-mru m))
                (<= (fn-tcl-sess-init-segment-mru m) *fn-tcl-max-u64*)
                (natp (fn-tcl-sess-init-transfer-mru m))
                (<= (fn-tcl-sess-init-transfer-mru m) *fn-tcl-max-u64*)
                (fn-cbor-octet-listp (fn-tcl-sess-init-node-id m))
                (<= (len (fn-tcl-sess-init-node-id m)) *fn-tcl-node-id-cap*)
                (fn-tcl-item-listp (fn-tcl-sess-init-ext m))
                (<= (len (fn-tcl-encode-items (fn-tcl-sess-init-ext m))) *fn-tcl-ext-cap*)))
          ((equal kind :xfer-segment)
           (and (fn-tcl-xfer-segment-shapep m)
                (fn-cbor-octetp (fn-tcl-xfer-segment-flags m))
                (natp (fn-tcl-xfer-segment-xfer-id m))
                (<= (fn-tcl-xfer-segment-xfer-id m) *fn-tcl-max-u64*)
                (fn-tcl-item-listp (fn-tcl-xfer-segment-ext m))
                (<= (len (fn-tcl-encode-items (fn-tcl-xfer-segment-ext m))) *fn-tcl-ext-cap*)
                (or (fn-tcl-flag-start (fn-tcl-xfer-segment-flags m))
                    (null (fn-tcl-xfer-segment-ext m)))
                (fn-cbor-octet-listp (fn-tcl-xfer-segment-data m))
                (<= (len (fn-tcl-xfer-segment-data m)) segment-mru)
                (<= segment-mru *fn-tcl-max-u64*)))
          ((equal kind :xfer-ack)
           (and (fn-tcl-xfer-ack-shapep m)
                (fn-cbor-octetp (fn-tcl-xfer-ack-flags m))
                (natp (fn-tcl-xfer-ack-xfer-id m))
                (<= (fn-tcl-xfer-ack-xfer-id m) *fn-tcl-max-u64*)
                (natp (fn-tcl-xfer-ack-acked-len m))
                (<= (fn-tcl-xfer-ack-acked-len m) *fn-tcl-max-u64*)))
          ((equal kind :xfer-refuse)
           (and (fn-tcl-xfer-refuse-shapep m)
                (fn-cbor-octetp (fn-tcl-xfer-refuse-reason m))
                (natp (fn-tcl-xfer-refuse-xfer-id m))
                (<= (fn-tcl-xfer-refuse-xfer-id m) *fn-tcl-max-u64*)))
          ((equal kind :keepalive) (fn-tcl-keepalive-shapep m))
          ((equal kind :sess-term)
           (and (fn-tcl-sess-term-shapep m)
                (fn-cbor-octetp (fn-tcl-sess-term-flags m))
                (fn-cbor-octetp (fn-tcl-sess-term-reason m))))
          ((equal kind :msg-reject)
           (and (fn-tcl-msg-reject-shapep m)
                (fn-cbor-octetp (fn-tcl-msg-reject-reason m))
                (fn-cbor-octetp (fn-tcl-msg-reject-header m))))
          (t nil))))

; -----------------------------------------------------------------------------
; Encoder.  One body encoder per message kind after the type octet; the
; Contact Header has no type octet.  A message that is not fn-tcl-messagep
; encodes to nil.

(defun fn-tcl-encode-init-body (m)
  (declare (xargs :guard (and (fn-tcl-messagep m *fn-tcl-max-u64*)
                              (equal (fn-tcl-msg-kind m) :sess-init))
                  :verify-guards nil))
  (let ((ext (fn-tcl-encode-items (fn-tcl-sess-init-ext m))))
    (append (fn-tcl-be-bytes (fn-tcl-sess-init-keepalive m) 2)
            (fn-tcl-be-bytes (fn-tcl-sess-init-segment-mru m) 8)
            (fn-tcl-be-bytes (fn-tcl-sess-init-transfer-mru m) 8)
            (fn-tcl-be-bytes (len (fn-tcl-sess-init-node-id m)) 2)
            (fn-tcl-sess-init-node-id m)
            (fn-tcl-be-bytes (len ext) 4)
            ext)))

(defun fn-tcl-encode-segment-body (m)
  (declare (xargs :guard (and (fn-tcl-messagep m *fn-tcl-max-u64*)
                              (equal (fn-tcl-msg-kind m) :xfer-segment))
                  :verify-guards nil))
  (let ((ext (fn-tcl-encode-items (fn-tcl-xfer-segment-ext m))))
    (cons (fn-tcl-xfer-segment-flags m)
          (append (fn-tcl-be-bytes (fn-tcl-xfer-segment-xfer-id m) 8)
                  (if (fn-tcl-flag-start (fn-tcl-xfer-segment-flags m))
                      (append (fn-tcl-be-bytes (len ext) 4) ext)
                    nil)
                  (fn-tcl-be-bytes (len (fn-tcl-xfer-segment-data m)) 8)
                  (fn-tcl-xfer-segment-data m)))))

(defun fn-tcl-encode-ack-body (m)
  (declare (xargs :guard (and (fn-tcl-messagep m *fn-tcl-max-u64*)
                              (equal (fn-tcl-msg-kind m) :xfer-ack))
                  :verify-guards nil))
  (cons (fn-tcl-xfer-ack-flags m)
        (append (fn-tcl-be-bytes (fn-tcl-xfer-ack-xfer-id m) 8)
                (fn-tcl-be-bytes (fn-tcl-xfer-ack-acked-len m) 8))))

(defun fn-tcl-encode-refuse-body (m)
  (declare (xargs :guard (and (fn-tcl-messagep m *fn-tcl-max-u64*)
                              (equal (fn-tcl-msg-kind m) :xfer-refuse))
                  :verify-guards nil))
  (cons (fn-tcl-xfer-refuse-reason m)
        (fn-tcl-be-bytes (fn-tcl-xfer-refuse-xfer-id m) 8)))

(defun fn-tcl-encode-term-body (m)
  (declare (xargs :guard t))
  (list (fn-tcl-sess-term-flags m) (fn-tcl-sess-term-reason m)))

(defun fn-tcl-encode-reject-body (m)
  (declare (xargs :guard t))
  (list (fn-tcl-msg-reject-reason m) (fn-tcl-msg-reject-header m)))

(defun fn-tcl-encode (m)
  (declare (xargs :guard (fn-tcl-messagep m *fn-tcl-max-u64*) :verify-guards nil))
  (let ((kind (fn-tcl-msg-kind m)))
    (cond ((equal kind :contact)
           (append *fn-tcl-magic*
                   (fn-tcl-be-bytes (fn-tcl-contact-version m) 1)
                   (fn-tcl-be-bytes (fn-tcl-contact-flags m) 1)))
          ((equal kind :sess-init) (cons 7 (fn-tcl-encode-init-body m)))
          ((equal kind :xfer-segment) (cons 1 (fn-tcl-encode-segment-body m)))
          ((equal kind :xfer-ack) (cons 2 (fn-tcl-encode-ack-body m)))
          ((equal kind :xfer-refuse) (cons 3 (fn-tcl-encode-refuse-body m)))
          ((equal kind :keepalive) (list 4))
          ((equal kind :sess-term) (cons 5 (fn-tcl-encode-term-body m)))
          ((equal kind :msg-reject) (cons 6 (fn-tcl-encode-reject-body m)))
          (t nil))))

(verify-guards fn-tcl-encode-init-body
  :hints (("Goal" :in-theory (enable fn-tcl-messagep))))
(verify-guards fn-tcl-encode-segment-body
  :hints (("Goal" :in-theory (enable fn-tcl-messagep))))
(verify-guards fn-tcl-encode-ack-body
  :hints (("Goal" :in-theory (enable fn-tcl-messagep))))
(verify-guards fn-tcl-encode-refuse-body
  :hints (("Goal" :in-theory (enable fn-tcl-messagep))))
(verify-guards fn-tcl-encode
  :hints (("Goal" :in-theory (enable fn-tcl-messagep))))

; -----------------------------------------------------------------------------
; Decoders.  Each `fn-tcl-has` test precedes the read it guards, and each
; length field is compared with its cap before the take it sizes.

(defun fn-tcl-decode-contact (buf)
  (declare (xargs :guard (fn-cbor-octet-listp buf)
                  :verify-guards nil))
  (if (not (fn-tcl-has buf 6))
      (fn-tcl-parse-need)
    (if (not (equal (fn-tcl-take 4 buf) *fn-tcl-magic*))
        (fn-tcl-parse-error :magic)
      (let* ((tail (fn-tcl-drop 4 buf))
             (after-version (fn-tcl-drop 1 tail)))
        (fn-tcl-parse-ok (fn-tcl-make-contact (fn-tcl-uint 1 tail)
                                              (fn-tcl-uint 1 after-version))
                         (fn-tcl-drop 1 after-version))))))

(defun fn-tcl-decode-segment-data (flags xfer-id ext buf segment-mru)
  (declare (xargs :guard (and (fn-cbor-octet-listp buf) (natp segment-mru))
                  :verify-guards nil))
  (if (not (fn-tcl-has buf 8))
      (fn-tcl-parse-need)
    (let ((data-len (fn-tcl-uint 8 buf))
          (after (fn-tcl-drop 8 buf)))
      (if (< segment-mru data-len)
          (fn-tcl-parse-error :segment-exceeds-mru)
        (if (not (fn-tcl-has after data-len))
            (fn-tcl-parse-need)
          (fn-tcl-parse-ok (fn-tcl-make-xfer-segment flags xfer-id ext
                                                     (fn-tcl-take data-len after))
                           (fn-tcl-drop data-len after)))))))

(defun fn-tcl-decode-segment (body segment-mru)
  (declare (xargs :guard (and (fn-cbor-octet-listp body) (natp segment-mru))
                  :verify-guards nil))
  (if (not (fn-tcl-has body 9))
      (fn-tcl-parse-need)
    (let* ((flags (car body))
           (xfer-id (fn-tcl-uint 8 (cdr body)))
           (after-id (fn-tcl-drop 8 (cdr body))))
      (if (not (fn-tcl-flag-start flags))
          (fn-tcl-decode-segment-data flags xfer-id nil after-id segment-mru)
        (if (not (fn-tcl-has after-id 4))
            (fn-tcl-parse-need)
          (let ((ext-len (fn-tcl-uint 4 after-id))
                (after-len (fn-tcl-drop 4 after-id)))
            (if (< *fn-tcl-ext-cap* ext-len)
                (fn-tcl-parse-error :extension-length)
              (if (not (fn-tcl-has after-len ext-len))
                  (fn-tcl-parse-need)
                (let ((items (fn-tcl-decode-items (fn-tcl-take ext-len after-len))))
                  (if (not (fn-tcl-parse-okp items))
                      (fn-tcl-parse-error :extension-items)
                    (fn-tcl-decode-segment-data flags xfer-id (fn-tcl-parse-msg items)
                                                (fn-tcl-drop ext-len after-len)
                                                segment-mru)))))))))))

(defun fn-tcl-decode-init (body)
  (declare (xargs :guard (fn-cbor-octet-listp body)
                  :verify-guards nil))
  (if (not (fn-tcl-has body 20))
      (fn-tcl-parse-need)
    (let* ((keepalive (fn-tcl-uint 2 body))
           (after-ka (fn-tcl-drop 2 body))
           (segment-mru (fn-tcl-uint 8 after-ka))
           (after-seg (fn-tcl-drop 8 after-ka))
           (transfer-mru (fn-tcl-uint 8 after-seg))
           (after-xfer (fn-tcl-drop 8 after-seg))
           (nid-len (fn-tcl-uint 2 after-xfer))
           (after-nl (fn-tcl-drop 2 after-xfer)))
      (if (< *fn-tcl-node-id-cap* nid-len)
          (fn-tcl-parse-error :node-id-length)
        (if (not (fn-tcl-has after-nl nid-len))
            (fn-tcl-parse-need)
          (let ((node-id (fn-tcl-take nid-len after-nl))
                (after-nid (fn-tcl-drop nid-len after-nl)))
            (if (not (fn-tcl-has after-nid 4))
                (fn-tcl-parse-need)
              (let ((ext-len (fn-tcl-uint 4 after-nid))
                    (after-len (fn-tcl-drop 4 after-nid)))
                (if (< *fn-tcl-ext-cap* ext-len)
                    (fn-tcl-parse-error :extension-length)
                  (if (not (fn-tcl-has after-len ext-len))
                      (fn-tcl-parse-need)
                    (let ((items (fn-tcl-decode-items (fn-tcl-take ext-len after-len))))
                      (if (not (fn-tcl-parse-okp items))
                          (fn-tcl-parse-error :extension-items)
                        (fn-tcl-parse-ok (fn-tcl-make-sess-init keepalive segment-mru
                                                                transfer-mru node-id
                                                                (fn-tcl-parse-msg items))
                                         (fn-tcl-drop ext-len after-len))))))))))))))

(defun fn-tcl-decode-ack (body)
  (declare (xargs :guard (fn-cbor-octet-listp body)
                  :verify-guards nil))
  (if (not (fn-tcl-has body 17))
      (fn-tcl-parse-need)
    (fn-tcl-parse-ok (fn-tcl-make-xfer-ack (car body)
                                           (fn-tcl-uint 8 (cdr body))
                                           (fn-tcl-uint 8 (fn-tcl-drop 8 (cdr body))))
                     (fn-tcl-drop 8 (fn-tcl-drop 8 (cdr body))))))

(defun fn-tcl-decode-refuse (body)
  (declare (xargs :guard (fn-cbor-octet-listp body)
                  :verify-guards nil))
  (if (not (fn-tcl-has body 9))
      (fn-tcl-parse-need)
    (fn-tcl-parse-ok (fn-tcl-make-xfer-refuse (car body) (fn-tcl-uint 8 (cdr body)))
                     (fn-tcl-drop 8 (cdr body)))))

(defun fn-tcl-decode-term (body)
  (declare (xargs :guard (fn-cbor-octet-listp body)
                  :verify-guards nil))
  (if (not (fn-tcl-has body 2))
      (fn-tcl-parse-need)
    (fn-tcl-parse-ok (fn-tcl-make-sess-term (car body) (car (cdr body)))
                     (cdr (cdr body)))))

(defun fn-tcl-decode-reject (body)
  (declare (xargs :guard (fn-cbor-octet-listp body)
                  :verify-guards nil))
  (if (not (fn-tcl-has body 2))
      (fn-tcl-parse-need)
    (fn-tcl-parse-ok (fn-tcl-make-msg-reject (car body) (car (cdr body)))
                     (cdr (cdr body)))))

; One message after the contact exchange (section 4.5).  An unknown type is
; an error carrying the offending header octet, so the session can echo it in
; MSG_REJECT before closing.
(defun fn-tcl-decode-message (buf segment-mru)
  (declare (xargs :guard (and (fn-cbor-octet-listp buf) (natp segment-mru))
                  :verify-guards nil))
  (if (not (consp buf))
      (fn-tcl-parse-need)
    (let ((type (car buf)) (body (cdr buf)))
      (cond ((equal type 1) (fn-tcl-decode-segment body segment-mru))
            ((equal type 2) (fn-tcl-decode-ack body))
            ((equal type 3) (fn-tcl-decode-refuse body))
            ((equal type 4) (fn-tcl-parse-ok (fn-tcl-make-keepalive) body))
            ((equal type 5) (fn-tcl-decode-term body))
            ((equal type 6) (fn-tcl-decode-reject body))
            ((equal type 7) (fn-tcl-decode-init body))
            (t (fn-tcl-parse-error (list :unknown-type type)))))))

; The largest buffer a `need` can leave behind: the SESS_INIT fixed fields
; with a maximal node ID and extension list, plus the segment overhead and
; the segment MRU.  Loose, and stated with its slack in specs/tcpcl.md.
(defun fn-tcl-max-message (segment-mru)
  (declare (xargs :guard (natp segment-mru)))
  (+ 5145 segment-mru))

; -----------------------------------------------------------------------------
; Codec keystones, one block per decoder (GENERATED by the lane's
; gen_keystones.py; edit the generator).  Each block: round trip of a
; well-formed message followed by anything; canonicality of every accepted
; octet string over arbitrary input; the decoded kind; well-formedness of
; the decoded record; prefix determinism of the ok and error outcomes (what
; the partition theorem needs); consumption and typing of the rest; the
; three outcomes exhaustive and exclusive; the need bound.  The
; message-level keystones after them dispatch on the type octet with the
; sub-decoders opaque.

(local (defthm fn-tcl-take-4-magic
         (equal (fn-tcl-take 4 (list* 100 116 110 33 x)) '(100 116 110 33))))
(local (defthm fn-tcl-drop-4-magic
         (equal (fn-tcl-drop 4 (list* 100 116 110 33 x)) x)))

(local (in-theory (disable fn-tcl-take fn-tcl-drop fn-tcl-has
                           fn-tcl-flag-end fn-tcl-flag-start fn-tcl-flag-reply
                           fn-tcl-flag-can-tls fn-tcl-flag-critical)))

; --- Contact Header.

(defthm fn-tcl-decode-contact-of-encode
  (implies (and (fn-cbor-octetp version) (fn-cbor-octetp flags))
           (equal (fn-tcl-decode-contact
                   (append (fn-tcl-encode (fn-tcl-make-contact version flags)) rest))
                  (fn-tcl-parse-ok (fn-tcl-make-contact version flags) rest)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-accepted-contact-is-canonical
  (implies (and (fn-cbor-octet-listp buf)
                (fn-tcl-parse-okp (fn-tcl-decode-contact buf)))
           (equal (append (fn-tcl-encode (fn-tcl-parse-msg (fn-tcl-decode-contact buf)))
                          (fn-tcl-parse-rest (fn-tcl-decode-contact buf)))
                  buf))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-tcl-take-drop-reconstruct (n 4) (octets buf))))))

(defthm fn-tcl-decode-contact-kind
  (implies (and (fn-cbor-octet-listp buf) (fn-tcl-parse-okp (fn-tcl-decode-contact buf)))
           (equal (fn-tcl-msg-kind (fn-tcl-parse-msg (fn-tcl-decode-contact buf))) :contact))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-contact-yields-message
  (implies (and (fn-cbor-octet-listp buf)
                (fn-tcl-parse-okp (fn-tcl-decode-contact buf)))
           (fn-tcl-messagep (fn-tcl-parse-msg (fn-tcl-decode-contact buf)) mru))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-contact-append-ok
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-okp (fn-tcl-decode-contact left)))
           (equal (fn-tcl-decode-contact (append left right))
                  (fn-tcl-parse-ok (fn-tcl-parse-msg (fn-tcl-decode-contact left))
                                   (append (fn-tcl-parse-rest (fn-tcl-decode-contact left))
                                           right))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-contact-append-error
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-errorp (fn-tcl-decode-contact left)))
           (equal (fn-tcl-decode-contact (append left right))
                  (fn-tcl-decode-contact left)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-contact-consumes
  (implies (fn-tcl-parse-okp (fn-tcl-decode-contact buf))
           (< (len (fn-tcl-parse-rest (fn-tcl-decode-contact buf))) (len buf)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-contact-rest-octet-listp
  (implies (and (fn-cbor-octet-listp buf)
                (fn-tcl-parse-okp (fn-tcl-decode-contact buf)))
           (fn-cbor-octet-listp (fn-tcl-parse-rest (fn-tcl-decode-contact buf))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-contact-outcomes
  (implies (fn-cbor-octet-listp buf)
  (and (implies (and (not (fn-tcl-parse-okp (fn-tcl-decode-contact buf)))
                     (not (fn-tcl-parse-needp (fn-tcl-decode-contact buf))))
                (fn-tcl-parse-errorp (fn-tcl-decode-contact buf)))
       (implies (fn-tcl-parse-okp (fn-tcl-decode-contact buf))
                (and (not (fn-tcl-parse-needp (fn-tcl-decode-contact buf)))
                     (not (fn-tcl-parse-errorp (fn-tcl-decode-contact buf)))))
       (implies (fn-tcl-parse-needp (fn-tcl-decode-contact buf))
                (not (fn-tcl-parse-errorp (fn-tcl-decode-contact buf))))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-need-means-short-buffer-contact
  (implies (fn-tcl-parse-needp (fn-tcl-decode-contact buf))
           (< (len buf) 6))
  :hints (("Goal" :do-not-induct t)))

; --- XFER_SEGMENT data part: the length field and the data, kept opaque
; in the segment block so the segment case split stays small.

(defthm fn-tcl-decode-segment-data-of-encode
  (implies (and (fn-cbor-octet-listp data) (<= (len data) mru)
                (<= mru *fn-tcl-max-u64*))
           (equal (fn-tcl-decode-segment-data
                   flags xfer-id ext
                   (append (fn-tcl-be-bytes (len data) 8) (append data rest)) mru)
                  (fn-tcl-parse-ok (fn-tcl-make-xfer-segment flags xfer-id ext data) rest)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-segment-data-fields
  (implies (and (fn-cbor-octet-listp buf)
                (fn-tcl-parse-okp (fn-tcl-decode-segment-data flags xfer-id ext buf mru)))
           (let ((m (fn-tcl-parse-msg (fn-tcl-decode-segment-data flags xfer-id ext buf mru))))
             (and (fn-tcl-xfer-segment-shapep m)
                  (equal (fn-tcl-msg-kind m) :xfer-segment)
                  (equal (fn-tcl-xfer-segment-flags m) flags)
                  (equal (fn-tcl-xfer-segment-xfer-id m) xfer-id)
                  (equal (fn-tcl-xfer-segment-ext m) ext)
                  (fn-cbor-octet-listp (fn-tcl-xfer-segment-data m))
                  (<= (len (fn-tcl-xfer-segment-data m)) mru))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-segment-data-canonical
  (implies (and (fn-cbor-octet-listp buf)
                (fn-tcl-parse-okp (fn-tcl-decode-segment-data flags xfer-id ext buf mru)))
           (equal (append (fn-tcl-be-bytes
                           (len (fn-tcl-xfer-segment-data
                                 (fn-tcl-parse-msg
                                  (fn-tcl-decode-segment-data flags xfer-id ext buf mru))))
                           8)
                          (append (fn-tcl-xfer-segment-data
                                   (fn-tcl-parse-msg
                                    (fn-tcl-decode-segment-data flags xfer-id ext buf mru)))
                                  (fn-tcl-parse-rest
                                   (fn-tcl-decode-segment-data flags xfer-id ext buf mru))))
                  buf))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-segment-data-append-ok
  (implies (and (fn-cbor-octet-listp left)
                (fn-tcl-parse-okp (fn-tcl-decode-segment-data flags xfer-id ext left mru)))
           (equal (fn-tcl-decode-segment-data flags xfer-id ext (append left right) mru)
                  (fn-tcl-parse-ok
                   (fn-tcl-parse-msg (fn-tcl-decode-segment-data flags xfer-id ext left mru))
                   (append (fn-tcl-parse-rest
                            (fn-tcl-decode-segment-data flags xfer-id ext left mru))
                           right))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-segment-data-append-error
  (implies (and (fn-cbor-octet-listp left)
                (fn-tcl-parse-errorp (fn-tcl-decode-segment-data flags xfer-id ext left mru)))
           (equal (fn-tcl-decode-segment-data flags xfer-id ext (append left right) mru)
                  (fn-tcl-decode-segment-data flags xfer-id ext left mru)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-segment-data-consumes
  (implies (fn-tcl-parse-okp (fn-tcl-decode-segment-data flags xfer-id ext buf mru))
           (<= (len (fn-tcl-parse-rest (fn-tcl-decode-segment-data flags xfer-id ext buf mru)))
               (len buf)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-segment-data-rest-octet-listp
  (implies (and (fn-cbor-octet-listp buf)
                (fn-tcl-parse-okp (fn-tcl-decode-segment-data flags xfer-id ext buf mru)))
           (fn-cbor-octet-listp
            (fn-tcl-parse-rest (fn-tcl-decode-segment-data flags xfer-id ext buf mru))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-segment-data-outcomes
  (implies (fn-cbor-octet-listp buf)
  (and (implies (and (not (fn-tcl-parse-okp (fn-tcl-decode-segment-data flags xfer-id ext buf mru)))
                     (not (fn-tcl-parse-needp (fn-tcl-decode-segment-data flags xfer-id ext buf mru))))
                (fn-tcl-parse-errorp (fn-tcl-decode-segment-data flags xfer-id ext buf mru)))
       (implies (fn-tcl-parse-okp (fn-tcl-decode-segment-data flags xfer-id ext buf mru))
                (and (not (fn-tcl-parse-needp
                           (fn-tcl-decode-segment-data flags xfer-id ext buf mru)))
                     (not (fn-tcl-parse-errorp
                           (fn-tcl-decode-segment-data flags xfer-id ext buf mru)))))
       (implies (fn-tcl-parse-needp (fn-tcl-decode-segment-data flags xfer-id ext buf mru))
                (not (fn-tcl-parse-errorp
                      (fn-tcl-decode-segment-data flags xfer-id ext buf mru))))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-segment-data-need-short
  (implies (and (fn-cbor-octet-listp buf) (natp mru)
                (fn-tcl-parse-needp (fn-tcl-decode-segment-data flags xfer-id ext buf mru)))
           (< (len buf) (+ 8 mru)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-segment-never-exceeds-mru
  (implies (and (fn-tcl-has buf 8) (< mru (fn-tcl-uint 8 buf)))
           (equal (fn-tcl-decode-segment-data flags xfer-id ext buf mru)
                  (fn-tcl-parse-error :segment-exceeds-mru)))
  :hints (("Goal" :do-not-induct t)))

; --- len stays closed from here to the end of the book.  Under
; fn-tcl-has-is-len-bound a decoder's has-check is a len bound, and
; fn-tcl-consp-by-len then reopens the definition of len on every cdr under
; the decoder's case split: measured at 406 s and 2.6e8 prover steps for
; fn-tcl-decode-term-yields-message (build/acl2/certify-20260919T234310Z-5770),
; and the same unrolling took the SESS_INIT and XFER_SEGMENT blocks below to
; 20 s and 135 s in a session of 2026-09-23
; (planning/evidence/chain-remainder-cost-2026-09-23.md).  The two rules
; below are the only way from a len bound to a cons fact, and each strips
; one cdr, so the chain is bounded by the layout.
(local (defthm fn-tcl-len-of-cons
         (equal (len (cons a x)) (+ 1 (len x)))))
(local (defthm fn-tcl-len-of-cdr
         (implies (consp x) (equal (len (cdr x)) (+ -1 (len x))))))
(local (in-theory (disable len)))

; --- :sess-init through fn-tcl-decode-init.

; The decode-init keystones below (append-error, consumes, append-ok) spent
; most of their time backchaining FN-TCL-CONSP-BY-LEN and FN-TCL-TAKE-ALL
; through the unrolled session-init fields; none of them needs either.
(local (in-theory (disable fn-tcl-consp-by-len fn-tcl-take-all)))

(defthm fn-tcl-decode-init-of-encode-body
  (implies (fn-tcl-messagep (fn-tcl-make-sess-init keepalive segment-mru transfer-mru node-id ext) mru)
           (equal (fn-tcl-decode-init (append (fn-tcl-encode-init-body (fn-tcl-make-sess-init keepalive segment-mru transfer-mru node-id ext)) rest))
                  (fn-tcl-parse-ok (fn-tcl-make-sess-init keepalive segment-mru transfer-mru node-id ext) rest)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-init-canonical
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-init body)))
           (equal (append (fn-tcl-encode-init-body (fn-tcl-parse-msg (fn-tcl-decode-init body)))
                          (fn-tcl-parse-rest (fn-tcl-decode-init body)))
                  body))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-init-kind
  (implies (and (fn-cbor-octet-listp body) (fn-tcl-parse-okp (fn-tcl-decode-init body)))
           (equal (fn-tcl-msg-kind (fn-tcl-parse-msg (fn-tcl-decode-init body))) :sess-init))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-init-yields-message
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-init body)))
           (fn-tcl-messagep (fn-tcl-parse-msg (fn-tcl-decode-init body)) mru))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-init-append-ok
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-okp (fn-tcl-decode-init left)))
           (equal (fn-tcl-decode-init (append left right))
                  (fn-tcl-parse-ok (fn-tcl-parse-msg (fn-tcl-decode-init left))
                                   (append (fn-tcl-parse-rest (fn-tcl-decode-init left)) right))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-init-append-error
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-errorp (fn-tcl-decode-init left)))
           (equal (fn-tcl-decode-init (append left right)) (fn-tcl-decode-init left)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-init-consumes
  (implies (fn-tcl-parse-okp (fn-tcl-decode-init body))
           (<= (len (fn-tcl-parse-rest (fn-tcl-decode-init body))) (len body)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-init-rest-octet-listp
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-init body)))
           (fn-cbor-octet-listp (fn-tcl-parse-rest (fn-tcl-decode-init body))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-init-outcomes
  (implies (fn-cbor-octet-listp body)
  (and (implies (and (not (fn-tcl-parse-okp (fn-tcl-decode-init body)))
                     (not (fn-tcl-parse-needp (fn-tcl-decode-init body))))
                (fn-tcl-parse-errorp (fn-tcl-decode-init body)))
       (implies (fn-tcl-parse-okp (fn-tcl-decode-init body))
                (and (not (fn-tcl-parse-needp (fn-tcl-decode-init body)))
                     (not (fn-tcl-parse-errorp (fn-tcl-decode-init body)))))
       (implies (fn-tcl-parse-needp (fn-tcl-decode-init body))
                (not (fn-tcl-parse-errorp (fn-tcl-decode-init body))))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-init-need-short
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-needp (fn-tcl-decode-init body)))
           (< (len body) 5144))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

; The SESS_INIT need bound just proved is a :linear rule on (len body)
; whose hypothesis is fn-tcl-decode-init itself, and every len term of the
; XFER_SEGMENT goals below would try it and open that decoder to relieve it:
; 4.8 million frames, none useful, in fn-tcl-decode-segment-append-error
; (the evidence file above).  Withdrawn here, as it is for the later blocks.
(local (in-theory (disable (:linear fn-tcl-decode-init-need-short))))

; --- :xfer-segment through fn-tcl-decode-segment.

(defthm fn-tcl-decode-segment-of-encode-body
  (implies (fn-tcl-messagep (fn-tcl-make-xfer-segment flags xfer-id ext data) mru)
           (equal (fn-tcl-decode-segment (append (fn-tcl-encode-segment-body (fn-tcl-make-xfer-segment flags xfer-id ext data)) rest) mru)
                  (fn-tcl-parse-ok (fn-tcl-make-xfer-segment flags xfer-id ext data) rest)))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data))))

(defthm fn-tcl-decode-segment-canonical
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-segment body mru)))
           (equal (append (fn-tcl-encode-segment-body (fn-tcl-parse-msg (fn-tcl-decode-segment body mru)))
                          (fn-tcl-parse-rest (fn-tcl-decode-segment body mru)))
                  body))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data))))

(defthm fn-tcl-decode-segment-kind
  (implies (and (fn-cbor-octet-listp body) (fn-tcl-parse-okp (fn-tcl-decode-segment body mru)))
           (equal (fn-tcl-msg-kind (fn-tcl-parse-msg (fn-tcl-decode-segment body mru))) :xfer-segment))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data))))

(defthm fn-tcl-decode-segment-yields-message
  (implies (and (fn-cbor-octet-listp body)
                (natp mru) (<= mru *fn-tcl-max-u64*)
                (fn-tcl-parse-okp (fn-tcl-decode-segment body mru)))
           (fn-tcl-messagep (fn-tcl-parse-msg (fn-tcl-decode-segment body mru)) mru))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data))))

(defthm fn-tcl-decode-segment-append-ok
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-okp (fn-tcl-decode-segment left mru)))
           (equal (fn-tcl-decode-segment (append left right) mru)
                  (fn-tcl-parse-ok (fn-tcl-parse-msg (fn-tcl-decode-segment left mru))
                                   (append (fn-tcl-parse-rest (fn-tcl-decode-segment left mru)) right))))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data))))

(defthm fn-tcl-decode-segment-append-error
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-errorp (fn-tcl-decode-segment left mru)))
           (equal (fn-tcl-decode-segment (append left right) mru) (fn-tcl-decode-segment left mru)))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data))))

(defthm fn-tcl-decode-segment-consumes
  (implies (fn-tcl-parse-okp (fn-tcl-decode-segment body mru))
           (<= (len (fn-tcl-parse-rest (fn-tcl-decode-segment body mru))) (len body)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data))))

(defthm fn-tcl-decode-segment-rest-octet-listp
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-segment body mru)))
           (fn-cbor-octet-listp (fn-tcl-parse-rest (fn-tcl-decode-segment body mru))))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data))))

(defthm fn-tcl-decode-segment-outcomes
  (implies (fn-cbor-octet-listp body)
  (and (implies (and (not (fn-tcl-parse-okp (fn-tcl-decode-segment body mru)))
                     (not (fn-tcl-parse-needp (fn-tcl-decode-segment body mru))))
                (fn-tcl-parse-errorp (fn-tcl-decode-segment body mru)))
       (implies (fn-tcl-parse-okp (fn-tcl-decode-segment body mru))
                (and (not (fn-tcl-parse-needp (fn-tcl-decode-segment body mru)))
                     (not (fn-tcl-parse-errorp (fn-tcl-decode-segment body mru)))))
       (implies (fn-tcl-parse-needp (fn-tcl-decode-segment body mru))
                (not (fn-tcl-parse-errorp (fn-tcl-decode-segment body mru))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data))))

(defthm fn-tcl-decode-segment-need-short
  (implies (and (fn-cbor-octet-listp body) (natp mru)
                (fn-tcl-parse-needp (fn-tcl-decode-segment body mru)))
           (< (len body) (+ 4117 mru)))
  :rule-classes (:rewrite :linear)
  ; The data part's need bound is stated over its own buffer, which is a drop
  ; of body and never a term of this goal, so both branches cite it by :use:
  ; 1 + 8 + (len after-id) for a continuation, 1 + 8 + 4 + ext-len + (len
  ; rest) with ext-len at most 4096 for a START.
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data)
           :use ((:instance fn-tcl-decode-segment-data-need-short
                            (flags (car body)) (xfer-id (fn-tcl-uint 8 (cdr body)))
                            (ext nil) (buf (fn-tcl-drop 8 (cdr body))))
                 (:instance fn-tcl-decode-segment-data-need-short
                            (flags (car body)) (xfer-id (fn-tcl-uint 8 (cdr body)))
                            (ext (fn-tcl-parse-msg
                                  (fn-tcl-decode-items
                                   (fn-tcl-take (fn-tcl-uint 4 (fn-tcl-drop 8 (cdr body)))
                                                (fn-tcl-drop 4 (fn-tcl-drop 8 (cdr body)))))))
                            (buf (fn-tcl-drop (fn-tcl-uint 4 (fn-tcl-drop 8 (cdr body)))
                                              (fn-tcl-drop 4 (fn-tcl-drop 8 (cdr body))))))))))

; --- Fixed-layout decoders (ack, refuse, term, reject) read (car body) and
; (car (cdr body)) raw; len is closed for them since the SESS_INIT block.
; The need bounds of the decoders above are :linear rules on (len body)
; whose hypothesis is the decoder itself, still open in this section: on a
; goal with several len terms each is re-run per term (fn-tcl-decode-init
; on (cdr left), on (append left right), ...), and
; fn-tcl-decode-term-append-ok did not return in 1600 s
; (build/acl2/certify-20260920T005346Z-77003).  Withdrawn for these blocks.
(local (in-theory (disable (:linear fn-tcl-decode-segment-data-need-short) (:linear fn-tcl-decode-init-need-short) (:linear fn-tcl-decode-segment-need-short))))

; --- :xfer-ack through fn-tcl-decode-ack.

(defthm fn-tcl-decode-ack-of-encode-body
  (implies (fn-tcl-messagep (fn-tcl-make-xfer-ack flags xfer-id acked-len) mru)
           (equal (fn-tcl-decode-ack (append (fn-tcl-encode-ack-body (fn-tcl-make-xfer-ack flags xfer-id acked-len)) rest))
                  (fn-tcl-parse-ok (fn-tcl-make-xfer-ack flags xfer-id acked-len) rest)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-ack-canonical
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-ack body)))
           (equal (append (fn-tcl-encode-ack-body (fn-tcl-parse-msg (fn-tcl-decode-ack body)))
                          (fn-tcl-parse-rest (fn-tcl-decode-ack body)))
                  body))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-ack-kind
  (implies (and (fn-cbor-octet-listp body) (fn-tcl-parse-okp (fn-tcl-decode-ack body)))
           (equal (fn-tcl-msg-kind (fn-tcl-parse-msg (fn-tcl-decode-ack body))) :xfer-ack))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-ack-yields-message
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-ack body)))
           (fn-tcl-messagep (fn-tcl-parse-msg (fn-tcl-decode-ack body)) mru))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-ack-append-ok
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-okp (fn-tcl-decode-ack left)))
           (equal (fn-tcl-decode-ack (append left right))
                  (fn-tcl-parse-ok (fn-tcl-parse-msg (fn-tcl-decode-ack left))
                                   (append (fn-tcl-parse-rest (fn-tcl-decode-ack left)) right))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-ack-append-error
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-errorp (fn-tcl-decode-ack left)))
           (equal (fn-tcl-decode-ack (append left right)) (fn-tcl-decode-ack left)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-ack-consumes
  (implies (fn-tcl-parse-okp (fn-tcl-decode-ack body))
           (<= (len (fn-tcl-parse-rest (fn-tcl-decode-ack body))) (len body)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-ack-rest-octet-listp
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-ack body)))
           (fn-cbor-octet-listp (fn-tcl-parse-rest (fn-tcl-decode-ack body))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-ack-outcomes
  (implies (fn-cbor-octet-listp body)
  (and (implies (and (not (fn-tcl-parse-okp (fn-tcl-decode-ack body)))
                     (not (fn-tcl-parse-needp (fn-tcl-decode-ack body))))
                (fn-tcl-parse-errorp (fn-tcl-decode-ack body)))
       (implies (fn-tcl-parse-okp (fn-tcl-decode-ack body))
                (and (not (fn-tcl-parse-needp (fn-tcl-decode-ack body)))
                     (not (fn-tcl-parse-errorp (fn-tcl-decode-ack body)))))
       (implies (fn-tcl-parse-needp (fn-tcl-decode-ack body))
                (not (fn-tcl-parse-errorp (fn-tcl-decode-ack body))))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-ack-need-short
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-needp (fn-tcl-decode-ack body)))
           (< (len body) 17))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

; --- :xfer-refuse through fn-tcl-decode-refuse.

(defthm fn-tcl-decode-refuse-of-encode-body
  (implies (fn-tcl-messagep (fn-tcl-make-xfer-refuse reason xfer-id) mru)
           (equal (fn-tcl-decode-refuse (append (fn-tcl-encode-refuse-body (fn-tcl-make-xfer-refuse reason xfer-id)) rest))
                  (fn-tcl-parse-ok (fn-tcl-make-xfer-refuse reason xfer-id) rest)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-refuse-canonical
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-refuse body)))
           (equal (append (fn-tcl-encode-refuse-body (fn-tcl-parse-msg (fn-tcl-decode-refuse body)))
                          (fn-tcl-parse-rest (fn-tcl-decode-refuse body)))
                  body))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-refuse-kind
  (implies (and (fn-cbor-octet-listp body) (fn-tcl-parse-okp (fn-tcl-decode-refuse body)))
           (equal (fn-tcl-msg-kind (fn-tcl-parse-msg (fn-tcl-decode-refuse body))) :xfer-refuse))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-refuse-yields-message
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-refuse body)))
           (fn-tcl-messagep (fn-tcl-parse-msg (fn-tcl-decode-refuse body)) mru))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-refuse-append-ok
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-okp (fn-tcl-decode-refuse left)))
           (equal (fn-tcl-decode-refuse (append left right))
                  (fn-tcl-parse-ok (fn-tcl-parse-msg (fn-tcl-decode-refuse left))
                                   (append (fn-tcl-parse-rest (fn-tcl-decode-refuse left)) right))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-refuse-append-error
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-errorp (fn-tcl-decode-refuse left)))
           (equal (fn-tcl-decode-refuse (append left right)) (fn-tcl-decode-refuse left)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-refuse-consumes
  (implies (fn-tcl-parse-okp (fn-tcl-decode-refuse body))
           (<= (len (fn-tcl-parse-rest (fn-tcl-decode-refuse body))) (len body)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-refuse-rest-octet-listp
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-refuse body)))
           (fn-cbor-octet-listp (fn-tcl-parse-rest (fn-tcl-decode-refuse body))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-refuse-outcomes
  (implies (fn-cbor-octet-listp body)
  (and (implies (and (not (fn-tcl-parse-okp (fn-tcl-decode-refuse body)))
                     (not (fn-tcl-parse-needp (fn-tcl-decode-refuse body))))
                (fn-tcl-parse-errorp (fn-tcl-decode-refuse body)))
       (implies (fn-tcl-parse-okp (fn-tcl-decode-refuse body))
                (and (not (fn-tcl-parse-needp (fn-tcl-decode-refuse body)))
                     (not (fn-tcl-parse-errorp (fn-tcl-decode-refuse body)))))
       (implies (fn-tcl-parse-needp (fn-tcl-decode-refuse body))
                (not (fn-tcl-parse-errorp (fn-tcl-decode-refuse body))))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-refuse-need-short
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-needp (fn-tcl-decode-refuse body)))
           (< (len body) 9))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

; --- :sess-term through fn-tcl-decode-term.

(defthm fn-tcl-decode-term-of-encode-body
  (implies (fn-tcl-messagep (fn-tcl-make-sess-term flags reason) mru)
           (equal (fn-tcl-decode-term (append (fn-tcl-encode-term-body (fn-tcl-make-sess-term flags reason)) rest))
                  (fn-tcl-parse-ok (fn-tcl-make-sess-term flags reason) rest)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-term-canonical
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-term body)))
           (equal (append (fn-tcl-encode-term-body (fn-tcl-parse-msg (fn-tcl-decode-term body)))
                          (fn-tcl-parse-rest (fn-tcl-decode-term body)))
                  body))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-term-kind
  (implies (and (fn-cbor-octet-listp body) (fn-tcl-parse-okp (fn-tcl-decode-term body)))
           (equal (fn-tcl-msg-kind (fn-tcl-parse-msg (fn-tcl-decode-term body))) :sess-term))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-term-yields-message
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-term body)))
           (fn-tcl-messagep (fn-tcl-parse-msg (fn-tcl-decode-term body)) mru))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-term-append-ok
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-okp (fn-tcl-decode-term left)))
           (equal (fn-tcl-decode-term (append left right))
                  (fn-tcl-parse-ok (fn-tcl-parse-msg (fn-tcl-decode-term left))
                                   (append (fn-tcl-parse-rest (fn-tcl-decode-term left)) right))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-term-append-error
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-errorp (fn-tcl-decode-term left)))
           (equal (fn-tcl-decode-term (append left right)) (fn-tcl-decode-term left)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-term-consumes
  (implies (fn-tcl-parse-okp (fn-tcl-decode-term body))
           (<= (len (fn-tcl-parse-rest (fn-tcl-decode-term body))) (len body)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-term-rest-octet-listp
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-term body)))
           (fn-cbor-octet-listp (fn-tcl-parse-rest (fn-tcl-decode-term body))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-term-outcomes
  (implies (fn-cbor-octet-listp body)
  (and (implies (and (not (fn-tcl-parse-okp (fn-tcl-decode-term body)))
                     (not (fn-tcl-parse-needp (fn-tcl-decode-term body))))
                (fn-tcl-parse-errorp (fn-tcl-decode-term body)))
       (implies (fn-tcl-parse-okp (fn-tcl-decode-term body))
                (and (not (fn-tcl-parse-needp (fn-tcl-decode-term body)))
                     (not (fn-tcl-parse-errorp (fn-tcl-decode-term body)))))
       (implies (fn-tcl-parse-needp (fn-tcl-decode-term body))
                (not (fn-tcl-parse-errorp (fn-tcl-decode-term body))))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-term-need-short
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-needp (fn-tcl-decode-term body)))
           (< (len body) 2))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

; --- :msg-reject through fn-tcl-decode-reject.

(defthm fn-tcl-decode-reject-of-encode-body
  (implies (fn-tcl-messagep (fn-tcl-make-msg-reject reason header) mru)
           (equal (fn-tcl-decode-reject (append (fn-tcl-encode-reject-body (fn-tcl-make-msg-reject reason header)) rest))
                  (fn-tcl-parse-ok (fn-tcl-make-msg-reject reason header) rest)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-reject-canonical
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-reject body)))
           (equal (append (fn-tcl-encode-reject-body (fn-tcl-parse-msg (fn-tcl-decode-reject body)))
                          (fn-tcl-parse-rest (fn-tcl-decode-reject body)))
                  body))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-reject-kind
  (implies (and (fn-cbor-octet-listp body) (fn-tcl-parse-okp (fn-tcl-decode-reject body)))
           (equal (fn-tcl-msg-kind (fn-tcl-parse-msg (fn-tcl-decode-reject body))) :msg-reject))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-reject-yields-message
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-reject body)))
           (fn-tcl-messagep (fn-tcl-parse-msg (fn-tcl-decode-reject body)) mru))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-reject-append-ok
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-okp (fn-tcl-decode-reject left)))
           (equal (fn-tcl-decode-reject (append left right))
                  (fn-tcl-parse-ok (fn-tcl-parse-msg (fn-tcl-decode-reject left))
                                   (append (fn-tcl-parse-rest (fn-tcl-decode-reject left)) right))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-reject-append-error
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-errorp (fn-tcl-decode-reject left)))
           (equal (fn-tcl-decode-reject (append left right)) (fn-tcl-decode-reject left)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-reject-consumes
  (implies (fn-tcl-parse-okp (fn-tcl-decode-reject body))
           (<= (len (fn-tcl-parse-rest (fn-tcl-decode-reject body))) (len body)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-reject-rest-octet-listp
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-reject body)))
           (fn-cbor-octet-listp (fn-tcl-parse-rest (fn-tcl-decode-reject body))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-reject-outcomes
  (implies (fn-cbor-octet-listp body)
  (and (implies (and (not (fn-tcl-parse-okp (fn-tcl-decode-reject body)))
                     (not (fn-tcl-parse-needp (fn-tcl-decode-reject body))))
                (fn-tcl-parse-errorp (fn-tcl-decode-reject body)))
       (implies (fn-tcl-parse-okp (fn-tcl-decode-reject body))
                (and (not (fn-tcl-parse-needp (fn-tcl-decode-reject body)))
                     (not (fn-tcl-parse-errorp (fn-tcl-decode-reject body)))))
       (implies (fn-tcl-parse-needp (fn-tcl-decode-reject body))
                (not (fn-tcl-parse-errorp (fn-tcl-decode-reject body))))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-reject-need-short
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-needp (fn-tcl-decode-reject body)))
           (< (len body) 2))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

; The MRU block and the message-level block below reason in the section's
; original theory with len open; the decoders' need bounds return as linear
; rules only once the decoders are closed (the message-level disable below),
; because with a decoder open they re-run it on every len term: the MRU
; bound's conclusion is a len term and it did not return in 2e7 steps.
(local (in-theory (enable len)))
(local (in-theory (disable fn-tcl-len-of-cons fn-tcl-len-of-cdr)))

; --- The segment MRU bound at the decoder.

(defthm fn-tcl-decoded-segment-fits-mru
  (implies (and (fn-cbor-octet-listp body)
                (fn-tcl-parse-okp (fn-tcl-decode-segment body mru)))
           (<= (len (fn-tcl-xfer-segment-data
                     (fn-tcl-parse-msg (fn-tcl-decode-segment body mru))))
               mru))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-decode-segment-data))))

; --- The message level: the type octet dispatches, the sub-decoders stay
; opaque and their keystones do the work.

(local (in-theory (disable fn-tcl-decode-init fn-tcl-decode-segment fn-tcl-decode-ack
                           fn-tcl-decode-refuse fn-tcl-decode-term fn-tcl-decode-reject
                           fn-tcl-decode-segment-data
                           fn-tcl-encode-init-body fn-tcl-encode-segment-body
                           fn-tcl-encode-ack-body fn-tcl-encode-refuse-body
                           fn-tcl-encode-term-body fn-tcl-encode-reject-body)))
(local (in-theory (enable (:linear fn-tcl-decode-segment-data-need-short) (:linear fn-tcl-decode-init-need-short) (:linear fn-tcl-decode-segment-need-short))))

(defthm fn-tcl-decode-message-of-encode-init
  (implies (fn-tcl-messagep (fn-tcl-make-sess-init keepalive segment-mru transfer-mru node-id ext) mru)
           (equal (fn-tcl-decode-message (append (fn-tcl-encode (fn-tcl-make-sess-init keepalive segment-mru transfer-mru node-id ext)) rest) mru)
                  (fn-tcl-parse-ok (fn-tcl-make-sess-init keepalive segment-mru transfer-mru node-id ext) rest)))
  ; The sub-decoder round trip has mru only in its hypothesis, which the
  ; goal would otherwise open into conjuncts, so the recognizer stays closed
  ; here and the keystone is cited with mru bound.
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-messagep)
           :use ((:instance fn-tcl-decode-init-of-encode-body (mru mru))))))

(defthm fn-tcl-decode-message-of-encode-segment
  (implies (fn-tcl-messagep (fn-tcl-make-xfer-segment flags xfer-id ext data) mru)
           (equal (fn-tcl-decode-message (append (fn-tcl-encode (fn-tcl-make-xfer-segment flags xfer-id ext data)) rest) mru)
                  (fn-tcl-parse-ok (fn-tcl-make-xfer-segment flags xfer-id ext data) rest)))
  ; As for the other kinds: the recognizer stays closed so the keystone's
  ; hypothesis is the goal's own literal, and the keystone is cited.
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-messagep)
           :use ((:instance fn-tcl-decode-segment-of-encode-body (mru mru))))))

(defthm fn-tcl-decode-message-of-encode-ack
  (implies (fn-tcl-messagep (fn-tcl-make-xfer-ack flags xfer-id acked-len) mru)
           (equal (fn-tcl-decode-message (append (fn-tcl-encode (fn-tcl-make-xfer-ack flags xfer-id acked-len)) rest) mru)
                  (fn-tcl-parse-ok (fn-tcl-make-xfer-ack flags xfer-id acked-len) rest)))
  ; The sub-decoder round trip has mru only in its hypothesis, which the
  ; goal would otherwise open into conjuncts, so the recognizer stays closed
  ; here and the keystone is cited with mru bound.
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-messagep)
           :use ((:instance fn-tcl-decode-ack-of-encode-body (mru mru))))))

(defthm fn-tcl-decode-message-of-encode-refuse
  (implies (fn-tcl-messagep (fn-tcl-make-xfer-refuse reason xfer-id) mru)
           (equal (fn-tcl-decode-message (append (fn-tcl-encode (fn-tcl-make-xfer-refuse reason xfer-id)) rest) mru)
                  (fn-tcl-parse-ok (fn-tcl-make-xfer-refuse reason xfer-id) rest)))
  ; The sub-decoder round trip has mru only in its hypothesis, which the
  ; goal would otherwise open into conjuncts, so the recognizer stays closed
  ; here and the keystone is cited with mru bound.
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-messagep)
           :use ((:instance fn-tcl-decode-refuse-of-encode-body (mru mru))))))

(defthm fn-tcl-decode-message-of-encode-term
  (implies (fn-tcl-messagep (fn-tcl-make-sess-term flags reason) mru)
           (equal (fn-tcl-decode-message (append (fn-tcl-encode (fn-tcl-make-sess-term flags reason)) rest) mru)
                  (fn-tcl-parse-ok (fn-tcl-make-sess-term flags reason) rest)))
  ; The sub-decoder round trip has mru only in its hypothesis, which the
  ; goal would otherwise open into conjuncts, so the recognizer stays closed
  ; here and the keystone is cited with mru bound.
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-messagep)
           :use ((:instance fn-tcl-decode-term-of-encode-body (mru mru))))))

(defthm fn-tcl-decode-message-of-encode-reject
  (implies (fn-tcl-messagep (fn-tcl-make-msg-reject reason header) mru)
           (equal (fn-tcl-decode-message (append (fn-tcl-encode (fn-tcl-make-msg-reject reason header)) rest) mru)
                  (fn-tcl-parse-ok (fn-tcl-make-msg-reject reason header) rest)))
  ; The sub-decoder round trip has mru only in its hypothesis, which the
  ; goal would otherwise open into conjuncts, so the recognizer stays closed
  ; here and the keystone is cited with mru bound.
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-tcl-messagep)
           :use ((:instance fn-tcl-decode-reject-of-encode-body (mru mru))))))

(defthm fn-tcl-decode-message-of-encode-keepalive
  (equal (fn-tcl-decode-message (append (fn-tcl-encode (fn-tcl-make-keepalive)) rest) mru)
         (fn-tcl-parse-ok (fn-tcl-make-keepalive) rest))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-accepted-message-is-canonical
  (implies (and (fn-cbor-octet-listp buf)
                (fn-tcl-parse-okp (fn-tcl-decode-message buf mru)))
           (equal (append (fn-tcl-encode (fn-tcl-parse-msg (fn-tcl-decode-message buf mru)))
                          (fn-tcl-parse-rest (fn-tcl-decode-message buf mru)))
                  buf))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-message-yields-message
  (implies (and (fn-cbor-octet-listp buf)
                (natp mru) (<= mru *fn-tcl-max-u64*)
                (fn-tcl-parse-okp (fn-tcl-decode-message buf mru)))
           (fn-tcl-messagep (fn-tcl-parse-msg (fn-tcl-decode-message buf mru)) mru))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-message-append-ok
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-okp (fn-tcl-decode-message left mru)))
           (equal (fn-tcl-decode-message (append left right) mru)
                  (fn-tcl-parse-ok (fn-tcl-parse-msg (fn-tcl-decode-message left mru))
                                   (append (fn-tcl-parse-rest (fn-tcl-decode-message left mru))
                                           right))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-message-append-error
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-errorp (fn-tcl-decode-message left mru)))
           (equal (fn-tcl-decode-message (append left right) mru)
                  (fn-tcl-decode-message left mru)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-message-consumes
  (implies (fn-tcl-parse-okp (fn-tcl-decode-message buf mru))
           (< (len (fn-tcl-parse-rest (fn-tcl-decode-message buf mru))) (len buf)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-message-rest-octet-listp
  (implies (and (fn-cbor-octet-listp buf)
                (fn-tcl-parse-okp (fn-tcl-decode-message buf mru)))
           (fn-cbor-octet-listp (fn-tcl-parse-rest (fn-tcl-decode-message buf mru))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-decode-message-outcomes
  (implies (fn-cbor-octet-listp buf)
  (and (implies (and (not (fn-tcl-parse-okp (fn-tcl-decode-message buf mru)))
                     (not (fn-tcl-parse-needp (fn-tcl-decode-message buf mru))))
                (fn-tcl-parse-errorp (fn-tcl-decode-message buf mru)))
       (implies (fn-tcl-parse-okp (fn-tcl-decode-message buf mru))
                (and (not (fn-tcl-parse-needp (fn-tcl-decode-message buf mru)))
                     (not (fn-tcl-parse-errorp (fn-tcl-decode-message buf mru)))))
       (implies (fn-tcl-parse-needp (fn-tcl-decode-message buf mru))
                (not (fn-tcl-parse-errorp (fn-tcl-decode-message buf mru))))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-tcl-need-means-short-buffer
  (implies (and (fn-cbor-octet-listp buf) (natp mru)
                (fn-tcl-parse-needp (fn-tcl-decode-message buf mru)))
           (< (len buf) (fn-tcl-max-message mru)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

; -----------------------------------------------------------------------------
; Executable guard closure of the decoders.  The three lemmas that turn the
; length arithmetic of `has` into the cons facts `car` and `cdr` need are
; local: a consp rule backchained to len is exactly what section 8 of
; docs/proof-style.md keeps out of an export theory.

(local (defthm fn-tcl-consp-drop
         (implies (< (nfix n) (len x)) (consp (fn-tcl-drop n x)))
         :hints (("Goal" :in-theory (enable fn-tcl-drop)))))
(local (defthm fn-tcl-cdr-drop
         (implies (natp n) (equal (cdr (fn-tcl-drop n x)) (fn-tcl-drop (+ 1 n) x)))
         :hints (("Goal" :in-theory (enable fn-tcl-drop)))))

(verify-guards fn-tcl-decode-contact)
(verify-guards fn-tcl-decode-segment-data)
(verify-guards fn-tcl-decode-segment)
(verify-guards fn-tcl-decode-init)
(verify-guards fn-tcl-decode-ack)
(verify-guards fn-tcl-decode-refuse)
(verify-guards fn-tcl-decode-term)
(verify-guards fn-tcl-decode-reject)
(verify-guards fn-tcl-decode-message)

; -----------------------------------------------------------------------------
; Export theory.  Keystones, record lemmas and the list vocabulary proofs
; induct on stay enabled.  The codec definitions, the flag predicates, the
; message recognizer and the bound function are withdrawn under one name.

(deftheory fn-tcl-codec-vocabulary
  '(fn-tcl-messagep fn-tcl-encode fn-tcl-encode-init-body fn-tcl-encode-segment-body
    fn-tcl-encode-ack-body fn-tcl-encode-refuse-body fn-tcl-encode-term-body
    fn-tcl-encode-reject-body fn-tcl-decode-contact fn-tcl-decode-segment-data
    fn-tcl-decode-segment fn-tcl-decode-init fn-tcl-decode-ack fn-tcl-decode-refuse
    fn-tcl-decode-term fn-tcl-decode-reject fn-tcl-decode-message fn-tcl-max-message
    fn-tcl-flag-end fn-tcl-flag-start fn-tcl-flag-reply fn-tcl-flag-can-tls
    fn-tcl-flag-critical fn-tcl-has fn-tcl-take fn-tcl-drop fn-tcl-rev fn-tcl-rev-aux
    fn-tcl-has-is-len-bound))

(in-theory (disable fn-tcl-codec-vocabulary))
