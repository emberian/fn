; fn: proactive fragmentation of an outbound bundle (RFC 9171 section 5.8)
; sized by the receiving convergence layer's Transfer MRU (RFC 9174 section
; 5.4.1: an entity SHALL NOT send a transfer longer than the peer's Transfer
; MRU).  Segmentation within one transfer is TCPCL's; a bundle longer than
; the peer's Transfer MRU is fragmented here or not sent.
;
; `fn-bpfs-plan WIRE MRU` is what host/native/bp-service.lisp
; `fnn-bps-send-effect` calls after SESS_INIT, with the session's negotiated
; Transfer MTU.  It answers one of
;
;   (:whole)                 WIRE is at most MRU octets: send it as it is;
;   (:fragments W1 ... Wn)   the fragments' wires in offset order;
;   (:refused REASON)        :malformed, :no-fragment (the bundle forbids
;                            it) or :mru-too-small (no payload octet fits).
;
; Each fragment is the parent's primary block through `fn-bpf-fragment-block`
; (for a parent that is itself a fragment, at its own ADU offset plus the
; local one and with its total: `fn-bpf-refragment-block`), EVERY extension
; block of the parent (RFC 9171 requires the replicate-flagged ones; a
; bundle whose creation time is zero needs its Bundle Age block in each,
; section 4.4.2), and a payload block carrying one contiguous extent.
;
; Keystones (the subject is `fn-bpfs-plan`, the function the host calls):
;   fn-bpfs-plan-fragments-fit-mru        every fragment wire is at most MRU;
;   fn-bpfs-plan-fragments-reassemble-exactly
;                                         the fragments' decoded views draw
;                                         the parent's payload exactly on the
;                                         reassembly canvas at the parent's
;                                         ADU offset, with no data cap;
;   fn-bpfs-plan-fragments-restore-parent every fragment decodes to a bundle
;                                         with the parent's extension blocks
;                                         whose primary unfragments to the
;                                         parent's (a whole parent).
; The receiver's executable reassembler `fn-bpf-reassemble` keeps its caps
; (*fn-bpf-max-length*, *fn-bpf-max-fragments*, in `fn-bpf-inputsp` and the
; held-row recognizer `fn-bpf-fragmentp`); within them it answers (:ok
; payload) on these fragments (fn-bpfs-plan-fragments-reassemble-within-caps).

(in-package "ACL2")

(include-book "bp-fragment-invariants")
(include-book "bp-bundle-invariants")

; -----------------------------------------------------------------------------
; One fragment

; The primary block of the fragment at local offset OFFSET of a parent whose
; payload has N octets: a whole parent is cut in its own coordinates; a
; fragment parent keeps its ADU coordinates and total
; (`fn-bpf-refragment-block`, spelled out so both cases are one
; `fn-bpf-fragment-block` term).
(defun fn-bpfs-base (p)
  (declare (xargs :guard (fn-bpp-blockp p)))
  (if (fn-bpp-fragmentp (fn-bpp-flags p)) (nfix (fn-bpp-fragment-offset p)) 0))

(defun fn-bpfs-total (p n)
  (declare (xargs :guard (fn-bpp-blockp p)))
  (if (fn-bpp-fragmentp (fn-bpp-flags p)) (nfix (fn-bpp-total-adu-length p)) (nfix n)))

(defun fn-bpfs-primary (p offset n)
  (declare (xargs :verify-guards nil :guard (and (fn-bpp-blockp p) (natp offset))))
  (fn-bpf-fragment-block p (+ (fn-bpfs-base p) offset) (fn-bpfs-total p n)))

(defun fn-bpfs-payload-block (pay bytes)
  (declare (xargs :verify-guards nil :guard (and (fn-bpb-blockp pay) (fn-bpb-datap bytes))))
  (fn-bpb-make-block (fn-bpb-block-type pay) (fn-bpb-block-number pay)
                     (fn-bpb-block-flags pay) (fn-bpb-block-crc-type pay)
                     bytes))

; The fragment of BUNDLE whose payload is BYTES at local offset OFFSET.
(defun fn-bpfs-fragment (bundle offset bytes)
  (declare (xargs :verify-guards nil :guard (and (fn-bpb-bundlep bundle) (natp offset)
                              (fn-bpb-datap bytes))))
  (fn-bpb-make-bundle
   (fn-bpfs-primary (fn-bpb-bundle-primary bundle) offset
                    (len (fn-bpb-payload bundle)))
   (fn-bpb-bundle-blocks bundle)
   (fn-bpfs-payload-block (fn-bpb-bundle-payload bundle) bytes)))

; A parent the plan can cut: fragmentation allowed, the fragment flag
; representable, and a fragment parent's extent inside its declared total.
(defun fn-bpfs-cuttablep (bundle)
  (declare (xargs :verify-guards nil :guard (fn-bpb-bundlep bundle)))
  (let ((p (fn-bpb-bundle-primary bundle)))
    (and (<= (+ (fn-bpp-flags p) 1) *fn-bpc-max-uint*)
         (or (not (fn-bpp-fragmentp (fn-bpp-flags p)))
             (<= (+ (nfix (fn-bpp-fragment-offset p))
                    (len (fn-bpb-payload bundle)))
                 (nfix (fn-bpp-total-adu-length p)))))))

; The encoded length of the fragment carrying no payload octets at the
; largest local offset, N: every fragment's encoding is at most this plus
; the growth of the payload's byte-string head (at most 8 octets) plus its
; payload (fn-bpfs-fragment-length-bound).
(defun fn-bpfs-overhead (bundle)
  (declare (xargs :verify-guards nil
                  :guard (and (fn-bpb-bundlep bundle) (fn-bpfs-cuttablep bundle))))
  (len (fn-bpb-encode
        (fn-bpfs-fragment bundle (len (fn-bpb-payload bundle)) nil))))

; -----------------------------------------------------------------------------
; The cut: consecutive extents of CHUNK octets (the last shorter).

(defun fn-bpfs-cut (bundle payload offset chunk)
  (declare (xargs :guard (and (fn-bpb-bundlep bundle) (fn-bpfs-cuttablep bundle)
                              (fn-cbor-octet-listp payload) (natp offset)
                              (equal (+ offset (len payload))
                                     (len (fn-bpb-payload bundle)))
                              (natp chunk))
                  :verify-guards nil
                  :measure (len payload)))
  (if (or (atom payload) (zp chunk))
      nil
    (let ((n (min chunk (len payload))))
      (cons (fn-bpb-encode (fn-bpfs-fragment bundle offset (take n payload)))
            (fn-bpfs-cut bundle (nthcdr n payload) (+ offset n) chunk)))))

(defun fn-bpfs-plan (wire mru)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((not (and (natp mru) (fn-cbor-octet-listp wire))) (list :refused :malformed))
   ((<= (len wire) mru) (list :whole))
   (t
    (let ((r (fn-bpb-decode wire (len wire))))
      (if (not (fn-cbor-result-okp r))
          (list :refused :malformed)
        (let* ((bundle (fn-cbor-result-value r))
               (p (fn-bpb-bundle-primary bundle)))
          (cond
           ((fn-bpp-no-fragmentp (fn-bpp-flags p)) (list :refused :no-fragment))
           ((not (fn-bpfs-cuttablep bundle)) (list :refused :malformed))
           ;; No cut makes a bundle with an empty payload any shorter.
           ((atom (fn-bpb-payload bundle)) (list :refused :mru-too-small))
           (t
            (let ((chunk (- mru (+ 8 (fn-bpfs-overhead bundle)))))
              (if (<= chunk 0)
                  (list :refused :mru-too-small)
                (cons :fragments
                      (fn-bpfs-cut bundle (fn-bpb-payload bundle) 0
                                   chunk))))))))))))

; The bundle a :fragments plan cut (the decoded WIRE).
(defun fn-bpfs-parent (wire)
  (declare (xargs :guard (fn-cbor-octet-listp wire) :verify-guards nil))
  (fn-cbor-result-value (fn-bpb-decode wire (len wire))))

; -----------------------------------------------------------------------------
; What a receiver sees: each wire decoded, as a reassembly fragment view
; (offset bytes total), and the per-wire checks the keystones state.

(defun fn-bpfs-views (wires)
  (declare (xargs :guard (true-listp wires) :verify-guards nil))
  (if (atom wires)
      nil
    (let* ((b (fn-cbor-result-value
               (fn-bpb-decode (car wires) (len (car wires)))))
           (p (fn-bpb-bundle-primary b)))
      (cons (fn-bpf-make (fn-bpp-fragment-offset p) (fn-bpb-payload b)
                         (fn-bpp-total-adu-length p))
            (fn-bpfs-views (cdr wires))))))

(defun fn-bpfs-all-at-most (wires mru)
  (declare (xargs :guard (and (true-listp wires) (natp mru))))
  (if (atom wires)
      t
    (and (<= (len (car wires)) mru)
         (fn-bpfs-all-at-most (cdr wires) mru))))

; -----------------------------------------------------------------------------
; Encoded lengths: a CBOR head, the CRC field, the payload block.

(defun fn-bpfs-argument-width (n)
  (declare (xargs :guard (natp n)))
  (cond ((< n 24) 1) ((< n 256) 2) ((< n 65536) 3) ((< n 4294967296) 5) (t 9)))

(defthm fn-bpfs-u32-octets-length
  (equal (len (fn-bpc-u32-octets n)) 4)
  :hints (("Goal" :in-theory (enable fn-bpc-u32-octets))))

(defthm fn-bpfs-len-of-append
  (equal (len (append x y)) (+ (len x) (len y))))

(defthm fn-bpfs-u16-bytes-length
  (equal (len (fn-cbor-u16-bytes n)) 2)
  :hints (("Goal" :in-theory (enable fn-cbor-u16-bytes))))

(defthm fn-bpfs-u32-bytes-length
  (equal (len (fn-cbor-u32-bytes n)) 4)
  :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes))))

(defthm fn-bpfs-argument-length
  (implies (and (natp major) (natp n))
           (equal (len (fn-bpc-argument major n))
                  (fn-bpfs-argument-width n)))
  :hints (("Goal" :in-theory (e/d (fn-bpc-argument fn-cbor-encode-argument
                                     fn-bpc-u64-bytes)
                           (fn-bpc-u32-octets fn-cbor-u32-bytes fn-cbor-u16-bytes floor mod)))))

(defthm fn-bpfs-argument-width-monotone
  (implies (and (natp n) (natp m) (<= n m))
           (<= (fn-bpfs-argument-width n) (fn-bpfs-argument-width m)))
  :rule-classes :linear)

(defthm fn-bpfs-argument-width-range
  (and (<= 1 (fn-bpfs-argument-width n))
       (<= (fn-bpfs-argument-width n) 9))
  :rule-classes :linear)

(defthm fn-bpfs-argument-width-of-zero
  (equal (fn-bpfs-argument-width 0) 1))

(in-theory (disable fn-bpfs-argument-width))

(defthm fn-bpfs-crc-octets-width
  (implies (fn-bpp-crc-typep type)
           (equal (len (fn-bpp-crc-octets type octets))
                  (fn-bpp-crc-width type)))
  :hints (("Goal" :in-theory (e/d (fn-bpc-u16-bytes-have-length-two
                                   fn-bpc-u32-bytes-have-length-four
                                   fn-bpp-crc-octets)
                                  (fn-bpp-crc16 fn-bpp-crc32c
                                   fn-cbor-u16-bytes fn-cbor-u32-bytes)))))

(defthm fn-bpfs-block-crc-type-is-a-crc-type
  (implies (fn-bpb-blockp b) (fn-bpp-crc-typep (fn-bpb-block-crc-type b)))
  :hints (("Goal" :in-theory (enable fn-bpb-blockp))))

(defthm fn-bpfs-block-crc-width
  (implies (fn-bpb-blockp b)
           (equal (len (fn-bpb-block-crc b))
                  (fn-bpp-crc-width (fn-bpb-block-crc-type b))))
  :hints (("Goal" :in-theory (e/d (fn-bpb-block-crc)
                                  (fn-bpb-encode-block-with-crc fn-bpp-crc-octets
                                   fn-bpp-crc-width fn-bpp-zero-crc fn-bpp-crc-typep)))))

(defthm fn-bpfs-payload-block-fields
  (and (equal (fn-bpb-block-type (fn-bpfs-payload-block pay bytes))
              (fn-bpb-block-type pay))
       (equal (fn-bpb-block-number (fn-bpfs-payload-block pay bytes))
              (fn-bpb-block-number pay))
       (equal (fn-bpb-block-flags (fn-bpfs-payload-block pay bytes))
              (fn-bpb-block-flags pay))
       (equal (fn-bpb-block-crc-type (fn-bpfs-payload-block pay bytes))
              (fn-bpb-block-crc-type pay))
       (equal (fn-bpb-block-data (fn-bpfs-payload-block pay bytes))
              bytes)))

(defthm fn-bpfs-payload-block-is-a-block
  (implies (and (fn-bpb-blockp pay) (fn-bpb-datap bytes))
           (fn-bpb-blockp (fn-bpfs-payload-block pay bytes)))
  :hints (("Goal" :in-theory (e/d (fn-bpb-blockp) (fn-bpb-datap fn-bpp-timep
                                                   fn-bpp-flag-setp fn-bpp-crc-typep)))))

(defthm fn-bpfs-nil-is-data
  (fn-bpb-datap nil))

(in-theory (disable fn-bpfs-payload-block))

; The payload block's encoding grows with its data exactly by the data and
; the growth of the byte-string head.
(defthm fn-bpfs-payload-block-length
  (implies (and (fn-bpb-blockp pay) (fn-bpb-datap bytes))
           (equal (len (fn-bpb-encode-block (fn-bpfs-payload-block pay bytes)))
                  (+ (len (fn-bpb-encode-block (fn-bpfs-payload-block pay nil)))
                     -1 (fn-bpfs-argument-width (len bytes)) (len bytes))))
  :hints (("Goal" :in-theory (e/d (fn-bpb-encode-block fn-bpb-encode-block-with-crc)
                                  (fn-bpb-block-crc fn-bpp-crc-width fn-bpb-datap
                                   fn-bpb-blockp fn-bpc-argument)))))

; Used by instance only: at BYTES nil it would rewrite its own right side.
(in-theory (disable fn-bpfs-payload-block-length))

; -----------------------------------------------------------------------------
; The primary block: moving the offset changes its encoding by exactly the
; change of the offset's CBOR head.

(defthm fn-bpfs-primary-crc-type-is-a-crc-type
  (implies (fn-bpp-blockp b) (fn-bpp-crc-typep (fn-bpp-crc-type b)))
  :hints (("Goal" :in-theory (e/d (fn-bpp-blockp)
                                  (fn-bpp-eidp fn-bpp-timep fn-bpp-crc-typep
                                   fn-bpp-flag-setp fn-bpp-fragmentp)))))

(defthm fn-bpfs-primary-crc-width
  (implies (fn-bpp-blockp b)
           (equal (len (fn-bpp-block-crc b))
                  (fn-bpp-crc-width (fn-bpp-crc-type b))))
  :hints (("Goal" :in-theory (e/d (fn-bpp-block-crc)
                                  (fn-bpp-zeroed-encoding fn-bpp-crc-octets
                                   fn-bpp-crc-width fn-bpp-crc-typep fn-bpp-blockp))
           :use ((:instance fn-bpfs-crc-octets-width
                            (type (fn-bpp-crc-type b))
                            (octets (fn-bpp-zeroed-encoding b)))))))

(defthm fn-bpfs-fragment-block-fields
  (and (equal (fn-bpp-crc-type (fn-bpf-fragment-block p x total)) (fn-bpp-crc-type p))
       (equal (fn-bpp-destination (fn-bpf-fragment-block p x total)) (fn-bpp-destination p))
       (equal (fn-bpp-source (fn-bpf-fragment-block p x total)) (fn-bpp-source p))
       (equal (fn-bpp-report-to (fn-bpf-fragment-block p x total)) (fn-bpp-report-to p))
       (equal (fn-bpp-creation-time (fn-bpf-fragment-block p x total)) (fn-bpp-creation-time p))
       (equal (fn-bpp-sequence (fn-bpf-fragment-block p x total)) (fn-bpp-sequence p))
       (equal (fn-bpp-lifetime (fn-bpf-fragment-block p x total)) (fn-bpp-lifetime p))
       (equal (fn-bpp-fragment-offset (fn-bpf-fragment-block p x total)) x)
       (equal (fn-bpp-total-adu-length (fn-bpf-fragment-block p x total)) total)))

(defthm fn-bpfs-fragment-block-flags-ignore-offset
  (equal (fn-bpp-flags (fn-bpf-fragment-block p x total))
         (fn-bpp-flags (fn-bpf-fragment-block p y total2)))
  :rule-classes nil)

; The CBOR encoder, one step at a time, so the eid items stay closed.

(defthm fn-bpfs-enc-array
  (equal (fn-bpc-enc :item (cons :array xs))
         (if (true-listp xs)
             (append (fn-bpc-argument 4 (len xs)) (fn-bpc-enc :list xs))
           nil))
  :hints (("Goal" :expand ((fn-bpc-enc :item (cons :array xs))))))

(defthm fn-bpfs-enc-list-cons
  (equal (fn-bpc-enc :list (cons a b))
         (append (fn-bpc-enc :item a) (fn-bpc-enc :list b)))
  :hints (("Goal" :expand ((fn-bpc-enc :list (cons a b))))))

(defthm fn-bpfs-enc-list-nil
  (equal (fn-bpc-enc :list nil) nil)
  :hints (("Goal" :expand ((fn-bpc-enc :list nil)))))

(defthm fn-bpfs-enc-uint
  (equal (fn-bpc-enc :item (cons :uint n))
         (if (natp n) (fn-bpc-argument 0 n) nil))
  :hints (("Goal" :expand ((fn-bpc-enc :item (cons :uint n))))))

(defthm fn-bpfs-enc-bytes
  (equal (fn-bpc-enc :item (cons :bytes c))
         (if (fn-cbor-octet-listp c) (append (fn-bpc-argument 2 (len c)) c) nil))
  :hints (("Goal" :expand ((fn-bpc-enc :item (cons :bytes c))))))

(defthm fn-bpfs-enc-list-atom
  (implies (not (consp a)) (equal (fn-bpc-enc :list a) nil))
  :hints (("Goal" :expand ((fn-bpc-enc :list a)))))

(defthm fn-bpfs-enc-list-append
  (equal (fn-bpc-enc :list (append a b))
         (append (fn-bpc-enc :list a) (fn-bpc-enc :list b)))
  :hints (("Goal" :induct (len a) :in-theory (disable fn-bpc-enc))))

(defthm fn-bpfs-primary-numeric-fields
  (implies (fn-bpp-blockp p)
           (and (natp (fn-bpp-flags p))
                (natp (fn-bpp-crc-type p))
                (natp (fn-bpp-creation-time p))
                (natp (fn-bpp-sequence p))
                (natp (fn-bpp-lifetime p))))
  :hints (("Goal" :in-theory (e/d (fn-bpp-blockp fn-bpp-timep fn-bpp-flag-setp fn-bpp-crc-typep)
                                  (fn-bpp-eidp fn-bpp-fragmentp)))))

(defthm fn-bpfs-fragment-primary-length-shift
  (implies (and (fn-bpp-blockp p)
                (<= (+ (fn-bpp-flags p) 1) *fn-bpc-max-uint*)
                (fn-bpp-timep x) (fn-bpp-timep y) (fn-bpp-timep total))
           (equal (+ (len (fn-bpp-encode (fn-bpf-fragment-block p x total)))
                     (fn-bpfs-argument-width y))
                  (+ (len (fn-bpp-encode (fn-bpf-fragment-block p y total)))
                     (fn-bpfs-argument-width x))))
  :hints (("Goal" :in-theory (e/d (fn-bpp-encode fn-bpp-block-value)
                                  (fn-bpc-enc fn-bpfs-primary-numeric-fields binary-append fn-bpf-fragment-block fn-bpp-block-crc
                                   fn-bpp-eid-value fn-bpp-blockp fn-bpp-timep
                                   fn-bpp-crc-width fn-bpc-argument fn-bpp-fragmentp))
           :use ((:instance fn-bpfs-fragment-block-flags-ignore-offset (total2 total))
                 (:instance fn-bpfs-primary-numeric-fields (p (fn-bpf-fragment-block p x total)))
                 (:instance fn-bpfs-primary-numeric-fields (p (fn-bpf-fragment-block p y total)))
                 (:instance fn-bpf-fragment-block-sets-the-fragment-flag (b p) (offset x))
                 (:instance fn-bpf-fragment-block-is-a-block (b p) (offset x))
                 (:instance fn-bpf-fragment-block-is-a-block (b p) (offset y))))))

; Used by instance only: X and Y are symmetric.
(in-theory (disable fn-bpfs-fragment-primary-length-shift))

; -----------------------------------------------------------------------------
; One fragment's encoded length, and the cut's.

(defthm fn-bpfs-block-data-is-data
  (implies (fn-bpb-blockp x) (fn-bpb-datap (fn-bpb-block-data x)))
  :hints (("Goal" :in-theory (e/d (fn-bpb-blockp) (fn-bpb-datap fn-bpp-timep
                                                   fn-bpp-flag-setp fn-bpp-crc-typep)))))

(defthm fn-bpfs-bundle-parts
  (implies (fn-bpb-bundlep b)
           (and (fn-bpp-blockp (fn-bpb-bundle-primary b))
                (fn-bpb-block-listp (fn-bpb-bundle-blocks b))
                (fn-bpb-payload-blockp (fn-bpb-bundle-payload b))
                (fn-bpb-blockp (fn-bpb-bundle-payload b))
                (fn-bpb-splitp (fn-bpb-bundle-blocks b) (fn-bpb-bundle-payload b))
                (fn-bpb-datap (fn-bpb-payload b))))
  :hints (("Goal" :in-theory (e/d (fn-bpb-bundlep fn-bpb-payload-blockp fn-bpb-payload)
                                  (fn-bpb-blockp fn-bpp-blockp fn-bpb-block-listp
                                   fn-bpb-splitp fn-bpb-datap)))))

(defthm fn-bpfs-bundle-encode-length
  (equal (len (fn-bpb-encode b))
         (+ 2 (len (fn-bpp-encode (fn-bpb-bundle-primary b)))
            (len (fn-bpb-encode-blocks (fn-bpb-bundle-blocks b)))
            (len (fn-bpb-encode-block (fn-bpb-bundle-payload b)))))
  :hints (("Goal" :in-theory (e/d (fn-bpb-encode)
                                  (fn-bpp-encode fn-bpb-encode-blocks
                                   fn-bpb-encode-block)))))

(defthm fn-bpfs-datap-bound
  (implies (fn-bpb-datap d) (<= (len d) *fn-bpb-max-data*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-bpb-datap))))

(defthm fn-bpfs-fragment-parent-fields
  (implies (and (fn-bpp-blockp p) (fn-bpp-fragmentp (fn-bpp-flags p)))
           (and (fn-bpp-timep (fn-bpp-fragment-offset p))
                (fn-bpp-timep (fn-bpp-total-adu-length p))))
  :hints (("Goal" :in-theory (e/d (fn-bpp-blockp)
                                  (fn-bpp-eidp fn-bpp-crc-typep fn-bpp-flag-setp
                                   fn-bpp-fragmentp fn-bpp-timep)))))

; The primary's offset and total are representable for every local offset
; up to the parent's payload length.
(defthm fn-bpfs-primary-coordinates-are-times
  (implies (and (fn-bpb-bundlep b) (fn-bpfs-cuttablep b)
                (natp o) (<= o (len (fn-bpb-payload b))))
           (and (fn-bpp-timep (+ (fn-bpfs-base (fn-bpb-bundle-primary b)) o))
                (fn-bpp-timep (fn-bpfs-total (fn-bpb-bundle-primary b)
                                             (len (fn-bpb-payload b))))))
  :hints (("Goal" :in-theory (e/d ()
                                  (fn-bpp-blockp fn-bpp-fragmentp fn-bpb-payload
                                   fn-bpfs-bundle-parts fn-bpfs-fragment-parent-fields))
           :use ((:instance fn-bpfs-bundle-parts)
                 (:instance fn-bpfs-fragment-parent-fields (p (fn-bpb-bundle-primary b)))
                 (:instance fn-bpfs-datap-bound (d (fn-bpb-payload b)))))))

(defthm fn-bpfs-cuttable-flags
  (implies (fn-bpfs-cuttablep b)
           (<= (+ (fn-bpp-flags (fn-bpb-bundle-primary b)) 1) *fn-bpc-max-uint*))
  :rule-classes :forward-chaining)

; Exact: the fragment at local offset O carrying D is the overhead's
; encoding with the offset head and the payload head and data changed.
(defthm fn-bpfs-fragment-encode-length
  (implies (and (fn-bpb-bundlep b) (fn-bpfs-cuttablep b)
                (natp o) (<= o (len (fn-bpb-payload b)))
                (fn-bpb-datap d))
           (equal (len (fn-bpb-encode (fn-bpfs-fragment b o d)))
                  (+ (fn-bpfs-overhead b) -1
                     (fn-bpfs-argument-width (len d)) (len d)
                     (fn-bpfs-argument-width
                      (+ (fn-bpfs-base (fn-bpb-bundle-primary b)) o))
                     (- (fn-bpfs-argument-width
                         (+ (fn-bpfs-base (fn-bpb-bundle-primary b))
                            (len (fn-bpb-payload b))))))))
  :hints (("Goal" :in-theory (e/d (fn-bpfs-fragment fn-bpfs-overhead fn-bpfs-primary)
                                  (fn-bpb-encode fn-bpp-encode fn-bpb-encode-blocks
                                   fn-bpb-encode-block fn-bpf-fragment-block
                                   fn-bpfs-base fn-bpfs-total fn-bpfs-cuttablep
                                   fn-bpb-bundlep fn-bpb-payload fn-bpb-datap
                                   fn-bpp-timep fn-bpp-blockp
                                   fn-bpfs-fragment-primary-length-shift
                                   fn-bpfs-payload-block-length
                                   fn-bpfs-primary-coordinates-are-times
                                   fn-bpfs-argument-width-monotone))
           :use ((:instance fn-bpfs-primary-coordinates-are-times)
                 (:instance fn-bpfs-primary-coordinates-are-times (o (len (fn-bpb-payload b))))
                 (:instance fn-bpfs-fragment-primary-length-shift
                            (p (fn-bpb-bundle-primary b))
                            (x (+ (fn-bpfs-base (fn-bpb-bundle-primary b)) o))
                            (y (+ (fn-bpfs-base (fn-bpb-bundle-primary b))
                                  (len (fn-bpb-payload b))))
                            (total (fn-bpfs-total (fn-bpb-bundle-primary b)
                                                  (len (fn-bpb-payload b)))))
                 (:instance fn-bpfs-payload-block-length
                            (pay (fn-bpb-bundle-payload b)) (bytes d))))))

(defthm fn-bpfs-fragment-length-bound
  (implies (and (fn-bpb-bundlep b) (fn-bpfs-cuttablep b)
                (natp o) (<= o (len (fn-bpb-payload b)))
                (fn-bpb-datap d))
           (<= (len (fn-bpb-encode (fn-bpfs-fragment b o d)))
               (+ (fn-bpfs-overhead b) 8 (len d))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-bpfs-fragment fn-bpfs-overhead
                                      fn-bpfs-base fn-bpb-payload fn-bpb-bundlep
                                      fn-bpfs-cuttablep fn-bpb-datap)
           :use ((:instance fn-bpfs-argument-width-monotone
                            (n (+ (fn-bpfs-base (fn-bpb-bundle-primary b)) o))
                            (m (+ (fn-bpfs-base (fn-bpb-bundle-primary b))
                                  (len (fn-bpb-payload b)))))))))

(defthm fn-bpfs-take-of-octets
  (implies (and (fn-cbor-octet-listp xs) (natp n) (<= n (len xs)))
           (fn-cbor-octet-listp (take n xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))

(defthm fn-bpfs-nthcdr-of-octets
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (nthcdr n xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))

(defthm fn-bpfs-len-of-take
  (equal (len (take n xs)) (nfix n)))

(defthm fn-bpfs-take-is-data
  (implies (and (fn-cbor-octet-listp xs) (natp n) (<= n (len xs))
                (<= (len xs) *fn-bpb-max-data*))
           (fn-bpb-datap (take n xs)))
  :hints (("Goal" :in-theory (e/d (fn-bpb-datap) (fn-cbor-octet-listp take))
           :use ((:instance fn-bpfs-take-of-octets)))))

(defthm fn-bpfs-cut-step-fits-take
  (implies (and (fn-bpb-bundlep b) (fn-bpfs-cuttablep b)
                (fn-cbor-octet-listp payload) (natp off)
                (equal (+ off (len payload)) (len (fn-bpb-payload b)))
                (natp limit) (natp n) (<= n chunk) (<= n (len payload))
                (<= (+ (fn-bpfs-overhead b) 8 chunk) limit))
           (<= (len (fn-bpb-encode (fn-bpfs-fragment b off (take n payload))))
               limit))
  :hints (("Goal" :in-theory (union-theories
                               (theory 'minimal-theory)
                               '(fn-bpfs-len-of-take nfix natp
                                 (:type-prescription len)))
           :use ((:instance fn-bpfs-fragment-length-bound
                            (o off) (d (take n payload)))
                 (:instance fn-bpfs-take-is-data (xs payload))
                 (:instance fn-bpfs-bundle-parts)
                 (:instance fn-bpfs-datap-bound (d (fn-bpb-payload b)))))))

(defthm fn-bpfs-all-at-most-of-cons
  (equal (fn-bpfs-all-at-most (cons a rest) m)
         (and (<= (len a) m) (fn-bpfs-all-at-most rest m))))

(defthm fn-bpfs-len-of-nthcdr
  (implies (and (natp k) (<= k (len xs)))
           (equal (len (nthcdr k xs)) (- (len xs) k))))

(defthm fn-bpfs-cut-fits
  (implies (and (fn-bpb-bundlep b) (fn-bpfs-cuttablep b)
                (fn-cbor-octet-listp payload) (natp off)
                (equal (+ off (len payload)) (len (fn-bpb-payload b)))
                (natp limit)
                (<= (+ (fn-bpfs-overhead b) 8 chunk) limit))
           (fn-bpfs-all-at-most (fn-bpfs-cut b payload off chunk) limit))
  :hints (("Goal" :induct (fn-bpfs-cut b payload off chunk)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-bpfs-all-at-most-of-cons fn-bpfs-all-at-most fn-bpfs-cut
                         fn-bpfs-len-of-take fn-bpfs-len-of-nthcdr
                         fn-bpfs-nthcdr-of-octets nfix min natp posp zp atom
                         (:type-prescription len) (:induction fn-bpfs-cut))))
          ("Subgoal *1/2" :use ((:instance fn-bpfs-cut-step-fits-take
                                           (n (min chunk (len payload))))))))

; -----------------------------------------------------------------------------
; Keystone: every fragment the plan answers is at most MRU octets.

(defthm fn-bpfs-payload-is-octets
  (implies (fn-bpb-bundlep b) (fn-cbor-octet-listp (fn-bpb-payload b)))
  :hints (("Goal" :use ((:instance fn-bpfs-bundle-parts))
           :in-theory (e/d (fn-bpb-datap) (fn-bpfs-bundle-parts fn-bpb-payload fn-bpb-bundlep)))))

(defthm fn-bpfs-plan-fragments-fit-mru
  (implies (equal (car (fn-bpfs-plan wire mru)) :fragments)
           (fn-bpfs-all-at-most (cdr (fn-bpfs-plan wire mru)) mru))
  :hints (("Goal" :in-theory (disable fn-bpfs-cut fn-bpfs-overhead fn-bpb-decode
                                      fn-bpb-bundlep fn-bpfs-cuttablep fn-bpb-payload
                                      fn-bpp-no-fragmentp)
           :use ((:instance fn-bpb-decode-yields-bundle (octets wire) (limit (len wire)))
                 (:instance fn-bpfs-cut-fits
                            (b (fn-cbor-result-value (fn-bpb-decode wire (len wire))))
                            (payload (fn-bpb-payload (fn-cbor-result-value (fn-bpb-decode wire (len wire)))))
                            (off 0) (limit mru)
                            (chunk (- mru (+ 8 (fn-bpfs-overhead (fn-cbor-result-value (fn-bpb-decode wire (len wire))))))))))))

; Everything below reasons about fragments through the facts above, never
; through the encoders.
(in-theory (disable fn-bpb-encode fn-bpp-encode fn-bpf-fragment-block
                    fn-bpfs-fragment fn-bpfs-primary fn-bpfs-overhead
                    fn-bpfs-cuttablep fn-bpfs-base fn-bpfs-total
                    fn-bpfs-enc-array fn-bpfs-enc-list-cons fn-bpfs-enc-uint
                    fn-bpfs-enc-bytes fn-bpfs-enc-list-append
                    fn-bpfs-bundle-encode-length fn-bpfs-fragment-encode-length))

; -----------------------------------------------------------------------------
; What a receiver decodes: each fragment wire is the fragment bundle, and the
; cut's views are consecutive extents of the payload.

(defthm fn-bpfs-fragment-is-a-bundle
  (implies (and (fn-bpb-bundlep b) (fn-bpfs-cuttablep b)
                (natp o) (<= o (len (fn-bpb-payload b)))
                (fn-bpb-datap d))
           (fn-bpb-bundlep (fn-bpfs-fragment b o d)))
  :hints (("Goal" :in-theory (e/d (fn-bpfs-fragment fn-bpfs-primary fn-bpb-bundlep
                                   fn-bpb-splitp fn-bpb-payload-blockp)
                                  (fn-bpf-fragment-block fn-bpfs-base fn-bpfs-total
                                   fn-bpfs-cuttablep fn-bpb-payload fn-bpb-datap
                                   fn-bpp-timep fn-bpp-blockp fn-bpb-blockp
                                   fn-bpb-block-listp fn-bpb-numbers-distinctp
                                   fn-bpfs-primary-coordinates-are-times))
           :use ((:instance fn-bpfs-primary-coordinates-are-times)
                 (:instance fn-bpfs-primary-coordinates-are-times (o (len (fn-bpb-payload b))))
                 (:instance fn-bpf-fragment-block-is-a-block
                            (b (fn-bpb-bundle-primary b))
                            (offset (+ (fn-bpfs-base (fn-bpb-bundle-primary b)) o))
                            (total (fn-bpfs-total (fn-bpb-bundle-primary b)
                                                  (len (fn-bpb-payload b)))))))))

(defthm fn-bpfs-encode-is-true-list
  (true-listp (fn-bpb-encode b))
  :hints (("Goal" :in-theory (enable fn-bpb-encode))))

(defthm fn-bpfs-fragment-decodes
  (implies (and (fn-bpb-bundlep b) (fn-bpfs-cuttablep b)
                (natp o) (<= o (len (fn-bpb-payload b)))
                (fn-bpb-datap d))
           (equal (fn-bpb-decode (fn-bpb-encode (fn-bpfs-fragment b o d))
                                 (len (fn-bpb-encode (fn-bpfs-fragment b o d))))
                  (fn-cbor-ok (fn-bpfs-fragment b o d) nil)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                              '(natp (:type-prescription len)))
           :use ((:instance fn-bpb-decode-of-encode
                            (bundle (fn-bpfs-fragment b o d))
                            (limit (len (fn-bpb-encode (fn-bpfs-fragment b o d)))))
                 (:instance fn-bpfs-fragment-is-a-bundle)
                 (:instance fn-bpfs-encode-is-true-list (b (fn-bpfs-fragment b o d)))
                 (:instance fn-cbor-at-mostp-from-length
                            (xs (fn-bpb-encode (fn-bpfs-fragment b o d)))
                            (bound (len (fn-bpb-encode (fn-bpfs-fragment b o d)))))))))

(defthm fn-bpfs-fragment-parts
  (and (equal (fn-bpb-bundle-primary (fn-bpfs-fragment b o d))
              (fn-bpf-fragment-block (fn-bpb-bundle-primary b)
                                     (+ (fn-bpfs-base (fn-bpb-bundle-primary b)) o)
                                     (fn-bpfs-total (fn-bpb-bundle-primary b)
                                                    (len (fn-bpb-payload b)))))
       (equal (fn-bpb-bundle-blocks (fn-bpfs-fragment b o d))
              (fn-bpb-bundle-blocks b))
       (equal (fn-bpb-payload (fn-bpfs-fragment b o d)) d))
  :hints (("Goal" :in-theory (e/d (fn-bpfs-fragment fn-bpfs-primary fn-bpb-payload)
                                  (fn-bpf-fragment-block fn-bpfs-base fn-bpfs-total)))))

; The reassembly views of a cut: consecutive extents of the payload at the
; parent's ADU coordinates.
(defun fn-bpfs-extents (payload from chunk total)
  (declare (xargs :guard (and (true-listp payload) (natp from) (natp chunk))
                  :measure (len payload)))
  (if (or (atom payload) (zp chunk))
      nil
    (let ((n (min chunk (len payload))))
      (cons (fn-bpf-make from (take n payload) total)
            (fn-bpfs-extents (nthcdr n payload) (+ from n) chunk total)))))

(defthm fn-bpfs-views-of-cons
  (equal (fn-bpfs-views (cons w rest))
         (let* ((b (fn-cbor-result-value (fn-bpb-decode w (len w))))
                (p (fn-bpb-bundle-primary b)))
           (cons (fn-bpf-make (fn-bpp-fragment-offset p) (fn-bpb-payload b)
                              (fn-bpp-total-adu-length p))
                 (fn-bpfs-views rest)))))

(defthm fn-bpfs-views-of-atom
  (implies (atom wires) (equal (fn-bpfs-views wires) nil)))

(defthm fn-bpfs-extents-step
  (implies (and (consp payload) (posp chunk))
           (equal (fn-bpfs-extents payload from chunk total)
                  (cons (fn-bpf-make from (take (min chunk (len payload)) payload) total)
                        (fn-bpfs-extents (nthcdr (min chunk (len payload)) payload)
                                         (+ from (min chunk (len payload)))
                                         chunk total)))))

(defthm fn-bpfs-extents-of-atom
  (implies (or (atom payload) (zp chunk))
           (equal (fn-bpfs-extents payload from chunk total) nil)))

(defthm fn-bpfs-cut-step
  (implies (and (consp payload) (posp chunk))
           (equal (fn-bpfs-cut b payload off chunk)
                  (cons (fn-bpb-encode
                         (fn-bpfs-fragment b off (take (min chunk (len payload)) payload)))
                        (fn-bpfs-cut b (nthcdr (min chunk (len payload)) payload)
                                     (+ off (min chunk (len payload))) chunk)))))

(defthm fn-bpfs-cut-of-atom
  (implies (or (atom payload) (zp chunk))
           (equal (fn-bpfs-cut b payload off chunk) nil)))

(defthm fn-bpfs-views-of-cut
  (implies (and (fn-bpb-bundlep b) (fn-bpfs-cuttablep b)
                (fn-cbor-octet-listp payload) (natp off)
                (equal (+ off (len payload)) (len (fn-bpb-payload b))))
           (equal (fn-bpfs-views (fn-bpfs-cut b payload off chunk))
                  (fn-bpfs-extents payload
                                   (+ (fn-bpfs-base (fn-bpb-bundle-primary b)) off)
                                   chunk
                                   (fn-bpfs-total (fn-bpb-bundle-primary b)
                                                  (len (fn-bpb-payload b))))))
  :hints (("Goal" :induct (fn-bpfs-cut b payload off chunk)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-bpfs-views-of-cons fn-bpfs-views-of-atom car-cons cdr-cons fn-bpfs-extents-step fn-bpfs-cut-step fn-bpfs-extents-of-atom fn-bpfs-cut-of-atom posp associativity-of-+
                         fn-bpfs-fragment-decodes fn-bpfs-fragment-parts
                         fn-bpfs-fragment-block-fields fn-cbor-ok
                         fn-cbor-result-value fn-bpf-make
                         fn-bpfs-len-of-take fn-bpfs-len-of-nthcdr
                         fn-bpfs-nthcdr-of-octets min nfix natp zp atom
                         (:type-prescription len) (:induction fn-bpfs-cut))))
          ("Subgoal *1/2" :use ((:instance fn-bpfs-take-is-data
                                           (xs payload) (n (min chunk (len payload))))
                                (:instance fn-bpfs-bundle-parts)
                                (:instance fn-bpfs-datap-bound (d (fn-bpb-payload b)))))))

; -----------------------------------------------------------------------------
; Exact reassembly on the canvas, with no data cap.

(defthm fn-bpfs-cell-at-of-cons
  (equal (fn-bpf-cell-at (cons f rest) i)
         (fn-bpf-merge-cell (fn-bpf-cell-of f i) (fn-bpf-cell-at rest i))))

(defthm fn-bpfs-cell-at-of-atom
  (implies (atom fs) (equal (fn-bpf-cell-at fs i) :gap)))

(defthm fn-bpfs-cell-of-make
  (equal (fn-bpf-cell-of (fn-bpf-make from bytes total) i)
         (if (and (<= from i) (< i (+ from (len bytes))))
             (nth (- i from) bytes)
           :gap)))

(defthm fn-bpfs-merge-cell-gaps
  (and (equal (fn-bpf-merge-cell x :gap) x)
       (equal (fn-bpf-merge-cell :gap y) y)))

(defthm fn-bpfs-nth-of-take
  (implies (and (natp i) (natp n) (< i n))
           (equal (nth i (take n xs)) (nth i xs))))

(defthm fn-bpfs-nth-of-nthcdr
  (implies (and (natp i) (natp n))
           (equal (nth i (nthcdr n xs)) (nth (+ i n) xs))))

(defthm fn-bpfs-extents-below-are-gaps
  (implies (and (natp from) (natp i) (< i from))
           (equal (fn-bpf-cell-at (fn-bpfs-extents payload from chunk total) i)
                  :gap))
  :hints (("Goal" :induct (fn-bpfs-extents payload from chunk total)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-bpfs-extents-step fn-bpfs-extents-of-atom
                         fn-bpfs-cell-at-of-cons fn-bpfs-cell-at-of-atom
                         fn-bpfs-cell-of-make fn-bpfs-merge-cell-gaps
                         fn-bpfs-len-of-take min natp posp zp nfix
                         (:type-prescription len)
                         (:induction fn-bpfs-extents))))))

(defthm fn-bpfs-cancel-shift
  (implies (and (acl2-numberp a) (acl2-numberp b) (acl2-numberp c))
           (equal (+ a b (- (+ a c))) (+ b (- c))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(commutativity-of-+ associativity-of-+
                                               commutativity-2-of-+ inverse-of-+
                                               unicity-of-0 distributivity-of-minus-over-+
                                               fix)))))

(defthm fn-bpfs-extents-cell
  (implies (and (natp from) (natp i) (posp chunk)
                (<= from i) (< i (+ from (len payload))))
           (equal (fn-bpf-cell-at (fn-bpfs-extents payload from chunk total) i)
                  (nth (- i from) payload)))
  :hints (("Goal" :induct (fn-bpfs-extents payload from chunk total)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-bpfs-extents-step fn-bpfs-extents-of-atom
                         fn-bpfs-cell-at-of-cons fn-bpfs-cell-at-of-atom
                         fn-bpfs-cell-of-make fn-bpfs-merge-cell-gaps
                         fn-bpfs-extents-below-are-gaps
                         fn-bpfs-nth-of-take fn-bpfs-nth-of-nthcdr
                         fn-bpfs-len-of-take fn-bpfs-len-of-nthcdr
                         min natp posp zp nfix fix len
                         commutativity-of-+ associativity-of-+ commutativity-2-of-+
                         unicity-of-0 inverse-of-+ fn-bpfs-cancel-shift
                         (:type-prescription len)
                         (:induction fn-bpfs-extents))))))

(defthm fn-bpfs-car-of-nthcdr
  (equal (car (nthcdr k xs)) (nth k xs))
  :hints (("Goal" :induct (nthcdr k xs) :expand ((nth k xs))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(nthcdr nth zp natp nfix fix commutativity-of-+
                                        (:induction nthcdr) car-cons cdr-cons)))))

(defthm fn-bpfs-cdr-of-nthcdr
  (implies (natp k)
           (equal (cdr (nthcdr k xs)) (nthcdr (+ 1 k) xs)))
  :hints (("Goal" :induct (nthcdr k xs) :expand ((nthcdr (+ 1 k) xs))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(nthcdr zp natp nfix fix
                                        (:induction nthcdr) car-cons cdr-cons
                                        commutativity-of-+ associativity-of-+
                                        commutativity-2-of-+ inverse-of-+ unicity-of-0
                                        fold-consts-in-+)))))

(defthm fn-bpfs-take-of-nthcdr-step
  (implies (and (natp k) (posp n))
           (equal (take n (nthcdr k xs))
                  (cons (nth k xs) (take (- n 1) (nthcdr (+ 1 k) xs)))))
  :hints (("Goal" :expand ((take n (nthcdr k xs)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-bpfs-car-of-nthcdr fn-bpfs-cdr-of-nthcdr
                                        zp natp posp nfix fix)))))

(defthm fn-bpfs-canvas-of-extents-range
  (implies (and (natp from) (natp s) (natp n) (posp chunk)
                (<= from s) (<= (+ s n) (+ from (len payload))))
           (equal (fn-bpf-canvas (fn-bpfs-extents payload from chunk total) s n)
                  (take n (nthcdr (- s from) payload))))
  :hints (("Goal" :induct (fn-bpf-canvas (fn-bpfs-extents payload from chunk total) s n)
           :in-theory (union-theories
                       (theory 'ground-zero)
                       '(fn-bpf-canvas fn-bpfs-extents-cell fn-bpfs-take-of-nthcdr-step
                         fn-bpfs-cancel-shift (:induction fn-bpf-canvas))))))

(defthm fn-bpfs-take-of-len
  (implies (true-listp xs) (equal (take (len xs) xs) xs))
  :hints (("Goal" :induct (len xs)
           :in-theory (union-theories (theory 'ground-zero) '((:induction len))))))

; Exact reassembly, with no data cap: the canvas of the extents at the
; parent's ADU offset is the parent's payload.
(defthm fn-bpfs-canvas-of-extents
  (implies (and (true-listp payload) (natp from) (posp chunk))
           (equal (fn-bpf-canvas (fn-bpfs-extents payload from chunk total)
                                 from (len payload))
                  payload))
  :hints (("Goal" :use ((:instance fn-bpfs-canvas-of-extents-range
                                   (s from) (n (len payload))))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-bpfs-take-of-len)))))

; -----------------------------------------------------------------------------
; The plan's answer, unfolded once for the keystones below.

(defun fn-bpfs-chunk (bundle mru)
  (declare (xargs :guard (and (fn-bpb-bundlep bundle) (natp mru)) :verify-guards nil))
  (- mru (+ 8 (fn-bpfs-overhead bundle))))

; What a :fragments answer is: the cut of the decoded parent's payload.
(defthm fn-bpfs-plan-fragments-unfold
  (implies (equal (car (fn-bpfs-plan wire mru)) :fragments)
           (let ((parent (fn-bpfs-parent wire)))
             (and (fn-bpb-bundlep parent)
                  (fn-bpfs-cuttablep parent)
                  (consp (fn-bpb-payload parent))
                  (natp mru)
                  (posp (fn-bpfs-chunk parent mru))
                  (equal (cdr (fn-bpfs-plan wire mru))
                         (fn-bpfs-cut parent (fn-bpb-payload parent) 0
                                      (fn-bpfs-chunk parent mru))))))
  :hints (("Goal" :in-theory (disable fn-bpfs-cut fn-bpb-decode fn-bpb-bundlep
                                      fn-bpb-payload fn-bpp-no-fragmentp)
           :use ((:instance fn-bpb-decode-yields-bundle (octets wire) (limit (len wire)))))))

; -----------------------------------------------------------------------------
; Keystone: exact reassembly.  The fragments' decoded views draw the parent's
; payload on the reassembly canvas at the parent's ADU offset, and all carry
; the parent's total.  No data cap: nothing bounds the payload length or the
; number of fragments here.

(defthm fn-bpfs-octets-are-a-true-list
  (implies (fn-cbor-octet-listp xs) (true-listp xs))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))

(defthm fn-bpfs-base-is-natural
  (natp (fn-bpfs-base p))
  :hints (("Goal" :in-theory (enable fn-bpfs-base)))
  :rule-classes :type-prescription)

(defthm fn-bpfs-extents-same-total
  (fn-bpf-same-total (fn-bpfs-extents payload from chunk total) total)
  :hints (("Goal" :induct (fn-bpfs-extents payload from chunk total)
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-bpfs-extents-step fn-bpfs-extents-of-atom
                                        fn-bpf-same-total fn-bpf-total fn-bpf-make
                                        (:induction fn-bpfs-extents))))))

(defthm fn-bpfs-plan-fragments-reassemble-exactly
  (implies (equal (car (fn-bpfs-plan wire mru)) :fragments)
           (let* ((parent (fn-bpfs-parent wire))
                  (p (fn-bpb-bundle-primary parent))
                  (payload (fn-bpb-payload parent))
                  (views (fn-bpfs-views (cdr (fn-bpfs-plan wire mru)))))
             (and (equal (fn-bpf-canvas views (fn-bpfs-base p) (len payload))
                         payload)
                  (fn-bpf-same-total views (fn-bpfs-total p (len payload))))))
  :hints (("Goal"
           :use ((:instance fn-bpfs-plan-fragments-unfold)
                 (:instance fn-bpfs-views-of-cut
                            (b (fn-bpfs-parent wire))
                            (payload (fn-bpb-payload (fn-bpfs-parent wire)))
                            (off 0) (chunk (fn-bpfs-chunk (fn-bpfs-parent wire) mru)))
                 (:instance fn-bpfs-canvas-of-extents
                            (payload (fn-bpb-payload (fn-bpfs-parent wire)))
                            (from (fn-bpfs-base (fn-bpb-bundle-primary (fn-bpfs-parent wire))))
                            (chunk (fn-bpfs-chunk (fn-bpfs-parent wire) mru))
                            (total (fn-bpfs-total (fn-bpb-bundle-primary (fn-bpfs-parent wire))
                                                  (len (fn-bpb-payload (fn-bpfs-parent wire))))))
                 (:instance fn-bpfs-payload-is-octets (b (fn-bpfs-parent wire))))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-bpfs-octets-are-a-true-list
                                        fn-bpfs-base-is-natural
                                        fn-bpfs-extents-same-total)))))

; -----------------------------------------------------------------------------
; Keystone: every fragment decodes, carries the parent's extension blocks and
; the fragment flag, keeps the parent's ADU identity, and (a whole parent)
; unfragments to the parent's primary block.

(defun fn-bpfs-restoresp (wires parent)
  (declare (xargs :guard (and (true-listp wires) (fn-bpb-bundlep parent))
                  :verify-guards nil))
  (if (atom wires)
      t
    (let* ((r (fn-bpb-decode (car wires) (len (car wires))))
           (f (fn-cbor-result-value r))
           (p (fn-bpb-bundle-primary parent))
           (fp (fn-bpb-bundle-primary f)))
      (and (fn-cbor-result-okp r)
           (equal (fn-bpb-bundle-blocks f) (fn-bpb-bundle-blocks parent))
           (fn-bpp-fragmentp (fn-bpp-flags fp))
           (equal (fn-bpp-adu-key fp) (fn-bpp-adu-key p))
           (or (fn-bpp-fragmentp (fn-bpp-flags p))
               (equal (fn-bpf-unfragment-block fp) p))
           (fn-bpfs-restoresp (cdr wires) parent)))))

(defthm fn-bpfs-fragment-restores
  (implies (and (fn-bpb-bundlep b) (fn-bpfs-cuttablep b)
                (natp o) (<= o (len (fn-bpb-payload b)))
                (fn-bpb-datap d))
           (let* ((w (fn-bpb-encode (fn-bpfs-fragment b o d)))
                  (r (fn-bpb-decode w (len w)))
                  (f (fn-cbor-result-value r))
                  (p (fn-bpb-bundle-primary b))
                  (fp (fn-bpb-bundle-primary f)))
             (and (fn-cbor-result-okp r)
                  (equal (fn-bpb-bundle-blocks f) (fn-bpb-bundle-blocks b))
                  (fn-bpp-fragmentp (fn-bpp-flags fp))
                  (equal (fn-bpp-adu-key fp) (fn-bpp-adu-key p))
                  (or (fn-bpp-fragmentp (fn-bpp-flags p))
                      (equal (fn-bpf-unfragment-block fp) p)))))
  :hints (("Goal"
           :use ((:instance fn-bpfs-fragment-decodes)
                 (:instance fn-bpfs-fragment-parts)
                 (:instance fn-bpfs-bundle-parts)
                 (:instance fn-bpfs-cuttable-flags)
                 (:instance fn-bpfs-primary-coordinates-are-times)
                 (:instance fn-bpfs-primary-coordinates-are-times
                            (o (len (fn-bpb-payload b))))
                 (:instance fn-bpf-fragment-block-sets-the-fragment-flag
                            (b (fn-bpb-bundle-primary b))
                            (offset (+ (fn-bpfs-base (fn-bpb-bundle-primary b)) o))
                            (total (fn-bpfs-total (fn-bpb-bundle-primary b)
                                                  (len (fn-bpb-payload b)))))
                 (:instance fn-bpf-fragment-block-preserves-adu-key
                            (b (fn-bpb-bundle-primary b))
                            (offset (+ (fn-bpfs-base (fn-bpb-bundle-primary b)) o))
                            (total (fn-bpfs-total (fn-bpb-bundle-primary b)
                                                  (len (fn-bpb-payload b)))))
                 (:instance fn-bpf-whole-fragment-unfragments-to-parent
                            (parent (fn-bpb-bundle-primary b))
                            (offset (+ (fn-bpfs-base (fn-bpb-bundle-primary b)) o))
                            (total (fn-bpfs-total (fn-bpb-bundle-primary b)
                                                  (len (fn-bpb-payload b))))))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-cbor-ok fn-cbor-result-okp fn-cbor-result-value
                                        fn-cbor-ag-car fn-bpp-timep)))))

(defthm fn-bpfs-restoresp-of-cons
  (equal (fn-bpfs-restoresp (cons w rest) parent)
         (let* ((r (fn-bpb-decode w (len w)))
                (f (fn-cbor-result-value r))
                (p (fn-bpb-bundle-primary parent))
                (fp (fn-bpb-bundle-primary f)))
           (and (fn-cbor-result-okp r)
                (equal (fn-bpb-bundle-blocks f) (fn-bpb-bundle-blocks parent))
                (fn-bpp-fragmentp (fn-bpp-flags fp))
                (equal (fn-bpp-adu-key fp) (fn-bpp-adu-key p))
                (or (fn-bpp-fragmentp (fn-bpp-flags p))
                    (equal (fn-bpf-unfragment-block fp) p))
                (fn-bpfs-restoresp rest parent))))
  :hints (("Goal" :expand ((fn-bpfs-restoresp (cons w rest) parent))
           :in-theory (theory 'ground-zero))))

(defthm fn-bpfs-cut-restores
  (implies (and (fn-bpb-bundlep b) (fn-bpfs-cuttablep b)
                (fn-cbor-octet-listp payload) (natp off)
                (equal (+ off (len payload)) (len (fn-bpb-payload b))))
           (fn-bpfs-restoresp (fn-bpfs-cut b payload off chunk) b))
  :hints (("Goal" :induct (fn-bpfs-cut b payload off chunk)
           :in-theory (union-theories
                       (theory 'ground-zero)
                       '(fn-bpfs-restoresp-of-cons fn-bpfs-cut-step fn-bpfs-cut-of-atom
                         fn-bpfs-restoresp fn-bpfs-len-of-take fn-bpfs-len-of-nthcdr
                         fn-bpfs-nthcdr-of-octets (:induction fn-bpfs-cut))))
          ("Subgoal *1/2" :use ((:instance fn-bpfs-fragment-restores
                                           (o off)
                                           (d (take (min chunk (len payload)) payload)))
                                (:instance fn-bpfs-take-is-data
                                           (xs payload) (n (min chunk (len payload))))
                                (:instance fn-bpfs-bundle-parts)
                                (:instance fn-bpfs-datap-bound (d (fn-bpb-payload b)))))))

(defthm fn-bpfs-plan-fragments-restore-parent
  (implies (equal (car (fn-bpfs-plan wire mru)) :fragments)
           (fn-bpfs-restoresp (cdr (fn-bpfs-plan wire mru)) (fn-bpfs-parent wire)))
  :hints (("Goal"
           :use ((:instance fn-bpfs-plan-fragments-unfold)
                 (:instance fn-bpfs-cut-restores
                            (b (fn-bpfs-parent wire))
                            (payload (fn-bpb-payload (fn-bpfs-parent wire)))
                            (off 0) (chunk (fn-bpfs-chunk (fn-bpfs-parent wire) mru)))
                 (:instance fn-bpfs-payload-is-octets (b (fn-bpfs-parent wire))))
           :in-theory (theory 'ground-zero))))

; -----------------------------------------------------------------------------
; The receiver's executable reassembler `fn-bpf-reassemble` (through
; `fn-bpf-reassemble-fast`, bp-node-fragment-family) keeps its caps
; *fn-bpf-max-length* and *fn-bpf-max-fragments*; within them it answers
; (:ok payload) on these fragments.

(defthm fn-bpfs-consp-of-take
  (implies (posp n) (consp (take n xs)))
  :hints (("Goal" :expand ((take n xs)))))

(defthm fn-bpfs-len-positive
  (implies (consp x) (< 0 (len x)))
  :rule-classes :linear)

(defthm fn-bpfs-extents-are-fragments
  (implies (and (fn-cbor-octet-listp payload) (natp from) (posp chunk)
                (natp total) (<= (+ from (len payload)) total)
                (<= total *fn-bpf-max-length*))
           (fn-bpf-fragment-listp (fn-bpfs-extents payload from chunk total)))
  :hints (("Goal" :induct (fn-bpfs-extents payload from chunk total)
           :in-theory (union-theories
                       (theory 'ground-zero)
                       '(fn-bpfs-extents-step fn-bpfs-extents-of-atom
                         fn-bpf-fragment-listp fn-bpf-fragmentp fn-bpf-make
                         fn-bpf-offset fn-bpf-bytes fn-bpf-total
                         fn-bpfs-take-of-octets fn-bpfs-len-of-take
                         fn-bpfs-nthcdr-of-octets fn-bpfs-len-of-nthcdr fn-bpfs-consp-of-take fn-bpfs-len-positive
                         (:induction fn-bpfs-extents))))))

(defthm fn-bpfs-len-of-views
  (equal (len (fn-bpfs-views wires)) (len wires))
  :hints (("Goal" :induct (len wires)
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-bpfs-views-of-cons fn-bpfs-views-of-atom
                                        (:induction len))))))

(defthm fn-bpfs-whole-parent-coordinates
  (implies (not (fn-bpp-fragmentp (fn-bpp-flags p)))
           (and (equal (fn-bpfs-base p) 0)
                (equal (fn-bpfs-total p n) (nfix n))))
  :hints (("Goal" :in-theory (enable fn-bpfs-base fn-bpfs-total))))

(defthm fn-bpfs-extents-consp
  (implies (and (consp payload) (posp chunk))
           (consp (fn-bpfs-extents payload from chunk total)))
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
                                             '(fn-bpfs-extents-step)))))

; The receiver's executable reassembler keeps its caps; within them it
; answers exactly the parent's payload on these fragments.
(defthm fn-bpfs-plan-fragments-reassemble-within-caps
  (implies (and (equal (car (fn-bpfs-plan wire mru)) :fragments)
                (not (fn-bpp-fragmentp
                      (fn-bpp-flags (fn-bpb-bundle-primary (fn-bpfs-parent wire)))))
                (<= (len (fn-bpb-payload (fn-bpfs-parent wire))) *fn-bpf-max-length*)
                (<= (len (cdr (fn-bpfs-plan wire mru))) *fn-bpf-max-fragments*))
           (equal (fn-bpf-reassemble (fn-bpfs-views (cdr (fn-bpfs-plan wire mru)))
                                     (len (fn-bpb-payload (fn-bpfs-parent wire))))
                  (list :ok (fn-bpb-payload (fn-bpfs-parent wire)))))
  :hints (("Goal"
           :use ((:instance fn-bpfs-plan-fragments-unfold)
                 (:instance fn-bpfs-views-of-cut
                            (b (fn-bpfs-parent wire))
                            (payload (fn-bpb-payload (fn-bpfs-parent wire)))
                            (off 0) (chunk (fn-bpfs-chunk (fn-bpfs-parent wire) mru)))
                 (:instance fn-bpfs-whole-parent-coordinates
                            (p (fn-bpb-bundle-primary (fn-bpfs-parent wire)))
                            (n (len (fn-bpb-payload (fn-bpfs-parent wire)))))
                 (:instance fn-bpfs-canvas-of-extents
                            (payload (fn-bpb-payload (fn-bpfs-parent wire)))
                            (from 0)
                            (chunk (fn-bpfs-chunk (fn-bpfs-parent wire) mru))
                            (total (len (fn-bpb-payload (fn-bpfs-parent wire)))))
                 (:instance fn-bpfs-extents-are-fragments
                            (payload (fn-bpb-payload (fn-bpfs-parent wire)))
                            (from 0)
                            (chunk (fn-bpfs-chunk (fn-bpfs-parent wire) mru))
                            (total (len (fn-bpb-payload (fn-bpfs-parent wire)))))
                 (:instance fn-bpfs-extents-consp
                            (payload (fn-bpb-payload (fn-bpfs-parent wire)))
                            (from 0)
                            (chunk (fn-bpfs-chunk (fn-bpfs-parent wire) mru))
                            (total (len (fn-bpb-payload (fn-bpfs-parent wire)))))
                 (:instance fn-bpfs-extents-same-total
                            (payload (fn-bpb-payload (fn-bpfs-parent wire)))
                            (from 0)
                            (chunk (fn-bpfs-chunk (fn-bpfs-parent wire) mru))
                            (total (len (fn-bpb-payload (fn-bpfs-parent wire)))))
                 (:instance fn-bpfs-len-of-views (wires (cdr (fn-bpfs-plan wire mru))))
                 (:instance fn-bpfs-payload-is-octets (b (fn-bpfs-parent wire)))
                 (:instance fn-bpf-no-marker-in-octet-list
                            (cells (fn-bpb-payload (fn-bpfs-parent wire)))
                            (from 0) (marker :conflict))
                 (:instance fn-bpf-no-marker-in-octet-list
                            (cells (fn-bpb-payload (fn-bpfs-parent wire)))
                            (from 0) (marker :gap)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-bpf-reassemble fn-bpf-inputsp
                                        fn-bpfs-octets-are-a-true-list
                                        fn-bpfs-len-positive)))))

; -----------------------------------------------------------------------------
; Guards: the plan the host calls runs guard-verified.  `fn-bpfs-parent`,
; `-views`, `-restoresp` and `-chunk` are the keystones' specification
; vocabulary; the host never calls them.

(defthm fn-bpfs-primary-is-a-true-list
  (implies (fn-bpp-blockp p) (true-listp p))
  :hints (("Goal" :in-theory (enable fn-bpp-blockp)))
  :rule-classes :forward-chaining)
(verify-guards fn-bpfs-primary)
(verify-guards fn-bpfs-payload-block)
(verify-guards fn-bpfs-fragment
  :hints (("Goal" :in-theory (enable fn-bpfs-bundle-parts))))
(verify-guards fn-bpfs-cuttablep
  :hints (("Goal" :use ((:instance fn-bpfs-bundle-parts (b bundle))
                        (:instance fn-bpfs-primary-numeric-fields
                                   (p (fn-bpb-bundle-primary bundle))))
           :in-theory (disable fn-bpfs-bundle-parts fn-bpfs-primary-numeric-fields
                               fn-bpb-bundlep fn-bpp-blockp))))

(verify-guards fn-bpfs-overhead
  :hints (("Goal" :use ((:instance fn-bpfs-fragment-is-a-bundle
                                   (b bundle) (o (len (fn-bpb-payload bundle))) (d nil)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-bpfs-nil-is-data)))))
(verify-guards fn-bpfs-cut
  :hints (("Goal" :use ((:instance fn-bpfs-fragment-is-a-bundle
                                   (b bundle) (o offset)
                                   (d (take (min chunk (len payload)) payload)))
                        (:instance fn-bpfs-take-is-data
                                   (xs payload) (n (min chunk (len payload))))
                        (:instance fn-bpfs-bundle-parts (b bundle))
                        (:instance fn-bpfs-datap-bound (d (fn-bpb-payload bundle))))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-bpfs-octets-are-a-true-list
                                        fn-bpfs-len-of-nthcdr fn-bpfs-nthcdr-of-octets
                                        fn-bpfs-len-positive)))))

(verify-guards fn-bpfs-plan
  :hints (("Goal" :use ((:instance fn-bpb-decode-yields-bundle (octets wire) (limit (len wire)))
                        (:instance fn-bpfs-payload-is-octets
                                   (b (fn-cbor-result-value (fn-bpb-decode wire (len wire)))))
                        (:instance fn-bpfs-bundle-parts
                                   (b (fn-cbor-result-value (fn-bpb-decode wire (len wire)))))
                        (:instance fn-bpfs-primary-numeric-fields
                                   (p (fn-bpb-bundle-primary
                                       (fn-cbor-result-value (fn-bpb-decode wire (len wire)))))))
           :in-theory (e/d (fn-bpfs-primary-is-a-true-list)
                           (fn-bpb-decode fn-bpfs-cut fn-bpfs-overhead fn-bpb-bundlep
                            fn-bpfs-cuttablep fn-bpb-payload fn-bpp-no-fragmentp
                            fn-bpfs-bundle-parts fn-bpfs-primary-numeric-fields
                            fn-bpp-blockp fn-cbor-octet-listp len)))))

; -----------------------------------------------------------------------------
; The job's outcome over its fragments.  host/native/bp-service.lisp
; `fnn-bps-send-effect` sends the fragments in order, one transfer each, and
; stops at the first that is not accepted; this reads each further
; transfer.  After the first fragment has gone, a transfer that certainly
; did not happen (:failed, a connect that sent nothing) leaves the job
; :uncertain: earlier fragments may be held by the receiver.

(defun fn-bpfs-fragment-outcome (index outcome)
  (declare (xargs :guard (natp index)))
  (if (and (< 1 index) (equal outcome :failed)) :uncertain outcome))

(defthm fn-bpfs-fragment-outcome-after-first-is-never-failed-by-definition
  (implies (< 1 index)
           (not (equal (fn-bpfs-fragment-outcome index outcome) :failed))))

(defthm fn-bpfs-fragment-outcome-accepted-iff-accepted-by-definition
  (equal (equal (fn-bpfs-fragment-outcome index outcome) :accepted)
         (equal outcome :accepted)))
