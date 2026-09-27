; fn: compressed records in the log (lane compression-extents, brief C2 of
; planning/evidence/article-compression-2026-09-27.md section 6; PRF-326).
; Prefix `fn-lzr-'.
;
; THE FRAME.  The record log holds each event as its codec's octets R (an
; article `fn-r', a store event `fn-e').  A compressed article is held as
;
;   Z = 'fn-z' head (5) ++ u32 DICT-ID ++ u32 K ++ u32 N ++ u32 |STUB|
;       ++ STUB ++ C
;
; where [K, K+N) is R's payload span, STUB is R without it and C is an LZ4
; block (books/payload-lz.lisp) that decodes, against dictionary DICT-ID, to
; exactly those N octets.  `fn-lzr-expand' gives R back:
; STUB[0,K) ++ decode(C) ++ STUB[K..].  The frame sits between the record
; codec and the log: the codec, its seam (books/records-seam.lisp), the
; meaning of a record's payload and the log kernel are untouched, and a
; record that is not a frame passes through unchanged.
;
; THE SEAL.  `fn-lzr-seal' is the one producer of a frame.  It runs the
; proved decoder over the host's CANDIDATE (liblz4-HC's output: untrusted)
; and frames R only when the candidate decodes to R's span, the span is at
; least the profile's threshold MIN (0: never) and the frame is shorter than
; R (`fn-lzr-compress-p'); otherwise R is kept.  KEYSTONE
; `fn-lzr-expand-of-seal': the expansion of the seal is R, whatever the
; candidate, the threshold or the span.  (A record that happens to begin
; with the frame's head is framed with an empty span, so the keystone needs
; no hypothesis on R beyond its octets and its length.)
;
; WHICH BYTES THE DIGESTS COVER (D25: the authored bytes are the article).
; The content identity, the Message-ID, a signature and Cancel-Lock are all
; over the ORIGINAL octets: they are computed from the article before the
; seal (the owner's prepare), and a replay reads the record from the
; expansion, which is R exactly, so the record it decodes is the record that
; was sealed (`fn-lzr-replay-reads-the-sealed-record') and its payload is the
; authored article.  The log's frame trailer (books/store-log.lisp) covers Z:
; the durable octets.  The seal is what ties C to R.
;
; DICTIONARIES.  A table of (ID . OCTETS), each at most the LZ4 window
; (`fn-lzr-dictsp'); ID 0 is the empty dictionary.  `fn-lzr-dicts-add'
; refuses to rebind an ID to other octets (a dictionary is immutable once
; named: `fn-lzr-dicts-add-keeps-bindings').
;
; THE COMPRESSED EXTENT.  A frame at its PLACE in a log segment (the
; places of books/payload-extent.lisp) holds C contiguously at its end: the
; extent (FILE EOFF ELEN CPOFF CLEN TRAILER N DICT-ID).  `fn-lzr-extent-of'
; answers it only when C decodes to the record's payload.  The served read
; is `fn-lzr-read': the decode of C's durable octets.  KEYSTONE
; `fn-lzr-extent-read-denotes': when the log holds the frame at its place
; (A-DURABLE-EXTENT's faithful read), the read of the extent is the record's
; payload -- the composition of the LZ seal's check with the extent's.  A
; decode that fails is refused by name (:lz-decode), never served.

(in-package "ACL2")
(include-book "payload-lz-value")
(include-book "payload-commit-extent")
(include-book "records-seam")


; -----------------------------------------------------------------------------
; 1. u32 fields and the frame.

(defconst *fn-lzr-magic* '(68 102 110 45 122)) ; bstr(4) "fn-z"
(defconst *fn-lzr-head-len* 21)

(defun fn-lzr-u32p (n)
  (declare (xargs :guard t))
  (and (natp n) (< n 4294967296)))

(defun fn-lzr-u32 (n)
  (declare (xargs :guard t))
  (fn-cbor-u32-bytes (if (fn-lzr-u32p n) n 0)))

(defthm fn-lzr-u32-reads-back
  (implies (fn-lzr-u32p n)
           (equal (fn-arx-u32-list (append (fn-lzr-u32 n) rest)) n))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-from fn-cbor-octet-listp fn-cbor-octetp)
                                  (fn-cbor-u32-bytes))
           :use (fn-cbor-u32-from-u32-bytes fn-cbor-u32-bytes-are-octets
                 fn-cbor-u32-bytes-have-four-octets))))

(defthm fn-lzr-u32-octets
  (fn-cbor-octet-listp (fn-lzr-u32 n))
  :hints (("Goal" :in-theory (disable fn-cbor-u32-bytes)
           :use ((:instance fn-cbor-u32-bytes-are-octets (n (if (fn-lzr-u32p n) n 0)))))))

(defthm fn-lzr-len-u32
  (equal (len (fn-lzr-u32 n)) 4)
  :hints (("Goal" :in-theory (disable fn-cbor-u32-bytes)
           :use ((:instance fn-cbor-u32-bytes-have-four-octets (n (if (fn-lzr-u32p n) n 0)))))))

(in-theory (disable fn-lzr-u32))

(defun fn-lzr-frame (dict-id k n stub c)
  (declare (xargs :guard (and (true-listp stub) (true-listp c))))
  (append *fn-lzr-magic*
          (append (fn-lzr-u32 dict-id)
                  (append (fn-lzr-u32 k)
                          (append (fn-lzr-u32 n)
                                  (append (fn-lzr-u32 (len stub))
                                          (append stub c)))))))

(defun fn-lzr-magicp (z)
  (declare (xargs :guard (true-listp z)))
  (and (consp (nthcdr 4 z))
       (equal (take 5 z) *fn-lzr-magic*)))

; The frame's fields, or nil: (DICT-ID K N STUB C).
(defun fn-lzr-parse (z)
  (declare (xargs :guard (true-listp z)))
  (if (and (fn-lzr-magicp z) (<= *fn-lzr-head-len* (len z)))
      (let* ((z1 (nthcdr 5 z))
             (d (fn-arx-u32-list z1))
             (z2 (nthcdr 4 z1))
             (k (fn-arx-u32-list z2))
             (z3 (nthcdr 4 z2))
             (n (fn-arx-u32-list z3))
             (z4 (nthcdr 4 z3))
             (slen (fn-arx-u32-list z4))
             (body (nthcdr 4 z4)))
        (if (and (<= slen (len body)) (<= k slen))
            (list d k n (take slen body) (nthcdr slen body))
          nil))
    nil))

(local
 (defthm fn-lzr-len-take
   (equal (len (take n x)) (nfix n))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-lzr-true-listp-take
   (true-listp (take n x))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-lzr-true-listp-nthcdr
   (implies (true-listp x) (true-listp (nthcdr n x)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

;; The octet lists the frame is cut from.
(defthm fn-lzr-octets-of-nthcdr
  (implies (fn-cbor-octet-listp x) (fn-cbor-octet-listp (nthcdr k x)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm fn-lzr-octets-of-take
  (implies (and (fn-cbor-octet-listp x) (<= (nfix k) (len x)))
           (fn-cbor-octet-listp (take k x)))
  :hints (("Goal" :in-theory (enable take))))

(defthm fn-lzr-natp-u32-list
  (natp (fn-arx-u32-list xs))
  :rule-classes :type-prescription)

(defthm fn-lzr-parse-shape
  (implies (fn-lzr-parse z)
           (and (true-listp (fn-lzr-parse z))
                (natp (nth 0 (fn-lzr-parse z)))
                (natp (nth 1 (fn-lzr-parse z)))
                (natp (nth 2 (fn-lzr-parse z)))
                (<= (nth 1 (fn-lzr-parse z)) (len (nth 3 (fn-lzr-parse z))))
                (true-listp (nth 3 (fn-lzr-parse z)))
                (implies (true-listp z) (true-listp (nth 4 (fn-lzr-parse z))))))
  :hints (("Goal" :in-theory (disable fn-arx-u32-list take nthcdr))))

(defthm fn-lzr-parse-octets
  (implies (and (fn-cbor-octet-listp z) (fn-lzr-parse z))
           (and (fn-cbor-octet-listp (nth 3 (fn-lzr-parse z)))
                (fn-cbor-octet-listp (nth 4 (fn-lzr-parse z)))))
  :hints (("Goal" :in-theory (disable fn-arx-u32-list take nthcdr))))

(in-theory (disable fn-lzr-parse))

; -----------------------------------------------------------------------------
; 2. Dictionaries.

(defconst *fn-lzr-dict-max* 65536) ; the LZ4 window: an offset reaches 65,535 back

(defun fn-lzr-dictp (d)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp d) (<= (len d) *fn-lzr-dict-max*)))

(defun fn-lzr-dictsp (dicts)
  (declare (xargs :guard t))
  (if (atom dicts)
      (null dicts)
    (and (consp (car dicts))
         (fn-lzr-u32p (caar dicts))
         (fn-lzr-dictp (cdar dicts))
         (fn-lzr-dictsp (cdr dicts)))))

(defthm fn-lzr-dictsp-alistp
  (implies (fn-lzr-dictsp dicts) (alistp dicts)))

(defthm fn-lzr-dictsp-assoc-octets
  (implies (and (fn-lzr-dictsp dicts) (assoc-equal id dicts))
           (fn-cbor-octet-listp (cdr (assoc-equal id dicts)))))

; The initial table: ID 0, the empty dictionary.
(defun fn-lzr-dicts-initial ()
  (declare (xargs :guard t))
  (list (cons 0 nil)))

; Bind ID to OCTETS: (:ok DICTS') or a named refusal.  An ID already bound
; to the same octets is the same table; to other octets, refused.
(defun fn-lzr-dicts-add (dicts id octets)
  (declare (xargs :guard (fn-lzr-dictsp dicts)))
  (cond ((not (and (fn-lzr-u32p id) (fn-lzr-dictp octets)))
         (list :refused :lz-dictionary-format))
        ((assoc-equal id dicts)
         (if (equal (cdr (assoc-equal id dicts)) octets)
             (list :ok dicts)
           (list :refused :lz-dictionary-rebound)))
        (t (list :ok (cons (cons id octets) dicts)))))

(defthm fn-lzr-dicts-add-dictsp
  (implies (and (fn-lzr-dictsp dicts)
                (equal (car (fn-lzr-dicts-add dicts id octets)) :ok))
           (fn-lzr-dictsp (cadr (fn-lzr-dicts-add dicts id octets)))))

; Immutability: every binding survives an accepted add.
(defthm fn-lzr-dicts-add-keeps-bindings
  (implies (and (equal (car (fn-lzr-dicts-add dicts id octets)) :ok)
                (assoc-equal j dicts))
           (equal (assoc-equal j (cadr (fn-lzr-dicts-add dicts id octets)))
                  (assoc-equal j dicts))))

; -----------------------------------------------------------------------------
; 3. The decision, the seal and the expansion.

(defthm fn-lzr-dictsp-assoc-consp
  (implies (and (fn-lzr-dictsp dicts) (assoc-equal id dicts))
           (consp (assoc-equal id dicts))))

; Compress a span of N octets to C of CLEN octets: the profile's threshold
; MIN is set (0 never compresses), the span reaches it, and the frame is
; shorter than the record (the frame adds its 21-octet head: CLEN + 21 < N).
(defun fn-lzr-compress-p (min n clen)
  (declare (xargs :guard t))
  (and (posp min) (natp n) (natp clen)
       (<= min n)
       (< (+ clen *fn-lzr-head-len*) n)))

; Whether to run the encoder at all (the host asks before it encodes).
(defun fn-lzr-want-p (min n)
  (declare (xargs :guard t))
  (and (posp min) (natp n) (<= min n) (< *fn-lzr-head-len* n)))

(defun fn-lzr-seal (dict dict-id min r k n candidate)
  (declare (xargs :guard (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp r)
                              (fn-cbor-octet-listp candidate) (natp k) (natp n))))
  (cond ((and (fn-lzr-u32p dict-id) (fn-lzr-u32p k) (fn-lzr-u32p n)
              (fn-lzr-u32p (len r))
              (<= (+ k n) (len r))
              (fn-lzr-compress-p min n (len candidate))
              (equal (fn-lz-decode dict candidate n) (list :ok (take n (nthcdr k r)))))
         (fn-lzr-frame dict-id k n (append (take k r) (nthcdr (+ k n) r)) candidate))
        ((and (fn-lzr-magicp r) (fn-lzr-u32p dict-id) (fn-lzr-u32p (len r)))
         ;; R begins with the frame's head: an empty span keeps it unambiguous.
         (fn-lzr-frame dict-id 0 0 r (fn-lz-literal-block nil)))
        (t r)))

(defun fn-lzr-expand (dicts z)
  (declare (xargs :guard (and (fn-lzr-dictsp dicts) (fn-cbor-octet-listp z))
                  :guard-hints (("Goal" :in-theory (disable fn-lz-decode take nthcdr assoc-equal
                                                            fn-lzr-dictsp fn-lzr-magicp)))))
  (if (not (fn-lzr-magicp z))
      (list :ok z)
    (let ((p (fn-lzr-parse z)))
      (if (not p)
          (list :refused :lz-frame)
        (let ((e (assoc-equal (nth 0 p) dicts)))
          (if (not e)
              (list :refused :lz-dictionary)
            (let ((r (fn-lz-decode (cdr e) (nth 4 p) (nfix (nth 2 p))))
                  (k (nfix (nth 1 p)))
                  (stub (nth 3 p)))
              (if (eq (car r) :ok)
                  (list :ok (append (take k stub) (append (cadr r) (nthcdr k stub))))
                (list :refused :lz-decode)))))))))

; -----------------------------------------------------------------------------
; 4. The frame reads back.

(local
 (defthm fn-lzr-nthcdr-len-append
   (equal (nthcdr (len a) (append a b)) b)
   :hints (("Goal" :induct (len a) :in-theory (enable nthcdr)))))

(local
 (defthm fn-lzr-nthcdr-4-u32
   (equal (nthcdr 4 (append (fn-lzr-u32 x) b)) b)
   :hints (("Goal" :in-theory (disable fn-lzr-nthcdr-len-append)
            :use ((:instance fn-lzr-nthcdr-len-append (a (fn-lzr-u32 x))))))))

(local
 (defthm fn-lzr-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-lzr-take-len-append
   (implies (true-listp a) (equal (take (len a) (append a b)) a))
   :hints (("Goal" :induct (len a) :in-theory (enable take)))))

(defthm fn-lzr-magicp-of-frame
  (fn-lzr-magicp (fn-lzr-frame d k n stub c)))

(local
 (defthm fn-lzr-frame-after-magic
   (equal (nthcdr 5 (fn-lzr-frame d k n stub c))
          (append (fn-lzr-u32 d)
                  (append (fn-lzr-u32 k)
                          (append (fn-lzr-u32 n)
                                  (append (fn-lzr-u32 (len stub)) (append stub c))))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm fn-lzr-len-frame
  (equal (len (fn-lzr-frame d k n stub c))
         (+ *fn-lzr-head-len* (len stub) (len c))))

(in-theory (disable fn-lzr-frame))

(defthm fn-lzr-parse-of-frame
  (implies (and (fn-lzr-u32p d) (fn-lzr-u32p k) (fn-lzr-u32p n) (fn-lzr-u32p (len stub))
                (<= k (len stub)) (true-listp stub))
           (equal (fn-lzr-parse (fn-lzr-frame d k n stub c))
                  (list d k n stub c)))
  :hints (("Goal" :in-theory (e/d (fn-lzr-parse)
                                  (fn-lzr-magicp fn-arx-u32-list fn-lzr-u32p take nthcdr)))))

; -----------------------------------------------------------------------------
; 5. KEYSTONE: the expansion of the seal is the record.

(local
 (defthm fn-lzr-append-take-nthcdr
   (implies (<= (nfix k) (len r))
            (equal (append (take k r) (nthcdr k r)) r))
   :hints (("Goal" :in-theory (enable take nthcdr) :induct (nthcdr k r)))))

(local
 (defthm fn-lzr-nthcdr-nthcdr
   (implies (and (natp k) (natp n))
            (equal (nthcdr n (nthcdr k r)) (nthcdr (+ k n) r)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-lzr-len-nthcdr
   (implies (<= (nfix k) (len r))
            (equal (len (nthcdr k r)) (- (len r) (nfix k))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-lzr-take-of-append-len
   (implies (equal (nfix k) (len a))
            (equal (take k (append a b)) (true-list-fix a)))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-lzr-nthcdr-of-append-len2
   (implies (equal (nfix k) (len a))
            (equal (nthcdr k (append a b)) b))
   :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr k a)))))

(local
 (defthm fn-lzr-reassemble
   (implies (and (natp k) (natp n) (<= (+ k n) (len r)) (true-listp r))
            (equal (append (take k r) (append (take n (nthcdr k r)) (nthcdr (+ k n) r)))
                   r))
   :hints (("Goal" :in-theory (disable fn-lzr-nthcdr-nthcdr fn-lzr-append-take-nthcdr)
            :use ((:instance fn-lzr-append-take-nthcdr (k k) (r r))
                  (:instance fn-lzr-append-take-nthcdr (k n) (r (nthcdr k r)))
                  (:instance fn-lzr-nthcdr-nthcdr))))))

(local
 (defthm fn-lzr-decode-empty-literal
   (equal (fn-lz-decode dict '(0) 0) (list :ok nil))
   :hints (("Goal" :use ((:instance fn-lz-decode-of-literal-block (x nil)))))))

(local
 (defthm fn-lzr-expand-of-compressed
   (implies (and (equal (assoc-equal dict-id dicts) (cons dict-id dict))
                 (fn-lzr-u32p dict-id) (fn-lzr-u32p k) (fn-lzr-u32p n) (fn-lzr-u32p (len r))
                 (<= (+ k n) (len r))
                 (true-listp r)
                 (equal (fn-lz-decode dict candidate n) (list :ok (take n (nthcdr k r)))))
            (equal (fn-lzr-expand dicts (fn-lzr-frame dict-id k n
                                                      (append (take k r) (nthcdr (+ k n) r))
                                                      candidate))
                   (list :ok r)))
   :hints (("Goal" :in-theory (disable fn-lzr-magicp take nthcdr fn-lzr-reassemble)
            :use fn-lzr-reassemble))))

(local
 (defthm fn-lzr-expand-of-escape
   (implies (and (equal (assoc-equal dict-id dicts) (cons dict-id dict))
                 (fn-lzr-u32p dict-id) (fn-lzr-u32p (len r)) (true-listp r))
            (equal (fn-lzr-expand dicts (fn-lzr-frame dict-id 0 0 r '(0)))
                   (list :ok r)))
   :hints (("Goal" :in-theory (disable fn-lzr-magicp take nthcdr)))))

(local
 (defthm fn-lzr-expand-of-plain
   (implies (not (fn-lzr-magicp r))
            (equal (fn-lzr-expand dicts r) (list :ok r)))))

(defthm fn-lzr-expand-of-seal
  (implies (and (equal (assoc-equal dict-id dicts) (cons dict-id dict))
                (fn-lzr-u32p dict-id)
                (fn-lzr-u32p (len r))
                (fn-cbor-octet-listp r))
           (equal (fn-lzr-expand dicts (fn-lzr-seal dict dict-id min r k n candidate))
                  (list :ok r)))
  :hints (("Goal" :in-theory (e/d (fn-lzr-seal)
                                  (fn-lzr-expand fn-lzr-magicp take nthcdr fn-lzr-compress-p
                                   fn-lzr-u32p)))))

; -----------------------------------------------------------------------------
; 6. Which bytes the digests cover: the replay reads the sealed record.
;
; A record's encoding is at most the codec's u32 width, so it can be sealed.
(defthm fn-lzr-record-encode-u32
  (implies (fn-record-p w)
           (fn-lzr-u32p (len (fn-record-encode w))))
  :hints (("Goal" :use ((:instance fn-record-accepted-input-bounds
                                   (octets (fn-record-encode w)))
                        fn-record-encode-of-a-record-is-accepted)
           :in-theory (disable fn-record-encode-of-a-record-is-accepted))))

; The replay (the log's open) expands each record and decodes it with the
; codec: a sealed article decodes to exactly the record the owner sealed, so
; its payload -- the octets the content identity, the Message-ID's D25
; comparison, a signature and Cancel-Lock are computed over -- is the
; authored article, whether or not the log holds it compressed.
(defthm fn-lzr-replay-reads-the-sealed-record
  (implies (and (fn-record-p w)
                (equal (assoc-equal dict-id dicts) (cons dict-id dict))
                (fn-lzr-u32p dict-id))
           (let ((x (fn-lzr-expand dicts (fn-lzr-seal dict dict-id min (fn-record-encode w)
                                                      k n candidate))))
             (and (equal (car x) :ok)
                  (equal (fn-record-decode-exact (cadr x)) (list :ok w)))))
  :hints (("Goal" :in-theory (disable fn-lzr-expand fn-lzr-seal fn-lzr-u32p))))

; -----------------------------------------------------------------------------
; 7. The compressed extent and its read.
;
; A frame's C is its tail.
(local
 (defthm fn-lzr-nthcdr-4-nthcdr
   (equal (nthcdr 4 (nthcdr j z)) (nthcdr (+ 4 (nfix j)) z))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-lzr-len-minus-len-nthcdr
   (implies (<= (nfix j) (len z))
            (equal (- (len z) (len (nthcdr j z))) (nfix j)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm fn-lzr-parse-c-is-the-tail
  (implies (fn-lzr-parse z)
           (equal (nthcdr (- (len z) (len (nth 4 (fn-lzr-parse z)))) z)
                  (nth 4 (fn-lzr-parse z))))
  :hints (("Goal" :in-theory (e/d (fn-lzr-parse)
                                  (fn-lzr-magicp fn-arx-u32-list take fn-lzr-len-nthcdr len
                                   fn-lzr-len-minus-len-nthcdr))
           :use ((:instance fn-lzr-len-nthcdr (k 21) (r z))
                 (:instance fn-lzr-len-minus-len-nthcdr
                            (j (+ 21 (fn-arx-u32-list (nthcdr 17 z)))))))))

(defthm fn-lzr-parse-c-len
  (implies (fn-lzr-parse z)
           (<= (len (nth 4 (fn-lzr-parse z))) (len z)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-lzr-parse) (fn-lzr-magicp fn-arx-u32-list take)))))

; The compressed extent E = (FILE EOFF ELEN CPOFF CLEN TRAILER N DICT-ID):
; C at [CPOFF, CPOFF+CLEN) inside the entry's protected prefix
; [EOFF, EOFF+ELEN), decoding against DICT-ID to N octets.
(defun fn-lzr-extentp (e)
  (declare (xargs :guard t))
  (and (true-listp e)
       (equal (len e) 8)
       (fn-arn-extent-guardp (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e))
       (natp (nth 6 e))
       (fn-lzr-u32p (nth 7 e))))

; The frame Z (octets) at its PLACE (START N ROFF RLEN) in FILE, whose
; record's payload is PAYLOAD: the compressed extent, or nil when the place
; is not Z's, Z is not a frame, its dictionary is not in DICTS, or its C
; does not decode to PAYLOAD.  (The replay has PAYLOAD from the expansion:
; the decode here is the check that ties the extent to it.)
(defun fn-lzr-extent-of (file position z payload dicts)
  (declare (xargs :guard (and (natp file) (fn-cbor-octet-listp z) (true-listp position)
                              (fn-lzr-dictsp dicts))
                  :guard-hints (("Goal" :in-theory (disable fn-lzr-magicp take nthcdr)))))
  (let ((p (fn-lzr-parse z)))
    (if (not p)
        nil
      (let* ((start (nfix (nth 0 position)))
             (n (nfix (nth 1 position)))
             (roff (nfix (nth 2 position)))
             (rlen (len z))
             (e (assoc-equal (nth 0 p) dicts))
             (c (nth 4 p))
             (clen (len c)))
        (if (and e
                 (fn-lzr-u32p (nth 0 p))
                 (equal (nth 3 position) rlen)
                 (<= (+ start *fn-arx-record-at*) roff)
                 (<= (+ roff rlen *fn-frame-trailer-octets*) (+ start n))
                 (true-listp payload)
                 (equal (len payload) (nfix (nth 2 p)))
                 (equal (fn-lz-decode (cdr e) c (nfix (nth 2 p))) (list :ok payload)))
            (list (nfix file) start (- n *fn-frame-trailer-octets*)
                  (+ roff (- rlen clen)) clen 0 (nfix (nth 2 p)) (nth 0 p))
          nil)))))

(defthm fn-lzr-extent-of-extentp
  (implies (fn-lzr-extent-of file position z payload dicts)
           (fn-lzr-extentp (fn-lzr-extent-of file position z payload dicts)))
  :hints (("Goal" :in-theory (disable fn-lzr-magicp take nthcdr fn-lz-decode))))

; The served read of a compressed extent: the decode of C's durable octets
; (read by the host's realizer, which checks the entry's trailer first).
(defun fn-lzr-read (dict c n)
  (declare (xargs :guard (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp c) (natp n))))
  (let ((r (fn-lz-decode dict c n)))
    (if (equal (car r) :ok) r (list :refused :lz-decode))))

(local
 (defthm fn-lzr-take-len-self
   (implies (true-listp x) (equal (take (len x) x) x))
   :hints (("Goal" :in-theory (enable take)))))

; KEYSTONE: the extent read denotes the stored octets.  When the log holds
; the frame at its place (the faithful read: what the scan read is the file,
; A-HOST and A-DURABLE-EXTENT), the read of the compressed extent's durable
; octets, against its dictionary, is the record's payload.
(defthm fn-lzr-extent-read-denotes
  (let ((e (fn-lzr-extent-of file position z payload dicts)))
    (implies (and e
                  (equal (fn-durable-octets (nfix file) (nfix (nth 2 position)) (len z)) z)
                  (true-listp z))
             (equal (fn-lzr-read (cdr (assoc-equal (nth 7 e) dicts))
                                 (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e))
                                 (nth 6 e))
                    (list :ok payload))))
  :hints (("Goal" :in-theory (e/d () (fn-lzr-magicp take nthcdr fn-lz-decode
                                      fn-lzr-parse-c-is-the-tail fn-arx-durable-slice))
           :use ((:instance fn-lzr-parse-c-is-the-tail)
                 (:instance fn-arx-durable-slice
                            (file (nfix file)) (off (nfix (nth 2 position))) (len (len z))
                            (k (- (len z) (len (nth 4 (fn-lzr-parse z)))))
                            (m (len (nth 4 (fn-lzr-parse z)))))))))

; The value the arena holds for the extent is the payload.
(local
 (defthm fn-lzr-read-ok-is-the-decode
   (implies (equal (fn-lzr-read d c n) (list :ok p))
            (equal (fn-lz-decode d c n) (list :ok p)))
   :rule-classes nil))

(defthm fn-lzr-extent-of-payload-shape
  (implies (fn-lzr-extent-of file position z payload dicts)
           (and (true-listp payload)
                (equal (len payload) (nth 6 (fn-lzr-extent-of file position z payload dicts)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-lzr-magicp take nthcdr fn-lz-decode fn-lzr-parse-shape))))

(defthm fn-lzr-extent-of-lz-value
  (let ((e (fn-lzr-extent-of file position z payload dicts)))
    (implies (and e
                  (equal (fn-durable-octets (nfix file) (nfix (nth 2 position)) (len z)) z)
                  (true-listp z))
             (equal (fn-lzr-lz-value (cdr (assoc-equal (nth 7 e) dicts))
                                     (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e))
                                     (nth 6 e))
                    payload)))
  :hints (("Goal" :in-theory (disable fn-lzr-extent-of fn-lzr-extent-read-denotes fn-lzr-read
                                      fn-lzr-lz-value-of-decode fn-lz-decode)
           :use (fn-lzr-extent-read-denotes
                 fn-lzr-extent-of-payload-shape
                 (:instance fn-lzr-read-ok-is-the-decode
                            (d (cdr (assoc-equal (nth 7 (fn-lzr-extent-of file position z payload dicts))
                                                 dicts)))
                            (c (fn-durable-octets
                                (nth 0 (fn-lzr-extent-of file position z payload dicts))
                                (nth 3 (fn-lzr-extent-of file position z payload dicts))
                                (nth 4 (fn-lzr-extent-of file position z payload dicts))))
                            (n (nth 6 (fn-lzr-extent-of file position z payload dicts)))
                            (p payload))
                 (:instance fn-lzr-lz-value-of-decode
                            (dict (cdr (assoc-equal (nth 7 (fn-lzr-extent-of file position z payload dicts))
                                                    dicts)))
                            (c (fn-durable-octets
                                (nth 0 (fn-lzr-extent-of file position z payload dicts))
                                (nth 3 (fn-lzr-extent-of file position z payload dicts))
                                (nth 4 (fn-lzr-extent-of file position z payload dicts))))
                            (n (nth 6 (fn-lzr-extent-of file position z payload dicts))))))))

(defthm fn-lzr-extent-of-dict-octets
  (implies (and (fn-lzr-extent-of file position z payload dicts) (fn-lzr-dictsp dicts))
           (fn-cbor-octet-listp
            (cdr (assoc-equal (nth 7 (fn-lzr-extent-of file position z payload dicts)) dicts))))
  :hints (("Goal" :in-theory (disable fn-lzr-magicp take nthcdr fn-lz-decode))))

(in-theory (disable fn-lzr-extent-of))

; -----------------------------------------------------------------------------
; 9. The host's compressed realizer (A-DURABLE-LZ, host/native/extent.lisp
; fn-durable-realize-lz) runs this over the block it read: the value when the
; decode gives exactly N octets, else the named refusal.  What it answers is
; the value A-DURABLE-LZ names.
(defun fn-lzr-lz-read (dict c n)
  (declare (xargs :guard (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp c) (natp n))))
  (let ((r (fn-lz-decode dict c n)))
    (if (and (eq (car r) :ok) (true-listp (cadr r)) (equal (len (cadr r)) (nfix n)))
        (list :ok (cadr r))
      (list :refused :lz-decode))))

(defthm fn-lzr-lz-read-is-the-lz-value
  (implies (equal (car (fn-lzr-lz-read dict c n)) :ok)
           (equal (cadr (fn-lzr-lz-read dict c n)) (fn-lzr-lz-value dict c n)))
  :hints (("Goal" :in-theory (enable fn-lzr-lz-value))))

