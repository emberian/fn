; fn: the store's lineage at a checkpoint's log position (lane store-lineage,
; PRF-979; row A2's last piece, the G1 finding of composed-owner-6).
;
; A checkpoint's F row names the log position its capture rotated to, (K
; GENESIS): the first suffix segment and the chain value that segment's
; records continue from (books/store-checkpoint-tables.lisp
; fn-sct-log-positionp).  Before this book the open compared GENESIS with the
; log only through the scan of K: an entry of K chained from another
; predecessor is refused `log-chain-broken' (fn-lgs-chain-broken-p) -- but a
; K holding no entry compares nothing, so a checkpoint from a FORK of this
; store (a restored backup that then diverged: the same genesis record, node
; identity and salt, the same K, an equal count, another history) put in this
; store's place was accepted whenever the suffix was empty (GPT-6's
; equal-count/different-history case at the composed boundary).
;
; The lineage.  Every segment K >= 2 begins with a ROTATION entry: an FNLG
; frame of kind 3 (*fn-lg-rotation-kind*) chained from the closed segment's
; last trailer P, whose body names K (fn-lgl-rotation-frame).  The rotation
; writes and fences it before any checkpoint names K, and the F row's GENESIS
; is the entry's TRAILER: a digest over P, so a fork's GENESIS (a digest over
; its own P') differs unless the digests collide.  The open reads K's head
; (fn-lgl-head-len octets) and decides BEFORE it scans (fn-lgl-open): a head
; whose trailer is not GENESIS is refused `:foreign-lineage' by name -- never
; as absence, never as uncertainty; a head that is not a readable rotation
; entry `:segment-head-damaged'; one naming another index `:segment-misnamed'.
; Segment 1 continues from the genesis record's trailer T0 (host
; fnn-genesis-open), which a position naming segment 1 must carry.
;
; KEYSTONE fn-lgl-open-of-rotated-segment (PRF-979): over segment K as the
; rotation wrote it from P -- the entry, then whatever followed (records, or
; nothing: the empty suffix) -- the open accepts (K GENESIS) exactly when
; GENESIS is the entry's trailer.  fn-lgl-fork-refused: a checkpoint whose
; GENESIS is the trailer of a rotation entry from another P' is refused
; :foreign-lineage, under the per-pair collision hypothesis
; fn-lgl-trailer-distinct.  fn-lgl-accepted-shares-lineage, the composed
; statement over publish, recover and open: with P the chain value of the
; covered segments the log held and P' that of the segments the checkpoint's
; capture covered, an accepted checkpoint covered exactly the log's segments
; (fn-lgl-chain-distinct, the per-pair hypothesis of fn-hib-chain-distinct's
; shape, over segments).  THE TOOTH (tests/acl2/store-log-lineage-tests.lisp,
; a hypothesis-removal witness over the lineage clause): the old open's three
; decisions (fn-lgs-open-plan, fn-lg-scan of the empty K, fn-lgs-chain-broken-p
; over nothing) are the same for the store's own GENESIS and the fork's;
; fn-lgl-open is not.
;
; Host: fnn-log-rotate writes the entry (host/native/io.lisp, cut
; rotate-headed, the file fenced before rotate-durable) and fn-lgc-rotate KS K
; carries its trailer as the kernel's chain head (the empty-segment path of
; the rotation answers the same value); fnn-recover-log calls fn-lgl-open
; over the first suffix segment's head and streams K from the head's claimed
; predecessor (fn-lgl-head-prev), which validates the entry as a zero-record
; entry of the chain (books/store-log.lisp kind 3).
(in-package "ACL2")
(include-book "store-log-segments")

; -----------------------------------------------------------------------------
; The rotation entry.

(defconst *fn-lg-rotation-kind* 3)
(defconst *fn-lgl-body-octets* 4)
(defconst *fn-lgl-payload-octets* (+ *fn-frame-trailer-octets* *fn-lgl-body-octets*))

; A segment index the body can name.
(defun fn-lgl-indexp (k)
  (declare (xargs :guard t))
  (and (posp k) (<= k *fn-lgs-max-segment*)))

(defun fn-lgl-rotation-frame (prev k)
  (declare (xargs :guard t :verify-guards nil))
  (fn-frame-seal *fn-lg-magic* *fn-lg-version* *fn-lg-rotation-kind*
                 (append prev (fn-cbor-u32-bytes k))))

(defun fn-lgl-rotation-entry (prev k unit)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-lgl-rotation-frame prev k)))
    (append frame (fn-bs-zeros (fn-lg-pad-len (len frame) unit)))))

(local
 (defthm fn-lgl-u32-bytes-len
   (equal (len (fn-cbor-u32-bytes n)) 4)
   :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes)))))

(local
 (defthm fn-lgl-indexp-forward
   (implies (fn-lgl-indexp k) (and (natp k) (<= k *fn-cbor-max-uint*)))
   :rule-classes :forward-chaining))

(local
 (defthm fn-lgl-octet-listp-of-append
   (implies (true-listp a)
            (equal (fn-cbor-octet-listp (append a b))
                   (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-lgl-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-lgl-digestp-forward
   (implies (fn-frame-digestp xs)
            (and (fn-cbor-octet-listp xs) (true-listp xs) (equal (len xs) 32)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-frame-digestp)))))

(defthm fn-lgl-rotation-payload-octets
  (implies (and (fn-frame-digestp prev) (fn-lgl-indexp k))
           (and (fn-cbor-octet-listp (append prev (fn-cbor-u32-bytes k)))
                (equal (len (append prev (fn-cbor-u32-bytes k))) *fn-lgl-payload-octets*)))
  :hints (("Goal" :in-theory (disable fn-cbor-u32-bytes fn-cbor-octet-listp fn-frame-digestp)
           :use ((:instance fn-cbor-u32-bytes-are-octets (n k))))))

; The frame's shape (fn-frame-seal opened: header, payload, digest), as
; store-log.lisp proves fn-lg-frame-len and fn-lg-frame-octets.
(local
 (defthm fn-lgl-rotation-protected-octets
   (implies (and (fn-frame-digestp prev) (fn-lgl-indexp k))
            (and (fn-cbor-octet-listp (fn-frame-protected *fn-lg-magic* *fn-lg-version* *fn-lg-rotation-kind*
                                                          (append prev (fn-cbor-u32-bytes k))))
                 (true-listp (fn-frame-protected *fn-lg-magic* *fn-lg-version* *fn-lg-rotation-kind*
                                                 (append prev (fn-cbor-u32-bytes k))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-frame-protected fn-frame-header fn-cbor-octet-listp fn-cbor-octetp)
                            (fn-frame-digestp fn-lgl-indexp fn-cbor-u32-bytes))
            :use ((:instance fn-cbor-u32-bytes-are-octets (n k))
                  (:instance fn-cbor-u32-bytes-are-octets (n *fn-lgl-payload-octets*)))))))

(defthm fn-lgl-rotation-frame-len
  (implies (and (fn-frame-digestp prev) (fn-lgl-indexp k))
           (equal (len (fn-lgl-rotation-frame prev k))
                  (+ *fn-frame-overhead-octets* *fn-lgl-payload-octets*)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgl-rotation-frame fn-frame-seal fn-frame-encode fn-frame-protected fn-frame-header)
                           (fn-cbor-u32-bytes fn-frame-digestp fn-lgl-indexp fn-cbor-octet-listp
                            fn-frame-digest-length))
           :use ((:instance fn-frame-digest-length
                            (octets (fn-frame-protected *fn-lg-magic* *fn-lg-version* *fn-lg-rotation-kind*
                                                        (append prev (fn-cbor-u32-bytes k)))))))))

(defthm fn-lgl-rotation-frame-octets
  (implies (and (fn-frame-digestp prev) (fn-lgl-indexp k))
           (fn-cbor-octet-listp (fn-lgl-rotation-frame prev k)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgl-rotation-frame fn-frame-seal fn-frame-encode)
                           (fn-cbor-u32-bytes fn-frame-digestp fn-lgl-indexp fn-cbor-octet-listp
                            fn-frame-protected fn-frame-digest-octet-listp))
           :use ((:instance fn-frame-digest-octet-listp
                            (octets (fn-frame-protected *fn-lg-magic* *fn-lg-version* *fn-lg-rotation-kind*
                                                        (append prev (fn-cbor-u32-bytes k)))))))))

(defthm fn-lgl-rotation-frame-true-listp
  (implies (and (fn-frame-digestp prev) (fn-lgl-indexp k))
           (true-listp (fn-lgl-rotation-frame prev k)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgl-rotation-frame fn-frame-seal fn-frame-encode)
                           (fn-cbor-u32-bytes fn-frame-digestp fn-lgl-indexp fn-cbor-octet-listp
                            fn-frame-protected fn-frame-digest-octet-listp))
           :use ((:instance fn-frame-digest-octet-listp
                            (octets (fn-frame-protected *fn-lg-magic* *fn-lg-version* *fn-lg-rotation-kind*
                                                        (append prev (fn-cbor-u32-bytes k)))))))))

; The sealed entry opens to what was sealed (fn-frame-open-of-seal, A-CRYPTO).
(defthm fn-lgl-open-of-rotation-frame
  (implies (and (fn-frame-digestp prev) (fn-lgl-indexp k)
                (natp max) (<= *fn-lgl-payload-octets* max) (<= max *fn-frame-max-payload*))
           (equal (fn-frame-open (fn-lgl-rotation-frame prev k) max)
                  (fn-frame-ok *fn-lg-magic* *fn-lg-version* *fn-lg-rotation-kind*
                               (append prev (fn-cbor-u32-bytes k)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-open-of-seal
                            (magic *fn-lg-magic*) (version *fn-lg-version*)
                            (kind *fn-lg-rotation-kind*)
                            (payload (append prev (fn-cbor-u32-bytes k)))
                            (max-payload max)))
           :in-theory (e/d (fn-frame-inputp)
                           (fn-frame-open fn-frame-seal fn-frame-open-of-seal
                            fn-cbor-u32-bytes fn-frame-digestp fn-lgl-indexp)))))

; The head's declared length is the frame's: the slice of the entry followed
; by anything is the frame (as fn-lg-slice-of-entry-append for a record entry).
(defthm fn-lgl-declared-len-of-rotation-frame-append
  (implies (and (fn-frame-digestp prev) (fn-lgl-indexp k))
           (equal (fn-lg-declared-len (append (fn-lgl-rotation-frame prev k) x))
                  (len (fn-lgl-rotation-frame prev k))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-declared-len fn-lgl-rotation-frame fn-frame-seal fn-frame-encode
                            fn-frame-protected fn-frame-header fn-bs-take nthcdr)
                           (fn-cbor-u32-bytes fn-cbor-u32-from fn-frame-digestp fn-lgl-indexp
                            fn-cbor-octet-listp fn-lgl-rotation-frame-len fn-lgl-rotation-frame-octets
                            fn-lgl-rotation-frame-true-listp fn-frame-digest-length))
           :use ((:instance fn-frame-digest-length
                            (octets (fn-frame-protected *fn-lg-magic* *fn-lg-version* *fn-lg-rotation-kind*
                                                        (append prev (fn-cbor-u32-bytes k)))))))))

(local
 (defthm fn-lgl-take-of-append-exact
   (implies (true-listp a)
            (equal (fn-bs-take (len a) (append a b)) a))))

(local
 (defthm fn-lgl-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-lgl-slice-of-rotation-entry-append
  (implies (and (fn-frame-digestp prev) (fn-lgl-indexp k))
           (equal (fn-lg-slice (append (fn-lgl-rotation-entry prev k unit) x))
                  (fn-lgl-rotation-frame prev k)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-slice fn-lgl-rotation-entry)
                           (fn-lgl-rotation-frame fn-lg-declared-len fn-lg-pad-len
                            fn-frame-digestp fn-lgl-indexp fn-cbor-u32-bytes))
           :use ((:instance fn-lgl-declared-len-of-rotation-frame-append
                            (x (append (fn-bs-zeros (fn-lg-pad-len (len (fn-lgl-rotation-frame prev k)) unit)) x)))
                 (:instance fn-lgl-take-of-append-exact
                            (a (fn-lgl-rotation-frame prev k))
                            (b (append (fn-bs-zeros (fn-lg-pad-len (len (fn-lgl-rotation-frame prev k)) unit)) x)))))))

; -----------------------------------------------------------------------------
; The head of a segment, as the open reads it.

; The octets the open reads from a segment's front: one rotation entry, padded.
(defun fn-lgl-head-len (unit)
  (declare (xargs :guard t))
  (let ((n (+ *fn-frame-overhead-octets* *fn-lgl-payload-octets*)))
    (+ n (fn-lg-pad-len n unit))))

(defun fn-lgl-head (octets max)
  (declare (xargs :guard t :verify-guards nil))
  (fn-frame-open (fn-lg-slice octets) max))

(defun fn-lgl-headed-p (octets max)
  ; The front of OCTETS is a readable rotation entry.
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-lgl-head octets max)))
    (and (fn-frame-result-okp r)
         (equal (fn-frame-result-magic r) *fn-lg-magic*)
         (equal (fn-frame-result-version r) *fn-lg-version*)
         (equal (fn-frame-result-kind r) *fn-lg-rotation-kind*)
         (equal (len (fn-frame-result-payload r)) *fn-lgl-payload-octets*))))

(defun fn-lgl-head-prev (octets max)
  ; The chain value the entry claims to continue from: the closed segment's
  ; last trailer.  The host streams the segment from it.
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-take *fn-frame-trailer-octets* (fn-frame-result-payload (fn-lgl-head octets max))))

(defun fn-lgl-head-index (octets max)
  (declare (xargs :guard t :verify-guards nil))
  (nthcdr *fn-frame-trailer-octets* (fn-frame-result-payload (fn-lgl-head octets max))))

(defun fn-lgl-head-trailer (octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-trailer (fn-lg-slice octets)))

(defun fn-lgl-head-check (octets k g max)
  ; Segment K's head against the F row's (K G): nil, or the refusal by name.
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (fn-lgl-headed-p octets max)) (list :refused :segment-head-damaged))
        ((not (equal (fn-lgl-head-index octets max) (fn-cbor-u32-bytes k)))
         (list :refused :segment-misnamed))
        ((not (equal (fn-lgl-head-trailer octets) g)) (list :refused :foreign-lineage))
        (t nil)))

(defun fn-lgl-open (k g octets t0 max)
  ; The open's lineage decision over the F row's position (K G), the head
  ; OCTETS of segment K and the genesis record's trailer T0: nil when the
  ; checkpoint continues this log, else the refusal by name.
  (declare (xargs :guard t :verify-guards nil))
  (if (equal k 1)
      (if (equal g t0) nil (list :refused :foreign-lineage))
    (fn-lgl-head-check octets k g max)))

; -----------------------------------------------------------------------------
; The keystone.

(local
 (defthm fn-lgl-nthcdr-of-append-exact
   (implies (true-listp a)
            (equal (nthcdr (len a) (append a b)) b))))

(local
 (defthm fn-lgl-frame-item-of-ok
   (and (equal (fn-frame-result-okp (fn-frame-ok m v k p)) t)
        (equal (fn-frame-result-magic (fn-frame-ok m v k p)) m)
        (equal (fn-frame-result-version (fn-frame-ok m v k p)) v)
        (equal (fn-frame-result-kind (fn-frame-ok m v k p)) k)
        (equal (fn-frame-result-payload (fn-frame-ok m v k p)) p))
   :hints (("Goal" :in-theory (enable fn-frame-item)))))

; KEYSTONE (PRF-979).  Segment K as the rotation wrote it from the closed
; segment's last trailer P -- the rotation entry, then whatever followed
; (records, or nothing) -- opened under the F row's (K G): accepted exactly
; when G is the entry's trailer, else refused :foreign-lineage by name.
(defthm fn-lgl-open-of-rotated-segment
  (implies (and (fn-frame-digestp p) (fn-lgl-indexp k) (not (equal k 1))
                (natp max) (<= *fn-lgl-payload-octets* max) (<= max *fn-frame-max-payload*))
           (equal (fn-lgl-open k g (append (fn-lgl-rotation-entry p k unit) rest) t0 max)
                  (if (equal g (fn-lg-trailer (fn-lgl-rotation-frame p k)))
                      nil
                    (list :refused :foreign-lineage))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgl-open fn-lgl-head-check fn-lgl-headed-p fn-lgl-head
                            fn-lgl-head-index fn-lgl-head-trailer)
                           (fn-lgl-rotation-frame fn-lgl-rotation-entry fn-frame-open
                            fn-frame-ok fn-lg-slice fn-lg-trailer fn-cbor-u32-bytes
                            fn-frame-digestp fn-lgl-indexp))
           :use ((:instance fn-lgl-nthcdr-of-append-exact (a p) (b (fn-cbor-u32-bytes k)))))))

; The per-pair collision hypothesis, in the shape of fn-hib-chain-distinct
; (books/history-image-binding.lisp): two rotation entries naming K whose
; trailers agree continue from the same chain value.  Its failure is a
; collision of the frame digest (BLAKE3) between these two frames; the
; pessimistic figure is the collision bound, 2^-128 per pair.  No universal
; injectivity is assumed or claimed.
(defun-nx fn-lgl-trailer-distinct (p q k)
  (implies (equal (fn-lg-trailer (fn-lgl-rotation-frame p k))
                  (fn-lg-trailer (fn-lgl-rotation-frame q k)))
           (equal p q)))

; A fork's checkpoint -- its GENESIS the trailer of a rotation entry naming K
; from ANOTHER chain value Q -- put in this store's place is refused
; :foreign-lineage, whatever segment K holds after its head.
(defthm fn-lgl-fork-refused
  (implies (and (fn-frame-digestp p) (fn-frame-digestp q) (not (equal p q))
                (fn-lgl-trailer-distinct p q k)
                (fn-lgl-indexp k) (not (equal k 1))
                (natp max) (<= *fn-lgl-payload-octets* max) (<= max *fn-frame-max-payload*))
           (equal (fn-lgl-open k (fn-lg-trailer (fn-lgl-rotation-frame q k))
                               (append (fn-lgl-rotation-entry p k unit) rest) t0 max)
                  (list :refused :foreign-lineage)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgl-open-of-rotated-segment
                            (g (fn-lg-trailer (fn-lgl-rotation-frame q k)))))
           :in-theory (union-theories '(fn-lgl-trailer-distinct) (theory 'minimal-theory)))))

; The per-pair hypothesis over segments (fn-hib-chain-distinct's shape): two
; segment lists chained from the same genesis trailer that reach the same
; chain value are the same segments.
(defun-nx fn-lgl-chain-distinct (t0 s1 s2 unit max)
  (implies (equal (fn-lgs-chain-last s1 t0 unit max) (fn-lgs-chain-last s2 t0 unit max))
           (equal s1 s2)))

; KEYSTONE (the composed statement over publish, recover and open).  The log
; held the segments COVERED below K, and the rotation wrote K's head from
; their chain value; a checkpoint's capture covered the segments COVERED-C
; (its own log's, when it is a fork's) and its F row carries (K GENESIS) with
; GENESIS the trailer of the rotation entry from THEIR chain value.  When the
; open accepts that checkpoint over this log's K, the segments the checkpoint
; covered are the log's: the same entries, records and order -- not merely as
; many.  Established by the open's decision; the host assumes none of it.
(defthm fn-lgl-accepted-shares-lineage
  (let ((p (fn-lgs-chain-last covered t0 unit max))
        (q (fn-lgs-chain-last covered-c t0 unit max)))
    (implies (and (fn-frame-digestp p) (fn-frame-digestp q)
                  (fn-lgl-trailer-distinct p q k)
                  (fn-lgl-chain-distinct t0 covered-c covered unit max)
                  (fn-lgl-indexp k) (not (equal k 1))
                  (natp max) (<= *fn-lgl-payload-octets* max) (<= max *fn-frame-max-payload*)
                  (not (fn-lgl-open k (fn-lg-trailer (fn-lgl-rotation-frame q k))
                                    (append (fn-lgl-rotation-entry p k unit) rest) t0 max)))
             (equal covered-c covered)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgl-open-of-rotated-segment
                            (p (fn-lgs-chain-last covered t0 unit max))
                            (g (fn-lg-trailer (fn-lgl-rotation-frame (fn-lgs-chain-last covered-c t0 unit max) k)))))
           :in-theory (union-theories '(fn-lgl-trailer-distinct fn-lgl-chain-distinct)
                                      (theory 'minimal-theory)))))

(in-theory (disable fn-lgl-rotation-frame fn-lgl-rotation-entry fn-lgl-head fn-lgl-headed-p
                    fn-lgl-head-prev fn-lgl-head-index fn-lgl-head-trailer fn-lgl-head-check
                    fn-lgl-open))
