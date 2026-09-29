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
; last trailer P, whose body names K (fn-lg-rotation-frame).  The rotation
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
; The rotation entry is the log format's (books/store-log.lisp
; fn-lg-rotation-frame, fn-lg-rotation-entry, fn-lg-rotation-indexp,
; *fn-lg-rotation-kind*; its frame lemmas and the scan over it,
; fn-lg-scan-of-rotation-entry-append).  The head the open reads holds the
; claimed predecessor and the index.
(defconst *fn-lgl-payload-octets* (+ *fn-frame-trailer-octets* *fn-lg-rotation-body-octets*))

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

; The reply line of a refusal, as the host prints it (ACL2 owns the text).
(defun fn-lgl-refusal-text (verdict)
  (declare (xargs :guard t))
  (let ((reason (and (consp verdict) (consp (cdr verdict)) (cadr verdict))))
    (cond ((eq reason :foreign-lineage)
           "open refused reason=foreign-lineage: the checkpoint's log segment continues another history (a restored backup or another store's checkpoint)")
          ((eq reason :segment-head-damaged)
           "open refused reason=segment-head-damaged: the checkpoint's log segment has no readable rotation entry")
          ((eq reason :segment-misnamed)
           "open refused reason=segment-misnamed: the checkpoint's log segment is headed for another segment index")
          (t "open refused reason=foreign-lineage: the checkpoint's log segment does not continue this history"))))

; -----------------------------------------------------------------------------
; The keystone.

(local
 (defthm fn-lgl-nthcdr-of-append-exact
   (implies (true-listp a)
            (equal (nthcdr (len a) (append a b)) b))))

(local
 (defthm fn-lgl-digestp-forward
   (implies (fn-frame-digestp xs)
            (and (fn-cbor-octet-listp xs) (true-listp xs) (equal (len xs) 32)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-frame-digestp)))))

(local
 (defthm fn-lgl-u32-bytes-len
   (equal (len (fn-cbor-u32-bytes n)) 4)
   :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes)))))

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
  (implies (and (fn-frame-digestp p) (fn-lg-rotation-indexp k) (not (equal k 1))
                (natp max) (<= *fn-lgl-payload-octets* max) (<= max *fn-frame-max-payload*))
           (equal (fn-lgl-open k g (append (fn-lg-rotation-entry p k unit) rest) t0 max)
                  (if (equal g (fn-lg-trailer (fn-lg-rotation-frame p k)))
                      nil
                    (list :refused :foreign-lineage))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgl-open fn-lgl-head-check fn-lgl-headed-p fn-lgl-head
                            fn-lgl-head-index fn-lgl-head-trailer)
                           (fn-lg-rotation-frame fn-lg-rotation-entry fn-frame-open
                            fn-frame-ok fn-lg-slice fn-lg-trailer fn-cbor-u32-bytes
                            fn-frame-digestp fn-lg-rotation-indexp))
           :use ((:instance fn-lgl-nthcdr-of-append-exact (a p) (b (fn-cbor-u32-bytes k)))))))

; The per-pair collision hypothesis, in the shape of fn-hib-chain-distinct
; (books/history-image-binding.lisp): two rotation entries naming K whose
; trailers agree continue from the same chain value.  Its failure is a
; collision of the frame digest (BLAKE3) between these two frames; the
; pessimistic figure is the collision bound, 2^-128 per pair.  No universal
; injectivity is assumed or claimed.
(defun-nx fn-lgl-trailer-distinct (p q k)
  (implies (equal (fn-lg-trailer (fn-lg-rotation-frame p k))
                  (fn-lg-trailer (fn-lg-rotation-frame q k)))
           (equal p q)))

; A fork's checkpoint -- its GENESIS the trailer of a rotation entry naming K
; from ANOTHER chain value Q -- put in this store's place is refused
; :foreign-lineage, whatever segment K holds after its head.
(defthm fn-lgl-fork-refused
  (implies (and (fn-frame-digestp p) (fn-frame-digestp q) (not (equal p q))
                (fn-lgl-trailer-distinct p q k)
                (fn-lg-rotation-indexp k) (not (equal k 1))
                (natp max) (<= *fn-lgl-payload-octets* max) (<= max *fn-frame-max-payload*))
           (equal (fn-lgl-open k (fn-lg-trailer (fn-lg-rotation-frame q k))
                               (append (fn-lg-rotation-entry p k unit) rest) t0 max)
                  (list :refused :foreign-lineage)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgl-open-of-rotated-segment
                            (g (fn-lg-trailer (fn-lg-rotation-frame q k)))))
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
                  (fn-lg-rotation-indexp k) (not (equal k 1))
                  (natp max) (<= *fn-lgl-payload-octets* max) (<= max *fn-frame-max-payload*)
                  (not (fn-lgl-open k (fn-lg-trailer (fn-lg-rotation-frame q k))
                                    (append (fn-lg-rotation-entry p k unit) rest) t0 max)))
             (equal covered-c covered)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgl-open-of-rotated-segment
                            (p (fn-lgs-chain-last covered t0 unit max))
                            (g (fn-lg-trailer (fn-lg-rotation-frame (fn-lgs-chain-last covered-c t0 unit max) k)))))
           :in-theory (union-theories '(fn-lgl-trailer-distinct fn-lgl-chain-distinct)
                                      (theory 'minimal-theory)))))

(in-theory (disable fn-lgl-head fn-lgl-headed-p
                    fn-lgl-head-prev fn-lgl-head-index fn-lgl-head-trailer fn-lgl-head-check
                    fn-lgl-open))
