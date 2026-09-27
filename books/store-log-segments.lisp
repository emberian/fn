; fn: the record log's segments -- rotation, the drop and the open over
; several segments (lane log-recovery, PKT-750; design
; planning/design-2026-09-27-storage-log.md sections 3.1, 3.5, 4 and 6).
;
; A format-9 store's history is the chained FNLG entries of its segments
; journal/000001.log, journal/000002.log, ...  (fn-lgs-segment-name).  The
; highest index present is the active segment; every lower one is closed: the
; checkpoint's capture ROTATED it (the next segment created and fenced before
; the checkpoint names it), so its last entry's trailer is the next segment's
; genesis (fn-lgs-chain-*).  A checkpoint whose F row names its first suffix
; segment K and that segment's genesis G covers every segment below K; after
; the checkpoint's install those are unlinked (the drop), and the open
; is the checkpoint's capture followed by the scan of K, K+1, ... from G.
;
; ACL2 decides: the segment names (fn-lgs-segment-name, fn-lgs-segment-index),
; which segments the open scans and which it drops (fn-lgs-open-plan, by name
; `history-short-of-checkpoint' and `checkpoint-damaged' otherwise), whether a
; scan's stop is a torn tail or a splice (fn-lgs-chain-broken-p: an entry that
; validates under another predecessor is refused `log-chain-broken', never read
; as a torn tail), and the rotation's next index (fn-lgs-next-segment).  The
; host (host/native/io.lisp fnn-recover-log, fnn-log-rotate, fnn-log-drop)
; lists journal/, reads each segment through the per-segment kernel
; (fn-lg-open-kernel = fn-lgt-recover: fn-lg-open-kernel-is-the-recovered-
; kernel), and carries the genesis from one segment's kernel (fn-lgk-last) to
; the next.
;
; T8 (fn-lg-segment-drop-preserves-the-open): with the covered segments' chain
; being the checkpoint's prefix and its last trailer the F row's genesis, the
; history the open replays from the checkpoint over the remaining segments is
; the full chain over all of them (the chain splits at any segment boundary,
; fn-lgs-chain-records-of-append), and the replay of that split is the full
; replay (fn-sn-recover-from-checkpoint-equals-full-recover).
(in-package "ACL2")
(include-book "store-log-programs")

; -----------------------------------------------------------------------------
; Names.

; Six decimal digits and ".log"; index 1 is fn-olr-segment-name's "000001.log".
(defconst *fn-lgs-max-segment* 999999)

(defun fn-lgs-digit-char (d)
  (declare (xargs :guard t))
  (case d (0 #\0) (1 #\1) (2 #\2) (3 #\3) (4 #\4) (5 #\5) (6 #\6) (7 #\7)
    (8 #\8) (otherwise #\9)))

(defun fn-lgs-digits (n width)
  (declare (xargs :guard (and (natp n) (natp width))))
  (if (zp width)
      nil
    (append (fn-lgs-digits (floor (nfix n) 10) (1- width))
            (list (fn-lgs-digit-char (mod (nfix n) 10))))))

(defthm fn-lgs-character-listp-of-digits
  (character-listp (fn-lgs-digits n width)))

(defun fn-lgs-segment-name (k)
  (declare (xargs :guard t))
  (coerce (append (fn-lgs-digits (nfix k) 6) (coerce ".log" 'list)) 'string))

(defun fn-lgs-digits-value (chars acc)
  (declare (xargs :guard (and (character-listp chars) (natp acc))))
  (if (consp chars)
      (and (digit-char-p (car chars))
           (fn-lgs-digits-value (cdr chars)
                                (+ (* 10 acc) (digit-char-p (car chars)))))
    acc))

; The index of a directory entry that is a segment, or NIL.
(defun fn-lgs-segment-index (name)
  (declare (xargs :guard t))
  (and (stringp name)
       (equal (length name) 10)
       (equal (subseq name 6 10) ".log")
       (let ((k (fn-lgs-digits-value (coerce (subseq name 0 6) 'list) 0)))
         (and (posp k) (equal (fn-lgs-segment-name k) name) k))))

; The next segment a rotation creates after the active K, or NIL past the
; name's width (the rotation is then refused by name: segment-index-exhausted).
(defun fn-lgs-next-segment (k)
  (declare (xargs :guard t))
  (and (posp k) (< k *fn-lgs-max-segment*) (1+ k)))

; -----------------------------------------------------------------------------
; The open's plan over the segments present.

(defun fn-lgs-indices (names)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((k (fn-lgs-segment-index (car names))))
        (if k (cons k (fn-lgs-indices (cdr names))) (fn-lgs-indices (cdr names))))
    nil))

(defthm fn-lgs-true-listp-indices
  (true-listp (fn-lgs-indices names))
  :rule-classes :type-prescription)

(defun fn-lgs-max-index (ks acc)
  (declare (xargs :guard (natp acc)))
  (if (consp ks)
      (fn-lgs-max-index (cdr ks) (max acc (nfix (car ks))))
    acc))

(defthm fn-lgs-natp-max-index
  (implies (natp acc) (natp (fn-lgs-max-index ks acc)))
  :rule-classes :type-prescription)

; FROM, FROM+1, ..., TO.
(defun fn-lgs-range (from to)
  (declare (xargs :guard (and (natp from) (natp to))
                  :measure (nfix (- (+ 1 (nfix to)) (nfix from)))))
  (if (and (natp from) (natp to) (<= from to))
      (cons from (fn-lgs-range (1+ from) to))
    nil))

(defun fn-lgs-all-present (ks present)
  (declare (xargs :guard (true-listp present)))
  (if (consp ks)
      (and (member-equal (car ks) present) t
           (fn-lgs-all-present (cdr ks) present))
    t))

(defun fn-lgs-below (ks k)
  (declare (xargs :guard t))
  (if (consp ks)
      (if (and (natp (car ks)) (natp k) (< (car ks) k))
          (cons (car ks) (fn-lgs-below (cdr ks) k))
        (fn-lgs-below (cdr ks) k))
    nil))

; NAMES: journal/'s entries as the host listed them.  FIRST: the first suffix
; segment the selected checkpoint's F row names, or NIL when no checkpoint
; names one (none, damaged, of another schema).
;   (:scan SCAN DROP)  scan the indices SCAN in order (the last is the active
;                      segment) and unlink the covered indices DROP;
;   (:refused :history-short-of-checkpoint)  a segment from FIRST (or 1) to
;                      the active one is missing, or none is present;
;   (:refused :checkpoint-damaged)  no checkpoint names a first segment and
;                      segment 1 is gone: the history below the remaining
;                      segments is only in a checkpoint the open cannot use.
(defun fn-lgs-open-plan (names first)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-lgs-indices fn-lgs-range
                                                            fn-lgs-all-present fn-lgs-below
                                                            fn-lgs-max-index)))))
  (let* ((present (fn-lgs-indices names))
         (top (fn-lgs-max-index present 0)))
    (cond ((atom present) (list :refused :history-short-of-checkpoint))
          ((posp first)
           (if (and (<= first top) (fn-lgs-all-present (fn-lgs-range first top) present))
               (list :scan (fn-lgs-range first top) (fn-lgs-below present first))
             (list :refused :history-short-of-checkpoint)))
          ((not (member-equal 1 present)) (list :refused :checkpoint-damaged))
          ((fn-lgs-all-present (fn-lgs-range 1 top) present)
           (list :scan (fn-lgs-range 1 top) nil))
          (t (list :refused :history-short-of-checkpoint)))))

; -----------------------------------------------------------------------------
; A scan's stop: a torn tail or a splice.

; The predecessor a slice's frame claims (its payload's first 32 octets).
(defun fn-lgs-claimed-prev (slice max)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-take *fn-frame-trailer-octets*
              (fn-frame-result-payload (fn-frame-open slice max))))

; At the stop of the scan of OCTETS from PREV: an entry there validates as a
; chained frame of this log under the predecessor it claims, which is not the
; scan's last trailer.  A torn tail is never that (its first damaged unit
; stops the scan and does not validate), except by the A-CRYPTO-TRAILER
; forgery event; a splice, a stale segment or a wrong genesis is.
(defun fn-lgs-chain-broken-p (octets prev unit max)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((stop (cdr (fn-lg-scan octets prev unit max)))
         (last (fn-lg-scan-last octets prev unit max))
         (slice (fn-lg-slice (nthcdr stop octets))))
    (and (fn-lg-entry-okp slice (fn-lgs-claimed-prev slice max) max)
         (not (equal (fn-lgs-claimed-prev slice max) last)))))

; The host's string form (the segment as fn-lg-decode reads it).
(defun fn-lgs-chain-broken-string-p (s prev unit max)
  (declare (xargs :guard (stringp s) :verify-guards nil))
  (fn-lgs-chain-broken-p (fn-lgd-octets s) prev unit max))

; -----------------------------------------------------------------------------
; The chain over several segments.

; SEGS: the segments' durable contents in index order.  Each is scanned from
; the previous one's last trailer (the first from PREV): the host's per-
; segment kernel is fn-lgk-recover, whose committed records are the scan's
; and whose last is fn-lg-scan-last (fn-lgk-recover's definition).
(defun fn-lgs-chain-last (segs prev unit max)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp segs)
      (fn-lgs-chain-last (cdr segs) (fn-lg-scan-last (car segs) prev unit max) unit max)
    prev))

(defun fn-lgs-chain-records (segs prev unit max)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp segs)
      (append (car (fn-lg-scan (car segs) prev unit max))
              (fn-lgs-chain-records (cdr segs)
                                    (fn-lg-scan-last (car segs) prev unit max)
                                    unit max))
    nil))

; The per-segment step is the host's kernel.
(defthm fn-lgs-chain-step-is-the-kernel-by-definition
  (and (equal (fn-lgk-committed (fn-lgk-recover c prev unit max next))
              (car (fn-lg-scan c prev unit max)))
       (equal (fn-lgk-last (fn-lgk-recover c prev unit max next))
              (fn-lg-scan-last c prev unit max)))
  :hints (("Goal" :in-theory (enable fn-lgk-recover fn-lgk-make fn-lgk-committed
                                     fn-lgk-last))))

(local
 (defthm fn-lgs-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; The chain splits at any segment boundary.
(defthm fn-lgs-chain-records-of-append
  (equal (fn-lgs-chain-records (append covered remaining) prev unit max)
         (append (fn-lgs-chain-records covered prev unit max)
                 (fn-lgs-chain-records remaining
                                       (fn-lgs-chain-last covered prev unit max)
                                       unit max)))
  :hints (("Goal" :induct (fn-lgs-chain-last covered prev unit max)
                  :in-theory (disable fn-lg-scan fn-lg-scan-last))))

; -----------------------------------------------------------------------------
; Rotation.  The active segment is closed where its kernel stands (no batch
; open, none in flight: fn-lgs-rotate-admitsp) and the next segment -- created
; preallocated to zeros and fenced with journal/ before anything names it --
; becomes the active one.  Its kernel (host/native/io.lisp fnn-log-rotate) is
; fn-lgs-rotate: no records, frontier 0, the genesis the closed segment's last
; trailer, the txid allocation carried.  That is the kernel recovery derives
; from the new segment's durable zeros (fn-lgs-rotate-is-the-recovered-kernel),
; so the relation R holds for the new segment by the fact that establishes it
; at log-recovered.

(defun fn-lgs-rotate-admitsp (ks)
  (declare (xargs :guard (true-listp ks)))
  (and (atom (fn-lgk-batch ks))
       (atom (fn-lgk-inflight ks))
       (not (equal (fn-lgk-phase ks) :fault))))

(defun fn-lgs-rotate (ks)
  (declare (xargs :guard (true-listp ks)))
  (fn-lgk-make nil (fn-lgk-last ks) 0 (fn-lgk-next-txid ks) nil nil 0 :ready))

(defthm fn-lgs-rotate-is-the-recovered-kernel
  (implies (fn-lg-zerosp z)
           (equal (fn-lgk-recover z (fn-lgk-last ks) unit max (fn-lgk-next-txid ks))
                  (fn-lgs-rotate ks)))
  :hints (("Goal" :in-theory (enable fn-lgk-recover))))

; -----------------------------------------------------------------------------
; T8: the drop preserves the open.
;
; COVERED are the segments below the F row's first suffix segment, REMAINING
; that segment and the ones after it.  Hypotheses: the checkpoint's capture is
; of the covered chain's records (the pipeline captures at the rotation, and
; fn-sct-load-of-publish-is-the-capture gives back what it captured) and the F
; row's genesis is the covered chain's last trailer (the rotation takes it
; from the closed segment's kernel, fn-lgs-rotate).  Then the history the open
; hands to the replay once the covered segments are unlinked -- the
; checkpoint's records, then the scan of the remaining segments from the named
; genesis (host/native/io.lisp fnn-recover-log) -- is the history of the full
; chain over every segment.  The replay over that split is the full replay by
; fn-sn-recover-from-checkpoint-equals-full-recover (the checkpoint's prefix
; and the suffix decode record by record into the events that theorem splits).
(defthm fn-lg-segment-drop-preserves-the-open
  (implies (and (equal prefix (fn-lgs-chain-records covered genesis0 unit max))
                (equal genesis (fn-lgs-chain-last covered genesis0 unit max)))
           (equal (append prefix (fn-lgs-chain-records remaining genesis unit max))
                  (fn-lgs-chain-records (append covered remaining) genesis0 unit max)))
  :hints (("Goal" :in-theory (disable fn-lgs-chain-records fn-lgs-chain-last))))
