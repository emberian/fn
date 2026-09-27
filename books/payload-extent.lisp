; fn: the payload arena's extents at the open, and the served read's trailer
; check (lane arena-offheap-2, 2026-09-27; PRF-294; design:
; planning/evidence/arena-offheap-2026-09-27.md section 3).
;
; The open of a format-9 store scans each log segment (host/native/io.lisp
; fnn-log-scan-segments).  While the segment's octets are in hand, ACL2
; answers each committed entry's POSITION: its start, its frame length and
; its trailer (`fn-arx-positions', stepped as the scan steps).  The replay
; then interns each chunk with its positions (`fn-arx-intern-step'): a
; record whose payload the entry holds contiguously -- found by the codec's
; suffix length and VERIFIED octet for octet against the decoded payload
; (`fn-arx-extent-of') -- is sealed as an EXTENT (`fn-arena-seal-extent':
; no octets on the heap); any other event is interned as before.
;
; KEYSTONE fn-arx-intern-step-refines: when each record's octets are the
; durable octets at its entry (`fn-arx-faithful-p': what the scan read is
; the file, A-HOST's read of a regular file and A-DURABLE-EXTENT), the
; extent intern answers exactly the rows and the arena of the resident
; intern (books/store-recover-stream.lisp fn-srs-intern-step), so every
; theorem about the open's rows and arena holds of it.
;
; The served read of an extent handle goes through the host's realizer
; (A-DURABLE-EXTENT), which preads the entry's protected prefix and asks
; ACL2 `fn-arx-entry-ok': SHA-256 of the octets read equals the trailer the
; open recorded.  fn-arx-entry-ok-of-durable: a faithful read passes (no
; false refusal).  A mismatch is refused by name (arena-extent-digest), a
; recovery event; it is never served.  The figure for a forged prefix that
; passes: a SHA-256 second preimage against the recorded trailer (the
; A-CRYPTO-TRAILER event); the collision figure, 2^-128, is the one to quote.

(in-package "ACL2")
(include-book "payload-arena")
(include-book "store-log")
(include-book "store-intern")
(include-book "store-recover-stream")
(include-book "sha256-stobj")

; -----------------------------------------------------------------------------
; 1. Octets as a big-endian natural (the trailer, 32 octets: one bignum).

(defun fn-arx-octets-nat (xs acc)
  (declare (xargs :guard (natp acc)))
  (if (atom xs)
      (nfix acc)
    (fn-arx-octets-nat (cdr xs) (+ (* 256 (nfix acc)) (nfix (car xs))))))

(defthm fn-arx-octets-nat-natp
  (natp (fn-arx-octets-nat xs acc))
  :rule-classes :type-prescription)

; -----------------------------------------------------------------------------
; 2. The entries' positions in a segment, from the records the scan read: an
; entry is the frame (the header, the chain, the record, the trailer: the
; log's fn-lg-frame) padded to the write unit (fn-lg-entry), so entry i+1
; starts where entry i's padding ends.  Per record (START N 0), N the frame's
; length; the realizer checks the entry's own trailer at [START+N-32,
; START+N) when it reads it (fn-arx-entry-ok), so a position that is not an
; entry is refused there, never served.

(defconst *fn-arx-record-at* 42)

(local
 (defthm fn-arx-octets-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :rule-classes nil))   ; the frame header (10) and the chain (32)

(defun fn-arx-positions (pos unit lens acc)
  (declare (xargs :guard (and (natp pos) (nat-listp lens) (true-listp acc))))
  (if (atom lens)
      (revappend acc nil)
    (let ((n (+ *fn-arx-record-at* (nfix (car lens)) *fn-frame-trailer-octets*)))
      (fn-arx-positions (+ (nfix pos) n (fn-lg-pad-len n unit)) unit (cdr lens)
                        (cons (list (nfix pos) n 0) acc)))))

; -----------------------------------------------------------------------------
; 3. The extent of one record, verified.

; The encoding after the payload item (books/records.lisp
; fn-record-encode-impl): the group count, the groups, three strings, the
; charge and the stamp.
(defun fn-arx-record-suffix-len (w)
  (declare (xargs :guard (fn-record-p w)
                  :guard-hints (("Goal" :in-theory (enable fn-record-p)))))
  (+ (len (fn-record-uint-encode (len (fn-record-groups w))))
     (len (fn-record-encode-groups (fn-record-groups w)))
     (len (fn-record-item-encode (cons :bytes (fn-record-string-octets (fn-record-obligation-id w)))))
     (len (fn-record-item-encode (cons :bytes (fn-record-string-octets (fn-record-content-subject w)))))
     (len (fn-record-item-encode (cons :bytes (fn-record-string-octets (fn-record-release-evidence w)))))
     (len (fn-record-uint-encode (fn-record-charge w)))
     (if (equal (fn-record-stamp w) :legacy) 0 (len (fn-record-uint-encode (fn-record-stamp w))))))

; P is a prefix of R.
(defun fn-arx-prefixp (p r)
  (declare (xargs :guard t))
  (if (atom p)
      t
    (and (consp r) (equal (car p) (car r)) (fn-arx-prefixp (cdr p) (cdr r)))))

; The record R (octets) at the entry POSITION (START N TRAILER) of FILE,
; decoded as the record W: the extent (FILE START N-32 POFF PLEN TRAILER),
; or nil when the entry does not hold W's payload at the codec's place.
(defun fn-arx-extent-of (file position r w)
  (declare (xargs :guard (and (natp file) (fn-record-p w) (true-listp r) (true-listp position))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let* ((start (nfix (nth 0 position)))
         (n (nfix (nth 1 position)))
         (trailer (nfix (nth 2 position)))
         (p (fn-record-payload w))
         (plen (len p))
         (rlen (len r))
         (k (- rlen (+ (fn-arx-record-suffix-len w) plen))))
    (if (and (natp k)
             (equal n (+ *fn-arx-record-at* rlen *fn-frame-trailer-octets*))
             (fn-arx-prefixp p (nthcdr k r)))
        (list (nfix file) start (- n *fn-frame-trailer-octets*)
              (+ start *fn-arx-record-at* k) plen trailer)
      nil)))

(defthm fn-arx-extent-of-extentp
  (implies (fn-arx-extent-of file position r w)
           (fn-arn-extentp (fn-arx-extent-of file position r w)))
  :hints (("Goal" :in-theory (disable fn-arx-record-suffix-len fn-arx-prefixp))))

(defthm fn-arx-extentp-guardp
  (implies (fn-arn-extentp x)
           (fn-arn-extent-guardp (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x))))

; -----------------------------------------------------------------------------
; 4. The intern with extents.

(defun fn-arx-cat-intern-extent (w x keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-record-p w) (fn-prin-keyringp keyring) (natp generation)
                              (fn-arn-extentp x))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let* ((bytes (fn-record-payload w))
         (h (fn-arena-count fn-arena))
         (fn-arena (fn-arena-seal-extent (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x)
                                         fn-arena)))
    (mv (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                      (fn-record-generation w) (fn-record-msgid w) h
                      (fn-record-groups w) (fn-record-obligation-id w)
                      (fn-record-content-subject w) (fn-record-release-evidence w)
                      (fn-record-charge w) (fn-record-stamp w)
                      (fn-held-facts-of bytes)
                      (fn-held-context-of bytes keyring generation)
                      nil nil)
        fn-arena)))

(local (in-theory (disable fn-arx-extent-of fn-arx-record-suffix-len)))

(local
 (defthm fn-arx-record-payload-octets
   (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))

(local
 (defthm fn-arx-composite-payload-octets
   (implies (fn-record-p (fn-replay-composite-record w))
            (fn-cbor-octet-listp (fn-record-payload (fn-replay-composite-record w))))
   :hints (("Goal" :use ((:instance fn-arx-record-payload-octets
                                    (w (fn-replay-composite-record w))))))))

(defun fn-arx-intern-event (w r position file keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp file) (fn-prin-keyringp keyring) (natp generation))
                  :guard-hints (("Goal" :in-theory (disable fn-record-p fn-intern-event
                                                            fn-arx-cat-intern-extent)))))
  (let ((x (and (fn-record-p w) (true-listp r) (true-listp position)
                (fn-arx-extent-of file position r w))))
    (if x
        (fn-arx-cat-intern-extent w x keyring generation fn-arena)
      (fn-intern-event w keyring generation fn-arena))))

(defthm fn-arx-arena-p-of-seal-extent
  (implies (fn-arena-p fn-arena)
           (fn-arena-p (fn-arena-seal-extent file eoff elen poff plen trailer fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-p-is-payload-listp)
           :use ((:instance fn-arn-payload-listp-of-append-one
                            (a fn-arena) (xs (fn-durable-octets file poff plen)))))))

; WS the decoded events, RS their octets, PS their positions (FILE . POSITION).
(defun fn-arx-intern-events (ws rs ps keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))
                  :guard-hints (("Goal" :in-theory (disable fn-arx-intern-event)))))
  (if (atom ws)
      (mv nil fn-arena)
    (let* ((r (and (consp rs) (car rs)))
           (p (and (consp ps) (consp (car ps)) (car ps)))
           (file (nfix (and (consp p) (car p))))
           (position (and (consp p) (cdr p))))
    (mv-let (row fn-arena)
      (fn-arx-intern-event (car ws) r position file keyring generation fn-arena)
      (if (eq row :bad)
          (mv :bad fn-arena)
        (mv-let (rest fn-arena)
          (fn-arx-intern-events (cdr ws) (and (consp rs) (cdr rs)) (and (consp ps) (cdr ps))
                                keyring generation fn-arena)
          (if (eq rest :bad)
              (mv :bad fn-arena)
            (mv (cons row rest) fn-arena))))))))

(defthm fn-arx-intern-events-true-listp
  (or (true-listp (mv-nth 0 (fn-arx-intern-events ws rs ps keyring generation fn-arena)))
      (equal (mv-nth 0 (fn-arx-intern-events ws rs ps keyring generation fn-arena)) :bad))
  :rule-classes nil
  :hints (("Goal" :induct (fn-arx-intern-events ws rs ps keyring generation fn-arena)
           :in-theory (disable fn-arx-intern-event))))

; The chunk step the host calls (fnn-bridge-recover), fn-srs-intern-step's
; twin with the chunk's octets and positions.
(defun fn-arx-intern-step (acc ws rs ps fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :guard-hints (("Goal" :use ((:instance fn-arx-intern-events-true-listp
                                                 (keyring nil) (generation 0)))
                                 :in-theory (disable fn-arx-intern-events)))))
  (if (or (eq acc :bad) (eq ws :bad))
      (mv :bad fn-arena)
    (mv-let (rows fn-arena)
      (fn-arx-intern-events ws rs ps nil 0 fn-arena)
      (if (eq rows :bad)
          (mv :bad fn-arena)
        (mv (revappend rows acc) fn-arena)))))

; -----------------------------------------------------------------------------
; 5. The refinement.

; Each record's octets are the durable octets of its file at its entry's
; record position (the scan read the file: A-HOST; the file holds what it
; durably wrote: A-DURABLE-EXTENT).
(defun-nx fn-arx-faithful-p (rs ps)
  (if (atom rs)
      t
    (and (equal (fn-durable-octets (nfix (car (car ps)))
                                   (+ (nfix (nth 0 (cdr (car ps)))) *fn-arx-record-at*)
                                   (len (car rs)))
                (car rs))
         (fn-arx-faithful-p (cdr rs) (cdr ps)))))

(local
 (defun fn-arx-slice-ind (k off len)
   (if (zp k) (list off len) (fn-arx-slice-ind (1- k) (+ 1 (nfix off)) (1- len)))))

(local
 (defthm fn-arx-durable-take
   (implies (and (natp m) (<= m (nfix len)))
            (equal (take m (fn-durable-octets file off len))
                   (fn-durable-octets file off m)))
   :hints (("Goal" :induct (fn-arx-slice-ind m off len)
            :in-theory (enable fn-durable-octets-unfold)))))

(local
 (defthm fn-arx-durable-nthcdr
   (implies (and (natp k) (<= k (nfix len)) (natp off))
            (equal (nthcdr k (fn-durable-octets file off len))
                   (fn-durable-octets file (+ off k) (- (nfix len) k))))
   :hints (("Goal" :induct (fn-arx-slice-ind k off len)
            :in-theory (enable fn-durable-octets-unfold)))))

(local
 (defthm fn-arx-prefixp-take
   (implies (and (fn-arx-prefixp p r) (true-listp p))
            (equal (take (len p) r) p))))

;; A slice of a durable extent is the durable extent of the slice.
(defthm fn-arx-durable-slice
  (implies (and (natp k) (natp m) (<= (+ k m) (nfix len)) (natp off))
           (equal (take m (nthcdr k (fn-durable-octets file off len)))
                  (fn-durable-octets file (+ off k) m))))

; The verified extent denotes the payload.
(defthm fn-arx-extent-of-denotes-payload
  (implies (and (fn-arx-extent-of file position r w)
                (equal (fn-durable-octets (nfix file) (+ (nfix (nth 0 position)) *fn-arx-record-at*)
                                          (len r))
                       r)
                (true-listp (fn-record-payload w)))
           (equal (fn-durable-octets (nth 0 (fn-arx-extent-of file position r w))
                                     (nth 3 (fn-arx-extent-of file position r w))
                                     (nth 4 (fn-arx-extent-of file position r w)))
                  (fn-record-payload w)))
  :hints (("Goal" :use ((:instance fn-arx-durable-slice
                                   (k (- (len r) (+ (fn-arx-record-suffix-len w)
                                                    (len (fn-record-payload w)))))
                                   (m (len (fn-record-payload w)))
                                   (file (nfix file))
                                   (off (+ (nfix (nth 0 position)) *fn-arx-record-at*))
                                   (len (len r)))
                        (:instance fn-arx-prefixp-take
                                   (p (fn-record-payload w))
                                   (r (nthcdr (- (len r) (+ (fn-arx-record-suffix-len w)
                                                            (len (fn-record-payload w))))
                                              r))))
           :in-theory (e/d (fn-arx-extent-of)
                           (fn-arx-durable-slice fn-arx-prefixp-take
                            fn-arx-record-suffix-len)))))

(defthm fn-arx-cat-intern-extent-refines
  (implies (and (fn-arena-p fn-arena)
                (equal (fn-durable-octets (nth 0 x) (nth 3 x) (nth 4 x)) (fn-record-payload w)))
           (equal (fn-arx-cat-intern-extent w x keyring generation fn-arena)
                  (fn-cat-intern-list w keyring generation fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-cat-intern-list)
                                  (fn-record-p fn-held-facts-of fn-held-context-of)))))

(defthm fn-arx-intern-event-refines
  (implies (and (fn-arena-p fn-arena)
                (equal (fn-durable-octets (nfix file) (+ (nfix (nth 0 position)) *fn-arx-record-at*)
                                          (len r))
                       r))
           (equal (fn-arx-intern-event w r position file keyring generation fn-arena)
                  (fn-intern-event w keyring generation fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-intern-event)
                                  (fn-arx-cat-intern-extent fn-cat-intern-list
                                   fn-stxa-p fn-replay-composite-record))
           :use ((:instance fn-arx-extent-of-denotes-payload)
                 (:instance fn-arx-record-payload-octets)))))

(defthm fn-arx-durable-octets-empty
  (implies (zp len) (equal (fn-durable-octets file off len) nil))
  :hints (("Goal" :in-theory (enable fn-durable-octets-unfold))))

(local
 (defthm fn-arx-arena-p-of-seal-list
   (implies (and (fn-arena-p fn-arena) (fn-cbor-octet-listp xs))
            (fn-arena-p (fn-arena-seal-list xs fn-arena)))
   :hints (("Goal" :in-theory (enable fn-arena-p-is-payload-listp)))))

(local
 (defthm fn-arx-arena-p-of-intern-event
   (implies (fn-arena-p fn-arena)
            (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
   :hints (("Goal" :in-theory (disable fn-intern-event fn-record-p fn-stxa-p
                                       fn-replay-composite-record fn-arena-seal-list-is-append)))))

(defthm fn-arx-intern-events-refines
  (implies (and (fn-arena-p fn-arena)
                (fn-arx-faithful-p rs ps))
           (equal (fn-arx-intern-events ws rs ps keyring generation fn-arena)
                  (fn-intern-events ws keyring generation fn-arena)))
  :hints (("Goal" :induct (fn-arx-intern-events ws rs ps keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-arx-intern-event fn-intern-event fn-intern-event-arena)))))

; KEYSTONE (PRF-294).  The host's chunk step with extents
; (host/native/io.lisp fnn-bridge-recover calls fn-arx-intern-step) is the
; resident chunk step whenever each record's octets are the durable octets at
; its entry: the same rows, the same arena (whose extent handles hold no
; octets on the heap).
(defthm fn-arx-intern-step-refines
  (implies (and (fn-arena-p fn-arena)
                (fn-arx-faithful-p rs ps))
           (equal (fn-arx-intern-step acc ws rs ps fn-arena)
                  (fn-srs-intern-step acc ws fn-arena)))
  :hints (("Goal" :in-theory (disable fn-arx-intern-events fn-intern-events))))

; -----------------------------------------------------------------------------
; 6. The served read's check and the read cache's bound.

; The realizer's check over the entry as read, its protected prefix
; (ELEN octets) and then its trailer: SHA-256 of the prefix is the trailer
; (the frame's own trailer, fn-frame-digest under the host's attachment,
; which the open's scan checked when it read the entry).
(defun fn-arx-entry-ok (octets elen)
  (declare (xargs :guard (natp elen)))
  (let ((prefix (take (min (nfix elen) (len octets)) (true-list-fix octets)))
        (trailer (nthcdr (nfix elen) (true-list-fix octets))))
    (and (equal (len octets) (+ (nfix elen) *fn-frame-trailer-octets*))
         (equal (fn-sha256-stobj prefix) trailer))))

(local
 (defthm fn-arx-durable-true-listp
   (true-listp (fn-durable-octets file off len))
   :hints (("Goal" :use ((:instance fn-arx-octets-true-listp
                                    (x (fn-durable-octets file off len))))))))

(local
 (defthm fn-arx-take-append-len
   (implies (and (true-listp a) (equal n (len a)))
            (equal (take n (append a b)) a))))

(local
 (defthm fn-arx-nthcdr-append-len
   (implies (equal n (len a))
            (equal (nthcdr n (append a b)) b))))

; A faithful read of an intact entry passes: when the file holds, after the
; entry's protected prefix, that prefix's digest, reading prefix and trailer
; is accepted (no false refusal).
(defthm fn-arx-entry-ok-of-durable
  (implies (and (natp elen)
                (equal (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*)
                       (fn-sha256 (fn-durable-octets file eoff elen))))
           (fn-arx-entry-ok (append (fn-durable-octets file eoff elen)
                                    (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*))
                            elen))
  :hints (("Goal" :in-theory (enable fn-sha256-stobj-is-sha256))))

; The realizer's cache: at most this many verified entries (each at most the
; log's entry bound, fnn-store-log-max): the bound on the octets the host
; holds for reads of extent handles.
(defun fn-arx-read-cache-entries ()
  (declare (xargs :guard t))
  8)
