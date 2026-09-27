; fn: the payload arena's extents at the open, and the served read's trailer
; check (lane arena-offheap-2, 2026-09-27; PRF-294; design:
; planning/evidence/arena-offheap-2026-09-27.md section 3).
;
; The open of a format-9 store scans each log segment (host/native/io.lisp
; fnn-log-scan-segments).  While the segment's octets are in hand, ACL2
; answers each committed record's PLACE: its entry's start and frame length,
; where the record starts in it and its length (`fn-arx-list-places' over
; each entry the stream reads: a batch's records share chunk entries).  The replay
; then interns each chunk with its positions (`fn-arx-intern-step'): a
; record whose payload the entry holds contiguously -- found by the codec's
; suffix length and VERIFIED octet for octet against the decoded payload
; (`fn-arx-extent-of') -- is sealed as an EXTENT (`fn-arena-seal-extent':
; no octets on the heap); any other event is interned as before.
;
; KEYSTONE fn-arx-intern-step-refines: when each record's octets are the
; durable octets at its place (`fn-arx-faithful-p': what the scan read is
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

;; -----------------------------------------------------------------------------
; 2. The records' PLACES in a segment, read from its entries (lane
; arena-offheap-3: stage 2 first assumed one record per entry; a batch of
; several records is one or more CHUNK entries, books/store-log.lisp fn-lg-log
; with fn-lg-chunk-len, kind 2, each record behind its u32 length).
;
; An entry at P is the frame -- header (magic 4, version 1, kind 1, the
; payload's length L as u32, 10 octets), the payload (the 32-octet chain and
; the body), the trailer (32) -- padded to the write unit (fn-lg-entry): its
; frame length N is 10 + L + 32 and the next entry starts at P + N + pad.
; Kind 1: the body is one record, at P + 42, of L - 32 octets.  Kind 2: the
; body is the packed records (fn-lg-pack), each a u32 length then the record.
; A record's PLACE is (START N ROFF RLEN): its entry's start and frame
; length, where the record starts, its length.  The walker reads an entry's
; octets as the open's stream reads them (host/native/io.lisp
; fnn-log-stream-segment: one entry at a time, at its offset) or the octets
; the commit wrote (fn-arx-list-places), COUNT records; anything that is not
; such an entry, or a count the entries do not hold, answers nil (every
; record stays resident).  The places decide nothing by themselves: the
; extent check (fn-arx-extent-of) requires the place's length to be the
; record's, and the served read checks the entry's own trailer.

(defconst *fn-arx-record-at* 42)

(local
 (defthm fn-arx-octets-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :rule-classes nil))

; A big-endian u32 from the first four elements of XS.
(defun fn-arx-u32-list (xs)
  (declare (xargs :guard (true-listp xs)))
  (+ (* 16777216 (nfix (nth 0 xs))) (* 65536 (nfix (nth 1 xs)))
     (* 256 (nfix (nth 2 xs))) (nfix (nth 3 xs))))

; The walk over an octet list.  TAIL is the octets from the entry at P; when
; inside a kind-2 body, QTAIL is the octets from Q, the body ends at QEND,
; and the entry is (EP EN).
(defun fn-arx-list-places (tail p count unit ep en qtail q qend acc)
  (declare (xargs :guard (and (true-listp tail) (true-listp qtail)
                              (natp p) (natp count) (natp ep) (natp en) (natp q) (natp qend)
                              (true-listp acc))
                  :measure (nfix count)
                  :hints (("Goal" :in-theory (disable nthcdr fn-lg-pad-len fn-arx-u32-list nth)))
                  :verify-guards nil))
  (cond ((zp count) (revappend acc nil))
        ((and (natp q) (natp qend) (< q qend))
         (let* ((rlen (fn-arx-u32-list qtail))
                (r (+ q 4))
                (q2 (+ r rlen))
                (acc (cons (list (nfix ep) (nfix en) r rlen) acc)))
           (cond ((< qend q2) nil)
                 ((equal q2 qend)
                  (let ((np (+ (nfix ep) (nfix en) (fn-lg-pad-len en unit))))
                    (fn-arx-list-places (nthcdr (nfix (- np (nfix p))) tail) np (1- count) unit
                                        0 0 nil 0 0 acc)))
                 (t (fn-arx-list-places tail p (1- count) unit ep en (nthcdr (+ 4 rlen) qtail)
                                        q2 qend acc)))))
        (t
         (let* ((p (nfix p))
                (kind (nfix (nth 5 tail)))
                (l (fn-arx-u32-list (nthcdr 6 tail)))
                (n (+ 10 l *fn-frame-trailer-octets*)))
           (cond ((not (consp (nthcdr 9 tail))) nil)
                 ((< l 32) nil)
                 ((equal kind 1)
                  (let ((np (+ p n (fn-lg-pad-len n unit))))
                    (fn-arx-list-places (nthcdr (nfix (- np p)) tail) np (1- count) unit 0 0 nil 0 0
                                        (cons (list p n (+ p *fn-arx-record-at*) (- l 32)) acc))))
                 ((and (equal kind 2) (<= 4 (- l 32)))
                  (let* ((q (+ p *fn-arx-record-at*))
                         (qend (+ q (- l 32)))
                         (qtail (nthcdr *fn-arx-record-at* tail))
                         (rlen (fn-arx-u32-list qtail))
                         (r (+ q 4))
                         (q2 (+ r rlen))
                         (acc (cons (list p n r rlen) acc)))
                    (cond ((< qend q2) nil)
                          ((equal q2 qend)
                           (let ((np (+ p n (fn-lg-pad-len n unit))))
                             (fn-arx-list-places (nthcdr (nfix (- np p)) tail) np (1- count) unit
                                                 0 0 nil 0 0 acc)))
                          (t (fn-arx-list-places tail p (1- count) unit p n
                                                 (nthcdr (+ 4 rlen) qtail) q2 qend acc)))))
                 (t nil))))))

(local
 (defthm fn-arx-true-listp-nthcdr
   (implies (true-listp x) (true-listp (nthcdr k x)))))

(verify-guards fn-arx-list-places
  :hints (("Goal" :in-theory (disable fn-lg-pad-len nthcdr fn-arx-u32-list nth))))

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

; The record R (octets) at its PLACE (START N ROFF RLEN) in FILE, decoded as
; the record W: the extent (FILE START N-32 POFF PLEN 0), or nil when the
; place is not R's (its length, or a record not inside the entry's protected
; prefix) or R does not hold W's payload at the codec's place.
(defun fn-arx-extent-of (file position r w)
  (declare (xargs :guard (and (natp file) (fn-record-p w) (true-listp r) (true-listp position))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let* ((start (nfix (nth 0 position)))
         (n (nfix (nth 1 position)))
         (roff (nfix (nth 2 position)))
         (p (fn-record-payload w))
         (plen (len p))
         (rlen (len r))
         (k (- rlen (+ (fn-arx-record-suffix-len w) plen))))
    (if (and (natp k)
             (equal (nth 3 position) rlen)
             (<= (+ start *fn-arx-record-at*) roff)
             (<= (+ roff rlen *fn-frame-trailer-octets*) (+ start n))
             (fn-arx-prefixp p (nthcdr k r)))
        (list (nfix file) start (- n *fn-frame-trailer-octets*) (+ roff k) plen 0)
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
; A record with no place (the scan could not place its segment's entries:
; the host's fnn-extent-positions answers NIL for each) is interned resident
; and needs nothing.
(defun-nx fn-arx-faithful-p (rs ps)
  (if (atom rs)
      t
    (and (or (atom (car ps))
             (equal (fn-durable-octets (nfix (car (car ps)))
                                       (nfix (nth 2 (cdr (car ps))))
                                       (len (car rs)))
                    (car rs)))
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
                (equal (fn-durable-octets (nfix file) (nfix (nth 2 position))
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
                                   (off (nfix (nth 2 position)))
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
                (equal (fn-durable-octets (nfix file) (nfix (nth 2 position))
                                          (len r))
                       r))
           (equal (fn-arx-intern-event w r position file keyring generation fn-arena)
                  (fn-intern-event w keyring generation fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-intern-event)
                                  (fn-arx-cat-intern-extent fn-cat-intern-list
                                   fn-stxa-p fn-replay-composite-record))
           :use ((:instance fn-arx-extent-of-denotes-payload)
                 (:instance fn-arx-record-payload-octets)))))

; With no place the event is the resident one, with no hypothesis: the
; place's frame length is 0, never a frame's (fn-arx-extent-of).
(defthm fn-arx-intern-event-without-place
  (equal (fn-arx-intern-event w r nil file keyring generation fn-arena)
         (fn-intern-event w keyring generation fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-arx-extent-of) (fn-arx-cat-intern-extent fn-intern-event)))))

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

; The chunk stream (host/native/io.lisp fnn-recover-record-chunks with the
; scan's positions, folded by fnn-bridge-recover): per chunk the host makes
; the decode and the extent step; PLACESS is each chunk's places.
(defun fn-arx-step (acc chunk places fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-arx-intern-step acc (fn-srs-decode chunk) chunk places fn-arena))

(defun fn-arx-steps (chunks placess acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (atom chunks)
      (mv acc fn-arena)
    (mv-let (acc fn-arena)
      (fn-arx-step acc (car chunks) (and (consp placess) (car placess)) fn-arena)
      (fn-arx-steps (cdr chunks) (and (consp placess) (cdr placess)) acc fn-arena))))

; Every chunk's records faithful at their places.
(defun-nx fn-arx-faithful-chunks-p (chunks placess)
  (if (atom chunks)
      t
    (and (fn-arx-faithful-p (car chunks) (and (consp placess) (car placess)))
         (fn-arx-faithful-chunks-p (cdr chunks) (and (consp placess) (cdr placess))))))

(local
 (defthm fn-arx-arena-p-of-intern-events
   (implies (fn-arena-p fn-arena)
            (fn-arena-p (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
   :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
            :in-theory (e/d (fn-intern-events)
                            (fn-intern-event fn-intern-event-arena fn-wire-event-p
                             fn-record-p fn-stxa-p fn-arena-p))))))

(local
 (defthm fn-arx-arena-p-of-srs-intern-step
   (implies (fn-arena-p fn-arena)
            (fn-arena-p (mv-nth 1 (fn-srs-intern-step acc ws fn-arena))))
   :hints (("Goal" :in-theory (disable fn-intern-events fn-arena-p)))))

(defthm fn-arx-steps-are-the-resident-steps
  (implies (and (fn-arena-p fn-arena)
                (fn-arx-faithful-chunks-p chunks placess))
           (equal (fn-arx-steps chunks placess acc fn-arena)
                  (fn-srs-steps chunks acc fn-arena)))
  :hints (("Goal" :induct (fn-arx-steps chunks placess acc fn-arena)
           :in-theory (disable fn-arx-intern-step fn-srs-intern-step fn-srs-decode))))

; KEYSTONE (PRF-294).  The chunk stream with extents: folding the host's
; extent step over ANY split of the history into chunks, each record faithful
; at its place, answers what one resident step over the whole history
; answers (fn-srs-steps-are-one-step-of-the-concatenation): :bad exactly when
; it is :bad, and otherwise the same rows and the same arena.
(defthm fn-arx-steps-are-one-step-of-the-concatenation
  (implies (and (fn-arena-p fn-arena)
                (fn-srs-chunksp chunks)
                (fn-arx-faithful-chunks-p chunks placess))
           (let ((steps (fn-arx-steps chunks placess acc fn-arena))
                 (one (fn-srs-step acc (fn-srs-concat chunks) fn-arena)))
             (and (iff (eq (mv-nth 0 steps) :bad) (eq (mv-nth 0 one) :bad))
                  (implies (not (eq (mv-nth 0 one) :bad))
                           (equal steps one)))))
  :hints (("Goal" :use (fn-arx-steps-are-the-resident-steps
                        (:instance fn-srs-steps-are-one-step-of-the-concatenation))
           :in-theory (disable fn-arx-steps fn-srs-steps fn-srs-step fn-arx-faithful-chunks-p
                               fn-srs-steps-are-one-step-of-the-concatenation
                               fn-arx-steps-are-the-resident-steps))))

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
