; fn: the COMMIT's extent reseat (lane arena-offheap-3, 2026-09-27; PRF-309;
; record planning/evidence/arena-offheap-3-2026-09-27.md).
;
; A POST's payload is sealed at its prepare, before its log batch is durable:
; the extent arena STAGES it (books/payload-arena-extent.lisp: the handle's
; own stage page, marked :staged).  Once the batch's barrier returned, the
; log entry holding the record is durable, and the payload is in it.  The
; owner then asks ACL2, per fenced member (host/native/io.lisp
; fnn-log-reseat-fenced), to re-point the handle at that extent:
;
;   fn-arx-commit-extent  where in the record the log wrote the handle's
;                         payload lies: the entry's frame must be the record's
;                         (42 + |r| + 32 octets), and the payload's octets
;                         must occur in the record, compared octet for octet
;                         against the arena's own copy (read by index, no
;                         list), in a bounded window before the record's end
;                         (the codec puts the payload item before a short
;                         suffix: groups, three strings, the charge, the
;                         stamp); no place found, no reseat (the payload stays
;                         staged: correct, only not yet off the heap).
;   fn-arx-commit-reseat  the reseat when the extent is found.
;
; Nothing here decodes the record or trusts the host's pairing of a handle
; with a record: a wrong pairing finds no place, and a place that is found
; holds exactly the arena's octets.  So the one assumption is the faithful
; WRITE (A-DURABLE-EXTENT with A-HOST's write): the file holds, at the
; entry's record position, the record the log wrote there.  KEYSTONE
; fn-arx-commit-reseat-keeps-the-arena: under it, the reseat leaves the
; arena -- every handle's payload -- unchanged (via the generic's
; fn-arena-reseat-extent-keeps-a-faithful-arena); the extent reads the same
; bytes the commit wrote.

(in-package "ACL2")
(include-book "payload-extent")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-arn-extent-guardp))))

(local (in-theory (disable fn-arx-prefixp)))

; -----------------------------------------------------------------------------
; 1. The payload's place, compared against the arena's copy.

; The arena's octets [J, N) of handle H open TAIL.
(defun fn-arx-arena-prefixp (h j n tail fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena))
                              (natp j) (natp n) (<= n (fn-arena-payload-len h fn-arena)))
                  :measure (nfix (- (nfix n) (nfix j)))))
  (if (or (not (natp j)) (not (natp n)) (<= n j))
      t
    (and (consp tail)
         (equal (car tail) (fn-arena-get h j fn-arena))
         (fn-arx-arena-prefixp h (1+ j) n (cdr tail) fn-arena))))

; The first I in [I, END] where the payload opens (nthcdr I r), walking the
; record's tails; nil when none.
(defun fn-arx-arena-find (h n tail i end fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena))
                              (natp n) (<= n (fn-arena-payload-len h fn-arena))
                              (natp i) (natp end))
                  :measure (nfix (- (1+ (nfix end)) (nfix i)))))
  (cond ((or (not (natp i)) (not (natp end)) (< end i)) nil)
        ((fn-arx-arena-prefixp h 0 n tail fn-arena) i)
        ((atom tail) nil)
        (t (fn-arx-arena-find h n (cdr tail) (1+ i) end fn-arena))))

; The window before the record's end searched for the payload: the codec's
; suffix after the payload item is a few hundred octets (fn-arx-record-suffix-len).
(defconst *fn-arx-commit-window* 4096)

; Where in R handle H's payload opens, searched in the window before R's
; end; nil when it does not (or does not fit).
(defun fn-arx-commit-place (h r fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena)) (true-listp r))))
  (let ((plen (fn-arena-payload-len h fn-arena))
        (rlen (len r)))
    (if (<= plen rlen)
        (let* ((end (- rlen plen))
               (from (nfix (- end *fn-arx-commit-window*))))
          (fn-arx-arena-find h plen (nthcdr from r) from end fn-arena))
      nil)))

; The extent of handle H's payload in the record R the log wrote at its
; PLACE (START N ROFF RLEN TRAILER) in FILE (books/payload-extent.lisp
; fn-arx-list-places, the entry's commitment attached by
; fn-arx-attach-trailers), or nil: the place must be R's (its length) and lie
; in the entry's protected prefix.  The descriptor carries TRAILER: the
; realizer decides every read against it (lane extent-identity, PRF-994).
(defun fn-arx-commit-extent (h file position r fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena))
                              (natp file) (true-listp position) (true-listp r))))
  (let* ((start (nfix (nth 0 position)))
         (n (nfix (nth 1 position)))
         (roff (nfix (nth 2 position)))
         (k (and (equal (nth 3 position) (len r))
                 (<= (+ start *fn-arx-record-at*) roff)
                 (<= (+ roff (len r) *fn-frame-trailer-octets*) (+ start n))
                 (fn-arx-commit-place h r fn-arena))))
    (if (natp k)
        (list (nfix file) start (- n *fn-frame-trailer-octets*)
              (+ roff k) (fn-arena-payload-len h fn-arena) (nfix (nth 4 position)))
      nil)))

(defthm fn-arx-arena-find-bounds
  (implies (fn-arx-arena-find h n tail i end fn-arena)
           (and (natp (fn-arx-arena-find h n tail i end fn-arena))
                (<= (fn-arx-arena-find h n tail i end fn-arena) end)
                (<= i (fn-arx-arena-find h n tail i end fn-arena))))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                  (implies (fn-arx-arena-find h n tail i end fn-arena)
                           (and (<= (fn-arx-arena-find h n tail i end fn-arena) end)
                                (<= i (fn-arx-arena-find h n tail i end fn-arena)))))
                 (:type-prescription :corollary
                  (or (equal (fn-arx-arena-find h n tail i end fn-arena) nil)
                      (natp (fn-arx-arena-find h n tail i end fn-arena)))))
  :hints (("Goal" :induct (fn-arx-arena-find h n tail i end fn-arena)
           :in-theory (disable fn-arx-arena-prefixp))))

(defthm fn-arx-commit-place-bounds
  (implies (fn-arx-commit-place h r fn-arena)
           (and (natp (fn-arx-commit-place h r fn-arena))
                (<= (+ (fn-arx-commit-place h r fn-arena) (fn-arena-payload-len h fn-arena))
                    (len r))))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                  (implies (fn-arx-commit-place h r fn-arena)
                           (<= (+ (fn-arx-commit-place h r fn-arena)
                                  (fn-arena-payload-len h fn-arena))
                               (len r))))
                 (:type-prescription :corollary
                  (or (equal (fn-arx-commit-place h r fn-arena) nil)
                      (natp (fn-arx-commit-place h r fn-arena)))))
  :hints (("Goal" :in-theory (disable fn-arx-arena-find fn-arena-payload-len-is-len-nth))))

(defthm fn-arx-commit-extent-extentp
  (implies (fn-arx-commit-extent h file position r fn-arena)
           (fn-arn-extentp (fn-arx-commit-extent h file position r fn-arena)))
  :hints (("Goal" :in-theory (disable fn-arx-commit-place fn-arena-payload-len-is-len-nth))))

(in-theory (disable fn-arx-commit-extent))

(defun fn-arx-commit-reseat (h file position r fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp file) (true-listp position) (true-listp r))))
  (if (and (natp h) (< h (fn-arena-count fn-arena)))
      (let ((x (fn-arx-commit-extent h file position r fn-arena)))
        (if (and (true-listp x)
                 (fn-arn-extent-guardp (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x)))
            (fn-arena-reseat-extent h (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x)
                                    fn-arena)
          fn-arena))
    fn-arena))

; The batch: MEMBERS a list of (H FILE POSITION R), the fenced members in
; the log's order.
(defun fn-arx-commit-reseats (members fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom members)
      fn-arena
    (let* ((m (car members))
           (fn-arena (if (and (true-listp m) (equal (len m) 4) (natp (nth 1 m))
                              (true-listp (nth 2 m)) (true-listp (nth 3 m)))
                         (fn-arx-commit-reseat (nth 0 m) (nth 1 m) (nth 2 m) (nth 3 m) fn-arena)
                       fn-arena)))
      (fn-arx-commit-reseats (cdr members) fn-arena))))

; -----------------------------------------------------------------------------
; 2. What a found place means.

(local
 (defthm fn-pce-take-cons
   (implies (posp n) (equal (take n (cons a x)) (cons a (take (1- n) x))))))

(local
 (defthm fn-pce-nthcdr-true-listp
   (implies (true-listp x) (true-listp (nthcdr k x)))))

(local
 (defthm fn-pce-nthcdr-opens
   (implies (and (natp j) (< j (len p)))
            (equal (nthcdr j p) (cons (nth j p) (nthcdr (1+ j) p))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-pce-take-0
   (equal (take 0 x) nil)))

(local
 (defthm fn-pce-nthcdr-len
   (implies (true-listp p) (equal (nthcdr (len p) p) nil))))

; The arena's octets from J match TAIL: TAIL opens with the payload's suffix
; from J.
(defthm fn-arx-arena-prefixp-is-take
  (implies (and (natp j) (true-listp (nth h fn-arena))
                (equal n (len (nth h fn-arena))) (<= j n)
                (fn-arx-arena-prefixp h j n tail fn-arena))
           (equal (take (- n j) tail)
                  (nthcdr j (nth h fn-arena))))
  :hints (("Goal" :induct (fn-arx-arena-prefixp h j n tail fn-arena)
           :in-theory (disable nthcdr take))
          ("Subgoal *1/2" :use ((:instance fn-pce-nthcdr-opens (p (nth h fn-arena))))
           :expand ((take (+ (len (nth h fn-arena)) (- j)) tail)))))

; A found place I is where the payload opens.
(defthm fn-arx-arena-find-is-a-place
  (implies (and (fn-arx-arena-find h n tail i end fn-arena) (natp i))
           (fn-arx-arena-prefixp h 0 n
                                 (nthcdr (- (fn-arx-arena-find h n tail i end fn-arena) i) tail)
                                 fn-arena))
  :hints (("Goal" :induct (fn-arx-arena-find h n tail i end fn-arena)
           :in-theory (e/d (nthcdr) (fn-arx-arena-prefixp)))))

(local
 (defthm fn-pce-nthcdr-nthcdr
   (implies (and (natp a) (natp b))
            (equal (nthcdr a (nthcdr b x)) (nthcdr (+ a b) x)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm fn-arx-arena-find-in-r
  (implies (and (fn-arx-arena-find h n (nthcdr from r) from end fn-arena) (natp from))
           (fn-arx-arena-prefixp h 0 n
                                 (nthcdr (fn-arx-arena-find h n (nthcdr from r) from end fn-arena) r)
                                 fn-arena))
  :hints (("Goal" :use ((:instance fn-arx-arena-find-is-a-place (tail (nthcdr from r)) (i from))
                        (:instance fn-pce-nthcdr-nthcdr (x r) (b from)
                                   (a (- (fn-arx-arena-find h n (nthcdr from r) from end fn-arena)
                                         from))))
           :in-theory (disable fn-arx-arena-find-is-a-place fn-arx-arena-find fn-pce-nthcdr-nthcdr
                               fn-arx-arena-prefixp nthcdr fn-arena-get-is-nth))))

(defthm fn-arx-commit-place-opens
  (implies (fn-arx-commit-place h r fn-arena)
           (fn-arx-arena-prefixp h 0 (len (nth h fn-arena))
                                 (nthcdr (fn-arx-commit-place h r fn-arena) r) fn-arena))
  :hints (("Goal" :in-theory (disable fn-arx-arena-find fn-arx-arena-prefixp nthcdr take
                                      fn-arx-arena-find-in-r fn-arx-arena-prefixp-is-take
                                      fn-arena-get-is-nth)
           :use ((:instance fn-arx-arena-find-in-r
                            (n (len (nth h fn-arena)))
                            (from (nfix (- (- (len r) (len (nth h fn-arena)))
                                           *fn-arx-commit-window*)))
                            (end (- (len r) (len (nth h fn-arena)))))))))

(local
 (defthm fn-pce-nthcdr-0
   (equal (nthcdr 0 x) x)))

; A found place is where the payload opens in R.
(defthm fn-arx-commit-place-is-a-place
  (implies (and (fn-arx-commit-place h r fn-arena) (true-listp (nth h fn-arena)))
           (equal (take (len (nth h fn-arena)) (nthcdr (fn-arx-commit-place h r fn-arena) r))
                  (nth h fn-arena)))
  :hints (("Goal" :in-theory (disable fn-arx-commit-place fn-arx-arena-prefixp nthcdr take
                                      fn-arx-commit-place-opens fn-arx-arena-prefixp-is-take
                                      fn-arena-get-is-nth)
           :use ((:instance fn-arx-commit-place-opens)
                 (:instance fn-arx-arena-prefixp-is-take
                            (j 0) (n (len (nth h fn-arena)))
                            (tail (nthcdr (fn-arx-commit-place h r fn-arena) r)))))))

(local
 (defthm fn-pce-durable-of-a-slice
   (implies (and (natp k) (natp m) (natp off) (<= (+ k m) (len r))
                 (equal (fn-durable-octets file off (len r)) r)
                 (equal (take m (nthcdr k r)) p))
            (equal (fn-durable-octets file (+ off k) m) p))
   :hints (("Goal" :use ((:instance fn-arx-durable-slice (len (len r))))
            :in-theory (disable fn-arx-durable-slice)))))

(local
 (defthm fn-pce-octets-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))))

(local
 (defthm fn-pce-payload-listp-nth-true-listp
   (implies (fn-arn-payload-listp a) (true-listp (nth h a)))
   :hints (("Goal" :in-theory (enable nth fn-arn-payload-listp)))))

(local
 (defthm fn-pce-arena-nth-true-listp
   (implies (fn-arena-p fn-arena) (true-listp (nth h fn-arena)))
   :hints (("Goal" :in-theory (enable fn-arena-p-is-payload-listp)))))

; The found extent denotes the arena's payload of H, when the file holds the
; record at the entry's record position (the faithful write).
(defthm fn-arx-commit-extent-denotes-the-payload
  (implies (and (fn-arena-p fn-arena)
                (fn-arx-commit-extent h file position r fn-arena)
                (equal (fn-durable-octets (nfix file) (nfix (nth 2 position))
                                          (len r))
                       r))
           (equal (fn-durable-octets (nth 0 (fn-arx-commit-extent h file position r fn-arena))
                                     (nth 3 (fn-arx-commit-extent h file position r fn-arena))
                                     (nth 4 (fn-arx-commit-extent h file position r fn-arena)))
                  (fn-arena-payload h fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-arx-commit-extent)
                           (fn-arx-commit-place fn-arx-commit-place-is-a-place
                            fn-pce-durable-of-a-slice nthcdr take fn-arena-get-is-nth))
           :use ((:instance fn-arx-commit-place-is-a-place)
                 (:instance fn-pce-durable-of-a-slice
                            (file (nfix file))
                            (off (nfix (nth 2 position)))
                            (k (fn-arx-commit-place h r fn-arena))
                            (m (len (nth h fn-arena)))
                            (p (nth h fn-arena)))))))

; -----------------------------------------------------------------------------
; 3. KEYSTONE (PRF-309).  The commit's reseat keeps the arena: when the file
; holds, at the entry's record position, the record the log wrote there
; (the faithful write: the log's pwrite and barrier returned, A-HOST, and the
; file keeps what it durably holds, A-DURABLE-EXTENT), every handle's payload
; after the reseat is what it was -- the extent reads the same bytes the
; commit wrote.  Host subject: host/native/io.lisp fnn-log-reseat-fenced
; calls fn-arx-commit-reseats after the batch's barrier.
(defthm fn-arx-commit-reseat-keeps-the-arena
  (implies (and (fn-arena-p fn-arena)
                (true-listp r)
                (equal (fn-durable-octets (nfix file) (nfix (nth 2 position))
                                          (len r))
                       r))
           (equal (fn-arx-commit-reseat h file position r fn-arena)
                  fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-arn-extent-guardp)
                                  (fn-arx-commit-extent fn-arena-reseat-extent-keeps-a-faithful-arena
                                   fn-arx-commit-extent-denotes-the-payload))
           :use ((:instance fn-arx-commit-extent-denotes-the-payload)
                 (:instance fn-arena-reseat-extent-keeps-a-faithful-arena
                            (file (nth 0 (fn-arx-commit-extent h file position r fn-arena)))
                            (eoff (nth 1 (fn-arx-commit-extent h file position r fn-arena)))
                            (elen (nth 2 (fn-arx-commit-extent h file position r fn-arena)))
                            (poff (nth 3 (fn-arx-commit-extent h file position r fn-arena)))
                            (plen (nth 4 (fn-arx-commit-extent h file position r fn-arena)))
                            (trailer (nth 5 (fn-arx-commit-extent h file position r fn-arena))))))))

; Every member of a fenced batch faithful at its place.
(defun-nx fn-arx-commit-faithful-p (members)
  (if (atom members)
      t
    (let ((m (car members)))
      (and (or (not (and (true-listp m) (equal (len m) 4) (natp (nth 1 m))
                         (true-listp (nth 2 m)) (true-listp (nth 3 m))))
               (equal (fn-durable-octets (nth 1 m) (nfix (nth 2 (nth 2 m)))
                                         (len (nth 3 m)))
                      (nth 3 m)))
           (fn-arx-commit-faithful-p (cdr members))))))

; KEYSTONE (PRF-309).  The batch the host reseats (fnn-log-reseat-fenced):
; every member faithful, the arena is unchanged.
(defthm fn-arx-commit-reseats-keep-the-arena
  (implies (and (fn-arena-p fn-arena)
                (fn-arx-commit-faithful-p members))
           (equal (fn-arx-commit-reseats members fn-arena)
                  fn-arena))
  :hints (("Goal" :induct (fn-arx-commit-reseats members fn-arena)
           :in-theory (disable fn-arx-commit-reseat))))
