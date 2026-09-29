; fn: the queued submission packed (lane chunked-body-2, row B6b of
; COMPLETE-BEFORE-6.6.0, 2026-09-29; D27; D35 F8).
;
; A submission waits in the owner's queue (books/owner.lisp fn-own-queue)
; from the read that completed its article until the committer takes it.
; Its decision (books/injection.lisp fn-inj-make-decision, or the transit
; record books/peer-inbound.lisp fn-peer-make-submission) carries the
; article's octets and, for an injection, the groups its Newsgroups header
; names -- octet lists, sixteen octets of heap an octet: the term that made
; the per-article credit (books/heap-store-figure.lisp
; fn-heap-article-reserve-octets) sixteen times the article.  This book is
; the queued form: the octets packed into ONE natural (books/packed-octets.lisp
; fn-bch-pack: one octet a byte) and the groups joined by commas (a group
; name holds no comma, RFC 5536 section 3.1.4) and packed the same way.
; The owner packs at enqueue and unpacks at the take (fn-own-enqueue,
; fn-own-take-submission), so the taken submission -- the one the durable
; path reads -- is the submission that was enqueued, exactly.
;
; Every packing here is TOTAL with an unconditional round trip: a field that
; is not an octet list (a list of joinable names) is kept as (:raw . X).
;
; KEYSTONES
;   fn-psub-unpack-of-pack-octets    the octets round trip (no hypothesis);
;   fn-psub-unpack-of-pack-groups    the groups round trip (no hypothesis);
;   fn-psub-unpack-of-pack-sub       the submission round trip (no
;                                    hypothesis): what the take installs is
;                                    what the read enqueued.
;   fn-psub-packed-octets-len-is-len the packed octets' length (what the
;                                    credit charges) is the article's.

(in-package "ACL2")
(include-book "packed-octets")
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/append" :dir :system))

; -----------------------------------------------------------------------------
; A list's first N elements and the rest (total; the rest by a loop).

(defun fn-psub-first (xs n)
  (declare (xargs :guard t :measure (nfix n)))
  (if (and (consp xs) (posp n))
      (cons (car xs) (fn-psub-first (cdr xs) (- n 1)))
    nil))

(defun fn-psub-drop (xs n)
  (declare (xargs :guard t :measure (nfix n)))
  (if (and (consp xs) (posp n))
      (fn-psub-drop (cdr xs) (- n 1))
    xs))

(local
 (defthm fn-psub-len-of-first
   (implies (<= (nfix n) (len xs))
            (equal (len (fn-psub-first xs n)) (nfix n)))))

(local
 (defthm fn-psub-len-of-drop
   (implies (<= (nfix n) (len xs))
            (equal (len (fn-psub-drop xs n)) (- (len xs) (nfix n))))))

(local
 (defthm fn-psub-first-of-len
   (implies (and (true-listp xs) (equal n (len xs)))
            (equal (fn-psub-first xs n) xs))))

(local
 (defthm fn-psub-first-splits
   (implies (and (natp h) (natp n) (<= h n))
            (equal (fn-psub-first xs n)
                   (append (fn-psub-first xs h)
                           (fn-psub-first (fn-psub-drop xs h) (- n h)))))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; Packing a list: divide and conquer.  At most eight octets by Horner's rule
; (fn-psub-pack-small, a frame each: at most eight); else the two halves
; packed and the high one shifted past the low one's octets
; (fn-bch-pack-of-append).  Depth log2 of the length; each level one shift.

(defun fn-psub-pack-small (xs n)
  (declare (xargs :guard t :measure (nfix n)))
  (if (and (consp xs) (posp n))
      (+ (fn-bch-byte (car xs)) (* 256 (fn-psub-pack-small (cdr xs) (- n 1))))
    1))

(local
 (defthm fn-psub-pack-small-is-pack
   (equal (fn-psub-pack-small xs n) (fn-bch-pack (fn-psub-first xs n)))))

(defthm fn-psub-pack-small-posp
  (posp (fn-psub-pack-small xs n))
  :rule-classes :type-prescription)

(defun fn-psub-pack-dc (xs n)
  (declare (xargs :guard (and (natp n) (<= n (len xs)))
                  :measure (nfix n) :verify-guards nil))
  (if (or (zp n) (<= n 8))
      (fn-psub-pack-small xs n)
    (let* ((h (floor n 2))
           (lo (fn-psub-pack-dc xs h))
           (hi (fn-psub-pack-dc (fn-psub-drop xs h) (- n h))))
      (+ lo (fn-bch-shift (- hi 1) h)))))

(local
 (defthm fn-psub-pack-of-first-splits
   (implies (and (natp h) (natp n) (<= h n) (<= n (len xs)))
            (equal (fn-bch-pack (fn-psub-first xs n))
                   (+ (fn-bch-pack (fn-psub-first xs h))
                      (* (fn-bch-pow h)
                         (- (fn-bch-pack (fn-psub-first (fn-psub-drop xs h) (- n h))) 1)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-psub-first-splits))))))

; The divide and conquer is the logical packing of the first N (a lemma of
; the round trip below, which is what the host's call, fn-psub-pack-octets,
; is held to).
(defthm fn-psub-pack-dc-is-pack
  (implies (<= (nfix n) (len xs))
           (equal (fn-psub-pack-dc xs n)
                  (fn-bch-pack (fn-psub-first xs n))))
  :hints (("Goal" :induct (fn-psub-pack-dc xs n))
          ("Subgoal *1/2" :use ((:instance fn-psub-pack-of-first-splits (h (floor n 2)))))))

(defthm fn-psub-pack-dc-posp
  (implies (<= (nfix n) (len xs))
           (posp (fn-psub-pack-dc xs n)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable fn-psub-pack-dc))))

(verify-guards fn-psub-pack-dc)

; -----------------------------------------------------------------------------
; The octets field: an octet list packs to (LEN . N); anything else is kept.

(local
 (defthm fn-psub-len-of-bytes
   (equal (len (fn-bch-bytes xs)) (len xs))))

(local
 (defthm fn-psub-digits-of-pack
   (equal (fn-bch-digits (fn-bch-pack xs) (len xs)) (fn-bch-bytes xs))
   :hints (("Goal" :use ((:instance fn-bch-unpack-is-digits (n (fn-bch-pack xs))))
                   :in-theory (disable fn-bch-unpack-is-digits fn-bch-digits
                                       fn-bch-pack fn-bch-unpack)))))

(local
 (defthm fn-psub-append-nil-of-digits
   (equal (append (fn-bch-digits n len) nil) (fn-bch-digits n len))))

(local
 (defthm fn-psub-octetsp-true-listp
   (implies (fn-bch-octetsp x) (true-listp x))
   :rule-classes :forward-chaining))

(local
 (defthm fn-psub-pack-dc-of-len
   (implies (fn-bch-octetsp x)
            (equal (fn-psub-pack-dc x (len x)) (fn-bch-pack x)))
   :hints (("Goal" :in-theory (disable fn-psub-pack-dc fn-bch-pack)))))

(defun fn-psub-pack-octets (x)
  (declare (xargs :guard t))
  (if (fn-bch-octetsp x)
      (cons (len x) (fn-psub-pack-dc x (len x)))
    (cons :raw x)))

(defun fn-psub-packed-octetsp (p)
  (declare (xargs :guard t))
  (and (consp p) (natp (car p)) (natp (cdr p))))

(defun fn-psub-unpack-octets (p)
  (declare (xargs :guard t))
  (if (fn-psub-packed-octetsp p)
      (fn-bch-digits-onto (cdr p) (car p) nil)
    (if (consp p) (cdr p) p)))

; KEYSTONE (no hypothesis): the octets field round trips.
(defthm fn-psub-unpack-of-pack-octets
  (equal (fn-psub-unpack-octets (fn-psub-pack-octets x)) x)
  :hints (("Goal" :in-theory (disable fn-psub-pack-dc fn-bch-pack fn-bch-digits))))

; The length the credit charges (books/owner-credits.lisp fn-mca-sub-charge).
(defun fn-psub-packed-octets-len (p)
  (declare (xargs :guard t))
  (if (fn-psub-packed-octetsp p)
      (car p)
    (len (if (consp p) (cdr p) p))))

(defthm fn-psub-packed-octets-len-is-len
  (equal (fn-psub-packed-octets-len (fn-psub-pack-octets x)) (len x)))

; -----------------------------------------------------------------------------
; The groups: joined by commas (44) and packed.  Joinable: at least one
; name, each a nonempty octet list without a comma.

(defun fn-psub-namep (g)
  (declare (xargs :guard t))
  (and (consp g) (fn-bch-octetsp g) (not (member 44 g))))

(defun fn-psub-joinablep (gs)
  (declare (xargs :guard t))
  (if (consp gs)
      (and (fn-psub-namep (car gs))
           (or (null (cdr gs)) (fn-psub-joinablep (cdr gs))))
    nil))

; The join, logically; executed reversed onto an accumulator (a loop).
(local
 (defthm fn-psub-namep-true-listp
   (implies (fn-psub-namep g) (true-listp g))
   :rule-classes :forward-chaining))

(local
 (defthm fn-psub-joinablep-true-list-listp
   (implies (fn-psub-joinablep gs) (true-list-listp gs))))

(defun fn-psub-join (gs)
  (declare (xargs :guard (true-list-listp gs)))
  (if (consp gs)
      (if (consp (cdr gs))
          (append (car gs) (cons 44 (fn-psub-join (cdr gs))))
        (car gs))
    nil))

(defun fn-psub-join-rev-onto (gs acc)
  (declare (xargs :guard (and (true-list-listp gs) (true-listp acc))))
  (if (consp gs)
      (fn-psub-join-rev-onto (cdr gs)
                             (if (consp (cdr gs))
                                 (cons 44 (revappend (car gs) acc))
                               (revappend (car gs) acc)))
    acc))

(local
 (defthm fn-psub-join-rev-onto-is
   (equal (fn-psub-join-rev-onto gs acc)
          (revappend (fn-psub-join gs) acc))))

(local
 (defthm fn-psub-revappend-revappend
   (implies (true-listp g)
            (equal (revappend (revappend g nil) nil) g))))

(local
 (defthm fn-psub-true-listp-of-join
   (implies (true-list-listp gs) (true-listp (fn-psub-join gs)))))

(defun fn-psub-join-exec (gs)
  (declare (xargs :guard (true-list-listp gs)))
  (mbe :logic (fn-psub-join gs)
       :exec (revappend (fn-psub-join-rev-onto gs nil) nil)))

; The split at commas: CUR the current name reversed, ACC the names
; reversed.  A loop.
(defun fn-psub-split-onto (xs cur acc)
  (declare (xargs :guard (and (true-listp cur) (true-listp acc))))
  (if (consp xs)
      (if (equal (car xs) 44)
          (fn-psub-split-onto (cdr xs) nil (cons (revappend cur nil) acc))
        (fn-psub-split-onto (cdr xs) (cons (car xs) cur) acc))
    (revappend (cons (revappend cur nil) acc) nil)))

(local
 (defun fn-psub-name-ind (g cur)
   (if (consp g) (fn-psub-name-ind (cdr g) (cons (car g) cur)) cur)))

(local
 (defthm fn-psub-split-onto-of-name
   (implies (not (member 44 g))
            (equal (fn-psub-split-onto (append g ys) cur acc)
                   (fn-psub-split-onto ys (revappend g cur) acc)))
   :hints (("Goal" :induct (fn-psub-name-ind g cur))
           ("Subgoal *1/1" :expand ((rev g))))))

(local
 (defthm fn-psub-split-onto-of-last-name
   (implies (and (not (member 44 g)) (true-listp g))
            (equal (fn-psub-split-onto g cur acc)
                   (revappend (cons (revappend (revappend g cur) nil) acc) nil)))
   :hints (("Goal" :use ((:instance fn-psub-split-onto-of-name (ys nil)))
                   :in-theory (disable fn-psub-split-onto-of-name)))))

(local
 (defun fn-psub-join-ind (gs acc)
   (if (and (consp gs) (consp (cdr gs)))
       (fn-psub-join-ind (cdr gs) (cons (car gs) acc))
     acc)))

(local
 (defthm fn-psub-split-onto-of-join
   (implies (fn-psub-joinablep gs)
            (equal (fn-psub-split-onto (fn-psub-join gs) nil acc)
                   (revappend acc gs)))
   :hints (("Goal" :induct (fn-psub-join-ind gs acc)))))

(local
 (defthm fn-psub-octetsp-of-append
   (implies (and (fn-bch-octetsp a) (fn-bch-octetsp b))
            (fn-bch-octetsp (append a b)))))

(local
 (defthm fn-psub-octetsp-of-join
   (implies (fn-psub-joinablep gs)
            (fn-bch-octetsp (fn-psub-join gs)))))

(defun fn-psub-pack-groups (gs)
  (declare (xargs :guard t))
  (if (fn-psub-joinablep gs)
      (cons :g (fn-psub-pack-octets (fn-psub-join-exec gs)))
    (cons :raw gs)))

(defun fn-psub-unpack-groups (p)
  (declare (xargs :guard t))
  (if (and (consp p) (equal (car p) :g))
      (fn-psub-split-onto (fn-psub-unpack-octets (cdr p)) nil nil)
    (if (consp p) (cdr p) p)))

; KEYSTONE (no hypothesis): the groups round trip.
(defthm fn-psub-unpack-of-pack-groups
  (equal (fn-psub-unpack-groups (fn-psub-pack-groups gs)) gs)
  :hints (("Goal" :in-theory (disable fn-psub-pack-octets fn-psub-unpack-octets
                                      fn-psub-split-onto))))

; The octets the packed groups hold, and the list form's cells otherwise.
(defun fn-psub-names-cells-onto (gs n)
  (declare (xargs :guard (natp n)))
  (if (consp gs)
      (fn-psub-names-cells-onto (cdr gs) (+ n 1 (len (car gs))))
    n))

(defthm fn-psub-names-cells-onto-natp
  (implies (natp n) (natp (fn-psub-names-cells-onto gs n)))
  :rule-classes :type-prescription)

(defthm fn-psub-packed-octets-len-natp
  (natp (fn-psub-packed-octets-len p))
  :rule-classes :type-prescription)

(defun fn-psub-packed-groups-heap (p)
  (declare (xargs :guard t))
  (if (and (consp p) (equal (car p) :g))
      (+ 64 (fn-psub-packed-octets-len (cdr p)))
    (* 16 (fn-psub-names-cells-onto (if (consp p) (cdr p) p) 1))))

; -----------------------------------------------------------------------------
; The decision: a five-element list.  A transit record (car :transit;
; peer, kind, Message-ID, octets) packs its octets; an injection (status,
; reason, Message-ID, groups, octets) its groups and its octets.  The other
; fields -- the Message-ID the queue's readers look up among others -- stay.

(defun fn-psub-decision-shapep (d)
  (declare (xargs :guard t))
  (and (true-listp d) (equal (len d) 5)))

(defun fn-psub-pack-decision (d)
  (declare (xargs :guard t))
  (if (fn-psub-decision-shapep d)
      (list (nth 0 d) (nth 1 d) (nth 2 d)
            (if (equal (nth 0 d) :transit) (nth 3 d) (fn-psub-pack-groups (nth 3 d)))
            (fn-psub-pack-octets (nth 4 d)))
    d))

(defun fn-psub-unpack-decision (d)
  (declare (xargs :guard t))
  (if (fn-psub-decision-shapep d)
      (list (nth 0 d) (nth 1 d) (nth 2 d)
            (if (equal (nth 0 d) :transit) (nth 3 d) (fn-psub-unpack-groups (nth 3 d)))
            (fn-psub-unpack-octets (nth 4 d)))
    d))

(local
 (defthm fn-psub-true-listp-len-zero
   (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
   :rule-classes :forward-chaining))

(local
 (defthm fn-psub-five-list
   (implies (fn-psub-decision-shapep d)
            (equal (list (nth 0 d) (nth 1 d) (nth 2 d) (nth 3 d) (nth 4 d)) d))
   :hints (("Goal" :expand ((nth 0 d) (nth 1 d) (nth 2 d) (nth 3 d) (nth 4 d)
                            (len d) (len (cdr d)) (len (cddr d)) (len (cdddr d))
                            (len (cddddr d)))))))

(defthm fn-psub-unpack-of-pack-decision
  (equal (fn-psub-unpack-decision (fn-psub-pack-decision d)) d)
  :hints (("Goal" :use ((:instance fn-psub-five-list))
                  :in-theory (disable fn-psub-five-list fn-psub-pack-groups fn-psub-unpack-groups
                                      fn-psub-pack-octets fn-psub-unpack-octets))))

(defthm fn-psub-pack-decision-fields
  (and (equal (nth 0 (fn-psub-pack-decision d)) (nth 0 d))
       (equal (nth 1 (fn-psub-pack-decision d)) (nth 1 d))
       (equal (nth 2 (fn-psub-pack-decision d)) (nth 2 d))
       (equal (fn-psub-decision-shapep (fn-psub-pack-decision d))
              (fn-psub-decision-shapep d)))
  :hints (("Goal" :in-theory (disable fn-psub-pack-groups fn-psub-pack-octets))))

(defthm fn-psub-pack-decision-transit-field
  (implies (equal (nth 0 d) :transit)
           (equal (nth 3 (fn-psub-pack-decision d)) (nth 3 d)))
  :hints (("Goal" :in-theory (disable fn-psub-pack-groups fn-psub-pack-octets))))

; -----------------------------------------------------------------------------
; The submission: (id version mark decision . rest).  The decision packed.

(defun fn-psub-sub-shapep (x)
  (declare (xargs :guard t))
  (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x))))

(defun fn-psub-pack-sub (x)
  (declare (xargs :guard t))
  (if (fn-psub-sub-shapep x)
      (list* (car x) (cadr x) (caddr x) (fn-psub-pack-decision (cadddr x)) (cddddr x))
    x))

(defun fn-psub-unpack-sub (x)
  (declare (xargs :guard t))
  (if (fn-psub-sub-shapep x)
      (list* (car x) (cadr x) (caddr x) (fn-psub-unpack-decision (cadddr x)) (cddddr x))
    x))

; KEYSTONE (no hypothesis): the submission round trips.
(defthm fn-psub-unpack-of-pack-sub
  (equal (fn-psub-unpack-sub (fn-psub-pack-sub x)) x)
  :hints (("Goal" :in-theory (disable fn-psub-pack-decision fn-psub-unpack-decision))))

(defthm fn-psub-pack-sub-fields
  (and (equal (car (fn-psub-pack-sub x)) (car x))
       (equal (cadr (fn-psub-pack-sub x)) (cadr x))
       (equal (caddr (fn-psub-pack-sub x)) (caddr x))
       (equal (cddddr (fn-psub-pack-sub x)) (cddddr x))
       (equal (cadddr (fn-psub-pack-sub x))
              (if (fn-psub-sub-shapep x) (fn-psub-pack-decision (cadddr x)) (cadddr x)))
       (equal (consp (fn-psub-pack-sub x)) (consp x))
       (equal (len (fn-psub-pack-sub x)) (len x))
       (equal (true-listp (fn-psub-pack-sub x)) (true-listp x)))
  :hints (("Goal" :in-theory (disable fn-psub-pack-decision))))

; -----------------------------------------------------------------------------
; What a queued (packed) submission holds, in octets of heap: the packed
; octets (a natural, one octet a byte, and its cons: 48), the packed groups,
; the Message-ID as an octet list (at most 250 octets, RFC 5536 section
; 3.1.3), and the records' cells (512).  books/owner-credits.lisp charges
; twice this (the collector's copy).
(defun fn-psub-sub-heap (x)
  (declare (xargs :guard t))
  (let ((d (if (fn-psub-sub-shapep x) (cadddr x) nil)))
    (if (fn-psub-decision-shapep d)
        (+ 512
           (+ 48 (fn-psub-packed-octets-len (nth 4 d)))
           (if (equal (nth 0 d) :transit)
               (* 16 (len (nth 3 d)))
             (+ (fn-psub-packed-groups-heap (nth 3 d))
                (* 16 (len (nth 2 d))))))
      512)))

(defthm fn-psub-sub-heap-natp
  (natp (fn-psub-sub-heap x))
  :rule-classes :type-prescription)

(in-theory (disable fn-psub-pack-octets fn-psub-unpack-octets fn-psub-pack-groups
                    fn-psub-unpack-groups fn-psub-pack-decision fn-psub-unpack-decision
                    fn-psub-pack-sub fn-psub-unpack-sub fn-psub-sub-heap))
