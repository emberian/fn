; fn: the heap a store needs in the flipped representation (lane
; reservation-after-flip, 2026-09-27; D27, D35 F8; PRF-198's figure,
; books/heap-figure.lisp, re-derived from the arena).
;
; Until the records flip (lanes flip-L1 to flip-L6-2) every retained payload
; was an octet list, sixteen bytes of heap per octet, and heap-figure charged
; the history as list copies: 2 x 16 x (2H + R + 3 HDR), the collector's copy
; included.  The flip moved the retained payloads into the payload arena
; (books/payload-arena-bytes.lisp: one byte array, an offset and a size per
; handle), so the served state is no longer the lists; but two things were
; not flipped, and this figure counts each by what it is, measured on the
; flipped image (planning/evidence/reservation-after-flip-2026-09-27.md):
;
;   THE STATE a store of USED payload octets and N records keeps, after a
;   full collection:
;     arena    the byte array, one byte per octet; it doubles when full
;              (fn-arn-write-octet), so its capacity is at most twice the
;              octets it holds, and while a resize copies it the old array
;              is live beside the new: 3 x USED at the peak.  A large object:
;              the collector never copies it.
;     handles  the offset and size arrays, 8 bytes each per handle, doubling
;              the same way: 48 x N at the peak.
;     records  the rest of a record's retained state (the held record, its
;              catalog rows, the Message-ID and group indexes, the views):
;              small objects the collector copies, so twice.  Measured at
;              3.5 to 3.7 KiB a record after a reopen and 4.4 to 4.8 KiB while
;              serving, whatever the article's size or its Subject's length
;              (1,000 and 2,000 articles of 400 octets to 8,000 octets, a
;              1,500-octet folded Subject), plus 0.25 KiB for each group past
;              the first the article is posted to: *fn-heap-record-octets*
;              and *fn-heap-membership-octets* a group, G groups a record at
;              most (the profile's max-groups-per-article).
;
;   THE OPEN's transient: the recovery decodes the retained records as octet
;   lists before it interns their payloads (host/native/io.lisp fnn-recover:
;   fn-store-sn-recover-records, then fn-intern-events, then the rows), so a
;   full replay -- every open whose checkpoint is absent or unreadable, and
;   today every open of the flipped image, whose checkpoints read back
;   `corrupt' (the record, section 4) -- holds *fn-heap-open-list-copies*
;   list copies of the history at 16 octets per octet, twice for the
;   collector, and *fn-heap-open-record-octets* of small objects a record.
;
;   THE REQUEST IN FLIGHT: the served POST's record and three copies of its
;   header as lists (as heap-figure counted them: 2 x 16 x (R + 3 HDR)); and
;   both octet buffers (the reader's and the publication's), byte vectors of
;   at most the checkpoint read bound F each: 2F (heap-figure's B).
;
;   THE IMAGE: the saved core's DYNAMIC content, which the collector never
;   copies (its pseudo-static generation).  The host observes the core
;   file's length and the dynamic space in use when the launcher's probe
;   starts (host/native/heap.lisp fnn-heap-image-observation): at least the
;   core's dynamic content and at most the file.  Before this lane the whole
;   file was counted in the heap (the production image: a 200 MB file of
;   which 109 MiB is dynamic content).
;
;   THE COLLECTOR's trigger: the host sets SBCL's bytes-consed-between-gcs to
;   `fn-heap-nursery-trigger' of the dynamic space it got (a sixteenth, at
;   least 8 MiB, at most the host's cap: host/native/io.lisp
;   fnn-gc-nursery-octets calls it), and a copying collection of the nursery
;   needs up to the nursery again in free space: 2 x trigger.  The figure is
;   the least dynamic space D (in the sense of `fn-heap-with-nursery') that
;   holds everything else and 2 x trigger(D) -- a fixed point, since the
;   trigger grows with D.
;
; KEYSTONE `fn-heap-store-figure-holds-every-store': in any dynamic space of
; at least the figure, every store the profile admits (USED <= H payload
; octets, N <= T records, each in at most G groups) fits with its open's
; transient, the request in flight, the buffers, the image and the
; collector's room at the trigger the host sets there.

(in-package "ACL2")
(include-book "owner-checkpoint-pipeline")

(defconst *fn-heap-list-octets-per-octet* 16)

; -----------------------------------------------------------------------------
; The image observation.  CORE is either the core file's length (the old
; observation: the whole file is counted as dynamic content) or
; (FILE . DYNAMIC), DYNAMIC the dynamic space in use at the probe's start.

(defun fn-heap-core-file (core)
  (declare (xargs :guard t))
  (if (consp core) (nfix (car core)) (nfix core)))

(defun fn-heap-core-dynamic (core)
  (declare (xargs :guard t))
  (if (consp core)
      (min (nfix (cdr core)) (fn-heap-core-file core))
    (nfix core)))

(defthm fn-heap-core-dynamic-is-at-most-the-file
  (<= (fn-heap-core-dynamic core) (fn-heap-core-file core))
  :rule-classes :linear)

(defthm fn-heap-core-dynamic-natp
  (natp (fn-heap-core-dynamic core))
  :rule-classes :type-prescription)

(defthm fn-heap-core-file-natp
  (natp (fn-heap-core-file core))
  :rule-classes :type-prescription)

; -----------------------------------------------------------------------------
; The collector's trigger in a dynamic space of D octets, NURSERY the host's
; cap (+fnn-gc-nursery-octets+, 64 MiB).  The host sets exactly this.

(defconst *fn-heap-nursery-least-octets* (* 8 1024 1024))

(defun fn-heap-nursery-trigger (d nursery)
  (declare (xargs :guard t))
  (max *fn-heap-nursery-least-octets*
       (min (nfix nursery) (floor (nfix d) 16))))

(defthm fn-heap-nursery-trigger-natp
  (natp (fn-heap-nursery-trigger d nursery))
  :rule-classes :type-prescription)

; The least D this figure takes for BASE octets of everything else: the
; smallest of three candidates that is valid in its range of the trigger.
(defun fn-heap-with-nursery (base nursery)
  (declare (xargs :guard t))
  (let* ((base (nfix base))
         (d1 (+ base (* 2 *fn-heap-nursery-least-octets*)))
         (d2 (ceiling (* 8 base) 7))
         (d3 (+ base (* 2 (max *fn-heap-nursery-least-octets* (nfix nursery))))))
    (max d1 (min d2 d3))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-heap-floor-16-bound
   (implies (natp d) (<= (* 16 (floor d 16)) d))
   :rule-classes :linear))

(local
 (defthm fn-heap-ceiling-7-bound
   (implies (natp x) (<= x (* 7 (ceiling x 7))))
   :rule-classes :linear))

; Every dynamic space of at least the figure holds BASE and the collector's
; room at the trigger the host sets in it.
(defthm fn-heap-with-nursery-holds-the-trigger
  (implies (and (natp d) (natp base)
                (<= (fn-heap-with-nursery base nursery) d))
           (<= (+ base (* 2 (fn-heap-nursery-trigger d nursery))) d))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable floor ceiling)
           :cases ((<= (floor d 16) (nfix nursery))))))

(defthm fn-heap-with-nursery-natp
  (natp (fn-heap-with-nursery base nursery))
  :rule-classes :type-prescription)

(defthm fn-heap-with-nursery-covers-base
  (<= (nfix base) (fn-heap-with-nursery base nursery))
  :rule-classes :linear)

(in-theory (disable fn-heap-with-nursery fn-heap-nursery-trigger))

; -----------------------------------------------------------------------------
; The measured terms (the record, sections 2 and 3).

(defconst *fn-heap-arena-octets-per-octet* 3)
(defconst *fn-heap-handle-octets* 48)
(defconst *fn-heap-record-octets* 5120)
(defconst *fn-heap-membership-octets* 320)
(defconst *fn-heap-open-list-copies* 2)
(defconst *fn-heap-open-record-octets* 16384)
(defconst *fn-heap-inflight-header-copies* 3)

; The state a store of USED payload octets and N records keeps.
(defun fn-heap-store-state-octets (profile used n)
  (declare (xargs :guard t))
  (+ (* *fn-heap-arena-octets-per-octet* (nfix used))
     (* *fn-heap-handle-octets* (nfix n))
     (* 2 (nfix n)
        (+ *fn-heap-record-octets*
           (* *fn-heap-membership-octets*
              (nfix (fn-bs-profile-max-groups-per-article profile)))))))

; The open's transient over that store.
(defun fn-heap-store-open-octets (used n)
  (declare (xargs :guard t))
  (+ (* 2 *fn-heap-list-octets-per-octet* *fn-heap-open-list-copies* (nfix used))
     (* 2 *fn-heap-open-record-octets* (nfix n))))

; The request in flight and the two octet buffers.
(defun fn-heap-store-inflight-octets (profile)
  (declare (xargs :guard t))
  (+ (* 2 *fn-heap-list-octets-per-octet*
        (+ (nfix (fn-bs-profile-max-record-octets profile))
           (* *fn-heap-inflight-header-copies*
              (nfix (fn-bs-profile-field 17 profile)))))
     (* 2 (fn-ock-capture-budget profile))))

; THE MODEL: what a process holding a store of USED octets and N records
; needs of its dynamic space at the collector's TRIGGER.
(defun fn-heap-store-need (profile core used n trigger)
  (declare (xargs :guard t))
  (+ (fn-heap-core-dynamic core)
     (fn-heap-store-state-octets profile used n)
     (fn-heap-store-open-octets used n)
     (fn-heap-store-inflight-octets profile)
     (* 2 (nfix trigger))))

; Everything but the collector's room, at the profile's bounds.
(defun fn-heap-store-base-octets (profile core)
  (declare (xargs :guard t))
  (+ (fn-heap-core-dynamic core)
     (fn-heap-store-state-octets profile (fn-bs-profile-max-history-octets profile)
                                 (fn-bs-profile-max-transactions profile))
     (fn-heap-store-open-octets (fn-bs-profile-max-history-octets profile)
                                (fn-bs-profile-max-transactions profile))
     (fn-heap-store-inflight-octets profile)))

; THE FIGURE, in octets.
(defun fn-heap-store-figure-octets (profile core nursery)
  (declare (xargs :guard t))
  (fn-heap-with-nursery (fn-heap-store-base-octets profile core) nursery))

(defthm fn-heap-store-base-octets-natp
  (natp (fn-heap-store-base-octets profile core))
  :rule-classes :type-prescription)

(defthm fn-heap-store-figure-octets-natp
  (natp (fn-heap-store-figure-octets profile core nursery))
  :rule-classes :type-prescription)

; The need grows with the store: at most the base and the room at the bounds.
(local
 (defthm fn-heap-store-need-within-the-base
   (implies (and (<= (nfix used) (nfix (fn-bs-profile-max-history-octets profile)))
                 (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile))))
            (<= (fn-heap-store-need profile core used n trigger)
                (+ (fn-heap-store-base-octets profile core) (* 2 (nfix trigger)))))
   :hints (("Goal" :in-theory (disable fn-ock-capture-budget
                                       fn-bs-profile-max-history-octets
                                       fn-bs-profile-max-transactions
                                       fn-bs-profile-max-groups-per-article
                                       fn-bs-profile-max-record-octets
                                       fn-bs-profile-field)
            :nonlinearp t))))

; KEYSTONE.  In a dynamic space of D octets, D at least the figure, every
; store the profile admits -- USED payload octets within H, N records within
; T -- fits with its open's transient, the request in flight, both buffers,
; the image's dynamic content and the collector's room at the trigger the
; host sets in D.
(defthm fn-heap-store-figure-holds-every-store
  (implies (and (natp d)
                (<= (fn-heap-store-figure-octets profile core nursery) d)
                (<= (nfix used) (nfix (fn-bs-profile-max-history-octets profile)))
                (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile))))
           (<= (fn-heap-store-need profile core used n
                                   (fn-heap-nursery-trigger d nursery))
               d))
  :hints (("Goal" :in-theory (union-theories
                               '(fn-heap-store-figure-octets fn-heap-store-base-octets-natp
                                 fn-heap-nursery-trigger-natp nfix natp)
                               (theory 'minimal-theory))
           :use ((:instance fn-heap-store-need-within-the-base
                            (trigger (fn-heap-nursery-trigger d nursery)))
                 (:instance fn-heap-with-nursery-holds-the-trigger
                            (base (fn-heap-store-base-octets profile core)))))))

(in-theory (disable fn-heap-store-need fn-heap-store-base-octets
                    fn-heap-store-figure-octets fn-heap-core-dynamic fn-heap-core-file))
