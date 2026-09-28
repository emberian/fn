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
;     arena    `fn-heap-arena-octets', a named parameter.  Today (dev: the
;              paged arena of arena-offheap stage 1, books/payload-arena-
;              paged.lisp) the payload octets in fixed pages of 256 KiB that
;              are never copied, the last page partly filled, and the page
;              table's pointers (a doubling of pointers, never of octets):
;              USED + one page + 32 octets a page.  Large objects: the
;              collector never copies them.  Lane arena-offheap-3 (payloads
;              read from the log files) replaces the term with its cache
;              bound; the keystones use only its monotonicity.
;     handles  the offset and size arrays, 8 bytes each per handle, doubling:
;              48 x N at the peak.
;     records  the rest of a record's retained state: small objects the
;              collector copies, so twice.  *fn-heap-record-octets* is the
;              measured live state a record, less its payload, on dev after
;              per-record-state (the log kernel holds only the COUNT, PRF-282)
;              and catalog-columns (the catalog on the served path): 8 to 10
;              KB a record posted or reopened (1,000 x 2 KiB, 10,000 x 400;
;              planning/evidence/catalog-columns-2026-09-27.md section 4,
;              per-record-state-2026-09-27.md section 4), plus about 1.3 KB
;              for a realistic 45-character Message-ID in the two tries
;              (per-record-state section 2): 12 KiB.  The 5 KiB it replaces
;              was measured before the catalog and the carried retention trie
;              and was BELOW the measurement.
;     memberships *fn-heap-membership-octets* a membership (a group a
;              record is filed in; measured 137 + 45 octets), twice for the
;              collector.  Since lane membership-budget (2026-09-27, ember's
;              decision) every membership is CHARGED to the history budget at
;              `*fn-sbud-membership-octets*' (books/store-budget.lisp; the
;              same 320), so a store the profile admits holds at most
;              H / 320 memberships (`fn-sbud-record-octets-pays-the-
;              memberships'): the term is at most 2 x 320 x floor(H / 320)
;              <= 2 H.  Before, nothing but G bounded them and the term was
;              2 x T x 320 x G: 41 TB on the scale gate (T 2^20, G 65,535;
;              planning/evidence/reservation-figure-2026-09-27.md section 1).
;              Lane history-columns lowers the record term (the history as
;              columns: 200 octets a record is its target) with its record.
;
;   THE OPEN's transient, since log-open-stream (PRF-283) and rm2-format9: the
;   open reads one log entry at a time and the full replay takes each record
;   straight into the replay's chunk, so no list of the history exists; what
;   is live beside the state is one entry's octet list and one chunk (closed
;   at *fn-heap-open-chunk-octets* = books/store-recover-stream.lisp's
;   *fn-srs-chunk-octets*, plus the record that fills it) as octet lists and
;   their decode (*fn-heap-open-list-copies* lists of at most chunk + R
;   octets at 16 octets per octet, twice for the collector); on the
;   checkpoint paths the scanned suffix's record vectors (at most the
;   input's octets, small objects: twice); and the replay's per-record spine
;   and index build beside the rows the state already counts,
;   *fn-heap-open-record-octets* a record.  Measured (log-open-stream's
;   record, section 3b: 10,000 x 32 KiB full replay, 1,029 MB peak over 640
;   MB live at the replay) the transient is the chunk's, not the history's.
;   Before, the open held *two* list copies of the whole history (64 octets
;   per history octet) and 16 KiB a record: the 64 H term was 48 GiB of the
;   scale preset's figure.
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
; octets, N <= T records, M memberships whose charge 320 M is within H)
; fits with its open's
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

(defthm fn-heap-with-nursery-is-at-most-an-eighth-more
  (<= (fn-heap-with-nursery base nursery)
      (max (+ (nfix base) (* 2 *fn-heap-nursery-least-octets*))
           (ceiling (* 8 (nfix base)) 7)))
  :rule-classes :linear)

(in-theory (disable fn-heap-with-nursery fn-heap-nursery-trigger))

; -----------------------------------------------------------------------------
; The measured terms (the record, sections 2 and 3).

(defconst *fn-heap-arena-page-octets* 262144)       ; *fn-arp-page*
(defconst *fn-heap-arena-page-pointer-octets* 32)
(defconst *fn-heap-handle-octets* 48)
(defconst *fn-heap-record-octets* 12288)
(defconst *fn-heap-membership-octets* 320)
(defconst *fn-heap-open-chunk-octets* 1048576)      ; *fn-srs-chunk-octets*
(defconst *fn-heap-open-list-copies* 2)
(defconst *fn-heap-open-record-octets* 1024)
(defconst *fn-heap-inflight-header-copies* 3)

; THE ARENA's cost, a named parameter: today's paged arena (arena-offheap
; stage 1): the payload octets, under one page of the last page's slack, and
; the page table's pointers for at most USED / page + 1 pages.  (Before it,
; the one byte array doubling: three octets per octet at a resize's peak.)
; Lane arena-offheap-3 (payloads read on demand from the log files) replaces
; this term with its cache bound; the keystones below hold for any
; definition of it that grows with USED (fn-heap-arena-octets-monotone is
; all they use of it).
(defun fn-heap-arena-octets (used)
  (declare (xargs :guard t))
  (+ (nfix used) *fn-heap-arena-page-octets*
     (* *fn-heap-arena-page-pointer-octets*
        (+ 1 (floor (nfix used) *fn-heap-arena-page-octets*)))))

(local
 (defthm fn-heap-floor-page-monotone
   (implies (and (natp a) (natp b) (<= a b))
            (<= (floor a 262144) (floor b 262144)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable floor)))))

(local
 (defthm fn-heap-arena-pointers-monotone
   (implies (<= (nfix a) (nfix b))
            (<= (* 32 (+ 1 (floor (nfix a) 262144)))
                (* 32 (+ 1 (floor (nfix b) 262144)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-heap-floor-page-monotone (a (nfix a)) (b (nfix b))))
            :in-theory (disable floor)))))

(defthm fn-heap-arena-octets-monotone
  (implies (<= (nfix u1) (nfix u2))
           (<= (fn-heap-arena-octets u1) (fn-heap-arena-octets u2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-arena-octets) (theory 'minimal-theory))
           :use ((:instance fn-heap-arena-pointers-monotone (a u1) (b u2))))))

(defthm fn-heap-arena-octets-natp
  (natp (fn-heap-arena-octets used))
  :rule-classes :type-prescription)

; The state a store of USED payload octets, N records and M memberships
; keeps.
(defun fn-heap-store-state-octets (profile used n m)
  (declare (xargs :guard t) (ignore profile))
  (+ (fn-heap-arena-octets used)
     (* *fn-heap-handle-octets* (nfix n))
     (* 2 (nfix n) *fn-heap-record-octets*)
     (* 2 *fn-heap-membership-octets* (nfix m))))

; The memberships a store of the profile holds at most: the history budget
; charges each `*fn-sbud-membership-octets*' and holds at most H.
(defun fn-heap-membership-bound (profile)
  (declare (xargs :guard t))
  (floor (nfix (fn-bs-profile-max-history-octets profile))
         *fn-sbud-membership-octets*))

(defthm fn-heap-membership-bound-natp
  (natp (fn-heap-membership-bound profile))
  :rule-classes :type-prescription)

(defthm fn-heap-nfix-of-membership-bound
  (equal (nfix (fn-heap-membership-bound profile))
         (fn-heap-membership-bound profile)))

; KEYSTONE (the membership term is a function of H).  A store's
; memberships, whose charge is within H, are at most the bound, and the
; bound's heap term is at most 2 H.
(defthm fn-heap-membership-bound-holds-the-charged-memberships
  (implies (<= (* *fn-sbud-membership-octets* (nfix m))
               (nfix (fn-bs-profile-max-history-octets profile)))
           (<= (nfix m) (fn-heap-membership-bound profile)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-profile-max-history-octets))))

(defthm fn-heap-membership-term-is-at-most-twice-h
  (<= (* 2 *fn-heap-membership-octets* (fn-heap-membership-bound profile))
      (* 2 (nfix (fn-bs-profile-max-history-octets profile))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-profile-max-history-octets))))

; The open's transient over an input of OU octets in ON records: one chunk
; and one entry as lists (at most the chunk and a record of R octets), the
; checkpoint suffix's vectors, and the per-record build.
(defun fn-heap-store-open-octets (profile ou on)
  (declare (xargs :guard t))
  (+ (* 2 *fn-heap-list-octets-per-octet* *fn-heap-open-list-copies*
        (+ *fn-heap-open-chunk-octets*
           (nfix (fn-bs-profile-max-record-octets profile))))
     (* 2 (nfix ou))
     (* 2 *fn-heap-open-record-octets* (nfix on))))

; The request in flight and the two octet buffers.
(defun fn-heap-store-inflight-octets (profile)
  (declare (xargs :guard t))
  (+ (* 2 *fn-heap-list-octets-per-octet*
        (+ (nfix (fn-bs-profile-max-record-octets profile))
           (* *fn-heap-inflight-header-copies*
              (nfix (fn-bs-profile-field 17 profile)))))
     (* 2 (fn-ock-capture-budget profile))))

; THE MODEL: what a process needs of its dynamic space at the collector's
; TRIGGER while it holds a store of USED octets in N records with M
; memberships, having opened
; (or opening) an input of OU octets in ON records.
(defun fn-heap-store-need (profile core used n m ou on trigger)
  (declare (xargs :guard t))
  (+ (fn-heap-core-dynamic core)
     (fn-heap-store-state-octets profile used n m)
     (fn-heap-store-open-octets profile ou on)
     (fn-heap-store-inflight-octets profile)
     (* 2 (nfix trigger))))

; -----------------------------------------------------------------------------
; THE OPEN'S INPUT.  A full replay reads the transaction files, at most H
; octets of them (books/store-profile-facts.lisp fn-profile-replay-within-
; boundp refuses more) and at most T records.  OBSERVED is what the launcher's
; probe saw on disk before the image started (host/native/heap.lisp
; fnn-heap-history-observation): NIL when unobserved, the octets of the
; store's history files, or (OCTETS . RECORDS) with RECORDS the transaction
; files' count; the open replays at most that (the files it reads are among
; them, one record a file).  A `run' grows the store past what it opened, so
; the STATE term stays at the profile's bounds; only the open's transient
; is the observed store's.

(defun fn-heap-observed-octets (observed)
  (declare (xargs :guard t))
  (if (consp observed) (car observed) observed))

(defun fn-heap-observed-records (observed)
  (declare (xargs :guard t))
  (and (consp observed) (cdr observed)))

(defun fn-heap-open-octets-bound (profile observed)
  (declare (xargs :guard t))
  (let ((h (nfix (fn-bs-profile-max-history-octets profile)))
        (o (fn-heap-observed-octets observed)))
    (if (natp o) (min o h) h)))

(defun fn-heap-open-records-bound (profile observed)
  (declare (xargs :guard t))
  (let ((tt (nfix (fn-bs-profile-max-transactions profile)))
        (c (fn-heap-observed-records observed)))
    (if (natp c) (min c tt) tt)))

(defthm fn-heap-open-bounds-of-nil
  (and (equal (fn-heap-open-octets-bound profile nil)
              (nfix (fn-bs-profile-max-history-octets profile)))
       (equal (fn-heap-open-records-bound profile nil)
              (nfix (fn-bs-profile-max-transactions profile)))))

; Everything but the collector's room: the state at the profile's bounds,
; the open's transient at the input's bound.
(defun fn-heap-store-base-octets (profile core observed)
  (declare (xargs :guard t))
  (+ (fn-heap-core-dynamic core)
     (fn-heap-store-state-octets profile (fn-bs-profile-max-history-octets profile)
                                 (fn-bs-profile-max-transactions profile)
                                 (fn-heap-membership-bound profile))
     (fn-heap-store-open-octets profile
                                (fn-heap-open-octets-bound profile observed)
                                (fn-heap-open-records-bound profile observed))
     (fn-heap-store-inflight-octets profile)))

(defthm fn-heap-store-base-octets-natp
  (natp (fn-heap-store-base-octets profile core observed))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-heap-nfix-of-store-base-octets
  (equal (nfix (fn-heap-store-base-octets profile core observed))
         (fn-heap-store-base-octets profile core observed))
  :hints (("Goal" :in-theory (union-theories '(nfix fn-heap-store-base-octets-natp)
                                             (theory 'minimal-theory)))))

(defthm fn-heap-nfix-of-nursery-trigger
  (equal (nfix (fn-heap-nursery-trigger d nursery))
         (fn-heap-nursery-trigger d nursery))
  :hints (("Goal" :in-theory (enable fn-heap-nursery-trigger))))

; THE FIGURE, in octets.
(defun fn-heap-store-figure-octets (profile core nursery observed)
  (declare (xargs :guard t))
  (fn-heap-with-nursery (fn-heap-store-base-octets profile core observed) nursery))

(defthm fn-heap-store-figure-octets-natp
  (natp (fn-heap-store-figure-octets profile core nursery observed))
  :rule-classes :type-prescription)

; The need grows with the store and the input: at most the base and the room.
(local
 (defthm fn-heap-store-state-octets-monotone
   (implies (and (<= (nfix used) (nfix h)) (<= (nfix n) (nfix tt))
                 (<= (nfix m) (nfix mm)))
            (<= (fn-heap-store-state-octets profile used n m)
                (fn-heap-store-state-octets profile h tt mm)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-heap-arena-octets)
            :use ((:instance fn-heap-arena-octets-monotone (u1 used) (u2 h)))
            :nonlinearp t))))

(local
 (defthm fn-heap-store-open-octets-monotone
   (implies (and (<= (nfix ou) (nfix h)) (<= (nfix on) (nfix tt)))
            (<= (fn-heap-store-open-octets profile ou on)
                (fn-heap-store-open-octets profile h tt)))
   :rule-classes nil))

(local
 (defthm fn-heap-open-bounds-natp
   (and (natp (fn-heap-open-octets-bound profile observed))
        (natp (fn-heap-open-records-bound profile observed)))
   :rule-classes ((:type-prescription :corollary
                                      (natp (fn-heap-open-octets-bound profile observed)))
                  (:type-prescription :corollary
                                      (natp (fn-heap-open-records-bound profile observed))))))

(local
 (defthm fn-heap-nfix-of-open-bounds
   (and (equal (nfix (fn-heap-open-octets-bound profile observed))
               (fn-heap-open-octets-bound profile observed))
        (equal (nfix (fn-heap-open-records-bound profile observed))
               (fn-heap-open-records-bound profile observed)))))

(local
 (defthm fn-heap-store-need-within-the-base
   (implies (and (<= (nfix used) (nfix (fn-bs-profile-max-history-octets profile)))
                 (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                 (<= (nfix m) (fn-heap-membership-bound profile))
                 (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                 (<= (nfix on) (fn-heap-open-records-bound profile observed)))
            (<= (fn-heap-store-need profile core used n m ou on trigger)
                (+ (fn-heap-store-base-octets profile core observed) (* 2 (nfix trigger)))))
   :hints (("Goal" :in-theory (e/d (fn-heap-store-need fn-heap-store-base-octets)
                                   (fn-heap-store-state-octets fn-heap-store-open-octets
                                    fn-heap-store-inflight-octets fn-heap-core-dynamic
                                    fn-heap-open-octets-bound fn-heap-open-records-bound
                                    fn-heap-membership-bound
                                    fn-bs-profile-max-history-octets
                                    fn-bs-profile-max-transactions nfix))
            :use ((:instance fn-heap-store-state-octets-monotone
                             (h (fn-bs-profile-max-history-octets profile))
                             (tt (fn-bs-profile-max-transactions profile))
                             (mm (fn-heap-membership-bound profile)))
                  (:instance fn-heap-store-open-octets-monotone
                             (h (fn-heap-open-octets-bound profile observed))
                             (tt (fn-heap-open-records-bound profile observed))))))))

; KEYSTONE.  In a dynamic space of D octets, D at least the figure, every
; store the profile admits -- USED payload octets within H, N records within
; T, M memberships whose charge (`*fn-sbud-membership-octets*' each) is
; within H -- fits, with the open's transient over any input within the observed
; bound (OU octets, ON records), the request in flight, both buffers, the
; image's dynamic content and the collector's room at the trigger the host
; sets in D.
(defthm fn-heap-store-figure-holds-every-store
  (implies (and (natp d)
                (<= (fn-heap-store-figure-octets profile core nursery observed) d)
                (<= (nfix used) (nfix (fn-bs-profile-max-history-octets profile)))
                (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                (<= (* *fn-sbud-membership-octets* (nfix m))
                    (nfix (fn-bs-profile-max-history-octets profile)))
                (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                (<= (nfix on) (fn-heap-open-records-bound profile observed)))
           (<= (fn-heap-store-need profile core used n m ou on
                                   (fn-heap-nursery-trigger d nursery))
               d))
  :hints (("Goal" :in-theory (union-theories
                               '(fn-heap-store-figure-octets fn-heap-store-base-octets-natp
                                 fn-heap-nfix-of-nursery-trigger)
                               (theory 'minimal-theory))
           :use (fn-heap-membership-bound-holds-the-charged-memberships
                 (:instance fn-heap-store-need-within-the-base
                            (trigger (fn-heap-nursery-trigger d nursery)))
                 (:instance fn-heap-with-nursery-holds-the-trigger
                            (base (fn-heap-store-base-octets profile core observed)))))))

; The observation only lowers the figure.
(defthm fn-heap-with-nursery-monotone
  (implies (<= (nfix b1) (nfix b2))
           (<= (fn-heap-with-nursery b1 nursery) (fn-heap-with-nursery b2 nursery)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-with-nursery))))

(local
 (defthm fn-heap-open-bounds-are-at-most-unobserved
   (and (<= (fn-heap-open-octets-bound profile observed)
            (fn-heap-open-octets-bound profile nil))
        (<= (fn-heap-open-records-bound profile observed)
            (fn-heap-open-records-bound profile nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-heap-open-octets-bound fn-heap-open-records-bound)
                                   (fn-bs-profile-max-history-octets
                                    fn-bs-profile-max-transactions))))))

(defthm fn-heap-store-base-observed-is-at-most-unobserved
  (<= (fn-heap-store-base-octets profile core observed)
      (fn-heap-store-base-octets profile core nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-store-base-octets)
                                  (fn-heap-store-state-octets fn-heap-store-open-octets
                                   fn-heap-store-inflight-octets fn-heap-core-dynamic
                                   fn-heap-open-octets-bound fn-heap-open-records-bound
                                   fn-heap-open-bounds-of-nil))
           :use (fn-heap-open-bounds-are-at-most-unobserved
                 (:instance fn-heap-store-open-octets-monotone
                            (ou (fn-heap-open-octets-bound profile observed))
                            (on (fn-heap-open-records-bound profile observed))
                            (h (fn-heap-open-octets-bound profile nil))
                            (tt (fn-heap-open-records-bound profile nil)))))))

(defthm fn-heap-store-figure-observed-is-at-most-unobserved
  (<= (fn-heap-store-figure-octets profile core nursery observed)
      (fn-heap-store-figure-octets profile core nursery nil))
  :rule-classes :linear
  :hints (("Goal" :in-theory (union-theories '(fn-heap-store-figure-octets
                                               fn-heap-store-base-octets-natp nfix)
                                             (theory 'minimal-theory))
           :use (fn-heap-store-base-observed-is-at-most-unobserved
                 (:instance fn-heap-with-nursery-monotone
                            (b1 (fn-heap-store-base-octets profile core observed))
                            (b2 (fn-heap-store-base-octets profile core nil)))))))

; The figure grows with the profile's bounds.  (A hypothesis on the
; max-groups-per-article field G was removed after proving the weakened
; theorem, lane membership-budget: the memberships are bounded by H, and the
; figure no longer reads G.)
(local
 (defthm fn-heap-membership-bound-monotone
   (implies (<= (nfix (fn-bs-profile-max-history-octets p1))
                (nfix (fn-bs-profile-max-history-octets p2)))
            (<= (fn-heap-membership-bound p1) (fn-heap-membership-bound p2)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-bs-profile-max-history-octets)))))

(defthm fn-heap-store-base-octets-grows-with-the-profile
  (implies (and (<= (nfix (fn-bs-profile-max-history-octets p1))
                    (nfix (fn-bs-profile-max-history-octets p2)))
                (<= (nfix (fn-bs-profile-max-transactions p1))
                    (nfix (fn-bs-profile-max-transactions p2)))
                (<= (nfix (fn-bs-profile-max-record-octets p1))
                    (nfix (fn-bs-profile-max-record-octets p2)))
                (<= (nfix (fn-bs-profile-field 17 p1))
                    (nfix (fn-bs-profile-field 17 p2)))
                (<= (fn-ock-capture-budget p1) (fn-ock-capture-budget p2)))
           (<= (fn-heap-store-base-octets p1 core nil)
               (fn-heap-store-base-octets p2 core nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-store-base-octets fn-heap-store-state-octets
                                   fn-heap-store-open-octets fn-heap-store-inflight-octets)
                                  (fn-ock-capture-budget fn-heap-open-bounds-of-nil
                                   fn-heap-arena-octets fn-heap-membership-bound
                                   fn-heap-open-octets-bound fn-heap-open-records-bound
                                   fn-bs-profile-max-history-octets
                                   fn-bs-profile-max-transactions
                                   fn-bs-profile-max-groups-per-article
                                   fn-bs-profile-max-record-octets
                                   fn-bs-profile-field))
           :use ((:instance fn-heap-open-bounds-of-nil (profile p1))
                 (:instance fn-heap-open-bounds-of-nil (profile p2))
                 (:instance fn-heap-membership-bound-monotone)
                 (:instance fn-heap-arena-octets-monotone
                            (u1 (fn-bs-profile-max-history-octets p1))
                            (u2 (fn-bs-profile-max-history-octets p2))))
           :nonlinearp t)))

(in-theory (disable fn-heap-store-need fn-heap-store-base-octets fn-heap-membership-bound
                    fn-heap-store-figure-octets fn-heap-core-dynamic fn-heap-core-file
                    fn-heap-open-octets-bound fn-heap-open-records-bound))
