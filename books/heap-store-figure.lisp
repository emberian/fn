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
;              collector copies, so twice.  Lane heap-bounds (row B2,
;              2026-09-28) derives it from the profile's limits, since the
;              measured constant it replaces (12 KiB a record) was BELOW
;              the need of records with long headers (f8-reservation's
;              finding F2: 250-octet Message-IDs and 900-octet Subjects
;              held about 27 KB a record while posting).  What a record
;              retains, structure by structure (the lane's record,
;              planning/evidence/heap-bounds-2026-09-28.md):
;              - a FIXED part that no header octet changes: the held row's
;                spine and facts, the catalog's and the history columns'
;                entries, the handle's extent and the retention carry
;                (measured: 3.4 KB a record reopened and 5.0 KB posting,
;                28-octet Message-IDs and short headers, header columns
;                included): *fn-heap-record-fixed-octets*;
;              - per HEADER octet, the column that holds it: the overview
;                fields as character strings (4 octets a character) or the
;                control words (Cancel-Lock, Cancel-Key) as octet lists (16
;                octets an octet), each twice while the owner posts (the
;                checkpoint base's canonical rows beside the live ones):
;                *fn-heap-record-header-octet-cost* (32) a header octet, the
;                control words' 2 x 16;
;              - per MESSAGE-ID octet, more: the two strings that name it in
;                the row and the overview (4 each, twice posting): 48 an
;                octet, *fn-heap-record-msgid-octet-cost* (16) over the
;                header octet's 32, for at most *fn-record-max-msgid* (RFC
;                5536 3.1.3's 250, which every admission checks:
;                fn-af-message-idp, fn-record-msgidp).  THE SWITCH (PRF-1037,
;                lane paged-history-6, row P2): the catalog's Message-ID
;                column is the keyed page table (books/msgid-pages-exec),
;                at most 8 u64 words a record whatever the Message-ID's
;                length -- *fn-heap-record-msgid-index-octets* (64) a
;                record, in the fixed part -- where the retired `equal'
;                hash table and the view trie it fed cost 32 an octet with
;                their rebuild at a checkpoint: 2 x 48 x 250 x 16,384
;                records = 375 MiB of the small profile's state, now
;                2 x 64 x 16,384 = 2.0 MiB (a model term, not a measured
;                peak).
;              Against f8-reservation's long-header curve (250-octet
;              Message-IDs, 900-octet Subjects): 222 Message-ID octets x 80
;              and 872 Subject octets x 8 is 24.7 KB a record over the short
;              headers' state, where 23.5 KB was measured posting.
;              Since lane heap-pool (B9) the history budget CHARGES the header:
;              a held row pays *fn-sbud-header-weight* (8) history octets a
;              header octet and *fn-sbud-msgid-weight* (12) more a
;              Message-ID octet (books/store-budget.lisp
;              fn-sbud-held-heap-charge), so a record's header state is 4
;              heap octets a charged octet (8 with the collector's copy).
;              USED here is the history the budget charges less the
;              memberships -- the payloads and the header charges -- so the
;              records' header term is at most 8 x USED
;              (*fn-heap-charge-heap-octets*), and the rest is
;              *fn-heap-record-octets* a record, the fixed part.  KEYSTONE
;              `fn-heap-records-retained-within-the-terms'.  (Lane
;              heap-bounds' term without the charge was 64 x min(USED,
;              N x HDR) and a Message-ID at its ceiling a record: 1,032 MiB
;              of the small preset's state where this is 209 MiB.)
;     memberships *fn-heap-membership-octets* a membership (a group a
;              record is filed in; measured 137 + 45 octets), twice for the
;              collector.  Since lane membership-budget (2026-09-27, ember's
;              decision) every membership is CHARGED to the history budget at
;              `*fn-sbud-membership-octets*' (books/store-budget.lisp; the
;              same 320), so a store the profile admits holds at most
;              H / 320 memberships (`fn-sbud-record-octets-pays-the-
;              memberships'): the term is at most 2 x 320 x floor(H / 320)
;              <= 2 H.  And since lane f8-reservation the payload and the
;              memberships are charged against their ONE budget (USED + 320
;              M <= H), so arena and memberships together are at most the
;              empty arena and 2 H (`fn-heap-store-history-octets'), not 3 H.
;              Before membership-budget, nothing but G bounded them and the term was
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

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

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
; cap (+fnn-gc-nursery-octets+, 8 MiB).  The host sets exactly this.

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

(defconst *fn-heap-arena-page-octets* 16384)        ; *adt-pg-octets*
; A pool page's overhead: its stobj header and array header (about 40 octets)
; and its slot in a table page (8, with the table page's own 1/64 share),
; rounded up.
(defconst *fn-heap-arena-page-pointer-octets* 64)
(defconst *fn-heap-handle-octets* 48)
; A record's retained state (the header's comment, `records'): the fixed
; part, a header octet's columns, and a Message-ID octet's trie and names.
(defconst *fn-heap-record-fixed-octets* 4096)
(defconst *fn-heap-record-header-octet-cost* 32)
(defconst *fn-heap-record-msgid-octet-cost* 16)
; THE SWITCH (PRF-1037): the keyed Message-ID page table's words a record,
; at most 8 (books/msgid-pages-exec.lisp; 32 octets at a load of 1/4),
; whatever the Message-ID's length.
(defconst *fn-heap-record-msgid-index-octets* 64)
; The part of a record's state no header octet moves (lane heap-pool: the
; Message-ID's octets are charged with the header now; its index entry is
; here).
(defconst *fn-heap-record-octets*
  (+ *fn-heap-record-fixed-octets* *fn-heap-record-msgid-index-octets*))
; The heap a charged history octet of header costs, the collector's copy
; included: 2 x 32 / 8 for a header octet, 2 x (32 + 16) / (8 + 12) for a
; Message-ID octet; the header octet's 8 bounds both
; (fn-heap-record-charge-covers-the-state).
(defconst *fn-heap-charge-heap-octets* 8)
(defconst *fn-heap-membership-octets* 320)
(defconst *fn-heap-open-chunk-octets* 1048576)      ; *fn-srs-chunk-octets*
(defconst *fn-heap-open-list-copies* 2)
(defconst *fn-heap-open-record-octets* 1024)
(defconst *fn-heap-inflight-header-copies* 3)
(defconst *fn-heap-message-id-octets* 250)       ; RFC 5536 section 3.1.3

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
            (<= (floor a 16384) (floor b 16384)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable floor)))))

(local
 (defthm fn-heap-arena-pointers-monotone
   (implies (<= (nfix a) (nfix b))
            (<= (* 64 (+ 1 (floor (nfix a) 16384)))
                (* 64 (+ 1 (floor (nfix b) 16384)))))
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

; THE ARENA's slope: an octet more of payload costs at most two octets of
; the term, plus one page pointer at a page boundary.  (Today's paged arena:
; one octet and 64 per page.  A cache bound that does not grow with USED,
; arena-offheap-3's, has slope 0.)  With monotonicity it is all the history
; bound below uses of the arena.
(local
 (defthm fn-heap-floor-page-bounds
   (implies (natp a)
            (and (<= (* 16384 (floor a 16384)) a)
                 (< a (* 16384 (+ 1 (floor a 16384))))))
   :rule-classes nil))

(local
 (defthm fn-heap-floor-page-of-sum
   (implies (and (natp u) (natp x))
            (<= (floor (+ u x) 16384) (+ (floor u 16384) (floor x 16384) 1)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable floor)
            :use ((:instance fn-heap-floor-page-bounds (a u))
                  (:instance fn-heap-floor-page-bounds (a x))
                  (:instance fn-heap-floor-page-bounds (a (+ u x))))))))

(defthm fn-heap-arena-octets-slope
  (implies (and (natp u) (natp x))
           (<= (fn-heap-arena-octets (+ u x))
               (+ (fn-heap-arena-octets u) (* 2 x) *fn-heap-arena-page-pointer-octets*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable floor)
           :use ((:instance fn-heap-floor-page-of-sum)
                 (:instance fn-heap-floor-page-bounds (a x))))))

; ONE RECORD's retained state: MID octets of Message-ID among HDR header
; octets (the Message-ID's octets are header octets too, so a Message-ID
; octet costs the header octet's and its two strings'), and the keyed
; index's words a record (THE SWITCH: *fn-heap-record-msgid-index-octets*,
; a constant of the record, not of the Message-ID's length).
(defun fn-heap-record-retained-octets (mid hdr)
  (declare (xargs :guard t))
  (+ *fn-heap-record-fixed-octets*
     *fn-heap-record-msgid-index-octets*
     (* *fn-heap-record-header-octet-cost* (nfix hdr))
     (* *fn-heap-record-msgid-octet-cost* (nfix mid))))

;; A record's HEADER CHARGE, the history budget's (books/store-budget.lisp
;; fn-sbud-held-heap-charge over a held row's header and Message-ID
;; octets).
(defun fn-heap-record-charge (mid hdr)
  (declare (xargs :guard t))
  (+ (* *fn-sbud-header-weight* (nfix hdr))
     (* *fn-sbud-msgid-weight* (nfix mid))))

; The charge is the one the history budget computes of a held row (its
; header's octets, at most its octets, and its Message-ID's): the store's
; committed charge is the model's USED and memberships
; (books/store-budget.lisp fn-sbud-row-octets).
(defthm fn-heap-record-charge-is-the-budgets-charge
  (equal (fn-sbud-held-heap-charge row)
         (fn-heap-record-charge (fn-sbud-held-msgid-octets row)
                                (fn-sbud-held-header-octets row)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sbud-held-heap-charge)
                                  (fn-sbud-held-msgid-octets fn-sbud-held-header-octets)))))

; A record's header state, twice for the collector, is its charge's heap.
(defthm fn-heap-record-charge-covers-the-state
  (<= (* 2 (fn-heap-record-retained-octets mid hdr))
      (+ (* 2 *fn-heap-record-octets*)
         (* *fn-heap-charge-heap-octets* (fn-heap-record-charge mid hdr))))
  :rule-classes nil)

; The records a store holds, each (MID HDR PAYLOAD): its Message-ID's
; octets, its header's and its payload's, naturals.  (Lane heap-bounds also
; asked the header to be within the payload and the profile's header bound;
; the charge counts the header whatever its size, and the weakened keystone
; was proved first.)
(defun fn-heap-record-admissiblep (rec)
  (declare (xargs :guard t))
  (and (true-listp rec) (equal (len rec) 3)
       (natp (first rec)) (natp (second rec)) (natp (third rec))))

(defun fn-heap-records-admissiblep (recs)
  (declare (xargs :guard t))
  (if (consp recs)
      (and (fn-heap-record-admissiblep (car recs))
           (fn-heap-records-admissiblep (cdr recs)))
    t))

(defun fn-heap-records-retained-octets (recs)
  (declare (xargs :guard t))
  (if (consp recs)
      (+ (let ((rec (car recs)))
           (if (consp rec)
               (fn-heap-record-retained-octets (car rec) (and (consp (cdr rec)) (cadr rec)))
             *fn-heap-record-fixed-octets*))
         (fn-heap-records-retained-octets (cdr recs)))
    0))

; USED of the records: their payloads and their header charges, the history
; the budget charges them less their memberships.
(defun fn-heap-records-charged-octets (recs)
  (declare (xargs :guard t))
  (if (consp recs)
      (+ (let ((rec (car recs)))
           (if (and (consp rec) (consp (cdr rec)) (consp (cddr rec)))
               (+ (nfix (caddr rec)) (fn-heap-record-charge (car rec) (cadr rec)))
             0))
         (fn-heap-records-charged-octets (cdr recs)))
    0))

; KEYSTONE (the record terms bound every record's state).  The state
; retained by records (MID HDR PAYLOAD), twice for the
; collector, is within the figure's two record terms at N = their count and
; USED = their charged octets: *fn-heap-record-octets* a record and
; *fn-heap-charge-heap-octets* a charged octet.
(defthm fn-heap-records-retained-within-the-terms
  (implies (fn-heap-records-admissiblep recs)
           (<= (* 2 (fn-heap-records-retained-octets recs))
               (+ (* 2 (len recs) *fn-heap-record-octets*)
                  (* *fn-heap-charge-heap-octets*
                     (fn-heap-records-charged-octets recs)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-heap-records-admissiblep recs)
           :in-theory (enable fn-heap-record-retained-octets fn-heap-record-charge))))

; The state a store of USED charged octets (payloads and header charges),
; N records and M memberships keeps: the arena, the handles, the records'
; fixed term and header term (with the collector's copy) and the
; memberships.
(defun fn-heap-store-state-octets (profile used n m)
  (declare (xargs :guard t) (ignore profile))
  (+ (fn-heap-arena-octets used)
     (* *fn-heap-handle-octets* (nfix n))
     (* 2 (nfix n) *fn-heap-record-octets*)
     (* *fn-heap-charge-heap-octets* (nfix used))
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

; THE HISTORY'S STATE (lane f8-reservation, 2026-09-28).  The payload the
; arena holds and the memberships are paid from ONE budget: a held row's
; stored octets are its payload octets plus `*fn-sbud-membership-octets*'
; a membership (books/store-budget.lisp fn-sbud-row-octets), and the store
; commits at most H of them.  Until this lane the figure charged each at
; its own worst case -- the arena at H payload octets AND the memberships
; at H / 320 -- so every store cost H more than any store the budget
; admits (for the default preset's 1 TiB of history, 1 TiB of the 11.5 TB
; that `init --max-transactions 20000' asked).  Jointly, the payload's
; octets cost at most two each in the arena (fn-heap-arena-octets-slope,
; one page pointer more) and a membership's charge its heap octets twice
; (the collector's copy), so the pair costs at most the empty arena, 2 H
; and a pointer.
(defun fn-heap-store-history-octets (profile)
  (declare (xargs :guard t))
  (+ (fn-heap-arena-octets 0)
     (* 2 (nfix (fn-bs-profile-max-history-octets profile)))
     *fn-heap-arena-page-pointer-octets*))

; A membership's heap octets are within its charge (both 320 today; a
; measurement that raised the heap figure past the charge breaks this).
(defthm fn-heap-membership-octets-within-the-charge
  (<= *fn-heap-membership-octets* *fn-sbud-membership-octets*)
  :rule-classes nil)

; KEYSTONE.  The payload octets and the memberships of a store whose
; charges are within H -- USED payload octets and M memberships, USED +
; 320 M <= H, as the history budget commits them -- cost at most the
; history bound in the arena and the memberships' rows.
(defthm fn-heap-store-history-holds-payload-and-memberships
  (implies (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
               (nfix (fn-bs-profile-max-history-octets profile)))
           (<= (+ (fn-heap-arena-octets used)
                  (* 2 *fn-heap-membership-octets* (nfix m)))
               (fn-heap-store-history-octets profile)))
  :rule-classes nil
  :hints (("Goal" :cases ((natp used))
           :in-theory (e/d (fn-heap-store-history-octets)
                           (fn-heap-arena-octets fn-bs-profile-max-history-octets))
           :use (fn-heap-membership-octets-within-the-charge
                 (:instance fn-heap-arena-octets-slope (u 0) (x (nfix used)))))
          ("Subgoal 2" :in-theory (e/d (fn-heap-store-history-octets fn-heap-arena-octets)
                                       (fn-bs-profile-max-history-octets)))))

(defthm fn-heap-store-history-octets-natp
  (natp (fn-heap-store-history-octets profile))
  :rule-classes :type-prescription)

; The state at the profile's bounds: the history's, and T records' handles
; and rows.
(defun fn-heap-store-state-bound (profile)
  (declare (xargs :guard t))
  (+ (fn-heap-store-history-octets profile)
     (* *fn-heap-handle-octets* (nfix (fn-bs-profile-max-transactions profile)))
     (* 2 (nfix (fn-bs-profile-max-transactions profile)) *fn-heap-record-octets*)
     (* *fn-heap-charge-heap-octets* (nfix (fn-bs-profile-max-history-octets profile)))))

; The octets one open chunk holds over an input of OU octets: a chunk closes
; once it holds the quantum (`fn-srs-chunk-fullp'), so it is at most the
; quantum and the record that filled it (R); and every octet of it is an
; octet of the input, so it is at most OU.  (Lane heap-bounds, row B4: the
; term was the quantum and R whatever the input, 76 MiB of the small
; preset's figure for an empty store.)
(defun fn-heap-open-chunk-bound (profile ou)
  (declare (xargs :guard t))
  (min (nfix ou)
       (+ *fn-heap-open-chunk-octets*
          (nfix (fn-bs-profile-max-record-octets profile)))))

(defthm fn-heap-open-chunk-bound-monotone
  (implies (and (<= (nfix ou1) (nfix ou2))
                (<= (nfix (fn-bs-profile-max-record-octets p1))
                    (nfix (fn-bs-profile-max-record-octets p2))))
           (<= (fn-heap-open-chunk-bound p1 ou1) (fn-heap-open-chunk-bound p2 ou2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-profile-max-record-octets))))

; The open's transient over an input of OU octets in ON records: one chunk
; and one entry as lists (each at most `fn-heap-open-chunk-bound'), the
; checkpoint suffix's vectors, and the per-record build.
(defun fn-heap-store-open-octets (profile ou on)
  (declare (xargs :guard t))
  (+ (* 2 *fn-heap-list-octets-per-octet* *fn-heap-open-list-copies*
        (fn-heap-open-chunk-bound profile ou))
     (* 2 (nfix ou))
     (* 2 *fn-heap-open-record-octets* (nfix on))))

; The request in flight and the two octet buffers.
; And (lane chunked-body-2, B6b) the submission the committer took: the take
; unpacks it (fn-own-take-submission), its octets, groups and Message-ID as
; lists until the outcome, one at a time.
(defun fn-heap-store-inflight-octets (profile)
  (declare (xargs :guard t))
  (+ (* 2 *fn-heap-list-octets-per-octet*
        (+ (nfix (fn-bs-profile-max-record-octets profile))
           (* *fn-heap-inflight-header-copies*
              (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile)))))
     (* 2 *fn-heap-list-octets-per-octet*
        (+ (nfix (fn-bs-profile-max-article-octets profile))
           (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile))
           *fn-heap-message-id-octets*))
     (* 2 (fn-ock-capture-budget profile))))

; THE ARTICLES IN FLIGHT (lane zero-copy-commit, 2026-09-28).  A connection
; in the middle of an article (after POST's 340, IHAVE's 335 or a TAKETHIS
; line) retains the body until its terminator, and a connection whose article
; has arrived holds its submission (the decision's octets) in the owner's
; queue or in the batch in flight until the commit answers it.  These are the
; per-connection terms that grow with the profile's largest article A and
; record R, and until this lane the dynamic space held none of them
; (books/connection-budget.lisp charged the body to the machine only, so
; enough concurrent posters of large articles exhausted the heap: a fault,
; exit 4).  The figure now holds `fn-heap-article-slots' articles in flight,
; each at `fn-heap-article-reserve-octets'; the owner admits a connection to
; article mode only while fewer than that many are held
; (books/owner-article-slots.lisp fn-oas-read-span) and refuses the rest by
; name (POST 440; IHAVE and TAKETHIS 400 and close).  The slots: as many as
; *fn-heap-article-slot-budget* holds at the reserve, at least one (a node
; always takes a POST) and at most *fn-heap-article-slots-most* (32, the
; default configuration's connections).
(defconst *fn-heap-article-slot-budget* (* 64 1048576))
(defconst *fn-heap-article-slots-most* 32)
(defconst *fn-heap-article-line-octets* 512)

;; What one slot retains, the larger of its two forms (lane chunked-body-2,
;; B6b; each an octet of heap about an octet, where the octet lists they
;; replaced cost sixteen):
;;   THE WIRE'S: the body mid-article, the wire's store of 512-octet packed
;;   blocks (books/body-chunks.lisp), at most the body limit A and one octet
;;   (books/wire.lisp fn-wire-line-room; KEYSTONE
;;   fn-wire-statep-article-holds-at-most-the-body-limit).  A block is a
;;   66-word bignum and a cons: *fn-heap-packed-block-octets*; the store's
;;   own cells *fn-heap-packed-store-octets*.
;;   THE QUEUE'S: the submission as fn-own-enqueue holds it
;;   (books/packed-submission.lisp fn-psub-sub-heap): the article's octets one
;;   natural (at most A, and a cons), the groups comma-joined into another (at
;;   most the header bound HDR), the Message-ID an octet list of at most 250
;;   (RFC 5536 section 3.1.3), the records' cells.
;; Twice, for the collector's copy.  The article's LIST forms -- its lines at
;; the terminator, the injection, and the submission the committer took and
;; unpacked (one at a time: fn-own-take-submission requires none in flight)
;; -- are the request in flight (fn-heap-store-inflight-octets), never a
;; slot's.
(defconst *fn-heap-packed-block-octets* 544)
(defconst *fn-heap-packed-store-octets* 64)
(defconst *fn-heap-packed-natural-octets* 48)
(defconst *fn-heap-packed-groups-octets* 64)
(defconst *fn-heap-submission-record-octets* 512)

(defun fn-heap-article-wire-octets (profile)
  (declare (xargs :guard t))
  (+ (* *fn-heap-packed-block-octets*
        (floor (+ (nfix (fn-bs-profile-max-article-octets profile)) *fn-heap-article-line-octets*)
               *fn-heap-article-line-octets*))
     *fn-heap-packed-store-octets*))

(defun fn-heap-article-queued-octets (profile)
  (declare (xargs :guard t))
  (+ *fn-heap-submission-record-octets*
     *fn-heap-packed-natural-octets*
     (nfix (fn-bs-profile-max-article-octets profile))
     *fn-heap-packed-groups-octets*
     (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile))
     (* *fn-heap-list-octets-per-octet* *fn-heap-message-id-octets*)))

(defun fn-heap-article-reserve-octets (profile)
  (declare (xargs :guard t))
  (* 2 (max (fn-heap-article-wire-octets profile)
            (fn-heap-article-queued-octets profile))))

; The octets the figure holds for articles in flight: the budget, but at
; least one reserve and at most one per slot of the default capacity.
; Monotone in A (the figure grows with the profile).
(defun fn-heap-articles-octets (profile)
  (declare (xargs :guard t))
  (let ((r (fn-heap-article-reserve-octets profile)))
    (max r (min (* *fn-heap-article-slots-most* r) *fn-heap-article-slot-budget*))))

; The slots: how many reserves that holds.
(defun fn-heap-article-slots (profile)
  (declare (xargs :guard t))
  (floor (fn-heap-articles-octets profile) (fn-heap-article-reserve-octets profile)))


(defthm fn-heap-article-reserve-octets-posp
  (posp (fn-heap-article-reserve-octets profile))
  :rule-classes :type-prescription)

(local
 (defthm fn-heap-articles-octets-between
   (and (<= (fn-heap-article-reserve-octets profile) (fn-heap-articles-octets profile))
        (<= (fn-heap-articles-octets profile)
            (* *fn-heap-article-slots-most* (fn-heap-article-reserve-octets profile))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable fn-heap-article-reserve-octets)))))

(local
 (defthm fn-heap-floor-between
   (implies (and (posp r) (natp x) (<= r x) (<= x (* 32 r)))
            (and (<= 1 (floor x r)) (<= (floor x r) 32)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(defthm fn-heap-article-slots-bounds
  (and (posp (fn-heap-article-slots profile))
       (<= (fn-heap-article-slots profile) *fn-heap-article-slots-most*))
  :rule-classes ((:type-prescription :corollary (posp (fn-heap-article-slots profile)))
                 (:linear :corollary (<= (fn-heap-article-slots profile)
                                         *fn-heap-article-slots-most*)))
  :hints (("Goal" :in-theory (disable fn-heap-article-reserve-octets fn-heap-articles-octets
                                      fn-heap-articles-octets-between)
           :use (fn-heap-articles-octets-between
                 (:instance fn-heap-floor-between
                            (r (fn-heap-article-reserve-octets profile))
                            (x (fn-heap-articles-octets profile)))))))

; KEYSTONE (the slots are held): every count of articles in flight up to the
; slots, each within the reserve, is within the figure's articles term.
(defthm fn-heap-article-slots-are-held
  (implies (<= (nfix k) (fn-heap-article-slots profile))
           (<= (* (nfix k) (fn-heap-article-reserve-octets profile))
               (fn-heap-articles-octets profile)))
  :hints (("Goal" :in-theory (disable fn-heap-article-reserve-octets fn-heap-articles-octets)
           :nonlinearp t)))

(local
 (defthm fn-heap-floor-512-monotone
   (implies (and (natp a) (natp b) (<= a b))
            (<= (floor a 512) (floor b 512)))
   :rule-classes nil))

(local
 (defthm fn-heap-article-wire-octets-monotone
   (implies (<= (nfix (fn-bs-profile-max-article-octets p1))
                (nfix (fn-bs-profile-max-article-octets p2)))
            (<= (fn-heap-article-wire-octets p1) (fn-heap-article-wire-octets p2)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-heap-article-wire-octets)
                                   (fn-bs-profile-max-article-octets))
                   :use ((:instance fn-heap-floor-512-monotone
                                    (a (nfix (fn-bs-profile-max-article-octets p1)))
                                    (b (nfix (fn-bs-profile-max-article-octets p2)))))))))

(local
 (defthm fn-heap-article-reserve-octets-monotone
   (implies (and (<= (nfix (fn-bs-profile-max-article-octets p1))
                     (nfix (fn-bs-profile-max-article-octets p2)))
                 (<= (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* p1))
                     (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* p2))))
            (<= (fn-heap-article-reserve-octets p1) (fn-heap-article-reserve-octets p2)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-heap-article-reserve-octets fn-heap-article-queued-octets)
                                   (fn-heap-article-wire-octets
                                    fn-bs-profile-max-article-octets fn-bs-profile-field))
                   :use (fn-heap-article-wire-octets-monotone)))))

(local
 (defthm fn-heap-articles-of-reserve-monotone
   (implies (and (natp r1) (natp r2) (<= r1 r2))
            (<= (max r1 (min (* 32 r1) b)) (max r2 (min (* 32 r2) b))))
   :rule-classes nil))

(defthm fn-heap-articles-octets-monotone
  (implies (and (<= (nfix (fn-bs-profile-max-article-octets p1))
                    (nfix (fn-bs-profile-max-article-octets p2)))
                (<= (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* p1))
                    (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* p2))))
           (<= (fn-heap-articles-octets p1) (fn-heap-articles-octets p2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-articles-octets posp natp
                                                fn-heap-article-reserve-octets-posp)
                                              (theory 'minimal-theory))
                  :use (fn-heap-article-reserve-octets-monotone
                        (:instance fn-heap-article-reserve-octets-posp (profile p1))
                        (:instance fn-heap-article-reserve-octets-posp (profile p2))
                        (:instance fn-heap-articles-of-reserve-monotone
                                   (r1 (fn-heap-article-reserve-octets p1))
                                   (r2 (fn-heap-article-reserve-octets p2))
                                   (b *fn-heap-article-slot-budget*))))))

(in-theory (disable fn-heap-article-slots fn-heap-articles-octets
                    fn-heap-article-reserve-octets))

; THE MODEL: what a process needs of its dynamic space at the collector's
; TRIGGER while it holds a store of USED octets in N records with M
; memberships, having opened
; (or opening) an input of OU octets in ON records, with every article
; slot in use.
(defun fn-heap-store-need (profile core used n m ou on trigger)
  (declare (xargs :guard t))
  (+ (fn-heap-core-dynamic core)
     (fn-heap-store-state-octets profile used n m)
     (fn-heap-store-open-octets profile ou on)
     (fn-heap-store-inflight-octets profile)
     (fn-heap-articles-octets profile)
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

; -----------------------------------------------------------------------------
; THE LIVE RECLAIM's SECOND GENERATION (lane reclaim-funding, 2026-10-04;
; planning/design/reclaim-funding-2026-10-04.md; S152).  A live `store
; reclaim' (host/native/owner.lisp fnn-owner-reclaim-pass) walks the pinned
; history in chunks (books/reclaim-chunked-walk.lisp) and builds, beside the
; served state, a whole second one: the rewritten rows decoded from the
; history pages, the rebuilt Store from them (the full open over them:
; books/owner-reclaim-pass.lisp fn-orcp-rebuild-is-the-full-open), a fresh
; catalog and history columns.  Only the payload arena is shared.  So its
; demand over a store of N records whose history budget charges C octets
; (books/store-budget.lisp fn-sbud-record-octets: the payloads, the header
; charges and 320 a membership) is, in this figure's own terms:
;   the state less the arena: 48 N of handles, 2 x 4,160 N of records and 8
;     heap octets a charged octet (the header term, 8 USED + 640 M <= 8 C);
;   the open's per-record build, 2 x 1,024 N, which the rebuild makes and
;     which covers the reclaim context the pass frees before it;
;   one walk chunk of decoded rows beside them, at the same per-record
;     terms: *fn-heap-reclaim-chunk-rows* (the host's walk quantum,
;     fnn-owner-reclaim-walk, reads it from here);
;   the reclaimed rows' tombstones (books/reclaim-tombstone.lisp: 145 octets
;     and the Path agent), held as octet lists from the rewrite until the
;     swap quantum seals them (books/owner-reclaim-seal.lisp fn-orcs-payloads,
;     the checkpoint walk's sources): sixteen octets a list octet, twice for
;     the collector -- 4,640 a record, and 32 a Path-agent octet, which is a
;     header octet the history budget charges at least 8
;     (fn-sbud-held-heap-charge), so at most 4 a charged octet.  (D27: a byte
;     vector would cost one octet an octet; the term falls with that change.)
; The pass's checkpoint capture and history image are the publication's
; (the pass is the publication in flight), not this term's.
(defconst *fn-heap-reclaim-chunk-rows* 1024)

; The walk's quantum as the host reads it (host/native/owner.lisp
; fnn-owner-reclaim-walk): the chunk this term holds is the chunk it walks.
(defun fn-heap-reclaim-chunk-rows ()
  (declare (xargs :guard t))
  *fn-heap-reclaim-chunk-rows*)

(defconst *fn-heap-reclaim-record-octets*
  (+ *fn-heap-handle-octets* (* 2 *fn-heap-record-octets*) (* 2 *fn-heap-open-record-octets*)))

(defconst *fn-heap-reclaim-tombstone-octets*
  (* 2 *fn-heap-list-octets-per-octet* *fn-rcl-tombstone-fixed*))
(defconst *fn-heap-reclaim-agent-octets-per-charge* 4)

(defun fn-heap-reclaim-demand-octets (n c)
  (declare (xargs :guard t))
  (+ (* *fn-heap-reclaim-record-octets*
        (+ (nfix n) (min (nfix n) *fn-heap-reclaim-chunk-rows*)))
     (* *fn-heap-reclaim-tombstone-octets* (nfix n))
     (* (+ *fn-heap-charge-heap-octets* *fn-heap-reclaim-agent-octets-per-charge*) (nfix c))))

(defthm fn-heap-reclaim-demand-octets-natp
  (natp (fn-heap-reclaim-demand-octets n c))
  :rule-classes :type-prescription)

; The demand grows with the store.
(defthm fn-heap-reclaim-demand-octets-monotone
  (implies (and (<= (nfix n1) (nfix n2)) (<= (nfix c1) (nfix c2)))
           (<= (fn-heap-reclaim-demand-octets n1 c1) (fn-heap-reclaim-demand-octets n2 c2)))
  :rule-classes nil)

; The demand at the profile's bounds: T records charging H.
(defun fn-heap-reclaim-octets (profile)
  (declare (xargs :guard t))
  (fn-heap-reclaim-demand-octets (fn-bs-profile-max-transactions profile)
                                 (fn-bs-profile-max-history-octets profile)))

; THE OWNER's WORK RESERVE.  The open's transient and a live pass never
; coexist in a run (the open precedes the run's ledger; a recovery event
; stops the service and the open runs in the next process), so one reserve
; holds whichever is larger: the open's terms and the excess of the pass's
; demand at the bounds over them.
(defun fn-heap-reclaim-excess-octets (profile ou on)
  (declare (xargs :guard t))
  (nfix (- (fn-heap-reclaim-octets profile) (fn-heap-store-open-octets profile ou on))))

(defthm fn-heap-reclaim-excess-octets-natp
  (natp (fn-heap-reclaim-excess-octets profile ou on))
  :rule-classes :type-prescription)

(defthm fn-heap-open-and-excess-hold-the-reclaim
  (<= (fn-heap-reclaim-octets profile)
      (+ (fn-heap-store-open-octets profile ou on) (fn-heap-reclaim-excess-octets profile ou on)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-heap-store-open-octets fn-heap-reclaim-octets))))

(defthm fn-heap-open-and-excess-is-the-larger
  (equal (+ (fn-heap-store-open-octets profile ou on) (fn-heap-reclaim-excess-octets profile ou on))
         (max (fn-heap-store-open-octets profile ou on) (fn-heap-reclaim-octets profile)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-heap-store-open-octets fn-heap-reclaim-octets))))

(defthm fn-heap-reclaim-octets-grows-with-the-profile
  (implies (and (<= (nfix (fn-bs-profile-max-transactions p1))
                    (nfix (fn-bs-profile-max-transactions p2)))
                (<= (nfix (fn-bs-profile-max-history-octets p1))
                    (nfix (fn-bs-profile-max-history-octets p2))))
           (<= (fn-heap-reclaim-octets p1) (fn-heap-reclaim-octets p2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-heap-reclaim-demand-octets
                                      fn-bs-profile-max-transactions
                                      fn-bs-profile-max-history-octets)
           :use ((:instance fn-heap-reclaim-demand-octets-monotone
                            (n1 (fn-bs-profile-max-transactions p1))
                            (n2 (fn-bs-profile-max-transactions p2))
                            (c1 (fn-bs-profile-max-history-octets p1))
                            (c2 (fn-bs-profile-max-history-octets p2)))))))

(in-theory (disable fn-heap-reclaim-demand-octets fn-heap-reclaim-octets
                    fn-heap-reclaim-excess-octets))

;; THE HISTORY ROOTS (lane mem10-hroot, 2026-10-07; MEM-010, MEM-011;
;; planning/design/history-root-reserve-2026-10-07.md).  The live P3 history
;; root holds the whole history as a page image, and two generations coexist
;; across a publication (the retained one and the candidate being built).
;; The figure holds them as their own term, outside the articles' pool
;; (books/memory-credits.lisp fn-mcr-hroot-resize draws it, never the pool).
;;
;; A root at the profile's bounds: at most T rows and H event octets.  The
;; image is four word columns of one word a row (each starts at a page) and
;; one octet column of 16384 octets a page, so at most
;; 1 + 4 ceil(T/2048) + ceil(H/16384) pages; a page store of NP pages holds
;; 2048 NP words (data), 2048 NT (table, NT = pgs-ntables NP), 2 NP flags,
;; NT table flags and a directory of a few pages; the suffix array holds at
;; most T cells, 8 octets each, and the header 4096.
(defun fn-heap-hroot-ntables (np)
  (declare (xargs :guard (natp np)))
  (if (zp np) 0 (+ 1 (floor (1- np) 341))))

(defun fn-heap-hroot-dir-pages (nt)
  (declare (xargs :guard (natp nt)))
  (+ 2 (ceiling (* 6 (nfix nt)) 2048)))

(defun fn-heap-hroot-image-octets (np)
  (declare (xargs :guard (natp np)))
  (let* ((np (nfix np)) (nt (fn-heap-hroot-ntables np)))
    (+ 512 (* 8 (+ (* 2048 np) (* 2 np) (* 2049 nt)
                   (* 2048 (fn-heap-hroot-dir-pages nt)))))))

(defun fn-heap-hroot-npages (profile)
  (declare (xargs :guard t))
  (+ 1 (* 4 (ceiling (nfix (fn-bs-profile-max-transactions profile)) 2048))
     (ceiling (nfix (fn-bs-profile-max-history-octets profile)) 16384)))

; A root's memory at the bounds (fn-hroot-memory-octets over its page store).
(defun fn-heap-hroot-memory-bound (profile)
  (declare (xargs :guard t))
  (+ (fn-heap-hroot-image-octets (fn-heap-hroot-npages profile))
     (* 8 (nfix (fn-bs-profile-max-transactions profile)))
     4096))

;; The most one generation's RESIDENT credit asks: the tail demand (twice the
;; root's memory) dominates the event, grow and retain demands.  The per-event
;; decode transient (books/history-root-credit.lisp fn-hroot-event-transient) is
;; NOT here: it is its own ops credit against the article pool, released after
;; the decode, so the reserve is the two generations' images only.
(defun fn-heap-hroot-demand-bound (profile)
  (declare (xargs :guard t))
  (+ (* 2 (fn-heap-hroot-memory-bound profile))
     (* 64 (+ 1 (nfix (fn-bs-profile-max-transactions profile))))
     (fn-heap-hroot-image-octets (fn-heap-hroot-npages profile))))

; The reserve: the retained generation and the candidate, each at the most
; its credit asks.
(defun fn-heap-hroot-reserve-octets (profile)
  (declare (xargs :guard t))
  (* 2 (fn-heap-hroot-demand-bound profile)))

(in-theory (disable fn-heap-hroot-reserve-octets fn-heap-hroot-demand-bound
                    fn-heap-hroot-memory-bound fn-heap-hroot-npages fn-heap-hroot-image-octets
                    fn-heap-hroot-ntables fn-heap-hroot-dir-pages))

(defthm fn-heap-hroot-dir-pages-natp
  (natp (fn-heap-hroot-dir-pages nt))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-heap-hroot-dir-pages))))
(defthm fn-heap-hroot-ntables-natp
  (natp (fn-heap-hroot-ntables np))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-heap-hroot-ntables))))
(defthm fn-heap-hroot-image-octets-natp
  (natp (fn-heap-hroot-image-octets np))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-heap-hroot-image-octets))))
(defthm fn-heap-hroot-npages-natp
  (natp (fn-heap-hroot-npages profile))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-heap-hroot-npages) (fn-bs-profile-max-history-octets fn-bs-profile-max-transactions fn-bs-profile-max-record-octets)))))
(defthm fn-heap-hroot-memory-bound-natp
  (natp (fn-heap-hroot-memory-bound profile))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-heap-hroot-memory-bound) (fn-bs-profile-max-history-octets fn-bs-profile-max-transactions fn-bs-profile-max-record-octets)))))
(defthm fn-heap-hroot-demand-bound-natp
  (natp (fn-heap-hroot-demand-bound profile))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-heap-hroot-demand-bound) (fn-bs-profile-max-history-octets fn-bs-profile-max-transactions fn-bs-profile-max-record-octets)))))
(defthm fn-heap-hroot-reserve-octets-natp
  (natp (fn-heap-hroot-reserve-octets profile))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-heap-hroot-reserve-octets) (fn-bs-profile-max-history-octets fn-bs-profile-max-transactions fn-bs-profile-max-record-octets)))))

(defthm fn-heap-hroot-ntables-monotone
  (implies (and (natp a) (natp b) (<= a b))
           (<= (fn-heap-hroot-ntables a) (fn-heap-hroot-ntables b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-hroot-ntables))))

(defthm fn-heap-hroot-dir-pages-monotone
  (implies (and (natp a) (natp b) (<= a b))
           (<= (fn-heap-hroot-dir-pages a) (fn-heap-hroot-dir-pages b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-hroot-dir-pages))))

(defthm fn-heap-hroot-image-octets-monotone
  (implies (and (natp a) (natp b) (<= a b))
           (<= (fn-heap-hroot-image-octets a) (fn-heap-hroot-image-octets b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-hroot-image-octets)
           :use (fn-heap-hroot-ntables-monotone
                 (:instance fn-heap-hroot-dir-pages-monotone
                            (a (fn-heap-hroot-ntables a)) (b (fn-heap-hroot-ntables b)))))))

(defthm fn-heap-hroot-ceiling-2048-monotone
  (implies (and (natp x) (natp y) (<= x y))
           (<= (ceiling x 2048) (ceiling y 2048)))
  :rule-classes nil)
(defthm fn-heap-hroot-ceiling-16384-monotone
  (implies (and (natp x) (natp y) (<= x y))
           (<= (ceiling x 16384) (ceiling y 16384)))
  :rule-classes nil)

(defthm fn-heap-hroot-npages-monotone
  (implies (and (<= (nfix (fn-bs-profile-max-history-octets p1))
                    (nfix (fn-bs-profile-max-history-octets p2)))
                (<= (nfix (fn-bs-profile-max-transactions p1))
                    (nfix (fn-bs-profile-max-transactions p2))))
           (<= (fn-heap-hroot-npages p1) (fn-heap-hroot-npages p2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-hroot-npages)
                                  (ceiling rewrite-ceiling-to-floor fn-bs-profile-max-history-octets
                                   fn-bs-profile-max-transactions))
           :use ((:instance fn-heap-hroot-ceiling-2048-monotone
                            (x (nfix (fn-bs-profile-max-transactions p1)))
                            (y (nfix (fn-bs-profile-max-transactions p2))))
                 (:instance fn-heap-hroot-ceiling-16384-monotone
                            (x (nfix (fn-bs-profile-max-history-octets p1)))
                            (y (nfix (fn-bs-profile-max-history-octets p2))))))))

(defthm fn-heap-hroot-reserve-octets-monotone
  (implies (and (<= (nfix (fn-bs-profile-max-history-octets p1))
                    (nfix (fn-bs-profile-max-history-octets p2)))
                (<= (nfix (fn-bs-profile-max-transactions p1))
                    (nfix (fn-bs-profile-max-transactions p2))))
           (<= (fn-heap-hroot-reserve-octets p1) (fn-heap-hroot-reserve-octets p2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-hroot-reserve-octets fn-heap-hroot-demand-bound
                                   fn-heap-hroot-memory-bound)
                                  (fn-heap-hroot-image-octets fn-heap-hroot-npages
                                   fn-bs-profile-max-history-octets
                                   fn-bs-profile-max-transactions))
           :use (fn-heap-hroot-npages-monotone
                 (:instance fn-heap-hroot-image-octets-monotone
                            (a (fn-heap-hroot-npages p1)) (b (fn-heap-hroot-npages p2)))))))

; Everything but the collector's room: the state at the profile's bounds,
; the open's transient at the input's bound, the request in flight and the
; articles.  A live reclaim's reserve is NOT here: it is the operator's
; opt-in (`fn-heap-store-reclaim-base-octets' below, books/reclaim-
; reservation.lisp).
(defun fn-heap-store-base-octets (profile core observed)
  (declare (xargs :guard t))
  (+ (fn-heap-core-dynamic core)
     (fn-heap-store-state-bound profile)
     (fn-heap-store-open-octets profile
                                (fn-heap-open-octets-bound profile observed)
                                (fn-heap-open-records-bound profile observed))
     (fn-heap-store-inflight-octets profile)
     (fn-heap-articles-octets profile)
     (fn-heap-hroot-reserve-octets profile)))

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

; The runtime capture is the actual fixed-process trigger, not the nursery
; cap used to solve the launcher's least dynamic-space equation.  OBSERVED is
; the store on disk the launcher's figure was sized by (heap-figure.lisp
; fn-heap-operation-observation; lane reservation-after-flip): the open term
; replays at most that, the state term stays at the profile's bounds.  NIL
; is the unobserved bound.
(defun fn-heap-runtime-protected-octets (profile core nursery observed)
 (declare (xargs :guard t))
 (+ (fn-heap-store-base-octets profile core observed)
    (* 2 (max *fn-heap-nursery-least-octets* (nfix nursery)))))

; Adding backing can raise the launcher's trigger. Re-solve that room rather
; than spending it as the child bank's headroom. Preserve any prior surplus.
(defun fn-heap-grow-runtime-dynamic (dynamic extra nursery-cap)
 (declare (xargs :guard t))
 (let* ((d (nfix dynamic)) (extra (nfix extra))
        (backing (nfix (- d (* 2 (fn-heap-nursery-trigger d nursery-cap))))))
  (max (+ d extra) (fn-heap-with-nursery (+ backing extra) nursery-cap))))
(defthm fn-heap-grow-runtime-dynamic-covers-addition
 (<= (+ (nfix dynamic) (nfix extra))
     (fn-heap-grow-runtime-dynamic dynamic extra nursery-cap))
 :rule-classes :linear
 :hints (("Goal" :in-theory (e/d (fn-heap-grow-runtime-dynamic)
                                (fn-heap-with-nursery fn-heap-nursery-trigger)))))

(in-theory (disable fn-heap-runtime-protected-octets fn-heap-grow-runtime-dynamic))

; THE FIGURE, in octets.
(defun fn-heap-store-figure-octets (profile core nursery observed)
  (declare (xargs :guard t))
  (fn-heap-with-nursery (fn-heap-store-base-octets profile core observed) nursery))

(defthm fn-heap-store-figure-octets-natp
  (natp (fn-heap-store-figure-octets profile core nursery observed))
  :rule-classes :type-prescription)

; The need grows with the store and the input: at most the base and the room.
(local
 (defthm fn-heap-store-state-within-the-bound
   (implies (and (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
                     (nfix (fn-bs-profile-max-history-octets profile)))
                 (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile))))
            (<= (fn-heap-store-state-octets profile used n m)
                (fn-heap-store-state-bound profile)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-heap-store-state-octets fn-heap-store-state-bound)
                                   (fn-heap-arena-octets fn-heap-store-history-octets
                                    fn-bs-profile-max-history-octets
                                    fn-bs-profile-max-transactions fn-bs-profile-field))
            :use (fn-heap-store-history-holds-payload-and-memberships)))))

(local
 (defthm fn-heap-store-open-octets-monotone
   (implies (and (<= (nfix ou) (nfix h)) (<= (nfix on) (nfix tt)))
            (<= (fn-heap-store-open-octets profile ou on)
                (fn-heap-store-open-octets profile h tt)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-heap-open-chunk-bound)
            :use ((:instance fn-heap-open-chunk-bound-monotone
                             (p1 profile) (p2 profile) (ou1 ou) (ou2 h)))))))

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
   (implies (and (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
                     (nfix (fn-bs-profile-max-history-octets profile)))
                 (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                 (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                 (<= (nfix on) (fn-heap-open-records-bound profile observed)))
            (<= (fn-heap-store-need profile core used n m ou on trigger)
                (+ (fn-heap-store-base-octets profile core observed) (* 2 (nfix trigger)))))
   :hints (("Goal" :in-theory (e/d (fn-heap-store-need fn-heap-store-base-octets)
                                   (fn-heap-store-state-octets fn-heap-store-open-octets
                                    fn-heap-store-state-bound
                                    fn-heap-store-inflight-octets fn-heap-core-dynamic
                                    fn-heap-open-octets-bound fn-heap-open-records-bound
                                    fn-bs-profile-max-history-octets
                                    fn-bs-profile-max-transactions nfix))
            :use ((:instance fn-heap-store-state-within-the-bound)
                  (:instance fn-heap-store-open-octets-monotone
                             (h (fn-heap-open-octets-bound profile observed))
                             (tt (fn-heap-open-records-bound profile observed))))))))

; KEYSTONE.  In a dynamic space of D octets, D at least the figure, every
; store the profile admits -- USED payload octets and M memberships whose
; charges (the payload's octets and `*fn-sbud-membership-octets*' a
; membership: the history budget's) are together within H, N records within
; T -- fits, with the open's transient over any input within the observed
; bound (OU octets, ON records), the request in flight, both buffers, the
; image's dynamic content and the collector's room at the trigger the host
; sets in D.
(defthm fn-heap-store-figure-holds-every-store
  (implies (and (natp d)
                (<= (fn-heap-store-figure-octets profile core nursery observed) d)
                (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
                    (nfix (fn-bs-profile-max-history-octets profile)))
                (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                (<= (nfix on) (fn-heap-open-records-bound profile observed)))
           (<= (fn-heap-store-need profile core used n m ou on
                                   (fn-heap-nursery-trigger d nursery))
               d))
  :hints (("Goal" :in-theory (union-theories
                               '(fn-heap-store-figure-octets fn-heap-store-base-octets-natp
                                 fn-heap-nfix-of-nursery-trigger)
                               (theory 'minimal-theory))
           :use ((:instance fn-heap-store-need-within-the-base
                            (trigger (fn-heap-nursery-trigger d nursery)))
                 (:instance fn-heap-with-nursery-holds-the-trigger
                            (base (fn-heap-store-base-octets profile core observed)))))))

; THE OPT-IN's FIGURE.  An operator who asks for live reclaim
; (`[resources] reclaim_live = true') reserves, beyond the store figure, the
; owner's work reserve: the open's transient at the input's bound and the
; reclaim's excess over it, the larger of the two (fn-heap-open-and-excess-is-
; the-larger).  Without the key no such term exists and a live reclaim is
; refused by name (books/owner-reclaim-pass.lisp fn-orcp-reserve).
(defun fn-heap-store-reclaim-base-octets (profile core observed)
  (declare (xargs :guard t))
  (+ (fn-heap-store-base-octets profile core observed)
     (fn-heap-reclaim-excess-octets profile
                                    (fn-heap-open-octets-bound profile observed)
                                    (fn-heap-open-records-bound profile observed))))

(defthm fn-heap-store-reclaim-base-octets-natp
  (natp (fn-heap-store-reclaim-base-octets profile core observed))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-heap-store-reclaim-base-is-at-least-the-base
  (<= (fn-heap-store-base-octets profile core observed)
      (fn-heap-store-reclaim-base-octets profile core observed))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-heap-store-reclaim-base-octets))))

; The store figure with the opt-in's reserve, in octets.
(defun fn-heap-store-live-figure-octets (profile core nursery observed)
  (declare (xargs :guard t))
  (fn-heap-with-nursery (fn-heap-store-reclaim-base-octets profile core observed) nursery))

(defthm fn-heap-store-live-figure-octets-natp
  (natp (fn-heap-store-live-figure-octets profile core nursery observed))
  :rule-classes :type-prescription)

; What a process needs while it serves a store of USED payload octets in N
; records with M memberships and a live reclaim pass runs over it: the
; image, the state, the pass's demand over the store's shape (N records
; charging USED + 320 M), the request in flight, the articles and the
; collector's room at TRIGGER.  The open's transient is not live: the open
; ended before the run's ledger was installed.
(defun fn-heap-store-reclaim-need (profile core used n m trigger)
  (declare (xargs :guard t))
  (+ (fn-heap-core-dynamic core)
     (fn-heap-store-state-octets profile used n m)
     (fn-heap-reclaim-demand-octets n (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))))
     (fn-heap-store-inflight-octets profile)
     (fn-heap-articles-octets profile)
     (* 2 (nfix trigger))))

(local
 (defthm fn-heap-store-reclaim-need-within-the-base
   (implies (and (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
                     (nfix (fn-bs-profile-max-history-octets profile)))
                 (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile))))
            (<= (fn-heap-store-reclaim-need profile core used n m trigger)
                (+ (fn-heap-store-reclaim-base-octets profile core observed)
                   (* 2 (nfix trigger)))))
   :hints (("Goal" :in-theory (e/d (fn-heap-store-reclaim-need fn-heap-store-base-octets
                                    fn-heap-store-reclaim-base-octets
                                    fn-heap-reclaim-octets)
                                   (fn-heap-store-state-octets fn-heap-store-open-octets
                                    fn-heap-store-state-bound fn-heap-reclaim-demand-octets
                                    fn-heap-store-inflight-octets fn-heap-core-dynamic
                                    fn-heap-open-octets-bound fn-heap-open-records-bound
                                    fn-bs-profile-max-history-octets
                                    fn-bs-profile-max-transactions))
            :use ((:instance fn-heap-store-state-within-the-bound)
                  (:instance fn-heap-open-and-excess-hold-the-reclaim
                             (ou (fn-heap-open-octets-bound profile observed))
                             (on (fn-heap-open-records-bound profile observed)))
                  (:instance fn-heap-reclaim-demand-octets-monotone
                             (n1 n) (c1 (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))))
                             (n2 (fn-bs-profile-max-transactions profile))
                             (c2 (fn-bs-profile-max-history-octets profile))))))))

; KEYSTONE (K4), CONDITIONED ON THE OPT-IN.  In a dynamic space of D octets,
; D at least the LIVE figure (the store figure with the opt-in's reserve) at
; ANY observation, every store the profile admits -- USED payload octets and
; M memberships charged together within H, N records within T -- fits with a
; live reclaim pass over it, the request in flight, the articles, the
; image's dynamic content and the collector's room at the trigger the host
; sets in D.  The launcher reserves the figure for `run' at the observed
; store (books/heap-figure.lisp fn-heap-operation-figure-octets): this holds
; whatever the store was when the node started and whatever it grew to.
(defthm fn-heap-store-live-figure-holds-every-store-and-its-reclaim
  (implies (and (natp d)
                (<= (fn-heap-store-live-figure-octets profile core nursery observed) d)
                (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
                    (nfix (fn-bs-profile-max-history-octets profile)))
                (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile))))
           (<= (fn-heap-store-reclaim-need profile core used n m
                                           (fn-heap-nursery-trigger d nursery))
               d))
  :hints (("Goal" :in-theory (union-theories
                               '(fn-heap-store-live-figure-octets
                                 fn-heap-store-reclaim-base-octets-natp
                                 fn-heap-nfix-of-nursery-trigger)
                               (theory 'minimal-theory))
           :use ((:instance fn-heap-store-reclaim-need-within-the-base
                            (trigger (fn-heap-nursery-trigger d nursery)))
                 (:instance fn-heap-with-nursery-holds-the-trigger
                            (base (fn-heap-store-reclaim-base-octets profile core observed)))))))

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
(defthm fn-heap-store-base-octets-grows-with-the-profile
  (implies (and (<= (nfix (fn-bs-profile-max-history-octets p1))
                    (nfix (fn-bs-profile-max-history-octets p2)))
                (<= (nfix (fn-bs-profile-max-transactions p1))
                    (nfix (fn-bs-profile-max-transactions p2)))
                (<= (nfix (fn-bs-profile-max-record-octets p1))
                    (nfix (fn-bs-profile-max-record-octets p2)))
                (<= (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* p1))
                    (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* p2)))
                (<= (fn-ock-capture-budget p1) (fn-ock-capture-budget p2))
                (<= (nfix (fn-bs-profile-max-article-octets p1))
                    (nfix (fn-bs-profile-max-article-octets p2))))
           (<= (fn-heap-store-base-octets p1 core nil)
               (fn-heap-store-base-octets p2 core nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-store-base-octets fn-heap-store-state-bound
                                   fn-heap-store-history-octets
                                   fn-heap-store-open-octets fn-heap-store-inflight-octets)
                                  (fn-ock-capture-budget fn-heap-open-bounds-of-nil
                                   fn-heap-arena-octets fn-heap-membership-bound
                                   fn-heap-open-octets-bound fn-heap-open-records-bound
                                   fn-bs-profile-max-history-octets
                                   fn-bs-profile-max-transactions
                                   fn-bs-profile-max-groups-per-article
                                   fn-bs-profile-max-record-octets
                                   fn-bs-profile-max-article-octets
                                   fn-bs-profile-field))
           :use ((:instance fn-heap-open-bounds-of-nil (profile p1))
                 (:instance fn-heap-open-bounds-of-nil (profile p2))
                 (:instance fn-heap-articles-octets-monotone)
                 (:instance fn-heap-hroot-reserve-octets-monotone)
                 (:instance fn-heap-open-chunk-bound-monotone
                            (ou1 (fn-bs-profile-max-history-octets p1))
                            (ou2 (fn-bs-profile-max-history-octets p2))))
           :nonlinearp t)))

(in-theory (disable fn-heap-store-need fn-heap-store-reclaim-need fn-heap-store-base-octets
                    fn-heap-membership-bound
                    fn-heap-store-figure-octets fn-heap-core-dynamic fn-heap-core-file
                    fn-heap-open-octets-bound fn-heap-open-records-bound))
