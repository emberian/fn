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
;              - per MESSAGE-ID octet, more: the owner view's Message-ID trie
;                (a cons and a list cell a character, 32), its rebuild while
;                a checkpoint is published (the base's event index,
;                fn-scka-restore-base, 32 more) and the two strings that name
;                it in the row and the overview (4 each, twice posting): 80
;                an octet, *fn-heap-record-msgid-octet-cost* (48) over the
;                header octet's 32, for at most *fn-record-max-msgid* (RFC
;                5536 3.1.3's 250, which every admission checks:
;                fn-af-message-idp, fn-record-msgidp).
;              Against f8-reservation's long-header curve (250-octet
;              Message-IDs, 900-octet Subjects): 222 Message-ID octets x 80
;              and 872 Subject octets x 8 is 24.7 KB a record over the short
;              headers' state, where 23.5 KB was measured posting.
;              A record's header octets are octets of its payload, which the
;              history budget charges (USED), and at most the profile's
;              max-header-octets (HDR), so the header term of N records is at
;              most the cost of min(USED, N x HDR) octets
;              (`fn-heap-record-headers-octets'); the rest is
;              *fn-heap-record-octets* a record, the fixed part and the
;              Message-ID's at its ceiling.  KEYSTONE
;              `fn-heap-records-retained-within-the-terms'.
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
; A record's retained state (the header's comment, `records'): the fixed
; part, a header octet's columns, and a Message-ID octet's trie and names.
(defconst *fn-heap-record-fixed-octets* 4096)
(defconst *fn-heap-record-header-octet-cost* 32)
(defconst *fn-heap-record-msgid-octet-cost* 48)
; The part of a record's state no header octet but the Message-ID's moves:
; the fixed part and a Message-ID at its ceiling (16,096 octets).
(defconst *fn-heap-record-octets*
  (+ *fn-heap-record-fixed-octets*
     (* *fn-heap-record-msgid-octet-cost* *fn-record-max-msgid*)))
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

; THE ARENA's slope: an octet more of payload costs at most two octets of
; the term, plus one page pointer at a page boundary.  (Today's paged arena:
; one octet and 32 per page.  A cache bound that does not grow with USED,
; arena-offheap-3's, has slope 0.)  With monotonicity it is all the history
; bound below uses of the arena.
(local
 (defthm fn-heap-floor-page-bounds
   (implies (natp a)
            (and (<= (* 262144 (floor a 262144)) a)
                 (< a (* 262144 (+ 1 (floor a 262144))))))
   :rule-classes nil))

(local
 (defthm fn-heap-floor-page-of-sum
   (implies (and (natp u) (natp x))
            (<= (floor (+ u x) 262144) (+ (floor u 262144) (floor x 262144) 1)))
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
; octet costs the header octet's and the trie's).
(defun fn-heap-record-retained-octets (mid hdr)
  (declare (xargs :guard t))
  (+ *fn-heap-record-fixed-octets*
     (* *fn-heap-record-header-octet-cost* (nfix hdr))
     (* *fn-heap-record-msgid-octet-cost* (nfix mid))))

; The header term of N records holding USED payload octets under the
; profile's header bound.
(defun fn-heap-record-headers-octets (profile used n)
  (declare (xargs :guard t))
  (* *fn-heap-record-header-octet-cost*
     (min (nfix used)
          (* (nfix n) (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile))))))

(defthm fn-heap-record-headers-octets-natp
  (natp (fn-heap-record-headers-octets profile used n))
  :rule-classes :type-prescription)

; The records a store holds, each (MID HDR PAYLOAD): its Message-ID's
; octets, its header's and its payload's.  Admissible under a profile: the
; Message-ID within RFC 5536's 250 (every admission checks it), the header
; within the profile's max-header-octets (the parse under the profile's
; limits refuses more), and the header a part of the payload.
(defun fn-heap-record-admissiblep (profile rec)
  (declare (xargs :guard t))
  (and (true-listp rec) (equal (len rec) 3)
       (natp (first rec)) (natp (second rec)) (natp (third rec))
       (<= (first rec) *fn-record-max-msgid*)
       (<= (second rec) (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile)))
       (<= (second rec) (third rec))))

(defun fn-heap-records-admissiblep (profile recs)
  (declare (xargs :guard t))
  (if (consp recs)
      (and (fn-heap-record-admissiblep profile (car recs))
           (fn-heap-records-admissiblep profile (cdr recs)))
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

(defun fn-heap-records-payload-octets (recs)
  (declare (xargs :guard t))
  (if (consp recs)
      (+ (let ((rec (car recs)))
           (if (and (consp rec) (consp (cdr rec)) (consp (cddr rec))) (nfix (caddr rec)) 0))
         (fn-heap-records-payload-octets (cdr recs)))
    0))

(defun fn-heap-records-header-octets (recs)
  (declare (xargs :guard t))
  (if (consp recs)
      (+ (let ((rec (car recs)))
           (if (and (consp rec) (consp (cdr rec))) (nfix (cadr rec)) 0))
         (fn-heap-records-header-octets (cdr recs)))
    0))

(local
 (defthm fn-heap-records-retained-is-fixed-and-headers
   (implies (fn-heap-records-admissiblep profile recs)
            (<= (fn-heap-records-retained-octets recs)
                (+ (* (len recs) *fn-heap-record-octets*)
                   (* *fn-heap-record-header-octet-cost*
                      (fn-heap-records-header-octets recs)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-heap-records-admissiblep profile recs)
            :in-theory (e/d (fn-heap-record-retained-octets) (fn-bs-profile-field))))))

(local
 (defthm fn-heap-records-headers-within-payload
   (implies (fn-heap-records-admissiblep profile recs)
            (<= (fn-heap-records-header-octets recs)
                (fn-heap-records-payload-octets recs)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-heap-records-admissiblep profile recs)
            :in-theory (disable fn-bs-profile-field)))))

(local
 (defthm fn-heap-records-headers-within-the-limit
   (implies (fn-heap-records-admissiblep profile recs)
            (<= (fn-heap-records-header-octets recs)
                (* (len recs)
                   (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-heap-records-admissiblep profile recs)
            :in-theory (disable fn-bs-profile-field)))))

; KEYSTONE (the record term is a bound for every admissible record).  The
; state retained by records each admissible under the profile -- a
; Message-ID within 250 octets, a header within the profile's
; max-header-octets and a part of the payload -- is within the figure's two
; record terms at N = their count and USED = their payload's octets:
; *fn-heap-record-octets* a record, and the header term.
(defthm fn-heap-records-retained-within-the-terms
  (implies (fn-heap-records-admissiblep profile recs)
           (<= (fn-heap-records-retained-octets recs)
               (+ (* (len recs) *fn-heap-record-octets*)
                  (fn-heap-record-headers-octets
                   profile (fn-heap-records-payload-octets recs) (len recs)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-heap-records-retained-octets
                                      fn-heap-records-header-octets
                                      fn-heap-records-payload-octets
                                      fn-heap-records-admissiblep
                                      fn-bs-profile-field)
           :use (fn-heap-records-retained-is-fixed-and-headers
                 fn-heap-records-headers-within-payload
                 fn-heap-records-headers-within-the-limit))))

; The header term grows with the payload, the records and the header bound.
(defthm fn-heap-record-headers-octets-monotone
  (implies (and (<= (nfix u1) (nfix u2)) (<= (nfix n1) (nfix n2))
                (<= (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* p1))
                    (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* p2))))
           (<= (fn-heap-record-headers-octets p1 u1 n1)
               (fn-heap-record-headers-octets p2 u2 n2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-profile-field)
           :nonlinearp t)))

(in-theory (disable fn-heap-record-headers-octets))

; The state a store of USED payload octets, N records and M memberships
; keeps: the arena, the handles, the records' fixed and header terms (twice:
; the collector's copy) and the memberships.
(defun fn-heap-store-state-octets (profile used n m)
  (declare (xargs :guard t))
  (+ (fn-heap-arena-octets used)
     (* *fn-heap-handle-octets* (nfix n))
     (* 2 (nfix n) *fn-heap-record-octets*)
     (* 2 (fn-heap-record-headers-octets profile used n))
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
     (* 2 (fn-heap-record-headers-octets profile
                                         (fn-bs-profile-max-history-octets profile)
                                         (fn-bs-profile-max-transactions profile)))))

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

; Everything but the collector's room: the state at the profile's bounds,
; the open's transient at the input's bound.
(defun fn-heap-store-base-octets (profile core observed)
  (declare (xargs :guard t))
  (+ (fn-heap-core-dynamic core)
     (fn-heap-store-state-bound profile)
     (fn-heap-store-open-octets profile
                                (fn-heap-open-octets-bound profile observed)
                                (fn-heap-open-records-bound profile observed))
     (fn-heap-store-inflight-octets profile)
     (fn-heap-articles-octets profile)))

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
            :use (fn-heap-store-history-holds-payload-and-memberships
                  (:instance fn-heap-record-headers-octets-monotone
                             (p1 profile) (p2 profile) (u1 used) (n1 n)
                             (u2 (fn-bs-profile-max-history-octets profile))
                             (n2 (fn-bs-profile-max-transactions profile))))))))

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
                 (:instance fn-heap-open-chunk-bound-monotone
                            (ou1 (fn-bs-profile-max-history-octets p1))
                            (ou2 (fn-bs-profile-max-history-octets p2)))
                 (:instance fn-heap-record-headers-octets-monotone
                            (u1 (fn-bs-profile-max-history-octets p1))
                            (u2 (fn-bs-profile-max-history-octets p2))
                            (n1 (fn-bs-profile-max-transactions p1))
                            (n2 (fn-bs-profile-max-transactions p2))))
           :nonlinearp t)))

(in-theory (disable fn-heap-store-need fn-heap-store-base-octets fn-heap-membership-bound
                    fn-heap-store-figure-octets fn-heap-core-dynamic fn-heap-core-file
                    fn-heap-open-octets-bound fn-heap-open-records-bound))
