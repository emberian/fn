; fn: the process's memory as five terms against one configured figure
; (Builder M, landing 1, 2026-10-09; RUNTIME-MODEL section 6; revision 3
; after Codex's two cross-reviews, build/memory/l1/codex-review*.final.md).
;
;   M_base + M_owner + C x M_connection + M_inflight + M_maintenance
;     <= M_configured
;
; THE POINT.  books/heap-figure.lisp and books/heap-reservation.lisp decide a
; RESERVATION (the dynamic space SBCL maps, the core file, every thread's
; control stack and runtime areas) and compare it with the least of every
; machine observation, resident or address-space alike.  That figure is
; neither the process's resident memory (VmHWM 135-178 MiB on the small
; preset where the reservation is about 1 GB) nor a fact about what a
; command does, and comparing it with a resident limit (a cgroup's
; memory.max) refuses a node the limit would hold (L-FRESH).  This book
; states the resident equation over the state the books hold: each term a
; function of the store's CHARGED TOTALS (what the checkpoint header and the
; log past it carry) and of the configuration, never of the profile's
; ceilings where a state exists.
;
; WHAT IS AND IS NOT CLAIMED.  The keystones over these definitions relate
; model terms to each other (the instant within the sum, the sum monotone,
; reopen within the limit, the launch).  That each term bounds what the
; process holds is a REFINEMENT obligation per term, named beside it (O-...),
; discharged by a proof over the host's state where one exists and otherwise
; carried as an assumption the process measurement (VmHWM, the host test)
; checks; the gap between the sum and the measured peak is reported.
;
; THE INPUTS, plain lists (decisions, not state):
;
;   TOT   the charged totals (RECORDS ARENA HCHARGE MEMBERSHIPS EVENTS LOG
;         HISTORY CHARGE RESIDENCY), each read from the store, none derived:
;         RECORDS the committed records (fn-sbud-used); ARENA the physical
;         octets of every held payload (accepted-statement composites'
;         included); HCHARGE the held rows' header charges
;         (fn-sbud-held-heap-charge); MEMBERSHIPS their group memberships;
;         EVENTS the encoded octets of every record that is not a plain held
;         row (fn-sbud-row-octets' other arms: composites and non-article
;         events); LOG the octets of the log's records, what a full replay
;         reads; HISTORY the history image's event column, the padded SCC
;         encodings (books/history-image-plan.lisp fn-hp-x-rowlen's third
;         value, summed); CHARGE fn-sbud-bytes-used itself, the budget's
;         coordinate (it is not the arena's: a composite's encoding carries
;         its payload, Codex review 2 F6); RESIDENCY :resident (payloads in
;         the heap's arena, today) or :paged.
;   IMG   the image's resident floor, MEASURED (FILE ANON THREAD): the
;         core's file-backed pages resident after the open, the runtime's
;         anonymous floor, one thread's resident areas.  A-IMAGE-RESIDENT.
;   CFG   (CONNECTIONS TLSP TRIGGER PUB-TRIGGER RECLAIM-LIVE CACHE COLD
;          HANDSHAKES OVER-WINDOW SERVER-OCTETS): the connection cap C,
;         whether a TLS context is loaded, the collector's trigger in service
;         and during a publication, the live-reclaim opt-in, the paged
;         payload cache's octets, the cold-read pool's funded budget (its
;         ledger's heap and native allowances: books/page-read-ledger.lisp,
;         cached entries and full paths charged within it), the handshake
;         allowance the served budget holds (the live limit, or the
;         outstanding handshakes when a reconfiguration lowered it), the OVER
;         cursor quantum the host uses (fn-splan-cursor-window of its
;         override), and the server name's octets (each NOV line's Xref).
;
; A-GC-FOOTPRINT: the dynamic space's resident pages are at most its live
; objects plus twice the trigger in force, freed pages returned (MEM-003).

(in-package "ACL2")
(include-book "charged-totals")
(include-book "heap-reservation")
(include-book "connection-budget")
(include-book "page-read-startup")
(include-book "served-plan-cursor")
(include-book "proto/adt-bytes")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; Accessors.

(defun fn-mm-img-file (img) (declare (xargs :guard t)) (fn-mm-nat 0 img))
(defun fn-mm-img-anon (img) (declare (xargs :guard t)) (fn-mm-nat 1 img))
(defun fn-mm-img-thread (img) (declare (xargs :guard t)) (fn-mm-nat 2 img))

(defun fn-mm-img-le (a b)
  (declare (xargs :guard t))
  (and (<= (fn-mm-img-file a) (fn-mm-img-file b))
       (<= (fn-mm-img-anon a) (fn-mm-img-anon b))
       (<= (fn-mm-img-thread a) (fn-mm-img-thread b))))

(defun fn-mm-cfg-connections (cfg) (declare (xargs :guard t)) (fn-mm-nat 0 cfg))
(defun fn-mm-cfg-tlsp (cfg) (declare (xargs :guard t)) (and (nth 1 (true-list-fix cfg)) t))
(defun fn-mm-cfg-trigger (cfg) (declare (xargs :guard t)) (fn-mm-nat 2 cfg))
(defun fn-mm-cfg-pub-trigger (cfg)
  (declare (xargs :guard t))
  (max (fn-mm-nat 3 cfg) (fn-mm-cfg-trigger cfg)))
(defun fn-mm-cfg-reclaim-live-p (cfg) (declare (xargs :guard t)) (and (nth 4 (true-list-fix cfg)) t))
(defun fn-mm-cfg-cache (cfg) (declare (xargs :guard t)) (fn-mm-nat 5 cfg))
(defun fn-mm-cfg-cold (cfg) (declare (xargs :guard t)) (fn-mm-nat 6 cfg))
(defun fn-mm-cfg-handshakes (cfg) (declare (xargs :guard t)) (fn-mm-nat 7 cfg))
(defun fn-mm-cfg-over-window (cfg)
  (declare (xargs :guard t))
  (fn-splan-cursor-window (nth 8 (true-list-fix cfg))))
(defun fn-mm-cfg-server-octets (cfg) (declare (xargs :guard t)) (fn-mm-nat 9 cfg))
; P, the large-payload holders: how many connections may hold a large reply
; (an article, an OVER quantum, a POST body) at once.  A natural at most C
; when the host bounds them (contract v2.1's pool, a FIFO lease that waits);
; otherwise C, today's host, where every connection may hold one.
(defun fn-mm-cfg-holders (cfg)
  (declare (xargs :guard t))
  (let ((p (nth 10 (true-list-fix cfg))))
    (if (natp p)
        (min p (fn-mm-cfg-connections cfg))
      (fn-mm-cfg-connections cfg))))

; -----------------------------------------------------------------------------
; M_configured.  Ruling (coordinator 2026-10-09, reversible, for ember): the
; small preset's 128 MiB (ruling 16) is the only per-preset figure; every
; other preset's is the operator's when given, else the machine's resident
; limit (D27: no named per-preset constant).

(defconst *fn-mm-preset-configured*
  '((:small . 134217728)))

(defun fn-mm-preset-configured-octets (preset)
  (declare (xargs :guard t))
  (let ((row (assoc-equal preset *fn-mm-preset-configured*)))
    (and (consp row) (cdr row))))

; The least observation, NIL when none: an observation is a natural (0 is a
; limit of nothing, not an absent one); anything else is not an observation.
(defun fn-mm-least-observation (obs)
  (declare (xargs :guard t))
  (if (consp obs)
      (let ((rest (fn-mm-least-observation (cdr obs))) (x (car obs)))
        (cond ((not (natp x)) rest)
              ((natp rest) (min x rest))
              (t x)))
    nil))

; The resident limit a decision is held to: the configured figure (a
; natural, or NIL for none) and every RESIDENT observation (physical memory
; less the OS reserve, a cgroup's memory.max up the hierarchy).  NIL when
; nothing bounds it.  Address-space limits (RLIMIT_AS, RLIMIT_DATA) are not
; resident observations: they bound the reservation only.
(defun fn-mm-resident-limit (configured resident-obs)
  (declare (xargs :guard t))
  (fn-mm-least-observation (cons configured resident-obs)))

; -----------------------------------------------------------------------------
; THE FIVE TERMS.

; M_base: the image's resident floor, every thread the node runs
; (connections cost none: host/native/mux.lisp; fn-heap-thread-count), the
; collector's room at the service trigger.  O-BASE: A-IMAGE-RESIDENT,
; A-GC-FOOTPRINT, and the thread count is the host's (heap-reservation).
(defun fn-mm-base (img cfg)
  (declare (xargs :guard t))
  (+ (fn-mm-img-file img) (fn-mm-img-anon img)
     (* (fn-heap-thread-count (fn-mm-cfg-connections cfg)) (fn-mm-img-thread img))
     (* 2 (fn-mm-cfg-trigger cfg))))

; The history root's page image over the store: four word columns of one
; word a record and the event column of the log's octets, each region of U
; octets taking adt-cap U pages (a power of two), after one header page
; (books/history-image-open.lisp fn-his-layout over books/proto/adt-bytes
; adt-end-l).  O-HROOT: the layout's plan is (RECORDS (8R 8R 8R 8R E)), E
; the HISTORY total (the padded SCC encodings, not the wire log's octets:
; Codex review 2 F1).  The LIVE root is built incrementally
; (host/native/history-root.lisp): a region that outgrows its capacity is
; relocated to newly appended pages and the old ones stay in the backing
; array (books/history-pages-relocate-step.lisp), so a region of final
; capacity K has held at most 1 + 2 + ... + K < 2K pages; the live root is
; charged twice the canonical layout (Codex review 3).  O-HROOT includes
; that relocation bound.
(defthm fn-mm-adt-end-l-natp
  (natp (adt-end-l lens start))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (adt-end-l lens start) :in-theory (enable adt-end-l))))

(defun fn-mm-hroot-npages (n history)
  (declare (xargs :guard t))
  (let ((w (* 8 (nfix n))))
    (* 2 (adt-end-l (list w w w w (nfix history)) 1))))

(defthm fn-mm-hroot-npages-natp
  (natp (fn-mm-hroot-npages n log))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable adt-end-l))))

; One generation's demand, fn-heap-hroot-demand-bound's shape at the store.
(defun fn-mm-hroot-demand (n history)
  (declare (xargs :guard t))
  (let ((img (fn-heap-hroot-image-octets (fn-mm-hroot-npages n history))))
    (+ (* 2 (+ img (* 8 (nfix n)) 4096))
       (* 64 (+ 1 (nfix n)))
       img)))

; The payloads: in the arena (:resident), or the empty arena and the
; configured cache (:paged).
(defun fn-mm-payload-octets (tot cfg)
  (declare (xargs :guard t))
  (if (fn-mm-tot-paged-p tot)
      (+ (fn-heap-arena-octets 0) (fn-mm-cfg-cache cfg))
    (fn-heap-arena-octets (fn-mm-tot-arena tot))))

; The non-article records' heap: held as decoded events, at most sixteen
; heap octets an encoded octet, twice for the collector.  O-EVENTS (owed: a
; measurement or a proof over the decoded event's shape).
(defconst *fn-mm-event-heap-octets* (* 2 *fn-heap-list-octets-per-octet*))

; M_owner: the held rows (handles, each record's fixed part twice for the
; collector), the header columns at 8 heap octets a CHARGED HEADER octet
; (fn-heap-record-charge-covers-the-state; the payload's octets are the
; arena's and are not charged again), the memberships twice, the other
; records' events, the payloads, and the retained history root.
; O-OWNER: fn-heap-records-retained-within-the-terms restated over HCHARGE.
(defun fn-mm-owner (tot cfg)
  (declare (xargs :guard t))
  (let ((n (fn-mm-tot-records tot)))
    (+ (fn-mm-payload-octets tot cfg)
       (* *fn-heap-handle-octets* n)
       (* 2 n *fn-heap-record-octets*)
       (* *fn-heap-charge-heap-octets* (fn-mm-tot-hcharge tot))
       (* 2 *fn-heap-membership-octets* (fn-mm-tot-memberships tot))
       (* *fn-mm-event-heap-octets* (fn-mm-tot-events tot))
       (fn-mm-hroot-demand n (fn-mm-tot-history tot)))))

; A reply a connection holds: the article (connection-budget's stated
; workload, 2A + 1,024) or an OVER/XOVER cursor quantum, W NOV lines built
; as octet lists (books/over-window.lisp fn-ovw-step; W the host's quantum,
; CFG's OVER-WINDOW), each line at most the header bound, its number, size
; and line-count fields, and the generated Xref: the server name and, for
; each of at most G memberships, a space, the group name, a colon and the
; article number (books/nntp-xref.lisp).  O-NOV-LINE (owed): a NOV line is
; at most fn-mm-nov-line-octets.
(defconst *fn-mm-nov-fields-octets* 128)
(defconst *fn-mm-xref-membership-fixed-octets* 12)   ; " " ":" and 10 digits

(defun fn-mm-nov-line-octets (profile cfg)
  (declare (xargs :guard t))
  (+ (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile))
     *fn-mm-nov-fields-octets*
     (fn-mm-cfg-server-octets cfg)
     (* (nfix (fn-bs-profile-max-groups-per-article profile))
        (+ (nfix (fn-bs-profile-max-group-name-octets profile))
           *fn-mm-xref-membership-fixed-octets*))))

(defun fn-mm-over-window-octets (profile cfg)
  (declare (xargs :guard t))
  (* 2 *fn-heap-list-octets-per-octet* (fn-mm-cfg-over-window cfg)
     (fn-mm-nov-line-octets profile cfg)))

; M_connection, split by what holds it (coordinator ruling (d), 2026-10-09;
; Builder A's contract v2.1).  FIXED: what every open connection holds
; whatever it serves (fn-cbud-conn-octets at an article of 0: the record,
; reads, the reply status, the command line, COMPRESS, kernel buffers,
; TLS).  LARGE: the one large reply a holder holds, the article reply
; (connection-budget's 2A + status) or the OVER cursor quantum, whichever is
; larger.  The process holds C fixed parts and at most P large replies.
; O-CONN: connection-budget's terms over the mux state, and O-NOV-LINE.
; Adapter, owner Builder C: the OVER quantum is W NOV lines as octet lists
; until C's OVER landing renders it into one leased buffer of the article
; bound; then LARGE is the lease's capacity.
(defun fn-mm-connection-fixed (profile cfg)
  (declare (xargs :guard t) (ignore profile))
  (fn-cbud-conn-octets 0 (fn-mm-cfg-tlsp cfg)))

(defun fn-mm-large-reply (profile cfg)
  (declare (xargs :guard t))
  (max (+ (* 2 (nfix (fn-bs-profile-max-article-octets profile)))
          *fn-cbud-reply-status-octets*)
       (fn-mm-over-window-octets profile cfg)))

(defun fn-mm-large-pool (profile cfg)
  (declare (xargs :guard t))
  (* (fn-mm-cfg-holders cfg) (fn-mm-large-reply profile cfg)))

; One connection holding a large reply, the figure before the split.
(defun fn-mm-connection (profile cfg)
  (declare (xargs :guard t))
  (+ (fn-mm-connection-fixed profile cfg) (fn-mm-large-reply profile cfg)))

; C fixed parts and the holders' large replies.
(defun fn-mm-connections (profile cfg)
  (declare (xargs :guard t))
  (+ (* (fn-mm-cfg-connections cfg) (fn-mm-connection-fixed profile cfg))
     (fn-mm-large-pool profile cfg)))

; The cold-read pool: its funded budget, the ledger's heap and native
; allowances (books/page-read-ledger.lisp fn-prl-make; tables, registration
; with full paths, workers' reads and cached entries are all charged within
; it).  O-COLD: the ledger's charges and baseline stay within its budget.
(defun fn-mm-cold-reads (profile cfg)
  (declare (xargs :guard t) (ignore profile))
  (fn-mm-cfg-cold cfg))

; M_inflight: the request the owner serves (record and header lists, the
; taken submission, both octet buffers), the articles in flight (the slots'
; pool), the TLS handshakes' scratch, and the cold reads.
(defun fn-mm-inflight (profile cfg)
  (declare (xargs :guard t))
  (+ (fn-heap-store-inflight-octets profile)
     (fn-heap-articles-octets profile)
     (fn-cbud-handshake-octets (fn-mm-cfg-tlsp cfg) (fn-mm-cfg-handshakes cfg))
     (fn-mm-cold-reads profile cfg)))

; M_maintenance: the history root's candidate generation, the collector's
; raise while a publication runs, and, opted in, a live reclaim's second
; generation over the store's shape.
(defun fn-mm-maintenance (tot cfg)
  (declare (xargs :guard t))
  (let ((n (fn-mm-tot-records tot)))
    (+ (fn-mm-hroot-demand n (fn-mm-tot-history tot))
       (* 2 (nfix (- (fn-mm-cfg-pub-trigger cfg) (fn-mm-cfg-trigger cfg))))
       (if (fn-mm-cfg-reclaim-live-p cfg)
           (fn-heap-reclaim-demand-octets n (fn-mm-tot-charge tot))
         0))))

; THE SUM.
(defun fn-mm-sum (profile img cfg tot)
  (declare (xargs :guard t))
  (+ (fn-mm-base img cfg)
     (fn-mm-owner tot cfg)
     (fn-mm-connections profile cfg)
     (fn-mm-inflight profile cfg)
     (fn-mm-maintenance tot cfg)))

; THE INSTANT: K connections open, J of them holding a large reply, S
; article slots in use, H handshakes in flight, PUBLISHING whether a
; publication runs.
(defun fn-mm-need (profile img cfg tot k j s h publishing)
  (declare (xargs :guard t))
  (+ (fn-mm-base img cfg)
     (fn-mm-owner tot cfg)
     (* (nfix k) (fn-mm-connection-fixed profile cfg))
     (* (nfix j) (fn-mm-large-reply profile cfg))
     (fn-heap-store-inflight-octets profile)
     (* (nfix s) (fn-heap-article-reserve-octets profile))
     (* (nfix h) *fn-cbud-handshake-scratch-octets*)
     (fn-mm-cold-reads profile cfg)
     (if publishing (fn-mm-maintenance tot cfg) 0)))

; -----------------------------------------------------------------------------
; REOPEN.  Its named terms over the totals the open holds:
;   directory and index metadata: the owner's (the history root built once,
;     the keyed Message-ID table in each record's fixed part);
;   the recovery workspace: the open's transient over the LOG octets it may
;     read in full (fn-heap-store-open-octets: one chunk and one entry as
;     lists, the suffix's vectors, the per-record build) -- a full replay
;     when the suffix exceeds the fast path's K, so no tail bound is assumed;
;   dirty pages and the first publication after recovery: maintenance;
;   reader pins: none at reopen (no connection is accepted before the open
;     ends); every pin after it is a connection's;
;   failure-reporting headroom: one refusal rendered and logged.
(defconst *fn-mm-failure-headroom-octets*
  (* 2 *fn-heap-list-octets-per-octet* *fn-cbud-reply-status-octets*))

(defun fn-mm-reopen-need (profile img cfg tot)
  (declare (xargs :guard t))
  (+ (fn-mm-base img cfg)
     (fn-mm-owner tot cfg)
     (fn-heap-store-open-octets profile (fn-mm-tot-log tot) (fn-mm-tot-records tot))
     (fn-mm-maintenance tot cfg)
     *fn-mm-failure-headroom-octets*))

; THE OBSERVATION a store-opening command sizes itself by: the checkpoint
; header's totals HDR and the totals SUFFIX of the log's records past it,
; read without replay (Builder A's header field and log scan).
(defun fn-mm-observed-tot (hdr suffix)
  (declare (xargs :guard t))
  (fn-mm-tot-plus hdr suffix))

; -----------------------------------------------------------------------------
; THE GATE: a store's totals are admissible under LIMIT when the process
; serving it fits and its reopen fits.
(defun fn-mm-gate-p (profile img cfg limit tot)
  (declare (xargs :guard t))
  (and (natp limit)
       (<= (fn-mm-sum profile img cfg tot) limit)
       (<= (fn-mm-reopen-need profile img cfg tot) limit)))

; A commit of a record whose totals are REC: admitted exactly when the
; totals after it pass the gate.
(defun fn-mm-admit-record (profile img cfg limit tot rec)
  (declare (xargs :guard t))
  (let ((after (fn-mm-tot-plus tot rec)))
    (if (fn-mm-gate-p profile img cfg limit after)
        (list :admitted after)
      (list :refused :memory-model tot))))

; -----------------------------------------------------------------------------
; THE LAUNCH: resident against resident limits, the reservation against
; address-space limits, never crossed.  The dynamic space holds the core's
; dynamic content and every heap within the resident limit, with the
; collector's room.
(defun fn-mm-launch-dynamic (limit core nursery)
  (declare (xargs :guard t))
  (fn-heap-with-nursery (+ (fn-heap-core-dynamic core) (nfix limit)) nursery))

(defun fn-mm-launch-reservation (limit core nursery cfg profile)
  (declare (xargs :guard t))
  (fn-heap-reservation-octets (fn-heap-mb-of (fn-mm-launch-dynamic limit core nursery))
                              core (fn-heap-stack-kib profile)
                              (fn-heap-thread-count (fn-mm-cfg-connections cfg))))

; Answers (:launch LIMIT DYNAMIC) or (:refused REASON NEED LIMIT).  OBS is
; the observed totals (fn-mm-observed-tot).
(defun fn-mm-launch-decide (profile img cfg configured resident-obs address-obs
                                    core nursery obs)
  (declare (xargs :guard t))
  (let* ((limit (fn-mm-resident-limit configured resident-obs))
         (addr (fn-mm-least-observation address-obs)))
    (cond ((not (natp limit)) (list :refused :memory-unbounded 0 0))
          ((not (fn-mm-gate-p profile img cfg limit obs))
           (list :refused :configured-memory-cannot-hold-the-store
                 (max (fn-mm-sum profile img cfg obs)
                      (fn-mm-reopen-need profile img cfg obs))
                 limit))
          ((and (natp addr)
                (< addr (fn-mm-launch-reservation limit core nursery cfg profile)))
           (list :refused :address-space-cannot-hold-the-reservation
                 (fn-mm-launch-reservation limit core nursery cfg profile) addr))
          (t (list :launch limit (fn-mm-launch-dynamic limit core nursery))))))

; -----------------------------------------------------------------------------
; THE KEYSTONES and their lemmas.

(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-mm-times-monotone
  (implies (and (natp a) (natp b) (natp c) (<= a b)) (<= (* a c) (* b c)))
  :rule-classes nil :hints (("Goal" :nonlinearp t)))
;; fn-mm-connection-fixed and fn-mm-large-reply are naturals.
(defthm fn-mm-terms-natp
  (and (natp (fn-mm-base img cfg)) (natp (fn-mm-owner tot cfg))
       (natp (fn-mm-connection-fixed profile cfg)) (natp (fn-mm-large-reply profile cfg))
       (natp (fn-mm-connection profile cfg)) (natp (fn-mm-maintenance tot cfg))
       (natp (fn-mm-cfg-connections cfg)) (natp (fn-mm-cfg-holders cfg))
       (natp (fn-mm-cold-reads profile cfg)))
  :rule-classes nil)
; KEYSTONE K1.  The instant within the sum: at most C connections open, at
; most P of them holding a large reply, the article slots and the TLS
; handshake slots in use, publishing or not.
(defthm fn-mm-need-within-the-sum
  (implies (and (<= (nfix k) (fn-mm-cfg-connections cfg))
                (<= (nfix j) (fn-mm-cfg-holders cfg))
                (<= (nfix s) (fn-heap-article-slots profile))
                (<= (nfix h) (fn-cbud-handshake-slots (fn-mm-cfg-tlsp cfg) (fn-mm-cfg-handshakes cfg))))
           (<= (fn-mm-need profile img cfg tot k j s h publishing)
               (fn-mm-sum profile img cfg tot)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-need fn-mm-sum fn-mm-inflight fn-cbud-handshake-octets
                                   fn-mm-connections fn-mm-large-pool)
                                  (fn-mm-base fn-mm-owner fn-mm-connection-fixed fn-mm-large-reply
                                   fn-mm-maintenance fn-mm-cold-reads
                                   fn-heap-store-inflight-octets fn-heap-article-slots fn-cbud-handshake-slots
                                   fn-heap-articles-octets fn-heap-article-reserve-octets
                                   fn-mm-cfg-connections fn-mm-cfg-holders fn-mm-cfg-tlsp))
           :use ((:instance fn-heap-article-slots-are-held (k s))
                 fn-mm-terms-natp
                 (:instance fn-mm-times-monotone (a (nfix k)) (b (fn-mm-cfg-connections cfg))
                            (c (fn-mm-connection-fixed profile cfg)))
                 (:instance fn-mm-times-monotone (a (nfix j)) (b (fn-mm-cfg-holders cfg))
                            (c (fn-mm-large-reply profile cfg)))
                 (:instance fn-mm-times-monotone (a (nfix h))
                            (b (nfix (fn-cbud-handshake-slots (fn-mm-cfg-tlsp cfg) (fn-mm-cfg-handshakes cfg))))
                            (c *fn-cbud-handshake-scratch-octets*))))
          (and stable-under-simplificationp '(:nonlinearp t))))

(defthm fn-mm-pow2-at-least-covers-acc
  (implies (posp acc) (<= acc (adt-pow2-at-least k acc)))
  :rule-classes :linear
  :hints (("Goal" :induct (adt-pow2-at-least k acc) :in-theory (enable adt-pow2-at-least))))
(defthm fn-mm-pow2-at-least-posp
  (posp (adt-pow2-at-least k acc))
  :rule-classes :type-prescription
  :hints (("Goal" :use adt-natp-pow2-at-least)))
(defthm fn-mm-pow2-at-least-monotone
  (implies (and (posp acc) (<= (nfix k1) (nfix k2)))
           (<= (adt-pow2-at-least k1 acc) (adt-pow2-at-least k2 acc)))
  :rule-classes nil
  :hints (("Goal" :induct (adt-pow2-at-least k2 acc) :in-theory (enable adt-pow2-at-least))))
(defthm fn-mm-adt-cap-monotone
  (implies (and (natp x) (natp y) (<= x y)) (<= (adt-cap x) (adt-cap y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (adt-cap) (ceiling adt-pow2-at-least))
           :use ((:instance fn-heap-hroot-ceiling-16384-monotone)
                 (:instance fn-mm-pow2-at-least-monotone (acc 1)
                            (k1 (ceiling x 16384)) (k2 (ceiling y 16384)))))))
(defthm fn-mm-adt-cap-natp
  (natp (adt-cap u))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable adt-cap))))
(defthm fn-mm-hroot-npages-is
  (equal (fn-mm-hroot-npages n log)
         (* 2 (+ 1 (* 4 (adt-cap (* 8 (nfix n)))) (adt-cap (nfix log)))))
  :hints (("Goal" :in-theory (e/d (fn-mm-hroot-npages adt-end-l) (adt-cap)))))
(defthm fn-mm-hroot-npages-monotone
  (implies (and (<= (nfix n1) (nfix n2)) (<= (nfix l1) (nfix l2)))
           (<= (fn-mm-hroot-npages n1 l1) (fn-mm-hroot-npages n2 l2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable adt-cap fn-mm-hroot-npages)
           :use ((:instance fn-mm-adt-cap-monotone (x (* 8 (nfix n1))) (y (* 8 (nfix n2))))
                 (:instance fn-mm-adt-cap-monotone (x (nfix l1)) (y (nfix l2)))))))
(defthm fn-mm-hroot-demand-monotone
  (implies (and (<= (nfix n1) (nfix n2)) (<= (nfix l1) (nfix l2)))
           (<= (fn-mm-hroot-demand n1 l1) (fn-mm-hroot-demand n2 l2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-hroot-demand) (fn-heap-hroot-image-octets fn-mm-hroot-npages fn-mm-hroot-npages-is))
           :use (fn-mm-hroot-npages-monotone
                 (:instance fn-heap-hroot-image-octets-monotone
                            (a (fn-mm-hroot-npages n1 l1)) (b (fn-mm-hroot-npages n2 l2)))))))
(defthm fn-mm-tot-charge-monotone
  (implies (fn-mm-tot-le a b) (<= (fn-mm-tot-charge a) (fn-mm-tot-charge b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-tot-le)
                                  (fn-mm-tot-arena fn-mm-tot-hcharge fn-mm-tot-memberships
                                   fn-mm-tot-events fn-mm-tot-records fn-mm-tot-log fn-mm-tot-paged-p
                                   fn-mm-tot-history fn-mm-tot-charge)))))
(defthm fn-mm-owner-monotone
  (implies (fn-mm-tot-le a b) (<= (fn-mm-owner a cfg) (fn-mm-owner b cfg)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-owner fn-mm-payload-octets fn-mm-tot-le)
                                  (fn-mm-hroot-demand fn-heap-arena-octets
                                   fn-mm-tot-arena fn-mm-tot-hcharge fn-mm-tot-memberships
                                   fn-mm-tot-records fn-mm-tot-paged-p fn-mm-tot-events fn-mm-tot-log))
           :use ((:instance fn-heap-arena-octets-monotone (u1 (fn-mm-tot-arena a)) (u2 (fn-mm-tot-arena b)))
                 (:instance fn-mm-hroot-demand-monotone
                            (n1 (fn-mm-tot-records a)) (n2 (fn-mm-tot-records b))
                            (l1 (fn-mm-tot-history a)) (l2 (fn-mm-tot-history b)))))))
(defthm fn-mm-tot-le-parts
  (implies (fn-mm-tot-le a b)
           (and (<= (fn-mm-tot-records a) (fn-mm-tot-records b))
                (<= (fn-mm-tot-log a) (fn-mm-tot-log b))
                (<= (fn-mm-tot-history a) (fn-mm-tot-history b))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-tot-le) (fn-mm-tot-records fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge fn-mm-tot-arena
                                                   fn-mm-tot-hcharge fn-mm-tot-memberships
                                                   fn-mm-tot-events fn-mm-tot-paged-p)))))
(defthm fn-mm-maintenance-monotone
  (implies (fn-mm-tot-le a b) (<= (fn-mm-maintenance a cfg) (fn-mm-maintenance b cfg)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-maintenance)
                                  (fn-mm-hroot-demand fn-mm-tot-charge fn-heap-reclaim-demand-octets
                                   fn-mm-tot-le fn-mm-tot-records fn-mm-tot-log fn-mm-tot-history
                                   fn-mm-cfg-pub-trigger fn-mm-cfg-trigger fn-mm-cfg-reclaim-live-p))
           :use (fn-mm-tot-charge-monotone fn-mm-tot-le-parts
                 (:instance fn-heap-reclaim-demand-octets-monotone
                            (n1 (fn-mm-tot-records a)) (n2 (fn-mm-tot-records b))
                            (c1 (fn-mm-tot-charge a)) (c2 (fn-mm-tot-charge b)))
                 (:instance fn-mm-hroot-demand-monotone
                            (n1 (fn-mm-tot-records a)) (n2 (fn-mm-tot-records b))
                            (l1 (fn-mm-tot-history a)) (l2 (fn-mm-tot-history b)))))))
; KEYSTONE K2.  The sum grows with the store: a prefix of a store, or what
; a reclaim leaves of it, needs no more than the store.
(defthm fn-mm-sum-grows-with-the-store
  (implies (fn-mm-tot-le a b)
           (<= (fn-mm-sum profile img cfg a) (fn-mm-sum profile img cfg b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-sum) (fn-mm-owner fn-mm-maintenance fn-mm-tot-le fn-mm-base
                                                fn-mm-connection fn-mm-inflight))
           :use (fn-mm-owner-monotone fn-mm-maintenance-monotone))))
(defthm fn-mm-base-monotone-in-the-image
  (implies (fn-mm-img-le i1 i2) (<= (fn-mm-base i1 cfg) (fn-mm-base i2 cfg)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-base fn-mm-img-le)
                                  (fn-mm-img-file fn-mm-img-anon fn-mm-img-thread
                                   fn-mm-cfg-trigger fn-mm-cfg-connections))
           :use ((:instance fn-mm-times-monotone (a (fn-mm-img-thread i1)) (b (fn-mm-img-thread i2))
                            (c (fn-heap-thread-count (fn-mm-cfg-connections cfg))))))))
(defthm fn-mm-open-octets-monotone
  (implies (and (<= (nfix ou1) (nfix ou2)) (<= (nfix on1) (nfix on2)))
           (<= (fn-heap-store-open-octets profile ou1 on1) (fn-heap-store-open-octets profile ou2 on2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-store-open-octets) (fn-heap-open-chunk-bound))
           :use ((:instance fn-heap-open-chunk-bound-monotone (p1 profile) (p2 profile))))))
(defthm fn-mm-reopen-need-monotone
  (implies (and (fn-mm-tot-le a b) (fn-mm-img-le i1 i2))
           (<= (fn-mm-reopen-need profile i1 cfg a) (fn-mm-reopen-need profile i2 cfg b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-reopen-need)
                                  (fn-mm-base fn-mm-owner fn-mm-maintenance fn-heap-store-open-octets
                                   fn-mm-tot-le fn-mm-img-le fn-mm-tot-log fn-mm-tot-records))
           :use (fn-mm-owner-monotone fn-mm-maintenance-monotone fn-mm-tot-le-parts
                 (:instance fn-mm-base-monotone-in-the-image)
                 (:instance fn-mm-open-octets-monotone
                            (ou1 (fn-mm-tot-log a)) (ou2 (fn-mm-tot-log b))
                            (on1 (fn-mm-tot-records a)) (on2 (fn-mm-tot-records b)))))))
(defthm fn-mm-img-le-reflexive (fn-mm-img-le i i))
; KEYSTONE K3 (REOPEN ADMISSIBILITY).  ADM the totals the gate admitted;
; TOT the store at any crash; HDR and SUFFIX what the observer reads (the
; checkpoint header's totals and the log's past it, however long: a suffix
; past the fast path's K is a full replay, and LOG charges it).  An
; observation counting at least the store and at most what was admitted
; sizes a reopen that holds the store's and fits the limit, on the same or
; a lighter image.  O-OBSERVE (A's header field and log scan): the
; observation counts the durable records and only them.
(defthm fn-mm-admitted-store-reopens
  (implies (and (fn-mm-gate-p profile img cfg limit adm)
                (fn-mm-tot-le tot (fn-mm-observed-tot hdr suffix))
                (fn-mm-tot-le (fn-mm-observed-tot hdr suffix) adm)
                (fn-mm-img-le img2 img))
           (and (<= (fn-mm-reopen-need profile img2 cfg tot)
                    (fn-mm-reopen-need profile img2 cfg (fn-mm-observed-tot hdr suffix)))
                (natp limit)
                (<= (fn-mm-reopen-need profile img2 cfg (fn-mm-observed-tot hdr suffix))
                    limit)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-gate-p)
                                  (fn-mm-reopen-need fn-mm-tot-le fn-mm-img-le fn-mm-observed-tot fn-mm-sum))
           :use ((:instance fn-mm-reopen-need-monotone (i1 img2) (i2 img2)
                            (a tot) (b (fn-mm-observed-tot hdr suffix)))
                 (:instance fn-mm-reopen-need-monotone (i1 img2) (i2 img)
                            (a (fn-mm-observed-tot hdr suffix)) (b adm))
                 (:instance fn-mm-img-le-reflexive (i img2))))))
(defthm fn-mm-least-observation-type
  (or (null (fn-mm-least-observation obs)) (natp (fn-mm-least-observation obs)))
  :rule-classes :type-prescription)
(defthm fn-mm-least-observation-is-least
  (implies (and (member-equal x obs) (natp x))
           (<= (fn-mm-least-observation obs) x))
  :rule-classes nil)
(defthm fn-mm-resident-limit-within-each
  (and (implies (and (natp configured) (natp (fn-mm-resident-limit configured robs)))
                (<= (fn-mm-resident-limit configured robs) configured))
       (implies (and (natp (fn-mm-least-observation robs))
                     (natp (fn-mm-resident-limit configured robs)))
                (<= (fn-mm-resident-limit configured robs) (fn-mm-least-observation robs))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-mm-resident-limit))))
(defthm fn-mm-launch-dynamic-holds-the-core-and-the-limit
  (<= (+ (fn-heap-core-dynamic core) (nfix limit)) (fn-mm-launch-dynamic limit core nursery))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-mm-launch-dynamic)
           :use ((:instance fn-heap-with-nursery-covers-base
                            (base (+ (fn-heap-core-dynamic core) (nfix limit))))))))
; KEYSTONE K4.  A launch holds the observed store and its reopen within the
; resident limit, the limit within the configured figure and every
; resident observation, the reservation within every address-space
; observation, and a dynamic space holding the core's content and every
; heap within the limit.
(defthm fn-mm-launch-holds-the-store-and-the-reservation
  (let ((d (fn-mm-launch-decide profile img cfg configured resident-obs address-obs
                                core nursery obs))
        (r (fn-mm-least-observation resident-obs))
        (a (fn-mm-least-observation address-obs)))
    (implies (equal (car d) :launch)
             (and (natp (cadr d))
                  (<= (fn-mm-sum profile img cfg obs) (cadr d))
                  (<= (fn-mm-reopen-need profile img cfg obs) (cadr d))
                  (implies (natp configured) (<= (cadr d) configured))
                  (implies (natp r) (<= (cadr d) r))
                  (implies (natp a)
                           (<= (fn-mm-launch-reservation (cadr d) core nursery cfg profile) a))
                  (<= (+ (fn-heap-core-dynamic core) (cadr d)) (caddr d)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-launch-decide fn-mm-gate-p)
                                  (fn-mm-sum fn-mm-reopen-need fn-mm-launch-reservation
                                   fn-mm-launch-dynamic fn-mm-resident-limit fn-mm-least-observation))
           :use ((:instance fn-mm-resident-limit-within-each (robs resident-obs))
                 (:instance fn-mm-launch-dynamic-holds-the-core-and-the-limit
                            (limit (fn-mm-resident-limit configured resident-obs)))))))
; KEYSTONE K5.  The launch refuses only by the model: a resident limit the
; observed store passes the gate under, with a reservation within every
; address-space observation, launches (L-FRESH's mechanism: a
; reservation compared with a resident limit, retired).
(defthm fn-mm-launch-refuses-only-by-the-model
  (let ((limit (fn-mm-resident-limit configured resident-obs))
        (a (fn-mm-least-observation address-obs)))
    (implies (and (fn-mm-gate-p profile img cfg limit obs)
                  (or (not (natp a))
                      (<= (fn-mm-launch-reservation limit core nursery cfg profile) a)))
             (equal (car (fn-mm-launch-decide profile img cfg configured resident-obs
                                              address-obs core nursery obs))
                    :launch)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-launch-decide)
                                  (fn-mm-gate-p fn-mm-sum fn-mm-reopen-need fn-mm-launch-reservation
                                   fn-mm-launch-dynamic fn-mm-resident-limit fn-mm-least-observation))
           :use ((:instance (:definition fn-mm-gate-p)
                            (limit (fn-mm-resident-limit configured resident-obs)) (tot obs))))))

; -----------------------------------------------------------------------------
; THE INSTANCE QUOTA (contract v2's per-instance buffer quota, Builder A's
; config term; coordinator ruling 2026-10-09): M_connection in buffers of CAP
; octets, rounded up, so QUOTA buffers hold the connection's term and waste
; less than one buffer.  CAP is A's (the payload span size from the path).
(defun fn-mm-instance-quota (profile cfg cap)
  (declare (xargs :guard t))
  (if (posp cap)
      (floor (+ (fn-mm-connection profile cfg) (- cap 1)) cap)
    0))

(defthm fn-mm-ceiling-quotient
  (implies (and (natp c) (posp k))
           (and (natp (floor (+ c (- k 1)) k))
                (<= c (* k (floor (+ c (- k 1)) k)))
                (< (* k (floor (+ c (- k 1)) k)) (+ c k))))
  :rule-classes nil)

(defthm fn-mm-instance-quota-is-the-ceiling
  (implies (posp cap)
           (and (natp (fn-mm-instance-quota profile cfg cap))
                (<= (fn-mm-connection profile cfg) (* cap (fn-mm-instance-quota profile cfg cap)))
                (< (* cap (fn-mm-instance-quota profile cfg cap)) (+ (fn-mm-connection profile cfg) cap))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-mm-instance-quota) (theory 'minimal-theory))
           :use ((:instance fn-mm-terms-natp)
                 (:instance fn-mm-ceiling-quotient (c (fn-mm-connection profile cfg)) (k cap))))))

; Contract v2.1 (Builder A): a connection's home buffers, QFIXED buffers of
; CAPF octets, hold its fixed term; the pool's P buffers of CAPL octets hold
; the holders' large replies, one a holder when the reply fits CAPL.
(defun fn-mm-instance-qfixed (profile cfg capf)
  (declare (xargs :guard t))
  (if (posp capf)
      (floor (+ (fn-mm-connection-fixed profile cfg) (- capf 1)) capf)
    0))

(defthm fn-mm-instance-qfixed-is-the-ceiling
  (implies (posp capf)
           (and (natp (fn-mm-instance-qfixed profile cfg capf))
                (<= (fn-mm-connection-fixed profile cfg) (* capf (fn-mm-instance-qfixed profile cfg capf)))
                (< (* capf (fn-mm-instance-qfixed profile cfg capf))
                   (+ (fn-mm-connection-fixed profile cfg) capf))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-mm-instance-qfixed) (theory 'minimal-theory))
           :use ((:instance fn-mm-terms-natp)
                 (:instance fn-mm-ceiling-quotient (c (fn-mm-connection-fixed profile cfg)) (k capf))))))

; The pool's leases hold the large term when one lease holds a large reply.
(defthm fn-mm-large-pool-within-the-leases
  (implies (and (natp capl) (<= (fn-mm-large-reply profile cfg) capl))
           (<= (fn-mm-large-pool profile cfg) (* (fn-mm-cfg-holders cfg) capl)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-large-pool) (fn-mm-large-reply fn-mm-cfg-holders))
           :use ((:instance fn-mm-terms-natp)
                 (:instance fn-mm-times-monotone (a (fn-mm-large-reply profile cfg)) (b capl)
                            (c (fn-mm-cfg-holders cfg)))))))
