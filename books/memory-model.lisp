; fn: the process's memory as five terms against one configured figure
; (Builder M, landing 1, 2026-10-09; RUNTIME-MODEL section 6).
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
; memory.max) refuses a node the limit would hold (L-FRESH: refused at
; 256 MB with `heap=594 MB').  This book states the resident equation over
; the state the books hold: each term a function of the store's CHARGED
; TOTALS (what the checkpoint header carries, Builder A's field) and of the
; configuration, never of the profile's ceilings where a state exists.
;
; THE INPUTS, plain lists (no stobj: these are decisions, not state):
;
;   TOT   the charged totals (RECORDS PAYLOAD HCHARGE MEMBERSHIPS RESIDENCY):
;         RECORDS the committed records (fn-sbud-used), PAYLOAD the held
;         rows' payload octets, HCHARGE their header charges
;         (fn-sbud-held-heap-charge summed), MEMBERSHIPS the group
;         memberships, RESIDENCY :resident (payloads in the heap's arena,
;         today) or :paged (payloads on disk behind a bounded cache).
;         PAYLOAD + HCHARGE + 320 MEMBERSHIPS is fn-sbud-bytes-used.
;   IMG   the image's resident floor, MEASURED, never derived
;         (FILE ANON THREAD): the core's file-backed pages resident after
;         the open, the runtime's anonymous floor (GC tables, static space,
;         the card table), and one thread's resident areas (control stack
;         touched, TLS).  Assumption A-IMAGE-RESIDENT: the build measures
;         them on the image it ships and the manifest carries them.
;   CFG   the configuration (CONNECTIONS TLSP TRIGGER PUB-TRIGGER
;         RECLAIM-LIVE CACHE): the configured connection cap C, whether a
;         TLS context is loaded, the collector's trigger in service and
;         while a publication runs, the live-reclaim opt-in, and the paged
;         payload cache's octets (used only under :paged).
;
; THE COLLECTOR.  Assumption A-GC-FOOTPRINT: the dynamic space's resident
; pages are at most its live objects plus twice the trigger in force (the
; nursery and its copy), provided pages freed by a collection are returned
; before the next trigger's worth is allocated (MEM-003: SBCL returns them
; only after a collection of generation 2 or more; the host's idle
; collection).  The equation charges 2 x TRIGGER in M_base and the
; publication's raise of it in M_maintenance.

(in-package "ACL2")
(include-book "heap-reservation")
(include-book "connection-budget")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; Accessors.

(defun fn-mm-nat (i x)
  (declare (xargs :guard (natp i)))
  (nfix (nth i (true-list-fix x))))

(defun fn-mm-tot-records (tot) (declare (xargs :guard t)) (fn-mm-nat 0 tot))
(defun fn-mm-tot-payload (tot) (declare (xargs :guard t)) (fn-mm-nat 1 tot))
(defun fn-mm-tot-hcharge (tot) (declare (xargs :guard t)) (fn-mm-nat 2 tot))
(defun fn-mm-tot-memberships (tot) (declare (xargs :guard t)) (fn-mm-nat 3 tot))
(defun fn-mm-tot-paged-p (tot)
  (declare (xargs :guard t))
  (equal (nth 4 (true-list-fix tot)) :paged))

; The history the budget charges: fn-sbud-bytes-used's three parts.
(defun fn-mm-tot-charge (tot)
  (declare (xargs :guard t))
  (+ (fn-mm-tot-payload tot) (fn-mm-tot-hcharge tot)
     (* *fn-sbud-membership-octets* (fn-mm-tot-memberships tot))))

(defun fn-mm-make-tot (records payload hcharge memberships residency)
  (declare (xargs :guard t))
  (list (nfix records) (nfix payload) (nfix hcharge) (nfix memberships)
        (if (equal residency :paged) :paged :resident)))

; Componentwise order, residency equal: a store that is a prefix of
; another, or what a reclaim leaves of it.
(defun fn-mm-tot-le (a b)
  (declare (xargs :guard t))
  (and (<= (fn-mm-tot-records a) (fn-mm-tot-records b))
       (<= (fn-mm-tot-payload a) (fn-mm-tot-payload b))
       (<= (fn-mm-tot-hcharge a) (fn-mm-tot-hcharge b))
       (<= (fn-mm-tot-memberships a) (fn-mm-tot-memberships b))
       (equal (fn-mm-tot-paged-p a) (fn-mm-tot-paged-p b))))

; One record's charges: REC = (PAYLOAD HCHARGE GROUPS).
(defun fn-mm-tot-add (tot rec)
  (declare (xargs :guard t))
  (fn-mm-make-tot (+ 1 (fn-mm-tot-records tot))
                  (+ (fn-mm-tot-payload tot) (fn-mm-nat 0 rec))
                  (+ (fn-mm-tot-hcharge tot) (fn-mm-nat 1 rec))
                  (+ (fn-mm-tot-memberships tot) (fn-mm-nat 2 rec))
                  (if (fn-mm-tot-paged-p tot) :paged :resident)))

(defun fn-mm-img-file (img) (declare (xargs :guard t)) (fn-mm-nat 0 img))
(defun fn-mm-img-anon (img) (declare (xargs :guard t)) (fn-mm-nat 1 img))
(defun fn-mm-img-thread (img) (declare (xargs :guard t)) (fn-mm-nat 2 img))

(defun fn-mm-cfg-connections (cfg) (declare (xargs :guard t)) (fn-mm-nat 0 cfg))
(defun fn-mm-cfg-tlsp (cfg) (declare (xargs :guard t)) (and (nth 1 (true-list-fix cfg)) t))
(defun fn-mm-cfg-trigger (cfg) (declare (xargs :guard t)) (fn-mm-nat 2 cfg))
(defun fn-mm-cfg-pub-trigger (cfg)
  (declare (xargs :guard t))
  (max (fn-mm-nat 3 cfg) (fn-mm-cfg-trigger cfg)))
(defun fn-mm-cfg-reclaim-live-p (cfg) (declare (xargs :guard t)) (and (nth 4 (true-list-fix cfg)) t))
(defun fn-mm-cfg-cache (cfg) (declare (xargs :guard t)) (fn-mm-nat 5 cfg))

; -----------------------------------------------------------------------------
; M_configured.  The small preset's is ruling 16's bar: 131,072 KiB.  The
; other presets carry none until ember decides (DECISION in the READY);
; NIL means the operator's configured figure alone.

(defconst *fn-mm-preset-configured*
  '((:small . 134217728)))

(defun fn-mm-preset-configured-octets (preset)
  (declare (xargs :guard t))
  (let ((row (assoc-equal preset *fn-mm-preset-configured*)))
    (and (consp row) (cdr row))))

; The resident limit a decision is held to: the configured figure, and every
; RESIDENT observation of the machine (physical memory less the OS reserve,
; a cgroup's memory.max up the hierarchy).  Address-space limits
; (RLIMIT_AS, RLIMIT_DATA) are NOT resident observations; they bound the
; reservation only (fn-mm-launch-decide).
(defun fn-mm-resident-limit (configured resident-observations)
  (declare (xargs :guard t))
  (let ((m (fn-heap-machine-octets resident-observations)))
    (cond ((not (posp configured)) m)
          ((zp m) configured)
          (t (min configured m)))))

; -----------------------------------------------------------------------------
; THE FIVE TERMS.

; M_base: the image's resident floor, every thread the node runs (connections
; cost no thread: host/native/mux.lisp; fn-heap-thread-count), and the
; collector's room at the service trigger.
(defun fn-mm-base (img cfg)
  (declare (xargs :guard t))
  (+ (fn-mm-img-file img) (fn-mm-img-anon img)
     (* (fn-heap-thread-count (fn-mm-cfg-connections cfg)) (fn-mm-img-thread img))
     (* 2 (fn-mm-cfg-trigger cfg))))

; The history root over the store's totals (the P3 root's page image:
; books/heap-store-figure.lisp fn-heap-hroot-npages and -demand-bound at the
; profile's bounds; here at the store's RECORDS and charged octets C).
(defun fn-mm-hroot-npages (n c)
  (declare (xargs :guard t))
  (+ 1 (* 4 (ceiling (nfix n) 2048)) (ceiling (nfix c) 16384)))

(defun fn-mm-hroot-demand (n c)
  (declare (xargs :guard t))
  (let ((img (fn-heap-hroot-image-octets (fn-mm-hroot-npages n c))))
    (+ (* 2 (+ img (* 8 (nfix n)) 4096))
       (* 64 (+ 1 (nfix n)))
       img)))

; The payloads: in the arena (:resident), or the empty arena and the
; configured cache (:paged).
(defun fn-mm-payload-octets (tot cfg)
  (declare (xargs :guard t))
  (if (fn-mm-tot-paged-p tot)
      (+ (fn-heap-arena-octets 0) (fn-mm-cfg-cache cfg))
    (fn-heap-arena-octets (fn-mm-tot-payload tot))))

; M_owner: the held rows (handles, each record's fixed part twice for the
; collector), the header columns at 8 heap octets a CHARGED HEADER octet
; (fn-heap-record-charge-covers-the-state; the payload's octets are the
; arena's, not charged again), the memberships twice, the payloads, and the
; retained history root.
(defun fn-mm-owner (tot cfg)
  (declare (xargs :guard t))
  (let ((n (fn-mm-tot-records tot)))
    (+ (fn-mm-payload-octets tot cfg)
       (* *fn-heap-handle-octets* n)
       (* 2 n *fn-heap-record-octets*)
       (* *fn-heap-charge-heap-octets* (fn-mm-tot-hcharge tot))
       (* 2 *fn-heap-membership-octets* (fn-mm-tot-memberships tot))
       (fn-mm-hroot-demand n (fn-mm-tot-charge tot)))))

; M_connection: one connection's heap and native parts as the served host
; holds them (books/connection-budget.lisp fn-cbud-conn-octets: record,
; reads, the stated workload's reply, the command line, COMPRESS, kernel
; buffers, TLS).
(defun fn-mm-connection (profile cfg)
  (declare (xargs :guard t))
  (fn-cbud-conn-octets (fn-bs-profile-max-article-octets profile)
                       (fn-mm-cfg-tlsp cfg)))

; M_inflight: the request the owner serves (record and header lists, the
; taken submission, both octet buffers) and the articles in flight, the
; slots' pool (books/heap-store-figure.lisp).
(defun fn-mm-inflight (profile)
  (declare (xargs :guard t))
  (+ (fn-heap-store-inflight-octets profile)
     (fn-heap-articles-octets profile)))

; M_maintenance: the history root's candidate generation during a
; publication, the collector's raise while it runs, and, opted in, a live
; reclaim's second generation over the store's shape.
(defun fn-mm-maintenance (tot cfg)
  (declare (xargs :guard t))
  (let ((n (fn-mm-tot-records tot)) (c (fn-mm-tot-charge tot)))
    (+ (fn-mm-hroot-demand n c)
       (* 2 (- (fn-mm-cfg-pub-trigger cfg) (fn-mm-cfg-trigger cfg)))
       (if (fn-mm-cfg-reclaim-live-p cfg) (fn-heap-reclaim-demand-octets n c) 0))))

; THE SUM.
(defun fn-mm-sum (profile img cfg tot)
  (declare (xargs :guard t))
  (+ (fn-mm-base img cfg)
     (fn-mm-owner tot cfg)
     (* (fn-mm-cfg-connections cfg) (fn-mm-connection profile cfg))
     (fn-mm-inflight profile)
     (fn-mm-maintenance tot cfg)))

; -----------------------------------------------------------------------------
; THE INSTANT: what the process holds at one moment, K connections open, S
; article slots in use, PUBLISHING whether a publication runs.  The sum is
; this at its bounds.
(defun fn-mm-need (profile img cfg tot k s publishing)
  (declare (xargs :guard t))
  (+ (fn-mm-base img cfg)
     (fn-mm-owner tot cfg)
     (* (nfix k) (fn-mm-connection profile cfg))
     (fn-heap-store-inflight-octets profile)
     (* (nfix s) (fn-heap-article-reserve-octets profile))
     (if publishing (fn-mm-maintenance tot cfg) 0)))

; -----------------------------------------------------------------------------
; REOPEN.  Its named terms over the totals the open will hold:
;   the uncheckpointed tail: at most K = max-open-suffix records past the
;     checkpoint, each at most the profile's article, header charge
;     (8 HDR + 12 x 250) and G memberships;
;   the directory and index metadata: the owner's own (the history root
;     built once, the keyed Message-ID table in each record's fixed part);
;   the recovery workspace: the open's transient over the history it reads
;     (fn-heap-store-open-octets: one chunk and one entry as lists, the
;     suffix's vectors, the per-record build);
;   dirty pages and the first publication after recovery: the maintenance
;     term;
;   reader pins: none at reopen (no connection is accepted before the open
;     ends), and every pin after it is a connection's (M_connection);
;   failure-reporting headroom: one refusal rendered and logged.

(defun fn-mm-worst-record (profile)
  (declare (xargs :guard t))
  (list (nfix (fn-bs-profile-max-article-octets profile))
        (+ (* *fn-sbud-header-weight*
              (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile)))
           (* *fn-sbud-msgid-weight* *fn-heap-message-id-octets*))
        (nfix (fn-bs-profile-max-groups-per-article profile))))

(defun fn-mm-tot-add-n (tot rec k)
  (declare (xargs :guard (natp k) :measure (nfix k)))
  (if (zp k) tot (fn-mm-tot-add-n (fn-mm-tot-add tot rec) rec (- k 1))))

(defun fn-mm-tail-tot (profile tot)
  (declare (xargs :guard t))
  (fn-mm-tot-add-n tot (fn-mm-worst-record profile)
                   (nfix (fn-bs-profile-max-open-suffix profile))))

(defconst *fn-mm-failure-headroom-octets*
  (* 2 *fn-heap-list-octets-per-octet* *fn-cbud-reply-status-octets*))

; The reopen's need over the totals the open holds.
(defun fn-mm-reopen-need (profile img cfg tot)
  (declare (xargs :guard t))
  (+ (fn-mm-base img cfg)
     (fn-mm-owner tot cfg)
     (fn-heap-store-open-octets profile (fn-mm-tot-charge tot) (fn-mm-tot-records tot))
     (fn-mm-maintenance tot cfg)
     *fn-mm-failure-headroom-octets*))

; The reopen's reservation sized from a checkpoint header's totals HDR: the
; header's store with a full uncheckpointed tail.
(defun fn-mm-reopen-sizing (profile img cfg hdr)
  (declare (xargs :guard t))
  (fn-mm-reopen-need profile img cfg (fn-mm-tail-tot profile hdr)))

; -----------------------------------------------------------------------------
; THE GATE: a store's totals are admissible under L when the process serving
; it fits and its reopen, sized from any checkpoint of it, fits.
(defun fn-mm-gate-p (profile img cfg limit tot)
  (declare (xargs :guard t))
  (and (<= (fn-mm-sum profile img cfg tot) (nfix limit))
       (<= (fn-mm-reopen-sizing profile img cfg tot) (nfix limit))))

; A commit of REC: admitted exactly when the totals after it pass the gate.
(defun fn-mm-admit-record (profile img cfg limit tot rec)
  (declare (xargs :guard t))
  (if (fn-mm-gate-p profile img cfg limit (fn-mm-tot-add tot rec))
      (list :admitted (fn-mm-tot-add tot rec))
    (list :refused :memory-model tot)))

; -----------------------------------------------------------------------------
; THE LAUNCH: resident against resident limits, reservation against
; address-space limits, never crossed.  The dynamic space is the resident
; limit's (every heap object is resident, so a heap within the gate's sum
; is within it), not the profile's ceiling.
(defun fn-mm-launch-dynamic (limit nursery)
  (declare (xargs :guard t))
  (fn-heap-with-nursery (nfix limit) nursery))

(defun fn-mm-launch-reservation (limit nursery core cfg profile)
  (declare (xargs :guard t))
  (fn-heap-reservation-octets (fn-heap-mb-of (fn-mm-launch-dynamic limit nursery))
                              core (fn-heap-stack-kib profile)
                              (fn-heap-thread-count (fn-mm-cfg-connections cfg))))

; Answers (:launch LIMIT DYNAMIC) or (:refused REASON NEED LIMIT).
(defun fn-mm-launch-decide (profile img cfg configured resident-obs address-obs
                                    core nursery hdr)
  (declare (xargs :guard t))
  (let* ((limit (fn-mm-resident-limit configured resident-obs))
         (addr (fn-heap-machine-octets address-obs))
         (res (fn-mm-launch-reservation limit nursery core cfg profile)))
    (cond ((zp limit) (list :refused :memory-unconfigured 0 0))
          ((not (fn-mm-gate-p profile img cfg limit hdr))
           (list :refused :configured-memory-cannot-hold-the-store
                 (max (fn-mm-sum profile img cfg hdr)
                      (fn-mm-reopen-sizing profile img cfg hdr))
                 limit))
          ((and (posp addr) (< addr res))
           (list :refused :address-space-cannot-hold-the-reservation res addr))
          (t (list :launch limit (fn-mm-launch-dynamic limit nursery))))))
