;; fn: a command's reservation states what the command holds (Builder M,
; landing 2, the observation form; RUNTIME-MODEL section 4).
;
; Every native action the operator surface names
; (books/native-operator.lisp fn-native-operator-result-native-action;
; tests/test_heap_action_growth.py checks each has a row) is one of:
;   :serves      `run': the owner, launched at the run's resident LIMIT
;                (fn-mo-serve-decide below, L-RUN-LAUNCH; the memory gate
;                keeps every store the run grows within it);
;   :grows       the offline commands that write records or rewrite the
;                store, and `account-hash', which reads a credential file
;                the profile sizes: the profile's bounds, today's figure;
;   :lists       the offline list verbs (*fn-heap-list-actions*);
;   :reads       the read-only commands that OPEN the store (`status
;                --replay', and `pins', `obligations' and the control and
;                moderation reports, which share the native action :status
;                and render over the replayed store; `inspect',
;                `inspect-group'): the reopen of the totals they observe,
;                today's figure while the totals are unobserved;
;   :header      `status' without `--replay' and `health' with no owner: the
;                checkpoint header, config.json and lstat, nothing replayed
;                (host/native/io.lisp fnn-stopped-report), and the
;                configuration history the profile is loaded with
;                (fnn-load-config's overlay, the live limits);
;   :store-less  commands that hold no store: `init' (its staged empty
;                store, fn-heap-storeless-figure-holds-the-empty-open),
;                `operation' (offline: no replay), `export-status' (asks
;                the owner), and the commands that name no store.
; The table is lane b-heap-growth's (60912084e) less its read profile,
; which Codex showed sizes nothing (physical octets bound neither expanded
; records nor memberships).
(in-package "ACL2")
(include-book "memory-model")
(include-book "admission-memory")

(defconst *fn-heap-action-growth*
  '((:run . :serves)
    (:post . :grows) (:admin . :grows) (:moderate . :grows) (:retire . :grows)
    (:peering . :grows) (:principal . :grows) (:keys . :grows) (:carry . :grows)
    (:tls . :grows) (:account-invite . :grows) (:import . :grows)
    (:checkpoint . :grows) (:reclaim-dry-run . :grows) (:reclaim-recorded . :grows)
    (:export . :grows) (:bless-snapshot . :grows) (:rebind-filesystem . :grows)
    (:account-hash . :grows)
    (:recover . :lists) (:compact . :lists) (:reclaim . :lists)
    (:status . :reads) (:inspect . :reads) (:inspect-group . :reads)
    (:health . :header)
    (:operation . :store-less) (:export-status . :store-less)
    (:init . :store-less) (:help . :store-less) (:show . :store-less)
    (:mission . :store-less) (:tls-self-signed . :store-less)
    (:owner-required . :store-less) (:none . :store-less)))

(defun fn-heap-action-growth (action)
  (declare (xargs :guard t))
  (let ((row (assoc-equal action *fn-heap-action-growth*)))
    (if (consp row) (cdr row) :grows)))

; The table's list rows are exactly the list verbs.
(defthm fn-heap-action-growth-lists-are-the-list-actions
  (iff (equal (fn-heap-action-growth action) :lists)
       (member-equal action *fn-heap-list-actions*)))

; The class of a command: the table's, except that the operator's `status'
; word without `--replay' (COMMAND "status"; `pins', `obligations' and the
; reports share the action :status and replay) reads the header.
(defun fn-heap-command-growth (action command replayp)
  (declare (xargs :guard t))
  (if (and (equal action :status) (equal command "status") (not replayp))
      :header
    (fn-heap-action-growth action)))

; -----------------------------------------------------------------------------
; THE OBSERVATION.  The checkpoint header's charged totals HDR and the log
; suffix's SUFFIX (books/charged-totals.lisp; A's landing-2 checkpoint
; writes HDR, A's suffix scan yields SUFFIX over the durable prefix).  The
; schema-3 header (books/store-tree-codec.lisp, 37 octets) carries none of
; the nine but RECORDS of the checkpointed prefix, so until A's field the
; host passes NIL and the observation is NIL.
;
; EXTENT is the log's physical length the probe observes (the largest
; journal segment's lstat size; Builder A's fnn-log-observed-extent), NIL
; when unobserved.  The open's reader allocates an entry's declared length
; before the step validates it (host/native/io.lisp fnn-log-stream-segment,
; books/store-log-entry-bound.lisp fn-lgw-entry-len-bounded), and that
; length is capped by the extent past the reader's position
; (books/store-log-stream.lisp fn-lgw-entry-len) and by the kind's open bound,
; which for a batch (kind 2) is the frame's payload limit: a damaged or padded
; file longer than its records' LOG is read in full.  So the observation's LOG is
; at least EXTENT, and the read's open terms over LOG charge the entry
; scratch (KEYSTONE fn-mo-observed-log-holds-every-entry-read).  An
; unobserved extent leaves the totals unseen (the offline adapter).
(defun fn-mo-tot-log-at-least (tot extent)
  (declare (xargs :guard t))
  (fn-mm-make-tot (fn-mm-tot-records tot) (fn-mm-tot-arena tot) (fn-mm-tot-hcharge tot)
                  (fn-mm-tot-memberships tot) (fn-mm-tot-events tot)
                  (max (fn-mm-tot-log tot) (nfix extent))
                  (fn-mm-tot-history tot) (fn-mm-tot-charge tot)
                  (if (fn-mm-tot-paged-p tot) :paged :resident)))

(defun fn-mo-observed-totals (hdr suffix extent)
  (declare (xargs :guard t))
  (if (and (fn-mm-tot-p hdr) (fn-mm-tot-p suffix) (natp extent))
      (fn-mo-tot-log-at-least (fn-mm-observed-tot hdr suffix) extent)
    nil))

; A read-only command serves nothing: no connection, no TLS, no handshake,
; no cold-read pool, no cache, no reclaim, the collector at the nursery; it
; holds the store's configuration, CONFIG-OCTETS of it (the owner's
; fn-mm-config-heap, and the checkpoint's configuration fold).
(defun fn-mo-read-cfg (nursery config-octets)
  (declare (xargs :guard t))
  (list 0 nil (nfix nursery) (nfix nursery) nil 0 0 0 nil 0 nil nil (nfix config-octets)))

; IMG observed by the probe: (FILE ANON THREAD), each natural.
(defun fn-mm-img-p (img)
  (declare (xargs :guard t))
  (and (true-listp img) (equal (len img) 3)
       (natp (nth 0 img)) (natp (nth 1 img)) (natp (nth 2 img))))

;; THE CONFIGURATION HISTORY.  Loading a store's profile reads every record
;; of its configuration history (host/native/io.lisp fnn-load-config-overlay:
;; each record's octets as a vector and then a list, decoded into the live
;; limits) -- a profile-sized input (Codex, landing-2 review F2: the history's
;; allowance admits a million records).  It is charged from the octets the
;; probe observes in config/ (the lstat sizes), at
;; books/memory-model.lisp fn-mm-config-heap (the same term the run's owner
;; charges over its CFG's configuration octets; a read's CFG carries none, so
;; it is charged once).

(defun fn-mo-config-heap (config-octets)
  (declare (xargs :guard t))
  (fn-mm-config-heap config-octets))

;; THE COLLECTOR'S CARD TABLE.  SBCL's generational collector marks one
;; octet a card of dynamic space and touches the whole table at start
;; (runtime/coreparse.c; Codex F4), outside the dynamic space, so a decision
;; that picks the dynamic space charges it resident, rounded to a power of
;; two cards as the runtime rounds it.  CARD is the image's
;; card size (sb-vm:gencgc-card-bytes), observed by the probe.
(defun fn-mo-card-octets (dynamic card)
  (declare (xargs :guard t))
  (if (posp card)
      ;; the runtime rounds the table to a power of two cards (Codex,
      ;; landing-2 re-check F2)
      (adt-pow2-at-least (floor (+ (nfix dynamic) (- card 1)) card) 1)
    0))

;; THE STORE-OPENING COMMANDS (:reads, :grows, :lists).  Each is decided by
;; the memory equation over TOT, the store's charged totals, when the probe
;; observes them (fn-mo-observed-totals).  Until it does (the schema-3
;; checkpoint header carries none of them, until Builder A's charged-totals
;; field), it is decided by THE OFFLINE ADAPTER below.  None serves: no
;; connection, TLS, handshake, cold-read pool, cache or reclaim, the
;; collector at the nursery (fn-mo-read-cfg).
;;   NEED: a read is held to the reopen of TOT (fn-mm-reopen-need: the
;;     image, the owner's state, the open's workspace over the log, the
;;     checkpoint load, maintenance, failure headroom); a writer and a list
;;     verb to the gate's both arms, the sum (the request and articles in
;;     flight) and the reopen; every one to the configuration history its
;;     open loads; a list verb (`recover', `store compact', `store reclaim')
;;     to its measured list copies of the log it walks
;;     (books/heap-figure.lisp fn-heap-operation-history-copies: 2, 6 for
;;     compaction and reclaim, at 16 heap octets an octet, twice for the
;;     collector), with the record and its header copies in flight.
;;   The heap holds the core's dynamic content and NEED with the collector's
;; room; NEED and the dynamic space's card table are held to the least
;; RESIDENT observation (physical memory, memory.max), the reservation (heap,
;; core file, the threads' stacks) to the least ADDRESS-SPACE one (RLIMIT_AS,
;; RLIMIT_DATA) only.  The answer is in the reservation's shape: (:heap MB
;; WORD LIMIT-MB STACK-KIB THREADS), or a refusal by name with its figures in
;; MB.
(defun fn-mo-store-opening-p (class)
  (declare (xargs :guard t))
  (and (member-equal class '(:reads :grows :lists)) t))

(defun fn-mo-list-octets (action profile tot)
  (declare (xargs :guard t))
  (if (member-equal action *fn-heap-list-actions*)
      (* 2 *fn-heap-octets-per-list-octet*
         (+ (* (fn-heap-operation-history-copies action) (fn-mm-tot-log tot))
            (nfix (fn-bs-profile-max-record-octets profile))
            (* *fn-heap-header-copies*
               (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile)))))
    0))

(defun fn-mo-read-need (action class profile img nursery tot config-octets)
  (declare (xargs :guard t))
  (let ((cfg (fn-mo-read-cfg nursery config-octets)))
    (+ (if (equal class :reads)
           (fn-mm-reopen-need profile img cfg tot)
         (max (fn-mm-sum profile img cfg tot) (fn-mm-reopen-need profile img cfg tot)))
       (fn-mo-list-octets action profile tot))))

(defun fn-mo-read-dynamic (action class profile img core nursery tot config-octets)
  (declare (xargs :guard t))
  (fn-heap-with-nursery (+ (fn-heap-core-dynamic core)
                           (fn-mo-read-need action class profile img nursery tot config-octets))
                        nursery))

(defun fn-mo-read-resident (action class profile img core nursery tot config-octets card)
  (declare (xargs :guard t))
  (+ (fn-mo-read-need action class profile img nursery tot config-octets)
     (fn-mo-card-octets (* *fn-heap-mib*
                           (fn-heap-mb-of (fn-mo-read-dynamic action class profile img core nursery tot
                                                              config-octets)))
                        card)))

(defun fn-mo-read-reservation (action class profile img core nursery tot config-octets)
  (declare (xargs :guard t))
  (fn-heap-reservation-octets (fn-heap-mb-of (fn-mo-read-dynamic action class profile img core nursery
                                                                 tot config-octets))
                              core (fn-heap-stack-kib profile) (fn-heap-thread-count 0)))

(defun fn-mo-read-decide (action class profile img core nursery tot config-octets card resident
                                 address)
  (declare (xargs :guard t))
  (let ((need (fn-mo-read-resident action class profile img core nursery tot config-octets card))
        (limit (fn-mm-least-observation resident))
        (a (fn-mm-least-observation address))
        (res (fn-mo-read-reservation action class profile img core nursery tot config-octets)))
    (cond ((not (natp limit)) (list :refused :machine-memory-unobserved 0 0))
          ((< limit need)
           (list :refused :machine-cannot-hold-the-store (fn-heap-mb-of need)
                 (floor limit *fn-heap-mib*)))
          ((and (natp a) (< a res))
           (list :refused :address-space-cannot-hold-the-reservation (fn-heap-mb-of res)
                 (floor a *fn-heap-mib*)))
          (t (list :heap (fn-heap-mb-of (fn-mo-read-dynamic action class profile img core nursery tot
                                                            config-octets))
                   (fn-heap-profile-word profile) (floor limit *fn-heap-mib*)
                   (fn-heap-stack-kib profile) (fn-heap-thread-count 0))))))

;; THE HEADER.  `status' and `health' of a stopped store open nothing: they
;; are init's store-less figure (the image's dynamic content and the
;; collector's room, one empty open), with its heap raised by the
;; configuration history the profile is loaded with, and the whole
;; reservation checked against the machine as init's is.
(defun fn-mo-header-of (init core observations config-octets)
  (declare (xargs :guard t))
  (let ((d (true-list-fix init)))
    (if (not (equal (car d) :heap))
        d
      (let* ((mb (+ (fn-heap-decision-mb d) (fn-heap-mb-of (fn-mo-config-heap config-octets))))
             (total (fn-heap-reservation-octets mb core (nth 4 d) (nth 5 d))))
        (if (<= total (fn-heap-machine-octets observations))
            (list :heap mb (nth 2 d) (nth 3 d) (nth 4 d) (nth 5 d))
          (list :refused :machine-cannot-hold-threads (fn-heap-mb-of total) (nth 3 d)))))))

(defun fn-mo-header-decide (profile core nursery observations connections config-octets)
  (declare (xargs :guard t))
  (fn-mo-header-of (fn-heap-reserve-operation-decide :init profile core nursery observations
                                                     connections nil)
                   core observations config-octets))


;; IMG as the probe observes it (O-BASE's measurement at the start of the
;; command, before any store is open): FILE the core file's octets (every
;; page of it may become resident), ANON the probe's own RssAnon from
;; /proc/self/status (the image's anonymous floor), THREAD one thread's
;; control stack and thread-local storage (its resident pages are within
;; them).  NIL when /proc/self/status does not report RssAnon.
(defun fn-mo-digits (octets acc)
  (declare (xargs :guard (natp acc)))
  (if (and (consp octets) (natp (car octets)) (<= 48 (car octets)) (<= (car octets) 57))
      (fn-mo-digits (cdr octets) (+ (* 10 acc) (- (car octets) 48)))
    acc))

(defun fn-mo-skip-blanks (octets)
  (declare (xargs :guard t))
  (if (and (consp octets) (member-equal (car octets) '(32 9)))
      (fn-mo-skip-blanks (cdr octets))
    octets))

(defun fn-mo-prefixp (key octets)
  (declare (xargs :guard t))
  (if (consp key)
      (and (consp octets) (equal (car key) (car octets)) (fn-mo-prefixp (cdr key) (cdr octets)))
    t))

(defun fn-mo-drop-key (key octets)
  (declare (xargs :guard t))
  (if (and (consp key) (consp octets))
      (fn-mo-drop-key (cdr key) (cdr octets))
    octets))

(defun fn-mo-after-line (octets)
  (declare (xargs :guard t))
  (cond ((atom octets) nil)
        ((equal (car octets) 10) (cdr octets))
        (t (fn-mo-after-line (cdr octets)))))

; The kB figure of the line KEY begins in the /proc status text OCTETS, in
; octets; NIL when no line begins with KEY followed by a number.
(defun fn-mo-status-kib-octets (key octets)
  (declare (xargs :guard t :measure (len octets)))
  (cond ((atom octets) nil)
        ((fn-mo-prefixp key octets)
         (let ((rest (fn-mo-skip-blanks (fn-mo-drop-key key octets))))
           (if (and (consp rest) (natp (car rest)) (<= 48 (car rest)) (<= (car rest) 57))
               (* 1024 (fn-mo-digits rest 0))
             nil)))
        (t (let ((next (fn-mo-after-line octets)))
             (if (< (len next) (len octets))
                 (fn-mo-status-kib-octets key next)
               nil)))))

(defconst *fn-mo-rss-anon-key* '(82 115 115 65 110 111 110 58)) ; "RssAnon:"

; The entry's kinds (lane entry-guards): CORE-OCTETS the core file's length,
; a natural (fnn-heap-core-octets: 0 when unread); STATUS-OCTETS
; /proc/self/status's octets, NIL off Linux or unread (fnn-heap-read-small);
; TLS-OCTETS a count, NIL when the runtime cannot report it (exempt in
; host/interfaces.lisp: the body tests natp and observes no image).
(defun fn-mo-img-observed (core-octets status-octets stack-kib tls-octets)
  (declare (xargs :guard (and (natp core-octets) (fn-cbor-octet-listp status-octets))))
  (let ((anon (fn-mo-status-kib-octets *fn-mo-rss-anon-key* status-octets)))
    (if (and (natp core-octets) (natp anon) (natp tls-octets))
        (list core-octets anon (+ (* 1024 (nfix stack-kib)) tls-octets))
      nil)))


; -----------------------------------------------------------------------------
; THE DECISION the host's probe makes for every command (host/native/
; heap.lisp fnn-heap-reservation).  RESIDENT and ADDRESS are the
; observations the model compares resident memory and the reservation with
; (physical memory and memory.max; RLIMIT_DATA and RLIMIT_AS); OBSERVATIONS
; all of them, as today's decision takes them; CONFIG-OCTETS the
; configuration history's observed octets, CARD the collector's card size
; (each NIL when unobserved: today's decision, named).
; What a store-opening decision by the equation reads: the store's charged
; totals, the image (its resident floor is M_base), the configuration
; history's octets and the card size.
(defun fn-mo-read-observed-p (totals img config-octets card)
  (declare (xargs :guard t))
  (and (fn-mm-tot-p totals) (fn-mm-img-p img) (natp config-octets) (posp card)))

;; THE OFFLINE ADAPTER (coordinator ruling, 2026-10-09, superseding ruling
;; (a); owner M; retirement: A's charged-totals header).  A store-opening
;; command whose observations the equation lacks is sized by the figure it
;; had before H charged a held row its payload alone: books/heap-reservation.lisp
;; fn-heap-reserve-operation-decide over books/heap-store-figure.lisp's state
;; term, which charges the history at 2 H and no membership.  It UNDER-BOUNDS
;; a store the profile admits.  The bound is the equation at the profile's
;; bound (books/memory-model.lisp fn-mm-profile-bound-tot: T x G memberships,
;; 20 x H header charge, the log at T x ALLOWANCE + H, the history at
;; T x ALLOWANCE + 3 H, ALLOWANCE = fn-adm-row-allowance).  PROVED to hold every
;; store whose rows are each within (books/admission-memory.lisp
;; fn-mm-profile-bound-holds-every-admitted-store); the producer facts that
;; every row the node holds is within are still owed.  The figures below are the
;; equation at H with the history at H and the log at T x (78 + 1,083 + 261 G)
;; + H, BEFORE the history's 3 H and the allowance's numbered-row term (the
;; bound is now larger); on fn-core's image (reads and writers; the adapter in
;; brackets): small 2,427 MB (575), filled 26,684 MB (7,392), development
;; 52,400 MB (2,377), scale 1.6 TB (20 GB).  Its line says so.
(defun fn-mo-offline-adapter-decide (action profile core nursery observations connections observed)
  (declare (xargs :guard t))
  (fn-heap-reserve-operation-decide action profile core nursery observations connections observed))

; The run's launch (ruling (b)): the model's launch decided at C', the most
; connections at which the gate holds at the resident limit over TOT
; (fn-adm-capacity), never at the configured C.  The accepted decision is
; read's shape (:heap MB PROFILE-WORD LIMIT-MB STACK-KIB THREADS) with the
; threads of C'; a refusal is read's shape (:refused WORD NEED-MB LIMIT-MB),
; in the words fn-mo-read-refusal-line and fn-heap-reserve-report-line print.
(defun fn-mo-run-refusal (d need)
  (declare (xargs :guard t))
  (let ((d (true-list-fix d)))
    (cond ((equal (nth 1 d) :address-space-cannot-hold-the-reservation)
           (list :refused :address-space-cannot-hold-the-reservation
                 (fn-heap-mb-of (nth 2 d)) (floor (nfix (nth 3 d)) *fn-heap-mib*)))
          ((equal (car d) :refused)
           (if (equal (nth 1 d) :memory-unbounded)
               (list :refused :machine-memory-unobserved 0 0)
             (list :refused :machine-cannot-hold-the-store
                   (fn-heap-mb-of (nth 2 d)) (floor (nfix (nth 3 d)) *fn-heap-mib*))))
          (t (list :refused :machine-cannot-hold-the-store
                   (fn-heap-mb-of need) (floor (nfix (nth 1 d)) *fn-heap-mib*))))))

(defun fn-mo-run-decide (profile img cfg configured resident address core nursery tot)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((limit (fn-mm-resident-limit configured resident))
         (cap (fn-adm-capacity profile img cfg limit tot))
         (d (fn-mm-launch-decide profile img (fn-adm-cfg-at cfg (nfix cap)) configured resident
                                 address core nursery tot)))
    (if (and (equal (car d) :launch) (posp cap))
        (list :heap (fn-heap-mb-of (caddr d)) (fn-heap-profile-word profile)
              (floor (cadr d) *fn-heap-mib*) (fn-heap-stack-kib profile)
              (fn-heap-thread-count cap))
      (fn-mo-run-refusal
       d
       (let ((one (fn-adm-cfg-at cfg (min 1 (fn-mm-cfg-connections cfg)))))
         (max (fn-mm-sum profile img one tot) (fn-mm-reopen-need profile img one tot)))))))

(defun fn-heap-command-decide (action command replayp profile core nursery observations connections
                                      observed totals img config-octets card resident address)
  (declare (xargs :guard t))
  (let ((class (fn-heap-command-growth action command replayp)))
    ; A served run over a store is the launch's (fn-mo-serve-decide, host/native/heap.lisp
    ; fnn-heap-serve-decision, L-RUN-LAUNCH); one that names no store holds none.
    (cond ((or (equal class :store-less) (equal class :serves))
           (fn-heap-reserve-operation-decide :init profile core nursery observations
                                             connections nil))
          ((and (equal class :header) (natp config-octets))
           (fn-mo-header-decide profile core nursery observations connections config-octets))
          ((not (fn-mo-store-opening-p class))
           (fn-heap-reserve-operation-decide action profile core nursery observations
                                             connections observed))
          ((fn-mo-read-observed-p totals img config-octets card)
           (fn-mo-read-decide action class profile img core nursery totals config-octets card
                              resident address))
          (t (fn-mo-offline-adapter-decide action profile core nursery observations connections
                                           observed)))))

;; A store-opening decision's own refusals, by name (fn-heap-report-line
;; knows today's).
(defun fn-mo-read-refusal-line (decision)
  (declare (xargs :guard t))
  (let ((d (true-list-fix decision)))
    (cond ((equal (nth 1 d) :machine-cannot-hold-the-store)
           (concatenate 'string "refused machine-cannot-hold-the-store need="
                        (fn-heap-decimal (nth 2 d)) " MB machine=" (fn-heap-decimal (nth 3 d)) " MB"))
          ((equal (nth 1 d) :machine-cannot-hold-the-pools)
           (concatenate 'string "refused machine-cannot-hold-the-pools need="
                        (fn-heap-decimal (nth 2 d)) " MB machine=" (fn-heap-decimal (nth 3 d)) " MB"))
          (t (concatenate 'string "refused address-space-cannot-hold-the-reservation reservation="
                          (fn-heap-decimal (nth 2 d)) " MB address-space="
                          (fn-heap-decimal (nth 3 d)) " MB")))))

; The line the run logs and refuses with at configure: the capacity line
; (books/admission-memory.lisp fn-adm-capacity-line), unless the run's launch
; (fn-mo-run-decide) was refused by the address space with a capacity C'
; standing, which no capacity line says.
(defun fn-mo-run-capacity-line (d capacity-line)
  (declare (xargs :guard t))
  (let ((d (true-list-fix d)))
    (if (and (equal (car d) :refused)
             (equal (nth 1 d) :address-space-cannot-hold-the-reservation))
        (fn-mo-read-refusal-line d)
      capacity-line)))

; What a decision was sized without, by name: a store-opening command the
; adapter decided says so and what the equation could not see.
(defconst *fn-mo-adapter-words*
  " sized by the offline adapter (pre-payload-only figure, under-bounds the store): ")

;; An observed store-opening line names the totals the decision read (the
;; header's fold plus the scanned suffix, books/charged-totals.lisp), so a
;; native can hold them against the store's replayed report: RECORDS, ARENA,
;; HCHARGE, MEMBERSHIPS, EVENTS, LOG, HISTORY, CHARGE, then the residency.
(defun fn-mo-totals-words (tot)
  (declare (xargs :guard t))
  (concatenate 'string " totals="
               (fn-heap-decimal (fn-mm-tot-records tot)) ","
               (fn-heap-decimal (fn-mm-tot-arena tot)) ","
               (fn-heap-decimal (fn-mm-tot-hcharge tot)) ","
               (fn-heap-decimal (fn-mm-tot-memberships tot)) ","
               (fn-heap-decimal (fn-mm-tot-events tot)) ","
               (fn-heap-decimal (fn-mm-tot-log tot)) ","
               (fn-heap-decimal (fn-mm-tot-history tot)) ","
               (fn-heap-decimal (fn-mm-tot-charge tot)) ","
               (if (fn-mm-tot-paged-p tot) "paged" "resident")))

(defun fn-mo-unseen-suffix (class totals img config-octets card)
  (declare (xargs :guard t))
  (cond ((and (equal class :header) (not (natp config-octets))) " config=unobserved")
        ((not (fn-mo-store-opening-p class)) "")
        ((not (fn-mm-tot-p totals))
         (concatenate 'string *fn-mo-adapter-words* "header totals unseen"))
        ((not (fn-mm-img-p img)) (concatenate 'string *fn-mo-adapter-words* "img unobserved"))
        ((not (natp config-octets)) (concatenate 'string *fn-mo-adapter-words* "config unobserved"))
        ((not (posp card)) (concatenate 'string *fn-mo-adapter-words* "card unobserved"))
        (t (fn-mo-totals-words totals))))

(defun fn-heap-command-line (decision action command replayp totals img config-octets card)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-mo-unseen-suffix fn-heap-command-growth
                                                            fn-mo-read-refusal-line
                                                            fn-heap-reserve-report-line)))))
  (concatenate 'string
               (if (and (consp decision) (equal (car decision) :refused) (consp (cdr decision))
                        (member-equal (cadr decision) '(:machine-cannot-hold-the-store
                                                        :machine-cannot-hold-the-pools
                                                        :address-space-cannot-hold-the-reservation)))
                   (fn-mo-read-refusal-line decision)
                 (fn-heap-reserve-report-line decision))
               (fn-mo-unseen-suffix (fn-heap-command-growth action command replayp)
                                    totals img config-octets card)))

; -----------------------------------------------------------------------------
; THE KEYSTONES.  K6: a stopped status holds init's store-less figure and the
; configuration history it loads, no store; K7: an accepted store-opening
; decision holds its need at TOT and its card table within the resident
; observations, its heap the core's content and the need, its reservation
; within the address-space ones; K7b: and the need at every store within
; TOT; K8: it refuses only by them; the dispatch: a store-opening command
; is that decision at the observed totals, else the offline adapter, named
; in its line; `run' is today's decision until the run launch
; (MEMORY-RUN-LAUNCH-MODEL, this landing).
(defthm fn-mo-header-of-holds-the-header
  (let ((d (fn-mo-header-of init core observations config-octets)))
    (implies (equal (car d) :heap)
             (and (equal (car init) :heap)
                  (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb init)) (fn-mo-config-heap config-octets))
                      (* *fn-heap-mib* (fn-heap-decision-mb d)))
                  (<= (fn-heap-reservation-octets (fn-heap-decision-mb d) core (nth 4 d) (nth 5 d))
                      (fn-heap-machine-octets observations)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mo-header-of fn-heap-decision-mb)
                                  (fn-heap-reservation-octets fn-heap-machine-octets fn-heap-mb-of
                                   fn-mo-config-heap))
           :use ((:instance fn-heap-mb-of-covers (octets (fn-mo-config-heap config-octets)))))))

(defthm fn-mo-header-decide-holds-the-header
  (implies (equal (car (fn-mo-header-decide profile core nursery observations connections config-octets))
                  :heap)
           (and (equal (car (fn-heap-reserve-operation-decide :init profile core nursery observations
                                                              connections nil))
                       :heap)
                (<= (+ (* *fn-heap-mib*
                          (fn-heap-decision-mb (fn-heap-reserve-operation-decide
                                                :init profile core nursery observations connections nil)))
                       (fn-mo-config-heap config-octets))
                    (* *fn-heap-mib*
                       (fn-heap-decision-mb (fn-mo-header-decide profile core nursery observations
                                                                 connections config-octets))))
                (<= (fn-heap-reservation-octets
                     (fn-heap-decision-mb (fn-mo-header-decide profile core nursery observations
                                                               connections config-octets))
                     core
                     (nth 4 (fn-mo-header-decide profile core nursery observations connections config-octets))
                     (nth 5 (fn-mo-header-decide profile core nursery observations connections config-octets)))
                    (fn-heap-machine-octets observations))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-mo-header-decide) (theory 'minimal-theory))
           :use ((:instance fn-mo-header-of-holds-the-header
                            (init (fn-heap-reserve-operation-decide :init profile core nursery
                                                                    observations connections nil)))))))

(defthm fn-heap-stopped-status-is-sized-without-the-store
  (implies (and (not replayp) (natp config-octets))
           (equal (fn-heap-command-decide :status "status" replayp profile core nursery observations
                                          connections observed totals img config-octets card
                                          resident address)
                  (fn-mo-header-decide profile core nursery observations connections config-octets)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-command-decide fn-heap-command-growth)
                                             (theory 'minimal-theory)))))

(defthm fn-heap-command-decide-store-opening-is-the-model
  (implies (and (fn-mo-store-opening-p (fn-heap-command-growth action command replayp))
                (fn-mo-read-observed-p totals img config-octets card))
           (equal (fn-heap-command-decide action command replayp profile core nursery observations
                                          connections observed totals img config-octets card
                                          resident address)
                  (fn-mo-read-decide action (fn-heap-command-growth action command replayp)
                                     profile img core nursery totals config-octets card
                                     resident address)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-command-decide fn-mo-store-opening-p)
                                  (fn-mo-read-decide fn-mo-header-decide fn-mo-read-observed-p
                                   fn-heap-reserve-operation-decide)))))

; The adapter decides exactly the store-opening commands the equation cannot.
(defthm fn-heap-command-decide-store-opening-unobserved-is-the-adapter
  (implies (and (fn-mo-store-opening-p (fn-heap-command-growth action command replayp))
                (not (fn-mo-read-observed-p totals img config-octets card)))
           (equal (fn-heap-command-decide action command replayp profile core nursery observations
                                          connections observed totals img config-octets card
                                          resident address)
                  (fn-mo-offline-adapter-decide action profile core nursery observations connections
                                                observed)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-command-decide fn-mo-store-opening-p)
                                  (fn-mo-read-decide fn-mo-header-decide fn-mo-read-observed-p
                                   fn-heap-reserve-operation-decide fn-mo-offline-adapter-decide)))))

(defthm fn-heap-command-decide-otherwise-is-todays
  (implies (and (not (equal (fn-heap-command-growth action command replayp) :store-less))
                (not (equal (fn-heap-command-growth action command replayp) :serves))
                (not (and (equal (fn-heap-command-growth action command replayp) :header)
                          (natp config-octets)))
                (not (fn-mo-store-opening-p (fn-heap-command-growth action command replayp))))
           (equal (fn-heap-command-decide action command replayp profile core nursery observations
                                          connections observed totals img config-octets card
                                          resident address)
                  (fn-heap-reserve-operation-decide action profile core nursery observations
                                                    connections observed)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-command-decide) (theory 'minimal-theory)))))

(defthm fn-mo-read-holds-the-observed-store
  (implies (equal (car (fn-mo-read-decide action class profile img core nursery tot config-octets card
                                          resident address))
                  :heap)
           (and (natp (fn-mm-least-observation resident))
                (<= (fn-mo-read-resident action class profile img core nursery tot config-octets card)
                    (fn-mm-least-observation resident))
                (<= (+ (fn-heap-core-dynamic core)
                       (fn-mo-read-need action class profile img nursery tot config-octets))
                    (* *fn-heap-mib*
                       (fn-heap-decision-mb
                        (fn-mo-read-decide action class profile img core nursery tot config-octets card
                                           resident address))))
                (implies (natp (fn-mm-least-observation address))
                         (<= (fn-mo-read-reservation action class profile img core nursery tot
                                                     config-octets)
                             (fn-mm-least-observation address)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mo-read-decide fn-heap-decision-mb)
                                  (fn-mo-read-need fn-mo-read-resident fn-mo-read-reservation
                                   fn-heap-mb-of fn-mm-least-observation fn-heap-with-nursery
                                   fn-heap-core-dynamic fn-heap-profile-word fn-heap-stack-kib
                                   fn-heap-thread-count))
           :use ((:instance fn-heap-mb-of-covers
                            (octets (fn-mo-read-dynamic action class profile img core nursery tot
                                                        config-octets)))
                 (:instance fn-heap-with-nursery-covers-base
                            (base (+ (fn-heap-core-dynamic core)
                                     (fn-mo-read-need action class profile img nursery tot
                                                      config-octets))))))))

; The need grows with the store: at every store within TOT it is at most
; the need at TOT.
(defthm fn-mo-list-octets-grows-with-the-log
  (implies (<= (fn-mm-tot-log a) (fn-mm-tot-log b))
           (<= (fn-mo-list-octets action profile a) (fn-mo-list-octets action profile b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mo-list-octets)
                                  (fn-mm-tot-log fn-heap-operation-history-copies nfix
                                   fn-bs-profile-max-record-octets fn-bs-profile-field))
           :use ((:instance fn-mm-times-monotone (a (fn-mm-tot-log a)) (b (fn-mm-tot-log b))
                            (c (fn-heap-operation-history-copies action)))))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-heap-operation-history-copies)))))

(defthm fn-mo-read-need-grows-with-the-store
  (implies (fn-mm-tot-le a b)
           (<= (fn-mo-read-need action class profile img nursery a config-octets)
               (fn-mo-read-need action class profile img nursery b config-octets)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-mo-read-need max) (theory 'minimal-theory))
           :use ((:instance fn-mm-sum-grows-with-the-store (cfg (fn-mo-read-cfg nursery config-octets)))
                 (:instance fn-mm-reopen-need-monotone (cfg (fn-mo-read-cfg nursery config-octets))
                            (i1 img) (i2 img))
                 (:instance fn-mm-img-le-reflexive (i img))
                 fn-mm-tot-le-parts
                 fn-mo-list-octets-grows-with-the-log))))

; K7b.  An accepted store-opening decision at TOT holds, within the resident
; limit and its heap, the need at every store whose totals are within TOT.
(defthm fn-mo-read-holds-every-store-within-its-totals
  (implies (and (equal (car (fn-mo-read-decide action class profile img core nursery tot config-octets
                                               card resident address))
                       :heap)
                (fn-mm-tot-le a tot))
           (and (<= (fn-mo-read-need action class profile img nursery a config-octets)
                    (fn-mm-least-observation resident))
                (<= (+ (fn-heap-core-dynamic core)
                       (fn-mo-read-need action class profile img nursery a config-octets))
                    (* *fn-heap-mib*
                       (fn-heap-decision-mb
                        (fn-mo-read-decide action class profile img core nursery tot config-octets card
                                           resident address))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mo-read-resident)
                                  (fn-mo-read-decide fn-mo-read-need fn-mo-card-octets
                                   fn-heap-decision-mb fn-mm-least-observation fn-heap-core-dynamic
                                   fn-mm-tot-le fn-mo-read-dynamic fn-heap-mb-of))
           :use (fn-mo-read-holds-the-observed-store
                 (:instance fn-mo-read-need-grows-with-the-store (b tot))))))

; A store-opening need is never zero (the failure headroom alone is not),
; so a need within the resident observation names one.
(defthm fn-mo-read-resident-positive
  (< 0 (fn-mo-read-resident action class profile img core nursery tot config-octets card))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-mo-read-resident fn-mo-read-need fn-mm-reopen-need
                                   fn-mo-config-heap fn-mo-card-octets fn-mm-reopen-live)
                                  (fn-mm-base fn-mm-owner fn-mm-maintenance fn-mm-sum fn-mo-list-octets
                                   fn-heap-store-open-octets fn-mo-read-dynamic fn-heap-mb-of
                                   fn-mm-collector fn-mm-checkpoint-load-octets))
           :use ((:instance fn-mm-terms-natp (cfg (fn-mo-read-cfg nursery config-octets)))))))

(defthm fn-mo-read-refuses-only-by-the-model
  (implies (and (<= (fn-mo-read-resident action class profile img core nursery tot config-octets card)
                    (fn-mm-least-observation resident))
                (or (not (natp (fn-mm-least-observation address)))
                    (<= (fn-mo-read-reservation action class profile img core nursery tot config-octets)
                        (fn-mm-least-observation address))))
           (equal (car (fn-mo-read-decide action class profile img core nursery tot config-octets card
                                          resident address))
                  :heap))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mo-read-decide)
                                  (fn-mo-read-resident fn-mo-read-reservation fn-mo-read-dynamic
                                   fn-mm-least-observation))
           :use ((:instance fn-mo-read-resident-positive)
                 (:instance fn-mm-least-observation-type (obs resident))))))

; The line of a store-opening command the adapter decided names it.
(defthm fn-heap-command-line-names-the-adapter
  (implies (and (fn-mo-store-opening-p (fn-heap-command-growth action command replayp))
                (not (fn-mm-tot-p totals)))
           (equal (fn-mo-unseen-suffix (fn-heap-command-growth action command replayp)
                                       totals img config-octets card)
                  (concatenate 'string *fn-mo-adapter-words* "header totals unseen")))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mo-unseen-suffix fn-mo-store-opening-p)
                                  (fn-heap-command-growth fn-mm-tot-p)))))

; -----------------------------------------------------------------------------
; THE RUN'S LAUNCH, K4 and K5 at C' (MEMORY-RUN-LAUNCH-MODEL; ruling (b)):
; the launch fn-mo-run-decide decides is the model's at C', never at the
; configured C, which would refuse every run the capacity line holds.  Not
; yet a line of fn-heap-command-decide: the arm waits on the run's cfg at the
; probe (host/native/heap.lisp; see the repair item).
(defthm fn-mo-run-refusal-is-a-refusal
  (equal (car (fn-mo-run-refusal d need)) :refused)
  :hints (("Goal" :in-theory (enable fn-mo-run-refusal))))

; The accepted run decision is the model's launch at C' with C' positive, and
; its heap is the launch's dynamic space in MB.
(defthm fn-mo-run-decide-heap-is-the-launch-at-its-capacity
  (let* ((limit (fn-mm-resident-limit configured resident))
         (cap (fn-adm-capacity profile img cfg limit tot))
         (dl (fn-mm-launch-decide profile img (fn-adm-cfg-at cfg (nfix cap)) configured resident
                                  address core nursery tot)))
    (implies (equal (car (fn-mo-run-decide profile img cfg configured resident address core nursery tot))
                    :heap)
             (and (equal (car dl) :launch)
                  (posp cap)
                  (equal (cadr (fn-mo-run-decide profile img cfg configured resident address core
                                                 nursery tot))
                         (fn-heap-mb-of (caddr dl))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-mo-run-decide fn-mo-run-refusal-is-a-refusal
                                               car-cons cdr-cons nfix)
                                             (theory 'minimal-theory)))))

(defthm fn-mo-run-decide-launches-at-its-capacity
  (let* ((limit (fn-mm-resident-limit configured resident))
         (cap (fn-adm-capacity profile img cfg limit tot))
         (dl (fn-mm-launch-decide profile img (fn-adm-cfg-at cfg (nfix cap)) configured resident
                                  address core nursery tot)))
    (implies (and (posp cap) (equal (car dl) :launch))
             (equal (car (fn-mo-run-decide profile img cfg configured resident address core nursery tot))
                    :heap)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-mo-run-decide fn-mo-run-refusal-is-a-refusal
                                               car-cons cdr-cons nfix)
                                             (theory 'minimal-theory)))))

(defthm fn-mm-launch-decide-launches-at-the-resident-limit
  (implies (equal (car (fn-mm-launch-decide profile img cfg configured resident address core nursery tot))
                  :launch)
           (equal (cadr (fn-mm-launch-decide profile img cfg configured resident address core nursery tot))
                  (fn-mm-resident-limit configured resident)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-launch-decide)
                                  (fn-mm-gate-p fn-mm-launch-dynamic fn-mm-launch-reservation
                                   fn-mm-resident-limit fn-mm-sum fn-mm-reopen-need
                                   fn-mm-least-observation)))))

(defthm fn-mm-launch-decide-dynamic-is-natp
  (implies (equal (car (fn-mm-launch-decide profile img cfg configured resident address core nursery tot))
                  :launch)
           (natp (caddr (fn-mm-launch-decide profile img cfg configured resident address core nursery tot))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-launch-decide fn-mm-launch-dynamic)
                                  (fn-mm-gate-p fn-mm-launch-reservation
                                   fn-mm-resident-limit fn-mm-sum fn-mm-reopen-need
                                   fn-mm-least-observation)))))

(defthm fn-mo-run-decide-holds-the-store-at-its-capacity
  (implies (equal (car (fn-mo-run-decide profile img cfg configured resident address core nursery tot))
                  :heap)
           (let* ((d (fn-mo-run-decide profile img cfg configured resident address core nursery tot))
                  (limit (fn-mm-resident-limit configured resident))
                  (c (fn-adm-capacity profile img cfg limit tot)))
             (and (posp c)
                  (<= c (fn-mm-cfg-connections cfg))
                  (natp limit)
                  (<= (fn-mm-sum profile img (fn-adm-cfg-at cfg c) tot) limit)
                  (<= (fn-mm-reopen-need profile img (fn-adm-cfg-at cfg c) tot) limit)
                  (implies (natp (fn-mm-least-observation address))
                           (<= (fn-mm-launch-reservation limit core nursery (fn-adm-cfg-at cfg c) profile)
                               (fn-mm-least-observation address)))
                  (<= (+ (fn-heap-core-dynamic core) limit)
                      (* (cadr d) *fn-heap-mib*)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-mm-launch-decide fn-adm-capacity fn-mo-run-decide fn-adm-cfg-at
                               fn-mm-resident-limit fn-mm-sum fn-mm-reopen-need fn-mm-launch-reservation
                               fn-mm-least-observation fn-heap-core-dynamic fn-heap-mb-of fn-mm-cfg-connections
                               fn-mm-gate-p)
           :use ((:instance fn-mo-run-decide-heap-is-the-launch-at-its-capacity)
                 (:instance fn-mm-launch-decide-dynamic-is-natp
                            (cfg (fn-adm-cfg-at cfg (nfix (fn-adm-capacity profile img cfg (fn-mm-resident-limit configured resident) tot)))))
                 (:instance fn-mm-launch-decide-launches-at-the-resident-limit
                            (cfg (fn-adm-cfg-at cfg (nfix (fn-adm-capacity profile img cfg (fn-mm-resident-limit configured resident) tot))))
                            (tot tot))
                 (:instance fn-adm-capacity-fits
                            (limit (fn-mm-resident-limit configured resident)))
                 (:instance fn-mm-launch-holds-the-store-and-the-reservation
                            (cfg (fn-adm-cfg-at cfg (nfix (fn-adm-capacity profile img cfg
                                                                           (fn-mm-resident-limit configured resident) tot))))
                            (resident-obs resident) (address-obs address) (obs tot))
                 (:instance fn-heap-mb-of-covers
                            (octets (caddr (fn-mm-launch-decide
                                            profile img
                                            (fn-adm-cfg-at cfg (nfix (fn-adm-capacity profile img cfg
                                                                                      (fn-mm-resident-limit configured resident) tot)))
                                            configured resident address core nursery tot))))))))

(defthm fn-mo-run-decide-refuses-only-by-the-model
  (implies (and (posp (fn-adm-capacity profile img cfg (fn-mm-resident-limit configured resident) tot))
                (or (not (natp (fn-mm-least-observation address)))
                    (<= (fn-mm-launch-reservation
                         (fn-mm-resident-limit configured resident) core nursery
                         (fn-adm-cfg-at cfg (fn-adm-capacity profile img cfg
                                                             (fn-mm-resident-limit configured resident) tot))
                         profile)
                        (fn-mm-least-observation address))))
           (equal (car (fn-mo-run-decide profile img cfg configured resident address core nursery tot))
                  :heap))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-mm-launch-decide fn-adm-capacity fn-mo-run-decide fn-adm-cfg-at
                               fn-mm-resident-limit fn-mm-sum fn-mm-reopen-need fn-mm-launch-reservation
                               fn-mm-least-observation fn-heap-core-dynamic fn-heap-mb-of fn-mm-cfg-connections
                               fn-mm-gate-p)
           :use ((:instance fn-mo-run-decide-launches-at-its-capacity)
                 (:instance fn-adm-capacity-fits
                            (limit (fn-mm-resident-limit configured resident)))
                 (:instance fn-mm-launch-refuses-only-by-the-model
                            (cfg (fn-adm-cfg-at cfg (nfix (fn-adm-capacity profile img cfg
                                                                           (fn-mm-resident-limit configured resident) tot))))
                            (resident-obs resident) (address-obs address) (obs tot))))))

; -----------------------------------------------------------------------------
; -----------------------------------------------------------------------------
; THE SERVED RUN'S LAUNCH (L-RUN-LAUNCH; planning/memory-l-fresh-attribution.md).  The `run' probe
; (host/native/heap.lisp fnn-heap-serve-decision) launches at the run's LIMIT, the configure's
; (host/owner-host.lisp fn-owner-memory-configure: the least resident observation less the pools): its
; dynamic space holds the launch's (the core's content and LIMIT, with the collector's room:
; fn-mm-launch-dynamic) plus the pools' heap, and it refuses an observed store whose reopen LIMIT
; cannot hold.  The run's capacity C' is the configure's alone (fn-adm-capacity over the replayed
; totals and the stored configuration), which refuses by name when no connection fits.  The reservation is compared
; with the address-space observations only: memory.max and physical memory bound resident memory,
; which the gate keeps within LIMIT, not the dynamic space.  The core's content is charged at the
; image FILE's bound (fn-prstartup-image-bound), so the owner, whose content at startup exceeds the
; probe's, is held by the same figure (fn-mo-serve-holds-every-admitted-store).
;
; The pools the served run funds beside the model's terms: the DEFAULT pool's heap (or the explicit
; cold policy's budget), the output pool's, the peer flight's heap and its workers' stacks.  The configure's LIMIT excludes them
; and the dynamic space adds them.
(defun fn-mo-serve-pools (profile cold output peer workers cache-limit root)
  (declare (xargs :guard t))
  (+ (if cold
         (nfix (car (fn-crv-pool-budget cold profile)))
       (nfix (fn-prstartup-launch-extra profile workers cache-limit root)))
     (if (consp output) (nfix (car output)) 0)
     (if (consp peer) (nfix (car peer)) 0)
     ;; the peer flight's workers: their stacks and runtime are resident beside the heap (the cold
     ;; policy's budget already holds its own, fn-crv-native-baseline)
     (if (consp peer)
         (* (nfix (nth 3 (true-list-fix peer)))
            (+ (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*))
       0)))

; The threads the pools run beside the node's own: the cold policy's workers and the peer flight's.
(defun fn-mo-serve-pool-threads (cold peer)
  (declare (xargs :guard t))
  (+ (if (consp cold) (nfix (nth 1 (true-list-fix cold))) 0)
     (if (consp peer) (nfix (nth 3 (true-list-fix peer))) 0)))

(defun fn-mo-serve-limit (resident pools)
  (declare (xargs :guard t))
  (let ((r (fn-mm-least-observation resident)))
    (and (natp r) (nfix (- r (nfix pools))))))

(defun fn-mo-serve-dynamic (limit core nursery pools)
  (declare (xargs :guard t))
  (+ (fn-mm-launch-dynamic limit (fn-prstartup-image-bound core) nursery) (nfix pools)))

; The node's threads (fn-heap-thread-count, structural since PRF-211) and the pools'.
(defun fn-mo-serve-threads (pool-threads)
  (declare (xargs :guard t))
  (+ (fn-heap-thread-count nil) (nfix pool-threads)))

(defun fn-mo-serve-reservation (profile core dynamic pool-threads)
  (declare (xargs :guard t))
  (fn-heap-reservation-octets (fn-heap-mb-of dynamic) core (fn-heap-stack-kib profile)
                              (fn-mo-serve-threads pool-threads)))

; The run's reopen coordinates, the only ones the store's reopen reads (fn-mo-serve-reopen-reads-
; its-coordinates): the serving trigger, the publication trigger the owner sets in the launched space
; (host/native/io.lisp fnn-gc-nursery-octets: fn-heap-nursery-trigger of that space), the live-reclaim
; opt-in, the cold policy's budget, and the configuration history's octets.  The serving coordinates
; (connections, TLS, handshakes, the OVER window, the server name) are the configure's, which decides C'
; (host/owner-host.lisp fn-owner-memory-configure); the probe does not read the stored configuration.
(defun fn-mo-reopen-cfg (cfg)
  (declare (xargs :guard t))
  (let ((cfg (true-list-fix cfg)))
    (list 0 nil (nth 2 cfg) (nth 3 cfg) (nth 4 cfg) (nth 5 cfg) (nth 6 cfg) 0 nil 0 nil
          (nth 11 cfg) (nth 12 cfg))))

(defun fn-mo-serve-cfg (trigger pub-trigger live cold profile config)
  (declare (xargs :guard t))
  (list 0 nil trigger pub-trigger live 0
        (if cold (car (fn-crv-pool-budget cold profile)) 0)
        0 nil 0 nil nil (nfix config)))

; (:heap MB PROFILE-WORD LIMIT-MB STACK-KIB THREADS), or a refusal in fn-mo-run-refusal's words.  TOT
; the observed charged totals, NIL when unseen (the reopen is then the configure's alone, after the
; open); TRIGGER, LIVE, COLD, CONFIG the run's reopen coordinates; NURSERY the collector cap the owner's
; trigger is taken under.
(defun fn-mo-serve-decide (profile img trigger live cold config resident address core nursery tot pools
                                   pool-threads)
  (declare (xargs :guard t))
  (let* ((limit (fn-mo-serve-limit resident pools))
         (dynamic (fn-mo-serve-dynamic limit core nursery pools))
         (cfg (fn-mo-serve-cfg trigger
                               (fn-heap-nursery-trigger (* *fn-heap-mib* (fn-heap-mb-of dynamic)) nursery)
                               live cold profile config))
         (reservation (fn-mo-serve-reservation profile core dynamic pool-threads))
         (addr (fn-mm-least-observation address)))
    (cond ((not (natp limit)) (list :refused :machine-memory-unobserved 0 0))
          ((< (fn-mm-least-observation resident) (nfix pools))
           (list :refused :machine-cannot-hold-the-pools
                 (fn-heap-mb-of (nfix pools)) (floor (fn-mm-least-observation resident) *fn-heap-mib*)))
          ((and (fn-mm-tot-p tot) (< limit (fn-mm-reopen-need profile img cfg tot)))
           (list :refused :machine-cannot-hold-the-store
                 (fn-heap-mb-of (fn-mm-reopen-need profile img cfg tot)) (floor limit *fn-heap-mib*)))
          ((and (natp addr) (< addr reservation))
           (list :refused :address-space-cannot-hold-the-reservation
                 (fn-heap-mb-of reservation) (floor addr *fn-heap-mib*)))
          (t (list :heap (fn-heap-mb-of dynamic) (fn-heap-profile-word profile)
                   (floor limit *fn-heap-mib*) (fn-heap-stack-kib profile)
                   (fn-mo-serve-threads pool-threads))))))

; The reopen coordinates carry every field the reopen reads, term by term.
(defthm fn-mo-reopen-cfg-accessors
  (and (equal (fn-mm-cfg-trigger (fn-mo-reopen-cfg cfg)) (fn-mm-cfg-trigger cfg))
       (equal (fn-mm-cfg-pub-trigger (fn-mo-reopen-cfg cfg)) (fn-mm-cfg-pub-trigger cfg))
       (equal (fn-mm-cfg-reclaim-live-p (fn-mo-reopen-cfg cfg)) (fn-mm-cfg-reclaim-live-p cfg))
       (equal (fn-mm-cfg-cache (fn-mo-reopen-cfg cfg)) (fn-mm-cfg-cache cfg))
       (equal (fn-mm-cfg-rho (fn-mo-reopen-cfg cfg)) (fn-mm-cfg-rho cfg))
       (equal (fn-mm-cfg-config (fn-mo-reopen-cfg cfg)) (fn-mm-cfg-config cfg)))
  :hints (("Goal" :in-theory (enable fn-mo-reopen-cfg fn-mm-cfg-trigger fn-mm-cfg-pub-trigger
                                     fn-mm-cfg-reclaim-live-p fn-mm-cfg-cache fn-mm-cfg-rho
                                     fn-mm-cfg-config fn-mm-nat))))

(defthm fn-mo-reopen-cfg-owner
  (equal (fn-mm-owner tot (fn-mo-reopen-cfg cfg)) (fn-mm-owner tot cfg))
  :hints (("Goal" :in-theory (e/d (fn-mm-owner fn-mm-payload-octets)
                                  (fn-mo-reopen-cfg fn-mm-cfg-cache fn-mm-cfg-config)))))

(defthm fn-mo-reopen-cfg-maintenance
  (equal (fn-mm-maintenance tot (fn-mo-reopen-cfg cfg)) (fn-mm-maintenance tot cfg))
  :hints (("Goal" :in-theory (e/d (fn-mm-maintenance)
                                  (fn-mo-reopen-cfg fn-mm-cfg-trigger fn-mm-cfg-pub-trigger
                                   fn-mm-cfg-reclaim-live-p)))))

(defthm fn-mo-reopen-cfg-checkpoint-load
  (equal (fn-mm-checkpoint-load-octets profile tot (fn-mo-reopen-cfg cfg))
         (fn-mm-checkpoint-load-octets profile tot cfg))
  :hints (("Goal" :in-theory (e/d (fn-mm-checkpoint-load-octets)
                                  (fn-mo-reopen-cfg fn-mm-cfg-config)))))

(defthm fn-mo-reopen-cfg-collector
  (equal (fn-mm-collector live (fn-mo-reopen-cfg cfg)) (fn-mm-collector live cfg))
  :hints (("Goal" :in-theory (e/d (fn-mm-collector)
                                  (fn-mo-reopen-cfg fn-mm-cfg-trigger fn-mm-cfg-rho)))))

(defthm fn-mo-reopen-cfg-base
  (equal (fn-mm-base img (fn-mo-reopen-cfg cfg)) (fn-mm-base img cfg))
  :hints (("Goal" :in-theory (e/d (fn-mm-base fn-mm-cfg-connections) (fn-mo-reopen-cfg)))))

; The store's reopen reads only the reopen coordinates.
(defthm fn-mo-serve-reopen-reads-its-coordinates
  (equal (fn-mm-reopen-need profile img (fn-mo-reopen-cfg cfg) tot)
         (fn-mm-reopen-need profile img cfg tot))
  :hints (("Goal" :in-theory (e/d (fn-mm-reopen-need fn-mm-reopen-live)
                                  (fn-mo-reopen-cfg fn-mm-owner fn-mm-maintenance
                                   fn-mm-checkpoint-load-octets fn-mm-collector fn-mm-base)))))

; The decision's cases, over abstract terms: the proofs of the keystones below never expand the
; decision's let* (a clause that size defeats the prover's subsumption).
(defthm fn-mo-serve-decide-pool-cases-launch-by-definition
  (implies (and (natp limit)
                (not poolbad)
                (or (not totp) (<= need limit))
                (or (not (natp addr)) (<= res addr)))
           (equal (car (cond ((not (natp limit)) (list :refused :machine-memory-unobserved 0 0))
                             (poolbad (list :refused :machine-cannot-hold-the-pools j k))
                             ((and totp (< limit need)) (list :refused :machine-cannot-hold-the-store a b))
                             ((and (natp addr) (< addr res))
                              (list :refused :address-space-cannot-hold-the-reservation c d))
                             (t (list :heap e f g h i))))
                  :heap))
  :rule-classes nil)

(defthm fn-mo-serve-decide-pool-cases-heap-by-definition
  (let ((d (cond ((not (natp limit)) (list :refused :machine-memory-unobserved 0 0))
                 (poolbad (list :refused :machine-cannot-hold-the-pools j k))
                 ((and totp (< limit need)) (list :refused :machine-cannot-hold-the-store a b))
                 ((and (natp addr) (< addr res))
                  (list :refused :address-space-cannot-hold-the-reservation c d0))
                 (t (list :heap e f g h i)))))
    (implies (equal (car d) :heap)
             (and (natp limit)
                  (not poolbad)
                  (implies totp (<= need limit))
                  (implies (natp addr) (<= res addr))
                  (equal d (list :heap e f g h i)))))
  :rule-classes nil)

(defthm fn-mo-serve-decide-heap-facts
  (let* ((limit (fn-mo-serve-limit resident pools))
         (dynamic (fn-mo-serve-dynamic limit core nursery pools))
         (cfg (fn-mo-serve-cfg trigger
                               (fn-heap-nursery-trigger (* *fn-heap-mib* (fn-heap-mb-of dynamic)) nursery)
                               live cold profile config))
         (addr (fn-mm-least-observation address))
         (d (fn-mo-serve-decide profile img trigger live cold config resident address core
                                nursery tot pools pool-threads)))
    (implies (equal (car d) :heap)
             (and (natp limit)
                  (implies (fn-mm-tot-p tot) (<= (fn-mm-reopen-need profile img cfg tot) limit))
                  (implies (natp addr)
                           (<= (fn-mo-serve-reservation profile core dynamic pool-threads) addr))
                  (equal d (list :heap (fn-heap-mb-of dynamic) (fn-heap-profile-word profile)
                                 (floor limit *fn-heap-mib*) (fn-heap-stack-kib profile)
                                 (fn-mo-serve-threads pool-threads))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-mo-serve-decide) (theory 'minimal-theory))
           :use ((:instance fn-mo-serve-decide-pool-cases-heap-by-definition
                  (limit (fn-mo-serve-limit resident pools))
                  (poolbad (< (fn-mm-least-observation resident) (nfix pools)))
                  (j (fn-heap-mb-of (nfix pools)))
                  (k (floor (fn-mm-least-observation resident) *fn-heap-mib*))
                  (totp (fn-mm-tot-p tot))
                  (need (fn-mm-reopen-need profile img
                          (fn-mo-serve-cfg trigger
                            (fn-heap-nursery-trigger
                             (* *fn-heap-mib* (fn-heap-mb-of (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools)))
                             nursery)
                            live cold profile config)
                          tot))
                  (addr (fn-mm-least-observation address))
                  (res (fn-mo-serve-reservation profile core
                         (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools) pool-threads))
                  (a (fn-heap-mb-of (fn-mm-reopen-need profile img
                          (fn-mo-serve-cfg trigger
                            (fn-heap-nursery-trigger
                             (* *fn-heap-mib* (fn-heap-mb-of (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools)))
                             nursery)
                            live cold profile config)
                          tot)))
                  (b (floor (fn-mo-serve-limit resident pools) *fn-heap-mib*))
                  (c (fn-heap-mb-of (fn-mo-serve-reservation profile core
                         (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools) pool-threads)))
                  (d0 (floor (fn-mm-least-observation address) *fn-heap-mib*))
                  (e (fn-heap-mb-of (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools)))
                  (f (fn-heap-profile-word profile))
                  (g (floor (fn-mo-serve-limit resident pools) *fn-heap-mib*))
                  (h (fn-heap-stack-kib profile))
                  (i (fn-mo-serve-threads pool-threads)))))))

(defthm fn-mo-serve-decide-heap-mb
  (implies (equal (car (fn-mo-serve-decide profile img trigger live cold config resident address core
                                           nursery tot pools pool-threads))
                  :heap)
           (equal (cadr (fn-mo-serve-decide profile img trigger live cold config resident address core
                                            nursery tot pools pool-threads))
                  (fn-heap-mb-of (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))
           :use ((:instance fn-mo-serve-decide-heap-facts)))))

(defthm fn-mo-serve-decide-heap-limit
  (implies (equal (car (fn-mo-serve-decide profile img trigger live cold config resident address core
                                           nursery tot pools pool-threads))
                  :heap)
           (natp (fn-mo-serve-limit resident pools)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))
           :use ((:instance fn-mo-serve-decide-heap-facts)))))

; A launched decision carries a natural resident observation that holds its pools.
(defthm fn-mo-serve-launch-holds-its-pools-at-the-decision
  (implies (equal (car (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot pools pool-threads)) :heap)
           (and (natp (fn-mm-least-observation resident))
                (<= (nfix pools) (fn-mm-least-observation resident))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories '(fn-mo-serve-decide fn-mo-serve-limit car-cons natp nfix)
                                      (theory 'minimal-theory)))))

; KEYSTONE K-L2p (L-RUN-LAUNCH, native m21-lrl-2): the probe refuses an unobserved
; resident bound or pools beyond it; no such decision launches.
(defthm fn-mo-serve-launch-holds-its-pools
  (implies (or (not (natp (fn-mm-least-observation resident)))
               (< (fn-mm-least-observation resident) (nfix pools)))
           (not (equal (car (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot pools pool-threads)) :heap)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use fn-mo-serve-launch-holds-its-pools-at-the-decision)))

(defthm fn-mo-serve-decide-heap-reservation
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live cold config resident address core
                                                nursery tot pools pool-threads))
                       :heap)
                (natp (fn-mm-least-observation address)))
           (<= (fn-mo-serve-reservation profile core
                                        (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools)
                                        pool-threads)
               (fn-mm-least-observation address)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))
           :use ((:instance fn-mo-serve-decide-heap-facts)))))

(defthm fn-mo-serve-gate-holds-the-limit
  (implies (fn-mm-gate-p profile img cfg limit tot)
           (and (natp limit) (<= (fn-mm-reopen-need profile img cfg tot) limit)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-mm-gate-p))))

(defthm fn-mo-serve-image-bound-dynamic-is-the-file
  (equal (fn-heap-core-dynamic (fn-prstartup-image-bound core))
         (fn-heap-core-file core))
  :hints (("Goal" :in-theory (enable fn-prstartup-image-bound fn-heap-core-dynamic fn-heap-core-file))))

(defthm fn-mo-serve-dynamic-holds-the-owner-and-the-store
  (implies (and (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp limit) (<= need limit))
           (<= (+ (fn-heap-core-dynamic owner) need (nfix pools))
               (fn-mo-serve-dynamic limit core nursery pools)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-mo-serve-dynamic)
                           (fn-mm-launch-dynamic fn-heap-core-dynamic fn-heap-core-file
                            fn-prstartup-image-bound))
           :use ((:instance fn-mm-launch-dynamic-holds-the-core-and-the-limit
                  (core (fn-prstartup-image-bound core)))
                 (:instance fn-heap-core-dynamic-is-at-most-the-file (core owner))))))

; KEYSTONE K-L2: the launched heap holds the core's content of any process of the same core file, the
; reopen of every store any memory gate at the run's LIMIT admits (whatever image and coordinates it is
; priced at: the owner's configure prices its own), and the pools.
(defthm fn-mo-serve-holds-every-admitted-store-at-the-decision
  (let ((d (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot
                               pools pool-threads)))
    (implies (and (equal (car d) :heap)
                  (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                  (fn-mm-gate-p profile img2 cfg2 (fn-mo-serve-limit resident pools) tot2))
             (<= (+ (fn-heap-core-dynamic owner)
                    (fn-mm-reopen-need profile img2 cfg2 tot2)
                    (nfix pools))
                 (* *fn-heap-mib* (cadr d)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-mo-serve-decide fn-mo-serve-limit fn-mo-serve-dynamic fn-mm-gate-p fn-mm-reopen-need fn-heap-mb-of fn-heap-core-dynamic fn-heap-core-file fn-mm-sum)
           :use ((:instance fn-mo-serve-decide-heap-mb)
                 (:instance fn-mo-serve-gate-holds-the-limit
                  (cfg cfg2) (img img2) (tot tot2) (limit (fn-mo-serve-limit resident pools)))
                 (:instance fn-mo-serve-dynamic-holds-the-owner-and-the-store
                  (limit (fn-mo-serve-limit resident pools))
                  (need (fn-mm-reopen-need profile img2 cfg2 tot2)))
                 (:instance fn-heap-mb-of-covers
                  (octets (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools)))))))

; KEYSTONE (L-RUN-LAUNCH), the statement its teeth bind: fn-mo-serve-holds-every-admitted-store-at-the-decision with the
; decision written out.
(defthm fn-mo-serve-holds-every-admitted-store
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot pools pool-threads)) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (fn-mm-gate-p profile img2 cfg2 (fn-mo-serve-limit resident pools) tot2))
           (<= (+ (fn-heap-core-dynamic owner)
                  (fn-mm-reopen-need profile img2 cfg2 tot2)
                  (nfix pools))
               (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot pools pool-threads))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(nfix fn-heap-mb-of-natp) (theory 'minimal-theory))
           :use (fn-mo-serve-holds-every-admitted-store-at-the-decision fn-mo-serve-decide-heap-mb))))


; KEYSTONE K-L3: the launch refuses only by the model: with a resident observation, the pools within
; that observation, the observed store's reopen within the limit (or the totals unseen), and the
; reservation within the address space (or none observed), it launches.  The pools beyond the resident
; limit join the model's refusals.  No comparison of the reservation with a resident limit remains.
(defthm fn-mo-serve-refuses-only-by-the-model-at-the-decision
  (let* ((limit (fn-mo-serve-limit resident pools))
         (dynamic (fn-mo-serve-dynamic limit core nursery pools))
         (cfg (fn-mo-serve-cfg trigger
                               (fn-heap-nursery-trigger (* *fn-heap-mib* (fn-heap-mb-of dynamic)) nursery)
                               live cold profile config))
         (addr (fn-mm-least-observation address)))
    (implies (and (natp limit)
                  (<= (nfix pools) (fn-mm-least-observation resident))
                  (or (not (fn-mm-tot-p tot)) (<= (fn-mm-reopen-need profile img cfg tot) limit))
                  (or (not (natp addr))
                      (<= (fn-mo-serve-reservation profile core dynamic pool-threads) addr)))
             (equal (car (fn-mo-serve-decide profile img trigger live cold config resident address core
                                             nursery tot pools pool-threads))
                    :heap)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-mo-serve-decide car-cons) (theory 'minimal-theory))
           :use ((:instance fn-mo-serve-decide-pool-cases-launch-by-definition
                  (limit (fn-mo-serve-limit resident pools))
                  (poolbad (< (fn-mm-least-observation resident) (nfix pools)))
                  (j 0) (k 0)
                  (totp (fn-mm-tot-p tot))
                  (need (fn-mm-reopen-need profile img
                          (fn-mo-serve-cfg trigger
                            (fn-heap-nursery-trigger
                             (* *fn-heap-mib* (fn-heap-mb-of (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools)))
                             nursery)
                            live cold profile config)
                          tot))
                  (addr (fn-mm-least-observation address))
                  (res (fn-mo-serve-reservation profile core
                         (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools) pool-threads))
                  (a 0) (b 0) (c 0) (d 0) (e 0) (f 0) (g 0) (h 0) (i 0))))))

; KEYSTONE (L-RUN-LAUNCH), the statement its teeth bind: fn-mo-serve-refuses-only-by-the-model-at-the-decision with the
; decision written out.
(defthm fn-mo-serve-refuses-only-by-the-model
  (implies (and (natp (fn-mo-serve-limit resident pools))
                (<= (nfix pools) (fn-mm-least-observation resident))
                (or (not (fn-mm-tot-p tot))
                    (<= (fn-mm-reopen-need profile img (fn-mo-serve-cfg trigger (fn-heap-nursery-trigger (* *fn-heap-mib* (fn-heap-mb-of (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools))) nursery) live cold profile config) tot) (fn-mo-serve-limit resident pools)))
                (or (not (natp (fn-mm-least-observation address)))
                    (<= (fn-mo-serve-reservation profile core (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools) pool-threads) (fn-mm-least-observation address))))
           (equal (car (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot pools pool-threads)) :heap))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use fn-mo-serve-refuses-only-by-the-model-at-the-decision)))


; KEYSTONE K-L3b: a launch's whole reservation (the dynamic space it answers, the core file, every
; thread it answers) fits every address-space observation, and an observed store reopens within the
; limit at the coordinates the owner will price it at: every configuration whose reopen coordinates
; are the probe's (fn-mo-reopen-cfg), the publication trigger the owner sets in the launched space.
(defthm fn-mo-serve-launch-fits-the-address-space-at-the-decision
  (let* ((limit (fn-mo-serve-limit resident pools))
         (d (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot
                                pools pool-threads))
         (addr (fn-mm-least-observation address)))
    (implies (equal (car d) :heap)
             (and (natp limit)
                  (implies (natp addr)
                           (<= (fn-heap-reservation-octets (cadr d) core (nth 4 d) (nth 5 d)) addr))
                  (implies (and (fn-mm-tot-p tot)
                                (equal (fn-mo-reopen-cfg owner-cfg)
                                       (fn-mo-reopen-cfg
                                        (fn-mo-serve-cfg trigger
                                                         (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr d))
                                                                                  nursery)
                                                         live cold profile config))))
                           (<= (fn-mm-reopen-need profile img owner-cfg tot) limit)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-mo-serve-reservation)
                           (fn-mo-serve-decide fn-mo-serve-limit fn-mo-serve-dynamic fn-mo-serve-cfg
                            fn-mm-reopen-need fn-mm-least-observation fn-mm-tot-p fn-heap-nursery-trigger
                            fn-heap-mb-of fn-mo-reopen-cfg fn-heap-reservation-octets fn-mo-serve-threads
                            fn-mo-serve-reopen-reads-its-coordinates floor fn-heap-profile-word fn-heap-stack-kib fn-heap-stack-octets))
           :use ((:instance fn-mo-serve-decide-heap-facts)
                 (:instance fn-mo-serve-reopen-reads-its-coordinates (cfg owner-cfg))
                 (:instance fn-mo-serve-reopen-reads-its-coordinates
                  (cfg (fn-mo-serve-cfg trigger
                         (fn-heap-nursery-trigger
                          (* *fn-heap-mib* (fn-heap-mb-of (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools)))
                          nursery)
                         live cold profile config)))))))

; KEYSTONE (L-RUN-LAUNCH), the statement its teeth bind: fn-mo-serve-launch-fits-the-address-space-at-the-decision with the
; decision written out.
(defthm fn-mo-serve-launch-fits-the-address-space
  (implies (equal (car (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot pools pool-threads)) :heap)
           (and (natp (fn-mo-serve-limit resident pools))
                  (implies (natp (fn-mm-least-observation address)) (<= (fn-heap-reservation-octets (cadr (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot pools pool-threads)) core (nth 4 (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot pools pool-threads)) (nth 5 (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot pools pool-threads))) (fn-mm-least-observation address)))
                  (implies (and (fn-mm-tot-p tot)
                                (equal (fn-mo-reopen-cfg owner-cfg)
                                       (fn-mo-reopen-cfg
                                        (fn-mo-serve-cfg trigger
                                                         (fn-heap-nursery-trigger (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot pools pool-threads))))
                                                                                  nursery)
                                                         live cold profile config))))
                           (<= (fn-mm-reopen-need profile img owner-cfg tot) (fn-mo-serve-limit resident pools)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(nfix fn-heap-mb-of-natp) (theory 'minimal-theory))
           :use (fn-mo-serve-launch-fits-the-address-space-at-the-decision fn-mo-serve-decide-heap-mb))))

