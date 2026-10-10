;; fn: a command's reservation states what the command holds (Builder M,
; landing 2, the observation form; RUNTIME-MODEL section 4).
;
; Every native action the operator surface names
; (books/native-operator.lisp fn-native-operator-result-native-action;
; tests/test_heap_action_growth.py checks each has a row) is one of:
;   :serves      `run': the owner, sized at the profile's bounds with no
;                observation (ADMISSION-RESERVES-NOT-REOPEN);
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
(defun fn-mo-observed-totals (hdr suffix)
  (declare (xargs :guard t))
  (if (and (fn-mm-tot-p hdr) (fn-mm-tot-p suffix))
      (fn-mm-observed-tot hdr suffix)
    nil))

; A read-only command serves nothing: no connection, no TLS, no handshake,
; no cold-read pool, no cache, no reclaim, the collector at the nursery.
(defun fn-mo-read-cfg (nursery)
  (declare (xargs :guard t))
  (list 0 nil (nfix nursery) (nfix nursery) nil 0 0 0 nil 0))

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
;; *fn-mo-config-heap-per-octet* heap octets an octet: a 16-octet cons a list
;; element, twice (the list and its decoding), the vector beside it.
;; O-CONFIG (owed, measured in landing 4): the overlay's heap is within it.
(defconst *fn-mo-config-heap-per-octet* 33)

(defun fn-mo-config-heap (config-octets)
  (declare (xargs :guard t))
  (* *fn-mo-config-heap-per-octet* (nfix config-octets)))

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
  (let ((cfg (fn-mo-read-cfg nursery)))
    (+ (if (equal class :reads)
           (fn-mm-reopen-need profile img cfg tot)
         (max (fn-mm-sum profile img cfg tot) (fn-mm-reopen-need profile img cfg tot)))
       (fn-mo-config-heap config-octets)
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

(defun fn-mo-img-observed (core-octets status-octets stack-kib tls-octets)
  (declare (xargs :guard t))
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
;; a store the profile admits.  The sound bound is the equation at the
;; profile's bound (books/memory-model.lisp fn-mm-profile-bound-tot: T x G
;; memberships, 20 x H header charge, the log at T x (78 + 1,083 + 261 G) +
;; H); on fn-core's image (reads and writers; the adapter in brackets):
;; small 2,427 MB (575), filled 26,684 MB (7,392), development 52,400 MB
;; (2,377), scale 1.6 TB (20 GB).  Its line says so.
(defun fn-mo-offline-adapter-decide (action profile core nursery observations connections observed)
  (declare (xargs :guard t))
  (fn-heap-reserve-operation-decide action profile core nursery observations connections observed))

(defun fn-heap-command-decide (action command replayp profile core nursery observations connections
                                      observed totals img config-octets card resident address)
  (declare (xargs :guard t))
  (let ((class (fn-heap-command-growth action command replayp)))
    (cond ((equal class :store-less)
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
          (t (concatenate 'string "refused address-space-cannot-hold-the-reservation reservation="
                          (fn-heap-decimal (nth 2 d)) " MB address-space="
                          (fn-heap-decimal (nth 3 d)) " MB")))))

; What a decision was sized without, by name: a store-opening command the
; adapter decided says so and what the equation could not see.
(defconst *fn-mo-adapter-words*
  " sized by the offline adapter (pre-payload-only figure, under-bounds the store): ")

(defun fn-mo-unseen-suffix (class totals img config-octets card)
  (declare (xargs :guard t))
  (cond ((and (equal class :header) (not (natp config-octets))) " config=unobserved")
        ((not (fn-mo-store-opening-p class)) "")
        ((not (fn-mm-tot-p totals))
         (concatenate 'string *fn-mo-adapter-words* "header totals unseen"))
        ((not (fn-mm-img-p img)) (concatenate 'string *fn-mo-adapter-words* "img unobserved"))
        ((not (natp config-octets)) (concatenate 'string *fn-mo-adapter-words* "config unobserved"))
        ((not (posp card)) (concatenate 'string *fn-mo-adapter-words* "card unobserved"))
        (t "")))

(defun fn-heap-command-line (decision action command replayp totals img config-octets card)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-mo-unseen-suffix fn-heap-command-growth
                                                            fn-mo-read-refusal-line
                                                            fn-heap-reserve-report-line)))))
  (concatenate 'string
               (if (and (consp decision) (equal (car decision) :refused) (consp (cdr decision))
                        (member-equal (cadr decision) '(:machine-cannot-hold-the-store
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
           :use ((:instance fn-mm-sum-grows-with-the-store (cfg (fn-mo-read-cfg nursery)))
                 (:instance fn-mm-reopen-need-monotone (cfg (fn-mo-read-cfg nursery))
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
           :use ((:instance fn-mm-terms-natp (cfg (fn-mo-read-cfg nursery)))))))

(defthm fn-mo-read-refuses-only-by-the-model
  (implies (and (natp (fn-mm-least-observation resident))
                (<= (fn-mo-read-resident action class profile img core nursery tot config-octets card)
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
                                   fn-mm-least-observation)))))

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
