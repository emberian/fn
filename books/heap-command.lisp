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

; The totals a decision could not see, named in its line.
(defconst *fn-mo-unseen-today*
  '(:arena :hcharge :memberships :events :log :history :charge :residency))

(defun fn-mo-unseen (totals)
  (declare (xargs :guard t))
  (if (fn-mm-tot-p totals) nil *fn-mo-unseen-today*))

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
;; that picks the dynamic space charges it resident.  CARD is the image's
;; card size (sb-vm:gencgc-card-bytes), observed by the probe.
(defun fn-mo-card-octets (dynamic card)
  (declare (xargs :guard t))
  (if (posp card)
      (floor (+ (nfix dynamic) (- card 1)) card)
    0))

;; THE READ.  A read-only command serves nothing, so it is held to the
;; reopen of the store it observes alone (fn-mm-reopen-need: the image, the
;; owner's state, the open's workspace over the log and records,
;; maintenance and failure headroom) and the configuration history its
;; open loads, never to the serving sum (whose in-flight term the profile
;; sizes).  The heap holds the core's dynamic content and that need with the
;; collector's room; the need and the dynamic space's card table are held
;; to the least RESIDENT observation (physical memory, memory.max), the
;; reservation (heap, core file, the node's threads' stacks) to the least
;; ADDRESS-SPACE one (RLIMIT_AS, RLIMIT_DATA) only.  The answer is in the
;; reservation's shape: (:heap MB WORD LIMIT-MB STACK-KIB THREADS), or a
;; refusal by name with its figures in MB.
(defun fn-mo-read-need (profile img nursery totals config-octets)
  (declare (xargs :guard t))
  (+ (fn-mm-reopen-need profile img (fn-mo-read-cfg nursery) totals)
     (fn-mo-config-heap config-octets)))

(defun fn-mo-read-dynamic (profile img core nursery totals config-octets)
  (declare (xargs :guard t))
  (fn-heap-with-nursery (+ (fn-heap-core-dynamic core)
                           (fn-mo-read-need profile img nursery totals config-octets))
                        nursery))

(defun fn-mo-read-resident (profile img core nursery totals config-octets card)
  (declare (xargs :guard t))
  (+ (fn-mo-read-need profile img nursery totals config-octets)
     (fn-mo-card-octets (* *fn-heap-mib*
                           (fn-heap-mb-of (fn-mo-read-dynamic profile img core nursery totals
                                                              config-octets)))
                        card)))

(defun fn-mo-read-reservation (profile img core nursery totals config-octets)
  (declare (xargs :guard t))
  (fn-heap-reservation-octets (fn-heap-mb-of (fn-mo-read-dynamic profile img core nursery totals
                                                                 config-octets))
                              core (fn-heap-stack-kib profile) (fn-heap-thread-count 0)))

(defun fn-mo-read-decide (profile img core nursery totals config-octets card resident address)
  (declare (xargs :guard t))
  (let ((need (fn-mo-read-resident profile img core nursery totals config-octets card))
        (limit (fn-mm-least-observation resident))
        (a (fn-mm-least-observation address))
        (res (fn-mo-read-reservation profile img core nursery totals config-octets)))
    (cond ((not (natp limit)) (list :refused :machine-memory-unobserved 0 0))
          ((< limit need)
           (list :refused :machine-cannot-hold-the-store (fn-heap-mb-of need)
                 (floor limit *fn-heap-mib*)))
          ((and (natp a) (< a res))
           (list :refused :address-space-cannot-hold-the-reservation (fn-heap-mb-of res)
                 (floor a *fn-heap-mib*)))
          (t (list :heap (fn-heap-mb-of (fn-mo-read-dynamic profile img core nursery totals
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
(defun fn-mo-read-observed-p (totals img config-octets card)
  (declare (xargs :guard t))
  (and (fn-mm-tot-p totals) (fn-mm-img-p img) (natp config-octets) (posp card)))

(defun fn-heap-command-decide (action command replayp profile core nursery observations connections
                                      observed totals img config-octets card resident address)
  (declare (xargs :guard t))
  (let ((class (fn-heap-command-growth action command replayp)))
    (cond ((equal class :store-less)
           (fn-heap-reserve-operation-decide :init profile core nursery observations
                                             connections nil))
          ((and (equal class :header) (natp config-octets))
           (fn-mo-header-decide profile core nursery observations connections config-octets))
          ((and (equal class :reads) (fn-mo-read-observed-p totals img config-octets card))
           (fn-mo-read-decide profile img core nursery totals config-octets card resident address))
          (t (fn-heap-reserve-operation-decide action profile core nursery observations
                                               connections observed)))))

; The line the probe prints: the reservation's, and for a command sized
; without what its class reads, what it could not see, by name (the
; launcher reads `heap=' and `stack=' and nothing after).
(defun fn-mo-unseen-word (field)
  (declare (xargs :guard t))
  (case field
    (:records "records") (:arena "arena") (:hcharge "hcharge") (:memberships "memberships")
    (:events "events") (:log "log") (:history "history") (:charge "charge")
    (:residency "residency") (otherwise "?")))

(defun fn-mo-unseen-words (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (concatenate 'string (fn-mo-unseen-word (car fields))
                   (if (consp (cdr fields)) "," "")
                   (fn-mo-unseen-words (cdr fields)))
    ""))

(defthm fn-mo-unseen-words-stringp
  (stringp (fn-mo-unseen-words fields))
  :rule-classes :type-prescription)

;; A read's own refusals, by name (fn-heap-report-line knows today's).
(defun fn-mo-read-refusal-line (decision)
  (declare (xargs :guard t))
  (let ((d (true-list-fix decision)))
    (concatenate 'string "refused "
                 (if (equal (nth 1 d) :machine-cannot-hold-the-store)
                     "machine-cannot-hold-the-store need="
                   "address-space-cannot-hold-the-reservation reservation=")
                 (fn-heap-decimal (nth 2 d))
                 (if (equal (nth 1 d) :machine-cannot-hold-the-store) " MB machine=" " MB address-space=")
                 (fn-heap-decimal (nth 3 d)) " MB")))

(defun fn-mo-unseen-suffix (class totals img config-octets card)
  (declare (xargs :guard t))
  (cond ((and (equal class :header) (not (natp config-octets))) " config=unobserved")
        ((not (equal class :reads)) "")
        ((not (fn-mm-tot-p totals))
         (concatenate 'string " totals=unobserved:" (fn-mo-unseen-words (fn-mo-unseen totals))))
        ((not (fn-mm-img-p img)) " img=unobserved")
        ((not (natp config-octets)) " config=unobserved")
        ((not (posp card)) " card=unobserved")
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
; configuration history it loads, no store; K7: an accepted read holds the
; observed store's reopen and its card table within the resident
; observations, its heap the core's content and the reopen, its
; reservation within the address-space ones; K8: a read refuses only by
; them; and the dispatch: every other case is today's decision (which
; holds the profile's store by fn-heap-operation-decide-holds-the-store).
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

(defthm fn-heap-command-decide-reads-is-the-read-decision
  (implies (and (equal (fn-heap-command-growth action command replayp) :reads)
                (fn-mo-read-observed-p totals img config-octets card))
           (equal (fn-heap-command-decide action command replayp profile core nursery observations
                                          connections observed totals img config-octets card
                                          resident address)
                  (fn-mo-read-decide profile img core nursery totals config-octets card resident
                                     address)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-command-decide) (theory 'minimal-theory)))))

(defthm fn-heap-command-decide-otherwise-is-todays
  (implies (and (not (equal (fn-heap-command-growth action command replayp) :store-less))
                (not (and (equal (fn-heap-command-growth action command replayp) :header)
                          (natp config-octets)))
                (not (and (equal (fn-heap-command-growth action command replayp) :reads)
                          (fn-mo-read-observed-p totals img config-octets card))))
           (equal (fn-heap-command-decide action command replayp profile core nursery observations
                                          connections observed totals img config-octets card
                                          resident address)
                  (fn-heap-reserve-operation-decide action profile core nursery observations
                                                    connections observed)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-command-decide) (theory 'minimal-theory)))))

(defthm fn-mo-read-holds-the-observed-store
  (implies (equal (car (fn-mo-read-decide profile img core nursery totals config-octets card
                                          resident address))
                  :heap)
           (and (natp (fn-mm-least-observation resident))
                (<= (fn-mo-read-resident profile img core nursery totals config-octets card)
                    (fn-mm-least-observation resident))
                (<= (+ (fn-heap-core-dynamic core)
                       (fn-mo-read-need profile img nursery totals config-octets))
                    (* *fn-heap-mib*
                       (fn-heap-decision-mb
                        (fn-mo-read-decide profile img core nursery totals config-octets card
                                           resident address))))
                (implies (natp (fn-mm-least-observation address))
                         (<= (fn-mo-read-reservation profile img core nursery totals config-octets)
                             (fn-mm-least-observation address)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mo-read-decide fn-heap-decision-mb)
                                  (fn-mo-read-need fn-mo-read-resident fn-mo-read-reservation
                                   fn-heap-mb-of fn-mm-least-observation fn-heap-with-nursery
                                   fn-heap-core-dynamic fn-heap-profile-word fn-heap-stack-kib
                                   fn-heap-thread-count))
           :use ((:instance fn-heap-mb-of-covers
                            (octets (fn-mo-read-dynamic profile img core nursery totals config-octets)))
                 (:instance fn-heap-with-nursery-covers-base
                            (base (+ (fn-heap-core-dynamic core)
                                     (fn-mo-read-need profile img nursery totals config-octets))))))))

; A read's resident need is never zero (the failure headroom alone is not),
; so a need within the resident observation names one.
(defthm fn-mo-read-resident-positive
  (< 0 (fn-mo-read-resident profile img core nursery totals config-octets card))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-mo-read-resident fn-mo-read-need fn-mm-reopen-need
                                   fn-mo-config-heap fn-mo-card-octets)
                                  (fn-mm-base fn-mm-owner fn-mm-maintenance
                                   fn-heap-store-open-octets fn-mo-read-dynamic fn-heap-mb-of))
           :use ((:instance fn-mm-terms-natp (cfg (fn-mo-read-cfg nursery)) (tot totals))))))

(defthm fn-mo-read-refuses-only-by-the-model
  (implies (and (<= (fn-mo-read-resident profile img core nursery totals config-octets card)
                    (fn-mm-least-observation resident))
                (or (not (natp (fn-mm-least-observation address)))
                    (<= (fn-mo-read-reservation profile img core nursery totals config-octets)
                        (fn-mm-least-observation address))))
           (equal (car (fn-mo-read-decide profile img core nursery totals config-octets card
                                          resident address))
                  :heap))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mo-read-decide)
                                  (fn-mo-read-resident fn-mo-read-reservation fn-mo-read-dynamic
                                   fn-mm-least-observation)))))
