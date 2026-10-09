; fn: a command's reservation states what the command holds (Builder M,
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
;                --replay', `health', `inspect', `inspect-group'): the
;                model's reopen of the totals they observe
;                (books/memory-model.lisp fn-mm-reopen-need of
;                fn-mm-observed-tot), today's figure while the totals are
;                unobserved;
;   :store-less  commands that hold no store: `init' (its staged empty
;                store, fn-heap-storeless-figure-holds-the-empty-open), a
;                stopped `status' (the checkpoint header and lstat only,
;                host/native/io.lisp fnn-command-stopped-status),
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
    (:status . :reads) (:health . :reads) (:inspect . :reads) (:inspect-group . :reads)
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

; The class of a command: the table's, except that `status' without
; `--replay' reads the checkpoint header and opens nothing.
(defun fn-heap-command-growth (action replayp)
  (declare (xargs :guard t))
  (if (and (equal action :status) (not replayp))
      :store-less
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

; IMG observed by the probe: (FILE ANON THREAD), each natural; NIL when the
; system does not report it.
(defun fn-mm-img-p (img)
  (declare (xargs :guard t))
  (and (true-listp img) (equal (len img) 3)
       (natp (nth 0 img)) (natp (nth 1 img)) (natp (nth 2 img))))

;; THE READ.  A read-only command serves nothing, so it is held to the
;; reopen of the store it observes alone (fn-mm-reopen-need: the image, the
;; owner's state, the open's workspace over the log and records,
;; maintenance and failure headroom), never to the serving sum (whose
;; in-flight term the profile sizes).  The heap holds the core's dynamic
;; content and that reopen with the collector's room; the reopen is held
;; to the least RESIDENT observation (physical memory, memory.max), the
;; reservation (heap, core file, the node's threads' stacks) to the least
;; ADDRESS-SPACE one (RLIMIT_AS, RLIMIT_DATA) only.  The answer is in the
;; reservation's shape: (:heap MB WORD LIMIT-MB STACK-KIB THREADS), or a
;; refusal by name with its figures in MB.
(defun fn-mo-read-need (profile img nursery totals)
  (declare (xargs :guard t))
  (fn-mm-reopen-need profile img (fn-mo-read-cfg nursery) totals))

(defun fn-mo-read-dynamic (profile img core nursery totals)
  (declare (xargs :guard t))
  (fn-heap-with-nursery (+ (fn-heap-core-dynamic core) (fn-mo-read-need profile img nursery totals))
                        nursery))

(defun fn-mo-read-reservation (profile img core nursery totals)
  (declare (xargs :guard t))
  (fn-heap-reservation-octets (fn-heap-mb-of (fn-mo-read-dynamic profile img core nursery totals))
                              core (fn-heap-stack-kib profile) (fn-heap-thread-count 0)))

(defun fn-mo-read-decide (profile img core nursery totals resident address)
  (declare (xargs :guard t))
  (let ((need (fn-mo-read-need profile img nursery totals))
        (limit (fn-mm-least-observation resident))
        (a (fn-mm-least-observation address))
        (res (fn-mo-read-reservation profile img core nursery totals)))
    (cond ((not (natp limit)) (list :refused :machine-memory-unobserved 0 0))
          ((< limit need)
           (list :refused :machine-cannot-hold-the-store (fn-heap-mb-of need)
                 (floor limit *fn-heap-mib*)))
          ((and (natp a) (< a res))
           (list :refused :address-space-cannot-hold-the-reservation (fn-heap-mb-of res)
                 (floor a *fn-heap-mib*)))
          (t (list :heap (fn-heap-mb-of (fn-mo-read-dynamic profile img core nursery totals))
                   (fn-heap-profile-word profile) (floor limit *fn-heap-mib*)
                   (fn-heap-stack-kib profile) (fn-heap-thread-count 0))))))

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
; heap.lisp fnn-heap-reservation and fnn-heap-print-store-line).  RESIDENT
; and ADDRESS are the observations the model compares resident memory and
; the reservation with (physical memory and memory.max; RLIMIT_AS and
; RLIMIT_DATA); OBSERVATIONS all of them, as today's decision takes them.
(defun fn-heap-command-decide (action replayp profile core nursery observations connections
                                      observed totals img resident address)
  (declare (xargs :guard t))
  (let ((class (fn-heap-command-growth action replayp)))
    (cond ((equal class :store-less)
           (fn-heap-reserve-operation-decide :init profile core nursery observations
                                             connections nil))
          ((and (equal class :reads) (fn-mm-tot-p totals) (fn-mm-img-p img))
           (fn-mo-read-decide profile img core nursery totals resident address))
          (t (fn-heap-reserve-operation-decide action profile core nursery observations
                                               connections observed)))))

; The line the probe prints: the reservation's, and for a read-only command
; sized without observed totals the totals it could not see, by name (the
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

(defun fn-heap-command-line (decision action replayp totals img)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-mm-tot-p fn-mm-img-p
                                                            fn-heap-command-growth fn-mo-unseen
                                                            fn-mo-unseen-words fn-mo-read-refusal-line
                                                            fn-heap-reserve-report-line)))))
  (let ((line (if (and (consp decision) (equal (car decision) :refused) (consp (cdr decision))
                       (member-equal (cadr decision) '(:machine-cannot-hold-the-store
                                                       :address-space-cannot-hold-the-reservation)))
                  (fn-mo-read-refusal-line decision)
                (fn-heap-reserve-report-line decision))))
    (if (equal (fn-heap-command-growth action replayp) :reads)
        (cond ((not (fn-mm-tot-p totals))
               (concatenate 'string line " totals=unobserved:"
                            (fn-mo-unseen-words (fn-mo-unseen totals))))
              ((not (fn-mm-img-p img)) (concatenate 'string line " img=unobserved"))
              (t line))
      line)))

; -----------------------------------------------------------------------------
; THE KEYSTONES.  K6: a stopped status holds no store; K7: an accepted read
; holds the observed store's reopen within the resident observations and
; its reservation within the address-space ones; K8: a read refuses only by
; them; and the dispatch: the reads branch is the read decision, every
; other class today's (which holds the profile's store by
; fn-heap-operation-decide-holds-the-store).
(defthm fn-heap-stopped-status-holds-no-store
  (implies (not replayp)
           (equal (fn-heap-command-decide :status replayp profile core nursery observations connections
                                          observed totals img resident address)
                  (fn-heap-reserve-operation-decide :init profile core nursery observations connections nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-command-decide fn-heap-command-growth)
                                             (theory 'minimal-theory)))))
(defthm fn-heap-command-decide-reads-is-the-read-decision
  (implies (and (equal (fn-heap-command-growth action replayp) :reads)
                (fn-mm-tot-p totals) (fn-mm-img-p img))
           (equal (fn-heap-command-decide action replayp profile core nursery observations connections
                                          observed totals img resident address)
                  (fn-mo-read-decide profile img core nursery totals resident address)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-command-decide) (theory 'minimal-theory)))))
(defthm fn-heap-command-decide-otherwise-is-todays
  (implies (and (not (equal (fn-heap-command-growth action replayp) :store-less))
                (not (and (equal (fn-heap-command-growth action replayp) :reads)
                          (fn-mm-tot-p totals) (fn-mm-img-p img))))
           (equal (fn-heap-command-decide action replayp profile core nursery observations connections
                                          observed totals img resident address)
                  (fn-heap-reserve-operation-decide action profile core nursery observations connections
                                                    observed)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-command-decide) (theory 'minimal-theory)))))
(defthm fn-mo-read-holds-the-observed-store
  (implies (equal (car (fn-mo-read-decide profile img core nursery totals resident address)) :heap)
           (and (natp (fn-mm-least-observation resident))
                (<= (fn-mo-read-need profile img nursery totals) (fn-mm-least-observation resident))
                (<= (+ (fn-heap-core-dynamic core) (fn-mo-read-need profile img nursery totals))
                    (* *fn-heap-mib*
                       (fn-heap-decision-mb
                        (fn-mo-read-decide profile img core nursery totals resident address))))
                (implies (natp (fn-mm-least-observation address))
                         (<= (fn-mo-read-reservation profile img core nursery totals)
                             (fn-mm-least-observation address)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mo-read-decide fn-heap-decision-mb)
                                  (fn-mo-read-need fn-mo-read-reservation fn-heap-mb-of
                                   fn-mm-least-observation fn-heap-with-nursery fn-heap-core-dynamic
                                   fn-heap-profile-word fn-heap-stack-kib fn-heap-thread-count))
           :use ((:instance fn-heap-mb-of-covers
                            (octets (fn-mo-read-dynamic profile img core nursery totals)))
                 (:instance fn-heap-with-nursery-covers-base
                            (base (+ (fn-heap-core-dynamic core) (fn-mo-read-need profile img nursery totals))))))))
; A read's need is never zero (the failure headroom alone is not), so a
; need within the resident observation names one.
(defthm fn-mo-read-need-positive
  (< 0 (fn-mo-read-need profile img nursery totals))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-mo-read-need fn-mm-reopen-need)
                                  (fn-mm-base fn-mm-owner fn-mm-maintenance
                                   fn-heap-store-open-octets))
           :use ((:instance fn-mm-terms-natp (cfg (fn-mo-read-cfg nursery)) (tot totals))))))
(defthm fn-mo-read-refuses-only-by-the-model
  (implies (and (<= (fn-mo-read-need profile img nursery totals) (fn-mm-least-observation resident))
                (or (not (natp (fn-mm-least-observation address)))
                    (<= (fn-mo-read-reservation profile img core nursery totals)
                        (fn-mm-least-observation address))))
           (equal (car (fn-mo-read-decide profile img core nursery totals resident address)) :heap))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mo-read-decide)
                                  (fn-mo-read-need fn-mo-read-reservation fn-mo-read-dynamic
                                   fn-mm-least-observation)))))
