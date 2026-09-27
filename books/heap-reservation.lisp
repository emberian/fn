; fn: the whole reservation a node makes, heap and thread stacks, decided
; before the image starts (lane image-floor, 2026-09-26; HST-025; an extension
; of PRF-198, books/heap-figure.lisp, which it calls and does not restate).
;
; SBCL reserves, besides the dynamic space, one region per thread: the control
; stack (`--control-stack-size', every thread the same) and the runtime's own
; per-thread areas (binding stack, alien stack, thread-local storage and guard
; pages).  The saved image's launcher passed 64 MiB of control stack, so each
; thread reserved 66.5 MiB (hbox, SBCL 2.6.8: 68,132 KiB per thread at
; --tls-limit 16384).  On OpenBSD a reservation counts against the login
; class's datasize: at 1,536 MiB and a 256 MB dynamic space the fourteenth
; thread was refused ("mmap: Cannot allocate memory", the VM, 2026-09-26), so
; a node with max-connections 32 failed its fifteenth client, not its start.
;
; THE STACK a thread needs is measured, not guessed, and since lane
; served-line-iterative (2026-09-26, PRF-218) it no longer grows with the
; article: the served path's per-line and per-octet recursions
; (fn-post-body-octets, fn-nntp-stuff-lines, fn-wire-list-length) are loops,
; and the least control stack is 142 KiB for an article of 16 lines, of
; 2,000,000 lines and of one 4 MiB line alike (its record, section 5; at 126
; KiB it is `init' that faults).  Before it the need was 144 KiB + 32 octets
; per line (planning/evidence/image-floor-2026-09-26.md section 4) and this
; figure carried a per-line term.  The figure is a constant 1,024 KiB: the
; value served-line-iterative's native witness serves 2,000,000 lines at on
; both images, 7 times the measured floor.
;
; THE THREADS: the owner's client workers (one per accepted connection up to
; the configuration's max-connections), the local control clients
; (fn-native-control-max-active-clients), and the fixed ones: the main
; thread, SBCL's finalizer, the service log writer, the checkpoint
; publisher, the outbound feed and pull workers, the control accept loop,
; the TLS, implicit-TLS and extra plain listeners; twelve with two spare.
;
; THE RUNTIME per thread beyond the control stack: 2,596 KiB on hbox (SBCL
; 2.6.8, from VmSize), at most 3 MiB on OpenBSD (SBCL 2.6.3: 64 more threads
; of a 1 MiB stack per 256 MiB more datasize); the figure takes 4 MiB.  THE
; IMAGE's own mappings outside the dynamic space (static, read-only and text
; spaces, 80 MB of the lane's 192 MB core) are at most the core file, which
; the reservation counts once more beside heap-figure's heap.
;
; The decision (`fn-heap-reserve-decide'): heap-figure's decision, and when
; that accepts an admitted profile, the stack for its largest article and
; the total HEAP + CORE + THREADS x (STACK + RUNTIME), refused by name when
; it exceeds the machine (the least observation, as heap-figure's).
;
;   (:heap MB WORD MACHINE-MB STACK-KB THREADS)
;   (:refused REASON MB MACHINE-MB)      heap-figure's refusals, unchanged
;   (:refused :machine-cannot-hold-threads TOTAL-MB MACHINE-MB)
;
; The host entry: host/native/heap.lisp `fnn-heap-reservation'.

(in-package "ACL2")
(include-book "heap-figure")
(include-book "native-control")

(defconst *fn-heap-stack-octets* (* 1024 1024))
(defconst *fn-heap-thread-runtime-octets* (* 4 *fn-heap-mib*))
(defconst *fn-heap-fixed-threads* 12)
; The stack when no store profile is named (help, --version): SBCL's own
; default, 2 MiB.
(defconst *fn-heap-default-stack-kib* 2048)

; The control stack of every thread: the constant above, whatever the
; profile (PROFILE stays an argument: the figure is the profile's, and a
; future served path that needs more for some profile says so here).
(defun fn-heap-stack-octets (profile)
  (declare (xargs :guard t) (ignore profile))
  *fn-heap-stack-octets*)

; Octets rounded up to SBCL's kilobytes (KiB: `--control-stack-size NKB').
(defun fn-heap-kib-of (octets)
  (declare (xargs :guard t))
  (floor (+ (nfix octets) 1023) 1024))

(defun fn-heap-stack-kib (profile)
  (declare (xargs :guard t))
  (fn-heap-kib-of (fn-heap-stack-octets profile)))

;; THE THREADS since connection-multiplexing (PRF-223, host/native/mux.lisp):
;; a served connection is no thread but a record on one of the I/O loops, so
;; the node runs the fixed threads, the loops and the control clients,
;; whatever its connections (CONNECTIONS stays an argument: the reservation
;; is the run's, and the connections' heap parts are connection-budget's).
;; Before this lane the reservation still counted one thread per connection
;; (32 x 5 MiB at the default capacity).  The host's thread count for the
;; connection budget is this one (fnn-mux-thread-count).
(defconst *fn-heap-mux-loops* 2)

(defun fn-heap-mux-loops ()
  (declare (xargs :guard t))
  *fn-heap-mux-loops*)

(defun fn-heap-thread-count (connections)
  (declare (xargs :guard t) (ignore connections))
  (+ *fn-heap-mux-loops* (fn-native-control-max-active-clients)
     *fn-heap-fixed-threads*))

(defun fn-heap-reservation-octets (mb core stack-kib threads)
  (declare (xargs :guard t))
  (+ (* *fn-heap-mib* (nfix mb))
     (fn-heap-core-file core)
     (* (nfix threads) (+ (* 1024 (nfix stack-kib)) *fn-heap-thread-runtime-octets*))))

;; A command naming no store (PKT-686 item 3): heap-figure's store-less heap,
;; one thread of SBCL's default stack, and the whole checked against the
;; machine as for a store's reservation (heap-figure's store-less figure is
;; sized so that this holds: `fn-heap-storeless-decide-is-small-and-fits').
(defun fn-heap-reserve-storeless (d core observations)
  (declare (xargs :guard (true-listp d)))
  (let ((total (fn-heap-reservation-octets (fn-heap-decision-mb d) core
                                           *fn-heap-default-stack-kib* 1)))
    (if (<= total (fn-heap-machine-octets observations))
        (list :heap (fn-heap-decision-mb d) (nth 2 d) (nth 3 d)
              *fn-heap-default-stack-kib* 1)
      (list :refused :machine-cannot-hold-threads (fn-heap-mb-of total) (nth 3 d)))))

; heap-figure's one-thread allowance is this book's default stack and runtime.
(defthm fn-heap-storeless-thread-is-one-default-thread
  (equal (+ (* 1024 *fn-heap-default-stack-kib*) *fn-heap-thread-runtime-octets*)
         *fn-heap-storeless-thread-octets*)
  :rule-classes nil)

(defthm fn-heap-decide-true-listp
  (true-listp (fn-heap-decide profile core nursery observations))
  :rule-classes :type-prescription)

(defun fn-heap-reserve-decide (profile core nursery observations connections)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-heap-decide
                                                            fn-bs-profile-admittedp
                                                            fn-heap-stack-kib
                                                            fn-heap-thread-count
                                                            fn-heap-reservation-octets
                                                            fn-heap-machine-octets)))))
  (let ((d (fn-heap-decide profile core nursery observations)))
    (cond ((not (equal (car d) :heap)) d)
          ((not (fn-bs-profile-admittedp profile))
           (fn-heap-reserve-storeless d core observations))
          (t
           (let* ((stack (fn-heap-stack-kib profile))
                  (threads (fn-heap-thread-count connections))
                  (total (fn-heap-reservation-octets (fn-heap-decision-mb d)
                                                     core stack threads))
                  (machine (fn-heap-machine-octets observations)))
             (if (<= total machine)
                 (list :heap (fn-heap-decision-mb d) (nth 2 d) (nth 3 d)
                       stack threads)
               (list :refused :machine-cannot-hold-threads
                     (fn-heap-mb-of total) (nth 3 d))))))))

(defun fn-heap-reserve-stack-kib (decision)
  (declare (xargs :guard t))
  (if (and (consp decision) (true-listp decision) (equal (car decision) :heap))
      (nfix (nth 4 decision))
    0))

(defun fn-heap-reserve-threads (decision)
  (declare (xargs :guard t))
  (if (and (consp decision) (true-listp decision) (equal (car decision) :heap))
      (nfix (nth 5 decision))
    0))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-heap-kib-of-covers
  (<= (nfix octets) (* 1024 (fn-heap-kib-of octets)))
  :rule-classes :linear)

(defthm fn-heap-decide-heap-shape
  (implies (equal (car (fn-heap-decide profile core nursery observations)) :heap)
           (natp (fn-heap-decision-mb (fn-heap-decide profile core nursery
                                                      observations))))
  :rule-classes nil)

(in-theory (disable fn-heap-kib-of))

; The refusal is exact: past heap-figure's acceptance, an admitted profile is
; refused by name exactly when the whole reservation exceeds the machine.
(defthm fn-heap-reserve-decide-refuses-exactly-past-the-machine
  (let ((d (fn-heap-decide profile core nursery observations)))
    (implies (and (fn-bs-profile-admittedp profile)
                  (equal (car d) :heap))
             (equal (fn-heap-reserve-decide profile core nursery observations
                                            connections)
                    (let ((total (fn-heap-reservation-octets
                                  (fn-heap-decision-mb d) core
                                  (fn-heap-stack-kib profile)
                                  (fn-heap-thread-count connections))))
                      (if (<= total (fn-heap-machine-octets observations))
                          (list :heap (fn-heap-decision-mb d) (nth 2 d) (nth 3 d)
                                (fn-heap-stack-kib profile)
                                (fn-heap-thread-count connections))
                        (list :refused :machine-cannot-hold-threads
                              (fn-heap-mb-of total) (nth 3 d)))))))
  :hints (("Goal" :in-theory (e/d (fn-heap-reserve-decide)
                                  (fn-heap-decide fn-bs-profile-admittedp
                                   fn-heap-decide-refuses-exactly-past-the-machine
                                   fn-heap-decision-mb
                                   fn-heap-reservation-octets
                                   fn-heap-stack-kib fn-heap-thread-count
                                   fn-heap-machine-octets)))))

; heap-figure's refusals pass through unchanged.
(defthm fn-heap-reserve-decide-keeps-heap-figures-refusals
  (implies (not (equal (car (fn-heap-decide profile core nursery observations))
                       :heap))
           (equal (fn-heap-reserve-decide profile core nursery observations
                                          connections)
                  (fn-heap-decide profile core nursery observations)))
  :hints (("Goal" :in-theory (e/d (fn-heap-reserve-decide)
                                  (fn-heap-decide
                                   fn-heap-decide-refuses-exactly-past-the-machine)))))

;; -----------------------------------------------------------------------------
;; The operation's reservation (lane openbsd-release-fixes, PKT-686): the
;; launcher's probe reserves for the command it will run.  The compaction
;; verbs (`store compact', `store reclaim') get heap-figure's operation figure
;; (`fn-heap-operation-decide', six list copies of the history, measured);
;; every other command gets `fn-heap-reserve-decide' unchanged.  The host:
;; host/native/heap.lisp `fnn-heap-reservation', from `fnn-command-heap' (the
;; `heap -- ARGV' probe packaging/fn runs), with ACL2's native action for ARGV.

; The reservation beside a heap decision D (heap-figure's shape).
(defthm fn-heap-operation-decide-true-listp
  (true-listp (fn-heap-operation-decide action profile core nursery observations observed))
  :rule-classes :type-prescription)

(defun fn-heap-reserve-of (d profile core observations connections)
  (declare (xargs :guard (true-listp d)
                  :guard-hints (("Goal" :in-theory (disable fn-bs-profile-admittedp
                                                            fn-heap-stack-kib
                                                            fn-heap-thread-count
                                                            fn-heap-reservation-octets
                                                            fn-heap-machine-octets)))))
  (cond ((not (equal (car d) :heap)) d)
        ((not (fn-bs-profile-admittedp profile))
         (fn-heap-reserve-storeless d core observations))
        (t
         (let* ((stack (fn-heap-stack-kib profile))
                (threads (fn-heap-thread-count connections))
                (total (fn-heap-reservation-octets (fn-heap-decision-mb d)
                                                   core stack threads))
                (machine (fn-heap-machine-octets observations)))
           (if (<= total machine)
               (list :heap (fn-heap-decision-mb d) (nth 2 d) (nth 3 d)
                     stack threads)
             (list :refused :machine-cannot-hold-threads
                   (fn-heap-mb-of total) (nth 3 d)))))))

(defthm fn-heap-reserve-decide-is-reserve-of-heap-decide
  (equal (fn-heap-reserve-decide profile core nursery observations connections)
         (fn-heap-reserve-of (fn-heap-decide profile core nursery observations)
                             profile core observations connections))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-reserve-decide)
                                  (fn-heap-decide
                                   fn-heap-decide-refuses-exactly-past-the-machine)))))

;; OBSERVED (PKT-686 item 1; every command since reservation-after-flip):
;; what the probe observed of the store's history on disk, or NIL;
;; heap-figure's operation figure sizes the command's open by it and the
;; offline verbs' list copies too (fn-heap-operation-history-octets).

(defun fn-heap-reserve-operation-decide (action profile core nursery observations
                                                connections observed)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-heap-operation-decide
                                                            fn-heap-reserve-decide
                                                            fn-heap-reserve-of)))))
  (declare (ignorable action))
  (fn-heap-reserve-of (fn-heap-operation-decide action profile core nursery
                                                observations observed)
                      profile core observations connections))

; Unobserved, every command but the offline verbs reserves exactly as
; fn-heap-reserve-decide.
(defthm fn-heap-reserve-operation-decide-of-a-serve-action
  (implies (and (not (member-equal action *fn-heap-list-actions*))
                (not (equal action :init)))
           (equal (fn-heap-reserve-operation-decide action profile core nursery
                                                    observations connections nil)
                  (fn-heap-reserve-decide profile core nursery observations
                                          connections)))
  :hints (("Goal" :use (fn-heap-reserve-decide-is-reserve-of-heap-decide
                        fn-heap-operation-decide-of-a-serve-action-is-heap-decide)
           :in-theory (union-theories '(fn-heap-reserve-operation-decide)
                                      (theory 'minimal-theory)))))

; An accepted reservation beside a heap decision D is D's heap, and heap,
; core and the threads' stacks fit the machine -- for a store's profile and
; for a command naming none alike (the store-less branch checks the same
; whole; PKT-686 item 3 removed the admitted-profile hypothesis).
(defthm fn-heap-reserve-of-holds-the-decision
  (let ((r (fn-heap-reserve-of d profile core observations connections)))
    (implies (equal (car r) :heap)
             (and (equal (car d) :heap)
                  (equal (fn-heap-decision-mb r) (fn-heap-decision-mb d))
                  (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                         (fn-heap-core-file core)
                         (* (fn-heap-reserve-threads r)
                            (+ (* 1024 (fn-heap-reserve-stack-kib r))
                               *fn-heap-thread-runtime-octets*)))
                      (fn-heap-machine-octets observations)))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-heap-reserve-of fn-heap-reserve-storeless
                                fn-heap-reservation-octets fn-heap-reserve-threads
                                fn-heap-reserve-stack-kib fn-heap-decision-mb
                                car-cons cdr-cons nth-0-cons nth-add1 true-listp
                                (:executable-counterpart nfix) (:executable-counterpart binary-*)
                                (:executable-counterpart binary-+)
                                (:type-prescription fn-heap-stack-kib)
                                (:type-prescription fn-heap-thread-count)
                                nfix natp)
                              (theory 'minimal-theory)))))

; KEYSTONE.  An accepted reservation for an admitted profile is heap-figure's
; heap (so everything heap-figure's keystone holds in it), and beside it
; THREADS threads, at least the I/O loops that serve every connection, the
; control clients and the fixed threads, each with a control stack of at
; least the constant (seven times the served path's measured floor, whatever
; the article); and the whole fits the machine.
; (A hypothesis (natp connections) was removed after proving the weakened
; theorem: since connection-multiplexing no connection is a thread.)
(defthm fn-heap-reserve-decide-holds-every-thread-the-node-runs
  (let ((r (fn-heap-reserve-decide profile core nursery observations connections)))
    (implies (and (fn-bs-profile-admittedp profile)
                  (equal (car r) :heap))
             (and (equal (fn-heap-decision-mb r)
                         (fn-heap-decision-mb
                          (fn-heap-decide profile core nursery observations)))
                  (<= (+ *fn-heap-mux-loops* (fn-native-control-max-active-clients)
                         *fn-heap-fixed-threads*)
                      (fn-heap-reserve-threads r))
                  (<= *fn-heap-stack-octets*
                      (* 1024 (fn-heap-reserve-stack-kib r)))
                  (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                         (fn-heap-core-file core)
                         (* (fn-heap-reserve-threads r)
                            (+ (* 1024 (fn-heap-reserve-stack-kib r))
                               *fn-heap-thread-runtime-octets*)))
                      (fn-heap-machine-octets observations)))))
  :hints (("Goal" :use ((:instance fn-heap-reserve-decide-is-reserve-of-heap-decide)
                        (:instance fn-heap-reserve-of-holds-the-decision
                                   (d (fn-heap-decide profile core nursery observations)))
                        (:instance fn-heap-kib-of-covers
                                   (octets (fn-heap-stack-octets profile))))
           :in-theory (e/d (fn-heap-reserve-of fn-heap-reserve-threads fn-heap-reserve-stack-kib
                            fn-heap-stack-kib fn-heap-thread-count)
                           (fn-heap-reserve-decide fn-heap-decide fn-heap-reserve-storeless
                            fn-bs-profile-admittedp fn-heap-machine-octets
                            fn-heap-reservation-octets fn-heap-reserve-of-holds-the-decision
                            fn-heap-decide-refuses-exactly-past-the-machine
                            fn-native-control-max-active-clients fn-heap-kib-of-covers
                            fn-heap-mb-of)))))

; KEYSTONE (PKT-686).  An accepted reservation is the operation's accepted
; heap figure (so `fn-heap-operation-decide-holds-the-operation' holds in it:
; the command's measured working set on every store the profile admits, and
; for `recover', `compact' and `reclaim' every history within the observed
; octets), and the heap, the image and the threads' stacks fit the machine.
; No profile hypothesis: a command naming no store fits too (item 3).
(defthm fn-heap-reserve-operation-decide-holds-the-operation
  (let ((r (fn-heap-reserve-operation-decide action profile core nursery
                                             observations connections observed))
        (d (fn-heap-operation-decide action profile core nursery observations
                                     observed)))
    (implies (equal (car r) :heap)
             (and (equal (car d) :heap)
                  (equal (fn-heap-decision-mb r) (fn-heap-decision-mb d))
                  (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                         (fn-heap-core-file core)
                         (* (fn-heap-reserve-threads r)
                            (+ (* 1024 (fn-heap-reserve-stack-kib r))
                               *fn-heap-thread-runtime-octets*)))
                      (fn-heap-machine-octets observations)))))
  :hints (("Goal" :use ((:instance fn-heap-reserve-of-holds-the-decision
                                   (d (fn-heap-operation-decide action profile core nursery
                                                                observations observed))))
           :in-theory (union-theories '(fn-heap-reserve-operation-decide)
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The report the probe prints: heap-figure's line, then on acceptance
;   stack=KB KB threads=N
; and the thread refusal's own line.

(defun fn-heap-reserve-accepted-line (heap-line stack threads)
  (declare (xargs :guard (stringp heap-line)))
  (concatenate 'string heap-line " stack=" (fn-heap-decimal stack)
               " KB threads=" (fn-heap-decimal threads)))

(defun fn-heap-reserve-threads-refused-line (mb machine-mb)
  (declare (xargs :guard t))
  (concatenate 'string "refused machine-cannot-hold-threads reservation="
               (fn-heap-decimal mb) " MB machine=" (fn-heap-decimal machine-mb) " MB"))

(defun fn-heap-reserve-report-line (decision)
  (declare (xargs :guard t))
  (let ((d (true-list-fix decision)))
    (cond ((equal (car d) :heap)
           (fn-heap-reserve-accepted-line
            (fn-heap-report-line (list :heap (nth 1 d) (nth 2 d) (nth 3 d)))
            (nth 4 d) (nth 5 d)))
          ((equal (nth 1 d) :machine-cannot-hold-threads)
           (fn-heap-reserve-threads-refused-line (nth 2 d) (nth 3 d)))
          (t (fn-heap-report-line decision)))))

(defthm fn-heap-reserve-report-line-stringp
  (stringp (fn-heap-reserve-report-line decision))
  :rule-classes :type-prescription)

(defthm fn-heap-reserve-thread-refusal-exits-1
  (equal (fn-heap-decision-exit-code
          (list :refused :machine-cannot-hold-threads mb machine-mb))
         1))

; -----------------------------------------------------------------------------
; What `init' writes (PKT-582, in the shape of gpt-6's review of wave 5 of
; 2026-09-26, section 8).  The default preset's history
; bound is the codec's 1 TiB, whose list-representation heap is
; 16 x 2 x 2^40 octets (`heap=73402949 MB', refused on every machine); a
; request that names no capacity field (a bare `init', and every mission:
; books/native-operator.lisp fn-native-mission-request sets only the article
; bound and groups per article) therefore takes its capacity here.
;
; THE BUDGET.  init sizes within an explicit process budget, the least of:
; the physical memory less what the OS and everything else on the machine
; keep (a quarter of it, at least 512 MiB: detected RAM is not all
; available to the service); each limit the process runs under (RLIMIT_DATA,
; RLIMIT_AS, every cgroup memory.max up the tree, which is how systemd's
; MemoryMax and OpenBSD's login class state a budget); and the operator's
; own figure, FN_INIT_BUDGET_MB, when set.  The thread stacks are inside the
; reservation judged against it (fn-heap-reserve-decide), not beside it.
;
; THE CHOICE.  A capacity-free request (conservative sizing, the default)
; takes the largest friend rung the budget holds (64, 32 or 16 MiB of
; history, transactions one per 512 octets of it), else the small floor (8
; MiB, 16,384 transactions), refused by name when the budget holds not even
; that; never development's 128 transactions (PKT-707), never scale.  FN_INIT_SIZING=largest takes the
; first of scale, development and small the budget holds.  Either way the
; request's own fields (a mission's article bound and groups per article)
; are laid over the preset and never lowered: when no candidate holds them
; the small candidate is refused by name with its reservation and the
; budget.  A request naming T, H or R, or a preset other than the default
; (`--profile development|scale'), is the operator's: written as named,
; never resized, the line saying whether the budget holds it (when it does
; not, the launcher's probe refuses the run by name on this machine; a
; harness that runs the image directly still can).  `init' prints the
; decision (fn-heap-init-report-line); nothing is resized silently.

(defun fn-heap-capacity-free-fieldsp (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (not (and (consp (car fields))
                      (member-equal (caar fields) '(2 3 4))))
           (fn-heap-capacity-free-fieldsp (cdr fields)))
    t))

(defun fn-heap-machine-sized-requestp (request)
  (declare (xargs :guard t))
  (and (fn-bs-profile-requestp request)
       (equal (car request) :default)
       (fn-heap-capacity-free-fieldsp (cadr request))))

; A field's value in a request's field list: the last one given (set-fields
; applies them in order), else DEFAULT.
(defun fn-heap-field-or (key fields default)
  (declare (xargs :guard t))
  (if (consp fields)
      (fn-heap-field-or key (cdr fields)
                        (if (and (consp (car fields)) (equal (caar fields) key)
                                 (natp (cdar fields)))
                            (cdar fields)
                          default))
    default))

;; A friend-sized rung (PKT-707, decided by the coordinator 2026-09-27): the
;; development base with history bound H, transaction slots H / 512 (a slot
;; for every 512 octets of history, so for articles of the sizes people post
;; the history binds first), and R raised to the article record the
;; candidate's A (the request's, else the development base's 32,768) and G
;; (the request's, else 16) need (fn-bs-profile-invalid-reason's
;; :max-record-octets-below-the-article-record), with H at least that R
;; (:max-history-octets-below-max-record-octets: an 8 MiB article's record is
;; past the 8 MiB floor; fix-line-stack).  The request's fields come last, so
;; they are the ones set.
(defun fn-heap-friend-candidate (request h)
  (declare (xargs :guard t))
  (let* ((fields (cadr (true-list-fix request)))
         (a (fn-heap-field-or 5 fields 32768))
         (g (fn-heap-field-or 6 fields 16))
         (r (max 196608 (nfix (fn-record-encoded-octets-ceiling a g)))))
    (list :development
          (append (list (cons 2 (floor (nfix h) 512)) (cons 3 (max (nfix h) r)) (cons 4 r)
                        (cons 6 16) (cons 8 128))
                  (true-list-fix fields)))))

;; The floor: 8 MiB of history and 16,384 transactions, the `small' profile.
(defconst *fn-heap-friend-floor-history* 8388608)
(defconst *fn-heap-friend-floor-transactions* 16384)

(defun fn-heap-small-candidate (request)
  (declare (xargs :guard t))
  (fn-heap-friend-candidate request *fn-heap-friend-floor-history*))

;; The rungs a capacity-free `init' (every mission, and a bare init) tries,
;; largest first: 64, 32 and 16 MiB of history, then the floor.  Measured by
;; the stranger rehearsal (2026-09-27): a short post with its headers is a
;; record of about 860 octets, so the floor holds about 9,700 such posts and
;; the top rung about 78,000, and a feed from a friend spends the same
;; history.  Reservations (hbox's core, the default mission): about 1.3 GB at
;; the floor and 104 MB for each further MiB of history (the list model's 32
;; octets per octet of history, and the capture buffer).
(defconst *fn-heap-friend-rungs* '(67108864 33554432 16777216))

(defun fn-heap-friend-ladder (request rungs)
  (declare (xargs :guard t))
  (if (consp rungs)
      (cons (fn-heap-friend-candidate request (car rungs))
            (fn-heap-friend-ladder request (cdr rungs)))
    (list (fn-heap-small-candidate request))))

; The connections `init' judges a store by: the configuration's default
; max-connections, which the heap probe also passes for `init' so that the
; store init makes is judged as it will run.
(defun fn-heap-reserve-init-connections ()
  (declare (xargs :guard t))
  *fn-ncfg-default-max-connections*)

; The connections a run's threads are reserved for.  Since PRF-211
; (books/native-operator.lisp fn-native-operator-result-run-max-connections)
; a run's owner bound is structural, one past a limit row's width, and the
; capacity is the `exposure-connections' policy row, 31 by default plus the
; operator's one: the configuration's former 32.  The reservation holds that
; default; a live raise of the row past it is not held by the reservation
; made at start (PKT-605, capacity against memory, is its owner).  A smaller
; owner bound is kept.
(defun fn-heap-reserve-run-connections (owner-bound)
  (declare (xargs :guard t))
  (min (nfix owner-bound) *fn-ncfg-default-max-connections*))

(defthm fn-heap-reserve-run-connections-is-at-most-the-default
  (<= (fn-heap-reserve-run-connections owner-bound)
      *fn-ncfg-default-max-connections*)
  :rule-classes nil)

;; THE STATUS LINE (lane reservation-figure; ops-fixes' sweep: `status'
;; printed heap=37643 MB for a node whose launcher reserved about 2.8 GB).
;; `status' and `health' printed connection-budget's launch figure
;; (fn-cbud-launch-decide: the store's heap plus room for as many connections
;; as the machine holds, up to 1,024), which the launcher stopped passing when
;; connections became records on the I/O loops (PRF-223).  They now print the
;; decision the launcher's probe makes for the store's `run' over the store on
;; disk: one figure.  The host calls this (host/native/heap.lisp
;; fnn-heap-print-store-line).
(defun fn-heap-status-decide (profile core nursery observations observed)
  (declare (xargs :guard t))
  (fn-heap-reserve-operation-decide :run profile core nursery observations
                                    (fn-heap-reserve-run-connections
                                     *fn-ncfg-default-max-connections*)
                                    observed))

;; KEYSTONE.  The status figure IS the launcher's run reservation, whatever
;; the configuration's owner bound (the threads a run reserves do not depend
;; on its connections: fn-heap-thread-count).
(defthm fn-heap-status-decide-is-the-launchers-run-reservation
  (equal (fn-heap-status-decide profile core nursery observations observed)
         (fn-heap-reserve-operation-decide :run profile core nursery observations
                                           (fn-heap-reserve-run-connections bound)
                                           observed))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-heap-status-decide fn-heap-reserve-operation-decide
                                fn-heap-reserve-of fn-heap-thread-count)
                              (theory 'minimal-theory)))))

;; What init promises (lane membership-budget, 2026-09-27; the coordinator's
;; release blocker from friend-path, packet A): the run of the FULL store the
;; profile admits -- the state at the profile's bounds and a replay of all
;; of it (heap-figure's :run figure unobserved: the open's input at H and T)
;; -- not the first run of the empty store.  Before, init judged the empty
;; store's first run (observed (0 . 0)), so a store init sized within the
;; budget grew until its own run was refused on the same machine: a 2 GiB
;; OpenBSD node, `init' 1,234 MB within-budget=yes, refused
;; machine-cannot-hold-profile heap=2104 MB machine=2031 MB after 960 posts
;; (lane friend-path's rehearsal record, section 2).  Every later
;; run's figure is at most this one (books/heap-store-figure.lisp
;; `fn-heap-store-figure-observed-is-at-most-unobserved'), so a store init
;; admitted always reopens on the same machine
;; (`fn-heap-init-accepted-store-always-reopens').

(defun fn-heap-reserve-full-store-decide (profile core nursery observations connections)
  (declare (xargs :guard t))
  (fn-heap-reserve-operation-decide :run profile core nursery observations connections
                                    nil))

(defun fn-heap-reserve-acceptsp (request core nursery observations)
  (declare (xargs :guard t))
  (let ((p (fn-bs-profile-resolve request nil)))
    (and (not (equal (car p) :invalid))
         (fn-bs-profile-admittedp p)
         (equal (car (fn-heap-reserve-full-store-decide p core nursery observations
                                                       *fn-ncfg-default-max-connections*))
                :heap))))

(defun fn-heap-reserve-init-choose (candidates last core nursery observations)
  (declare (xargs :guard t))
  (cond ((atom candidates) last)
        ((fn-heap-reserve-acceptsp (car candidates) core nursery observations)
         (car candidates))
        (t (fn-heap-reserve-init-choose (cdr candidates) last core nursery
                                        observations))))

(defthm fn-heap-reserve-init-choose-accepts-when-any-does
  (implies (or (fn-heap-reserve-acceptsp last core nursery observations)
               (fn-heap-reserve-acceptsp (fn-heap-reserve-init-choose
                                          candidates last core nursery observations)
                                         core nursery observations)
               (and (member-equal c candidates)
                    (fn-heap-reserve-acceptsp c core nursery observations)))
           (fn-heap-reserve-acceptsp
            (fn-heap-reserve-init-choose candidates last core nursery observations)
            core nursery observations))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp))))

(defthm fn-heap-reserve-init-choose-is-a-candidate-or-last
  (or (member-equal (fn-heap-reserve-init-choose candidates last core nursery
                                                 observations)
                    candidates)
      (equal (fn-heap-reserve-init-choose candidates last core nursery
                                          observations)
             last))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp))))

; ---- The budget.

(defconst *fn-heap-os-reserve-min-octets* (* 512 *fn-heap-mib*))

(defun fn-heap-os-reserve-octets (physical)
  (declare (xargs :guard t))
  (max *fn-heap-os-reserve-min-octets* (floor (nfix physical) 4)))

; The physical memory the service may count on, or NIL when unobserved.  At
; least one octet: a machine the reserve swallows is an observation that
; holds nothing, never an absent one.
(defun fn-heap-available-physical-octets (physical)
  (declare (xargs :guard t))
  (if (posp physical)
      (max 1 (- physical (fn-heap-os-reserve-octets physical)))
    nil))

(defthm fn-heap-available-physical-octets-posp
  (implies (posp physical)
           (posp (fn-heap-available-physical-octets physical)))
  :rule-classes nil)

(defthm fn-heap-available-physical-octets-is-under-physical
  (implies (posp physical)
           (<= (fn-heap-available-physical-octets physical) physical))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-heap-os-reserve-octets))))

; FN_INIT_BUDGET_MB's octets: NIL when unset, the budget in octets for a
; decimal of 1 to 20 digits naming at least 1 MB, else :bad.
(defun fn-heap-init-explicit-budget (octets)
  (declare (xargs :guard t))
  (if (null octets)
      nil
    (let ((mb (fn-heap-limit-of-octets octets)))
      (if (posp mb) (* *fn-heap-mib* mb) :bad))))

; FN_INIT_SIZING's octets: NIL when unset (conservative), :largest for
; `largest', else :bad.
(defun fn-heap-init-sizing (octets)
  (declare (xargs :guard t))
  (cond ((null octets) :conservative)
        ((equal octets '(108 97 114 103 101 115 116)) :largest)
        (t :bad)))

(defthm fn-heap-init-sizing-is-never-requested
  (not (equal (fn-heap-init-sizing octets) :requested)))

(defun fn-heap-init-observations (physical limits explicit)
  (declare (xargs :guard t))
  (cons (fn-heap-available-physical-octets physical)
        (cons (if (posp explicit) explicit nil) limits)))

; A candidate that holds the request's article.  The request's A and G are
; laid over a preset whose R and H were derived from the preset's own A
; (fn-bs-profile-preset: R the larger of H / T and the article record); a
; request whose article record is past R (development's R holds a 32 KiB
; article at 65,535 groups, so a 4 MiB article bound already exceeds it) left
; a candidate that failed :max-record-octets-below-the-article-record, and
; the small candidate's R raised past its 8 MiB H failed
; :max-history-octets-below-max-record-octets: `init --max-article-octets
; 8388608' was refused as invalid-init-profile on every machine (batch AR,
; tests/test_native_served_line_stack.py).  Here R is raised to the article
; record of the candidate's A and G and H to at least R, as the preset
; derivation does; nothing is lowered, and a candidate that already holds
; its article is returned unchanged.  Whether the budget holds the raised
; reservation is the decision's, as for every candidate.
;; The two fields that raise R and H, or NIL when VALS already hold the
;; article record under an H of at least R (or are :bad).
(defun fn-heap-article-raise (vals)
  (declare (xargs :guard t))
  (let* ((r0 (fn-bs-pf 4 vals))
         (h0 (fn-bs-pf 3 vals))
         (r (max r0 (nfix (fn-record-encoded-octets-ceiling
                           (fn-bs-pf 5 vals) (fn-bs-pf 6 vals)))))
         (h (max h0 r)))
    (if (or (equal vals :bad) (and (equal r r0) (equal h h0)))
        nil
      (list (cons 3 h) (cons 4 r)))))

(defun fn-heap-article-held (request)
  (declare (xargs :guard t))
  (let* ((request (true-list-fix request))
         (preset (car request))
         (fields (true-list-fix (cadr request)))
         (raise (fn-heap-article-raise
                 (fn-bs-profile-set-fields (fn-bs-config-for-profile preset) fields))))
    (if raise (list preset (append fields raise)) request)))

;; Its proof obligations: what it returns is a request, keeps the preset,
;; T, A and G, never lowers H or R, and holds the article record under an
;; H of at least R.
(local (defthm fn-heap-set-fields-of-append
  (implies (not (equal (fn-bs-profile-set-fields v a) :bad))
           (equal (fn-bs-profile-set-fields v (append a b))
                  (fn-bs-profile-set-fields (fn-bs-profile-set-fields v a) b)))))

(local (defthm fn-heap-meta-nth-of-put
  (implies (and (natp i) (natp j))
           (equal (fn-bs-meta-nth i (fn-bs-profile-put j x v))
                  (if (equal i j) x (fn-bs-meta-nth i v))))))

(local (defthm fn-heap-pf-of-put
  (implies (and (natp i) (natp j))
           (equal (fn-bs-pf i (fn-bs-profile-put j x v))
                  (if (equal i j) (nfix x) (fn-bs-pf i v))))))

(local (defthm fn-heap-record-ceiling-natp
  (implies (and (natp a) (natp g))
           (natp (fn-record-encoded-octets-ceiling a g)))
  :rule-classes :type-prescription))

(local (defthm fn-heap-alistp-of-append
  (implies (and (alistp a) (alistp b)) (alistp (append a b)))))

(defthm fn-heap-article-raise-alistp
  (alistp (fn-heap-article-raise vals))
  :hints (("Goal" :in-theory (disable fn-record-encoded-octets-ceiling fn-bs-pf max))))

; Setting the raise's two fields over VALS.
(local (defthm fn-heap-set-fields-of-the-raise
  (let ((raise (fn-heap-article-raise v0)))
    (implies (and raise (not (equal v :bad)))
             (equal (fn-bs-profile-set-fields v raise)
                    (fn-bs-profile-put 4 (cdr (cadr raise))
                                       (fn-bs-profile-put 3 (cdr (car raise)) v)))))
  :hints (("Goal" :in-theory (disable fn-record-encoded-octets-ceiling fn-bs-pf)))))

(defthm fn-heap-article-raise-holds-the-article-record
  (let ((raise (fn-heap-article-raise v0)))
    (implies (not (equal v0 :bad))
             (let ((v (if raise
                          (fn-bs-profile-put 4 (cdr (cadr raise))
                                             (fn-bs-profile-put 3 (cdr (car raise)) v0))
                        v0)))
               (and (<= (fn-record-encoded-octets-ceiling (fn-bs-pf 5 v) (fn-bs-pf 6 v))
                        (fn-bs-pf 4 v))
                    (<= (fn-bs-pf 4 v) (fn-bs-pf 3 v))
                    (equal (fn-bs-pf 2 v) (fn-bs-pf 2 v0))
                    (equal (fn-bs-pf 5 v) (fn-bs-pf 5 v0))
                    (equal (fn-bs-pf 6 v) (fn-bs-pf 6 v0))
                    (<= (fn-bs-pf 3 v0) (fn-bs-pf 3 v))
                    (<= (fn-bs-pf 4 v0) (fn-bs-pf 4 v))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-record-encoded-octets-ceiling fn-bs-pf
                                      fn-bs-profile-put))))

(defthm fn-heap-article-held-is-a-request
  (implies (fn-bs-profile-requestp request)
           (fn-bs-profile-requestp (fn-heap-article-held request)))
  :hints (("Goal" :in-theory (disable fn-heap-article-raise fn-bs-profile-set-fields
                                      fn-bs-config-for-profile
                                      (:e fn-bs-config-for-profile) member-equal)
           :expand ((fn-bs-profile-requestp request)))))

(local (defthm fn-heap-article-raise-is-not-of-bad
  (implies (fn-heap-article-raise v) (not (equal v :bad)))
  :rule-classes :forward-chaining))

(local (defthm fn-heap-profile-put-is-not-bad
  (not (equal (fn-bs-profile-put i x v) :bad))
  :hints (("Goal" :expand ((fn-bs-profile-put i x v))))))

; The values the held request resolves over: the request's, with the
; raise's two fields set when there is one.
(defthm fn-heap-article-held-values
  (implies (fn-bs-profile-requestp request)
           (let ((v0 (fn-bs-profile-set-fields (fn-bs-config-for-profile (car request))
                                               (cadr request))))
             (and (equal (car (fn-heap-article-held request)) (car request))
                  (equal (fn-bs-profile-set-fields
                          (fn-bs-config-for-profile (car (fn-heap-article-held request)))
                          (cadr (fn-heap-article-held request)))
                         (if (fn-heap-article-raise v0)
                             (fn-bs-profile-put 4 (cdr (cadr (fn-heap-article-raise v0)))
                                                (fn-bs-profile-put 3 (cdr (car (fn-heap-article-raise v0))) v0))
                           v0)))))
  :hints (("Goal" :in-theory (disable fn-heap-article-raise fn-bs-profile-set-fields
                                      fn-bs-config-for-profile (:e fn-bs-config-for-profile)
                                      fn-bs-profile-put member-equal)
           :expand ((fn-bs-profile-requestp request))
           :use ((:instance fn-heap-set-fields-of-the-raise
                            (v0 (fn-bs-profile-set-fields (fn-bs-config-for-profile (car request)) (cadr request)))
                            (v (fn-bs-profile-set-fields (fn-bs-config-for-profile (car request)) (cadr request)))))))
  :rule-classes nil)

(defthm fn-heap-article-held-holds-the-article-record
  (let* ((q (fn-heap-article-held request))
         (v (fn-bs-profile-set-fields (fn-bs-config-for-profile (car q)) (cadr q)))
         (v0 (fn-bs-profile-set-fields (fn-bs-config-for-profile (car request))
                                       (cadr request))))
    (implies (and (fn-bs-profile-requestp request)
                  (not (equal v0 :bad)))
             (and (equal (car q) (car request))
                  (not (equal v :bad))
                  (<= (fn-record-encoded-octets-ceiling (fn-bs-pf 5 v) (fn-bs-pf 6 v))
                      (fn-bs-pf 4 v))
                  (<= (fn-bs-pf 4 v) (fn-bs-pf 3 v))
                  (equal (fn-bs-pf 2 v) (fn-bs-pf 2 v0))
                  (equal (fn-bs-pf 5 v) (fn-bs-pf 5 v0))
                  (equal (fn-bs-pf 6 v) (fn-bs-pf 6 v0))
                  (<= (fn-bs-pf 3 v0) (fn-bs-pf 3 v))
                  (<= (fn-bs-pf 4 v0) (fn-bs-pf 4 v)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-profile-put-is-not-bad)
                                             (theory 'minimal-theory))
           :use ((:instance fn-heap-article-raise-holds-the-article-record
                            (v0 (fn-bs-profile-set-fields
                                 (fn-bs-config-for-profile (car request))
                                 (cadr request))))
                 (:instance fn-heap-article-held-values)))))

(local (defthm fn-heap-invalid-history-below-record-means
  (implies (equal (fn-bs-profile-invalid-reason v)
                  :max-history-octets-below-max-record-octets)
           (< (fn-bs-pf 3 v) (fn-bs-pf 4 v)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-pf fn-frame-values-okp fn-bs-profile-countp
                                      fn-record-encoded-octets-ceiling)))))

(local (defthm fn-heap-invalid-record-below-article-means
  (implies (equal (fn-bs-profile-invalid-reason v)
                  :max-record-octets-below-the-article-record)
           (< (fn-bs-pf 4 v)
              (fn-record-encoded-octets-ceiling (fn-bs-pf 5 v) (fn-bs-pf 6 v))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-pf fn-frame-values-okp fn-bs-profile-countp
                                      fn-record-encoded-octets-ceiling)))))

; KEYSTONE (fix-line-stack).  A candidate built from a preset request whose
; fields are well formed never fails either article relation: the store
; init sizes for a request's article bound is refused, if at all, for its
; reservation against the budget, never as an invalid profile.
(defthm fn-heap-article-held-meets-the-article-relations
  (implies (and (fn-bs-profile-requestp request)
                (not (equal (car request) :current))
                (not (equal (fn-bs-profile-set-fields
                             (fn-bs-config-for-profile (car request))
                             (cadr request))
                            :bad)))
           (let ((p (fn-bs-profile-resolve (fn-heap-article-held request) nil)))
             (and (not (equal p (list :invalid :max-history-octets-below-max-record-octets)))
                  (not (equal p (list :invalid :max-record-octets-below-the-article-record))))))
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-resolve)
                                  (fn-heap-article-held fn-bs-profile-set-fields
                                   fn-bs-config-for-profile fn-bs-profile-invalid-reason
                                   fn-record-encoded-octets-ceiling
                                   fn-bs-profile-put fn-bs-pf fn-bs-profile-requestp))
           :use ((:instance fn-heap-article-held-holds-the-article-record)
                 (:instance fn-heap-article-held-is-a-request)
                 (:instance fn-heap-invalid-history-below-record-means
                            (v (fn-bs-profile-set-fields
                                (fn-bs-config-for-profile (car (fn-heap-article-held request)))
                                (cadr (fn-heap-article-held request)))))
                 (:instance fn-heap-invalid-record-below-article-means
                            (v (fn-bs-profile-set-fields
                                (fn-bs-config-for-profile (car (fn-heap-article-held request)))
                                (cadr (fn-heap-article-held request)))))
                 (:instance fn-heap-invalid-history-below-record-means
                            (v (fn-bs-profile-put
                                8 (min (fn-bs-pf 8 (fn-bs-profile-set-fields
                                                    (fn-bs-config-for-profile (car (fn-heap-article-held request)))
                                                    (cadr (fn-heap-article-held request))))
                                       (fn-bs-pf 2 (fn-bs-profile-set-fields
                                                    (fn-bs-config-for-profile (car (fn-heap-article-held request)))
                                                    (cadr (fn-heap-article-held request)))))
                                (fn-bs-profile-set-fields
                                 (fn-bs-config-for-profile (car (fn-heap-article-held request)))
                                 (cadr (fn-heap-article-held request))))))
                 (:instance fn-heap-invalid-record-below-article-means
                            (v (fn-bs-profile-put
                                8 (min (fn-bs-pf 8 (fn-bs-profile-set-fields
                                                    (fn-bs-config-for-profile (car (fn-heap-article-held request)))
                                                    (cadr (fn-heap-article-held request))))
                                       (fn-bs-pf 2 (fn-bs-profile-set-fields
                                                    (fn-bs-config-for-profile (car (fn-heap-article-held request)))
                                                    (cadr (fn-heap-article-held request)))))
                                (fn-bs-profile-set-fields
                                 (fn-bs-config-for-profile (car (fn-heap-article-held request)))
                                 (cadr (fn-heap-article-held request)))))))))
  :rule-classes nil)

(defun fn-heap-preset-candidate (preset request)
  (declare (xargs :guard t))
  (fn-heap-article-held (list preset (cadr (true-list-fix request)))))

(defun fn-heap-init-candidates (request sizing)
  (declare (xargs :guard t))
  (if (equal sizing :largest)
      (list (fn-heap-preset-candidate :scale request)
            (fn-heap-preset-candidate :development request)
            (fn-heap-small-candidate request))
    (fn-heap-friend-ladder request *fn-heap-friend-rungs*)))

; The request init writes, before the budget is checked: the operator's, or
; for a capacity-free request the first candidate the budget holds (else the
; small one).
(defun fn-heap-init-chosen (request core nursery observations sizing)
  (declare (xargs :guard t))
  (if (fn-heap-machine-sized-requestp request)
      (fn-heap-reserve-init-choose (fn-heap-init-candidates request sizing)
                                   (fn-heap-small-candidate request)
                                   core nursery observations)
    request))

; The whole reservation a resolved profile makes at init's connections (the
; figure fn-heap-reserve-full-store-decide compares), in octets.
(defun fn-heap-init-reservation-octets (profile core nursery)
  (declare (xargs :guard t))
  (fn-heap-reservation-octets
   (fn-heap-mb-of (fn-heap-operation-figure-octets :run profile core nursery nil))
   core (fn-heap-stack-kib profile)
   (fn-heap-thread-count (fn-heap-reserve-init-connections))))

;; An explicit target budget holds the profile's whole reservation (the
;; figure init promises: the full store's run, its core and every thread's
;; stack).  EXPLICIT is `fn-heap-init-explicit-budget' of FN_INIT_BUDGET_MB:
;; NIL when unset, never :bad here.
(defun fn-heap-init-target-holdsp (profile core nursery explicit)
  (declare (xargs :guard t))
  (and (posp explicit)
       (fn-bs-profile-admittedp profile)
       (<= (fn-heap-init-reservation-octets profile core nursery) explicit)))

(in-theory (disable fn-heap-init-target-holdsp))

; The decision the host calls (host/native/heap.lisp fnn-heap-init-decision,
; from fnn-operator-execute-init and the heap probe):
;   (:init REQUEST WORD RESERVATION-MB BUDGET-MB SIZING HELDP [TARGET-MB])
;   (:refused REASON RESERVATION-MB BUDGET-MB WORD SIZING)
; HELDP says the budget holds the whole reservation; it is always T for a
; capacity-free request (fn-heap-init-decide-sized-init-is-held), and NIL only
; for an operator's request the budget does not hold but the target budget
; the operator named does (TARGET-MB), written as named (never resized) with
; the line saying so.  An operator's request neither holds is refused
; :init-budget-cannot-hold-profile (lane membership-budget).
; SIZING :conservative, :largest or :requested (the operator named the
; capacity or the preset).  REASON :init-budget-cannot-hold-profile,
; :machine-memory-unobserved, :invalid-init-profile, :invalid-init-budget or
; :invalid-init-sizing.
(defun fn-heap-init-decide (request core nursery physical limits
                                    budget-octets sizing-octets)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (disable fn-heap-reserve-acceptsp
                                          fn-bs-profile-resolve
                                          fn-heap-init-chosen
                                          fn-heap-init-reservation-octets
                                          fn-heap-init-observations
                                          fn-heap-init-explicit-budget
                                          fn-heap-init-sizing
                                          fn-heap-profile-word fn-heap-mb-of
                                          fn-heap-machine-sized-requestp)))))
  (let ((explicit (fn-heap-init-explicit-budget budget-octets))
        (sizing (fn-heap-init-sizing sizing-octets)))
    (cond ((equal explicit :bad)
           (list :refused :invalid-init-budget 0 0 "none" :requested))
          ((equal sizing :bad)
           (list :refused :invalid-init-sizing 0 0 "none" :requested))
          (t
           (let* ((obs (fn-heap-init-observations physical limits explicit))
                  (budget (fn-heap-machine-octets obs))
                  (budget-mb (floor budget *fn-heap-mib*))
                  (mode (if (fn-heap-machine-sized-requestp request)
                            sizing
                          :requested))
                  (chosen (fn-heap-init-chosen request core nursery obs sizing))
                  (profile (fn-bs-profile-resolve chosen nil))
                  (word (fn-heap-profile-word profile))
                  (mb (fn-heap-mb-of (fn-heap-init-reservation-octets
                                      profile core nursery))))
             (cond ((fn-heap-reserve-acceptsp chosen core nursery obs)
                    (list :init chosen word mb budget-mb mode t))
                   ((and (consp profile) (equal (car profile) :invalid))
                    (list :refused :invalid-init-profile 0 budget-mb "none" mode))
                   ; The operator's own request past this machine's budget
                   ; (ember, 2026-09-27 17:30Z): written only when the
                   ; operator NAMED a target budget (FN_INIT_BUDGET_MB, a
                   ; store made for another machine) that holds its whole
                   ; reservation; the line says within-budget=no here and
                   ; names the target.  Otherwise refused by name below with
                   ; both numbers: never a store every later start refuses.
                   ((and (equal mode :requested)
                         (fn-heap-init-target-holdsp profile core nursery explicit))
                    (list :init chosen word mb budget-mb mode nil
                          (floor (nfix explicit) *fn-heap-mib*)))
                   ((zp budget)
                    (list :refused :machine-memory-unobserved 0 0 word mode))
                   (t (list :refused :init-budget-cannot-hold-profile mb
                            budget-mb word mode))))))))

(defun fn-heap-init-decision-request (decision)
  (declare (xargs :guard t))
  (if (and (consp decision) (equal (car decision) :init) (consp (cdr decision)))
      (cadr decision)
    nil))

(defthm fn-heap-machine-octets-of-cons
  (equal (fn-heap-machine-octets (cons x rest))
         (let ((r (fn-heap-machine-octets rest)))
           (cond ((not (posp x)) r)
                 ((zp r) x)
                 (t (min x r))))))

(defthm fn-heap-machine-octets-of-cons-is-under-the-head
  (implies (posp x)
           (<= (fn-heap-machine-octets (cons x rest)) x))
  :rule-classes :linear)

(defthm fn-heap-machine-octets-of-cons-is-under-the-rest
  (implies (posp (fn-heap-machine-octets rest))
           (<= (fn-heap-machine-octets (cons x rest))
               (fn-heap-machine-octets rest)))
  :rule-classes :linear)

(defthm fn-heap-machine-octets-posp-with-a-posp-member
  (implies (and (member-equal x obs) (posp x))
           (posp (fn-heap-machine-octets obs)))
  :rule-classes nil)

(in-theory (disable fn-heap-machine-octets-of-cons))

; The budget is under each of its parts: the physical memory less the OS's
; reserve, each limit the process runs under, and the operator's figure.
(defthm fn-heap-init-budget-is-under-each-part
  (let ((b (fn-heap-machine-octets (fn-heap-init-observations physical limits
                                                              explicit))))
    (and (implies (posp physical)
                  (<= b (fn-heap-available-physical-octets physical)))
         (implies (posp explicit) (<= b explicit))
         (implies (and (member-equal x limits) (posp x)) (<= b x))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-heap-available-physical-octets
                                      fn-heap-machine-octets)
           :use ((:instance fn-heap-machine-octets-is-at-most-each-observation
                            (observations (fn-heap-init-observations
                                           physical limits explicit))
                            (x (fn-heap-available-physical-octets physical)))
                 (:instance fn-heap-machine-octets-is-at-most-each-observation
                            (observations (fn-heap-init-observations
                                           physical limits explicit))
                            (x explicit))
                 (:instance fn-heap-machine-octets-is-at-most-each-observation
                            (observations (fn-heap-init-observations
                                           physical limits explicit)))
                 (:instance fn-heap-available-physical-octets-posp)))))

; ... and so under the machine the run judges (the physical memory and the
; same limits: host/native/heap.lisp fnn-heap-observations).
(defthm fn-heap-init-budget-is-under-the-machine
  (implies (posp (fn-heap-machine-octets (cons physical limits)))
           (<= (fn-heap-machine-octets (fn-heap-init-observations physical limits
                                                                  explicit))
               (fn-heap-machine-octets (cons physical limits))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-machine-octets-of-cons)
                                  (fn-heap-available-physical-octets
                                   fn-heap-machine-octets))
           :use ((:instance fn-heap-available-physical-octets-posp)))))

; The reservation decision reads the observations only through the machine
; they give, and accepts on any machine at least as large.
; heap-figure's store-less figure leaves room for its one thread.
(defthm fn-heap-reserve-storeless-of-storeless-decide
  (implies (and (posp (fn-heap-machine-octets obs))
                (equal (car (fn-heap-storeless-decide core nursery
                                                      (fn-heap-machine-octets obs)))
                       :heap))
           (equal (car (fn-heap-reserve-storeless
                        (fn-heap-storeless-decide core nursery (fn-heap-machine-octets obs))
                        core obs))
                  :heap))
  :hints (("Goal" :use ((:instance fn-heap-storeless-decide-is-small-and-fits
                                   (machine (fn-heap-machine-octets obs)))
                        fn-heap-storeless-thread-is-one-default-thread)
           :in-theory (e/d (fn-heap-reserve-storeless fn-heap-reservation-octets)
                           (fn-heap-storeless-decide-is-small-and-fits
                            fn-heap-storeless-decide fn-heap-machine-octets)))))

(defthm fn-heap-reserve-full-store-accepts-on-a-larger-machine
  (implies (and (equal (car (fn-heap-reserve-full-store-decide p core nursery obs1 k)) :heap)
                (<= (fn-heap-machine-octets obs1) (fn-heap-machine-octets obs2)))
           (equal (car (fn-heap-reserve-full-store-decide p core nursery obs2 k)) :heap))
  :hints (("Goal" :cases ((fn-bs-profile-admittedp p))
           :in-theory (e/d (fn-heap-reserve-full-store-decide fn-heap-reserve-operation-decide
                            fn-heap-reserve-of fn-heap-operation-decide)
                           (fn-heap-operation-figure-octets fn-heap-profile-word
                            fn-bs-profile-admittedp fn-heap-storeless-decide
                            fn-heap-reserve-storeless
                            fn-heap-reservation-octets fn-heap-stack-kib
                            fn-heap-thread-count)))
          ("Subgoal 1" :use ((:instance fn-heap-storeless-decide-accepts-on-a-larger-machine
                                        (m1 (fn-heap-machine-octets obs1))
                                        (m2 (fn-heap-machine-octets obs2)))
                             (:instance fn-heap-reserve-storeless-of-storeless-decide
                                        (obs obs2))))))

;; The figure of any run is at most the full store's.
(local
 (defthm fn-heap-mb-of-monotone
   (implies (<= (nfix a) (nfix b))
            (<= (fn-heap-mb-of a) (fn-heap-mb-of b)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-heap-mb-of)))))

(local
 (defthm fn-heap-run-figure-is-at-most-the-full-store
   (<= (fn-heap-operation-figure-octets :run p core nursery observed)
       (fn-heap-operation-figure-octets :run p core nursery nil))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-heap-operation-figure-octets
                                      fn-heap-operation-observation)))))

(local
 (defthm fn-heap-reserve-of-accepts-a-smaller-heap
  (implies (and (fn-bs-profile-admittedp p)
                (equal (car d1) :heap) (equal (car d2) :heap)
                (<= (nfix (fn-heap-decision-mb d2)) (nfix (fn-heap-decision-mb d1)))
                (equal (car (fn-heap-reserve-of d1 p core obs k)) :heap))
           (equal (car (fn-heap-reserve-of d2 p core obs k2)) :heap))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-reserve-of fn-heap-reservation-octets
                                   fn-heap-thread-count)
                                  (fn-bs-profile-admittedp fn-heap-stack-kib
                                   fn-heap-machine-octets fn-heap-decision-mb))))))

(local
 (defthm fn-heap-run-decide-accepts-below-the-full-store
  (implies (and (fn-bs-profile-admittedp p)
                (equal (car (fn-heap-operation-decide :run p core nursery obs nil)) :heap))
           (and (equal (car (fn-heap-operation-decide :run p core nursery obs observed)) :heap)
                (<= (nfix (fn-heap-decision-mb
                           (fn-heap-operation-decide :run p core nursery obs observed)))
                    (nfix (fn-heap-decision-mb
                           (fn-heap-operation-decide :run p core nursery obs nil))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-heap-run-figure-is-at-most-the-full-store)
                        (:instance fn-heap-mb-of-monotone
                                   (a (fn-heap-operation-figure-octets
                                       :run p core nursery observed))
                                   (b (fn-heap-operation-figure-octets
                                       :run p core nursery nil))))
           :in-theory (e/d (fn-heap-operation-decide fn-heap-decision-mb)
                           (fn-heap-operation-figure-octets fn-heap-profile-word
                            fn-bs-profile-admittedp fn-heap-mb-of
                            fn-heap-machine-octets
                            fn-heap-operation-decide-of-a-serve-action-is-heap-decide))))))

(local
 (defthm fn-heap-init-accepted-admitted-store-always-reopens
  (implies (and (fn-bs-profile-admittedp p)
                (equal (car (fn-heap-reserve-full-store-decide p core nursery obs k))
                       :heap))
           (equal (car (fn-heap-reserve-operation-decide :run p core nursery obs k2
                                                         observed))
                  :heap))
  :hints (("Goal" :use ((:instance fn-heap-run-decide-accepts-below-the-full-store)
                        (:instance fn-heap-reserve-of-accepts-a-smaller-heap
                                   (d1 (fn-heap-operation-decide :run p core nursery obs nil))
                                   (d2 (fn-heap-operation-decide :run p core nursery obs observed)))
                        (:instance fn-heap-reserve-of-holds-the-decision
                                   (d (fn-heap-operation-decide :run p core nursery obs nil))
                                   (profile p) (observations obs) (connections k)))
           :in-theory (union-theories '(fn-heap-reserve-full-store-decide
                                        fn-heap-reserve-operation-decide)
                                      (theory 'minimal-theory))))))

;; KEYSTONE (the coordinator's release blocker, friend-path packet A).  A
;; store whose profile init accepted -- the full store's run reserved within
;; the machine's observations OBS -- is accepted by EVERY later run on the
;; same machine, whatever the store then holds on disk (any OBSERVED) and
;; at any owner bound (K2): the launcher's :run decision reserves the heap.
;; (A hypothesis (fn-bs-profile-admittedp p) was removed after proving the
;; weakened theorem: a store-less decision ignores the observation.)
(defthm fn-heap-init-accepted-store-always-reopens
  (implies (equal (car (fn-heap-reserve-full-store-decide p core nursery obs k))
                  :heap)
           (equal (car (fn-heap-reserve-operation-decide :run p core nursery obs k2
                                                         observed))
                  :heap))
  :hints (("Goal" :cases ((fn-bs-profile-admittedp p)))
          ("Subgoal 1" :use fn-heap-init-accepted-admitted-store-always-reopens
           :in-theory (disable fn-heap-init-accepted-admitted-store-always-reopens))
          ("Subgoal 2" :in-theory (e/d (fn-heap-reserve-full-store-decide
                                        fn-heap-reserve-operation-decide
                                        fn-heap-reserve-of fn-heap-operation-decide)
                                       (fn-heap-operation-figure-octets
                                        fn-bs-profile-admittedp fn-heap-reserve-storeless
                                        fn-heap-storeless-decide
                                        fn-heap-reserve-operation-decide-of-a-serve-action
                                        fn-heap-operation-decide-of-a-serve-action-is-heap-decide)))))

; An accepted full-store reservation of an admitted profile is the one
; fn-heap-init-reservation-octets names, within the machine.
(defthm fn-heap-reserve-full-store-accepted-is-within-the-machine
  (implies (and (fn-bs-profile-admittedp p)
                (equal (car (fn-heap-reserve-full-store-decide
                             p core nursery obs (fn-heap-reserve-init-connections)))
                       :heap))
           (<= (fn-heap-init-reservation-octets p core nursery)
               (fn-heap-machine-octets obs)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-reserve-full-store-decide
                                   fn-heap-reserve-operation-decide fn-heap-reserve-of
                                   fn-heap-operation-decide
                                   fn-heap-init-reservation-octets)
                                  (fn-heap-operation-figure-octets fn-heap-profile-word
                                   fn-bs-profile-admittedp
                                   fn-heap-reservation-octets fn-heap-stack-kib
                                   fn-heap-thread-count
                                   fn-heap-reserve-operation-decide-of-a-serve-action
                                   fn-heap-operation-decide-of-a-serve-action-is-heap-decide)))))

; What an accepted init decision writes is the chosen request, and the
; budget's observations accept it.
(defthm fn-heap-init-decide-accepted-is-the-chosen-request-by-definition
  (let ((d (fn-heap-init-decide request core nursery physical limits
                                budget-octets sizing-octets))
        (obs (fn-heap-init-observations
              physical limits (fn-heap-init-explicit-budget budget-octets))))
    (implies (and (equal (car d) :init) (nth 6 d))
             (and (equal (fn-heap-init-decision-request d)
                         (fn-heap-init-chosen request core nursery obs
                                              (fn-heap-init-sizing sizing-octets)))
                  (fn-heap-reserve-acceptsp
                   (fn-heap-init-chosen request core nursery obs
                                        (fn-heap-init-sizing sizing-octets))
                   core nursery obs))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-init-decide fn-heap-init-decision-request)
                                  (fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                   fn-heap-init-chosen
                                   fn-heap-init-reservation-octets
                                   fn-heap-machine-octets fn-heap-init-observations
                                   fn-heap-init-explicit-budget fn-heap-init-sizing
                                   fn-heap-profile-word fn-heap-mb-of
                                   fn-heap-machine-sized-requestp)))))

; KEYSTONE (PKT-582, gpt-6 wave-5 s.8).  What `init' writes resolves to an
; admitted profile whose whole reservation (heap, core and every thread's
; stack at init's connections) is within the budget init printed, and the
; run's own decision on the same machine (the physical memory and the same
; limits) accepts it: the store init makes is one the launcher starts.
(defthm fn-heap-init-decide-fits-the-budget-and-the-machine
  (let* ((d (fn-heap-init-decide request core nursery physical limits
                                 budget-octets sizing-octets))
         (p (fn-bs-profile-resolve (fn-heap-init-decision-request d) nil))
         (budget (fn-heap-machine-octets
                  (fn-heap-init-observations
                   physical limits (fn-heap-init-explicit-budget budget-octets)))))
    (implies (and (equal (car d) :init) (nth 6 d))
             (and (fn-bs-profile-admittedp p)
                  (<= (fn-heap-init-reservation-octets p core nursery) budget)
                  (implies (posp (fn-heap-machine-octets (cons physical limits)))
                           (equal (car (fn-heap-reserve-full-store-decide
                                        p core nursery (cons physical limits)
                                        (fn-heap-reserve-init-connections)))
                                  :heap)))))
  :hints (("Goal" :in-theory (e/d (fn-heap-reserve-acceptsp)
                                  (fn-heap-init-decide fn-heap-init-decision-request
                                   ;; lane fix-line-stack: the figure's and
                                   ;; the decision's definitions are
                                   ;; useless here (3.8 s -> 0.1 s)
                                   fn-heap-figure-octets
                                   fn-heap-decide fn-bs-profile-field fn-bs-profile-validp
                                   fn-heap-reserve-decide-keeps-heap-figures-refusals
                                   fn-heap-reserve-decide-refuses-exactly-past-the-machine
                                   fn-ock-capture-budget fn-bs-profile-max-history-octets
                                   fn-bs-profile-max-record-octets
                                   fn-heap-reserve-decide fn-heap-reserve-full-store-decide
                                   fn-bs-profile-resolve
                                   fn-bs-profile-admittedp fn-heap-init-chosen
                                   fn-heap-init-reservation-octets
                                   fn-heap-machine-octets fn-heap-init-observations
                                   fn-heap-init-explicit-budget fn-heap-init-sizing
                                   fn-heap-profile-word fn-heap-mb-of
                                   fn-heap-reserve-init-connections
                                   fn-heap-machine-sized-requestp))
           :use ((:instance fn-heap-init-decide-accepted-is-the-chosen-request-by-definition)
                 (:instance fn-heap-reserve-full-store-accepted-is-within-the-machine
                            (p (fn-bs-profile-resolve
                                (fn-heap-init-chosen request core nursery (fn-heap-init-observations physical limits (fn-heap-init-explicit-budget budget-octets))
                                                     (fn-heap-init-sizing sizing-octets))
                                nil))
                            (obs (fn-heap-init-observations physical limits (fn-heap-init-explicit-budget budget-octets))))
                 (:instance fn-heap-init-budget-is-under-the-machine
                            (explicit (fn-heap-init-explicit-budget budget-octets)))
                 (:instance fn-heap-reserve-full-store-accepts-on-a-larger-machine
                            (p (fn-bs-profile-resolve
                                (fn-heap-init-chosen request core nursery (fn-heap-init-observations physical limits (fn-heap-init-explicit-budget budget-octets))
                                                     (fn-heap-init-sizing sizing-octets))
                                nil))
                            (k (fn-heap-reserve-init-connections))
                            (obs1 (fn-heap-init-observations physical limits (fn-heap-init-explicit-budget budget-octets)))
                            (obs2 (cons physical limits)))))))

; A request that names its capacity or its preset, and resolves to a valid
; profile, is written exactly as named, never resized, when this machine's
; budget holds it or the target budget the operator named does.
(defthm fn-heap-init-decide-honors-the-operators-request
  (implies (and (not (fn-heap-machine-sized-requestp request))
                (not (equal (fn-heap-init-explicit-budget budget-octets) :bad))
                (not (equal (fn-heap-init-sizing sizing-octets) :bad))
                (not (equal (car (fn-bs-profile-resolve request nil)) :invalid))
                (or (fn-heap-reserve-acceptsp
                     request core nursery
                     (fn-heap-init-observations
                      physical limits (fn-heap-init-explicit-budget budget-octets)))
                    (fn-heap-init-target-holdsp
                     (fn-bs-profile-resolve request nil) core nursery
                     (fn-heap-init-explicit-budget budget-octets))))
           (let ((d (fn-heap-init-decide request core nursery physical
                                         limits budget-octets sizing-octets)))
             (and (equal (car d) :init)
                  (equal (fn-heap-init-decision-request d) request)
                  (equal (nth 5 d) :requested))))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp
                                      fn-bs-profile-resolve
                                      fn-heap-init-sizing
                                      fn-heap-reserve-init-choose
                                      fn-heap-init-candidates
                                      fn-heap-init-reservation-octets
                                      fn-heap-init-target-holdsp
                                      fn-heap-machine-octets
                                      fn-heap-init-observations
                                      fn-heap-init-explicit-budget
                                      fn-heap-profile-word
                                      fn-heap-mb-of
                                      fn-heap-machine-sized-requestp))))

;; KEYSTONE (ember's decision 2, 2026-09-27 17:30Z: init refuses by name).
;; An operator's request whose whole reservation this machine's budget does
;; not hold, and for which no named target budget holds it, is REFUSED
;; :init-budget-cannot-hold-profile, the decision carrying the reservation
;; and the budget in megabytes (the line prints both), and nothing is
;; written (the decision names no request).  Before, it was written with
;; within-budget=no and every later start refused it.
(defthm fn-heap-init-decide-refuses-the-operators-request-past-the-budget
  (let* ((explicit (fn-heap-init-explicit-budget budget-octets))
         (obs (fn-heap-init-observations physical limits explicit))
         (p (fn-bs-profile-resolve request nil))
         (d (fn-heap-init-decide request core nursery physical
                                 limits budget-octets sizing-octets)))
    (implies (and (not (fn-heap-machine-sized-requestp request))
                  (not (equal explicit :bad))
                  (not (equal (fn-heap-init-sizing sizing-octets) :bad))
                  (not (equal (car p) :invalid))
                  (posp (fn-heap-machine-octets obs))
                  (not (fn-heap-reserve-acceptsp request core nursery obs))
                  (not (fn-heap-init-target-holdsp p core nursery explicit)))
             (and (equal (car d) :refused)
                  (equal (nth 1 d) :init-budget-cannot-hold-profile)
                  (equal (nth 2 d)
                         (fn-heap-mb-of (fn-heap-init-reservation-octets p core nursery)))
                  (equal (nth 3 d) (floor (fn-heap-machine-octets obs) *fn-heap-mib*))
                  (equal (fn-heap-init-decision-request d) nil))))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp
                                      fn-bs-profile-resolve
                                      fn-heap-init-sizing
                                      fn-heap-reserve-init-choose
                                      fn-heap-init-candidates
                                      fn-heap-init-reservation-octets
                                      fn-heap-init-target-holdsp
                                      fn-heap-machine-octets
                                      fn-heap-init-observations
                                      fn-heap-init-explicit-budget
                                      fn-heap-profile-word
                                      fn-heap-machine-sized-requestp))))

; A capacity-free request (a bare init, every mission) is written only when
; the budget holds it: then the keystone applies.
(defthm fn-heap-init-decide-sized-init-is-held
  (implies (and (fn-heap-machine-sized-requestp request)
                (equal (car (fn-heap-init-decide request core nursery physical
                                                 limits budget-octets sizing-octets))
                       :init))
           (nth 6 (fn-heap-init-decide request core nursery physical
                                       limits budget-octets sizing-octets)))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp
                                      fn-bs-profile-resolve
                                      fn-heap-init-sizing
                                      fn-heap-init-chosen
                                      fn-heap-init-reservation-octets
                                      fn-heap-machine-octets
                                      fn-heap-init-observations
                                      fn-heap-init-explicit-budget
                                      fn-heap-profile-word
                                      fn-heap-mb-of
                                      fn-heap-machine-sized-requestp))))

;; Conservative sizing (FN_INIT_SIZING unset: every mission's init and a bare
;; init) writes one of the friend rungs, each with the request's own fields
;; laid last: never development's 128 transactions (PKT-707), never scale.
(defthm fn-heap-init-decide-conservative-is-a-friend-rung
  (let ((d (fn-heap-init-decide request core nursery physical limits
                                budget-octets nil)))
    (implies (and (fn-heap-machine-sized-requestp request)
                  (equal (car d) :init))
             (and (member-equal (fn-heap-init-decision-request d)
                                (fn-heap-friend-ladder request *fn-heap-friend-rungs*))
                  (equal (nth 5 d) :conservative))))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp
                                      fn-bs-profile-resolve
                                      fn-heap-small-candidate
                                      fn-heap-friend-candidate
                                      fn-heap-reserve-init-choose
                                      fn-heap-init-reservation-octets
                                      fn-heap-machine-octets
                                      fn-heap-init-observations
                                      fn-heap-init-explicit-budget
                                      fn-heap-profile-word
                                      fn-heap-mb-of
                                      fn-heap-machine-sized-requestp)
           :use ((:instance fn-heap-reserve-init-choose-is-a-candidate-or-last
                            (candidates (fn-heap-init-candidates request :conservative))
                            (last (fn-heap-small-candidate request))
                            (observations (fn-heap-init-observations
                                           physical limits
                                           (fn-heap-init-explicit-budget
                                            budget-octets))))))))

(local
 (defthm fn-heap-field-or-of-append
   (equal (fn-heap-field-or key (append f1 f2) d)
          (fn-heap-field-or key f2 (fn-heap-field-or key f1 d)))))

(local
 (defthm fn-heap-field-or-of-capacity-free
   (implies (and (fn-heap-capacity-free-fieldsp f)
                 (member-equal key '(2 3 4)))
            (equal (fn-heap-field-or key f d) d))))

(local
 (defthm fn-heap-field-or-of-true-list-fix
   (equal (fn-heap-field-or key (true-list-fix f) d)
          (fn-heap-field-or key f d))
   :hints (("Goal" :induct (fn-heap-field-or key f d)
            :in-theory (union-theories '(fn-heap-field-or true-list-fix car-cons cdr-cons)
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-heap-capacity-free-of-true-list-fix
   (equal (fn-heap-capacity-free-fieldsp (true-list-fix f))
          (fn-heap-capacity-free-fieldsp f))
   :hints (("Goal" :induct (fn-heap-capacity-free-fieldsp f)))))

;; The transaction slots and the history bound a request's field list sets.
(defun fn-heap-request-transactions (request)
  (declare (xargs :guard t))
  (fn-heap-field-or 2 (cadr (true-list-fix request)) 0))

(defun fn-heap-request-history (request)
  (declare (xargs :guard t))
  (fn-heap-field-or 3 (cadr (true-list-fix request)) 0))

(local
 (defthm fn-heap-friend-candidate-sets
   (implies (fn-heap-capacity-free-fieldsp (cadr (true-list-fix request)))
            (and (equal (fn-heap-request-transactions
                         (fn-heap-friend-candidate request h))
                        (floor (nfix h) 512))
                 (<= (nfix h)
                     (fn-heap-request-history
                      (fn-heap-friend-candidate request h)))))))

(local (in-theory (disable fn-heap-request-transactions fn-heap-request-history
                           fn-heap-friend-candidate)))

;; A rung's H is at least the rung (the larger of it and R, batch AV).
(local
 (defthm fn-heap-friend-candidate-history-is-at-least-the-rung
   (implies (fn-heap-capacity-free-fieldsp (cadr (true-list-fix request)))
            (<= (nfix h)
                (fn-heap-request-history (fn-heap-friend-candidate request h))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-heap-request-history fn-heap-friend-candidate)
                   :use ((:instance fn-heap-friend-candidate-sets))))))

(local
 (defthm fn-heap-friend-ladder-holds-the-floor
   (implies (and (fn-heap-capacity-free-fieldsp (cadr (true-list-fix request)))
                 (member-equal c (fn-heap-friend-ladder request
                                                        *fn-heap-friend-rungs*)))
            (and (<= *fn-heap-friend-floor-transactions*
                     (fn-heap-request-transactions c))
                 (<= *fn-heap-friend-floor-history*
                     (fn-heap-request-history c))))))

;; KEYSTONE (PKT-707, the floor).  Whenever `init' accepts a capacity-free
;; request under conservative sizing (every mission), the request it writes
;; sets at least 16,384 transaction slots and 8 MiB of history: never the
;; 128 transactions a friend's node filled after about 125 posts.  With
;; fn-heap-init-decide-fits-the-budget-and-the-machine, that capacity is
;; within the budget; when the budget cannot hold the floor, `init' is
;; refused by name (fn-heap-init-decide-sized-init-is-held and the
;; :init-budget-cannot-hold-profile arm).
(defthm fn-heap-init-decide-conservative-holds-the-floor
  (let ((d (fn-heap-init-decide request core nursery physical limits
                                budget-octets nil)))
    (implies (and (fn-heap-machine-sized-requestp request)
                  (equal (car d) :init))
             (and (<= *fn-heap-friend-floor-transactions*
                      (fn-heap-request-transactions
                       (fn-heap-init-decision-request d)))
                  (<= *fn-heap-friend-floor-history*
                      (fn-heap-request-history
                       (fn-heap-init-decision-request d))))))
  :hints (("Goal" :in-theory (e/d (fn-heap-machine-sized-requestp)
                                  (fn-heap-init-decide
                                   fn-heap-init-decision-request
                                   fn-heap-init-decide-conservative-is-a-friend-rung))
           :use ((:instance fn-heap-init-decide-conservative-is-a-friend-rung)))))

;; KEYSTONE (the largest rung the budget holds).  Under conservative sizing
;; the top rung is written whenever the budget holds it.
(defthm fn-heap-init-decide-conservative-takes-the-top-rung-when-it-fits
  (implies (and (fn-heap-machine-sized-requestp request)
                (not (equal (fn-heap-init-explicit-budget budget-octets) :bad))
                (fn-heap-reserve-acceptsp
                 (fn-heap-friend-candidate request (car *fn-heap-friend-rungs*))
                 core nursery
                 (fn-heap-init-observations physical limits
                                            (fn-heap-init-explicit-budget budget-octets))))
           (equal (fn-heap-init-decision-request
                   (fn-heap-init-decide request core nursery physical limits
                                        budget-octets nil))
                  (fn-heap-friend-candidate request (car *fn-heap-friend-rungs*))))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp
                                      fn-bs-profile-resolve
                                      fn-heap-init-reservation-octets
                                      fn-heap-machine-octets
                                      fn-heap-init-observations
                                      fn-heap-init-explicit-budget
                                      fn-heap-profile-word
                                      fn-heap-mb-of
                                      fn-heap-machine-sized-requestp))))

; FN_INIT_SIZING=largest takes scale whenever the budget holds it.
(defthm fn-heap-init-decide-largest-takes-scale-when-it-fits
  (implies (and (fn-heap-machine-sized-requestp request)
                (not (equal (fn-heap-init-explicit-budget budget-octets) :bad))
                (fn-heap-reserve-acceptsp
                 (fn-heap-preset-candidate :scale request) core nursery
                 (fn-heap-init-observations physical limits
                                            (fn-heap-init-explicit-budget budget-octets))))
           (equal (fn-heap-init-decision-request
                   (fn-heap-init-decide request core nursery physical limits
                                        budget-octets
                                        '(108 97 114 103 101 115 116)))
                  (fn-heap-preset-candidate :scale request)))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp fn-heap-preset-candidate
                                      fn-bs-profile-resolve
                                      fn-heap-init-reservation-octets
                                      fn-heap-machine-octets
                                      fn-heap-init-observations
                                      fn-heap-init-explicit-budget
                                      fn-heap-profile-word
                                      fn-heap-mb-of
                                      fn-heap-machine-sized-requestp))))

; ---- The line init prints (stdout on acceptance, stderr on refusal):
;   init: profile=WORD sizing=MODE reservation=MB MB budget=MB MB within-budget=yes|no
;   refused REASON profile=WORD sizing=MODE reservation=MB MB budget=MB MB

(defun fn-heap-init-mode-word (mode)
  (declare (xargs :guard t))
  (case mode
    (:conservative "conservative")
    (:largest "largest")
    (otherwise "requested")))

(defun fn-heap-init-reason-word (reason)
  (declare (xargs :guard t))
  (case reason
    (:init-budget-cannot-hold-profile "init-budget-cannot-hold-profile")
    (:machine-memory-unobserved "machine-memory-unobserved")
    (:invalid-init-profile "invalid-init-profile")
    (:invalid-init-budget "invalid-init-budget")
    (:invalid-init-sizing "invalid-init-sizing")
    (otherwise "malformed")))

(defun fn-heap-init-report-fields (head word mode mb budget)
  (declare (xargs :guard (stringp head)))
  (concatenate 'string head
               " profile=" (if (stringp word) word "none")
               " sizing=" (fn-heap-init-mode-word mode)
               " reservation=" (fn-heap-decimal mb)
               " MB budget=" (fn-heap-decimal budget) " MB"))

(defthm fn-heap-init-report-fields-stringp
  (stringp (fn-heap-init-report-fields head word mode mb budget))
  :rule-classes :type-prescription)

(in-theory (disable fn-heap-init-report-fields))

; The target budget an operator named for a store made for another machine.
(defun fn-heap-init-target-text (mb)
  (declare (xargs :guard t))
  (if (natp mb)
      (concatenate 'string " target-budget=" (fn-heap-decimal mb) " MB")
    ""))

(defthm fn-heap-init-target-text-stringp
  (stringp (fn-heap-init-target-text mb))
  :rule-classes :type-prescription)

(in-theory (disable fn-heap-init-target-text))

(defun fn-heap-init-report-line (decision)
  (declare (xargs :guard t))
  (let ((d (true-list-fix decision)))
    (if (equal (car d) :init)
        (concatenate 'string
                     (fn-heap-init-report-fields "init:" (nth 2 d) (nth 5 d) (nth 3 d)
                                                 (nth 4 d))
                     (if (nth 6 d) " within-budget=yes" " within-budget=no")
                     (fn-heap-init-target-text (nth 7 d)))
      (fn-heap-init-report-fields
       (concatenate 'string "refused " (fn-heap-init-reason-word (nth 1 d)))
       (nth 4 d) (nth 5 d) (nth 2 d) (nth 3 d)))))

(defthm fn-heap-init-report-line-stringp
  (stringp (fn-heap-init-report-line decision))
  :rule-classes :type-prescription)

(defun fn-heap-init-exit-code (decision)
  (declare (xargs :guard t))
  (fn-outcome-code (if (and (consp decision) (equal (car decision) :init))
                       :accepted
                     :refused)))

(defthm fn-heap-init-refusal-exits-1
  (implies (not (equal (car decision) :init))
           (equal (fn-heap-init-exit-code decision) 1)))

; -----------------------------------------------------------------------------
; The figure is heap-figure's formula since the records flip
; (books/heap-store-figure.lisp): the least dynamic space, at the trigger the
; host sets in it, that holds the image's dynamic content, the state of the
; profile's largest store, a full replay of it and the request in flight;
; and it grows with H, T, G, R, the header bound and the capture budget.

(defthm fn-heap-figure-octets-is-the-formula-by-definition
  (equal (fn-heap-figure-octets profile core nursery)
         (fn-heap-with-nursery
          (+ (fn-heap-core-dynamic core)
             (fn-heap-store-state-octets profile (fn-bs-profile-max-history-octets profile)
                                         (fn-bs-profile-max-transactions profile)
                                         (fn-heap-membership-bound profile))
             (fn-heap-store-open-octets
              profile
              (nfix (fn-bs-profile-max-history-octets profile))
              (nfix (fn-bs-profile-max-transactions profile)))
             (fn-heap-store-inflight-octets profile))
          nursery))
  :hints (("Goal" :in-theory (union-theories '(fn-heap-figure-octets fn-heap-store-figure-octets
                                               fn-heap-store-base-octets
                                               fn-heap-open-bounds-of-nil)
                                             (theory 'minimal-theory)))))

(local
 (defthm fn-heap-figure-octets-grows-given-the-capture-budget
  (implies (and (<= (nfix (fn-bs-profile-max-history-octets p1))
                    (nfix (fn-bs-profile-max-history-octets p2)))
                (<= (nfix (fn-bs-profile-max-transactions p1))
                    (nfix (fn-bs-profile-max-transactions p2)))
                (<= (nfix (fn-bs-profile-max-record-octets p1))
                    (nfix (fn-bs-profile-max-record-octets p2)))
                (<= (nfix (fn-bs-profile-field 17 p1)) (nfix (fn-bs-profile-field 17 p2)))
                (<= (fn-ock-capture-budget p1) (fn-ock-capture-budget p2)))
           (<= (fn-heap-figure-octets p1 core nursery)
               (fn-heap-figure-octets p2 core nursery)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-heap-figure-octets fn-heap-store-figure-octets
                                               fn-heap-nfix-of-store-base-octets)
                                             (theory 'minimal-theory))
           :use ((:instance fn-heap-store-base-octets-grows-with-the-profile)
                 (:instance fn-heap-with-nursery-monotone
                            (b1 (fn-heap-store-base-octets p1 core nil))
                            (b2 (fn-heap-store-base-octets p2 core nil))))))))

; The capture budget is fn-sccr-file-read-bound of H and R, monotone in
; each: the budget hypothesis the keystone once carried follows from H and
; R (audit packet G3-3, lane audit-fixes).
(defthm fn-heap-capture-budget-grows-with-history-and-record
  (implies (and (<= (nfix (fn-bs-profile-max-history-octets p1))
                    (nfix (fn-bs-profile-max-history-octets p2)))
                (<= (nfix (fn-bs-profile-max-record-octets p1))
                    (nfix (fn-bs-profile-max-record-octets p2))))
           (<= (fn-ock-capture-budget p1) (fn-ock-capture-budget p2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-ock-capture-budget fn-sccr-file-read-bound
                                               fn-scc-segment-max-octets)
                                             (theory 'minimal-theory)))))

(defthm fn-heap-figure-octets-grows-with-history-and-record
  (implies (and (<= (nfix (fn-bs-profile-max-history-octets p1))
                    (nfix (fn-bs-profile-max-history-octets p2)))
                (<= (nfix (fn-bs-profile-max-transactions p1))
                    (nfix (fn-bs-profile-max-transactions p2)))
                (<= (nfix (fn-bs-profile-max-record-octets p1))
                    (nfix (fn-bs-profile-max-record-octets p2)))
                (<= (nfix (fn-bs-profile-field 17 p1)) (nfix (fn-bs-profile-field 17 p2))))
           (<= (fn-heap-figure-octets p1 core nursery)
               (fn-heap-figure-octets p2 core nursery)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-heap-capture-budget-grows-with-history-and-record)
                 (:instance fn-heap-figure-octets-grows-given-the-capture-budget)))))
