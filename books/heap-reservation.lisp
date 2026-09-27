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

(defun fn-heap-thread-count (connections)
  (declare (xargs :guard t))
  (+ (nfix connections) (fn-native-control-max-active-clients)
     *fn-heap-fixed-threads*))

(defun fn-heap-reservation-octets (mb core stack-kib threads)
  (declare (xargs :guard t))
  (+ (* *fn-heap-mib* (nfix mb))
     (nfix core)
     (* (nfix threads) (+ (* 1024 (nfix stack-kib)) *fn-heap-thread-runtime-octets*))))

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
           (list :heap (fn-heap-decision-mb d) (nth 2 d) (nth 3 d)
                 *fn-heap-default-stack-kib* 1))
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

; KEYSTONE.  An accepted reservation for an admitted profile is heap-figure's
; heap (so everything heap-figure's keystone holds in it), and beside it
; THREADS threads, at least the connections the configuration admits plus
; the control clients and the fixed threads, each with a control stack of at
; least the constant (seven times the served path's measured floor, whatever
; the article); and the whole fits the machine.
(defthm fn-heap-reserve-decide-holds-every-thread-the-node-runs
  (let ((r (fn-heap-reserve-decide profile core nursery observations connections)))
    (implies (and (fn-bs-profile-admittedp profile)
                  (equal (car r) :heap)
                  (natp connections))
             (and (equal (fn-heap-decision-mb r)
                         (fn-heap-decision-mb
                          (fn-heap-decide profile core nursery observations)))
                  (<= (+ connections (fn-native-control-max-active-clients)
                         *fn-heap-fixed-threads*)
                      (fn-heap-reserve-threads r))
                  (<= *fn-heap-stack-octets*
                      (* 1024 (fn-heap-reserve-stack-kib r)))
                  (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                         (nfix core)
                         (* (fn-heap-reserve-threads r)
                            (+ (* 1024 (fn-heap-reserve-stack-kib r))
                               *fn-heap-thread-runtime-octets*)))
                      (fn-heap-machine-octets observations)))))
  :hints (("Goal" :cases ((equal (car (fn-heap-decide profile core nursery observations))
                                 :heap))
           :in-theory (e/d (fn-heap-stack-kib fn-heap-thread-count
                            fn-heap-reservation-octets)
                           (fn-heap-reserve-decide fn-heap-decide
                            fn-bs-profile-admittedp fn-heap-machine-octets
                            fn-heap-decide-refuses-exactly-past-the-machine
                            fn-native-control-max-active-clients
                            fn-heap-mb-of))
           :use ((:instance fn-heap-kib-of-covers
                            (octets (fn-heap-stack-octets profile)))
                 (:instance fn-heap-decide-heap-shape)))))

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
  (true-listp (fn-heap-operation-decide action profile core nursery observations))
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
         (list :heap (fn-heap-decision-mb d) (nth 2 d) (nth 3 d)
               *fn-heap-default-stack-kib* 1))
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

(defun fn-heap-reserve-operation-decide (action profile core nursery observations
                                                connections)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-heap-operation-decide
                                                            fn-heap-reserve-decide
                                                            fn-heap-reserve-of)))))
  (if (member-equal action '(:compact :reclaim))
      (fn-heap-reserve-of (fn-heap-operation-decide action profile core nursery
                                                    observations)
                          profile core observations connections)
    (fn-heap-reserve-decide profile core nursery observations connections)))

; Every command but the compaction verbs reserves exactly as before.
(defthm fn-heap-reserve-operation-decide-of-a-serve-action-by-definition
  (implies (not (member-equal action '(:compact :reclaim)))
           (equal (fn-heap-reserve-operation-decide action profile core nursery
                                                    observations connections)
                  (fn-heap-reserve-decide profile core nursery observations
                                          connections))))

; An accepted reservation beside a heap decision D is D's heap, and heap,
; core and the threads' stacks fit the machine.
(defthm fn-heap-reserve-of-holds-the-decision
  (let ((r (fn-heap-reserve-of d profile core observations connections)))
    (implies (and (fn-bs-profile-admittedp profile)
                  (equal (car r) :heap))
             (and (equal (car d) :heap)
                  (equal (fn-heap-decision-mb r) (fn-heap-decision-mb d))
                  (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                         (nfix core)
                         (* (fn-heap-reserve-threads r)
                            (+ (* 1024 (fn-heap-reserve-stack-kib r))
                               *fn-heap-thread-runtime-octets*)))
                      (fn-heap-machine-octets observations)))))
  :hints (("Goal" :in-theory (e/d (fn-heap-reservation-octets fn-heap-reserve-threads
                                   fn-heap-reserve-stack-kib)
                                  (fn-bs-profile-admittedp fn-heap-machine-octets
                                   fn-native-control-max-active-clients
                                   fn-heap-mb-of fn-heap-stack-kib fn-heap-thread-count)))))

; KEYSTONE (PKT-686).  An accepted reservation for an admitted profile is the
; operation's accepted heap figure (so `fn-heap-operation-decide-holds-the-
; operation' holds in it: the command's measured working set on every store
; the profile admits), and the heap, the image and the threads' stacks fit
; the machine.
(defthm fn-heap-reserve-operation-decide-holds-the-operation
  (let ((r (fn-heap-reserve-operation-decide action profile core nursery
                                             observations connections))
        (d (fn-heap-operation-decide action profile core nursery observations)))
    (implies (and (fn-bs-profile-admittedp profile)
                  (equal (car r) :heap))
             (and (equal (car d) :heap)
                  (equal (fn-heap-decision-mb r) (fn-heap-decision-mb d))
                  (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                         (nfix core)
                         (* (fn-heap-reserve-threads r)
                            (+ (* 1024 (fn-heap-reserve-stack-kib r))
                               *fn-heap-thread-runtime-octets*)))
                      (fn-heap-machine-octets observations)))))
  :hints (("Goal" :use ((:instance fn-heap-reserve-decide-is-reserve-of-heap-decide)
                        (:instance fn-heap-reserve-of-holds-the-decision
                                   (d (fn-heap-operation-decide action profile core nursery
                                                                observations)))
                        (:instance fn-heap-reserve-of-holds-the-decision
                                   (d (fn-heap-decide profile core nursery observations)))
                        (:instance fn-heap-operation-decide-of-a-serve-action-is-heap-decide))
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
; takes the development preset when the budget holds its whole reservation,
; else the small candidate; never scale.  FN_INIT_SIZING=largest takes the
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

; The small preset under the request's fields, R raised to the article
; record the candidate's A (the request's, else the development base's
; 32,768) and G (the request's, else 16) need (fn-bs-profile-invalid-reason's
; :max-record-octets-below-the-article-record).  The request's fields come
; last, so they are the ones set.
(defun fn-heap-small-candidate (request)
  (declare (xargs :guard t))
  (let* ((fields (cadr (true-list-fix request)))
         (a (fn-heap-field-or 5 fields 32768))
         (g (fn-heap-field-or 6 fields 16))
         (r (max 196608 (nfix (fn-record-encoded-octets-ceiling a g)))))
    (list :development
          (append (list (cons 2 16384) (cons 3 8388608) (cons 4 r)
                        (cons 6 16) (cons 8 128))
                  (true-list-fix fields)))))

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

(defun fn-heap-reserve-acceptsp (request core nursery observations)
  (declare (xargs :guard t))
  (let ((p (fn-bs-profile-resolve request nil)))
    (and (not (equal (car p) :invalid))
         (fn-bs-profile-admittedp p)
         (equal (car (fn-heap-reserve-decide p core nursery observations
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

(defun fn-heap-init-candidates (request sizing)
  (declare (xargs :guard t))
  (let ((fields (cadr (true-list-fix request))))
    (if (equal sizing :largest)
        (list (list :scale fields) (list :development fields)
              (fn-heap-small-candidate request))
      (list (list :development fields) (fn-heap-small-candidate request)))))

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
; figure fn-heap-reserve-decide compares), in octets.
(defun fn-heap-init-reservation-octets (profile core nursery)
  (declare (xargs :guard t))
  (fn-heap-reservation-octets
   (fn-heap-mb-of (fn-heap-figure-octets profile core nursery))
   core (fn-heap-stack-kib profile)
   (fn-heap-thread-count (fn-heap-reserve-init-connections))))

; The decision the host calls (host/native/heap.lisp fnn-heap-init-decision,
; from fnn-operator-execute-init and the heap probe):
;   (:init REQUEST WORD RESERVATION-MB BUDGET-MB SIZING HELDP)
;   (:refused REASON RESERVATION-MB BUDGET-MB WORD SIZING)
; HELDP says the budget holds the whole reservation; it is always T for a
; capacity-free request (fn-heap-init-decide-sized-init-is-held), and NIL only
; for an operator's request the budget does not hold, which is written as
; named (never resized) with the line saying so.
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
                   ; The operator's own request: written as named, the line
                   ; saying the budget does not hold it (the launcher's probe
                   ; refuses its run by name on this machine).
                   ((equal mode :requested)
                    (list :init chosen word mb budget-mb mode nil))
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
(defthm fn-heap-reserve-decide-accepts-on-a-larger-machine
  (implies (and (equal (car (fn-heap-reserve-decide p core nursery obs1 k)) :heap)
                (<= (fn-heap-machine-octets obs1) (fn-heap-machine-octets obs2)))
           (equal (car (fn-heap-reserve-decide p core nursery obs2 k)) :heap))
  :hints (("Goal" :in-theory (e/d (fn-heap-reserve-decide fn-heap-decide)
                                  (fn-heap-decide-refuses-exactly-past-the-machine
                                   fn-heap-figure-octets fn-heap-profile-word
                                   fn-bs-profile-admittedp
                                   fn-heap-reservation-octets fn-heap-stack-kib
                                   fn-heap-thread-count)))))

; An accepted reservation of an admitted profile is the one
; fn-heap-init-reservation-octets names, within the machine.
(defthm fn-heap-reserve-decide-accepted-is-within-the-machine
  (implies (and (fn-bs-profile-admittedp p)
                (equal (car (fn-heap-reserve-decide p core nursery obs
                                                    (fn-heap-reserve-init-connections)))
                       :heap))
           (<= (fn-heap-init-reservation-octets p core nursery)
               (fn-heap-machine-octets obs)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-reserve-decide fn-heap-decide
                                   fn-heap-init-reservation-octets)
                                  (fn-heap-decide-refuses-exactly-past-the-machine
                                   fn-heap-figure-octets fn-heap-profile-word
                                   fn-bs-profile-admittedp
                                   fn-heap-reservation-octets fn-heap-stack-kib
                                   fn-heap-thread-count)))))

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
                           (equal (car (fn-heap-reserve-decide
                                        p core nursery (cons physical limits)
                                        (fn-heap-reserve-init-connections)))
                                  :heap)))))
  :hints (("Goal" :in-theory (e/d (fn-heap-reserve-acceptsp)
                                  (fn-heap-init-decide fn-heap-init-decision-request
                                   fn-heap-reserve-decide fn-bs-profile-resolve
                                   fn-bs-profile-admittedp fn-heap-init-chosen
                                   fn-heap-init-reservation-octets
                                   fn-heap-machine-octets fn-heap-init-observations
                                   fn-heap-init-explicit-budget fn-heap-init-sizing
                                   fn-heap-profile-word fn-heap-mb-of
                                   fn-heap-reserve-init-connections
                                   fn-heap-machine-sized-requestp))
           :use ((:instance fn-heap-init-decide-accepted-is-the-chosen-request-by-definition)
                 (:instance fn-heap-reserve-decide-accepted-is-within-the-machine
                            (p (fn-bs-profile-resolve
                                (fn-heap-init-chosen request core nursery (fn-heap-init-observations physical limits (fn-heap-init-explicit-budget budget-octets))
                                                     (fn-heap-init-sizing sizing-octets))
                                nil))
                            (obs (fn-heap-init-observations physical limits (fn-heap-init-explicit-budget budget-octets))))
                 (:instance fn-heap-init-budget-is-under-the-machine
                            (explicit (fn-heap-init-explicit-budget budget-octets)))
                 (:instance fn-heap-reserve-decide-accepts-on-a-larger-machine
                            (p (fn-bs-profile-resolve
                                (fn-heap-init-chosen request core nursery (fn-heap-init-observations physical limits (fn-heap-init-explicit-budget budget-octets))
                                                     (fn-heap-init-sizing sizing-octets))
                                nil))
                            (k (fn-heap-reserve-init-connections))
                            (obs1 (fn-heap-init-observations physical limits (fn-heap-init-explicit-budget budget-octets)))
                            (obs2 (cons physical limits)))))))

; A request that names its capacity or its preset, and resolves to a valid
; profile, is written exactly as named, whatever the budget: never refused
; for size, never resized.
(defthm fn-heap-init-decide-honors-the-operators-request
  (implies (and (not (fn-heap-machine-sized-requestp request))
                (not (equal (fn-heap-init-explicit-budget budget-octets) :bad))
                (not (equal (fn-heap-init-sizing sizing-octets) :bad))
                (not (equal (car (fn-bs-profile-resolve request nil)) :invalid)))
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
                                      fn-heap-machine-octets
                                      fn-heap-init-observations
                                      fn-heap-init-explicit-budget
                                      fn-heap-profile-word
                                      fn-heap-mb-of
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

; Conservative sizing (FN_INIT_SIZING unset) writes development or the small
; candidate, each with the request's own fields laid last, never scale; and
; development whenever the budget holds it.
(defthm fn-heap-init-decide-conservative-is-development-or-small
  (let ((d (fn-heap-init-decide request core nursery physical limits
                                budget-octets nil))
        (fields (cadr (true-list-fix request))))
    (implies (and (fn-heap-machine-sized-requestp request)
                  (equal (car d) :init))
             (and (member-equal (fn-heap-init-decision-request d)
                                (list (list :development fields)
                                      (fn-heap-small-candidate request)))
                  (equal (nth 5 d) :conservative))))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp
                                      fn-bs-profile-resolve
                                      fn-heap-small-candidate
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

(defthm fn-heap-init-decide-conservative-takes-development-when-it-fits
  (implies (and (fn-heap-machine-sized-requestp request)
                (not (equal (fn-heap-init-explicit-budget budget-octets) :bad))
                (fn-heap-reserve-acceptsp
                 (list :development (cadr (true-list-fix request))) core nursery
                 (fn-heap-init-observations physical limits
                                            (fn-heap-init-explicit-budget budget-octets))))
           (equal (fn-heap-init-decide request core nursery physical limits
                                       budget-octets nil)
                  (list :init (list :development (cadr (true-list-fix request)))
                        (fn-heap-profile-word
                         (fn-bs-profile-resolve
                          (list :development (cadr (true-list-fix request))) nil))
                        (fn-heap-mb-of
                         (fn-heap-init-reservation-octets
                          (fn-bs-profile-resolve
                           (list :development (cadr (true-list-fix request))) nil)
                          core nursery))
                        (floor (fn-heap-machine-octets
                                (fn-heap-init-observations
                                 physical limits
                                 (fn-heap-init-explicit-budget budget-octets)))
                               *fn-heap-mib*)
                        :conservative t)))
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
                 (list :scale (cadr (true-list-fix request))) core nursery
                 (fn-heap-init-observations physical limits
                                            (fn-heap-init-explicit-budget budget-octets))))
           (equal (fn-heap-init-decision-request
                   (fn-heap-init-decide request core nursery physical limits
                                        budget-octets
                                        '(108 97 114 103 101 115 116)))
                  (list :scale (cadr (true-list-fix request)))))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp
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

(defun fn-heap-init-report-line (decision)
  (declare (xargs :guard t))
  (let ((d (true-list-fix decision)))
    (if (equal (car d) :init)
        (concatenate 'string
                     (fn-heap-init-report-fields "init:" (nth 2 d) (nth 5 d) (nth 3 d)
                                                 (nth 4 d))
                     (if (nth 6 d) " within-budget=yes" " within-budget=no"))
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
; The figure is heap-figure's formula and grows with H, R and the header
; bound (field 17, batch AS's header-limits-profile: three list copies of
; the header in flight): the default preset's figure is 32 x (2 x 2^40 +
; 2^26 + 3 x field 17) octets of lists and not a unit error.

(defthm fn-heap-figure-octets-is-the-formula-by-definition
  (equal (fn-heap-figure-octets profile core nursery)
         (+ (nfix core) (nfix nursery)
            (* 32 (+ (* 2 (fn-bs-profile-max-history-octets profile))
                     (fn-bs-profile-max-record-octets profile)
                     (* *fn-heap-header-copies* (fn-bs-profile-field 17 profile))))
            (* 2 (fn-ock-capture-budget profile))))
  :hints (("Goal" :in-theory (enable fn-heap-figure-octets fn-heap-list-octets
                                     fn-heap-buffer-octets))))

(defthm fn-heap-figure-octets-grows-with-history-and-record
  (implies (and (<= (fn-bs-profile-max-history-octets p1)
                    (fn-bs-profile-max-history-octets p2))
                (<= (fn-bs-profile-max-record-octets p1)
                    (fn-bs-profile-max-record-octets p2))
                (<= (fn-bs-profile-field 17 p1) (fn-bs-profile-field 17 p2))
                (<= (fn-ock-capture-budget p1) (fn-ock-capture-budget p2)))
           (<= (fn-heap-figure-octets p1 core nursery)
               (fn-heap-figure-octets p2 core nursery)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-figure-octets fn-heap-list-octets
                                   fn-heap-buffer-octets)
                                  (fn-ock-capture-budget
                                   fn-bs-profile-max-history-octets
                                   fn-bs-profile-max-record-octets
                                   fn-bs-profile-field)))))
