; fn: the whole reservation a node makes, heap and thread stacks, decided
; before the image starts (lane image-floor, 2026-09-26; HST-017; an extension
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
; THE STACK a thread needs is measured, not guessed: a served article of L
; lines needs about 144 KiB + 32 octets per line of control stack (hbox,
; node_measure.py stack-floor, lines of 3 octets: 10,922 lines 447 KiB,
; 87,381 lines 2,878 KiB, 349,525 lines 11,066 KiB; 32.0 octets per line
; between the last two).  The per-line frames are the served path's
; non-tail recursions over the article's lines (books/nntp-session.lisp
; fn-nntp-stuff-lines is one); below that stack the owner faults and stops
; (`owner core/store fault; process stopped: ... Control stack exhausted').
; An article of A octets has at most A/2 lines (each ends in CRLF); the
; stored article adds the node's own header lines, bounded here by 1,024.
; The figure takes 512 KiB + 40 octets per line: 3.5 times the measured base
; and a quarter over the measured slope.
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

(defconst *fn-heap-stack-base-octets* (* 512 1024))
(defconst *fn-heap-stack-octets-per-line* 40)
(defconst *fn-heap-stack-header-lines* 1024)
(defconst *fn-heap-thread-runtime-octets* (* 4 *fn-heap-mib*))
(defconst *fn-heap-fixed-threads* 12)
; The stack when no store profile is named (help, --version): SBCL's own
; default, 2 MiB.
(defconst *fn-heap-default-stack-kib* 2048)

; The most lines an article the profile admits can have in the store.
(defun fn-heap-article-lines-bound (profile)
  (declare (xargs :guard t))
  (+ (floor (nfix (fn-bs-profile-max-article-octets profile)) 2)
     *fn-heap-stack-header-lines*))

(defun fn-heap-stack-octets (profile)
  (declare (xargs :guard t))
  (+ *fn-heap-stack-base-octets*
     (* *fn-heap-stack-octets-per-line* (fn-heap-article-lines-bound profile))))

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
; least the measured need of the largest article the profile admits; and the
; whole fits the machine.
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
                  (<= (+ *fn-heap-stack-base-octets*
                         (* *fn-heap-stack-octets-per-line*
                            (fn-heap-article-lines-bound profile)))
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
                            fn-heap-article-lines-bound
                            fn-heap-mb-of))
           :use ((:instance fn-heap-kib-of-covers
                            (octets (fn-heap-stack-octets profile)))
                 (:instance fn-heap-decide-heap-shape)))))

; -----------------------------------------------------------------------------
; The report the probe prints: heap-figure's line, then on acceptance
;   stack=KB KB threads=N
; and the thread refusal's own line.

(defun fn-heap-reserve-report-line (decision)
  (declare (xargs :guard t))
  (cond ((and (consp decision) (true-listp decision) (equal (car decision) :heap))
         (concatenate 'string
                      (fn-heap-report-line (list :heap (nth 1 decision)
                                                 (nth 2 decision) (nth 3 decision)))
                      " stack=" (fn-heap-decimal (nth 4 decision))
                      " KB threads=" (fn-heap-decimal (nth 5 decision))))
        ((and (consp decision) (true-listp decision)
              (equal (nth 1 decision) :machine-cannot-hold-threads))
         (concatenate 'string "refused machine-cannot-hold-threads reservation="
                      (fn-heap-decimal (nth 2 decision))
                      " MB machine=" (fn-heap-decimal (nth 3 decision)) " MB"))
        (t (fn-heap-report-line decision))))

(defthm fn-heap-reserve-report-line-stringp
  (stringp (fn-heap-reserve-report-line decision))
  :rule-classes :type-prescription)

(defthm fn-heap-reserve-thread-refusal-exits-1
  (equal (fn-heap-decision-exit-code
          (list :refused :machine-cannot-hold-threads mb machine-mb))
         1))

; -----------------------------------------------------------------------------
; What `init' writes (PKT-582).  The default preset's history bound is the
; codec's 1 TiB, and a request over it that names no capacity field (a bare
; `init', and every mission: books/native-operator.lisp
; fn-native-mission-request sets only the article bound and groups per
; article) resolved to H = 1 TiB, whose list-representation heap is
; 16 x 2 x 2^40 octets: `heap=73402949 MB', refused on every machine.  The
; figure is the formula (fn-heap-figure-octets-grows-with-history below); the
; request was wrong for a machine.  Such a request now takes its capacity
; from the machine: the first of scale, development and the small preset
; (each with the request's own fields laid over it, the small one with R
; raised to the request's article record) that resolves to a valid profile
; whose whole reservation (fn-heap-reserve-decide, at the configuration's
; default max-connections) the machine holds; else the small one, which the
; machine then refuses by name.  A request naming T, H or R is the
; operator's, unchanged.

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
; :max-record-octets-below-the-article-record).
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

(defun fn-heap-init-candidates (request)
  (declare (xargs :guard t))
  (list (list :scale (cadr (true-list-fix request)))
        (list :development (cadr (true-list-fix request)))
        (fn-heap-small-candidate request)))

; The connections `init' judges a store by: the configuration's default
; max-connections, which the heap probe also passes for `init' so that the
; store init makes is judged as it will run.
(defun fn-heap-reserve-init-connections ()
  (declare (xargs :guard t))
  *fn-ncfg-default-max-connections*)

(defun fn-heap-reserve-acceptsp (request core nursery observations)
  (declare (xargs :guard t))
  (let ((p (fn-bs-profile-resolve request nil)))
    (and (not (equal (car p) :invalid))
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

(defun fn-heap-reserve-init-request (request core nursery observations)
  (declare (xargs :guard t))
  (if (fn-heap-machine-sized-requestp request)
      (fn-heap-reserve-init-choose (fn-heap-init-candidates request)
                                   (fn-heap-small-candidate request)
                                   core nursery observations)
    request))

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

; KEYSTONE (PKT-582).  For a request that names no capacity (a bare `init',
; every mission), on every machine that holds the small candidate's whole
; reservation, `init' writes a request whose profile is valid and whose
; whole reservation that machine holds: the launcher runs the store `init'
; made.
(defthm fn-heap-reserve-init-request-is-accepted-where-small-is
  (implies (and (fn-heap-machine-sized-requestp request)
                (fn-heap-reserve-acceptsp (fn-heap-small-candidate request)
                                          core nursery observations))
           (fn-heap-reserve-acceptsp
            (fn-heap-reserve-init-request request core nursery observations)
            core nursery observations))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp
                                      fn-heap-small-candidate
                                      fn-heap-machine-sized-requestp))))

; The first candidate the machine holds is taken: scale when it holds scale.
(defthm fn-heap-reserve-init-request-takes-scale-when-it-fits
  (implies (and (fn-heap-machine-sized-requestp request)
                (fn-heap-reserve-acceptsp (list :scale (cadr (true-list-fix request)))
                                          core nursery observations))
           (equal (fn-heap-reserve-init-request request core nursery observations)
                  (list :scale (cadr (true-list-fix request)))))
  :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp
                                      fn-heap-machine-sized-requestp))))

(defthm fn-heap-reserve-init-request-keeps-the-operators-request-by-definition
  (implies (not (fn-heap-machine-sized-requestp request))
           (equal (fn-heap-reserve-init-request request core nursery observations)
                  request)))

; -----------------------------------------------------------------------------
; The figure is heap-figure's formula and grows with H and R: the default
; preset's 73,402,949 MB is 32 x (2 x 2^40 + 2^26) octets of lists and not a
; unit error.

(defthm fn-heap-figure-octets-is-the-formula-by-definition
  (equal (fn-heap-figure-octets profile core nursery)
         (+ (nfix core) (nfix nursery)
            (* 32 (+ (* 2 (fn-bs-profile-max-history-octets profile))
                     (fn-bs-profile-max-record-octets profile)))
            (* 2 (fn-ock-capture-budget profile))))
  :hints (("Goal" :in-theory (enable fn-heap-figure-octets fn-heap-list-octets
                                     fn-heap-buffer-octets))))

(defthm fn-heap-figure-octets-grows-with-history-and-record
  (implies (and (<= (fn-bs-profile-max-history-octets p1)
                    (fn-bs-profile-max-history-octets p2))
                (<= (fn-bs-profile-max-record-octets p1)
                    (fn-bs-profile-max-record-octets p2))
                (<= (fn-ock-capture-budget p1) (fn-ock-capture-budget p2)))
           (<= (fn-heap-figure-octets p1 core nursery)
               (fn-heap-figure-octets p2 core nursery)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-figure-octets fn-heap-list-octets
                                   fn-heap-buffer-octets)
                                  (fn-ock-capture-budget
                                   fn-bs-profile-max-history-octets
                                   fn-bs-profile-max-record-octets)))))
