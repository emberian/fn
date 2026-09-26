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
; The decision (`fn-heap-reserve-decide'): heap-figure's decision, and when
; that accepts an admitted profile, the stack for its largest article and
; the total HEAP + THREADS x (STACK + RUNTIME), refused by name when it
; exceeds the machine (the least observation, as heap-figure's).
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
(defconst *fn-heap-thread-runtime-octets* (* 3 *fn-heap-mib*))
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

(defun fn-heap-reservation-octets (mb stack-kib threads)
  (declare (xargs :guard t))
  (+ (* *fn-heap-mib* (nfix mb))
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
                                                     stack threads))
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
                                  (fn-heap-decision-mb d)
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
