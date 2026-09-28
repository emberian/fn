;;; The process heap from the store profile (lane heap-from-profile,
;;; 2026-09-26; PKT-016; HST-013; PRF-198).
;;;
;;; This file observes and prints; books/heap-figure.lisp decides.  The
;;; observations: the saved core's length, the host's collection trigger
;;; (+fnn-gc-nursery-octets+), the machine's memory in each form the OS gives
;;; it (physical pages; on Linux the cgroup's memory.max from the process's
;;; own group up to the root, and RLIMIT_AS; RLIMIT_DATA everywhere, which
;;; OpenBSD's login classes set), and the store's saved profile (config.json,
;;; read without the writer lock as `principal' administration reads it).
;;;
;;;   heap -- ARGV...   the installed launcher's probe (packaging/fn): ACL2's
;;;                     decision for the command ARGV names, one line on
;;;                     stdout, always: `heap=MB MB profile=WORD machine=M MB
;;;                     stack=KB KB threads=N' (books/heap-reservation.lisp),
;;;                     exit 0; or ACL2's refusal line `refused REASON ...',
;;;                     exit 1 (outcome-class :refused), which the launcher
;;;                     prints on stderr as `fn: refused ...'.  A probe that
;;;                     prints no line never reached ACL2 (the runtime could
;;;                     not map the image under the process's limits): the
;;;                     launcher reports that as a fault, never as a refusal
;;;                     (lane openbsd-datasize).  On acceptance the launcher
;;;                     execs the image with `--dynamic-space-size MB
;;;                     --control-stack-size KBKB'.
;;;
;;; `operator CONFIG status' and `health' print the same line after their
;;; report; `operator CONFIG init' asks ACL2's `fn-heap-init-decide' what to
;;; write (fnn-heap-init-decision) and prints its line.

(in-package "ACL2")

(defun fnn-heap-sysconf (name)
  (sb-alien:alien-funcall
   (sb-alien:extern-alien "sysconf" (function sb-alien:long sb-alien:int))
   name))

;; _SC_PHYS_PAGES and _SC_PAGESIZE: each platform's <unistd.h> constants.
(defun fnn-heap-physical-octets ()
  (let ((pages #+linux (fnn-heap-sysconf 85) #+openbsd (fnn-heap-sysconf 500)
               #+darwin (fnn-heap-sysconf 200)
               #-(or linux openbsd darwin) -1)
        (size #+linux (fnn-heap-sysconf 30) #+openbsd (fnn-heap-sysconf 28)
              #+darwin (fnn-heap-sysconf 29)
              #-(or linux openbsd darwin) -1))
    (and (plusp pages) (plusp size) (* pages size))))

;; RLIMIT_DATA is 2 on Linux, OpenBSD and Darwin; RLIMIT_AS is Linux's 9.
;; The soft limit, or NIL when it is the platform's RLIM_INFINITY.
(defconstant +fnn-heap-rlim-infinity+
  #+openbsd (1- (expt 2 63))
  #-openbsd (1- (expt 2 64)))

(defun fnn-heap-rlimit (resource)
  (sb-alien:with-alien ((limit (sb-alien:array (sb-alien:unsigned 64) 2)))
    (let ((rc (sb-alien:alien-funcall
               (sb-alien:extern-alien
                "getrlimit"
                (function sb-alien:int sb-alien:int
                          (* (sb-alien:array (sb-alien:unsigned 64) 2))))
               resource (sb-alien:addr limit))))
      (let ((soft (sb-alien:deref limit 0)))
        (and (zerop rc) (/= soft +fnn-heap-rlim-infinity+) soft)))))

(defun fnn-heap-read-small (path)
  "PATH's octets (at most 4096) as a list, or NIL when it cannot be read."
  (handler-case
      (and (fnn-lstat path)
           (fnn-octet-list (fnn-read-regular-bounded path 4096)))
    (error () nil)))

;; Linux cgroup v2: /proc/self/cgroup's `0::PATH' line names the process's
;; group; memory.max there and in each ancestor bounds it, up to and
;; including the mount's root: inside a cgroup namespace (a container, an LXC
;; guest) that root IS a limited group, and its memory.max is the container's
;; limit (friend-path 2026-09-27: a 6 GiB container observed as the host's
;; 126 GB).  On a host the true root has no memory.max, and a missing file is
;; no observation.  Each file's octets go to ACL2 (`fn-heap-limit-of-octets'),
;; which reads the number.
#+linux
(defun fnn-heap-cgroup-observations ()
  (let* ((octets (fnn-heap-read-small "/proc/self/cgroup"))
         (text (and octets (map 'string #'code-char octets)))
         (start (and text (search "0::/" text)))
         (end (and start (position #\Newline text :start start)))
         (path (and start (subseq text (+ start 3) end)))
         (found nil))
    (loop while (and path (plusp (length path)))
          do (let ((octets (fnn-heap-read-small
                            (concatenate 'string "/sys/fs/cgroup" path "/memory.max"))))
               (when octets
                 (push (fnn-core 'fn-heap-limit-of-octets octets) found)))
             (let ((slash (position #\/ path :from-end t)))
               (setq path (and slash (plusp slash) (subseq path 0 slash)))))
    (let ((octets (and text (fnn-heap-read-small "/sys/fs/cgroup/memory.max"))))
      (when octets
        (push (fnn-core 'fn-heap-limit-of-octets octets) found)))
    found))

(defun fnn-heap-observations ()
  (append (list (fnn-heap-physical-octets) (fnn-heap-rlimit 2))
          #+linux (list (fnn-heap-rlimit 9))
          #+linux (fnn-heap-cgroup-observations)))

(defun fnn-heap-machine-octets ()
  (fnn-core 'fn-heap-machine-octets (fnn-heap-observations)))

(defun fnn-heap-core-octets ()
  (let ((core (and sb-ext:*core-pathname*
                   (sb-ext:native-namestring sb-ext:*core-pathname*))))
    (or (and core (handler-case (sb-posix:stat-size (sb-posix:stat core))
                    (error () nil)))
        0)))

;; The image observation books/heap-store-figure.lisp reads: (FILE . DYNAMIC),
;; the core file's length and the dynamic space in use now, at the probe's
;; start -- at least the core's dynamic content (the probe's own garbage
;; only adds), at most the file (ACL2 takes the least of the two).  Before
;; the records flip the whole file was counted as heap (a 200 MB production
;; core holds 109 MiB of dynamic content).
(defun fnn-heap-image-observation ()
  (cons (fnn-heap-core-octets) (sb-kernel:dynamic-usage)))

(defun fnn-heap-store-profile (root)
  "The profile ROOT's store was saved with, or NIL when there is no store
there or its config.json does not decode (the command itself then reports
that)."
  (handler-case
      (let ((store (make-fnn-store root)))
        (and (fnn-lstat (fnn-config-path store))
             (progn (fnn-load-config store) (fnn-store-config store))))
    (error () nil)))

(defun fnn-heap-print-store-line (root)
  "The `heap=' line `status' and `health' print after their report: the
reservation the launcher's probe makes for the store's next `run' over the
store as it is on disk (books/heap-reservation.lisp fn-heap-status-decide,
fn-heap-status-decide-is-the-launchers-run-reservation): one figure."
  (when (stringp root)
    (let ((profile (fnn-heap-store-profile root)))
      (fnn-out "~a" (fnn-core 'fn-heap-reserve-report-line
                              (fnn-core 'fn-heap-status-decide profile
                                        (fnn-heap-image-observation)
                                        +fnn-gc-nursery-octets+
                                        (fnn-heap-observations)
                                        (and profile
                                             (fnn-heap-history-observation root profile))))))))

(defun fnn-heap-env-octets (name)
  "NAME's value in the environment as octets for ACL2 to read (at most 32
of them: a longer value is refused there as malformed), or NIL when unset."
  (let ((value (sb-posix:getenv name)))
    (and value
         (map 'list (lambda (c) (min 255 (char-code c)))
              (subseq value 0 (min 33 (length value)))))))

(defun fnn-heap-init-decision (request)
  "ACL2's decision for what `init' writes (books/heap-reservation.lisp
fn-heap-init-decide, PKT-582 in gpt-6's wave-5 shape): the request, or for
a capacity-free one the preset the budget holds (conservative unless
FN_INIT_SIZING=largest), within the budget of the physical memory less the
OS's share, the process's limits and FN_INIT_BUDGET_MB; or a refusal."
  (let ((observations (fnn-heap-observations)))
    (fnn-core 'fn-heap-init-decide request (fnn-heap-image-observation)
              +fnn-gc-nursery-octets+ (first observations) (rest observations)
              (fnn-heap-env-octets "FN_INIT_BUDGET_MB")
              (fnn-heap-env-octets "FN_INIT_SIZING"))))

;; The decision and ACL2's note on it from ONE observation of the machine
;; (books/heap-reservation.lisp fn-heap-init-budget-note, finding R1 of the
;; public-node rehearsal): NIL, or the named budget FN_INIT_BUDGET_MB below
;; the machine init observes -- an init run outside the service's memory
;; limit.  Returns (values DECISION NOTE); the caller prints ACL2's line.
(defun fnn-heap-init-decision-noted (request)
  (let* ((observations (fnn-heap-observations))
         (budget (fnn-heap-env-octets "FN_INIT_BUDGET_MB"))
         (decision (fnn-core 'fn-heap-init-decide request (fnn-heap-image-observation)
                             +fnn-gc-nursery-octets+ (first observations)
                             (rest observations) budget
                             (fnn-heap-env-octets "FN_INIT_SIZING"))))
    (values decision
            (fnn-core 'fn-heap-init-budget-note decision (first observations)
                      (rest observations) budget))))

(defun fnn-heap-init-request (request)
  "The request `init' writes, or NIL when ACL2 refuses it."
  (fnn-core 'fn-heap-init-decision-request (fnn-heap-init-decision request)))

;; The store's history octets on disk (PKT-686 item 1): the sizes of the
;; regular files directly under journal/ (the record log's segments) and
;; checkpoints/ and the state checkpoint's, summed before the image starts.  An upper bound
;; of the stored octets the offline verbs hold copies of (heap-figure's
;; fn-heap-operation-history-octets states the use).  NIL -- the profile's H
;; then -- when a directory holds more entries than ACL2's listing bound, an
;; entry is not a regular file, or anything cannot be observed; the probe
;; never faults on it.
(defun fnn-heap-directory-octets (path limit)
  (let ((st (fnn-lstat path)))
    (cond ((null st) 0)
          ((not (fnn-directory-p st)) nil)
          (t (let ((sum 0))
               (dolist (name (fnn-list-directory-bounded path limit "history observation")
                             sum)
                 (let ((entry (fnn-lstat (fnn-join path name))))
                   (unless (and entry (fnn-regular-p entry))
                     (return nil))
                   (incf sum (sb-posix:stat-size entry)))))))))

(defun fnn-heap-history-observation (root profile)
  (let ((octets (fnn-heap-history-octets root profile))
        (records (handler-case
                     (let ((store (make-fnn-store root)))
                       (and (fnn-lstat (fnn-journal-dir store))
                            (fnn-heap-log-records store profile)))
                   (error () nil))))
    (if (and (integerp octets) (integerp records))
        (cons octets records)
      octets)))

(defun fnn-heap-listing-bound (profile)
  (fnn-core 'fn-heap-history-listing-bound profile))

;; Format 9 (the record log; lane log-recovery): the records a full replay
;; reads are the log's entries, each at least one write unit on disk
;; (books/store-log-route.lisp fn-olr-entry-octets pads every entry to the
;; unit), so the segments' octets over the unit bound them.  A state
;; checkpoint's prefix is not counted there: with one present the count is
;; not observed (NIL: the profile's T).
(defun fnn-heap-log-records (store profile)
  (let ((octets (fnn-heap-directory-octets (fnn-journal-dir store)
                                           (fnn-heap-listing-bound profile))))
    (and (integerp octets)
         (null (fnn-lstat (fnn-state-checkpoint-path store)))
         (floor octets (fnn-store-log-unit)))))

(defun fnn-heap-history-octets (root profile)
  (handler-case
      (let* ((store (make-fnn-store root))
             (limit (fnn-core 'fn-heap-history-listing-bound profile))
             (state (fnn-lstat (fnn-state-checkpoint-path store)))
             (parts (list ;; The record log's segments.
                          (fnn-heap-directory-octets (fnn-journal-dir store) limit)
                          (fnn-heap-directory-octets (fnn-join root "checkpoints") limit)
                          (cond ((null state) 0)
                                ((fnn-regular-p state) (sb-posix:stat-size state))
                                (t nil)))))
        (and (every #'integerp parts) (reduce #'+ parts)))
    (error () nil)))

;; The profile the command ARGV will run under: the store its operator
;; configuration names (the init request's target for `init'), the store a
;; `store ROOT' verb names, or NIL.  Every read is bounded (fn.toml by
;; ACL2's configuration bound, config.json at 16 KiB); a configuration or
;; command the operator plan refuses has no profile, and the command itself
;; reports the refusal under the no-store figure.
(defun fnn-heap-operator-profile (config-path words)
  (handler-case
      (let* ((argv-octets (fnn-operator-argv-octets
                           words
                           (fnn-core 'fn-native-operator-host-argv-max-arguments)
                           (fnn-core 'fn-native-operator-host-argv-max-octets)))
             (preflight (fnn-core 'fn-native-operator-host-preflight argv-octets)))
        (when (and (not (fnn-core 'fn-native-operator-host-preflight-needs-config-path-p
                                  preflight))
                   (fnn-core 'fn-native-operator-host-preflight-needs-config-p preflight))
          (let* ((config-octets (fnn-operator-read-config
                                 config-path (fnn-core 'fn-native-config-host-max-octets)))
                 (result (fnn-core 'fn-native-operator-host-run config-octets argv-octets))
                 (root (fnn-core 'fn-native-operator-host-result-store-root result)))
            (when (and (eq (fnn-core 'fn-native-operator-host-result-status result) :accepted)
                       (stringp root))
              (values
               (if (eq (fnn-core 'fn-native-operator-host-result-native-action result) :init)
                   (let ((request (fnn-core 'fn-native-operator-host-result-init-profile
                                            result)))
                     (and (consp request)
                          (let ((profile (fnn-core 'fn-bs-profile-resolve
                                                   (fnn-heap-init-request request) nil)))
                            (and (not (eq (car profile) :invalid)) profile))))
                 (fnn-heap-store-profile (fnn-absolute root)))
               ;; The owner's client workers a `run' admits, ACL2's figure
               ;; fnn-operator-execute passes on; for `init' the connections
               ;; init judged the store by (fn-heap-reserve-init-connections),
               ;; so the probe judges the store init makes as it will run.
               (if (eq (fnn-core 'fn-native-operator-host-result-native-action
                                 result)
                       :init)
                   (fnn-core 'fn-heap-reserve-init-connections)
                 ;; A run's owner bound is structural since PRF-211; ACL2
                 ;; says which connections the reservation's threads hold.
                 (fnn-core 'fn-heap-reserve-run-connections
                           (fnn-core 'fn-native-operator-host-result-run-max-connections
                                     result)))
               ;; ACL2's native action for ARGV: the compaction verbs get
               ;; their own figure (fn-heap-reserve-operation-decide, PKT-686).
               (fnn-core 'fn-native-operator-host-result-native-action result)
               ;; The history the offline verbs are sized by, observed only
               ;; for the actions ACL2 sizes by it (PKT-686 item 1).
               (let ((action (fnn-core 'fn-native-operator-host-result-native-action
                                       result)))
                 (and (fnn-core 'fn-heap-operation-observes-p action)
                      (let ((profile (fnn-heap-store-profile (fnn-absolute root))))
                        (and profile
                             (fnn-heap-history-observation (fnn-absolute root)
                                                           profile))))))))))
    (error () nil)))

(defun fnn-heap-command-profile (argv)
  "The command's store profile (or NIL), the client connections its run
admits (0 when it is not a run) and ACL2's native action for an operator
command (NIL otherwise: a developer `store ROOT' verb gets the serve
figure), and the store's observed history octets for an offline verb ACL2
sizes by them (NIL otherwise)."
  (cond ((and (string= (or (first argv) "") "operator") (second argv))
         (multiple-value-bind (profile connections action observed)
             (fnn-heap-operator-profile (second argv) (cddr argv))
           (values profile (if (integerp connections) connections 0) action observed)))
        ((and (string= (or (first argv) "") "store") (third argv))
         (let ((profile (fnn-heap-store-profile (second argv))))
           (values profile 0 nil
                   (and profile (fnn-heap-history-observation (fnn-absolute (second argv))
                                                              profile)))))
        (t (values nil 0 nil nil))))

;; The whole reservation (books/heap-reservation.lisp
;; fn-heap-reserve-operation-decide, HST-025, PKT-686): heap-figure's heap for
;; the command ACTION names (the compaction verbs' operation figure, every
;; other command's fn-heap-reserve-decide), then the thread stacks the node's
;; threads reserve beside it; the launcher passes `--control-stack-size KB'
;; too.
(defun fnn-heap-reservation (profile connections &optional action observed)
  (fnn-core 'fn-heap-reserve-operation-decide action profile (fnn-heap-image-observation)
            +fnn-gc-nursery-octets+ (fnn-heap-observations) connections observed))

(defun fnn-command-heap (marker argv)
  (unless (string= marker "--")
    (error 'fnn-usage-error :message "heap -- ARGV..."))
  (let* ((decision (multiple-value-bind (profile connections action observed)
                       (fnn-heap-command-profile argv)
                     (fnn-heap-reservation profile connections action observed)))
         (line (fnn-core 'fn-heap-reserve-report-line decision))
         (code (fnn-core 'fn-heap-decision-exit-code decision)))
    ;; The decision line on stdout whatever it is: the launcher tells ACL2's
    ;; refusal (a line, exit 1) from a runtime that never reached ACL2 (no
    ;; line) by it, and prints a refusal on stderr itself.
    (fnn-out "~a" line)
    code))

(fnn-register-verb "heap" #'fnn-command-heap)
