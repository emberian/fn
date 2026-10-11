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

(defun fnn-heap-profile-refusal (condition)
  "Only ACL2's known refusal class permits an absent profile result."
  (if (eql (fnn-exit-code-for condition) +fnn-exit-refused+)
      nil
    (error condition)))

(defun fnn-peer-flight-profile (root)
  "Capture one inert peer authority file. Absence alone means no policy."
  (when (stringp root)
    (let* ((path (fnn-join root (fnn-core 'fn-pfp-file-name)))
           (present (not (null (fnn-lstat path))))
           (policy
             (fnn-core 'fn-pfp-read present
                       (when present
                         ;; NONBLOCK rejects a FIFO replacement at fstat
                         ;; instead of waiting before the type check.
                         (let ((fd (fnn-open path (logior sb-posix:o-rdonly
                                                        sb-posix:o-nonblock
                                                        +fnn-o-nofollow+))))
                           (fnn-unwind-cleanups
                               ((let ((info (fnn-fstat fd)))
                                  (unless (fnn-regular-p info)
                                    (fnn-fault "refusing non-regular peer profile: ~a" path))
                                  (handler-case
                                      (fnn-octet-list
                                       (fnn-read-bounded-fd fd (fnn-core 'fn-pfp-read-bound)))
                                    (fnn-input-overbound () nil))))
                             (fnn-close fd)))))))
      (cond ((eq policy :bad)
             (fnn-refuse "~a" (fnn-core 'fn-pfp-refusal-line)))
            ((null policy)
             (if present (fnn-fault "peer profile decoder returned absent for a present file") nil))
            ((fnn-core 'fn-pfr-policy-p policy) policy)
            (t (fnn-fault "peer profile decoder returned a malformed policy"))))))

(defun fnn-heap-store-profile (root)
  "The profile ROOT's store was saved with, or NIL when there is no store
there or ACL2 names a refusal. Corruption and internal faults propagate."
  (handler-case
      (let ((store (make-fnn-store root)))
        (and (fnn-lstat (fnn-config-path store))
             (progn (fnn-load-config store) (fnn-store-config store))))
    (fnn-store-error (condition) (fnn-heap-profile-refusal condition))))

(defun fnn-heap-print-store-line (root &optional cold-resources output-resources reclaim-live)
  "The next configured run's launch, as its probe will decide it (fnn-heap-serve-decision)."
  (when (stringp root)
    (let* ((absolute-root (fnn-absolute root))
           (profile (fnn-heap-store-profile absolute-root)))
      (when profile
        (fnn-out "~a" (fnn-core 'fn-heap-reserve-report-line
                                (fnn-heap-serve-decision profile absolute-root (fnn-heap-image-observation)
                                                         cold-resources output-resources
                                                         (fnn-peer-flight-profile absolute-root)
                                                         reclaim-live)))))))

(defun fnn-lim-print-values (root)
  "With no process running, `status' prints each live limit's three values
(books/limits-live.lisp fn-lim-values-lines, PRF-996): requested (the
configuration history's profile), funded=none (no process holds a
reservation; the next start funds what the heap= line reserves) and the
representation ceiling."
  (when (stringp root)
    (let ((requested (fnn-heap-store-profile root)))
      (when requested
        (dolist (line (fnn-core 'fn-lim-values-lines requested nil))
          (fnn-out "~a" line))))))

(defun fnn-heap-init-decision (request budget sizing)
  "ACL2's decision for what `init' writes (books/peer-flight-default.lisp
fn-pfd-init-decide: books/heap-reservation.lisp fn-heap-init-decide, PKT-582
in gpt-6's wave-5 shape, against the machine less the default peer flight
profile's launch reserve, which every store init writes carries): the request, or for
a capacity-free one the preset the budget holds (conservative unless
`init --largest'), within the budget of the physical memory less the OS's
share, the process's limits and `init --budget MB'; or a refusal.  BUDGET
and SIZING are the accepted init plan's (books/native-operator.lisp
fn-native-operator-result-init-budget / -init-sizing, row Q10b)."
  (let ((observations (fnn-heap-observations)))
    (fnn-core 'fn-pfd-init-decide request (fnn-heap-image-observation)
              +fnn-gc-nursery-octets+ (first observations) (rest observations)
              budget sizing)))

;; The decision and ACL2's note on it from ONE observation of the machine
;; (books/heap-reservation.lisp fn-heap-init-budget-note, finding R1 of the
;; public-node rehearsal): NIL, or the named budget `init --budget MB' below
;; the machine init observes -- an init run outside the service's memory
;; limit.  Returns (values DECISION NOTE); the caller prints ACL2's line.
(defun fnn-heap-init-decision-noted (request budget sizing)
  (let* ((observations (fnn-heap-observations))
         (decision (fnn-core 'fn-pfd-init-decide request (fnn-heap-image-observation)
                             +fnn-gc-nursery-octets+ (first observations)
                             (rest observations) budget sizing)))
    (values decision
            (fnn-core 'fn-heap-init-budget-note decision (first observations)
                      (rest observations) budget))))

(defun fnn-heap-init-request (request budget sizing)
  "The request `init' writes, or NIL when ACL2 refuses it."
  (fnn-core 'fn-heap-init-decision-request
            (fnn-heap-init-decision request budget sizing)))

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

;; The record log (lane log-recovery): the records a full replay
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
(defun fnn-heap-operator-store-profile (root result)
  "ACL2's profile source (books/native-control.lisp
fn-native-control-profile-source) selects the owner snapshot or the
stopped-store open; a run observes no liveness."
  (let* ((live *fnn-operator-live-owner*)
         (path (fnn-core 'fn-omr-control-path-octets result))
         (action (fnn-core 'fn-native-operator-host-result-native-action result))
         (liveness (if (and live (fnn-core 'fn-native-control-profile-observes-p action))
                       (funcall (fnn-olo-admin-observe live) root path t)
                     :offline)))
    (case (fnn-core 'fn-native-control-profile-source action liveness)
      (:owner (funcall (fnn-olo-profile live) path))
      (:held (fnn-refuse "store-held: the owner's profile is unavailable"))
      (:store (fnn-heap-store-profile root))
      (otherwise (fnn-fault "ACL2 returned an invalid profile source")))))

(defun fnn-heap-operator-profile (config-path words)
  (handler-case
      (let* ((argv-octets (fnn-operator-argv-octets words))
             (preflight (fnn-core 'fn-native-operator-host-preflight argv-octets)))
        (when (and (not (fnn-core 'fn-native-operator-host-preflight-needs-config-path-p
                                  preflight))
                   (fnn-core 'fn-native-operator-host-preflight-needs-config-p preflight))
          (let* ((config-octets (fnn-operator-read-config
                                 config-path (fnn-core 'fn-native-config-host-max-octets)))
                 (result (fnn-operator-run-at config-path config-octets argv-octets))
                 (root (fnn-core 'fn-native-operator-host-result-store-root result))
                 (store-profile nil))
            (when (and (eq (fnn-core 'fn-native-operator-host-result-status result) :accepted)
                       (stringp root))
              (values
               (if (eq (fnn-core 'fn-native-operator-host-result-native-action result) :init)
                   (let ((request (fnn-core 'fn-native-operator-host-result-init-profile
                                            result)))
                     (and (consp request)
                          (let ((profile (fnn-core 'fn-bs-profile-resolve
                                                   (fnn-heap-init-request
                                                    request
                                                    (fnn-core 'fn-native-operator-host-result-init-budget
                                                              result)
                                                    (fnn-core 'fn-native-operator-host-result-init-sizing
                                                              result))
                                                   nil)))
                            (and (not (eq (car profile) :invalid)) profile))))
                 (setf store-profile
                       (fnn-heap-operator-store-profile (fnn-absolute root) result)))
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
                      (let ((profile (if (eq action :init)
                                         (fnn-heap-operator-store-profile (fnn-absolute root) result)
                                       store-profile)))
                        (and profile
                             (fnn-heap-history-observation (fnn-absolute root)
                                                           profile)))))
               (fnn-core 'fn-native-operator-host-result-run-cold-resources result)
               (fnn-core 'fn-native-operator-host-result-run-output-resources result)
               (fnn-absolute root)
               nil
               (fnn-core 'fn-native-operator-host-result-run-reclaim-live result)
               ;; The operator's word and `--replay': a stopped `status'
               ;; reads its checkpoint header, `status --replay' and the
               ;; reports that share its action open the store
               ;; (books/heap-command.lisp fn-heap-command-growth).
               (fnn-core 'fn-native-operator-host-result-command result)
               (fnn-core 'fn-omr-status-replayp result))))))
    (fnn-store-error (condition)
      ;; A named semantic refusal has no profile; a broken core, ambiguous
      ;; persistence outcome or host error cannot become a no-store budget.
      (fnn-heap-profile-refusal condition))))

(defun fnn-heap-command-profile-base (argv)
  "The command's store profile (or NIL), the client connections its run
admits (0 when it is not a run) and ACL2's native action for an operator
command (NIL otherwise: a developer `store ROOT' verb gets the serve
figure), and the store's observed history octets for an offline verb ACL2
sizes by them (NIL otherwise), and its normalized explicit cold-resource
policy and output-allocation policy (each NIL when absent), and the
normalized store root for the pre-open DEFAULT backing reservation."
  (let ((bp-plan (fnn-core 'fn-bph-command-plan argv)))
  (cond ((eq (car bp-plan) :run)
         (let* ((root (fnn-absolute (second bp-plan)))
                (profile (fnn-heap-store-profile root)))
           (values profile (third bp-plan) :run nil nil nil root)))
        ((eq (car bp-plan) :refused)
         (fnn-refuse "~a" (fnn-core 'fn-bph-refusal-line (second bp-plan))))
        ((and (string= (or (first argv) "") "operator") (second argv))
         (multiple-value-bind (profile connections action observed cold-resources output-resources root
                               peer reclaim-live command replayp)
             (fnn-heap-operator-profile (second argv) (cddr argv))
           (declare (ignore peer))
           (values profile (if (integerp connections) connections 0) action observed cold-resources output-resources root
                   nil reclaim-live command replayp)))
        ;; The developer owner (`owner run ROOT PORT ONCE MAX-CONNECTIONS'):
        ;; a served run over ROOT's store, sized as the operator's run is by
        ;; that store's profile.  Left to the final clause it answered
        ;; profile=none, 1024 MB, below what the store's read pool needs.
        ((and (string= (or (first argv) "") "owner") (string= (or (second argv) "") "run")
              (third argv))
         (let* ((root (fnn-absolute (third argv)))
                (profile (fnn-heap-store-profile root))
                (connections (or (ignore-errors (parse-integer (sixth argv))) 0)))
           ;; OBSERVED as the operator's run observes it (ACL2 says which
           ;; actions are sized by the store on disk): left NIL the figure is
           ;; the profile's whole bound, 3026 MB against the 1934 MB the
           ;; operator's run decides for the same store.
           (values profile connections :run
                   (and profile (fnn-core 'fn-heap-operation-observes-p :run)
                        (fnn-heap-history-observation root profile))
                   nil nil root)))
        ((and (string= (or (first argv) "") "store") (third argv))
         (let ((profile (fnn-heap-store-profile (second argv))))
           (values profile 0 nil
                   (and profile (fnn-heap-history-observation (fnn-absolute (second argv))
                                                              profile)))))
        (t (values nil 0 nil nil)))))

(defun fnn-heap-command-profile (argv)
  "Add independent peer authority to the seven-field command projection.
Only ACL2-selected served launches observe that file; all command families
share this boundary, including standalone BP owners."
  (multiple-value-bind (profile connections action observed cold output root ignored reclaim-live
                        command replayp)
      (fnn-heap-command-profile-base argv)
    (declare (ignore ignored))
    (values profile connections action observed cold output root
            (when (fnn-core 'fn-pfr-operation-observes-p action)
              (fnn-peer-flight-profile root))
            reclaim-live command replayp)))

;; THE SERVED RUN'S LAUNCH (L-RUN-LAUNCH; books/heap-command.lisp fn-mo-serve-decide): the
;; dynamic space the run's LIMIT needs (the least resident observation less the pools the run funds:
;; DEFAULT's or the cold policy's, the output pool's, the peer flight's, and a BP served command's
;; session capacity, books/bp-session-profile.lisp fn-bpsp-node-capacity), plus those pools, refused
;; by name when the observed store's reopen exceeds LIMIT or the reservation exceeds the address
;; space; a BP command whose session terms price nothing is refused by name.  The run's capacity C'
;; is its configure's (host/owner-host.lisp fn-owner-memory-configure).  Answers (values DECISION
;; TOTALS IMG CONFIG EXTENT): the totals, image and configuration octets the decision read.
(defun fnn-heap-serve-decision (profile root core cold-resources output-resources peer reclaim-live
                                &optional bp-terms)
  (multiple-value-bind (totals extent) (fnn-heap-charged-totals root profile)
    (let* ((img (and profile (fnn-heap-img-observation profile)))
           (config (fnn-heap-config-octets root profile))
           (bp-need (and bp-terms
                         (fnn-core 'fn-bpsp-node-capacity (first bp-terms) (second bp-terms)
                                   (third bp-terms) (fourth bp-terms))))
           (pools (+ (fnn-core 'fn-mo-serve-pools profile cold-resources output-resources peer
                               (fnn-core 'fn-pio-direct-workers) (fnn-extent-cache-limit) root)
                     (or bp-need 0))))
      (values (if (and bp-terms (null bp-need))
                  (list :refused :invalid-bp-session-terms 0 0)
                (fnn-core 'fn-mo-serve-decide profile img +fnn-owner-service-nursery-octets+
                          reclaim-live cold-resources config (fnn-heap-resident-observations)
                          (fnn-heap-address-observations) core +fnn-gc-nursery-octets+ totals pools
                          (fnn-core 'fn-mo-serve-pool-threads cold-resources peer)))
              totals img config extent))))

;; What the model reads beside today's observations (books/heap-command.lisp):
;; the resident observations (physical memory, memory.max) apart from the
;; address-space ones (RLIMIT_DATA, RLIMIT_AS); the image as this probe finds
;; itself (the core file, its own RssAnon, one thread's stack and
;; thread-local storage); and the store's charged totals, which the schema-3
;; checkpoint header does not carry: NIL, every read-only command sized by
;; today's figure and its line naming the totals unseen, until A's landing-2
;; checkpoint field and suffix scan supply HDR and SUFFIX.
(defun fnn-heap-resident-observations ()
  (append (list (fnn-heap-physical-octets))
          #+linux (fnn-heap-cgroup-observations)))

(defun fnn-heap-address-observations ()
  (append (list (fnn-heap-rlimit 2))
          #+linux (list (fnn-heap-rlimit 9))))

(defun fnn-heap-tls-octets ()
  (handler-case
      (sb-alien:extern-alien "dynamic_values_bytes" (sb-alien:unsigned 32))
    (error () nil)))

(defun fnn-heap-img-observation (profile)
  (fnn-core 'fn-mo-img-observed (fnn-heap-core-octets)
            #+linux (fnn-heap-read-small "/proc/self/status") #-linux nil
            (fnn-core 'fn-heap-stack-kib profile) (fnn-heap-tls-octets)))

(defun fnn-heap-charged-totals (root profile)
  "The read decision's totals (books/heap-command.lisp fn-mo-observed-totals):
HDR the checkpoint's charged-totals header as the open reads it
(io.lisp fnn-checkpoint-header-observation, books/charged-totals-header.lisp
fn-cth-header-open), SUFFIX the log's past the header's S, EXTENT the largest
journal/ segment's observed size (the lstat of every segment the walk below
reads), which the read's open terms charge as its entry scratch (KEYSTONE
fn-mo-observed-log-holds-every-entry-read).  Answers (values TOTALS EXTENT):
the probe prints EXTENT on its line when its decision is the observed branch
(books/heap-log-extent-cap.lisp fn-lxc-command-line), the launcher passes it to
the command as FN_LOG_EXTENT_CAP, and the command's open refuses a segment
longer than it before reading any of its entries (io.lisp
fnn-log-observed-extent; KEYSTONE
fn-lxc-admitted-segment-entries-within-the-decided-log): a segment grown
past EXTENT between this walk and the read is refused, and one that grows
after the read checks its descriptor is read only within the size it
admitted (fn-lxc-admitted-entries-end-within-the-admitted-size).  ADAPTER (owner
Builder L, retired by L's store-log-open-scan): SUFFIX is the zero tot only
when the log observably holds no record past S -- no octet of any segment in
journal/ but the genesis (fnn-genesis-path, which holds no
record) is nonzero past a headed segment's padded head
(books/store-log-lineage.lisp fn-lgl-head-len; every entry opens with a
nonzero header, and the rotation preallocates the segment with zeros, so a
fresh segment's extent is past its head) -- else NIL, and the decision says
the header's totals are unseen.  A segment that is not a regular file leaves
EXTENT, and so the totals, unseen.  Unlocked: as fresh as the read."
  (let* ((store (and (stringp root) profile (make-fnn-store root)))
         (open (and store
                    (progn (setf (fnn-store-config store) profile)
                           (handler-case (fnn-checkpoint-header-observation store)
                             (fnn-os-error () nil)))))
         (hdr (and (consp open) (eq (first open) :ok) (second open)))
         (walk (and hdr
                    (handler-case
                        (let ((genesis (fnn-genesis-path store))
                              (head (fnn-nat (fnn-core 'fn-lgl-head-len (fnn-store-log-unit))))
                              (extent 0))
                          (dolist (name (fnn-log-segment-names store) (list t extent))
                            (let* ((path (fnn-join (fnn-journal-dir store) name))
                                   (st (fnn-lstat path)))
                              (unless (and st (fnn-regular-p st))
                                (return (list nil nil)))
                              (setf extent (max extent (sb-posix:stat-size st)))
                              (unless (or (equal path genesis)
                                          (null (fnn-log-first-nonzero path head)))
                                (return (list nil nil))))))
                      ((or fnn-os-error fnn-store-error) () nil))))
         (empty (first walk))
         (extent (second walk)))
    (values (fnn-core 'fn-mo-observed-totals hdr
                      (and empty (fnn-core 'fn-cth-empty-suffix hdr))
                      extent)
            extent)))

;; The configuration history's octets on disk (config/, the lstat sizes of
;; its regular files under the profile's listing bound), which loading the
;; profile reads whole (fnn-load-config-overlay); NIL when an OS call fails
;; (unobserved).  A namespace past the bound faults here as it faults the
;; loader (fnn-list-directory-bounded), and a core failure is a fault: both
;; reach the fence, since the served paths (mux, owner, io) read this figure.
(defun fnn-heap-config-octets (root profile)
  (handler-case
      (and (stringp root) profile
           (fnn-heap-directory-octets (fnn-config-dir (make-fnn-store root))
                                      ;; the reader's own namespace bound
                                      ;; (io.lisp fnn-bridge-config-observation-limit)
                                      (fnn-core 'fn-store-config-observation-limit profile)))
    (fnn-os-error () nil)))

;; The collector's card size of this image (SBCL's gencgc), NIL when the
;; runtime does not name one.
(defun fnn-heap-card-octets ()
  #+gencgc sb-vm:gencgc-card-bytes
  #-gencgc nil)

;; The command's decision (books/heap-command.lisp fn-heap-command-decide; a served run's,
;; fnn-heap-serve-decision) and what it read: (values DECISION TOTALS IMG CONFIG-OCTETS CARD EXTENT).
(defun fnn-heap-reservation (profile connections &optional action observed cold-resources output-resources root peer reclaim-live
                             bp-terms command replayp)
  (let* ((core (fnn-heap-image-observation))
         (class (fnn-core 'fn-heap-command-growth action command replayp)))
    (if (and (eq class :serves) profile)
        (multiple-value-bind (decision totals img config extent)
            (fnn-heap-serve-decision profile root core cold-resources output-resources peer reclaim-live
                                     bp-terms)
          (values decision totals img config nil extent))
      (let* ((machine (fnn-heap-observations))
             (reads (eq class :reads))
             (observation (and reads (multiple-value-list (fnn-heap-charged-totals root profile))))
             (totals (first observation))
             (extent (second observation))
             (img (and reads profile (fnn-heap-img-observation profile)))
             (config (and (member class '(:reads :header)) (fnn-heap-config-octets root profile)))
             (card (and reads (fnn-heap-card-octets))))
        (values (fnn-core 'fn-heap-command-decide action command replayp profile core
                          +fnn-gc-nursery-octets+ machine connections observed totals img config card
                          (fnn-heap-resident-observations) (fnn-heap-address-observations))
                totals img config card extent)))))

(defun fnn-command-heap (marker argv)
  (unless (string= marker "--")
    (error 'fnn-usage-error :message "heap -- ARGV..."))
  (multiple-value-bind (profile connections action observed cold-resources output-resources root peer
                        reclaim-live command replayp)
      (fnn-heap-command-profile argv)
    (multiple-value-bind (decision totals img config card extent)
        (fnn-heap-reservation profile connections action observed cold-resources output-resources root peer
                              reclaim-live (fnn-heap-bp-terms argv) command replayp)
      (let ((line (fnn-core 'fn-lxc-command-line decision action command replayp totals img config card
                            extent))
            (code (fnn-core 'fn-heap-decision-exit-code decision)))
        ;; The decision line on stdout whatever it is: the launcher tells
        ;; ACL2's refusal (a line, exit 1) from a runtime that never reached
        ;; ACL2 (no line) by it, and prints a refusal on stderr itself.
        (fnn-out "~a" line)
        code))))

;; THE COLLECTOR POLICY (memory landing 3+4; books/memory-model.lisp
;; fn-mm-collector, fn-mm-collector-due-p).  SBCL's generational collector
;; leaves promoted garbage in the older generations until their own triggers:
;; measured on fn-core, the resident set at rest was 2-4 x the live heap (W1 at
;; 4,000 records: 245-302 MB against 74 MB live), so the equation's collector
;; room (live + 2 x trigger) was not true of the process.  The policy makes it
;; a mechanism: after every collection ACL2 says whether a full collection is
;; due (the dynamic usage past the live usage at the last full collection by
;; more than RHO percent of it and twice the trigger in force); when it is, the
;; collector thread runs one and records the live usage it leaves.  One thread
;; (profile-limits :fixed-threads counts it); the hook only signals, so no
;; collection runs inside another's hook.  Measured cost at RHO 25: full
;; collections of 57-111 ms at 220-330 MB live (census m34-owner-gcp).  It
;; bounds dead memory, never data, and decides nothing ACL2 decides.
;; The collector thread owns the live figure (a local of its loop); the
;; after-GC hook only wakes it, and no global is written while actors run
;; (lock_discipline_check R1b).  The thread is joined by
;; fnn-heap-collector-policy-stop at the owner's cold shutdown.
(defvar *fnn-heap-collector-thread* nil)
(defvar *fnn-heap-collector-wake* (sb-thread:make-semaphore :name "fn-collector"))
(defvar *fnn-heap-collector-stop* (sb-thread:make-semaphore :name "fn-collector-stop"))

(defun fnn-heap-collector-after-gc ()
  (when (zerop (sb-thread:semaphore-count *fnn-heap-collector-wake*))
    (sb-thread:signal-semaphore *fnn-heap-collector-wake*)))

(defun fnn-heap-collector-run (live)
  "LIVE: the dynamic usage after the last full collection.  Each wake asks
ACL2 whether a full collection is due and runs one when it is.  Answers
:stopped when asked to stop, or the condition that ended it (the policy
bounds dead memory only; the condition is the thread's result, which
fnn-heap-collector-policy-stop re-signals as a fault on the joining owner)."
  (handler-case
      (loop
        (sb-thread:wait-on-semaphore *fnn-heap-collector-wake*)
        (when (sb-thread:try-semaphore *fnn-heap-collector-stop*)
          (return :stopped))
        (when (fnn-core 'fn-mm-collector-due-p (sb-kernel:dynamic-usage) live
                        (fnn-core 'fn-mm-collector-cfg (sb-ext:bytes-consed-between-gcs) nil))
          (sb-ext:gc :full t)
          (setq live (sb-kernel:dynamic-usage))))
    (serious-condition (condition)
      (fnn-err "collector policy stopped: ~a" condition)
      condition)))

(defun fnn-heap-collector-policy-start ()
  "Start the policy once per process, right after a full collection (the
owner's, when recovery is done: host/native/owner.lisp
fnn-owner-release-recovery-garbage), whose usage is the first live figure;
then the collector thread and the after-GC hook."
  (unless *fnn-heap-collector-thread*
    (let ((live (sb-kernel:dynamic-usage)))
      (setq *fnn-heap-collector-thread*
            (sb-thread:make-thread (lambda () (fnn-heap-collector-run live))
                                   :name "fn-collector"))
      (push #'fnn-heap-collector-after-gc sb-ext:*after-gc-hooks*))))

(defun fnn-heap-collector-policy-stop ()
  "Remove the hook, stop the collector thread and join it (a full collection
in progress finishes first).  Nothing when the policy never started."
  (let ((thread *fnn-heap-collector-thread*))
    (when thread
      (setq sb-ext:*after-gc-hooks*
            (remove #'fnn-heap-collector-after-gc sb-ext:*after-gc-hooks*))
      (sb-thread:signal-semaphore *fnn-heap-collector-stop*)
      (sb-thread:signal-semaphore *fnn-heap-collector-wake*)
      (let ((result (sb-thread:join-thread thread :default nil)))
        (setq *fnn-heap-collector-thread* nil)
        (when (typep result 'condition)
          (fnn-fault "the collector policy ended by ~a" result))))))

(fnn-register-verb "heap" #'fnn-command-heap)
