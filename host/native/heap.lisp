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
;;;   heap -- ARGV...   the installed launcher's probe (packaging/fn): the
;;;                     figure for the command ARGV names, one line on stdout
;;;                     `heap=MB MB profile=WORD machine=M MB', exit 0; or
;;;                     ACL2's refusal line on stderr, exit 1 (outcome-class
;;;                     :refused).  The launcher then execs the image with
;;;                     `--dynamic-space-size MB'.
;;;
;;; `operator CONFIG status' and `health' print the same line after their
;;; report; `operator CONFIG init' with a bare request resolves ACL2's
;;; `fn-heap-init-request' against the observed machine.

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
;; group; memory.max there and in each ancestor bounds it.  Each file's
;; octets go to ACL2 (`fn-heap-limit-of-octets'), which reads the number.
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

(defun fnn-heap-store-profile (root)
  "The profile ROOT's store was saved with, or NIL when there is no store
there or its config.json does not decode (the command itself then reports
that)."
  (handler-case
      (let ((store (make-fnn-store root)))
        (and (fnn-lstat (fnn-config-path store))
             (progn (fnn-load-config store) (fnn-store-config store))))
    (error () nil)))

(defun fnn-heap-decision (profile)
  (fnn-core 'fn-heap-decide profile (fnn-heap-core-octets) +fnn-gc-nursery-octets+
            (fnn-heap-observations)))

(defun fnn-heap-report-line (profile)
  (fnn-core 'fn-heap-report-line (fnn-heap-decision profile)))

(defun fnn-heap-print-store-line (root)
  "The `heap=' line `status' and `health' print after their report."
  (when (stringp root)
    (fnn-out "~a" (fnn-heap-report-line (fnn-heap-store-profile root)))))

(defun fnn-heap-init-request (request)
  "The request `init' resolves: ACL2's small default on a small machine."
  (fnn-core 'fn-heap-init-request request (fnn-heap-machine-octets)))

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
              (if (eq (fnn-core 'fn-native-operator-host-result-native-action result) :init)
                  (let ((request (fnn-core 'fn-native-operator-host-result-init-profile
                                           result)))
                    (and (consp request)
                         (let ((profile (fnn-core 'fn-bs-profile-resolve
                                                  (fnn-heap-init-request request) nil)))
                           (and (not (eq (car profile) :invalid)) profile))))
                (fnn-heap-store-profile (fnn-absolute root)))))))
    (error () nil)))

(defun fnn-heap-command-profile (argv)
  (cond ((and (string= (or (first argv) "") "operator") (second argv))
         (fnn-heap-operator-profile (second argv) (cddr argv)))
        ((and (string= (or (first argv) "") "store") (third argv))
         (fnn-heap-store-profile (second argv)))
        (t nil)))

(defun fnn-command-heap (marker argv)
  (unless (string= marker "--")
    (error 'fnn-usage-error :message "heap -- ARGV..."))
  (let* ((decision (fnn-heap-decision (fnn-heap-command-profile argv)))
         (line (fnn-core 'fn-heap-report-line decision))
         (code (fnn-core 'fn-heap-decision-exit-code decision)))
    (if (eql code +fnn-exit-ok+)
        (fnn-out "~a" line)
      (fnn-err "fn: ~a" line))
    code))

(fnn-register-verb "heap" #'fnn-command-heap)
