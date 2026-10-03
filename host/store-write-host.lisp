; The writable store verbs as ACL2 :program code (lane extract-writable,
; 2026-09-28): `store ROOT recover', `store ROOT post' and `store ROOT
; node-secret create|rotate', as host/native/io.lisp runs them
; (fnn-command-recover, fnn-command-post, fnn-command-node-secret), so the
; extractor extracts them and the extracted program writes a store.
;
; Direction (coordinator, 2026-09-28, lane extract-2's e2): the host is byte
; primitives; the sequence belongs in ACL2 where the extractor reads it.
; host/store-open-host.lisp did the reader's read-only open; this file is the
; writable closure: the exclusive open with P-LOG-RECOVER on the active
; segment (fnn-open-live-store, fnn-acquire, fnn-recover-log), the staging
; sweep and the interrupted drop, the reservation, the prepare and seal, the
; publication on the record log (fnn-log-publish: the compressed append,
; fn-lgc-take, the extension, P-BATCH's append and barrier), the finish, and
; the node-secret key files.  Every decision is the ACL2 function the image
; calls; what io.lisp does in raw Lisp between the calls -- the sequence, the
; checks on what ACL2 returned, the fault cuts (fnn-at, fnn-log-at), the
; handlers and their texts -- is here.  The SBCL image does not load this
; file (host/native/build.lisp): it runs io.lisp, and the extraction gate's
; stateful differential (tools/extract/stateful.py) holds the two to the same
; outputs, exit codes, files and subsequent opens.
;
; CALLS INTO ACL2.  io.lisp calls each ACL2 entry through fnn-call (the entry
; guard, then the *1* function under guard-checking t).  The extractor treats
; a call from a function of this file (and store-open-host.lisp) to an fn-
; core function the same way: a boundary call (tools/extract/chicken.py,
; `port' callers; the front end adds those callees to the boundary).
;
; RESULTS.  A step answers (:ok . VALUES) or (CLASS TEXT) with CLASS one of
; :fault, :refused, :open-refusal, :indeterminate, :usage, :internal, or
; (:os TEXT ERRNO): io.lisp's condition types (fnn-store-fault,
; fnn-store-error, fnn-store-open-refusal, fnn-store-indeterminate,
; fnn-usage-error, a raw serious-condition, fnn-os-error), each handler-case
; of io.lisp written out as the test on CLASS it performs.  TEXT is the
; condition's report, io.lisp's words.
;
; NOT HERE (each refused by name, never approximated): a store holding a
; state checkpoint (its open is arena-store's page store), the owner's
; batched commit (*fnn-log-batch*: the served owner, host/native/owner.lisp),
; a staged buffer handle (the owner's buffer prepare): the offline verbs have
; none, so no member is reseated (fnn-log-members-in-flight finds no handle).
(in-package "ACL2")

; ---------------------------------------------------------------------------
; The host primitives this file adds (stubs; tools/extract/hostio.scm).
; Answers of a syscall: :ok, (:ok VALUE ...), or (:error ERRNO TEXT) with
; TEXT fnn-os-error's report of it ("[Errno N] STRERROR" and ": 'PATH'" where
; io.lisp's fnn-posix names the path).

; the environment variable NAME, or NIL
(defun fn-hx-getenv (name) (declare (xargs :mode :program) (ignore name)) (fn-hx-stub fn-hx-getenv))
; strerror(ERRNO)
(defun fn-hx-strerror (errno) (declare (xargs :mode :program) (ignore errno)) (fn-hx-stub fn-hx-strerror))
; SIGKILL to this process (a developer cut); never returns
(defun fn-hx-kill-self () (declare (xargs :mode :program)) (fn-hx-stub fn-hx-kill-self))
; one line (TEXT and LF) to standard output, flushed
(defun fn-hx-out (text) (declare (xargs :mode :program) (ignore text)) (fn-hx-stub fn-hx-out))
; open(PATH, O_RDWR|O_CREAT|O_NOFOLLOW, 0600), fstat, flock(LOCK_EX|LOCK_NB):
; (:ok H) | (:error ERRNO TEXT) (the open) | :not-regular | :locked
(defun fn-hx-lock-exclusive (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-lock-exclusive))
; flock(LOCK_UN) then close of a lock handle: :ok
(defun fn-hx-unlock (h) (declare (xargs :mode :program) (ignore h)) (fn-hx-stub fn-hx-unlock))
; open(PATH, O_RDWR|O_NOFOLLOW) and fstat: (:ok H SIZE) | (:error ERRNO TEXT)
(defun fn-hx-open-rw (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-open-rw))
; open(PATH, O_RDONLY|O_NOFOLLOW) and fstat, the handle registered for the
; process's life (the extent realizer's file id): (:ok H SIZE) | (:error ...)
(defun fn-hx-open-ro (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-open-ro))
; open(PATH, O_WRONLY|O_CREAT|O_EXCL[|O_NOFOLLOW], 0600): (:ok H) | (:error ...)
(defun fn-hx-create-excl (path nofollow)
  (declare (xargs :mode :program) (ignore path nofollow)) (fn-hx-stub fn-hx-create-excl))
; close(2) of a read-write handle: :ok | (:error ...)
(defun fn-hx-close (h) (declare (xargs :mode :program) (ignore h)) (fn-hx-stub fn-hx-close))
; lseek(OFF) and write(2) of OCTETS to completion: :ok | (:error ...)
(defun fn-hx-pwrite (h off octets) (declare (xargs :mode :program) (ignore h off octets)) (fn-hx-stub fn-hx-pwrite))
; the same with N zero octets
(defun fn-hx-pwrite-zeros (h off n) (declare (xargs :mode :program) (ignore h off n)) (fn-hx-stub fn-hx-pwrite-zeros))
; write(2) of OCTETS at the handle's position, to completion: :ok | (:error ...)
(defun fn-hx-write-all (h octets) (declare (xargs :mode :program) (ignore h octets)) (fn-hx-stub fn-hx-write-all))
; lseek(OFF) and read to completion, N octets: (:ok OCTETS) (fewer at end of file) | (:error ...)
(defun fn-hx-read-at (h off n) (declare (xargs :mode :program) (ignore h off n)) (fn-hx-stub fn-hx-read-at))
; fdatasync(2) (Linux; the platform's barrier elsewhere): :ok | (:error ...)
(defun fn-hx-fdatasync (h) (declare (xargs :mode :program) (ignore h)) (fn-hx-stub fn-hx-fdatasync))
; the durable barrier (fnn-durable-barrier): :ok | (:error ...)
(defun fn-hx-fsync (h) (declare (xargs :mode :program) (ignore h)) (fn-hx-stub fn-hx-fsync))
; zeros allocated over [FROM, EXTENT) (posix_fallocate; written elsewhere): :ok | (:error ...)
(defun fn-hx-preallocate (h from extent)
  (declare (xargs :mode :program) (ignore h from extent)) (fn-hx-stub fn-hx-preallocate))
; unlink(2), mkdir(2) mode 0700, link(2), rename(2): :ok | (:error ...)
(defun fn-hx-unlink (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-unlink))
(defun fn-hx-mkdir (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-mkdir))
(defun fn-hx-link (old new) (declare (xargs :mode :program) (ignore old new)) (fn-hx-stub fn-hx-link))
(defun fn-hx-rename (old new) (declare (xargs :mode :program) (ignore old new)) (fn-hx-stub fn-hx-rename))
; lstat(2) as fnn-lstat reads it: (:absent) | (:ok KIND SIZE MODE) with KIND
; :regular :directory :symlink :other | (:error ERRNO TEXT)
(defun fn-hx-lstat-full (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-lstat-full))
; fnn-list-directory-window: (:ok NAMES MORE), NAMES at most LIMIT in
; directory order | (:error ERRNO TEXT)
(defun fn-hx-list-window (path limit) (declare (xargs :mode :program) (ignore path limit)) (fn-hx-stub fn-hx-list-window))
; fnn-list-directory-bounded's listing: (:ok NAMES) | (:over) past LIMIT | (:error ERRNO TEXT)
(defun fn-hx-list-bounded (path limit) (declare (xargs :mode :program) (ignore path limit)) (fn-hx-stub fn-hx-list-bounded))
; fnn-read-regular-bounded over a no-follow descriptor:
; (:ok OCTETS) | (:non-regular) | (:overbound) | (:error ERRNO TEXT)
(defun fn-hx-read-file (path maximum) (declare (xargs :mode :program) (ignore path maximum)) (fn-hx-stub fn-hx-read-file))
; the clock readings (fnn-store-prepare-observation): (MONO-MS SECONDS MICROSECONDS)
(defun fn-hx-clock () (declare (xargs :mode :program)) (fn-hx-stub fn-hx-clock))
; N octets of the OS CSPRNG as a list: (:ok OCTETS) | (:error ERRNO TEXT)
(defun fn-hx-random-octets (n) (declare (xargs :mode :program) (ignore n)) (fn-hx-stub fn-hx-random-octets))
; the lowercase hex of N random octets (a staging name's suffix)
(defun fn-hx-random-hex (n) (declare (xargs :mode :program) (ignore n)) (fn-hx-stub fn-hx-random-hex))
; fnn-fsync-dir: open(PATH, O_RDONLY|O_DIRECTORY) and the durable barrier: :ok | (:error ...)
(defun fn-hx-sync-dir (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-sync-dir))
; getpid(2)
(defun fn-hx-getpid () (declare (xargs :mode :program)) (fn-hx-stub fn-hx-getpid))
; the image's LZ4-HC encoder (lib/libfn-lz4, host/native/lz4.lisp
; fnn-lz4-candidate) over octets [K, K+N) of SRC in at most CAP octets:
; an octet list | :none | (:code C) the encoder's answer outside its domain
(defun fn-hx-lz4-candidate (src k n cap)
  (declare (xargs :mode :program) (ignore src k n cap)) (fn-hx-stub fn-hx-lz4-candidate))
; the current directory (fnn-absolute's getcwd)
(defun fn-hx-getcwd () (declare (xargs :mode :program)) (fn-hx-stub fn-hx-getcwd))

; ---------------------------------------------------------------------------
; Values, results and texts.

(defun fn-xw-get (x k) (declare (xargs :mode :program)) (cdr (assoc-eq k x)))
(defun fn-xw-put (x k v) (declare (xargs :mode :program)) (put-assoc-eq k v x))
(defun fn-xw-okp (r) (declare (xargs :mode :program)) (and (consp r) (eq (car r) :ok)))
(defun fn-xw-fault (text) (declare (xargs :mode :program)) (list :fault text))
(defun fn-xw-refuse (text) (declare (xargs :mode :program)) (list :refused text))
(defun fn-xw-indeterminate (text) (declare (xargs :mode :program)) (list :indeterminate text))
; a primitive's (:error ERRNO TEXT) as the fnn-os-error it is
(defun fn-xw-os (e) (declare (xargs :mode :program)) (list :os (caddr e) (cadr e)))
(defun fn-xw-errp (r) (declare (xargs :mode :program)) (and (consp r) (eq (car r) :error)))
; the report of a result, as `~a' of its condition prints it
(defun fn-xw-text (r) (declare (xargs :mode :program)) (cadr r))
; a store error of any kind but an OS error (handler-case's fnn-store-error)
(defun fn-xw-store-error-p (r)
  (declare (xargs :mode :program))
  (member-eq (car r) '(:fault :refused :open-refusal :indeterminate :usage)))

(defun fn-xw-digits (n acc)
  (declare (xargs :mode :program))
  (if (< n 10) (cons (code-char (+ 48 n)) acc)
    (fn-xw-digits (floor n 10) (cons (code-char (+ 48 (mod n 10))) acc))))
; `~d' of an integer
(defun fn-xw-dec (n)
  (declare (xargs :mode :program))
  (cond ((not (integerp n)) "?")
        ((< n 0) (concatenate 'string "-" (coerce (fn-xw-digits (- n) nil) 'string)))
        (t (coerce (fn-xw-digits n nil) 'string))))
(defun fn-xw-cat (strings)
  (declare (xargs :mode :program))
  (if (endp strings) "" (concatenate 'string (car strings) (fn-xw-cat (cdr strings)))))
; `~(~a~)' of a keyword
(defun fn-xw-kw (k) (declare (xargs :mode :program)) (string-downcase (symbol-name k)))

; SBCL's ~S of a string (quotes; a backslash before " and \)
(defun fn-xw-escape (cs)
  (declare (xargs :mode :program))
  (cond ((endp cs) nil)
        ((member (car cs) '(#\" #\\)) (list* #\\ (car cs) (fn-xw-escape (cdr cs))))
        (t (cons (car cs) (fn-xw-escape (cdr cs))))))
(defun fn-xw-quote (s)
  (declare (xargs :mode :program))
  (concatenate 'string "\"" (coerce (fn-xw-escape (coerce s 'list)) 'string) "\""))

; fnn-os-fail ERRNO with no path, as its report prints
(defun fn-xw-os-errno (errno)
  (declare (xargs :mode :program))
  (list :os (fn-xw-cat (list "[Errno " (fn-xw-dec errno) "] " (fn-hx-strerror errno))) errno))

; fnn-action: a value outside io.lisp's +fnn-actions+ is a fault
(defun fn-xw-action (value)
  (declare (xargs :mode :program))
  (if (member-eq value '(:ready :prepared :durable :aborted :indeterminate :duplicate :conflict :absent
                         :invalid :refused :fault :recovering :frontier-staged :frontier-data-durable
                         :frontier-attempted :record-staged :record-data-durable :record-attempted
                         :reserved :aborting :completing :fenced-frontier :fenced-record :fenced-recovery))
      (list :ok value)
    (fn-xw-fault "unexpected ACL2 action: ?")))

(defun fn-xw-natp-result (value)
  ; fnn-nat
  (declare (xargs :mode :program))
  (if (and (integerp value) (<= 0 value)) (list :ok value) (fn-xw-fault "ACL2 returned a non-natural")))

(defun fn-xw-octet-list-p (x)
  (declare (xargs :mode :program))
  (if (consp x) (and (integerp (car x)) (<= 0 (car x)) (< (car x) 256) (fn-xw-octet-list-p (cdr x)))
    (null x)))

(defun fn-xw-string-mem (s l)
  (declare (xargs :mode :program))
  (and (consp l) (or (equal s (car l)) (fn-xw-string-mem s (cdr l)))))

; ---------------------------------------------------------------------------
; The developer cuts (fnn-at, fnn-log-at) and their selectors.
;
; The STORE is an alist (io.lisp's fnn-store struct): :root :fault :lock
; :config :fenced :pending :frontier :served :domain :generation :log
; :open-mode :orphans :orphans-more :repair :reports :lz-tally.  FAULT is
; (POINTS CLASS MESSAGE), POINTS the lowercase cut names one selector arms,
; CLASS :os, :kill, :indeterminate or :refused.

(defun fn-xw-at (store point)
  ; fnn-at: (:ok) or the armed class's condition; :kill never returns
  (declare (xargs :mode :program))
  (let ((fault (fn-xw-get store :fault)))
    (if (and fault (fn-xw-string-mem point (car fault)))
        (case (cadr fault)
          (:os (fn-xw-os-errno 5))
          (:kill (prog2$ (fn-hx-kill-self)
                         (fn-xw-fault "test SIGKILL did not terminate the process")))
          (:indeterminate (fn-xw-indeterminate (caddr fault)))
          (otherwise (fn-xw-refuse (caddr fault))))
      (list :ok))))

(defun fn-xw-log-at (point)
  ; fnn-log-at: FN_NATIVE_LOG_FAULT=NAME kills the process at NAME
  (declare (xargs :mode :program))
  (let ((armed (fn-hx-getenv "FN_NATIVE_LOG_FAULT")))
    (if (and (stringp armed) (equal armed point))
        (prog2$ (fn-hx-kill-self) (fn-xw-fault "test SIGKILL did not terminate the process"))
      (list :ok))))

(defun fn-xw-last-colon (cs i best)
  (declare (xargs :mode :program))
  (if (endp cs) best (fn-xw-last-colon (cdr cs) (+ 1 i) (if (eql (car cs) #\:) i best))))

(defun fn-xw-selector (raw name cuts msg)
  ; the MODEL-CUT:ACTION selectors (fnn-post-test-fault's and
  ; fnn-recovery-test-fault's shape): (:ok FAULT-OR-NIL) or a fault
  (declare (xargs :mode :program))
  (if (not (stringp raw)) (list :ok nil)
    (let ((colon (fn-xw-last-colon (coerce raw 'list) 0 nil)))
      (if (not colon)
          (fn-xw-fault (fn-xw-cat (list "invalid " name " (expected MODEL-CUT:eio|kill)")))
        (let* ((label (subseq raw 0 colon))
               (point (string-downcase label))
               (action (subseq raw (+ 1 colon) (length raw))))
          (cond ((and (equal point "record-prepublish") (equal name "FN_NATIVE_POST_FAULT"))
                 (if (equal action "refuse")
                     (list :ok (list (list point) :refused "developer-only known refusal before publication"))
                   (fn-xw-fault "FN_NATIVE_POST_FAULT record-prepublish takes only :refuse")))
                ((not (fn-xw-string-mem point cuts))
                 (fn-xw-fault (fn-xw-cat (list "unknown " name " cut: " label))))
                ((equal action "eio") (list :ok (list (list point) :os msg)))
                ((equal action "kill") (list :ok (list (list point) :kill msg)))
                (t (fn-xw-fault (fn-xw-cat (list "invalid " name " action: " action))))))))))

(defun fn-xw-post-faults (inject post recovery)
  ; fnn-post-entry-fault: the positional FAULT argument INJECT (or NIL) and
  ; the two selectors' values: (:ok FAULT-OR-NIL), a fault, or a usage error
  (declare (xargs :mode :program))
  (let ((positional
         (cond ((null inject) (list :ok nil))
               ((equal inject "postpublish")
                (list :ok (list (list "log-fenced") :indeterminate
                                "indeterminate injected failure after final publication")))
               ((equal inject "recordbarrier")
                (list :ok (list (list "log-written") :os "injected transaction directory barrier failure")))
               (t (list :usage "unknown fault point")))))
    (if (not (fn-xw-okp positional)) positional
      (let ((p (fn-xw-selector post "FN_NATIVE_POST_FAULT"
                               '("frontier-reserved" "record-completing" "finish-consumed" "finish-durable"
                                 "log-written" "log-fenced")
                               "developer-only native post fault")))
        (if (not (fn-xw-okp p)) p
          (let ((r (fn-xw-selector recovery "FN_NATIVE_RECOVERY_FAULT"
                                   '("recover-replayed" "recover-barrier-1" "recover-barrier-2"
                                     "recover-barrier-3" "recovery-stage-unlinked")
                                   "developer-only native recovery fault")))
            (if (not (fn-xw-okp r)) r
              (let ((selected (remove nil (list (cadr positional) (cadr p) (cadr r)))))
                (if (consp (cdr selected))
                    (list :usage "select at most one of the FAULT argument, FN_NATIVE_POST_FAULT and FN_NATIVE_RECOVERY_FAULT")
                  (list :ok (car selected)))))))))))

; ---------------------------------------------------------------------------
; Paths and files (io.lisp's fnn-join, fnn-parent, fnn-lstat, fnn-check-
; regular, fnn-safe-directory, fnn-read-regular-bounded).

(defun fn-xw-join (dir name)
  (declare (xargs :mode :program))
  (let ((n (length dir)))
    (if (and (< 0 n) (eql (char dir (- n 1)) #\/))
        (concatenate 'string dir name)
      (concatenate 'string dir "/" name))))

(defun fn-xw-rtrim-slash (cs)
  (declare (xargs :mode :program))
  ; the characters of a reversed path with its leading (the path's trailing) slashes dropped
  (if (and (consp cs) (eql (car cs) #\/)) (fn-xw-rtrim-slash (cdr cs)) cs))

(defun fn-xw-trim (path)
  (declare (xargs :mode :program))
  (coerce (reverse (fn-xw-rtrim-slash (reverse (coerce path 'list)))) 'string))

(defun fn-xw-parent (path)
  ; fnn-parent
  (declare (xargs :mode :program))
  (let* ((trimmed (fn-xw-trim path))
         (rcs (reverse (coerce trimmed 'list)))
         (after (member #\/ rcs)))
    (cond ((equal trimmed "") "/")
          ((null after) ".")
          ((null (cdr after)) "/")
          (t (coerce (reverse (cdr after)) 'string)))))

(defun fn-xw-absolute (path)
  ; fnn-absolute
  (declare (xargs :mode :program))
  (if (and (< 0 (length path)) (eql (char path 0) #\/))
      (fn-xw-trim path)
    (fn-xw-join (fn-xw-trim (fn-hx-getcwd)) (fn-xw-trim path))))

(defun fn-xw-basename (path)
  ; file-namestring of a path with no trailing slash
  (declare (xargs :mode :program))
  (let ((after (member #\/ (reverse (coerce path 'list)))))
    (if (null after) path
      (subseq path (len after) (length path)))))

(defun fn-xw-lstat (path)
  ; fnn-lstat: (:ok NIL) absent, (:ok (KIND SIZE MODE)), or the OS error
  (declare (xargs :mode :program))
  (let ((r (fn-hx-lstat-full path)))
    (cond ((equal r '(:absent)) (list :ok nil))
          ((fn-xw-errp r) (fn-xw-os r))
          (t (list :ok (cdr r))))))

(defun fn-xw-check-regular (path)
  ; fnn-check-regular: (:ok NIL) absent, (:ok (KIND SIZE MODE)) regular
  (declare (xargs :mode :program))
  (let ((r (fn-xw-lstat path)))
    (cond ((not (fn-xw-okp r)) r)
          ((null (cadr r)) r)
          ((eq (car (cadr r)) :regular) r)
          (t (fn-xw-fault (concatenate 'string "refusing non-regular path: " path))))))

(defun fn-xw-safe-directory (path)
  ; fnn-safe-directory without create
  (declare (xargs :mode :program))
  (let ((r (fn-xw-lstat path)))
    (cond ((not (fn-xw-okp r)) r)
          ((null (cadr r)) (fn-xw-fault (concatenate 'string "missing store directory: " path)))
          ((not (eq (car (cadr r)) :directory))
           (fn-xw-fault (concatenate 'string "refusing non-directory store path: " path)))
          (t (list :ok)))))

(defun fn-xw-read-file (path maximum)
  ; fnn-read-regular-bounded: (:ok OCTETS) or its condition
  (declare (xargs :mode :program))
  (let ((r (fn-hx-read-file path maximum)))
    (cond ((fn-xw-okp r) r)
          ((fn-xw-errp r) (fn-xw-os r))
          ((equal r '(:non-regular)) (fn-xw-fault (concatenate 'string "refusing non-regular store file: " path)))
          ((equal r '(:overbound)) (fn-xw-fault (concatenate 'string "store file exceeds bound: " path)))
          (t (fn-xw-fault "file exceeds ACL2-owned bound")))))

(defun fn-xw-fsync-dir (path)
  ; fnn-fsync-dir: :ok or the OS error (the open names the path, the barrier does not)
  (declare (xargs :mode :program))
  (let ((r (fn-hx-sync-dir path)))
    (if (eq r :ok) (list :ok) (fn-xw-os r))))

(defun fn-xw-sys (r)
  ; a syscall primitive's answer as a result
  (declare (xargs :mode :program))
  (if (fn-xw-errp r) (fn-xw-os r) (list :ok)))

(defun fn-xw-store-path (store name)
  (declare (xargs :mode :program))
  (fn-xw-join (fn-xw-get store :root) name))

; ---------------------------------------------------------------------------
; Acquire (fnn-acquire, writable: the exclusive writer lock).

(defun fn-xw-refuse-another-format (store)
  ; fnn-refuse-another-format: its reads' errors are ignored
  (declare (xargs :mode :program))
  (let* ((path (fn-xw-store-path store "config.json"))
         (c (fn-xw-check-regular path)))
    (if (not (and (fn-xw-okp c) (cadr c))) (list :ok)
      (let ((raw (fn-xw-read-file path 16384)))
        (if (not (and (fn-xw-okp raw) (consp (cadr raw)))) (list :ok)
          (let ((verdict (fn-store-metadata-config-open (cadr raw))))
            (if (and (consp verdict) (eq (car verdict) :refused) (consp (cdr verdict))
                     (eq (cadr verdict) :store-format))
                (list :open-refusal (fn-store-metadata-config-refusal-text verdict))
              (list :ok))))))))

(defun fn-xw-config-decode (octets)
  ; fnn-metadata-config-decode
  (declare (xargs :mode :program))
  (let ((verdict (fn-store-metadata-config-open octets)))
    (cond ((and (consp verdict) (eq (car verdict) :opened)
                (fn-store-profile-admittedp (cadr verdict)))
           (list :ok (cadr verdict)))
          ((and (consp verdict) (eq (car verdict) :refused))
           (let ((text (fn-store-metadata-config-refusal-text verdict)))
             (if (stringp text) (list :open-refusal text)
               (fn-xw-fault "ACL2 refused the store profile without naming a reason"))))
          ((equal verdict '(:rejected)) (fn-xw-fault "ACL2 rejected durable configuration frame"))
          (t (fn-xw-fault "ACL2 returned a malformed profile open verdict")))))

(defun fn-xw-load-config (store)
  ; fnn-load-config: (:ok CONFIG)
  (declare (xargs :mode :program))
  (let* ((path (fn-xw-store-path store "config.json"))
         (c (fn-xw-check-regular path)))
    (if (not (fn-xw-okp c)) c
      (let ((raw (fn-xw-read-file path 16384)))
        (cond ((eq (car raw) :os)
               (fn-xw-fault (concatenate 'string "invalid durable config: " (fn-xw-text raw))))
              ((not (fn-xw-okp raw)) raw)
              (t (fn-xw-config-decode (cadr raw))))))))

(defun fn-xw-lock (store)
  ; fnn-open-lock STORE t t: (:ok HANDLE)
  (declare (xargs :mode :program))
  (let ((r (fn-hx-lock-exclusive (fn-xw-store-path store "writer.lock"))))
    (cond ((fn-xw-okp r) r)
          ((eq r :locked) (fn-xw-refuse "store is already locked"))
          ((eq r :not-regular) (fn-xw-fault "refusing non-regular writer lock"))
          ((and (fn-xw-errp r) (eql (cadr r) 40)) (fn-xw-fault "refusing writer-lock symlink"))
          ((fn-xw-errp r) (fn-xw-fault (concatenate 'string "cannot open writer lock: " (caddr r))))
          (t (fn-xw-fault "cannot open writer lock")))))

(defun fn-xw-close (store)
  ; fnn-store-close: the log's descriptor, then the lock (unlocked, closed)
  (declare (xargs :mode :program))
  (let* ((log (fn-xw-get store :log))
         (x (and log (fn-xw-get log :h) (fn-hx-close (fn-xw-get log :h))))
         (y (and (fn-xw-get store :lock) (fn-hx-unlock (fn-xw-get store :lock)))))
    (declare (ignore x y))
    (fn-xw-put (fn-xw-put (fn-xw-put store :pending nil) :log nil) :lock nil)))

(defun fn-xw-acquire (store)
  ; (mv RESULT STORE)
  (declare (xargs :mode :program))
  (let ((r (fn-xw-safe-directory (fn-xw-get store :root))))
    (if (not (fn-xw-okp r)) (mv r store)
      (let ((fence (fn-xo-checkpoint-name-result (fn-store-checkpoint-clone-fence-name) "clone fence name")))
        (if (not (fn-xo-okp fence)) (mv fence store)
          (let ((l (fn-xw-lstat (fn-xw-store-path store (cadr fence)))))
            (cond
             ((not (fn-xw-okp l)) (mv l store))
             ((cadr l) (mv (fn-xw-refuse "clone is fenced pending durable incarnation rollover") store))
             (t
              (let ((r (fn-xw-refuse-another-format store)))
                (if (not (fn-xw-okp r)) (mv r store)
                  (let ((r (fn-xo-filesystem-identity (fn-xw-get store :root))))
                    (if (not (fn-xo-okp r)) (mv r store)
                      (let ((r (fn-xw-safe-directory (fn-xw-store-path store "staging"))))
                        (if (not (fn-xw-okp r)) (mv r store)
                          (let ((lock (fn-xw-lock store)))
                            (if (not (fn-xw-okp lock)) (mv lock store)
                              (let* ((store (fn-xw-put store :lock (cadr lock)))
                                     (config (fn-xw-load-config store)))
                                (cond
                                 ((not (fn-xw-okp config)) (mv config (fn-xw-close store)))
                                 ((not (fn-store-profile-logp (cadr config)))
                                  (mv (fn-xw-fault "a store that is not on the record log opened")
                                      (fn-xw-close store)))
                                 (t (let ((r (fn-xw-safe-directory (fn-xw-store-path store "journal"))))
                                      (if (not (fn-xw-okp r)) (mv r (fn-xw-close store))
                                        (mv (list :ok) (fn-xw-put store :config (cadr config))))))))))))))))))))))))

; ---------------------------------------------------------------------------
; The configuration history (fnn-config-record-observation, fnn-config-records).

(defun fn-xw-sort-strings (l) (declare (xargs :mode :program)) (fn-xo-sort-strings l nil))

(defun fn-xw-read-config-entries (dir names acc)
  ; each name checked regular and read under the record bound: (NAME . OCTETS)
  (declare (xargs :mode :program))
  (if (endp names) (list :ok (reverse acc))
    (let* ((path (fn-xw-join dir (car names)))
           (c (fn-xw-check-regular path)))
      (if (not (fn-xw-okp c)) c
        (let ((r (fn-xw-read-file path 65538)))
          (if (not (fn-xw-okp r)) r
            (fn-xw-read-config-entries dir (cdr names) (cons (cons (car names) (cadr r)) acc))))))))

(defun fn-xw-observed-names (observed)
  (declare (xargs :mode :program))
  (if (endp observed) nil (cons (car (car observed)) (fn-xw-observed-names (cdr observed)))))

(defun fn-xw-observation-args (observed)
  (declare (xargs :mode :program))
  (if (endp observed) nil
    (cons (list (fn-xo-octets (car (car observed))) (cdr (car observed)))
          (fn-xw-observation-args (cdr observed)))))

(defun fn-xw-plan-records (plan observed-names acc)
  ; fnn-bridge-config-observation's check of each returned entry, then the octets
  (declare (xargs :mode :program))
  (if (endp plan) (list :ok (reverse acc))
    (let ((e (car plan)))
      (if (and (true-listp e) (equal (len e) 2) (stringp (car e))
               (fn-xw-octet-list-p (cadr e))
               (not (member #\/ (coerce (car e) 'list)))
               (fn-xw-string-mem (car e) observed-names))
          (fn-xw-plan-records (cdr plan) observed-names (cons (cadr e) acc))
        (fn-xw-fault "ACL2 returned malformed configuration namespace entry")))))

(defun fn-xw-config-records (store)
  ; (:ok RECORDS): the configuration octets in ACL2's canonical order
  (declare (xargs :mode :program))
  (let ((limit (fn-store-config-observation-limit (fn-xw-get store :config))))
    (if (not (and (integerp limit) (< 0 limit)))
        (fn-xw-fault "ACL2 returned a malformed configuration generation bound")
      (let* ((dir (fn-xw-store-path store "config"))
             (listed (fn-hx-list-bounded dir limit)))
        (cond ((fn-xw-errp listed) (fn-xw-fault "cannot enumerate configuration history"))
              ((equal listed '(:over)) (fn-xw-fault "configuration namespace exceeds ACL2 observation bound"))
              (t (let ((entries (fn-xw-read-config-entries dir (fn-xw-sort-strings (cadr listed)) nil)))
                   (if (not (fn-xw-okp entries)) entries
                     (let ((value (fn-store-config-observation (fn-xw-observation-args (cadr entries)) limit)))
                       (if (not (and (true-listp value) (equal (len value) 3) (eq (car value) :ok)
                                     (null (cadr value)) (true-listp (caddr value))))
                           (fn-xw-fault "ACL2 refused configuration namespace observation")
                         (let ((records (fn-xw-plan-records (caddr value)
                                                            (fn-xw-observed-names (cadr entries)) nil)))
                           (cond ((not (fn-xw-okp records)) records)
                                 ((endp (cadr records))
                                  (fn-xw-fault "refusing store with no durable configuration record"))
                                 (t records)))))))))))))

; ---------------------------------------------------------------------------
; The log's segments and the genesis.

(defun fn-xw-segment-names (store)
  ; fnn-log-segment-names: journal/'s entries, directory order, bounded
  (declare (xargs :mode :program))
  (let ((r (fn-hx-list-bounded (fn-xw-store-path store "journal") (fn-lgs-listing-bound))))
    (cond ((fn-xw-errp r) (fn-xw-os r))
          ((equal r '(:over)) (fn-xw-fault "log segment exceeds ACL2 observation bound"))
          (t r))))

(defun fn-xw-segment-path (store k)
  ; fnn-segment-path-at
  (declare (xargs :mode :program))
  (let ((name (fn-lgs-segment-name k)))
    (if (and (stringp name) (< 0 (length name)) (not (member #\/ (coerce name 'list)))
             (eql (fn-lgs-segment-index name) k))
        (list :ok (fn-xw-join (fn-xw-store-path store "journal") name))
      (fn-xw-fault "ACL2 returned an invalid log segment name"))))

(defun fn-xw-genesis-open (store state)
  ; fnn-genesis-open: (mv (:ok CHAIN) state) or the refusal
  (declare (xargs :mode :program :stobjs state))
  (let* ((path (fn-xw-join (fn-xw-store-path store "journal") (fn-store-genesis-file-name)))
         (c (fn-xw-check-regular path)))
    (cond
     ((not (fn-xw-okp c)) (mv c state))
     ((null (cadr c))
      (mv (fn-xw-fault (concatenate 'string "missing store genesis: " path
                                    " (an init that did not finish: run init again)"))
          state))
     (t (let ((raw (fn-xw-read-file path 1024)))
          (if (not (fn-xw-okp raw)) (mv raw state)
            (let ((verdict (fn-store-genesis-open (cadr raw) (fn-xw-get store :config))))
              (cond
               ((not (and (consp verdict) (member-eq (car verdict) '(:genesis :refused))))
                (mv (fn-xw-fault "ACL2 returned a malformed genesis verdict") state))
               ((eq (car verdict) :refused)
                (let ((text (fn-store-genesis-refusal-text verdict)))
                  (mv (if (stringp text) (list :open-refusal text)
                        (fn-xw-fault "ACL2 refused the genesis without naming a reason"))
                      state)))
               (t (mv-let (erp val state) (fn-store-genesis-install verdict state)
                    (declare (ignore val))
                    (if erp (mv (fn-xw-fault "ACL2 error in fn-store-genesis-install") state)
                      (mv (list :ok (fn-store-genesis-chain verdict)) state))))))))))))

(defun fn-xw-observed-extent (path)
  ; fnn-log-observed-extent: (:ok SIZE)
  (declare (xargs :mode :program))
  (let ((c (fn-xw-check-regular path)))
    (cond ((not (fn-xw-okp c)) c)
          ((null (cadr c)) (fn-xw-refuse (concatenate 'string "no log segment at " path)))
          (t (list :ok (cadr (cadr c)))))))

(defun fn-xw-open-segment (path extent unit writable)
  ; fnn-log-open-segment of an existing segment: (:ok HANDLE), HANDLE a
  ; read-write handle when WRITABLE, else a registered read-only one
  (declare (xargs :mode :program))
  (if (not (fn-lg-extent-okp extent unit))
      (list :usage (fn-xw-cat (list "log extent " (fn-xw-dec extent) " is not a positive number of "
                                    (fn-xw-dec unit) "-octet units")))
    (let ((c (fn-xw-check-regular path)))
      (cond ((not (fn-xw-okp c)) c)
            ((null (cadr c))
             (if writable (fn-xw-fault "extract: a writable open creates no log segment")
               (fn-xw-refuse (concatenate 'string "no log segment at " path))))
            (t (let ((o (if writable (fn-hx-open-rw path) (fn-hx-open-ro path))))
                 (cond ((fn-xw-errp o) (fn-xw-os o))
                       ((not (equal (caddr o) extent))
                        (prog2$ (and writable (fn-hx-close (cadr o)))
                                (fn-xw-refuse (fn-xw-cat (list "log segment " path " is not "
                                                               (fn-xw-dec extent) " octets long")))))
                       (t (list :ok (cadr o))))))))))

(defun fn-xw-pread (h off n)
  ; fnn-log-pread: exactly N octets or the fault
  (declare (xargs :mode :program))
  (let ((r (fn-hx-read-at h off n)))
    (cond ((fn-xw-errp r) (fn-xw-os r))
          ((equal (len (cadr r)) n) r)
          (t (fn-xw-fault "log segment shorter than its extent")))))

; ---------------------------------------------------------------------------
; The full replay's stream (fnn-recover-log-stream-*).  REPLAY is
; (ACC CHUNK-REV OCTETS NEXT PLACES-REV FOLD STORED-REV SCANNED): io.lisp's
; seven slots and the count of records scanned.

(defun fn-xw-replay-begin (fn-arena)
  ; fnn-recover-log-stream-begin (fnn-bridge-recover-begin: the arena cleared)
  (declare (xargs :mode :program :stobjs fn-arena))
  (let ((fn-arena (fn-arena-clear fn-arena)))
    (mv (list nil nil 0 0 nil 1 nil 0) fn-arena)))

(defun fn-xw-some (l) (declare (xargs :mode :program)) (and (consp l) (or (car l) (fn-xw-some (cdr l)))))

(defun fn-xw-all-eq (a b)
  ; io.lisp's (every #'eq CHUNK STORED): each record is the stored list itself
  (declare (xargs :mode :program))
  (if (endp a) t (and (consp b) (eq (car a) (car b)) (fn-xw-all-eq (cdr a) (cdr b)))))

(defun fn-xw-replay-flush (replay fn-arena)
  ; (mv RESULT REPLAY fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (if (null (nth 1 replay))
      (mv (list :ok) replay fn-arena)
    (let ((chunk (reverse (nth 1 replay)))
          (places (reverse (nth 4 replay)))
          (stored (reverse (nth 6 replay))))
      (mv-let (decoded fold) (fn-lgb-decode-next chunk (nth 5 replay))
        (let ((next (if (consp decoded)
                        (fn-ofw-wire-next decoded (nth 3 replay))
                      (nth 3 replay))))
          (mv-let (acc fn-arena)
            (cond ((not (fn-xw-some places)) (fn-srs-intern-step (nth 0 replay) decoded fn-arena))
                  ((not (fn-xw-all-eq chunk stored))
                   (fn-lzr-intern-step (nth 0 replay) decoded stored places (fn-lzr-dicts-initial) fn-arena))
                  (t (fn-arx-intern-step (nth 0 replay) decoded chunk places fn-arena)))
            (if (eq acc :bad)
                (mv (fn-xw-fault "ACL2 replay rejected committed transaction history")
                    (update-nth 5 fold replay) fn-arena)
              (mv (list :ok)
                  (list acc nil 0 next nil fold nil (nth 7 replay))
                  fn-arena))))))))

(defun fn-xw-replay-take (replay record place stored fn-arena)
  ; fnn-recover-log-stream-take, and the scan's count
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (r replay fn-arena)
    (if (and (nth 1 replay) (fn-srs-chunk-fullp (nth 2 replay)))
        (fn-xw-replay-flush replay fn-arena)
      (mv (list :ok) replay fn-arena))
    (if (not (fn-xw-okp r)) (mv r replay fn-arena)
      (mv (list :ok)
          (list (nth 0 replay) (cons record (nth 1 replay)) (+ (nth 2 replay) (len record))
                (nth 3 replay) (cons place (nth 4 replay)) (nth 5 replay)
                (cons stored (nth 6 replay)) (+ 1 (nth 7 replay)))
          fn-arena))))

(defun fn-xw-read-record (tally z)
  ; fnn-log-read-record: (mv RESULT TALLY), RESULT (:ok R)
  (declare (xargs :mode :program))
  (mv-let (x tally) (fn-lzr-read-step (or tally (fn-lzr-tally-empty)) (fn-lzr-dicts-initial) z)
    (if (and (consp x) (eq (car x) :ok))
        (mv (list :ok (cadr x)) tally)
      (let ((line (or (fn-lzr-read-refusal-text x)
                      "log-frame: ACL2 refused a compressed record without a line")))
        (mv (if (equal x '(:refused :lz-dictionary)) (list :open-refusal line) (fn-xw-fault line))
            tally)))))

(defun fn-xw-sink-all (records places file tally replay fn-arena)
  ; each record the step took, through ACL2's read step, into the replay
  (declare (xargs :mode :program :stobjs fn-arena))
  (if (endp records) (mv (list :ok) tally replay fn-arena)
    (mv-let (r tally) (fn-xw-read-record tally (car records))
      (if (not (fn-xw-okp r)) (mv r tally replay fn-arena)
        (mv-let (r replay fn-arena)
          (fn-xw-replay-take replay (cadr r)
                             (and file (consp places) (cons file (car places)))
                             (car records) fn-arena)
          (if (not (fn-xw-okp r)) (mv r tally replay fn-arena)
            (fn-xw-sink-all (cdr records) (if (consp places) (cdr places) places) file
                            tally replay fn-arena)))))))

(defun fn-xw-walk (h extent unit max st file tally replay fn-octets-lg fn-arena)
  ; fnn-log-stream-segment's loop: (mv RESULT ST TALLY REPLAY fn-octets-lg fn-arena)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena)))
  (if (fn-lgw-stop st)
      (mv (list :ok) st tally replay fn-octets-lg fn-arena)
    (let* ((pos (fn-lgw-pos st))
           (hd (fn-xw-pread h pos (fn-lgw-header-len st extent))))
      (if (not (fn-xw-okp hd))
          (mv hd st tally replay fn-octets-lg fn-arena)
        (let* ((n (fn-lgw-entry-len-bounded (cadr hd) st extent max)))
          (mv-let (count fn-octets-lg) (fn-hx-fill h pos (if n n 0) fn-octets-lg)
            (if (not (equal count (if n n 0)))
                (mv (if (< count 0) (fn-xw-os-errno 5) (fn-xw-fault "log segment shorter than its extent"))
                    st tally replay fn-octets-lg fn-arena)
              (mv-let (took records next) (fn-lgw-step-buf-nf st unit max extent fn-octets-lg)
                (if (not took)
                    (fn-xw-walk h extent unit max next file tally replay fn-octets-lg fn-arena)
                  (let ((places (and file (fn-lgb-entry-places pos (len records) unit fn-octets-lg))))
                    (mv-let (r tally replay fn-arena)
                      (fn-xw-sink-all records places file tally replay fn-arena)
                      (if (not (fn-xw-okp r))
                          (mv r st tally replay fn-octets-lg fn-arena)
                        (fn-xw-walk h extent unit max next file tally replay fn-octets-lg fn-arena)))))))))))))

(defun fn-xw-probe-tail (h extent unit max ps)
  ; fnn-log-probe-tail: (:ok PS)
  (declare (xargs :mode :program))
  (if (fn-lgdm-done-p ps extent)
      (list :ok ps)
    (let* ((q (fn-lgdm-q ps))
           (hd (fn-xw-pread h q (fn-lgdm-header-len ps extent))))
      (if (not (fn-xw-okp hd)) hd
        (let* ((n (fn-lgdm-entry-len-bounded (cadr hd) ps extent max))
               (e (if n (fn-xw-pread h q n) (list :ok nil))))
          (if (not (fn-xw-okp e)) e
            (fn-xw-probe-tail h extent unit max (fn-lgdm-step (cadr hd) (and n (cadr e)) ps unit max))))))))

(defun fn-xw-stream-segment (h extent unit max genesis label writable file store replay
                               fn-octets-lg fn-arena)
  ; fnn-log-stream-segment under the full replay (*fnn-log-stream-finish*):
  ; (mv RESULT STORE REPLAY fn-octets-lg fn-arena), RESULT (:ok KERNEL VERDICT)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena)))
  (mv-let (r st tally replay fn-octets-lg fn-arena)
    (fn-xw-walk h extent unit max (fn-lgw-start genesis 1) file (fn-xw-get store :lz-tally)
                replay fn-octets-lg fn-arena)
    (mv-let (count fn-octets-lg) (fn-hx-fill h 0 0 fn-octets-lg)
      (declare (ignore count))
      (let ((store (fn-xw-put store :lz-tally tally)))
        (if (not (fn-xw-okp r))
            (mv r store replay fn-octets-lg fn-arena)
          ; the fold the replay took from its decode of this segment's records
          (mv-let (f replay fn-arena) (fn-xw-replay-flush replay fn-arena)
            (if (not (fn-xw-okp f))
                (mv f store replay fn-octets-lg fn-arena)
              (let* ((st (fn-lgw-set-next st (nth 5 replay)))
                     (replay (update-nth 5 1 replay))
                     (probe (fn-xw-probe-tail h extent unit max (fn-lgdm-start st))))
                (if (not (fn-xw-okp probe))
                    (mv probe store replay fn-octets-lg fn-arena)
                  (let ((verdict (fn-lgdm-effective (fn-lgdm-verdict st (cadr probe) extent)
                                                    label (fn-xw-get store :repair) writable)))
                    (if (fn-lgdm-refused-p verdict)
                        (let ((text (fn-lgdm-refusal-text verdict label)))
                          (mv (if text (list :open-refusal text)
                                (fn-xw-fault "ACL2 refused a log segment without a line"))
                              store replay fn-octets-lg fn-arena))
                      (let* ((line (or (fn-lgdm-report-text verdict label)
                                       (fn-lgdm-repair-text verdict label)))
                             (store (if (stringp line)
                                        (fn-xw-put store :reports (cons line (fn-xw-get store :reports)))
                                      store)))
                        (mv (list :ok (fn-lgw-kernel st) verdict) store replay fn-octets-lg fn-arena)))))))))))))

; ---------------------------------------------------------------------------
; P-LOG-RECOVER on the active segment (fnn-log-recover), the confirmed
; repair's quarantine (fnn-log-quarantine), an interrupted rotation
; (fnn-log-complete-rotation) and the scan (fnn-log-scan-segments).

(defun fn-xw-copy-out (in out at extent)
  (declare (xargs :mode :program))
  (if (<= extent at) (list :ok)
    (let ((chunk (fn-xw-pread in at (min 1048576 (- extent at)))))
      (if (not (fn-xw-okp chunk)) chunk
        (let ((w (fn-xw-sys (fn-hx-write-all out (cadr chunk)))))
          (if (not (fn-xw-okp w)) w
            (fn-xw-copy-out in out (+ at (len (cadr chunk))) extent)))))))

(defun fn-xw-quarantine-copy (h extent dir stage target)
  ; the copy under STAGE (a dead attempt's stage of the same name removed
  ; first), fenced, renamed onto TARGET; the stage removed on a failure
  (declare (xargs :mode :program))
  (let* ((sl (fn-xw-lstat stage))
         (u (cond ((not (fn-xw-okp sl)) sl)
                  ((cadr sl) (fn-xw-sys (fn-hx-unlink stage)))
                  (t (list :ok)))))
    (if (not (fn-xw-okp u)) u
      (let ((o (fn-hx-create-excl stage t)))
        (if (fn-xw-errp o) (fn-xw-os o)
          (let* ((c (fn-xw-copy-out h (cadr o) 0 extent))
                 (s (if (fn-xw-okp c) (fn-xw-sys (fn-hx-fsync (cadr o))) c))
                 (x (fn-hx-close (cadr o)))
                 (r (if (fn-xw-okp s) (fn-xw-sys (fn-hx-rename stage target)) s)))
            (declare (ignore x))
            (if (fn-xw-okp r)
                (fn-xw-fsync-dir dir)
              (let ((d (fn-hx-unlink stage)))
                (declare (ignore d))
                r))))))))

(defun fn-xw-quarantine (path h extent name)
  ; fnn-log-quarantine: the segment's octets kept as quarantine/NAME, copied
  ; under quarantine/.stage-NAME and renamed, so NAME only names a complete
  ; copy; a NAME already present is an earlier attempt's complete copy and
  ; is kept (sweep S040/S124)
  (declare (xargs :mode :program))
  (let* ((journal (fn-xw-parent path))
         (dir (fn-xw-join (fn-xw-parent journal) "quarantine"))
         (target (fn-xw-join dir name))
         (stage (fn-xw-join dir (concatenate 'string ".stage-" name)))
         (l (fn-xw-lstat dir)))
    (if (not (fn-xw-okp l)) l
      (let ((m (if (cadr l) (list :ok)
                 (let ((r (fn-xw-sys (fn-hx-mkdir dir))))
                   (if (not (fn-xw-okp r)) r (fn-xw-fsync-dir (fn-xw-parent journal)))))))
        (if (not (fn-xw-okp m)) m
          (let ((tl (fn-xw-lstat target)))
            (cond ((not (fn-xw-okp tl)) tl)
                  ((cadr tl) (fn-xw-fsync-dir dir))
                  (t (fn-xw-quarantine-copy h extent dir stage target)))))))))

(defun fn-xw-log-recover (path extent unit max genesis file store replay fn-octets-lg fn-arena)
  ; fnn-log-recover: (mv RESULT STORE REPLAY fn-octets-lg fn-arena), RESULT (:ok LOG)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena)))
  (let ((o (fn-xw-open-segment path extent unit t)))
    (if (not (fn-xw-okp o)) (mv o store replay fn-octets-lg fn-arena)
      (let ((h (cadr o)))
        (mv-let (r store replay fn-octets-lg fn-arena)
          (fn-xw-stream-segment h extent unit max genesis (fn-xw-basename path) t file store replay
                                fn-octets-lg fn-arena)
          (if (not (fn-xw-okp r))
              (prog2$ (fn-hx-close h) (mv r store replay fn-octets-lg fn-arena))
            (let* ((ks (cadr r))
                   (name (fn-lgdm-quarantine-name (caddr r) (fn-xw-basename path)))
                   (q (if (stringp name) (fn-xw-quarantine path h extent name) (list :ok))))
              (if (not (fn-xw-okp q))
                  (prog2$ (fn-hx-close h) (mv q store replay fn-octets-lg fn-arena))
                (mv-let (offset count) (fn-lg-recover-tail ks extent)
                 (let* ((w (fn-xw-sys (fn-hx-pwrite-zeros h offset count)))
                        (w (if (fn-xw-okp w) (fn-xw-log-at "log-truncated") w))
                        (w (if (fn-xw-okp w) (fn-xw-sys (fn-hx-fdatasync h)) w))
                        (w (if (fn-xw-okp w) (fn-xw-log-at "log-recovered") w)))
                  (if (not (fn-xw-okp w))
                      ;; the segment's handle closed here too (sweep S116):
                      ;; it is not yet the log's, so nothing else reaches it
                      (prog2$ (fn-hx-close h) (mv w store replay fn-octets-lg fn-arena))
                    (mv (list :ok (list (cons :path path) (cons :h h) (cons :kernel ks) (cons :unit unit)
                                        (cons :max max) (cons :extent extent) (cons :count 0)
                                        (cons :octets 0) (cons :bmax 64) (cons :omax 67108864)
                                        (cons :pending 0) (cons :reserved nil) (cons :lz-min nil)
                                        (cons :lz nil)))
                        store replay fn-octets-lg fn-arena))))))))))))

(defun fn-xw-complete-rotation (store path)
  ; fnn-log-complete-rotation, writable
  (declare (xargs :mode :program))
  (let ((c (fn-xw-check-regular path)))
    (cond ((not (fn-xw-okp c)) c)
          ((null (cadr c)) (fn-xw-fault "extract: an absent active segment"))
          ((fn-lg-extent-okp (cadr (cadr c)) (fn-store-log-unit)) (list :ok))
          (t (let ((o (fn-hx-open-rw path)))
               (if (fn-xw-errp o) (fn-xw-os o)
                 (let* ((p (fn-xw-sys (fn-hx-preallocate (cadr o) 0 (fn-store-log-initial-extent))))
                        (s (if (fn-xw-okp p) (fn-xw-sys (fn-hx-fsync (cadr o))) p))
                        (x (fn-hx-close (cadr o))))
                   (declare (ignore x))
                   (if (not (fn-xw-okp s)) s
                     (fn-xw-fsync-dir (fn-xw-store-path store "journal"))))))))))

(defun fn-xw-scan (store scan genesis unit max replay fn-octets-lg fn-arena)
  ; fnn-log-scan-segments with the full replay's places, writable:
  ; (mv RESULT STORE REPLAY fn-octets-lg fn-arena), RESULT (:ok LOG)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena)))
  (if (endp scan)
      (mv (fn-xw-fault "the log's open plan named no segment") store replay fn-octets-lg fn-arena)
    (let ((p (fn-xw-segment-path store (car scan))))
      (if (not (fn-xw-okp p)) (mv p store replay fn-octets-lg fn-arena)
        (let ((path (cadr p)))
          (if (consp (cdr scan))
              ; a closed segment, read only; its realizer id is its handle
              (let ((e (fn-xw-observed-extent path)))
                (if (not (fn-xw-okp e)) (mv e store replay fn-octets-lg fn-arena)
                  (let ((o (fn-xw-open-segment path (cadr e) unit nil)))
                    (if (not (fn-xw-okp o)) (mv o store replay fn-octets-lg fn-arena)
                      (mv-let (r store replay fn-octets-lg fn-arena)
                        (fn-xw-stream-segment (cadr o) (cadr e) unit max genesis (fn-xw-basename path) nil
                                              (cadr o) store replay fn-octets-lg fn-arena)
                        (if (not (fn-xw-okp r)) (mv r store replay fn-octets-lg fn-arena)
                          (fn-xw-scan store (cdr scan) (fn-lgc-last (cadr r)) unit max replay
                                      fn-octets-lg fn-arena)))))))
            (let ((c (fn-xw-complete-rotation store path)))
              (if (not (fn-xw-okp c)) (mv c store replay fn-octets-lg fn-arena)
                (let ((file (fn-hx-open-ro path)))
                  (if (fn-xw-errp file)
                      (mv (fn-xw-os file) store replay fn-octets-lg fn-arena)
                    (let ((e (fn-xw-observed-extent path)))
                      (if (not (fn-xw-okp e)) (mv e store replay fn-octets-lg fn-arena)
                        (mv-let (r store replay fn-octets-lg fn-arena)
                          (fn-xw-log-recover path (cadr e) unit max genesis (cadr file) store replay
                                             fn-octets-lg fn-arena)
                          (if (not (fn-xw-okp r)) (mv r store replay fn-octets-lg fn-arena)
                            (mv (list :ok (fn-xw-put (fn-xw-put (fn-xw-put (cadr r) :index (car scan))
                                                                :genesis genesis)
                                                     :file (cadr file)))
                                store replay fn-octets-lg fn-arena)))))))))))))))

; ---------------------------------------------------------------------------
; Observations (fnn-observe through fnn-bridge-io: fn-store-sn-io).

(defun fn-xw-observe (store operation result state)
  ; (mv RESULT STORE state), RESULT (:ok ACTION)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp val state) (fn-store-sn-io operation result state)
    (let ((a (if erp (list :fault "") (fn-xw-action val))))
      (if (fn-xw-okp a)
          (mv a store state)
        (mv (fn-xw-indeterminate (fn-xw-cat (list "ACL2 could not record " (fn-xw-kw operation) " observation")))
            (fn-xw-put (fn-xw-put store :fenced t) :pending nil)
            state)))))

; ---------------------------------------------------------------------------
; The recovery barriers (fnn-store-recovery-barriers, fnn-recover-log's loop).

(defun fn-xw-barriers (store dirs ordinal phase state)
  ; (mv RESULT STORE state); an OS error is returned as it is (the caller's
  ; handler makes it the uncertain frontier)
  (declare (xargs :mode :program :stobjs state))
  (if (endp dirs)
      (mv (if (eq phase :ready) (list :ok) (fn-xw-fault "ACL2 did not complete all recovery barriers"))
          store state)
    (let ((f (fn-xw-fsync-dir (car dirs))))
      (if (not (fn-xw-okp f))
          (mv-let (o store state) (fn-xw-observe store :recovery-barrier :uncertain state)
            (mv (if (fn-xw-okp o) f o) store state))
        (mv-let (o store state) (fn-xw-observe store :recovery-barrier :ok state)
          (cond ((not (fn-xw-okp o)) (mv o store state))
                ((not (member-eq (cadr o) '(:recovering :ready)))
                 (mv (fn-xw-fault "ACL2 rejected recovered barrier ordering") store state))
                (t (let ((c (fn-xw-at store (concatenate 'string "recover-barrier-" (fn-xw-dec ordinal)))))
                     (if (not (fn-xw-okp c)) (mv c store state)
                       (fn-xw-barriers store (cdr dirs) (+ 1 ordinal) (cadr o) state))))))))))

; ---------------------------------------------------------------------------
; The staging sweep (fnn-sweep-staging) and its observation.

(defun fn-xw-staging-observation (store state)
  ; (mv (:ok NAMES MORE) state): at most ACL2's limit of names, sorted
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp limit state) (fn-store-sn-staging-observation-limit state)
    (declare (ignore erp))
    (if (not (and (integerp limit) (< 0 limit)))
        (mv (fn-xw-fault "ACL2 returned a non-positive staging observation limit") state)
      (let ((r (fn-hx-list-window (fn-xw-store-path store "staging") limit)))
        (if (fn-xw-errp r)
            (mv (fn-xw-fault "cannot enumerate staging") state)
          (mv (list :ok (fn-xw-sort-strings (cadr r)) (caddr r)) state))))))

(defun fn-xw-octets-names (l)
  (declare (xargs :mode :program))
  (if (endp l) nil (cons (fn-xo-string (car l)) (fn-xw-octets-names (cdr l)))))

(defun fn-xw-names-octets (l)
  (declare (xargs :mode :program))
  (if (endp l) nil (cons (fn-xo-octets (car l)) (fn-xw-names-octets (cdr l)))))

(defun fn-xw-sweep-removals (store names observed)
  ; unlink each removal ACL2 named (an absent name won a race; any other
  ; failure is uncertain), cut recovery-stage-unlinked after each
  (declare (xargs :mode :program))
  (if (endp names) (list :ok)
    (if (not (fn-xw-string-mem (car names) observed))
        (fn-xw-fault "ACL2 returned a staging removal outside the observation")
      (let* ((u (fn-hx-unlink (fn-xw-join (fn-xw-store-path store "staging") (car names))))
             (r (cond ((and (fn-xw-errp u) (eql (cadr u) 2)) (list :ok))
                      ((fn-xw-errp u) (fn-xw-os u))
                      (t (fn-xw-at store "recovery-stage-unlinked")))))
        (cond ((fn-xw-okp r) (fn-xw-sweep-removals store (cdr names) observed))
              ((eq (car r) :os)
               (fn-xw-indeterminate (fn-xw-cat (list "cannot collect staging orphan " (car names) ": "
                                                     (fn-xw-text r)))))
              (t r))))))

(defun fn-xw-sweep (store fuel state)
  ; fnn-sweep-staging's rounds: (mv RESULT STORE state).  FUEL bounds the
  ; rounds only as a guard against a host defect: ACL2's :again promises a
  ; strictly smaller directory (fn-sn-sweep-rounds-collect-every-orphan).
  (declare (xargs :mode :program :stobjs state))
  (if (zp fuel) (mv (fn-xw-fault "extract: the staging sweep did not end") store state)
    (mv-let (o state) (fn-xw-staging-observation store state)
      (if (not (fn-xw-okp o)) (mv o store state)
        (mv-let (erp value state)
          (fn-store-sn-sweep-round (fn-xw-names-octets (cadr o)) (if (caddr o) t nil) nil state)
          (declare (ignore erp))
          (if (not (and (consp value) (member-eq (car value) '(:done :again :refused))
                        (consp (cdr value)) (null (cddr value))
                        (true-listp (cadr value))))
              (mv (fn-xw-fault "ACL2 returned a malformed staging sweep round") store state)
            (let ((r (fn-xw-sweep-removals store (fn-xw-octets-names (cadr value)) (cadr o))))
              (cond ((not (fn-xw-okp r)) (mv r store state))
                    ((eq (car value) :again) (fn-xw-sweep store (- fuel 1) state))
                    ((eq (car value) :done)
                     (mv-let (o2 state) (fn-xw-staging-observation store state)
                       (if (not (fn-xw-okp o2)) (mv o2 store state)
                         (mv (list :ok)
                             (fn-xw-put (fn-xw-put store :orphans (cadr o2)) :orphans-more (caddr o2))
                             state))))
                    (t (mv (fn-xw-refuse (fn-xw-cat (list "staging namespace holds more than "
                                                          (fn-xw-dec (len (cadr o)))
                                                          " names recovery may not remove")))
                           store state))))))))))

; ---------------------------------------------------------------------------
; P-DROP of the covered segments an interrupted drop left (fnn-log-drop).

(defun fn-xw-drop-each (store indices)
  (declare (xargs :mode :program))
  (if (endp indices) (list :ok)
    (let ((p (fn-xw-segment-path store (car indices))))
      (if (not (fn-xw-okp p)) p
        (let ((l (fn-xw-lstat (cadr p))))
          (if (not (fn-xw-okp l)) l
            (let ((u (if (cadr l) (fn-xw-sys (fn-hx-unlink (cadr p))) (list :ok))))
              (if (not (fn-xw-okp u)) u
                (let ((c (fn-xw-log-at "drop-unlinked")))
                  (if (not (fn-xw-okp c)) c (fn-xw-drop-each store (cdr indices))))))))))))

(defun fn-xw-drop (store indices)
  (declare (xargs :mode :program))
  (if (endp indices) (list :ok)
    (let ((r (fn-xw-drop-each store indices)))
      (if (not (fn-xw-okp r)) r
        (let ((f (fn-xw-fsync-dir (fn-xw-store-path store "journal"))))
          (if (not (fn-xw-okp f)) f (fn-xw-log-at "drop-durable")))))))

; ---------------------------------------------------------------------------
; The open (fnn-open-live-store STORE t: fnn-acquire, fnn-bridge-reset,
; fnn-recover -> fnn-recover-log's full replay, the barriers, the sweep and
; the interrupted drop).

(defun fn-xw-split-lf (octets current acc)
  ; fnn-decode-joined-names, each name kept as its octets
  (declare (xargs :mode :program))
  (cond ((endp octets) (reverse (if current (cons (reverse current) acc) acc)))
        ((eql (car octets) 10) (fn-xw-split-lf (cdr octets) nil (cons (reverse current) acc)))
        (t (fn-xw-split-lf (cdr octets) (cons (car octets) current) acc))))

(defun fn-xw-recover-body (store fn-octets-lg fn-arena state)
  ; fnn-recover-log's first handler-case body: (mv RESULT STORE fn-octets-lg
  ; fn-arena state), RESULT (:ok COUNT DROP)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena state)))
  (let ((c (fn-xw-check-regular (fn-xw-store-path store (fn-store-sco-file-name)))))
    (cond
     ((not (fn-xw-okp c)) (mv c store fn-octets-lg fn-arena state))
     ((cadr c)
      (mv (fn-xw-fault "extract: a store with a state checkpoint is not opened by this program (its open is the page store's)")
          store fn-octets-lg fn-arena state))
     (t
      (mv-let (erp val state) (fn-store-sco-clear state)
        (declare (ignore erp val))
        (let ((names (fn-xw-segment-names store)))
          (if (not (fn-xw-okp names)) (mv names store fn-octets-lg fn-arena state)
            (let ((plan (fn-lgs-open-plan (cadr names) nil)))
              (cond
               ((not (and (consp plan) (member-eq (car plan) '(:scan :refused))))
                (mv (fn-xw-fault "ACL2 returned a malformed log open plan") store fn-octets-lg fn-arena state))
               ((equal plan '(:refused :no-segment))
                (mv (fn-xw-fault (concatenate 'string "missing store directory: " (fn-xw-store-path store "journal")
                                              " has no log segment (an init that did not finish: run init again)"))
                    store fn-octets-lg fn-arena state))
               ((eq (car plan) :refused)
                (mv (list :open-refusal (fn-xw-cat (list "open refused reason=" (fn-xw-kw (cadr plan))
                                                         ": the log's segments do not hold the history")))
                    store fn-octets-lg fn-arena state))
               (t
                (mv-let (genesis state) (fn-xw-genesis-open store state)
                  (if (not (fn-xw-okp genesis)) (mv genesis store fn-octets-lg fn-arena state)
                    (let ((choice (fn-store-sco-select :absent 0 0 (fn-xw-get store :config))))
                      (if (not (and (consp choice) (member-eq (car choice) '(:checkpoint :full-replay))))
                          (mv (fn-xw-fault "ACL2 returned a malformed checkpoint selection")
                              store fn-octets-lg fn-arena state)
                        (if (not (eq (car choice) :full-replay))
                            (mv (fn-xw-fault "extract: ACL2 chose a checkpoint open this program does not make")
                                store fn-octets-lg fn-arena state)
                          (let ((config-records (fn-xw-config-records store)))
                            (if (not (fn-xw-okp config-records))
                                (mv config-records store fn-octets-lg fn-arena state)
                              (mv-let (replay fn-arena) (fn-xw-replay-begin fn-arena)
                                (mv-let (r store replay fn-octets-lg fn-arena)
                                  (fn-xw-scan (fn-xw-put store :lz-tally nil) (cadr plan) (cadr genesis)
                                              (fn-store-log-unit)
                                              (fn-store-profile-max-record-octets (fn-xw-get store :config))
                                              replay fn-octets-lg fn-arena)
                                  (if (not (fn-xw-okp r)) (mv r store fn-octets-lg fn-arena state)
                                    (mv-let (f replay fn-arena) (fn-xw-replay-flush replay fn-arena)
                                      (if (not (fn-xw-okp f)) (mv f store fn-octets-lg fn-arena state)
                                        (let* ((log (cadr r))
                                               ;; the configuration records' txids join
                                               ;; the frontier too, as the native open and
                                               ;; the read-only port do (sweep S039, walk F3)
                                               (next (fn-store-log-next-txid-join
                                                      (fn-store-log-next-txid-join
                                                       (fn-store-log-next-txid-join (nth 3 replay) 0)
                                                       (fn-store-cfg-next-txid (cadr config-records) 0))
                                                      (fn-lgc-next-txid (fn-xw-get log :kernel))))
                                               (log (fn-xw-put log :kernel (fn-lgc-consume-to (fn-xw-get log :kernel) next)))
                                               (store (fn-xw-put (fn-xw-put (fn-xw-put store :log log) :frontier next)
                                                                 :open-mode (list :full-replay (cadr choice)))))
                                          (mv-let (f replay fn-arena) (fn-xw-replay-flush replay fn-arena)
                                            (if (not (fn-xw-okp f)) (mv f store fn-octets-lg fn-arena state)
                                              (mv-let (erp action state)
                                                (fn-store-sn-recover-rows (fn-srs-rows (nth 0 replay)) next
                                                                          (cadr config-records) state)
                                                (declare (ignore erp))
                                                (let ((a (fn-xw-action action)))
                                                  (cond
                                                   ((not (fn-xw-okp a)) (mv a store fn-octets-lg fn-arena state))
                                                   ((eq action :refused)
                                                    (mv-let (erp text state) (fn-store-open-refusal-text state)
                                                      (declare (ignore erp))
                                                      (mv (if (stringp text) (list :open-refusal text)
                                                            (fn-xw-fault "ACL2 refused the open without naming a reason"))
                                                          store fn-octets-lg fn-arena state)))
                                                   ((not (eq action :recovering))
                                                    (mv-let (erp stop state) (fn-store-open-stop-text state)
                                                      (declare (ignore erp))
                                                      (mv (fn-xw-fault
                                                           (if (stringp stop)
                                                               (concatenate 'string "ACL2 replay rejected committed transaction history or configuration history: " stop)
                                                             "ACL2 replay rejected committed transaction history or configuration history"))
                                                          store fn-octets-lg fn-arena state)))
                                                   (t
                                                    (mv-let (erp gen state) (fn-store-cfg-generation state)
                                                      (declare (ignore erp))
                                                      (mv-let (erp served state) (fn-store-cfg-served state)
                                                        (declare (ignore erp))
                                                        (mv-let (erp domain state) (fn-store-cfg-domain state)
                                                          (declare (ignore erp))
                                                          (let ((g (fn-xw-natp-result gen)))
                                                            (cond
                                                             ((not (fn-xw-okp g)) (mv g store fn-octets-lg fn-arena state))
                                                             ((not (and (fn-xw-octet-list-p served) (fn-xw-octet-list-p domain)))
                                                              (mv (fn-xw-fault "ACL2 returned a non-octet list")
                                                                  store fn-octets-lg fn-arena state))
                                                             (t
                                                              (mv (list :ok (nth 7 replay) (caddr plan))
                                                                  (fn-xw-put (fn-xw-put (fn-xw-put store :generation gen)
                                                                                        :served (fn-xw-split-lf served nil nil))
                                                                             :domain (fn-xw-split-lf domain nil nil))
                                                                  fn-octets-lg fn-arena state))))))))))))))))))))))))))))))))))))

(defun fn-xw-recover (store fn-octets-lg fn-arena state)
  ; fnn-recover -> fnn-recover-log, writable: (mv RESULT STORE fn-octets-lg
  ; fn-arena state), RESULT (:ok COUNT)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena state)))
  (let ((store (fn-xw-put (fn-xw-put (fn-xw-put store :fenced t) :pending nil)
                          :open-mode '(:full-replay :absent))))
    (mv-let (r store fn-octets-lg fn-arena state) (fn-xw-recover-body store fn-octets-lg fn-arena state)
      (cond
       ((member-eq (car r) '(:fault :indeterminate :open-refusal))
        (mv r (fn-xw-put store :fenced t) fn-octets-lg fn-arena state))
       ((member-eq (car r) '(:refused :usage))
        (mv (fn-xw-fault (concatenate 'string "cannot reconstruct committed history: " (fn-xw-text r)))
            (fn-xw-put store :fenced t) fn-octets-lg fn-arena state))
       ((not (fn-xw-okp r)) (mv r store fn-octets-lg fn-arena state))
       (t
        (let ((count (cadr r)) (drop (caddr r))
              (c (fn-xw-at store "recover-replayed")))
          (if (not (fn-xw-okp c)) (mv c store fn-octets-lg fn-arena state)
            (mv-let (b store state)
              (fn-xw-barriers store (list (fn-xw-store-path store "journal") (fn-xw-get store :root)
                                          (fn-xw-parent (fn-xw-get store :root)))
                              1 nil state)
              (cond
               ((eq (car b) :os)
                (mv (fn-xw-indeterminate "cannot establish recovered log frontier")
                    (fn-xw-put store :fenced t) fn-octets-lg fn-arena state))
               ((not (fn-xw-okp b)) (mv b store fn-octets-lg fn-arena state))
               (t
                (mv-let (s store state) (fn-xw-sweep store 1000000 state)
                  (cond
                   ((member-eq (car s) '(:fault :indeterminate))
                    (mv s (fn-xw-put store :fenced t) fn-octets-lg fn-arena state))
                   ((not (fn-xw-okp s)) (mv s store fn-octets-lg fn-arena state))
                   (t
                    (let ((d (fn-xw-drop store drop)))
                      (cond
                       ((eq (car d) :os)
                        (mv (fn-xw-indeterminate
                             (concatenate 'string "the drop of covered log segments is uncertain: " (fn-xw-text d)))
                            (fn-xw-put store :fenced t) fn-octets-lg fn-arena state))
                       ((not (fn-xw-okp d)) (mv d store fn-octets-lg fn-arena state))
                       (t (mv (list :ok count) (fn-xw-put store :fenced nil)
                              fn-octets-lg fn-arena state)))))))))))))))))

(defun fn-xw-open-live-store (root fault repair fn-octets-lg fn-arena state)
  ; fnn-open-live-store ROOT t FAULT: (mv RESULT STORE fn-octets-lg fn-arena
  ; state), RESULT (:ok COUNT); on any failure the store is closed
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena state)))
  (let ((store (list (cons :root (fn-xw-absolute root)) (cons :fault fault) (cons :repair repair))))
    (mv-let (r store) (fn-xw-acquire store)
      (if (not (fn-xw-okp r)) (mv r store fn-octets-lg fn-arena state)
        (mv-let (erp action state) (fn-store-sn-reset state)
          (declare (ignore erp))
          (let ((a (fn-xw-action action)))
            (if (not (fn-xw-okp a)) (mv a (fn-xw-close store) fn-octets-lg fn-arena state)
              (mv-let (r store fn-octets-lg fn-arena state) (fn-xw-recover store fn-octets-lg fn-arena state)
                (if (fn-xw-okp r) (mv r store fn-octets-lg fn-arena state)
                  (mv r (fn-xw-close store) fn-octets-lg fn-arena state))))))))))

; ---------------------------------------------------------------------------
; The record log's commit of one record (fnn-log-reserve, fnn-log-compress,
; fnn-log-take, fnn-log-ensure-extent, fnn-log-append, fnn-log-fence,
; fnn-log-commit-open-batch, fnn-log-publish).  LOG is the store's :log.

(defun fn-xw-log (store) (declare (xargs :mode :program)) (fn-xw-get store :log))
(defun fn-xw-set-log (store k v)
  (declare (xargs :mode :program))
  (fn-xw-put store :log (fn-xw-put (fn-xw-log store) k v)))

(defun fn-xw-reserve (store current state)
  ; fnn-log-reserve: (mv (:ok NEXT) STORE state)
  (declare (xargs :mode :program :stobjs state))
  (cond
   ((not (fn-xw-get store :lock)) (mv (fn-xw-refuse "mutation requires a live exclusive store owner") store state))
   ((fn-xw-get store :fenced) (mv (fn-xw-indeterminate "store is fenced pending recovery") store state))
   ((not (eql current (fn-xw-get store :frontier)))
    (mv (fn-xw-fault "ACL2 allocator and the log's frontier disagree") (fn-xw-put store :fenced t) state))
   (t
    (let ((next (fn-store-metadata-frontier-next current)))
      (cond
       ((not (or (null next) (and (integerp next) (<= 0 next))))
        (mv (fn-xw-fault "ACL2 returned malformed allocation frontier successor") store state))
       ((null next) (mv (fn-xw-refuse "finite transaction-ID domain exhausted") store state))
       (t
        (let* ((store (fn-xw-set-log store :kernel (fn-lgc-consume-to (fn-xw-get (fn-xw-log store) :kernel) current)))
               (store (fn-xw-set-log store :reserved current)))
          (mv-let (o store state) (fn-xw-observe store :log-reserve :ok state)
            (cond ((not (fn-xw-okp o)) (mv o store state))
                  ((not (eq (cadr o) :reserved))
                   (mv (fn-xw-fault "ACL2 rejected the log route's reservation") (fn-xw-put store :fenced t) state))
                  (t (let* ((store (fn-xw-put store :frontier next))
                            (c (fn-xw-at store "frontier-reserved")))
                       (mv (if (fn-xw-okp c) (list :ok next) c) store state))))))))))))

(defun fn-xw-compress (store record state)
  ; fnn-log-compress: (mv (:ok RECORD-AS-THE-LOG-TAKES-IT) STORE state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (min store state)
    (let ((have (fn-xw-get (fn-xw-log store) :lz-min)))
      (if have (mv have store state)
        (mv-let (erp m state) (fn-store-compress-min-octets state)
          (declare (ignore erp))
          (mv m (fn-xw-set-log store :lz-min m) state))))
    (if (not (and (integerp min) (<= 0 min)))
        (mv (fn-xw-fault "ACL2 returned a non-natural") store state)
      (if (eql min 0) (mv (list :ok record) store state)
        (let ((plan (fn-lzr-append-plan min record)))
          (if (null plan) (mv (list :ok record) store state)
            (let* ((k (car plan)) (n (cdr plan))
                   (cap (fn-lzr-candidate-cap n))
                   (candidate (cond ((not (and (integerp k) (integerp n) (<= 0 k) (<= 0 n) (<= (+ k n) (len record))))
                                     (list :span))
                                    ((<= cap 0) :none)
                                    (t (fn-hx-lz4-candidate record k n cap)))))
              (cond
               ((equal candidate '(:span))
                (mv (fn-xw-fault "lz4-encoder: the span is not inside the record") store state))
               ((and (consp candidate) (eq (car candidate) :code))
                (mv (fn-xw-fault (fn-xw-cat (list "lz4-encoder: the encoder refused a planned span (code "
                                                  (fn-xw-dec (cadr candidate)) ")")))
                    store state))
               (t
                (let ((decision (fn-lzr-append-decide nil 0 min record k n candidate)))
                  (cond ((and (consp decision) (eq (car decision) :framed))
                         (mv (list :ok (cadr decision)) (fn-xw-set-log store :lz t) state))
                        ((and (consp decision) (eq (car decision) :kept)) (mv (list :ok record) store state))
                        ((and (consp decision) (eq (car decision) :refused)
                              (stringp (fn-lzr-append-refusal-text decision)))
                         ; the refused candidate's event; the log takes R
                         ; (fn-lzr-append-octets), as fnn-log-compress does
                         (prog2$ (cw "~s0~%" (fn-lzr-append-refusal-text decision))
                                 (mv (list :ok (fn-lzr-append-octets decision record)) store state)))
                        (t (mv (fn-xw-fault "ACL2 returned a malformed append decision")
                               store state)))))))))))))

(defun fn-xw-ensure-extent (store)
  ; fnn-log-ensure-extent: (mv RESULT STORE)
  (declare (xargs :mode :program))
  (let* ((log (fn-xw-log store))
         (ks (fn-xw-get log :kernel)) (unit (fn-xw-get log :unit)) (extent (fn-xw-get log :extent)))
    (if (not (fn-lgc-extension-needed-p ks extent unit))
        (mv (list :ok) store)
      (let ((next (fn-lgc-extension-target ks extent unit)))
        (if (not (and (integerp next) (<= 0 next) (fn-lg-extent-okp next unit) (< extent next)))
            (mv (if (and (integerp next) (<= 0 next)) (fn-xw-fault "ACL2 returned an invalid log extent")
                  (fn-xw-fault "ACL2 returned a non-natural"))
                store)
          (let* ((r (fn-xw-sys (fn-hx-preallocate (fn-xw-get log :h) extent next)))
                 (r (if (fn-xw-okp r) (fn-xw-log-at "log-extended") r))
                 (r (if (fn-xw-okp r) (fn-xw-sys (fn-hx-fdatasync (fn-xw-get log :h))) r))
                 (r (if (fn-xw-okp r) (fn-xw-log-at "log-extent-fenced") r)))
            (if (fn-xw-okp r) (mv r (fn-xw-set-log store :extent next)) (mv r store))))))))

(defun fn-xw-append (store)
  ; fnn-log-append: (mv RESULT STORE); the offline verbs stage no handle, so
  ; no member goes in flight (fnn-log-members-in-flight)
  (declare (xargs :mode :program))
  (let* ((log (fn-xw-log store))
         (ks (fn-xw-get log :kernel)) (unit (fn-xw-get log :unit)) (extent (fn-xw-get log :extent)))
    (if (not (fn-lgc-append-admitsp ks unit extent))
        (mv (fn-xw-refuse "the log kernel refuses the append (a batch in flight, fenced, or past the extent)") store)
      (let* ((frontier (fn-lgc-frontier ks))
             (w (fn-xw-sys (fn-hx-pwrite (fn-xw-get log :h) frontier (fn-lgc-append-octets ks unit)))))
        (if (not (fn-xw-okp w)) (mv w store)
          (let ((store (fn-xw-set-log store :kernel (fn-lgc-append ks unit extent))))
            (mv (fn-xw-log-at "log-written") store)))))))

(defun fn-xw-fence (store)
  ; fnn-log-fence: (mv RESULT STORE)
  (declare (xargs :mode :program))
  (let* ((log (fn-xw-log store))
         (b (fn-xw-sys (fn-hx-fdatasync (fn-xw-get log :h)))))
    (if (not (fn-xw-okp b))
        (mv (fn-xw-indeterminate (concatenate 'string "log barrier failed: " (fn-xw-text b)))
            (fn-xw-set-log store :kernel (fn-lgc-fence-failed (fn-xw-get log :kernel))))
      (let ((store (fn-xw-set-log store :kernel (fn-lgc-fence (fn-xw-get log :kernel) (fn-xw-get log :unit)))))
        (mv (fn-xw-log-at "log-fenced") store)))))

(defun fn-xw-commit-open-batch (store)
  ; fnn-log-commit-open-batch: (mv RESULT STORE)
  (declare (xargs :mode :program))
  (let ((log (fn-xw-log store)) (fenced (fn-xw-get store :fenced)))
    (if (not (< 0 (fn-xw-get log :count)))
        (mv (list :ok) store)
      (let ((store (fn-xw-put store :fenced t)))
        (mv-let (r store)
          (mv-let (r store) (fn-xw-ensure-extent store)
            (if (not (fn-xw-okp r)) (mv r store)
              (mv-let (r store) (fn-xw-append store)
                (let ((r (if (fn-xw-okp r) (fn-xw-at store "log-written") r)))
                  (if (not (fn-xw-okp r)) (mv r store)
                    (mv-let (r store) (fn-xw-fence store)
                      (mv (if (fn-xw-okp r) (fn-xw-at store "log-fenced") r) store)))))))
          (cond
           ((member-eq (car r) '(:indeterminate :fault)) (mv r store))
           ((eq (car r) :os)
            (mv (fn-xw-indeterminate (concatenate 'string "log batch outcome is indeterminate: " (fn-xw-text r)))
                (fn-xw-set-log store :kernel (fn-lgc-fence-failed (fn-xw-get (fn-xw-log store) :kernel)))))
           ((not (fn-xw-okp r))
            (mv (fn-xw-fault (concatenate 'string "the log kernel refused the batch's append: " (fn-xw-text r)))
                store))
           (t (let* ((log (fn-xw-log store))
                     (store (fn-xw-set-log store :pending (+ (fn-xw-get log :pending) (fn-xw-get log :count))))
                     (store (fn-xw-set-log store :count 0))
                     (store (fn-xw-set-log store :octets 0)))
                (mv (list :ok) (fn-xw-put store :fenced fenced))))))))))

(defun fn-xw-take (store octets tries)
  ; fnn-log-take: (mv RESULT STORE)
  (declare (xargs :mode :program))
  (if (zp tries) (mv (fn-xw-fault "the log kernel refused an empty batch's take") store)
    (let ((log (fn-xw-log store)))
      (if (eq (fn-lgc-phase (fn-xw-get log :kernel)) :fault)
          (mv (fn-xw-indeterminate "the log's barrier failed; the store needs recovery") store)
        (let ((answer (fn-lgc-take (fn-xw-get log :kernel) octets (fn-xw-get log :reserved)
                                   (fn-xw-get log :count) (fn-xw-get log :octets)
                                   (fn-xw-get log :bmax) (fn-xw-get log :omax) (fn-xw-get log :unit))))
          (case (car answer)
            (:taken (let* ((store (fn-xw-set-log store :kernel (cadr answer)))
                           (store (fn-xw-set-log store :count (+ 1 (fn-xw-get log :count))))
                           (store (fn-xw-set-log store :octets (+ (fn-xw-get log :octets) (caddr answer)))))
                      (mv (list :ok :taken) store)))
            (:full (mv-let (r store) (fn-xw-commit-open-batch store)
                     (if (not (fn-xw-okp r)) (mv r store) (fn-xw-take store octets (- tries 1)))))
            (otherwise
             (mv (fn-xw-fault "the log kernel refused the record (the owner's txid is not the log's next)") store))))))))

(defun fn-xw-log-publish (store sequence record state)
  ; fnn-publish -> fnn-log-publish: (mv RESULT STORE state)
  (declare (xargs :mode :program :stobjs state))
  (let ((c (fn-xw-at store "record-prepublish")))
    (cond
     ((not (fn-xw-okp c)) (mv c store state))
     ((not (fn-xw-get store :lock)) (mv (fn-xw-refuse "mutation requires a live exclusive store owner") store state))
     ((fn-xw-get store :fenced) (mv (fn-xw-indeterminate "store is fenced pending recovery") store state))
     ((not (eq (fn-store-publication-admissibility (fn-xw-get store :config) sequence (len record)) :admissible))
      (mv (fn-xw-refuse "prepared Store transaction exceeds persisted profile") store state))
     (t
      (mv-let (r store state) (fn-xw-compress store record state)
        (if (not (fn-xw-okp r)) (mv r store state)
          (mv-let (r store) (fn-xw-take (fn-xw-put store :fenced t) (cadr r) 2)
            (if (not (fn-xw-okp r)) (mv r store state)
              (mv-let (r store) (fn-xw-commit-open-batch store)
                (if (not (fn-xw-okp r)) (mv r store state)
                  (mv-let (o store state) (fn-xw-observe store :log-order :ok state)
                    (cond ((not (fn-xw-okp o)) (mv o store state))
                          ((not (eq (cadr o) :completing))
                           (mv (fn-xw-indeterminate "ACL2 rejected the record's place in the log") store state))
                          (t (let ((store (fn-xw-put store :pending t)))
                               (mv (fn-xw-at store "record-completing") store state)))))))))))))))

(defun fn-xw-finish-one (ks n)
  (declare (xargs :mode :program))
  (if (zp n) ks (fn-xw-finish-one (fn-lgc-finish-one ks) (- n 1))))

(defun fn-xw-finish (store state)
  ; fnn-finish: (mv RESULT STORE state), RESULT (:ok :durable)
  (declare (xargs :mode :program :stobjs state))
  (cond
   ((not (fn-xw-get store :lock)) (mv (fn-xw-refuse "mutation requires a live exclusive store owner") store state))
   ((not (and (fn-xw-get store :fenced) (fn-xw-get store :pending)))
    (mv (fn-xw-indeterminate "durable completion was not pending") store state))
   (t
    (let* ((store (fn-xw-put store :pending nil))
           (c (fn-xw-at store "finish-consumed")))
      (cond
       ((eq (car c) :os)
        (mv (fn-xw-indeterminate (concatenate 'string "completion interrupted after publication: " (fn-xw-text c)))
            (fn-xw-put store :fenced t) state))
       ((not (fn-xw-okp c)) (mv c store state))
       (t
        (mv-let (erp completion state) (fn-store-sn-finish state)
          (let ((a (if erp (list :fault "") (fn-xw-action completion))))
            (cond
             ((not (fn-xw-okp a))
              (mv (fn-xw-indeterminate "ACL2 completion failed after publication") (fn-xw-put store :fenced t) state))
             ((not (eq completion :durable))
              (mv (fn-xw-indeterminate "ACL2 rejected durable completion after publication")
                  (fn-xw-put store :fenced t) state))
             (t
              (let* ((store (fn-xw-put store :fenced nil))
                     (log (fn-xw-log store))
                     (store (fn-xw-set-log store :kernel (fn-xw-finish-one (fn-xw-get log :kernel) 1)))
                     (store (fn-xw-set-log store :pending (max 0 (- (fn-xw-get log :pending) 1))))
                     (c (fn-xw-at store "finish-durable")))
                (cond ((eq (car c) :os)
                       (mv (fn-xw-indeterminate
                            (concatenate 'string "writer reopening interrupted after the consumed completion: "
                                         (fn-xw-text c)))
                           (fn-xw-put store :fenced t) state))
                      ((not (fn-xw-okp c)) (mv c store state))
                      (t (mv (list :ok :durable) store state))))))))))))))

; ---------------------------------------------------------------------------
; `store ROOT post MSGID PAYLOAD CHARGE FAULT GROUP...' (fnn-command-post).

(defun fn-xw-digit-chars (cs acc)
  ; the value of a run of decimal digits, or NIL at a non-digit
  (declare (xargs :mode :program))
  (cond ((endp cs) acc)
        ((and (char<= #\0 (car cs)) (char<= (car cs) #\9))
         (fn-xw-digit-chars (cdr cs) (+ (* 10 acc) (- (char-code (car cs)) 48))))
        (t nil)))

(defun fn-xw-ws-p (c)
  (declare (xargs :mode :program))
  (member c '(#\Space #\Tab #\Newline #\Return #\Page)))

(defun fn-xw-trim-ws (cs)
  (declare (xargs :mode :program))
  (if (and (consp cs) (fn-xw-ws-p (car cs))) (fn-xw-trim-ws (cdr cs)) cs))

(defun fn-xw-parse-integer (text)
  ; SBCL's (parse-integer TEXT): whitespace around an optional sign and the
  ; digits; anything else its parse error, which fnn-main reports as an
  ; internal error
  (declare (xargs :mode :program))
  (let* ((cs (reverse (fn-xw-trim-ws (reverse (fn-xw-trim-ws (coerce text 'list))))))
         (neg (and (consp cs) (eql (car cs) #\-)))
         (digits (if (and (consp cs) (member (car cs) '(#\+ #\-))) (cdr cs) cs))
         (v (and (consp digits) (fn-xw-digit-chars digits 0))))
    (cond ((integerp v) (list :ok (if neg (- v) v)))
          ((endp cs) (list :internal (concatenate 'string "no non-whitespace characters in string "
                                                  (fn-xw-quote text) ".")))
          ((endp digits) (list :internal (concatenate 'string "no digits in string " (fn-xw-quote text))))
          (t (list :internal (concatenate 'string "junk in string " (fn-xw-quote text)))))))

(defun fn-xw-strings-octets (l)
  (declare (xargs :mode :program))
  (if (endp l) nil (cons (fn-xo-octets (car l)) (fn-xw-strings-octets (cdr l)))))

(defun fn-xw-group-codes (store groups)
  ; fnn-group-codes-for
  (declare (xargs :mode :program))
  (if (endp groups) (fn-xw-refuse "provide one or more distinct configured groups")
    (let ((value (fn-store-group-codes (fn-xw-strings-octets groups) (fn-xw-get store :domain))))
      (if (or (keywordp value) (not (true-listp value)) (not (equal (len value) (len groups))))
          (fn-xw-refuse "unknown or duplicate configured group")
        (list :ok value)))))

(defun fn-xw-as-octets (value)
  (declare (xargs :mode :program))
  (if (fn-xw-octet-list-p value) (list :ok value) (fn-xw-fault "ACL2 returned a non-octet list")))

(defun fn-xw-metadata (msgid payload state)
  ; fnn-metadata: (mv (:ok OBLIGATION-TEXT SUBJECT-TEXT PROVENANCE) state)
  (declare (xargs :mode :program :stobjs state))
  (let ((subject (fn-xw-as-octets (fn-store-subject-id-of-payload payload))))
    (if (not (fn-xw-okp subject)) (mv subject state)
      (let ((obligation (fn-xw-as-octets (fn-store-obligation-id-of msgid (cadr subject)))))
        (if (not (fn-xw-okp obligation)) (mv obligation state)
          (let ((otext (fn-xw-as-octets (fn-store-identity-text (cadr obligation))))
                (stext (fn-xw-as-octets (fn-store-identity-text (cadr subject)))))
            (cond ((not (fn-xw-okp otext)) (mv otext state))
                  ((not (fn-xw-okp stext)) (mv stext state))
                  (t (mv-let (erp prov state) (fn-store-prov-post state)
                       (cond (erp (mv (fn-xw-fault "ACL2 error in fn-store-prov-post") state))
                             ((not (fn-xw-octet-list-p prov))
                              (mv (fn-xw-fault "ACL2 returned invalid local-post provenance") state))
                             (t (mv (list :ok (cadr otext) (cadr stext) prov) state))))))))))))

(defun fn-xw-observation ()
  ; fnn-store-prepare-observation: the monotonic and wall readings, ACL2's
  ; reading of the wall clock (fn-otm-wall-reading) and its observation
  (declare (xargs :mode :program))
  (let* ((clock (fn-hx-clock))
         (reading (fn-otm-wall-reading (cadr clock) (caddr clock)))
         (ok (and (true-listp reading) (equal (len reading) 2)
                  (integerp (car reading)) (<= 0 (car reading)) (booleanp (cadr reading)))))
    (if (not ok) (fn-xw-fault "ACL2 returned a malformed wall reading")
      (list :ok (fn-clock-observation (car clock) (car reading) 1000 (cadr reading))))))

(defun fn-xw-prepare (msgid payload codes obligation subject evidence charge fn-arena state)
  ; fnn-bridge-prepare: (mv (:ok ACTION) fn-arena state)
  (declare (xargs :mode :program :stobjs (fn-arena state)))
  (let ((obs (fn-xw-observation)))
    (if (not (fn-xw-okp obs)) (mv obs fn-arena state)
      (mv-let (erp value fn-arena state)
        (fn-store-sn-prepare msgid payload codes obligation subject evidence charge (cadr obs) fn-arena state)
        (cond
         (erp (mv (fn-xw-fault "ACL2 error in fn-store-sn-prepare") fn-arena state))
         ((and (consp value) (eq (car value) :seal))
          (if (not (and (consp (cdr value)) (null (cddr value)) (fn-xw-octet-list-p (cadr value))))
              (mv (fn-xw-fault "ACL2 returned a malformed seal") fn-arena state)
            (let ((fn-arena (fn-arena-seal-list (cadr value) fn-arena)))
              (mv (list :ok :prepared) fn-arena state))))
         (t (mv (fn-xw-action value) fn-arena state)))))))

(defun fn-xw-post-commit (store msgid payload codes charge fn-arena state)
  ; the reservation, the prepare, the publication and the finish
  (declare (xargs :mode :program :stobjs (fn-arena state)))
  (mv-let (erp current state) (fn-store-sn-next-txid state)
    (declare (ignore erp))
    (let ((cur (fn-xw-natp-result current)))
      (if (not (fn-xw-okp cur)) (mv cur store fn-arena state)
        (mv-let (r store state) (fn-xw-reserve store current state)
          (if (not (fn-xw-okp r)) (mv r store fn-arena state)
            (mv-let (m state) (fn-xw-metadata msgid payload state)
              (if (not (fn-xw-okp m)) (mv m store fn-arena state)
                (mv-let (p fn-arena state)
                  (fn-xw-prepare msgid payload codes (nth 1 m) (nth 2 m) (nth 3 m) charge fn-arena state)
                  (cond
                   ((not (fn-xw-okp p)) (mv p store fn-arena state))
                   ((not (eq (cadr p) :prepared))
                    (mv-let (erp a state) (fn-store-sn-refuse-reservation state)
                      (declare (ignore erp))
                      (mv (if (eq a :refused)
                              (fn-xw-refuse (concatenate 'string "ACL2 refused post: " (fn-xw-kw (cadr p))))
                            (fn-xw-indeterminate "ACL2 could not consume refused reservation"))
                          (fn-xw-put store :fenced t) fn-arena state)))
                   (t
                    (mv-let (erp record state) (fn-store-sn-pending-octets fn-arena state)
                      (declare (ignore erp))
                      (let ((record (if (null record) (list :ok nil) (fn-xw-as-octets record))))
                        (if (not (fn-xw-okp record)) (mv record store fn-arena state)
                          (mv-let (erp sequence state) (fn-store-sn-pending-sequence state)
                            (declare (ignore erp))
                            (if (not (and (integerp sequence) (<= 0 sequence)))
                                (mv (fn-xw-fault "ACL2 returned no staged record sequence") store fn-arena state)
                              (mv-let (r store state) (fn-xw-log-publish store sequence (cadr record) state)
                                (cond
                                 ((eq (car r) :indeterminate) (mv r store fn-arena state))
                                 ((and (fn-xw-store-error-p r) (not (fn-xw-get store :fenced)))
                                  (mv-let (erp a state) (fn-store-sn-known-abort state)
                                    (declare (ignore erp))
                                    (mv (if (eq a :aborted) r
                                          (fn-xw-indeterminate "ACL2 rejected known pre-publication abort"))
                                        (fn-xw-put store :fenced t) fn-arena state)))
                                 ((not (fn-xw-okp r)) (mv r store fn-arena state))
                                 (t (mv-let (f store state) (fn-xw-finish (fn-xw-put store :fenced t) state)
                                      (mv (if (fn-xw-okp f) (list :ok :committed sequence charge) f)
                                          store fn-arena state)))))))))))))))))))))

(defun fn-xw-post-body (store msgid payload-path charge-text groups fn-arena state)
  ; fnn-command-post's body after the open: (mv RESULT STORE fn-arena state),
  ; RESULT (:ok :duplicate) or (:ok :committed SEQUENCE CHARGE)
  (declare (xargs :mode :program :stobjs (fn-arena state)))
  (let ((payload (fn-xw-read-file payload-path
                                  (+ 1 (fn-store-profile-max-article-octets (fn-xw-get store :config))))))
    (if (not (fn-xw-okp payload)) (mv payload store fn-arena state)
      (let* ((payload (cadr payload))
             (codes (fn-xw-group-codes store groups)))
        (if (not (fn-xw-okp codes)) (mv codes store fn-arena state)
          (let* ((codes (cadr codes))
                 (charge (if charge-text (fn-xw-parse-integer charge-text)
                           (let ((c (fn-store-charge (len payload))))
                             (if (and (integerp c) (< 0 c)) (list :ok c)
                               (fn-xw-fault "ACL2 returned a non-positive charge"))))))
            (if (not (fn-xw-okp charge)) (mv charge store fn-arena state)
              (let* ((charge (cadr charge))
                     (verdict (fn-sbud-post-boundary (fn-xw-get store :config) msgid (len payload) (len codes) charge)))
                (if (not (keywordp verdict))
                    (mv (fn-xw-fault "ACL2 returned an unexpected boundary verdict") store fn-arena state)
                  (let ((text (fn-sbud-post-boundary-refusal verdict)))
                    (cond
                     ((and text (fn-xw-octet-list-p text))
                      (mv (fn-xw-refuse (fn-xo-string text)) store fn-arena state))
                     (text (mv (fn-xw-fault "ACL2 returned a malformed POST boundary refusal") store fn-arena state))
                     (t
                      (mv-let (erp existing state) (fn-store-sn-existing-action msgid payload codes fn-arena state)
                        (let ((existing (if erp (fn-xw-fault "ACL2 error in fn-store-sn-existing-action")
                                          (fn-xw-action existing))))
                          (cond
                           ((not (fn-xw-okp existing)) (mv existing store fn-arena state))
                           ((eq (cadr existing) :duplicate) (mv (list :ok :duplicate) store fn-arena state))
                           ((eq (cadr existing) :conflict)
                            (mv (fn-xw-refuse "conflicting immutable Message-ID") store fn-arena state))
                           (t
                            (mv-let (erp word state)
                              (fn-store-sn-article-verdict-word (fn-xw-get store :config) (len payload) (len codes) state)
                              (cond
                               (erp (mv (fn-xw-fault "ACL2 error in fn-store-sn-article-verdict-word") store fn-arena state))
                               ((eq word :memberships)
                                (mv (fn-xw-refuse "store budget refuses the article's groups (memberships): each group it is posted to is charged to the history budget, and the article alone would fit; post it to fewer groups")
                                    store fn-arena state))
                               ((eq word :unaffordable)
                                (mv (fn-xw-refuse "store budget refuses the article (transaction count or history bound)")
                                    store fn-arena state))
                               ((not (eq word :admissible))
                                (mv (fn-xw-fault "ACL2 returned an invalid article verdict word") store fn-arena state))
                               (t (fn-xw-post-commit store msgid payload codes charge fn-arena state))))))))))))))))))))

(defun fn-xw-utf8-codes (bs)
  ; the characters' codes of a command-line word as the image reads it: SBCL
  ; decodes argv as UTF-8, and fnn-command-post takes (char-code c) of each
  ; character (fnn-ascii-octet-list) -- a code point, not an octet, for a
  ; character past U+007F.  BS: the word's octets; an octet no UTF-8 sequence
  ; starts is taken as itself.
  (declare (xargs :mode :program))
  (let ((b (car bs)) (r (cdr bs)))
    (cond ((endp bs) nil)
          ((and (<= 192 b) (< b 224) (consp r) (<= 128 (car r)) (< (car r) 192))
           (cons (+ (* 64 (- b 192)) (- (car r) 128)) (fn-xw-utf8-codes (cdr r))))
          ((and (<= 224 b) (< b 240) (consp r) (consp (cdr r))
                (<= 128 (car r)) (< (car r) 192) (<= 128 (cadr r)) (< (cadr r) 192))
           (cons (+ (* 4096 (- b 224)) (* 64 (- (car r) 128)) (- (cadr r) 128))
                 (fn-xw-utf8-codes (cddr r))))
          ((and (<= 240 b) (< b 248) (consp r) (consp (cdr r)) (consp (cddr r))
                (<= 128 (car r)) (< (car r) 192) (<= 128 (cadr r)) (< (cadr r) 192)
                (<= 128 (caddr r)) (< (caddr r) 192))
           (cons (+ (* 262144 (- b 240)) (* 4096 (- (car r) 128)) (* 64 (- (cadr r) 128)) (- (caddr r) 128))
                 (fn-xw-utf8-codes (cdddr r))))
          (t (cons b (fn-xw-utf8-codes r))))))

(defun fn-xw-command-post (root msgid-text payload-path charge-text inject groups fn-octets-lg fn-arena state)
  ; fnn-command-post: (mv RESULT fn-octets-lg fn-arena state), RESULT (:exit :accepted)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena state)))
  (let* ((msgid (fn-xw-utf8-codes (fn-xo-octets msgid-text)))
         (fault (fn-xw-post-faults inject (fn-hx-getenv "FN_NATIVE_POST_FAULT")
                                   (fn-hx-getenv "FN_NATIVE_RECOVERY_FAULT"))))
    (if (not (fn-xw-okp fault)) (mv fault fn-octets-lg fn-arena state)
      (mv-let (r store fn-octets-lg fn-arena state)
        (fn-xw-open-live-store root (cadr fault) nil fn-octets-lg fn-arena state)
        (if (not (fn-xw-okp r)) (mv r fn-octets-lg fn-arena state)
          (mv-let (r store fn-arena state)
            (fn-xw-post-body store msgid payload-path charge-text groups fn-arena state)
            (let ((store (fn-xw-close store)))
              (declare (ignore store))
              (cond ((not (fn-xw-okp r)) (mv r fn-octets-lg fn-arena state))
                    ((eq (cadr r) :duplicate)
                     (prog2$ (fn-hx-out "duplicate") (mv (list :exit :accepted) fn-octets-lg fn-arena state)))
                    (t (prog2$ (fn-hx-out (fn-xw-cat (list "committed sequence=" (fn-xw-dec (nth 2 r))
                                                           " charge=" (fn-xw-dec (nth 3 r)))))
                               (mv (list :exit :accepted) fn-octets-lg fn-arena state)))))))))))

; ---------------------------------------------------------------------------
; `store ROOT recover [--repair truncate SEGMENT:OFFSET]' (fnn-command-recover).

(defun fn-xw-join-words (l)
  (declare (xargs :mode :program))
  (cond ((endp l) "") ((endp (cdr l)) (car l)) (t (concatenate 'string (car l) " " (fn-xw-join-words (cdr l))))))

(defun fn-xw-orphan-report (store)
  ; fnn-orphan-report
  (declare (xargs :mode :program))
  (let ((orphans (fn-xw-get store :orphans)))
    (if (null orphans) "staging-orphans=0"
      (fn-xw-cat (list "staging-orphans=" (fn-xw-dec (len orphans))
                       (if (fn-xw-get store :orphans-more) "+" "")
                       " [" (fn-xw-join-words orphans) "]")))))

(defun fn-xw-out-lines (lines)
  (declare (xargs :mode :program))
  (if (endp lines) nil (prog2$ (fn-hx-out (car lines)) (fn-xw-out-lines (cdr lines)))))

(defun fn-xw-command-recover (root rest fn-octets-lg fn-arena state)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena state)))
  (let ((repair (cond ((null rest) (list :ok nil))
                      ((and (equal (len rest) 3) (equal (car rest) "--repair") (equal (cadr rest) "truncate"))
                       (list :ok (caddr rest)))
                      (t (list :usage "recover takes nothing, or --repair truncate SEGMENT:OFFSET (the at= of a log-damaged refusal)"))))
        (fault (fn-xw-selector (fn-hx-getenv "FN_NATIVE_RECOVERY_FAULT") "FN_NATIVE_RECOVERY_FAULT"
                               '("recover-replayed" "recover-barrier-1" "recover-barrier-2"
                                 "recover-barrier-3" "recovery-stage-unlinked")
                               "developer-only native recovery fault")))
    (cond
     ((not (fn-xw-okp repair)) (mv repair fn-octets-lg fn-arena state))
     ((not (fn-xw-okp fault)) (mv fault fn-octets-lg fn-arena state))
     (t
      (mv-let (r store fn-octets-lg fn-arena state)
        (fn-xw-open-live-store root (cadr fault) (cadr repair) fn-octets-lg fn-arena state)
        (if (not (fn-xw-okp r)) (mv r fn-octets-lg fn-arena state)
          (mv-let (erp articles state) (fn-store-sn-article-count state)
            (declare (ignore erp))
            (let* ((a (fn-xw-natp-result articles))
                   (anchor (fn-hx-lstat-full (fn-xw-store-path store "anchor.fnan")))
                   (uncertain (and (consp anchor) (eq (car anchor) :ok) (eq (cadr anchor) :regular)))
                   (store2 (fn-xw-close store)))
              (declare (ignore store2))
              (if (not (fn-xw-okp a)) (mv a fn-octets-lg fn-arena state)
                (prog2$
                 (fn-xw-out-lines
                  (append (list (fn-xw-cat (list "recovered transactions=" (fn-xw-dec (cadr r))
                                                 " articles=" (fn-xw-dec (cadr a))
                                                 " " (fn-xw-orphan-report store) " "
                                                 (if uncertain "anchor=uncertain [no anchor source in the native host]"
                                                   "anchor=none")))
                                (fn-xw-cat (list "open=full-replay reason="
                                                 (fn-xw-kw (cadr (fn-xw-get store :open-mode))))))
                          (reverse (fn-xw-get store :reports))))
                 (mv (list :exit (if uncertain :fenced :accepted)) fn-octets-lg fn-arena state)))))))))))

; ---------------------------------------------------------------------------
; `store ROOT node-secret create|rotate [IDENTITY]' (fnn-command-node-secret):
; the key files are ACL2's (books/node-secret.lisp); the host draws the root.

(defun fn-xw-octal-digits (n acc)
  (declare (xargs :mode :program))
  (if (< n 8) (cons (code-char (+ 48 n)) acc)
    (fn-xw-octal-digits (floor n 8) (cons (code-char (+ 48 (mod n 8))) acc))))

(defun fn-xw-keys-dir (store)
  ; fnn-node-secret-ensure-directory: (:ok DIR)
  (declare (xargs :mode :program))
  (let* ((dir (fn-xw-store-path store "keys"))
         (l (fn-xw-lstat dir)))
    (cond ((not (fn-xw-okp l)) l)
          ((null (cadr l))
           (let ((m (fn-xw-sys (fn-hx-mkdir dir))))
             (if (not (fn-xw-okp m)) m
               (let ((f (fn-xw-fsync-dir (fn-xw-get store :root))))
                 (if (fn-xw-okp f) (list :ok dir) f)))))
          ((not (eq (car (cadr l)) :directory))
           (fn-xw-fault (concatenate 'string "refusing non-directory key path: " dir)))
          (t (list :ok dir)))))

(defun fn-xw-fresh-root ()
  ; fnn-node-secret-fresh-root (fnn-csprng-octets)
  (declare (xargs :mode :program))
  (let ((width (fn-ns-secret-width)))
    (if (not (and (integerp width) (< 0 width)))
        (fn-xw-fault "ACL2 returned an invalid node secret width")
      (let ((r (fn-hx-random-octets width)))
        (if (fn-xw-errp r) (fn-xw-os r) r)))))

(defun fn-xw-render (entry)
  ; fnn-node-secret-render
  (declare (xargs :mode :program))
  (if (not (fn-ns-entryp entry)) (fn-xw-fault "ACL2 built an invalid node-secret entry")
    (let ((octets (fn-ns-file-render entry)))
      (if (fn-xw-octet-list-p octets) (list :ok octets)
        (fn-xw-fault "ACL2 returned invalid node-secret file octets")))))

(defun fn-xw-write-new (path octets nofollow)
  ; create PATH (O_EXCL), write OCTETS, fsync, close: :ok or the OS error
  (declare (xargs :mode :program))
  (let ((o (fn-hx-create-excl path nofollow)))
    (if (fn-xw-errp o) (fn-xw-os o)
      (let* ((w (fn-xw-sys (fn-hx-write-all (cadr o) octets)))
             (w (if (fn-xw-okp w) (fn-xw-sys (fn-hx-fsync (cadr o))) w))
             (c (fn-xw-sys (fn-hx-close (cadr o)))))
        (if (fn-xw-okp w) c w)))))

(defun fn-xw-publish-initial-file (store final octets)
  ; fnn-publish-initial-file without an initializer prefix:
  ; (:ok :published) | (:ok :existing) | the condition
  (declare (xargs :mode :program))
  (let* ((stage (fn-xw-join (fn-xw-store-path store "staging")
                            (fn-xw-cat (list ".init-" (fn-xw-dec (fn-hx-getpid)) "-" (fn-hx-random-hex 12)))))
         (w (fn-xw-write-new stage octets nil)))
    (if (not (fn-xw-okp w)) w
      (let* ((l (fn-hx-link stage final))
             (r (cond ((and (fn-xw-errp l) (eql (cadr l) 17)) (list :ok :existing))
                      ((fn-xw-errp l)
                       (fn-xw-indeterminate (concatenate 'string "initial immutable-link outcome is indeterminate: "
                                                         (caddr l))))
                      (t (let ((f (fn-xw-fsync-dir (fn-xw-get store :root))))
                           (if (fn-xw-okp f) (list :ok :published)
                             (fn-xw-indeterminate
                              (concatenate 'string "initial immutable-link directory fence is indeterminate: "
                                           (fn-xw-text f))))))))
             (u (fn-hx-unlink stage)))
        (declare (ignore u))
        r))))

(defun fn-xw-secret-create (store identity)
  ; fnn-node-secret-create STORE IDENTITY (existing :refuse)
  (declare (xargs :mode :program))
  (let ((dir (fn-xw-keys-dir store)))
    (if (not (fn-xw-okp dir)) dir
      (let* ((path (fn-xw-join (cadr dir) "node-secret.key"))
             (l (fn-xw-lstat path))
             (exists (fn-xw-refuse (fn-xw-cat (list "node secret " path " exists; refusing to replace it")))))
        (cond
         ((not (fn-xw-okp l)) l)
         ((cadr l) exists)
         (t (let ((root (fn-xw-fresh-root)))
              (if (not (fn-xw-okp root)) root
                (let ((octets (fn-xw-render (fn-ns-create-entry (and identity (fn-xo-octets identity)) (cadr root)))))
                  (if (not (fn-xw-okp octets)) octets
                    (let ((p (fn-xw-publish-initial-file store path (cadr octets))))
                      (cond ((not (fn-xw-okp p)) p)
                            ((eq (cadr p) :existing) exists)
                            (t (fn-xw-fsync-dir (cadr dir)))))))))))))))

(defun fn-xw-secret-read-entry (path what)
  ; fnn-node-secret-read-entry: (:ok ENTRY-OR-NIL)
  (declare (xargs :mode :program))
  (let ((l (fn-xw-lstat path)))
    (cond ((not (fn-xw-okp l)) l)
          ((null (cadr l)) (list :ok nil))
          ((not (eq (car (cadr l)) :regular))
           (fn-xw-refuse (fn-xw-cat (list what " " path " is not a regular file"))))
          ((not (eql 0 (logand (caddr (cadr l)) 63)))
           (fn-xw-refuse (fn-xw-cat (list what " " path " is readable or writable by group or others (mode "
                                          (coerce (fn-xw-octal-digits (logand (caddr (cadr l)) 511) nil) 'string)
                                          ")"))))
          (t (let ((raw (fn-xw-read-file path (+ 18 4 2 65535 32))))
               (if (not (fn-xw-okp raw)) raw
                 (let ((entry (fn-ns-file-parse (cadr raw))))
                   (if entry (list :ok entry)
                     (fn-xw-refuse (fn-xw-cat (list what " " path " is not a fn-node-secret v1 file")))))))))))

(defun fn-xw-secret-rotate (store identity)
  ; fnn-node-secret-rotate: (:ok EPOCH)
  (declare (xargs :mode :program))
  (let ((dir (fn-xw-keys-dir store)))
    (if (not (fn-xw-okp dir)) dir
      (let* ((path (fn-xw-join (cadr dir) "node-secret.key"))
             (current (fn-xw-secret-read-entry path "node secret")))
        (cond
         ((not (fn-xw-okp current)) current)
         ((null (cadr current))
          (fn-xw-refuse (fn-xw-cat (list "node secret " path " is missing: run `store " (fn-xw-get store :root)
                                         " node-secret create' once"))))
         (t
          (let* ((epoch (fn-ns-entry-epoch (cadr current)))
                 (keep (fn-xw-join (cadr dir) (fn-xw-cat (list "node-secret-" (fn-xw-dec epoch) ".key"))))
                 (l (fn-xw-lstat keep))
                 (k (cond ((not (fn-xw-okp l)) l)
                          ((cadr l)
                           (let ((a (fn-xw-read-file keep (+ 18 4 2 65535 32))))
                             (if (not (fn-xw-okp a)) a
                               (let ((b (fn-xw-read-file path (+ 18 4 2 65535 32))))
                                 (cond ((not (fn-xw-okp b)) b)
                                       ((equal (cadr a) (cadr b)) (list :ok))
                                       (t (fn-xw-refuse (fn-xw-cat (list "retained node secret " keep
                                                                         " exists and differs; refusing to rotate")))))))))
                          (t (let ((ln (fn-xw-sys (fn-hx-link path keep))))
                               (if (fn-xw-okp ln) (fn-xw-fsync-dir (cadr dir)) ln))))))
            (if (not (fn-xw-okp k)) k
              (let ((root (fn-xw-fresh-root)))
                (if (not (fn-xw-okp root)) root
                  (let* ((next (fn-ns-rotate-entry (cadr current) (and identity (fn-xo-octets identity)) (cadr root)))
                         (octets (fn-xw-render next)))
                    (if (not (fn-xw-okp octets)) octets
                      (let* ((stage (fn-xw-join (cadr dir) (fn-xw-cat (list ".node-secret-" (fn-xw-dec (fn-hx-getpid)) "-"
                                                                            (fn-hx-random-hex 8) ".stage"))))
                             (w (fn-xw-write-new stage (cadr octets) nil)))
                        (if (not (fn-xw-okp w)) w
                          (let ((rn (fn-hx-rename stage path)))
                            (if (fn-xw-errp rn)
                                (let ((u (fn-hx-unlink stage)))
                                  (declare (ignore u))
                                  (fn-xw-indeterminate (concatenate 'string "node secret rotation outcome is indeterminate: "
                                                                    (caddr rn))))
                              (let ((f (fn-xw-fsync-dir (cadr dir))))
                                (if (fn-xw-okp f) (list :ok (fn-ns-entry-epoch next)) f))))))))))))))))))

(defun fn-xw-command-node-secret (root words)
  (declare (xargs :mode :program))
  (let ((verb (car words)) (identity (cadr words)))
    (if (not (and (member-equal verb '("create" "rotate")) (null (cddr words))))
        (list :usage "usage: store ROOT node-secret create|rotate [IDENTITY]")
      (mv-let (r store) (fn-xw-acquire (list (cons :root (fn-xw-absolute root))))
        (if (not (fn-xw-okp r)) r
          (let* ((r (if (equal verb "create") (fn-xw-secret-create store identity)
                      (fn-xw-secret-rotate store identity)))
                 (store (fn-xw-close store)))
            (declare (ignore store))
            (cond ((not (fn-xw-okp r)) r)
                  ((equal verb "create") (prog2$ (fn-hx-out "node-secret created epoch 1") (list :exit :accepted)))
                  (t (prog2$ (fn-hx-out (concatenate 'string "node-secret rotated epoch " (fn-xw-dec (cadr r))))
                             (list :exit :accepted))))))))))

; ---------------------------------------------------------------------------
; The dispatch (fnn-dispatch's `store' arm, for the verbs this file holds).

(defun fn-xw-main (args fn-octets-lg fn-arena state)
  ; ARGS: the words after `--fn'.  (mv RESULT fn-octets-lg fn-arena state):
  ; (:exit :accepted|:fenced), or the condition that ended the command
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena state)))
  (cond
   ((not (and (consp args) (equal (car args) "store")))
    (mv (list :usage "extract: this program runs `store ROOT post|recover|node-secret' only")
        fn-octets-lg fn-arena state))
   ((< (len args) 3) (mv (list :usage "missing arguments") fn-octets-lg fn-arena state))
   (t
    (let ((root (cadr args)) (command (caddr args)) (rest (cdddr args)))
      (cond
       ((equal command "recover") (fn-xw-command-recover root rest fn-octets-lg fn-arena state))
       ((equal command "node-secret")
        (if (< (len args) 4) (mv (list :usage "missing arguments") fn-octets-lg fn-arena state)
          (mv (fn-xw-command-node-secret root rest) fn-octets-lg fn-arena state)))
       ((equal command "post")
        (if (< (len args) 8) (mv (list :usage "missing arguments") fn-octets-lg fn-arena state)
          (fn-xw-command-post root (nth 0 rest) (nth 1 rest)
                              (if (equal (nth 2 rest) "-") nil (nth 2 rest))
                              (if (equal (nth 3 rest) "-") nil (nth 3 rest))
                              (nthcdr 4 rest) fn-octets-lg fn-arena state)))
       (t (mv (list :usage (concatenate 'string "extract: store " command " is not in this program"))
              fn-octets-lg fn-arena state)))))))

