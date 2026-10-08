;;; RL-02: a checkpoint publication that captured and ended early, before
;;; the history's NEXT existed, over the DEPLOYED publication thread
;;; (host/native/owner.lisp fnn-owner-publish-captured), the DEPLOYED owner
;;; entries it and the due path call (host/owner-host.lisp
;;; fn-owner-sco-capture, -setup-of, -due, -publication-done,
;;; -publication-abandoned) and the deployed ACL2 decisions they ask
;;; (books/owner-checkpoint-open.lisp, owner-checkpoint-writer.lisp,
;;; owner-compact-request.lisp, owner-reclaim.lisp,
;;; owner-publication-lifecycle.lisp), against the owner's globals as a
;;; table.  MOCK: the store's I/O (the walk, the history image, the staged
;;; write) and the thread boundary's classifier are stubbed, so it is cited
;;; by no claim; the native witness is tests/test_native_checkpoint_abandon.py.
;;; Each case asserts the slot (fn-owner-sco-inflight) after the publication,
;;; then the recorded deferral and the next due decisions.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-owner-fault-service (service cid condition)
  (declare (ignorable service cid condition))
  (harness-stub-reached 'fnn-owner-fault-service "host/native/owner.lisp"))
(defun fnn-owner-fence-service (service)
  (declare (ignorable service))
  (harness-stub-reached 'fnn-owner-fence-service "host/native/owner.lisp"))
(defun fnn-owner-install-or-end (install original label)
  (declare (ignorable install original label))
  (harness-stub-reached 'fnn-owner-install-or-end "host/native/owner.lisp"))
;;; ---- derived stubs: END ----
(declaim (declaration xargs))

(defun strip-xargs (body)
  (remove-if (lambda (f) (and (consp f) (eq (car f) 'declare)
                              (consp (cadr f)) (eq (car (cadr f)) 'xargs)))
             body))

(defun load-deployed-forms (path wanted &key optional)
  "Evaluate PATH's top-level forms named by WANTED, (KIND NAME) each; a defun
loses its xargs declaration, a defconst is a defparameter.  OPTIONAL: a form
or a file that is absent is skipped (the base tree, before RL-02's fix)."
  (let ((missing (copy-list wanted)))
    (when (and optional (not (probe-file path)))
      (return-from load-deployed-forms nil))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval (case (car form)
                         (defun (destructuring-bind (name formals &rest body) (cdr form)
                                  `(defun ,name ,formals ,@(strip-xargs body))))
                         (defconst `(defparameter ,(cadr form) ,(caddr form)))
                         (t form)))
                 (setf missing (remove (list (car form) (cadr form)) missing :test #'equal))))
    (when (and missing (not optional))
      (error "deployed forms missing from ~a: ~s" path missing))))

;; ACL2's primitives the deployed forms read.
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun posp (x) (and (integerp x) (< 0 x)))
(defun zp (x) (not (posp x)))
(defun nfix (x) (if (natp x) x 0))
(defun len (x) (length x))
(defun true-listp (x) (null (cdr (last x))))
(defun member-eq (x l) (member x l :test #'eq))
(defun member-equal (x l) (member x l :test #'equal))
(defmacro value (x) `(values nil ,x state))
(defmacro mbe (&key logic exec) (declare (ignore logic)) exec)

;; The owner's globals.
(defvar *state* (make-hash-table))
(defun boundp-global (key state) (nth-value 1 (gethash key state)))
(defun f-get-global (key state) (gethash key state))
(defun f-put-global (key val state) (setf (gethash key state) val) state)

(load-deployed-forms "books/owner-reclaim.lisp" '((defun fn-orc-release-slot)))
(load-deployed-forms "books/owner-state-accessors.lisp"
 '((defun fn-owner-sco-global) (defun fn-owner-sco-deferred)))
(load-deployed-forms "books/consumer-position-fields.lisp" '((defun fn-cp-nth)))
(load-deployed-forms "books/store-checkpoint-accessors.lisp" '((defun fn-sco-at)))
(load-deployed-forms "books/store-checkpoint-open.lisp"
 '((defun fn-sco-records) (defun fn-sco-sequence)))
(load-deployed-forms "books/owner-checkpoint-open.lisp"
 '((defun fn-ock-publication-duep) (defun fn-ock-publication-next)))
(load-deployed-forms "books/owner-checkpoint-writer.lisp" '((defun fn-ock-publication-blockedp)))
(load-deployed-forms "books/owner-compact-request.lisp"
 '((defun fn-ock-requested-next) (defun fn-ock-request-duep)))
(load-deployed-forms "books/owner-publication-lifecycle.lisp"
 '((defconst *fn-opl-backoff-base-ms*) (defconst *fn-opl-backoff-cap-ms*)
   (defun fn-opl-delay) (defun fn-opl-classify) (defun fn-opl-recordp)
   (defun fn-opl-attempts-before) (defun fn-opl-not-before) (defun fn-opl-record)
   (defun fn-opl-eligiblep) (defun fn-opl-blockedp) (defun fn-opl-next-serial)
   (defun fn-opl-holdsp) (defun fn-opl-settle) (defun fn-opl-attempted))
 :optional t)
(load-deployed-forms "host/owner-host.lisp"
 '((defun fn-owner-sco-count) (defun fn-owner-sco-budget) (defun fn-owner-sco-due)
   (defun fn-owner-sco-capture) (defun fn-owner-sco-setup-of)
   (defun fn-owner-sco-publication-done)))
(load-deployed-forms "host/owner-host.lisp" '((defun fn-owner-sco-publication-abandoned))
                     :optional t)

;; Data readers of the store and the profile (nothing here decides the slot):
;; K = 128, the history *ROWS* records, nothing durable.
(defvar *rows* (make-list 64 :initial-element :row))
(defun fn-owner-core (state) (declare (ignore state)) :owner)
(defun fn-own-store (owner) (declare (ignore owner)) :store)
(defun fn-sn-files (st) (declare (ignore st)) :files)
(defun fn-sf-records (files) (declare (ignore files)) *rows*)
(defun fn-sf-records-count (files) (declare (ignore files)) (length *rows*))
(defun fn-sn-config-history (st) (declare (ignore st)) :configs)
(defun fn-sf-frontier (files) (declare (ignore files)) :frontier)
(defun fn-owner-store-profile (state) (declare (ignore state)) :profile)
(defun fn-bs-profile-max-open-suffix (profile) (declare (ignore profile)) 128)
(defun fn-bs-profile-max-record-octets (profile) (declare (ignore profile)) 4096)
(defun fn-ock-capture-budget (profile) (declare (ignore profile)) 1000000000)
(defun fn-ockp-space (free) free)
(defun fn-gen-node (v) (declare (ignore v)) :node)
(defun fn-gen-verdict-salt (v) (declare (ignore v)) :salt)
(defun fn-scka-strip-base (next) next)
(defun fn-scka-publication-setup (next frontier revision log seg budget free n)
  (declare (ignore next frontier revision log seg budget free n))
  (list '(:plan 1) nil nil nil nil 0 0))
(defun fn-scka-initial-state (walked n k) (declare (ignore walked n k)) :initial)

;;; The publication thread's seams.  *CASE* picks the early failure.
(defvar *case* nil)
(defvar *now* 1000)
(defvar *log* nil)
(defvar *checkpoint-stop-test* nil)
(defvar *fnn-checkpoint-stop-test* nil)
(defvar *fnn-section-step* nil)
(defvar *fnn-checkpoint-frames* nil)
(defvar *fnn-checkpoint-image-custody* nil)
(defconstant +fnn-checkpoint-batch-octets+ 65536)
(define-condition fnn-store-error (error) ((message :initarg :message :initform "" :reader fnn-store-error-message))
  (:report (lambda (c s) (format s "~a" (fnn-store-error-message c)))))
(define-condition fnn-store-fault (fnn-store-error) ())
(define-condition fnn-store-indeterminate (fnn-store-error) ())
(define-condition fnn-store-io-refusal (fnn-store-error) ())
;; RL-02's named image refusal, exactly as the tree declares it; absent on
;; the base tree, whose builder refuses with a bare fnn-store-io-refusal.
(defun load-deployed-text-form (path head)
  "Evaluate the one form of PATH that begins with the text HEAD (a file the
CL reader cannot read whole), or nothing when there is none."
  (let* ((text (with-open-file (s path)
                 (let ((out (make-string (file-length s))))
                   (subseq out 0 (read-sequence out s)))))
         (at (search head text)))
    (when at (eval (read-from-string text t nil :start at)))))
(load-deployed-text-form "host/native/io.lisp" "(define-condition fnn-history-image-refusal ")
(defun image-refusal (verdict)
  (if (find-class 'fnn-history-image-refusal nil)
      (error 'fnn-history-image-refusal :verdict verdict
             :message (format nil "history image refused by name: ~a" verdict))
    (error 'fnn-store-io-refusal
           :message (format nil "history image refused by name: ~a" verdict))))

(defmacro fnn-with-history-image (&body body) `(progn ,@body))
(defstruct fnn-owner-service (stopping nil) (store :store))
(defun fnn-gc-nursery-octets () (* 64 1024 1024))
(defun fnn-err (control &rest args)
  (let ((line (apply #'format nil control args)))
    (push line *log*)
    (format t "~a~%" line)))
(defun fnn-fault (control &rest args)
  (error 'fnn-store-fault :message (apply #'format nil control args)))
(defun fnn-owner-monotonic-ms () *now*)
(defun fnn-owner-core (name &rest args)
  (multiple-value-bind (erp val) (apply name (append args (list *state*)))
    (declare (ignore erp))
    val))
(defun fnn-core (name &rest args)
  (case name
    (fn-ockp-segment-octets 65536)
    (fn-owner-sco-next
     (if (eq *case* :unencodable) nil (list (list :next *rows*) (list 0 nil nil 100) (list nil nil nil))))
    (fn-sco-records (fn-sco-records (first args)))
    (fn-his-stream-free (first args))
    (fn-his-file-octets 100)
    (fn-owner-sco-setup-of (apply #'fn-owner-sco-setup-of args))
    (otherwise (error "unknown core seam ~s" name))))
(defun fnn-checkpoint-walk (records arena) (declare (ignore records arena)) :walk)
(defun fnn-extent-with-read-refusal (stage thunk)
  (if (eq *case* :walk-refused)
      (error 'fnn-store-io-refusal
             :message (format nil "the checkpoint publication is deferred: extent read refused (:pool) at the ~(~a~)" stage))
    (funcall thunk)))
(defun fnn-history-image-build (records node salt position)
  (declare (ignore records node salt))
  (case *case*
    (:image-count (image-refusal '(:refused :image-count)))
    (:pending-suffix (image-refusal '(:refused :pending-suffix)))
    (t (values position (list 1 nil)))))
(defun fnn-history-image-np (image) (and image (first image)))
(defun fnn-history-image-write (fd image) (declare (ignore fd image)) nil)
(defun fnn-store-log (store) (declare (ignore store)) :log)
(defun fnn-store-config (store) (declare (ignore store)) :config)
(defun fnn-log-make-durable (log) (declare (ignore log)) nil)
(defun fnn-state-checkpoint-write (store writer sequence image)
  (declare (ignore store writer sequence image))
  (error 'fnn-store-io-refusal :message "staged write refused: [Errno 28] No space left on device"))
(defun fnn-octets-pub-release () nil)
(defun fnn-live-octets-pub () :pub)
(defun fnn-checkpoint-write-steps (&rest args) (declare (ignore args)) 0)
(defun fnn-log-covered-indices (store k) (declare (ignore store k)) nil)
(defun fnn-log-drop (store covered) (declare (ignore store covered)) 0)
(defun fnn-segment-path-at (store k) (declare (ignore store k)) "")
(defun fnn-owner-release-extents (&rest args) (declare (ignore args)) nil)
(defun fnn-owner-serialized (service cid thunk &optional class)
  (declare (ignore service cid class))
  (funcall thunk))
;; The thread boundary's classifier (ACL2's fn-fs-classify-job): a known
;; refusal is :refusal, anything else here a job failure.
(defun fnn-owner-thread-escape (service condition label &optional jobp)
  (declare (ignore service label jobp))
  (if (typep condition 'fnn-store-io-refusal) :refusal :job-failure))
(defun fnn-condition-class (condition) (type-of condition))
(defun fn-fs-classify (class step) (declare (ignore class step)) :refusal)
(defun fnn-owner-worker-tail-hold (label) (declare (ignore label)) nil)
(defun fnn-owner-snapshot-pin-release (service pin) (declare (ignore service pin)) nil)
(defun fnn-owner-service-nursery () nil)
(defun fnn-owner-publisher-release (service) (declare (ignore service)) nil)
(defun fnn-owner-history-root-maintain (service) (declare (ignore service)) nil)
;; The publication's own "decide again" is the next case's business.
(defun fnn-owner-maybe-publish (service) (declare (ignore service)) nil)

(with-open-file (s "host/native/owner.lisp")
  (loop for form = (read s nil :eof) until (eq form :eof)
        when (and (consp form) (eq (car form) 'defun)
                  (member (cadr form) '(fnn-owner-publish-captured)))
          do (eval form)))

(defun check (ok label)
  (unless ok (format t "CHECKPOINT_ABANDON_ASSERTION:~a~%" label) (error "~a" label)))
(defun inflight () (gethash 'fn-owner-sco-inflight *state*))
(defun deferred () (gethash 'fn-owner-sco-deferred *state*))
(defun fresh-owner ()
  (clrhash *state*)
  (setq *log* nil *now* 1000 *rows* (make-list 64 :initial-element :row)))
(defun capture ()
  (let ((captured (fnn-owner-core 'fn-owner-sco-capture nil 1000000 "rev")))
    (check (and (true-listp captured) (eql (inflight) (length *rows*)))
           "the capture holds the slot at its count")
    captured))
(defun publish (case captured)
  (let ((*case* case))
    (fnn-owner-publish-captured (make-fnn-owner-service) captured :arena '(1 0) :pin)))
(defun due (now) (fnn-owner-core 'fn-owner-sco-due nil 1000000 now))
(defun abandoned-lines () (remove-if-not (lambda (l) (search "CHECKPOINT auto abandoned" l)) *log*))

;; 1. The history image refused by name for a reason that is not a
;; dependency: the slot is released and the publication BLOCKED, by name,
;; at every later count and time (the alarm; no storm of walks and
;; rotations on every POST).
(fresh-owner)
(publish :image-count (capture))
(check (null (inflight)) "an abandoned publication left fn-owner-sco-inflight set for the run")
(check (equal (subseq (deferred) 0 2) '(:deferred :blocked-history-image-refused))
       "the refused image is recorded as a deferral naming its reason")
(check (eq (nth 4 (deferred)) :blocked) "a refused image (not a dependency) blocks")
(check (= (length (abandoned-lines)) 1) "one CHECKPOINT auto abandoned line")
(check (search "class=blocked" (first (abandoned-lines))) "the line names the class")
(check (eq (due 1000) :blocked) "blocked at the same count")
(setq *rows* (make-list 200 :initial-element :row))
(check (eq (due 900000000) :blocked) "blocked at a later count and time")
(format t "PASS image refused by name: slot released, blocked by name~%")

;; 2. An unencodable history: released and blocked.
(fresh-owner)
(publish :unencodable (capture))
(check (null (inflight)) "an unencodable publication left fn-owner-sco-inflight set")
(check (equal (subseq (deferred) 0 2) '(:deferred :blocked-unencodable-history))
       "unencodable recorded by name")
(check (eq (due 900000000) :blocked) "unencodable blocks")
(format t "PASS unencodable history: slot released, blocked by name~%")

;; 3. A read refused during the walk (the store's I/O, may pass): released,
;; backed off by the clock alone; retried at the SAME count once the backoff
;; elapsed, with no commit; a late settlement of the first capture cannot
;; release the retry, though it shares the count.
(fresh-owner)
(let ((first-capture (capture)))
  (publish :walk-refused first-capture)
  (check (null (inflight)) "a refused walk left fn-owner-sco-inflight set")
  (check (eq (nth 4 (deferred)) :backoff) "a refused read backs off")
  (check (= (nth 6 (deferred)) 31000) "the backoff is 30 s from the abandonment")
  (check (eq (due 30999) :blocked) "before the backoff: blocked")
  (setq *rows* (append *rows* (make-list 10 :initial-element :row)))
  (check (eq (due 30999) :blocked) "commits do not hasten the backoff")
  (setq *rows* (make-list 64 :initial-element :row))
  (check (eq (due 31000) :due) "after the backoff the same count is due, with no commit")
  (let ((retry (capture)))
    (check (= (fifth retry) (fifth first-capture)) "the retry captured the same count")
    (check (eq (fnn-owner-core 'fn-owner-sco-publication-abandoned
                               (fifth first-capture) (car (last first-capture))
                               '(:io-refusal) 40000)
               :stale)
           "a late settlement of the first capture is stale")
    (check (eql (inflight) 64) "and the retry still holds the slot")
    (setq *now* 50000)
    (publish :walk-refused retry)
    (check (null (inflight)) "the retry settles its own slot")
    (check (= (nth 5 (deferred)) 2) "two abandonments in a row")
    (check (= (nth 6 (deferred)) (+ 50000 60000)) "the second backoff doubles")))
(format t "PASS refused walk: backoff by the clock, same-count retry, late settlement stale~%")

;; 4. A dependency still in flight (the image's pending suffix): eligible
;; only once the history advanced past the capture AND the backoff elapsed.
(fresh-owner)
(publish :pending-suffix (capture))
(check (null (inflight)) "a pending-suffix refusal left fn-owner-sco-inflight set")
(check (eq (nth 4 (deferred)) :await-change) "a pending suffix awaits the history")
(check (eq (due 900000000) :blocked) "time alone does not re-arm it")
(setq *rows* (make-list 65 :initial-element :row))
(check (eq (due 30999) :blocked) "a commit alone does not re-arm it")
(check (eq (due 31000) :due) "a commit and the backoff do")
(format t "PASS pending suffix: awaits the history's advance and the backoff~%")

;; 5. The staged write refused after NEXT existed: settled as an abandonment
;; first, then the done step installs NEXT as the base and keeps the record.
(fresh-owner)
(publish :write-refused (capture))
(check (null (inflight)) "a refused write left fn-owner-sco-inflight set")
(check (eq (nth 4 (deferred)) :backoff) "a refused write backs off, its record kept by done")
(check (equal (gethash 'fn-owner-sco-base *state*) (list :next *rows*)) "done installed NEXT")
(format t "PASS refused staged write: settled, then done keeps the record~%")

(format t "checkpoint abandon passed (5 cases)~%")
