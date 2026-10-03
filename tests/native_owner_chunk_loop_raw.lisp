;;; The deployed owner chunk loop, driven without an image.
;;;
;;; The served connection's life (host/native/mux.lisp) and the served step
;;; (host/native/owner.lisp fnn-owner-handle-chunk and what it calls) are
;;; read out of the files that ship them.  This exercises the shipped
;;; functions and not copies of them; the driver below plays the loop's poll
;;; and the committer, handing the connection each readiness and each
;;; completion it waits for.
;;;
;;; The harness is BUILT FROM DECLARATIONS, so the host cannot drift away from
;;; it silently (lane served-leftovers, 2026-09-27: the harness had been red
;;; all day on four independent drifts -- a stub's arity, a renamed dispatcher,
;;; a split function and two new callees -- each reported only as "the suffix
;;; was not the next step's input: NIL").  It declares three things:
;;;
;;;   *ROOTS*      the host functions the driver and the checks call;
;;;   the STUBS    every definition below whose name the host also defines:
;;;                the ACL2 boundary (fnn-core, fnn-owner-core, ...), the
;;;                socket, the TLS library and the owner mutex, each recording
;;;                what the loop did;
;;;   *UNREACHED*  host functions on branches these scenarios never take,
;;;                each a stub that fails the scenario if it is ever called.
;;;
;;; Everything else a root reaches, transitively, that host/native/io.lisp,
;;; owner.lisp or mux.lisp defines is EXTRACTED from the host source (a new
;;; callee, a split function, a struct's real slots come along by
;;; themselves).  At load the harness refuses, by name:
;;;   - a stub whose lambda list does not accept every arity the host's
;;;     definition accepts (a stale stub), or that stubs a name the host no
;;;     longer defines;
;;;   - a reached host function from any other file that is neither stubbed
;;;     nor declared unreached (a stale harness).
;;;
;;; Five properties, the first four each a defect found against the native
;;; 915 node on 2026-09-22 (planning/evidence/owner-defects-2026-09-22.md):
;;;
;;;   1. a step that consumes a prefix leaves the rest as the NEXT step's
;;;      input.  It is not a fault, and it is not read from the socket again.
;;;      The reachable case is an article over fn-own-body-limit, which closes
;;;      the wire mid-article (books/wire.lisp `fn-wire-after-line' answers
;;;      `fn-wire-close ... :body-overlimit' and
;;;      books/served-tls-prefix.lisp `fn-served-feed-counted' stops there);
;;;      the old line faulted and the whole process stopped.
;;;   2. the oversize article's closing step delivers its refusal and closes
;;;      gracefully; its suffix is not fed back.
;;;   3. a step that consumes nothing and neither closes nor hands the
;;;      transport over IS a fault: the same octets fed again cannot make
;;;      progress.
;;;   4. one clock reading reaches the owner at open and one before every
;;;      chunk, which is what gives each submission its own Injection-Date
;;;      (books/owner.lisp `fn-own-open'; RFC 5537 section 3.4).  A run whose
;;;      articles all carry one Date is exactly a host that read the clock
;;;      once.
;;;   5. the time model (planning/design-time-model-2026-09-27.md section
;;;      3.7, "who appends clock events"): on the format-9 path a served
;;;      POST's step appends exactly ONE disk clock event, on demand, and it
;;;      is recorded immediately before the admission that reads it
;;;      (fnn-owner-disk-admit, fn-otm-admit-post); a step that submits
;;;      nothing appends none.  The injection reading of property 4 is still
;;;      taken once per step, before the step's transition.  The submission
;;;      then waits for its batch and the reply follows the completion.

(require :sb-posix)
(require :sb-bsd-sockets)
(require :sb-introspect)
(defpackage "ACL2" (:use "CL"))
(defpackage "ACL2_*1*_ACL2" (:use))
(in-package "ACL2")

;;; ---------------------------------------------------------------------------
;;; The host's definitions, indexed.  Every top-level definition in
;;; host/native/*.lisp, by name and kind; EXTRACTABLE is where the harness may
;;; take a definition from (outside it, a reached function must be stubbed or
;;; declared unreached).

(defparameter *extractable*
  '("host/native/io.lisp" "host/native/owner.lisp" "host/native/mux.lisp"
    ;; Only the COMPRESS layer's structures (fnn-zin-pending on the mux's
    ;; step loop); its functions are declared unreached below.
    "host/native/deflate.lisp"
    ;; Likewise the cold line's structures (fnn-cold-worker); its functions
    ;; are declared unreached below.
    "host/native/extent.lisp"))

(defvar *host* (make-hash-table :test 'eq))   ; name -> list of (kind file form)
(defvar *ordinal* (make-hash-table :test 'eq)) ; form -> its position in the host

(defun index-form (form file)
  (setf (gethash form *ordinal*) (hash-table-count *ordinal*))
  (when (consp form)
    (let ((head (car form)))
      (flet ((note (name kind)
               (when (symbolp name)
                 (push (list kind file form) (gethash name *host*)))))
        (cond
          ((member head '(progn eval-when))
           (dolist (item (if (eq head 'eval-when) (cddr form) (cdr form)))
             (index-form item file)))
          ((eq head 'defun) (note (second form) :function))
          ((eq head 'defmacro) (note (second form) :macro))
          ((member head '(defconstant defvar defparameter)) (note (second form) :variable))
          ((eq head 'deftype) (note (second form) :type))
          ((eq head 'define-condition) (note (second form) :condition))
          ((eq head 'sb-alien:define-alien-routine)
           (let ((spec (second form)))
             (note (if (consp spec) (second spec) spec) :alien)))
          ((eq head 'defstruct)
           (let* ((spec (second form))
                  (name (if (consp spec) (car spec) spec))
                  (options (if (consp spec) (cdr spec) nil))
                  (conc (format nil "~a-" name))
                  (constructors nil) (predicate (format nil "~a-P" name)))
             (dolist (option options)
               (let ((key (if (consp option) (car option) option)))
                 (case key
                   (:conc-name (setq conc (if (and (consp option) (second option))
                                              (string (second option)) "")))
                   (:constructor (when (and (consp option) (second option))
                                   (push (second option) constructors)))
                   (:predicate (when (and (consp option) (second option))
                                 (setq predicate (string (second option))))))))
             (unless constructors (push (intern (format nil "MAKE-~a" name)) constructors))
             (note name :struct)
             (dolist (c constructors) (note c :struct))
             (note (intern predicate) :struct)
             (dolist (slot (cddr form))
               (unless (stringp slot)
                 (note (intern (format nil "~a~a" conc
                                       (if (consp slot) (car slot) slot)))
                       :struct))))))))))

(defun loaded-host-files ()
  "The host/native files the image build loads (host/native/build.lisp), and
what they load in turn, in order.  A file in host/native that no build loads
(a parked block, a runtime extension the image leaves out, such as
runtime-image-policy.lisp since stage 0) is not deployed code: indexing it
would either fail to read (its packages are absent) or offer the harness a
definition the node never runs."
  (let ((seen '()) (queue (list "host/native/build.lisp")) (needle "(load \"host/native/"))
    (loop while queue
          do (let* ((file (pop queue))
                    (text (with-open-file (stream file)
                            (let ((s (make-string (file-length stream))))
                              (subseq s 0 (read-sequence s stream))))))
               (loop for start = (search needle text) then (search needle text :start2 end)
                     for end = (and start (+ start (length needle)))
                     while start
                     do (let* ((close (position #\" text :start end))
                               (name (concatenate 'string "host/native/" (subseq text end close))))
                          (unless (or (member name seen :test #'string=)
                                      (member name queue :test #'string=)
                                      (string= name "host/native/build.lisp"))
                            (setq queue (append queue (list name))))))
               (unless (string= file "host/native/build.lisp")
                 (push file seen))))
    (nreverse seen)))

(let ((*read-eval* nil))
  (dolist (file (loaded-host-files))
    (with-open-file (stream file)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            do (index-form form file)))))

(defun host-entries (name) (gethash name *host*))

(defun host-lambda-list (name)
  "The lambda list the host gives the function NAME, or :none."
  (let ((entry (find-if (lambda (e) (member (first e) '(:function :alien)))
                        (host-entries name))))
    (cond ((null entry) :none)
          ((eq (first entry) :function) (third (third entry)))
          (t (mapcar #'first (cdddr (third entry)))))))

(defun arity-range (lambda-list)
  "(MIN . MAX) of the positional arguments LAMBDA-LIST accepts; MAX nil when
unbounded (&rest or &key)."
  (let ((min 0) (max 0) (mode :required))
    (dolist (item lambda-list (cons min max))
      (case item
        (&optional (setq mode :optional))
        ((&rest &body &key) (return (cons min nil)))
        (&aux (return (cons min max)))
        (t (when (eq mode :required) (incf min))
           (when max (incf max)))))))

;;; ---------------------------------------------------------------------------
;;; The recording stubs: the ACL2 boundary, the socket, the TLS library, the
;;; owner mutex and the log.  Every one is checked against the host below.

(defparameter *reads* nil)          ; octet vectors the socket will hand out
(defparameter *read-count* 0)       ; how many times the socket was read
(defparameter *chunks* nil)         ; each INCOMING the owner was handed
(defparameter *plans* nil)          ; (consumed closing starttls reply submitted) per step
(defparameter *step* nil)           ; the plan the current step is running
(defparameter *output* nil)         ; the octets fn-owner-output holds now
(defparameter *sent* nil)           ; each reply written to the socket
(defparameter *faults* nil)         ; each fault the service was stopped with
(defparameter *graceful* 0)         ; graceful closes
(defparameter *observations* nil)   ; (monotonic wall error has-wall) per reading
(defparameter *timeline* nil)       ; the owner's clock and admission events, in order
(defparameter *completion* nil)     ; what the committer answers a queued submission

(defconstant +fnn-exit-ok+ 0)
(defconstant +fnn-exit-uncertain+ 3)
(defconstant +fnn-exit-fault+ 4)

(defun fnn-socket-fd (socket) (declare (ignore socket)) 7)
;; Row A4 (c) (host/native/owner.lisp fnn-owner-chunk-span-no-io): the served
;; read runs first with the realizer's cold-extent throw armed; the stub says
;; the cache is on, so each step takes that path, and the recording ACL2
;; boundary below never meets a cold payload (no line throws
;; fnn-extent-cold), so every read is warm and the cold line's prefetch is
;; declared unreached.  The cold 403 itself is tests/test_native_slow_disk.py's.
(defvar *fnn-extent-no-io* nil)
(defun fnn-extent-no-io-usable-p () t)
(defun fnn-socket-shut (socket) (declare (ignore socket)) nil)
(defun fnn-tls-close-channel (channel) (declare (ignore channel)) nil)
;; host/native/tls.lisp's condition (tls.lisp is not extracted): the loop's
;; handler names it (host/native/mux.lisp), and SBCL resolves a handler's type
;; when a condition passes through it.
(define-condition fnn-tls-error (error)
  ((detail :initarg :detail))
  (:report (lambda (condition stream)
             (format stream "native TLS: ~a" (slot-value condition 'detail)))))
(defun fnn-now () (get-internal-real-time))
;; The graceful close's shutdown(2) of the output side.
(defun fnn-%shutdown (fd how) (declare (ignore fd how)) (incf *graceful*) 0)
;; statvfs(3) of the store (health-truth, PRF-359: the owner observes the free
;; space before a read's write admission): unobservable here, so every :space
;; event carries nil and nothing is shed for space.
(defun fnn-%statvfs (path buffer) (declare (ignore path buffer)) -1)
;; The owner mutex and its gate: the quantum runs at once.
(defun fnn-owner-serialized (service cid thunk &optional class)
  (declare (ignore service cid class)) (funcall thunk))
(defun fnn-owner-stop-service-locked (service code &optional answering)
  (declare (ignore service code answering)) nil)
(defun fnn-log-line (line) (declare (ignore line)) nil)
(defun fnn-owner-log (&optional global optional) (declare (ignore global optional)) nil)
(defun fnn-owner-socket-address (service socket)
  (declare (ignore service socket)) (values :inet (list 127 0 0 1)))
(defun fnn-owner-fence-service (service) (declare (ignore service)) nil)
(defun fnn-owner-fault-service (service cid condition)
  (declare (ignore service cid))
  (push (princ-to-string condition) *faults*))
(defun fnn-owner-abandon-connection (service cid condition &optional custody)
  (declare (ignore service cid condition custody)) nil)
(defun fnn-owner-send (fd channel octets seconds)
  (declare (ignore fd channel seconds))
  (push (text octets) *sent*))
(defun fnn-tls-consume-plaintext (fd expected seconds)
  (declare (ignore fd seconds)) expected)

;; The transport, one attempt each (fnn-mux-receive-now, fnn-mux-write-now,
;; and the drain's fnn-mux-read-plain): a read takes the next scripted chunk
;; (empty when the script ends: the peer closed); a write takes the whole
;; reply.
(defun fnn-mux-receive-now (service loop conn)
  (declare (ignore service loop conn))
  (incf *read-count*)
  (if *reads* (pop *reads*) (fnn-make-octets 0)))
(defun fnn-mux-write-now (conn)
  (let ((data (fnn-mux-conn-out conn)) (at (fnn-mux-conn-out-at conn)))
    (push (text (subseq data at)) *sent*)
    (- (length data) at)))
(defun fnn-mux-read-plain (fd &optional buffer)
  (declare (ignore fd buffer))
  (fnn-make-octets 0))
(defun fnn-mux-wake (loop) (declare (ignore loop)) nil)

;; The ACL2 boundary.  fnn-owner-core, fnn-owner-action and fnn-core answer
;; the scenario's plan; each call the time model cares about is recorded on
;; *timeline* in the order the owner made it.
(defun fnn-owner-core (name &rest args)
  (declare (ignore args))
  (ecase name
    (fn-owner-peer-for-socket-address nil)
    ;; PRF-161: the accept is admitted and opened by one ACL2 call, and every
    ;; step is charged against the address's budget first.
    (fn-owner-exposure-open (setq *output* (ascii "200 ready")) 1)
    (fn-owner-exposure-charge :proceed)
    ;; The served read size (fn-cbud-step-read-octets).
    (fn-owner-read-octets 4096)
    ;; PRF-164: no XREDEEM in these scenarios, so no connection waits.
    (fn-acct-host-owner-redeem-waitingp nil)
    ;; RFC 8054: no scenario sends COMPRESS DEFLATE, so no layer is owed.
    (fn-owner-compress-owed nil)))

(defun fnn-owner-action (name &rest args)
  (ecase name
    (fn-owner-observe (push args *observations*) (push :observe *timeline*) :observed)
    (fn-owner-close :closed)
    (fn-owner-exposure-idle :keep)
    (fn-owner-exposure-release :released)
    (fn-owner-tls-established :ok)
    ;; The plaintext open installs the SASL context (books/nntp-auth.lisp
    ;; (:sasl-context SEED BINDING)); it emits no reply.
    (fn-owner-sasl-context :ok)))

(defun fnn-owner-octets-global (name)
  (ecase name (fn-owner-output *output*)))

;; The octet buffer (books/octets-stobj.lisp fn-octets): the host fills it
;; once per read (fnn-octets-fill) and hands the owner the range [start, end)
;; (PRF-181, fn-owner-chunk-span); the stub records the range's octets as the
;; INCOMING that step was handed.
(defparameter *buffer* nil)
(defun fnn-octets-fill (vector) (setq *buffer* (fnn-octets vector)) *buffer*)

(defun take-step (incoming)
  (push (text incoming) *chunks*)
  (setq *step* (pop *plans*))
  (unless *step* (error "the loop took a step this scenario did not plan"))
  (setq *output* (ascii (fourth *step*)))
  :ok)

(defun fnn-core-buffer-state (name &rest args)
  (ecase name
    (fn-owner-chunk-span
     ;; SCHED is the gate's scheduler value at this read's recorded time
     ;; (lane log-leftovers: the read's admission and reason lines are
     ;; ACL2's over it); no disk here is slow, so every read admits.
     (destructuring-bind (cid start end sched) args
       (declare (ignore cid))
       (unless (eq sched :sched)
         (error "a read was handed the scheduler value ~s; the gate here holds :sched" sched))
       (take-step (subseq *buffer* start end))))))

;; The disk's clock and admission (books/owner-time-model.lisp): the event is
;; recorded with its reading; the admission reads the recorded time.
(defun fnn-call (name &rest args)
  (ecase name
    (fn-otm-disk-event
     (destructuring-bind (sched kind now deadline) args
       (declare (ignore deadline))
       (push (list :disk kind now) *timeline*)
       (list :none sched)))
    ;; Response ownership (books/response-plan-pins.lisp fn-rpin-step: the
    ;; reply plan's hold, acquired at capture and released by stage 0's
    ;; restored unpin in fnn-owner-response-unpin).  The stub keeps the
    ;; model's owner table, one hold per connection, at generation 0; the
    ;; arena's pin table is the token fn-arpn-initial answered.
    (fn-rpin-step
     (destructuring-bind (owners pins event) args
       (let ((held (assoc (second event) owners)))
         (ecase (first event)
           (:acquire (if held
                         (list owners pins :duplicate)
                       (list (acons (second event) 0 owners) pins :acquired)))
           (:release (if held
                         (list (remove held owners) pins :released)
                       (list owners pins :absent)))))))))

;; The step's typed result (books/served-plan.lisp fn-splan-step-*): the
;; scenario's plan supplies it, so the loop reads it exactly where
;; host/native/owner.lisp reads it.  The render (fnn-owner-render-next:
;; ACL2's fn-splan-window into a private buffer) is a stub over a plan that
;; is the list of the reply's remaining windows.
(defun fnn-core (name &rest args)
  (ecase name
    ;; The wall reading's validity is ACL2's (books/owner-time-model.lisp
    ;; fn-otm-wall-reading, lane time-model-2): milliseconds since the DTN
    ;; epoch and T at or after it, else (0 NIL).  The stub answers the
    ;; model's value on the host's raw reading.
    (fn-otm-wall-reading
     (destructuring-bind (seconds microseconds) args
       (if (and (integerp seconds) (integerp microseconds) (<= 0 microseconds)
                (<= 946684800 seconds))
           (list (+ (* 1000 (- seconds 946684800)) (floor microseconds 1000)) t)
         (list 0 nil))))
    ;; The monotonic milliseconds are ACL2's too (books/clock-wall-reading.lisp
    ;; fn-otm-monotonic-ms, PRF-305): the stub answers the model's value.
    (fn-otm-monotonic-ms
     (destructuring-bind (ticks units) args
       (floor (* ticks 1000) units)))
    ;; The empty arena-pin table (fn-arpn-initial), on the first release.
    (fn-arpn-initial :arena-pins)
    ;; S9's intake fence (books/owner-retire-counted.lisp
    ;; fn-ort-intake-action): the model's value; no scenario here retires.
    (fn-ort-intake-action (if (first args) :refused :admit))
    (fn-splan-step-p t)
    (fn-splan-step-closep (second *step*))
    (fn-splan-step-handshake-owed (third *step*))
    (fn-splan-step-submittedp (fifth *step*))
    (fn-splan-step-consumed
     (if (eq (first *step*) :all) (length (first *chunks*)) (first *step*)))
    ;; No read in these scenarios sends a 441 (books/owner-log.lisp
    ;; fn-olog-served-refusal-lines), so the refusal log lines are empty.
    (fn-splan-step-refusal-lines nil)
    ;; No step here reaches the failed-login limit (fn-exp-observe).
    (fn-splan-step-exposure-close nil)
    ;; The plan: the reply (the completion, once a batch answered) as its one
    ;; window, or nothing to write.
    (fn-splan-step-plan
     (let ((octets (if (second args) (fnn-octets (second args)) *output*)))
       (if (> (length octets) 0) (list octets) nil)))
    (fn-otm-admit-post (push :admit *timeline*) :admit)
    ;; A transit peer's read proceeds (fn-otm-peer-read-proceeds-p); these
    ;; scenarios are reader connections, which never ask.
    (fn-otm-peer-read-proceeds-p t)
    (fn-otm-log-line nil)
    ;; books/sasl.lisp *fn-sasl-seed-octets*.
    (fn-owner-sasl-seed-octets 32)))

;; The OS CSPRNG (host/native/io.lisp): the connection's SASL seed.
(defun fnn-csprng-octets (width what)
  (declare (ignore what))
  (make-list width :initial-element 0))
(defun fnn-owner-render-next (plan &optional compressedp)
  (declare (ignore compressedp))
  (if plan
      (values (first plan) (rest plan) (null (rest plan)))
    (values (fnn-make-octets 0) nil t)))

;;; ---------------------------------------------------------------------------
;;; The declarations.

(defparameter *roots*
  '(;; The connection's life, as the loop drives it.
    fnn-mux-begin fnn-mux-dispatch fnn-mux-take-arrived fnn-mux-guarded
    %make-fnn-mux-loop %make-fnn-mux-conn fnn-mux-loop-conns fnn-mux-conn-phase
    fnn-mux-conn-out fnn-mux-conn-out-at fnn-mux-conn-await fnn-mux-conn-cid
    ;; The committer's hand-over (host/native/owner.lisp).
    fnn-owner-deliver %make-fnn-owner-service %make-fnn-owner-gate
    ;; What the checks read.
    fnn-owner-wall-milliseconds fnn-octets fnn-make-octets fnn-ascii-octet-list))

(defparameter *unreached*
  '(;; Implicit TLS and STARTTLS: no scenario negotiates TLS.
    fnn-tls-accept-begin fnn-tls-accept-step fnn-tls-channel-of fnn-%ssl-free
    fnn-tls-exporter
    ;; The slow disk sheds the queued POSTs (every admission here is :admit).
    fnn-owner-shed-queued-locked
    ;; A submission drained in its own quantum (these scenarios batch).
    fnn-owner-drain-one
    ;; XREDEEM (PRF-164): no connection here waits for a redeem.
    fnn-owner-redeem-quantum
    ;; Row A4 (c): no read here meets a cold payload (see the stub above);
    ;; the unfunded cold line's issue and settlement (books/page-read-direct.lisp).
    fnn-extent-issue-direct fnn-extent-direct-settle
    ;; The rest of the cold line (host/native/extent.lisp, reached through
    ;; fnn-owner-cold-issue-locked / -await / -result-locked / -shutdown and
    ;; the pending-extent release): no extent is ever issued here.
    fnn-extent-cache-release fnn-extent-cache-store
    fnn-extent-cancel-read fnn-extent-close fnn-extent-complete-read
    fnn-extent-executor-commit fnn-extent-executor-observe-returned
    fnn-extent-executor-returned-p fnn-extent-executor-wait
    fnn-extent-issue-read fnn-extent-pool-funded-p
    ;; COMPRESS (RFC 8054): no scenario negotiates the DEFLATE layer.
    fnn-zin-new fnn-zin-inflate fnn-zout-new fnn-zout-sync fnn-zout-free))

(dolist (name *unreached*)
  (let ((name name))
    (when (fboundp name)
      (error "~a is both stubbed and declared unreached" name))
    (when (eq (host-lambda-list name) :none)
      (error "stale harness: ~a is declared unreached, and the host no longer ~
              defines it" name))
    (setf (fdefinition name)
          (lambda (&rest args)
            (declare (ignore args))
            (error "the harness reached ~a, which it declares unreached" name)))))

;;; The stubs are checked against the host: each names a host function, and
;;; accepts every arity the host's definition accepts.
(let ((problems nil))
  (do-symbols (symbol "ACL2")
    (when (and (eq (symbol-package symbol) (find-package "ACL2"))
               (fboundp symbol) (not (macro-function symbol))
               (not (member symbol *unreached*))
               (>= (length (symbol-name symbol)) 4)
               (string= "FNN-" (symbol-name symbol) :end2 4))
      (let ((host (host-lambda-list symbol)))
        (if (eq host :none)
            (push (format nil "stale stub: the host defines no function ~(~a~)" symbol)
                  problems)
          (let ((want (arity-range host))
                (have (arity-range (sb-introspect:function-lambda-list symbol))))
            (unless (and (<= (car have) (car want))
                         (or (null (cdr have))
                             (and (cdr want) (<= (cdr want) (cdr have)))))
              (push (format nil "stale stub: ~(~a~) takes ~(~s~) in the harness and ~
                                 ~(~s~) in the host" symbol
                            (sb-introspect:function-lambda-list symbol) host)
                    problems)))))))
  (when problems
    (error "~{~a~^~%~}" (sort problems #'string<))))

;;; ---------------------------------------------------------------------------
;;; The extraction: the closure of *ROOTS* over the host's definitions, minus
;;; what the harness provides.

(defun provided-p (name kind)
  (case kind
    ((:function :alien) (fboundp name))
    (:macro (macro-function name))
    (:variable (boundp name))
    (:condition (find-class name nil))
    (t nil)))

(defun symbols-of (form fn)
  (cond ((symbolp form) (funcall fn form))
        ((consp form) (symbols-of (car form) fn) (symbols-of (cdr form) fn))
        ((typep form 'sb-impl::comma) (symbols-of (sb-impl::comma-expr form) fn))))

(defparameter *extracted* nil)        ; (file . form), each form once
(defparameter *unresolved* nil)
(defparameter *reached* (make-hash-table :test 'eq))

(let ((seen *reached*) (queue (copy-list *roots*)))
  (loop while queue
        do (let ((name (pop queue)))
             (unless (gethash name seen)
               (setf (gethash name seen) t)
               (dolist (entry (host-entries name))
                 (destructuring-bind (kind file form) entry
                   (cond
                     ((provided-p name kind))
                     ((not (member file *extractable* :test #'string=))
                      (when (member kind '(:function :alien :macro :struct))
                        (pushnew (format nil "~(~a~) (~a)" name file) *unresolved*
                                 :test #'string=)))
                     ((eq kind :alien)
                      (pushnew (format nil "~(~a~) (~a, a foreign routine)" name file)
                               *unresolved* :test #'string=))
                     ((not (find form *extracted* :key #'cdr :test #'eq))
                      (push (cons file form) *extracted*)
                      (symbols-of form (lambda (s)
                                         (when (and (host-entries s)
                                                    (not (gethash s seen)))
                                           (push s queue))))))))))))

(let ((idle (remove-if (lambda (name) (gethash name *reached*)) *unreached*)))
  (when idle
    (error "stale harness: declared unreached, and nothing reaches them: ~(~{~a~^ ~}~)"
           idle)))

(when *unresolved*
  (error "stale harness: the connection life reaches host functions this harness ~
          neither extracts, stubs nor declares unreached:~%~{  ~a~%~}"
         (sort *unresolved* #'string<)))

;;; Evaluate what was extracted: definitions that others expand or read first
;;; (constants, types, conditions, structures, macros), then the functions,
;;; each group in the host's own order.
(let* ((rank (lambda (form)
               (case (car form)
                 ((defconstant defvar defparameter) 0) (deftype 1)
                 (define-condition 2) (defstruct 3) (defmacro 4) (t 5))))
       (ordered (stable-sort
                 (reverse *extracted*)
                 (lambda (a b)
                   (let ((ra (funcall rank (cdr a))) (rb (funcall rank (cdr b))))
                     (or (< ra rb)
                         (and (= ra rb)
                              (< (gethash (cdr a) *ordinal*)
                                 (gethash (cdr b) *ordinal*)))))))))
  (handler-bind ((style-warning #'muffle-warning)
                 (sb-ext:compiler-note #'muffle-warning))
    (dolist (item ordered) (eval (cdr item)))))

;;; ---------------------------------------------------------------------------
;;; The driver: the loop's poll and the committer.  Each pass hands the
;;; connection what it waits for -- a committed completion when it waits for
;;; its batch, else the readiness of its descriptor (a draining connection
;;; then reads the peer's end of input).

(defun drive (loop conn)
  (let ((service (fnn-mux-loop-service loop)))
    (loop repeat 1000
          until (eq (fnn-mux-conn-phase conn) :done)
          do (if (fnn-mux-conn-await conn)
                 (progn (fnn-owner-deliver service (fnn-mux-conn-cid conn) *completion*)
                        (fnn-mux-take-arrived loop))
               (fnn-mux-dispatch loop conn))))
  (unless (eq (fnn-mux-conn-phase conn) :done)
    (error "the connection did not end")))

(defun ascii (string) (fnn-octets (fnn-ascii-octet-list string)))
(defun text (octets) (map 'string #'code-char octets))

(defun run-scenario (reads plans &key batching)
  (setq *reads* (mapcar #'ascii reads)
        *read-count* 0 *chunks* nil *plans* plans *step* nil *output* nil
        *sent* nil *faults* nil *graceful* 0 *observations* nil *timeline* nil
        *completion* (fnn-ascii-octet-list "240 article received"))
  (let* ((service (%make-fnn-owner-service :batching batching
                                           :gate (%make-fnn-owner-gate :sched :sched)))
         (loop (%make-fnn-mux-loop :service service))
         (conn (%make-fnn-mux-conn :socket :socket)))
    (push conn (fnn-mux-loop-conns loop))
    (fnn-mux-guarded (loop conn) (fnn-mux-begin loop conn))
    (drive loop conn))
  (setq *chunks* (reverse *chunks*) *sent* (reverse *sent*)
        *observations* (reverse *observations*) *timeline* (reverse *timeline*)))

(defun check (test control &rest args)
  (unless test (error (apply #'format nil control args))))

;;; 1. A prefix consume leaves the suffix for the next step, and the socket is
;;;    not read for it.  The second read carries "BBBBB" and that step consumes
;;;    two octets; the third step must be handed exactly "BBB".
(run-scenario '("AAA" "BBBBB")
              (list (list :all nil nil "")
                    (list 2 nil nil "")
                    (list :all nil nil "")))
(check (null *faults*) "a partial consume faulted: ~s" *faults*)
(check (equal *chunks* '("AAA" "BBBBB" "BBB"))
       "the suffix was not the next step's input: ~s" *chunks*)
;; Three planned steps, then one read that ends the input: four reads would
;; mean the suffix had been taken from the socket a second time.
(check (= *read-count* 3) "the suffix was read from the socket again: ~d reads"
       *read-count*)

;;; 2. The oversize article: the step consumes the prefix that fitted, answers
;;;    the refusal and closes.  The process must survive, the client must get
;;;    the line, and the connection must end gracefully.
(run-scenario '("HELLO" "ARTICLE-TAIL")
              (list (list :all nil nil "")
                    (list 4 t nil "441 posting failed; the article was not received")))
(check (null *faults*) "an oversize article stopped the owner: ~s" *faults*)
(check (equal *sent* '("200 ready"
                       "441 posting failed; the article was not received"))
       "the refusal did not reach the client: ~s" *sent*)
(check (= *graceful* 1) "the connection did not close gracefully: ~d" *graceful*)
(check (equal *chunks* '("HELLO" "ARTICLE-TAIL"))
       "a closing step's suffix was fed back: ~s" *chunks*)

;;; 3. No progress is a fault: consumed 0, not closing, not handing over.
(run-scenario '("STUCK") (list (list 0 nil nil "")))
(check (= (length *faults*) 1) "a no-progress step did not fault: ~s" *faults*)
(check (search "consumed no octets" (first *faults*))
       "the no-progress fault says something else: ~s" (first *faults*))

;;; 4. One reading at open and one before every chunk (the exposure charge is
;;;    decided in the chunk's own quantum since HST-023, under that reading;
;;;    a deferred connection is stepped again and reads again), each a fresh
;;;    reading of this host's clocks in the units fn-clock-observation takes.
(run-scenario '("ONE" "TWO")
              (list (list :all nil nil "") (list :all nil nil "")))
(check (null *faults*) "an ordinary exchange faulted: ~s" *faults*)
(check (= (length *observations*) 3)
       "the owner was handed ~d clock readings for an open and two chunks"
       (length *observations*))
(check (notany #'consp *timeline*)
       "a step that submitted nothing appended a disk clock event: ~s" *timeline*)
(let ((now (fnn-owner-wall-milliseconds)))
  (dolist (observation *observations*)
    (destructuring-bind (monotonic wall error has-wall) observation
      (check (and (integerp monotonic) (<= 0 monotonic))
             "a monotonic reading is not a count of milliseconds: ~s" monotonic)
      (check (and (integerp wall) (< (abs (- wall now)) 60000))
             "a wall reading is not this minute's: ~s against ~s" wall now)
      (check (and (integerp error) (< 0 error))
             "a reading carries no error bound: ~s" error)
      (check (eq has-wall t) "a reading claims no wall clock: ~s" has-wall))))
(check (apply #'<= (mapcar #'second *observations*))
       "the wall readings went backwards: ~s" (mapcar #'second *observations*))
;; The defect: one reading reused for the whole run.  A reading taken per
;; event moves with the clock, so sleeping past the resolution must change it.
(let ((before (fnn-owner-wall-milliseconds)))
  (sleep 1.1)
  (check (<= (+ before 1000) (fnn-owner-wall-milliseconds))
         "the wall reading did not advance over 1.1 seconds"))

;;; 5. The format-9 path: a read, then a POST's step that submits, then a
;;;    read.  Per step one injection reading before the transition; the
;;;    POST's step alone appends one disk clock event, immediately before its
;;;    admission; its reply is the batch's completion.
(run-scenario '("GROUP" "POST-ARTICLE" "QUIT")
              (list (list :all nil nil "211 group")
                    (list :all nil nil "" t)
                    (list :all t nil "205 bye"))
              :batching t)
(check (null *faults*) "a batched POST faulted: ~s" *faults*)
(check (equal *sent* '("200 ready" "211 group" "240 article received" "205 bye"))
       "the batched POST's completion did not follow its step: ~s" *sent*)
(check (= (length *observations*) 4)
       "the owner was handed ~d injection readings for an open and three steps"
       (length *observations*))
; Lane time-model-2: the write admission is read at every read's recorded
; time, after that read's clock reading and before its step (host/native/
; owner.lisp fnn-owner-handle-chunk: a POST command is answered 440 while the
; disk sheds, a submitted POST 441); the POST's submission appends no clock
; event of its own.  With no time service bound (*fnn-owner-time-service*)
; a reading is the plain monotonic one, so no :served disk event is made.
(check (equal *timeline* '(:observe :observe :admit :observe :admit :observe :admit))
       "each read's admission does not follow its own clock reading: ~s" *timeline*)

(format t "native owner chunk loop: ~d host definitions extracted, ~d declared ~
           unreached; suffix, refusal, no-progress, clock and time-event passed~%"
        (length *extracted*) (length *unreached*))
