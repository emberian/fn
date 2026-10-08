; Commit, log frontier and reader-view composition. Derived native entries.
(in-package "ACL2")
(include-book "owner-reader-view")
(include-book "owner-queued-work")
(include-book "owner-time-held")
(include-book "owner-time-journal")
(include-book "store-log-pipeline")
(local (in-theory
 (disable fn-lgk-pipe-countedp fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-count
          fn-lgk-pipe-kernel-append fn-lgk-pipe-kernel-fence fn-lgk-pipe-kernel-fail
          fn-lgk-pipe-kernel-ack fn-lgk-pipe-kernel-take fn-lgk-pipe-kernel-octets
          fn-lgk-pipe-kernel-fitsp)))

(defun fn-ocp-gc-shapedp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (fn-lgk-pipe-shapedp (nth 0 x))
       (or (natp (nth 3 x)) (true-listp (nth 3 x)))
       (true-listp (nth 6 x)) (true-listp (nth 7 x))))

; Composition fields (one dispatcher; counted projection is proved in
; owner-commit-durability-concrete):
; 0 kernel+bit, 1 existing OTM scheduler, 2 OCVM views, 3 record history/count,
; 4 current job phase, 5 next job phase, 6/7 current/next member outcomes,
; 8 record dependency cuts, 9 releases, 10 unit, 11 extent, 12 BMAX,
; 13 OMAX, 14 append-behind write plan. Member counts are NOT record counts:
; a refusal may depend on earlier records without adding a record of its own.
(defun fn-ocp-gc-profilep (unit extent bmax omax)
  (declare (xargs :guard t :verify-guards nil))
  (and (posp unit) (natp extent) (posp bmax) (natp omax)))
(defun fn-ocp-gc-init (unit extent bmax omax)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-lgk-pipe-make (fn-lgk-make nil (make-list 32 :initial-element 0)
                                     0 1 nil nil 0 :ready) nil)
        (fn-otm-init) (fn-ocvm-init) nil :idle :idle nil nil nil nil
        unit extent bmax omax nil))

; STATE invariant, not an implication from a supplied :fenced observation.
; Phase/frontier coupling must be established initially and preserved by the
; machine below. It is NOT checked as an admission test by any transition.
; Output safety is deliberately not a conjunct: the corollary is over STEP.
(defun fn-ocp-gc-linkedp (x)
  (let* ((p (nth 0 x)) (ks (fn-lgk-pipe-ks p)) (s (nth 1 x)) (m (nth 2 x))
         (phase (nth 4 x)) (np (nth 5 x)) (d (fn-lgk-pipe-d p))
         (c (fn-ocvm-c m)) (a (fn-ocvm-a m)) (b (fn-ocvm-b m)))
    (and (true-listp x) (equal (len x) 15)
         (fn-ocp-gc-profilep (nth 10 x) (nth 11 x) (nth 12 x) (nth 13 x))
         (fn-lgk-pipe-okp p (nth 3 x)) (fn-ocvm-inv m)
         (equal (fn-ocvm-w m) (len (nth 3 x)))
         (true-listp (nth 6 x)) (true-listp (nth 7 x))
         (equal (if (member-eq phase '(:drain :stopped-drain)) a b)
                (len (fn-lgk-batch ks)))
         (member-eq np '(:idle :drain :intents :extend :append :writing :fence))
         (implies (equal np :idle) (equal b 0))
         (implies (not (equal np :idle)) (consp (cdr (fn-ocvm-views m))))
         (equal (fn-otm-next-of s)
                (if (member-eq np '(:intents :extend :append :writing :fence)) t nil))
         (equal (fn-lgk-pipe-behind p)
                (if (and (member-eq np '(:writing :fence)) (posp b)) t nil))
         (cond
          ((equal phase :idle)
           (and (equal (fn-otm-phase-of s) :idle)
                (member-eq (fn-lgk-phase ks) '(:ready :fenced))
                (equal np :idle) (equal a 0) (equal b 0)
                (equal c d) (not (fn-lgk-inflight ks))))
          ((member-eq phase '(:drain :stopped-drain))
           (and (equal (fn-otm-phase-of s)
                       (if (equal phase :drain) :idle :failed))
                (if (equal phase :drain)
                    (member-eq (fn-lgk-phase ks) '(:ready :fenced))
                  (equal (fn-lgk-phase ks) :fault))
                (consp (fn-ocvm-views m)) (not (consp (cdr (fn-ocvm-views m))))
                (equal np :idle) (equal b 0) (equal c d)
                (not (fn-lgk-inflight ks))))
          ((equal phase :stopped)
           (and (equal (fn-otm-phase-of s) :failed)
                (equal (fn-lgk-phase ks) :fault)
                (or (and (equal c d) (equal a (len (fn-lgk-inflight ks))))
                    (and (equal d (+ c a)) (not (fn-lgk-inflight ks))))))
          ((member-eq phase '(:intents :extend :append :fence))
           (and (equal (fn-otm-phase-of s) :staged)
                (consp (fn-ocvm-views m))
                (equal (fn-lgk-phase ks) :appended)
                (equal c d) (equal a (len (fn-lgk-inflight ks)))))
          ((member-eq phase '(:resolutions :done :collected))
           (and (equal (fn-otm-phase-of s)
                       (if (equal phase :collected) :fenced :staged))
                (implies (equal phase :collected) (not (member-eq np '(:drain :writing))))
                (consp (fn-ocvm-views m))
                (equal (fn-lgk-phase ks) :fenced)
                (equal d (+ c a)) (not (fn-lgk-inflight ks))))
          (t nil)))))

; Executable multiple-value projections (ACL2 rejects raw MV-NTH of these
; calls inside DEFUN). Equations in statements.lisp name the direct calls.
(defun fn-ocp-gc-event-action (s e)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (action after) (fn-otm-commit-event s e) (declare (ignore after)) action))
(defun fn-ocp-gc-event-state (s e)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (action after) (fn-otm-commit-event s e) (declare (ignore action)) after))
(defun fn-ocp-gc-pick (s w)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (class after) (fn-otm-next s w) (declare (ignore class)) after))



(defun fn-ocp-gc-stop (x)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (let* ((drainp (member-eq (nth 4 x) '(:drain :stopped-drain)))
         (before (if (equal (nth 4 x) :drain)
                     (fn-ocp-gc-event-state (nth 1 x) :started) (nth 1 x)))
         (action (fn-ocp-gc-event-action before :failed))
         (s (fn-ocp-gc-event-state before :failed))
         (rs (fn-ocs-member-releases action (append (nth 6 x) (nth 7 x)))))
    (update-nth 14 action
     (update-nth 9 rs (update-nth 4 (if drainp :stopped-drain :stopped)
      (update-nth 1 s (update-nth 0 (fn-lgk-pipe-fail (nth 0 x)) x)))))))


; IO step is the RECEIPT of exactly one fn-oqw phase. The next job can run
; through its append but cannot fence until promoted: one sync outstanding.
; Unknown/late events stutter. Failures are sticky, never erased by late OK.
(defun fn-ocp-gc-io (x nextp word)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (let* ((slot (if nextp 5 4)) (phase (nth slot x)) (p (nth 0 x))
         (m (nth 2 x)) (unit (nth 10 x)))
    (if (or (equal (nth 4 x) :collected)
            (not (member-eq phase (if nextp '(:intents :extend :writing)
                                   '(:intents :extend :append :fence :resolutions)))))
        x
      (let ((x (if (and (not nextp) (equal phase :resolutions))
                   (update-nth 8 (list (+ (fn-ocvm-c m) (fn-ocvm-a m))) x) x)))
        (if (not (equal word :ok)) (fn-ocp-gc-stop x)
          (let* ((q (cond ((and (not nextp) (equal phase :fence)) (fn-lgk-pipe-fence p unit))
                         (t p)))
                 (after (if (and nextp (equal phase :writing)) :fence
                          (fn-oqw-step :batch phase word))))
            (update-nth slot after (update-nth 0 q x))))))))

; Issue precedes the write syscall. B is frozen until its receipt; A's
; barrier may return in between, but its durable cut still contains only A.
(defun fn-ocp-gc-append-issue (x)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (let ((p (nth 0 x)) (unit (nth 10 x)) (extent (nth 11 x)))
    (if (not (and (member-eq (nth 4 x) '(:fence :resolutions :done))
                  (equal (nth 5 x) :append))) x
      (if (not (consp (fn-lgk-batch (fn-lgk-pipe-ks p))))
          (update-nth 5 :fence x)
        (if (not (fn-lgk-behind-admitsp p unit extent)) x
          (update-nth 14 (fn-lgk-behind-effect p unit extent)
           (update-nth 5 :writing
            (update-nth 0 (fn-lgk-behind-state p unit extent) x))))))))

(defun fn-ocp-gc-collect (x)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (if (or (not (equal (nth 4 x) :done)) (member-eq (nth 5 x) '(:drain :writing))) x
    (let* ((s (nth 1 x)) (m (nth 2 x))
           (action (fn-ocp-gc-event-action s :fenced)))
      (update-nth 14 action
       (update-nth 6 nil
        (update-nth 9 (fn-ocs-member-releases action (nth 6 x))
       (update-nth 8 (list (+ (fn-ocvm-c m) (fn-ocvm-a m)))
        (update-nth 4 :collected
         (update-nth 1 (fn-ocp-gc-event-state s :fenced)
          (update-nth 0 (fn-lgk-pipe-ack (nth 0 x) (fn-ocvm-a m)) x))))))))))

; Separate entry after COMPLETE's log/reply effects. No I/O lies between
; reader-view advance and the logical promotion/capture it returns.
(defun fn-ocp-gc-finish-event (s)
  (declare (xargs :guard t))
  (if (and (fn-otm-held s) (not (fn-otm-next-of s)))
      (fn-otm-held-event s :completed)
    (fn-otm-commit-event s :completed)))
(defun fn-ocp-gc-finish-action (s)
  (declare (xargs :guard t))
  (mv-let (action after) (fn-ocp-gc-finish-event s) (declare (ignore after)) action))
(defun fn-ocp-gc-finish-state (s)
  (declare (xargs :guard t))
  (mv-let (action after) (fn-ocp-gc-finish-event s) (declare (ignore action)) after))

(defun fn-ocp-gc-advance (x)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (if (or (not (equal (nth 4 x) :collected))
          (member-eq (nth 5 x) '(:drain :writing))
          (and (fn-otm-next-of (nth 1 x)) (not (equal (nth 5 x) :fence)))) x
    (let* ((s (nth 1 x)) (m (nth 2 x)) (unit (nth 10 x)) (extent (nth 11 x))
           (p1 (nth 0 x))
           (ks (fn-lgk-pipe-ks p1)) (nextp (fn-otm-next-of s)))
      ; No partly consumed completion on a refused promotion. Its immutable
      ; capture can wait for an off-owner extent extension before this step.
      (if (and nextp (not (fn-lgc-append-admitsp (fn-lgk-pipe-kernel-view ks) unit extent))) x
        (let ((p2 (if nextp (fn-lgk-pipe-make (fn-lgk-pipe-kernel-append ks unit extent) nil) p1)))
          (list p2 (fn-ocp-gc-finish-state s)
                (fn-ocvm-step m '(:complete)) (nth 3 x)
                (if nextp (nth 5 x) :idle) :idle (if nextp (nth 7 x) nil) nil
                nil nil
                unit extent (nth 12 x) (nth 13 x)
                (fn-ocp-gc-finish-action s)))))))

; The native drain has one reservation/take/outcome at a time. These arms
; are the shared primitives of that quantum, including zero-record members.
; None checks LINKEDP; its preservation is a proof obligation below.
(defun fn-ocp-gc-begin (x nextp)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (if (if nextp
          (and (member-eq (nth 4 x) '(:intents :extend :append :fence :resolutions :done))
               (not (fn-otm-held (nth 1 x)))
               (equal (nth 5 x) :idle) (not (fn-otm-next-of (nth 1 x))))
        (equal (nth 4 x) :idle))
      (update-nth (if nextp 7 6) nil
       (update-nth (if nextp 5 4) :drain
        (update-nth 2
          (fn-ocvm-step (if nextp (nth 2 x) (fn-ocvm-step (nth 2 x) '(:drop)))
                        (list (if nextp :next :start) 0)) x)))
    x))
(defun fn-ocp-gc-reserve (x nextp txid)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (if (equal (nth (if nextp 5 4) x) :drain)
      (update-nth 0 (fn-lgk-pipe-consume (nth 0 x) txid) x) x))
(defun fn-ocp-gc-take (x nextp record txid)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (if (not (equal (nth (if nextp 5 4) x) :drain)) x
    (let* ((p (nth 0 x)) (ks (fn-lgk-pipe-ks p)) (m (nth 2 x))
           (answer (fn-lgk-pipe-take p record txid
                      (len (fn-lgk-batch ks)) (fn-lg-pack-len (fn-lgk-batch ks))
                      (nth 12 x) (nth 13 x) (nth 10 x)))
           (out (list :take (car answer) (caddr answer)))
           (x (update-nth 14 out x)))
      (if (not (equal (car answer) :taken)) x
        (update-nth 3 (fn-ocp-gc-history-extend (nth 3 x) (list record))
         (update-nth 2
           (fn-ocvm-make (+ 1 (fn-ocvm-w m)) (fn-ocvm-c m)
                         (if nextp (fn-ocvm-a m) (+ 1 (fn-ocvm-a m)))
                         (if nextp (+ 1 (fn-ocvm-b m)) (fn-ocvm-b m))
                         (fn-ocvm-views m))
           (update-nth 0 (cadr answer) x)))))))
(defun fn-ocp-gc-member (x nextp outcome)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (if (not (equal (nth (if nextp 5 4) x) :drain)) x
    (update-nth (if nextp 7 6) (append (nth (if nextp 7 6) x) (list outcome)) x)))

; Pre-extend current's job for its append AND one next profile-sized append.
; This decision precedes I/O; next cannot issue a write before current's
; extend/append receipts. No second extension barrier is needed behind it.
(defun fn-ocp-gc-seal-extent (x)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (let* ((ks (fn-lgk-pipe-ks (nth 0 x))) (unit (nth 10 x))
         (extent (nfix (nth 11 x)))
         (need (+ (fn-lgk-frontier ks)
                  (fn-lgc-append-len (fn-lgk-pipe-kernel-view ks) unit)
                  (nfix (nth 13 x)) (nfix unit))))
    (if (<= need extent) extent (fn-olr-next-extent extent need unit))))
(defun fn-ocp-gc-seal (x nextp frames)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (if (not (equal (nth (if nextp 5 4) x) :drain)) x
    (let* ((p (nth 0 x)) (ks (fn-lgk-pipe-ks p)) (m (nth 2 x))
           (members (nth (if nextp 7 6) x)) (unit (nth 10 x)))
      (if (and (not frames) (not (consp members)) (not (consp (fn-lgk-batch ks))))
          (update-nth 14
           (list :seal nil nil
                 (fn-ocp-gc-event-action (nth 1 x) (if nextp :next-none :started-none))
                 (if nextp :unnext :drop))
           (update-nth (if nextp 5 4) :idle
            (update-nth 2 (fn-ocvm-step m (list (if nextp :unnext :drop))) x)))
        (if nextp
            (update-nth 14 (list :seal nil nil (fn-ocp-gc-event-action (nth 1 x) :next-started) nil)
             (update-nth 5 (fn-oqw-start :batch)
              (update-nth 1 (fn-ocp-gc-event-state (nth 1 x) :next-started) x)))
          (let ((extent (fn-ocp-gc-seal-extent x)))
            (if (not (fn-lgc-append-admitsp (fn-lgk-pipe-kernel-view ks) unit extent)) x
              (update-nth 14
                (list :seal
                      (if (equal extent (nth 11 x)) nil (cons extent (nth 11 x)))
                      (if (consp (fn-lgk-batch ks))
                          (list :write (fn-lgk-frontier ks) (fn-lgk-pipe-kernel-octets ks unit)) nil)
                      (fn-ocp-gc-event-action (nth 1 x) :started) nil)
               (update-nth 11 extent
                (update-nth 4 (fn-oqw-start :batch)
                 (update-nth 1 (fn-ocp-gc-event-state (nth 1 x) :started)
                  (update-nth 0 (fn-lgk-pipe-make (fn-lgk-pipe-kernel-append ks unit extent) nil) x))))))))))))

(defun fn-ocp-gc-seal-held (x frames)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (if (or (not (equal (nth 4 x) :drain)) (fn-otm-held (nth 1 x))) x
    (let* ((y (fn-ocp-gc-seal x nil frames))
           (event (case (nth 4 y) (:intents :started-held) (:idle :started-none-held))))
      (if (not event) y
        (mv-let (action s) (fn-otm-held-event (nth 1 x) event)
          (update-nth 14 (list :held action (nth 14 y)) (update-nth 1 s y)))))))

(defun fn-ocp-gc-gate (x event)
  (declare (xargs :guard (and (fn-ocp-gc-shapedp x) (true-listp event)) :verify-guards nil))
  (let ((s (nth 1 x)))
    (case (car event)
      (:pick (mv-let (class next) (fn-otm-next s (nth 1 event))
               (update-nth 14 class (update-nth 1 next x))))
      (:observe (update-nth 1 (fn-otm-observe s (nth 1 event) (nth 2 event) (nth 3 event)) x))
      (:disk (let ((r (fn-otm-disk-step s (nth 1 event) (nth 2 event) (nth 3 event))))
               (update-nth 14 r (update-nth 1 (cadr r) x))))
      (:note (let ((r (fn-otm-note-step s (nth 1 event) (nth 2 event))))
               (update-nth 14 r (update-nth 1 (car r) x))))
      (otherwise x))))

(defun fn-ocp-gc-close (x stopping)
  (declare (xargs :guard (true-listp x)))
  ; Return the scheduler for the detached boundary, retaining the terminal
  ; durability evidence in X. A failed Store can detach only after its
  ; external service fence is installed; it never resumes semantic work.
  (cond ((equal (nth 4 x) :idle)
         (update-nth 14 (list :closed (nth 1 x) :none) x))
        ((and stopping (member-eq (nth 4 x) '(:collected :stopped :stopped-drain)))
         (mv-let (action after)
             (fn-otm-held-event (nth 1 x)
                               (if (equal (nth 4 x) :collected) :completed-stopping :completed))
           (update-nth 14 (list :closed after action) x)))
        (t x)))

(defun fn-ocp-gc-host-step (x event)
  (declare (xargs :guard (and (fn-ocp-gc-shapedp x) (true-listp event)) :verify-guards nil))
  (let* ((x (update-nth 14 nil (update-nth 9 nil (update-nth 8 nil x))))
         (kind (car event)))
    (if (equal kind :close) (fn-ocp-gc-close x (nth 1 event))
     (if (member-eq kind '(:pick :observe :disk :note)) (fn-ocp-gc-gate x event)
     (if (member-eq (nth 4 x) '(:stopped :stopped-drain))
         (if (equal kind :collect)
             (update-nth 14 (fn-ocp-gc-event-action (nth 1 x) :failed) x) x)
      (case kind
        (:start (fn-ocp-gc-begin x nil))
        (:next (fn-ocp-gc-begin x t))
        (:begin (fn-ocp-gc-begin x (equal (nth 1 event) :next)))
        (:reserve (fn-ocp-gc-reserve x (equal (nth 1 event) :next) (nth 2 event)))
        (:take (fn-ocp-gc-take x (equal (nth 1 event) :next) (nth 2 event) (nth 3 event)))
        (:member (fn-ocp-gc-member x (equal (nth 1 event) :next) (nth 2 event)))
        (:seal (fn-ocp-gc-seal x (equal (nth 1 event) :next) nil))
        (:seal-held (fn-ocp-gc-seal-held x (nth 1 event)))
        (:append-issue (fn-ocp-gc-append-issue x))
        ;; A physical actor can fail before delivering a phase receipt too.
        ;; Its collector fences the same machine; no synthetic OK is needed.
        (:abort (if (member-eq (nth 4 x) '(:idle :collected :stopped)) x
                  (fn-ocp-gc-stop x)))
        (:io (fn-ocp-gc-io x (equal (nth 1 event) :next) (nth 2 event)))
        (:collect (fn-ocp-gc-collect x))
        (:advance (fn-ocp-gc-advance x))
        (:reader (update-nth 8 (list (fn-ocv-reader-view (fn-ocvm-views (nth 2 x))
                                                       (fn-ocvm-w (nth 2 x)))) x))
        (otherwise x)))))))

; Derived ACL2 entries. Native entry points install the returned core state
; and execute its output fields; they must not recompute any arm's decision.
(defun fn-ocp-gc-entry-close (x stopping)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :close stopping)))
(defthm fn-ocp-gc-entry-close-by-definition
  (equal (fn-ocp-gc-entry-close x stopping) (fn-ocp-gc-host-step x (list :close stopping))))
(defun fn-ocp-gc-entry-seal-held (x frames)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :seal-held frames)))
(defthm fn-ocp-gc-entry-seal-held-by-definition
  (equal (fn-ocp-gc-entry-seal-held x frames) (fn-ocp-gc-host-step x (list :seal-held frames))))

(defun fn-ocp-gc-entry-start (x)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x '(:start)))
(defun fn-ocp-gc-entry-start-next (x)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x '(:next)))
(defun fn-ocp-gc-entry-complete (x)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x '(:collect)))
(defun fn-ocp-gc-entry-syncer (x which word)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :io which word)))
(defun fn-ocp-gc-entry-reader-advance (x)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x '(:advance)))
(defun fn-ocp-gc-entry-append-issue (x)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x '(:append-issue)))
(defthm fn-ocp-gc-entry-append-issue-by-definition
  (equal (fn-ocp-gc-entry-append-issue x)
         (fn-ocp-gc-host-step x '(:append-issue))))
(defun fn-ocp-gc-entry-begin (x which)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :begin which)))
(defthm fn-ocp-gc-entry-begin-by-definition
  (equal (fn-ocp-gc-entry-begin x which)
         (fn-ocp-gc-host-step x (list :begin which))))
(defun fn-ocp-gc-entry-reserve (x which txid)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :reserve which txid)))
(defthm fn-ocp-gc-entry-reserve-by-definition
  (equal (fn-ocp-gc-entry-reserve x which txid)
         (fn-ocp-gc-host-step x (list :reserve which txid))))
(defun fn-ocp-gc-entry-take (x which record txid)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :take which record txid)))
(defthm fn-ocp-gc-entry-take-by-definition
  (equal (fn-ocp-gc-entry-take x which record txid)
         (fn-ocp-gc-host-step x (list :take which record txid))))
(defun fn-ocp-gc-entry-member (x which outcome)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :member which outcome)))
(defthm fn-ocp-gc-entry-member-by-definition
  (equal (fn-ocp-gc-entry-member x which outcome)
         (fn-ocp-gc-host-step x (list :member which outcome))))
(defun fn-ocp-gc-entry-seal (x which)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :seal which)))
(defthm fn-ocp-gc-entry-seal-by-definition
  (equal (fn-ocp-gc-entry-seal x which)
         (fn-ocp-gc-host-step x (list :seal which))))
(defun fn-ocp-gc-entry-abort (x which)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :abort which)))
(defthm fn-ocp-gc-entry-abort-by-definition
  (equal (fn-ocp-gc-entry-abort x which)
         (fn-ocp-gc-host-step x (list :abort which))))

(defun fn-ocp-gc-entry-pick (x waiting)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :pick waiting)))
(defthm fn-ocp-gc-entry-pick-by-definition
  (equal (fn-ocp-gc-entry-pick x waiting)
         (fn-ocp-gc-host-step x (list :pick waiting))))
(defun fn-ocp-gc-entry-observe (x class hold wait)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :observe class hold wait)))
(defthm fn-ocp-gc-entry-observe-by-definition
  (equal (fn-ocp-gc-entry-observe x class hold wait)
         (fn-ocp-gc-host-step x (list :observe class hold wait))))
(defun fn-ocp-gc-entry-disk (x kind reading arg)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :disk kind reading arg)))
(defthm fn-ocp-gc-entry-disk-by-definition
  (equal (fn-ocp-gc-entry-disk x kind reading arg)
         (fn-ocp-gc-host-step x (list :disk kind reading arg))))
(defun fn-ocp-gc-entry-note (x a b)
  (declare (xargs :guard (fn-ocp-gc-shapedp x) :verify-guards nil))
  (fn-ocp-gc-host-step x (list :note a b)))
(defthm fn-ocp-gc-entry-note-by-definition
  (equal (fn-ocp-gc-entry-note x a b)
         (fn-ocp-gc-host-step x (list :note a b))))

(defun fn-ocp-gc-run (x events)
  (declare (xargs :measure (len events)))
  (if (atom events) x (fn-ocp-gc-run (fn-ocp-gc-host-step x (car events)) (cdr events))))
(defun fn-ocv-gc-prefix-durablep (h p cut)
  (and (natp cut) (<= cut (fn-lgk-pipe-d p))
       (fn-lg-prefixp (take cut h) (fn-lgk-committed (fn-lgk-pipe-ks p)))))
(defun fn-ocp-gc-cuts-okp (h p cuts)
  (if (atom cuts) t
    (and (fn-ocv-gc-prefix-durablep h p (car cuts)) (fn-ocp-gc-cuts-okp h p (cdr cuts)))))
(defun fn-ocp-gc-reveals-okp (x)
  (fn-ocp-gc-cuts-okp (nth 3 x) (nth 0 x) (nth 8 x)))

; Failure statement includes the actual current job's :fence receipt, both
; batches, and an arbitrary post-stop event suffix: no late receipt can ACK.
(defun fn-ocp-gc-failure-hyp (x)
  (and (fn-ocp-gc-linkedp x) (equal (nth 4 x) :fence)
       (consp (nth 6 x)) (consp (nth 7 x))))
(defun fn-ocp-gc-failure-okp (x events)
  (let* ((y (fn-ocp-gc-host-step x '(:io :current :uncertain)))
         (z (fn-ocp-gc-run y events)))
    (and (equal (nth 4 y) :stopped) (equal (nth 4 z) :stopped)
         (equal (fn-lgk-phase (fn-lgk-pipe-ks (nth 0 z))) :fault)
         (equal (fn-lgk-pipe-d (nth 0 z)) (fn-lgk-pipe-d (nth 0 x)))
         (equal (fn-lgk-pipe-acked (nth 0 z)) (fn-lgk-pipe-acked (nth 0 x)))
         (<= (fn-lgk-pipe-acked (nth 0 z)) (fn-lgk-pipe-d (nth 0 x)))
         (equal (len (nth 9 y)) (+ (len (nth 6 x)) (len (nth 7 x))))
         (subsetp-equal (nth 9 y) '(:own-uncertain :uncertain-reply :close)))))




; Derived entries: no implementation twin, no hypothesis.
(defthm fn-ocp-gc-entry-start-by-definition
  (equal (fn-ocp-gc-entry-start x)
         (fn-ocp-gc-host-step x '(:start))))
(defthm fn-ocp-gc-entry-start-next-by-definition
  (equal (fn-ocp-gc-entry-start-next x)
         (fn-ocp-gc-host-step x '(:next))))
(defthm fn-ocp-gc-entry-complete-by-definition
  (equal (fn-ocp-gc-entry-complete x) (fn-ocp-gc-host-step x '(:collect))))
(defthm fn-ocp-gc-entry-syncer-by-definition
  (equal (fn-ocp-gc-entry-syncer x which word)
         (fn-ocp-gc-host-step x (list :io which word))))
(defthm fn-ocp-gc-entry-reader-advance-by-definition
  (equal (fn-ocp-gc-entry-reader-advance x) (fn-ocp-gc-host-step x '(:advance))))
(local (in-theory
 (disable (tau-system) nth len true-listp update-nth
          fn-lgk-pipe-okp fn-lgk-pipe-ks fn-lgk-pipe-behind fn-lgk-pipe-d
          fn-lgk-pipe-acked fn-lgk-pipe-fence fn-lgk-pipe-fail fn-lgk-pipe-ack
          fn-lgk-behind-state fn-lgk-behind-effect fn-lgk-behind-admitsp
          fn-lgk-phase fn-lgk-batch fn-lgk-inflight fn-lgk-committed fn-lgk-acked
          fn-lgk-last fn-lgk-append fn-lgc-append-admitsp fn-olr-gc-prepare
          fn-ocp-gc-linkedp fn-ocp-gc-profilep  fn-ocp-gc-io
          fn-ocp-gc-stop fn-ocp-gc-collect fn-ocp-gc-advance fn-ocp-gc-host-step
          fn-ocp-gc-event-state fn-ocp-gc-event-action fn-ocp-gc-pick
          fn-ocp-gc-finish-state fn-ocp-gc-finish-action fn-ocp-gc-finish-event
          fn-ocp-open-next fn-ocp-ocs fn-ocs-phase fn-otm-phase-of fn-otm-next-of
          fn-otm-ocp fn-otm-held fn-otm-held-event fn-ocvm-inv fn-ocvm-w
          fn-ocvm-c fn-ocvm-a fn-ocvm-b fn-ocvm-views fn-ocvm-step
          fn-oqw-step fn-oqw-start fn-ocp-gc-reveals-okp fn-ocp-gc-cuts-okp
          fn-ocv-gc-prefix-durablep fn-ocv-reader-view)))

(local (defthm fn-ocp-gc-seal-extent-natp
  (natp (fn-ocp-gc-seal-extent x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-ocp-gc-seal-extent fn-olr-next-extent)))))
; Guard obligations describe only representation shape. LINKEDP is carried
; by preservation and is never revalidated by the served entry.
(verify-guards fn-ocp-gc-profilep)
(verify-guards fn-ocp-gc-init)
(verify-guards fn-ocp-gc-event-action)
(verify-guards fn-ocp-gc-event-state)
(verify-guards fn-ocp-gc-pick)
(verify-guards fn-ocp-gc-stop :hints (("Goal" :in-theory (enable fn-ocp-gc-shapedp))))

(verify-guards fn-ocp-gc-io
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-append-issue
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-collect
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-advance
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-begin
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-reserve
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-take
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-member
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-seal-extent
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-seal
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-gate
  :hints (("Goal" :in-theory (enable fn-ocp-gc-shapedp nth))))
(verify-guards fn-ocp-gc-seal-held
 :hints (("Goal" :in-theory (enable fn-ocp-gc-seal fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks nth))))
(verify-guards fn-ocp-gc-host-step
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-start
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-start-next
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-complete
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-syncer
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-reader-advance
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-append-issue
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-begin
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-reserve
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-take
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-member
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-seal
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-abort
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-pick
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-observe
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-disk
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))
(verify-guards fn-ocp-gc-entry-note
  :hints (("Goal" :in-theory
           (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks
                   fn-lgk-pipe-kernel-view nth))))

(verify-guards fn-ocp-gc-entry-seal-held
 :hints (("Goal" :in-theory (enable fn-ocp-gc-shapedp fn-lgk-pipe-shapedp fn-lgk-pipe-ks nth))))
(verify-guards fn-ocp-gc-entry-close
 :hints (("Goal" :in-theory (enable fn-ocp-gc-shapedp))))
