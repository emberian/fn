; Bounded catchup spool controller. Fixed metadata, one input/output window;
; no record index, article line list or complete IHAVE body is retained.
;
; THE OFFER WINDOW (PRF-1335/1336): one transit connection is structurally
; one record in flight (a 335 cannot be rendered before the previous verdict,
; and the body cannot precede its 335), so catch-up pace is bounded by ONE
; IHAVE outstanding x the commit barrier.  The controller therefore offers
; through a WINDOW of W logical transit connections of the same peer (W the
; begin's argument, read by the host from the operator's log-batch-records:
; the controller never offers more ahead than the committer would place in
; one batch), each running the unchanged one-record-at-a-time IHAVE flow.
; The spool cursor stays sequential: one FILLING record reads the spool
; (header, then body windows, then its terminator) while earlier records
; await their verdicts on other connections.  Verdicts are keyed to record
; identity, not order: the binding (conn j <-> msgid) is created when the
; IHAVE for msgid is emitted on j and consumed exactly once, by the first
; reply on j that settles that record; a reply on j in any other conn state
; is a local protocol violation (:local-refused).  Retained per slot: one
; Message-ID; at most W of them (the window keystone's claim extended).
(in-package "ACL2")
(include-book "peer-catchup")
(include-book "peer-catchup-spool-framer")

(defmacro fn-csp-with (s &key
                         (mode 'nil mode-p)
                         (session 'nil session-p)
                         (header 'nil header-p)
                         (crp 'nil crp-p)
                         (framer 'nil framer-p)
                         (offset 'nil offset-p)
                         (start 'nil start-p)
                         (msgid 'nil msgid-p)
                         (chain 'nil chain-p)
                         (batch 'nil batch-p)
                         (pending 'nil pending-p)
                         (replay 'nil replay-p)
                         (limit 'nil limit-p)
                         (count 'nil count-p)
                         (resume 'nil resume-p)
                         (verified 'nil verified-p)
                         (skip 'nil skip-p)
                         (window 'nil window-p)
                         (conns 'nil conns-p)
                         (slot 'nil slot-p))
  `(list
     ,(if mode-p mode `(fn-pull-at 0 ,s))
     ,(if session-p session `(fn-pull-at 1 ,s))
     ,(if header-p header `(fn-pull-at 2 ,s))
     ,(if crp-p crp `(fn-pull-at 3 ,s))
     ,(if framer-p framer `(fn-pull-at 4 ,s))
     ,(if offset-p offset `(fn-pull-at 5 ,s))
     ,(if start-p start `(fn-pull-at 6 ,s))
     ,(if msgid-p msgid `(fn-pull-at 7 ,s))
     ,(if chain-p chain `(fn-pull-at 8 ,s))
     ,(if batch-p batch `(fn-pull-at 9 ,s))
     ,(if pending-p pending `(fn-pull-at 10 ,s))
     ,(if replay-p replay `(fn-pull-at 11 ,s))
     ,(if limit-p limit `(fn-pull-at 12 ,s))
     ,(if count-p count `(fn-pull-at 13 ,s))
     ,(if resume-p resume `(fn-pull-at 14 ,s))
     ,(if verified-p verified `(fn-pull-at 15 ,s))
     ,(if skip-p skip `(fn-pull-at 16 ,s))
     ,(if window-p window `(fn-pull-at 17 ,s))
     ,(if conns-p conns `(fn-pull-at 18 ,s))
     ,(if slot-p slot `(fn-pull-at 19 ,s))))

(defun fn-csp-mode (s) (declare (xargs :guard t)) (fn-pull-at 0 s))
(defun fn-csp-session (s) (declare (xargs :guard t)) (fn-pull-at 1 s))
(defun fn-csp-header (s) (declare (xargs :guard t)) (fn-pull-at 2 s))
(defun fn-csp-crp (s) (declare (xargs :guard t)) (fn-pull-at 3 s))
(defun fn-csp-body-framer (s) (declare (xargs :guard t)) (fn-pull-at 4 s))
(defun fn-csp-offset (s) (declare (xargs :guard t)) (fn-pull-at 5 s))
(defun fn-csp-start (s) (declare (xargs :guard t)) (fn-pull-at 6 s))
(defun fn-csp-msgid (s) (declare (xargs :guard t)) (fn-pull-at 7 s))
(defun fn-csp-chain (s) (declare (xargs :guard t)) (fn-pull-at 8 s))
(defun fn-csp-batch (s) (declare (xargs :guard t)) (fn-pull-at 9 s))
(defun fn-csp-pending (s) (declare (xargs :guard t)) (fn-pull-at 10 s))
(defun fn-csp-replay (s) (declare (xargs :guard t)) (fn-pull-at 11 s))
(defun fn-csp-limit (s) (declare (xargs :guard t)) (fn-pull-at 12 s))
(defun fn-csp-count (s) (declare (xargs :guard t)) (fn-pull-at 13 s))
(defun fn-csp-resume (s) (declare (xargs :guard t)) (fn-pull-at 14 s))
(defun fn-csp-verified (s) (declare (xargs :guard t)) (fn-pull-at 15 s))
(defun fn-csp-skip (s) (declare (xargs :guard t)) (fn-pull-at 16 s))
(defun fn-csp-window (s) (declare (xargs :guard t)) (fn-pull-at 17 s))
(defun fn-csp-conns (s) (declare (xargs :guard t)) (fn-pull-at 18 s))
(defun fn-csp-slot (s) (declare (xargs :guard t)) (fn-pull-at 19 s))

; -----------------------------------------------------------------------------
; The connection window
;
; One entry per logical transit connection j of the flight's peer:
;   :unopened            never opened
;   :opening             (:open-local j) emitted, its greeting awaited
;   :free                greeted (200/201), carrying nothing
;   (msgid . :await335)  IHAVE sent for msgid on j, awaiting the 335
;   (msgid . :streaming) the filling record: 335 seen, its body windows or
;                        terminator are being written on j (at most one
;                        streaming slot -- the spool cursor is sequential)
;   (msgid . :verdict)   terminator written, awaiting 235/435/437 on j.
; The binding (j <-> msgid) is created only by the IHAVE effect and consumed
; only once, by the first reply on j that settles the record.

(defun fn-csp-connp (c)
  (declare (xargs :guard t))
  (or (member-eq c '(:unopened :opening :free))
      (and (consp c) (fn-pull-msgidp (car c))
           (member-eq (cdr c) '(:await335 :streaming :verdict)))))

(defun fn-csp-connsp (conns)
  (declare (xargs :guard t))
  (if (atom conns) t
    (and (fn-csp-connp (car conns)) (fn-csp-connsp (cdr conns)))))

(defun fn-csp-conn (j s)
  (declare (xargs :guard (natp j)))
  (fn-pull-at (nfix j) (fn-csp-conns s)))

(defun fn-csp-conns-set (conns j c)
  ; UPDATE-NTH's placement without its true-listp guard demand (the conns of
  ; a real state are a true-list, FN-CSP-INV below): past the end this pads
  ; with nil exactly as UPDATE-NTH does, so its placement lemmas carry over.
  (declare (xargs :guard (natp j)))
  (if (zp j)
      (if (consp conns) (cons c (cdr conns)) (list c))
    (if (consp conns)
        (cons (car conns) (fn-csp-conns-set (cdr conns) (1- j) c))
      (cons nil (fn-csp-conns-set nil (1- j) c)))))

(defun fn-csp-conns-idlep (conns)
  ; No (msgid . phase) binding: every offered record settled.
  (declare (xargs :guard t))
  (if (atom conns) t
    (and (not (consp (car conns))) (fn-csp-conns-idlep (cdr conns)))))

(defun fn-csp-conns-idlep-but (conns j)
  ; Every bound entry except j's is settled: idleness of the conns with j
  ; freed, read directly off the pre-state (same recursion as CONNS-SET).
  (declare (xargs :guard (natp j)))
  (cond ((atom conns) t)
        ((zp j) (fn-csp-conns-idlep (cdr conns)))
        (t (and (not (consp (car conns)))
                (fn-csp-conns-idlep-but (cdr conns) (1- j))))))

(defun fn-csp-conns-fullp (conns)
  ; No connection a held record could take or open.
  (declare (xargs :guard t))
  (if (atom conns) t
    (and (not (member-eq (car conns) '(:free :unopened)))
         (fn-csp-conns-fullp (cdr conns)))))

(defun fn-csp-free-conn (conns j)
  ; The lowest :free index, or nil.
  (declare (xargs :guard t))
  (cond ((atom conns) nil)
        ((eq (car conns) :free) (nfix j))
        (t (fn-csp-free-conn (cdr conns) (+ 1 (nfix j))))))

(defun fn-csp-unopened-conn (conns j)
  ; The lowest :unopened index, or nil.
  (declare (xargs :guard t))
  (cond ((atom conns) nil)
        ((eq (car conns) :unopened) (nfix j))
        (t (fn-csp-unopened-conn (cdr conns) (+ 1 (nfix j))))))

(defun fn-csp-conns-phase-count (conns phase)
  (declare (xargs :guard (symbolp phase)))
  (if (atom conns) 0
    (+ (if (and (consp (car conns)) (eq (cdr (car conns)) phase)) 1 0)
       (fn-csp-conns-phase-count (cdr conns) phase))))

(defun fn-csp-conns-of (n c)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons c (fn-csp-conns-of (- n 1) c))))

(defun fn-csp-session-with-round (s r)
  (declare (xargs :guard t))
  (let ((session (fn-csp-session s)))
    (fn-csp-with s :session (fn-cu-session (fn-cu-s-fc session) r
                               (fn-cu-s-refusal session) (fn-cu-s-security session)))))

(defun fn-csp-fail (s reason)
  ; The round ends: the window is dead (the host closes every connection of
  ; the flight on the :close effect); no binding outlives the round.
  (declare (xargs :guard t))
  (mv-let (round effects) (fn-cu-fail (fn-cu-s-round (fn-csp-session s)) reason)
    (list (fn-csp-with (fn-csp-session-with-round s round)
                      :mode :failed :pending nil :header nil :slot nil
                      :conns (fn-csp-conns-of (nfix (fn-csp-window s)) :free))
          effects)))

(defun fn-csp-header-window (rev crp input fuel used count)
  ; Maximum512 content bytes, framed once. A pending CR is one scalar.
  (declare (xargs :guard (and (true-listp rev) (natp fuel) (natp used) (natp count))
                  :measure (nfix fuel) :verify-guards nil))
  (cond ((zp fuel) (list :yield rev crp input used))
        ((atom input) (list :need rev crp nil used))
        ((and crp (equal (car input) 10))
         (list :line (revappend rev nil) nil (cdr input) (1+ used)))
        (t
         (let* ((next-rev (if crp (cons 13 rev) rev))
                (cr2 (equal (car input) 13))
                (next-rev (if cr2 next-rev (cons (car input) next-rev))))
           (if (< 512 (+ count (if crp 1 0) (if cr2 0 1))) (list :refused rev crp input used)
             (fn-csp-header-window next-rev cr2 (cdr input) (1- fuel) (1+ used)
                                   (+ count (if crp 1 0) (if cr2 0 1))))))))
(verify-guards fn-csp-header-window)

(defun fn-csp-write (s emission resume)
  (declare (xargs :guard t))
  (let* ((bytes (fn-pull-list emission))
         (admit (fn-csp-append-admit (fn-csp-offset s) (fn-csp-limit s) bytes)))
    (if (not (eq (car admit) :write)) (fn-csp-fail s :spool-quota)
      (if (atom bytes) (list (fn-csp-with s :mode resume) nil)
        (list (fn-csp-with s :mode :write :resume resume
                          :offset (caddr admit) :count (len bytes))
              (list (list :spool-write (cadr admit) bytes)))))))

(defun fn-csp-hash-effect (s)
  (declare (xargs :guard t))
  (list s (list (list :spool-hash (nfix (fn-csp-start s))
                               (nfix (- (nfix (fn-csp-offset s))
                                        (nfix (fn-csp-start s))))))))

; A status line that is not a batch: why the peer refused, by name.
(defun fn-csp-status-refusal (line)
  (declare (xargs :guard t))
  (let ((code (fn-pull-code line)))
    (cond ((equal code 423) :position-past-end)
          ((equal code 480) :authentication-required)
          ((equal code 501) :peer-refused-syntax)
          ((equal code 500) :peer-lacks-catch-up)
          (t :peer-refused))))

(defun fn-csp-try-offer (s)
  ; The parsed record at the cursor meets the connection window: bind the
  ; lowest :free connection and offer it, or open the lowest :unopened one,
  ; or (every connection bound or opening) the record holds -- a pure wait:
  ; no tick is owed while it can do nothing.
  (declare (xargs :guard t))
  (let* ((conns (fn-csp-conns s))
         (j (fn-csp-free-conn conns 0)))
    (cond
     (j (list (fn-csp-with s :mode :offer :slot j
                           :conns (fn-csp-conns-set conns j
                                                     (cons (fn-csp-msgid s) :await335)))
              (list (list* :local j (fn-cu-ihave (cons (fn-csp-msgid s) nil))))))
     (t (let ((k (fn-csp-unopened-conn conns 0)))
          (if k
              (list (fn-csp-with s :mode :held :slot nil
                                  :conns (fn-csp-conns-set conns k :opening))
                    (list (list :open-local k)))
            (list (fn-csp-with s :mode :held :slot nil) nil)))))))

(defun fn-csp-after-header (s line rest used)
  (declare (xargs :guard (natp used)))
  (let* ((mode (fn-csp-mode s))
         (s (fn-csp-with s :header nil :crp nil :pending rest
                          :replay (if (eq mode :replay-header)
                                      (+ (nfix (fn-csp-replay s)) used) (fn-csp-replay s)))))
    (cond
     ((eq mode :status)
      (let ((batch (fn-cu-parse-status line)))
        (if (not batch) (fn-csp-fail s (fn-csp-status-refusal line))
          (let* ((round (fn-cu-s-round (fn-csp-session s)))
                 (s (fn-csp-session-with-round s (fn-cu-with round :batch batch :end (fn-cu-batch-end batch)))))
            (list (fn-csp-with s :mode :header :batch batch :offset 0
                              :chain (fn-cu-r-chain round) :verified nil) nil)))))
     ((and (eq mode :header) (equal line '(46)))
      (let* ((b (fn-csp-batch s)) (next (fn-cu-batch-next b)) (end (fn-cu-batch-end b))
             (round (fn-cu-s-round (fn-csp-session s)))
             (position (nfix (fn-cu-r-position round))))
        (cond ((consp rest) (fn-csp-fail s :malformed))
              ((not (and (natp next) (natp end) (<= next end)
                         (equal (fn-cu-batch-morep b) (< next end))))
               (fn-csp-fail s :malformed))
              ((not (or (< position next) (and (equal position next) (equal next end))))
               (fn-csp-fail s :no-progress))
              ((not (equal (fn-csp-chain s) (fn-cu-batch-claim b)))
               (fn-csp-fail s :digest-mismatch))
              ((not (fn-cu-r-localp round))
               (list (fn-csp-with
                      (fn-csp-session-with-round s (fn-cu-with round :localp t))
                      :mode :replay-header :verified t :replay 0 :pending nil
                      :conns (fn-csp-conns-set (fn-csp-conns s) 0 :opening))
                     '((:open-local 0))))
              (t (list (fn-csp-with s :mode :replay-header :verified t :replay 0 :pending nil) nil)))))
     (t
      (let ((header (fn-cu-parse-header line)))
        (if (not header) (fn-csp-fail s :malformed)
          (if (eq mode :replay-header)
              (if (not (fn-csp-verified s)) (fn-csp-fail s :unverified)
                (fn-csp-try-offer
                 (fn-csp-with s :msgid (car header)
                              :framer (fn-csp-framer (cdr header) nil) :skip nil)))
            (let* ((bytes (append '(82 32) (fn-pull-list (car header)) '(32)
                                  (fn-cu-u64-hex (cdr header)) '(13 10)))
                   (s (fn-csp-with s :framer (fn-csp-framer (cdr header) t)
                                    :msgid (car header)
                                    :start (+ (nfix (fn-csp-offset s)) (len bytes)))))
              (fn-csp-write s bytes (if (zp (cdr header)) :hash :body))))))))))

(defun fn-csp-batch-finish (s)
  (declare (xargs :guard t))
  (let ((round (fn-cu-s-round (fn-csp-session s))))
    (mv-let (next effects) (fn-cu-next (fn-cu-with round :todo nil))
      (list (fn-csp-with (fn-csp-session-with-round s next)
                        :mode (if (eq (fn-cu-r-phase next) :done) :done :status)
                        :offset 0 :replay 0 :verified nil :batch nil :pending nil)
            effects))))

(defun fn-csp-record-done (s)
  ; One record is complete at the spool cursor: read the next header, or (the
  ; spool exhausted) wait for the batch's outstanding verdicts, or (every
  ; record settled) journal the batch's cursor and ask the next.  The cursor
  ; journals ONLY at this boundary, never mid-record.
  (declare (xargs :guard t))
  (let ((s (fn-csp-with s :slot nil :skip nil :framer nil :msgid nil)))
    (if (< (nfix (fn-csp-replay s)) (nfix (fn-csp-offset s)))
        (list (fn-csp-with s :mode :replay-header) nil)
      (if (fn-csp-conns-idlep (fn-csp-conns s))
          (fn-csp-batch-finish s)
        (list (fn-csp-with s :mode :drain) nil)))))

(defun fn-csp-read-replay (s)
  (declare (xargs :guard t))
  (let* ((position (nfix (fn-csp-replay s))) (end (nfix (fn-csp-offset s)))
         (count (min 512 (nfix (- end position)))))
    (if (zp count)
        (if (and (eq (fn-csp-mode s) :replay-header) (not (consp (fn-csp-header s)))
                 (not (fn-csp-crp s)))
            (fn-csp-record-done s)
          (fn-csp-fail s :short-spool))
      (list (fn-csp-with s :count count)
            (list (list :spool-read position count))))))

(defun fn-csp-next (s)
  ; One bounded controller quantum. Returned tails resume after I/O/work draw.
  (declare (xargs :guard t))
  (let ((mode (fn-csp-mode s)) (pending (fn-pull-list (fn-csp-pending s))))
    (cond
     ((member-eq mode '(:status :header :replay-header))
      (if (atom pending)
          (if (eq mode :replay-header) (fn-csp-read-replay s) (list s nil))
        (let* ((line (fn-csp-header-window (fn-pull-list (fn-csp-header s))
                                           (fn-csp-crp s) pending 512 0 (len (fn-pull-list (fn-csp-header s)))))
               (word (car line)))
          (case word
            (:line (fn-csp-after-header s (cadr line) (cadddr line) (nfix (nth 4 line))))
            (:refused (fn-csp-fail s :malformed))
            (otherwise (list (fn-csp-with s :header (cadr line) :crp (caddr line)
                                         :pending (cadddr line)
                                         :replay (if (eq mode :replay-header)
                                                     (+ (nfix (fn-csp-replay s)) (nfix (nth 4 line)))
                                                   (fn-csp-replay s))) nil))))))
     ((eq mode :hash) (fn-csp-hash-effect s))
     ((member-eq mode '(:body :replay-body))
      (if (atom pending)
          (if (eq mode :replay-body) (fn-csp-read-replay s) (list s nil))
        (let* ((framed (fn-csp-framer-window (fn-csp-body-framer s) pending))
               (word (car framed))
               (s (fn-csp-with s :framer (cadr framed) :pending (cadddr framed)
                                :replay (if (eq mode :replay-body)
                                            (+ (nfix (fn-csp-replay s)) (nfix (nth 4 framed)))
                                          (fn-csp-replay s))))
               (emission (fn-pull-list (caddr framed))))
          (cond ((member-eq word '(:done :refused)) (fn-csp-fail s :malformed))
                ((eq mode :body)
                 (fn-csp-write s emission (if (eq word :record-end) :hash :body)))
                ((fn-csp-skip s)
                 ; A 435 record's body is skipped through the spool, sent on
                 ; no connection; the boundary check defers to the next
                 ; read, exactly as the filled record's does.
                 (list (if (eq word :record-end)
                           (fn-csp-with s :mode :replay-header :slot nil
                                        :framer nil :msgid nil :skip nil)
                         s)
                       nil))
                ((atom emission) (list s nil))
                (t (list (fn-csp-with s :mode :local-write
                                     :resume (if (eq word :record-end) :terminator :replay-body))
                         (list (list* :local (fn-csp-slot s) emission))))))))
     ((eq mode :terminator)
      (let* ((j (nfix (fn-csp-slot s))) (m (fn-csp-msgid s))
             (s2 (fn-csp-with s :conns (fn-csp-conns-set (fn-csp-conns s) j
                                                         (cons m :verdict))))
             (done (fn-csp-record-done s2)))
        (list (car done) (cons (list* :local j '(46 13 10)) (cadr done)))))
     ((eq mode :held) (fn-csp-try-offer s))
     (t (list s nil)))))

(defun fn-csp-local-event-octets (event)
  ; The octets of (:local j . octets): the local node's reply on connection j.
  (declare (xargs :guard t))
  (if (and (consp event) (consp (cdr event)) (fn-pull-octetsp (cddr event)))
      (cddr event) nil))

(defun fn-csp-local-opened (s j code conns)
  ; The reply while j greets: 200/201 frees the connection, anything else
  ; is a local protocol violation.
  (declare (xargs :guard (natp j)))
  (if (member-equal code '(200 201))
      (list (fn-csp-with s :conns (fn-csp-conns-set conns j :free)) nil)
    (fn-csp-fail s :local-refused)))

(defun fn-csp-local-await335 (s j code c conns round)
  ; The reply to the IHAVE the filling record sent on j: 335 opens the body,
  ; 435 settles the record as a duplicate at once (its body is skipped
  ; through the spool and sent on no connection), 436 defers the round,
  ; anything else is a local protocol violation.
  (declare (xargs :guard (and (natp j) (consp c))))
  (cond ((equal code 335)
         (list (fn-csp-with s
                            :conns (fn-csp-conns-set conns j (cons (car c) :streaming))
                            :mode (if (zp (nfix (fn-pull-at 3 (fn-csp-body-framer s))))
                                      :terminator :replay-body))
               nil))
        ((equal code 435)
         (let ((s1 (fn-csp-session-with-round
                    s (fn-cu-with round :counts
                                  (fn-cu-count (fn-cu-r-counts round) 1)))))
           (if (zp (nfix (fn-pull-at 3 (fn-csp-body-framer s1))))
               (fn-csp-record-done
                (fn-csp-with s1 :conns (fn-csp-conns-set conns j :free)
                             :slot nil))
             (list (fn-csp-with s1 :conns (fn-csp-conns-set conns j :free)
                                :slot nil :mode :replay-body :skip t)
                   nil))))
        ((equal code 436) (fn-csp-fail s :local-deferred))
        (t (fn-csp-fail s :local-refused))))

(defun fn-csp-local-verdict (s j code conns round)
  ; The settling reply for the record whose terminator j carried: the count
  ; of its own class moves exactly one, j is freed, and the last verdict of
  ; a drained batch is itself the one that makes the window idle -- so
  ; idleness is judged on the conns AFTER the free, and that verdict
  ; journals the batch.  436 defers, anything else is a violation.
  (declare (xargs :guard (natp j)))
  (cond ((member-equal code '(235 437))
         (let* ((s1 (fn-csp-session-with-round
                     s (fn-cu-with round :counts
                                   (fn-cu-count (fn-cu-r-counts round)
                                                (if (equal code 235) 0 2)))))
                (s2 (fn-csp-with s1 :conns (fn-csp-conns-set conns j :free))))
           (if (and (eq (fn-csp-mode s2) :drain)
                    (fn-csp-conns-idlep (fn-csp-conns s2)))
               (fn-csp-batch-finish s2)
             (list s2 nil))))
        ((equal code 436) (fn-csp-fail s :local-deferred))
        (t (fn-csp-fail s :local-refused))))

(defun fn-csp-local (s j octets)
  ; The local node's reply on connection j, keyed to the binding the conn
  ; holds: the greeting while :opening, the 335/435 while an IHAVE is owed,
  ; the verdict once the terminator is written.  A reply in any other conn
  ; state settles nothing: a local protocol violation (:local-refused); a
  ; 436 holds the round (:local-deferred).  No count moves on a reply that
  ; settles nothing.
  (declare (xargs :guard (natp j)))
  (let* ((code (fn-pull-local-code octets))
         (conns (fn-csp-conns s))
         (c (fn-csp-conn j s))
         (round (fn-cu-s-round (fn-csp-session s))))
    (cond
     ((eq c :opening) (fn-csp-local-opened s j code conns))
     ((and (consp c) (eq (cdr c) :await335)
           (eq (fn-csp-mode s) :offer) (equal (fn-csp-slot s) (nfix j)))
      (fn-csp-local-await335 s j code c conns round))
     ((and (consp c) (eq (cdr c) :verdict))
      (fn-csp-local-verdict s j code conns round))
     (t (fn-csp-fail s :local-refused)))))

(defun fn-csp-local-window (s j)
  ; The local node took connection j's body window without a reply: only the
  ; filling record's own window, only while it streams.
  (declare (xargs :guard (natp j)))
  (let ((c (fn-csp-conn j s)))
    (if (and (eq (fn-csp-mode s) :local-write)
             (equal (fn-csp-slot s) (nfix j))
             (consp c) (eq (cdr c) :streaming))
        (list (fn-csp-with s :mode (fn-csp-resume s)) nil)
      (fn-csp-fail s :local-refused))))

(defun fn-csp-step (s event)
  (declare (xargs :guard t))
  (let ((kind (car (fn-pull-list event))) (mode (fn-csp-mode s)))
    (cond
     ((member-eq mode '(:failed :done)) (list s nil))
     ((eq kind :lost)
      (fn-csp-fail s (if (eq (cadr (fn-pull-list event)) :round-deadline) :round-deadline :lost)))
     ; The bank refused this quantum's metered work (a spent coordinate): the
     ; round ends by name, its cursor at the last journaled batch.
     ((eq kind :work-refused) (fn-csp-fail s :peer-work-exhausted))
     ((not (fn-cu-session-readyp (fn-csp-session s)))
      (let ((pair (fn-cu-session-step-pair (fn-csp-session s) event)))
        (list (fn-csp-with s :session (car pair)) (cadr pair))))
     ((eq kind :remote)
      (let ((bytes (fn-pull-event-octets event)))
        (if (or (not (member-eq mode '(:status :header :body)))
                (consp (fn-csp-pending s)) (not (fn-cbor-at-mostp bytes 512)))
            (fn-csp-fail s :malformed)
          (list (fn-csp-with s :pending bytes) nil))))
     ((eq kind :spool-written)
      (if (and (eq mode :write) (eq (nth 1 event) :ok)
               (equal (nth 2 event) (fn-csp-count s)))
          (list (fn-csp-with s :mode (fn-csp-resume s)) nil)
        (fn-csp-fail s :spool-write)))
     ((eq kind :digest)
      (if (and (eq mode :hash) (fn-cu-chainp (nth 1 event)))
          (list (fn-csp-with s :mode :header
                            :chain (fn-blake3-stobj (append (fn-pull-list (fn-csp-chain s))
                                                            (nth 1 event) (fn-pull-list (fn-csp-msgid s))))) nil)
        (fn-csp-fail s :spool-hash)))
     ((eq kind :spool-read)
      (let ((bytes (fn-pull-list (nth 3 event))))
        (if (and (member-eq mode '(:replay-header :replay-body))
                 (eq (nth 1 event) :ok) (equal (nth 2 event) (fn-csp-count s))
                 (fn-cbor-at-mostp bytes 512) (equal (len bytes) (fn-csp-count s))
                 (fn-cbor-octet-listp bytes) (atom (fn-csp-pending s)))
            (list (fn-csp-with s :pending bytes) nil)
          (fn-csp-fail s :spool-read))))
     ((eq kind :local-window) (fn-csp-local-window s (nfix (nth 1 event))))
     ((eq kind :local)
      (fn-csp-local s (nfix (nth 1 event)) (fn-csp-local-event-octets event)))
     ((eq kind :tick) (fn-csp-next s))
     (t (fn-csp-fail s :malformed)))))

; KEYSTONE SUBJECT (host/native/pull-service.lisp `fnn-pull-flight-begin').
; LIMIT is the spool allowance of the flight's bank lease, or nil when no
; lease was drawn: without one the round never dials and fails by name.
; WINDOW is W, the offer window's width: the operator's own commit batch
; bound (log-batch-records), read once by the host -- a work-per-step bound,
; never a data cap (D27) and never a constant of this book.
(defun fn-csp-begin (plan cursor credential limit window)
  (declare (xargs :guard (natp window)))
  (let* ((pair (fn-cu-session-begin-pair plan cursor credential))
         (s (list :status (car pair) nil nil nil 0 0 nil (fn-cu-cursor-chain cursor)
                  nil nil 0 limit 0 nil nil nil
                  (nfix window) (fn-csp-conns-of window :unopened) nil)))
    (cond ((not (posp limit)) (fn-csp-fail s :peer-flight-unfunded))
          ((not (posp window)) (fn-csp-fail s :window-invalid))
          (t (list s (cadr pair))))))

; The host's other entry points (one value each).
(defun fn-csp-done-p (s)
  (declare (xargs :guard t))
  (and (member-eq (fn-csp-mode s) '(:done :failed)) t))

(defun fn-csp-close (s)
  ; The cursor a closed round leaves: always the committed one.
  (declare (xargs :guard t))
  (fn-cu-session-close (fn-csp-session s)))

(defun fn-csp-log-line (s)
  (declare (xargs :guard t))
  (fn-cu-session-log-line (fn-csp-session s)))

(defun fn-csp-read-limit (s)
  ; One peer window: the step refuses a larger chunk or one while pending.
  (declare (ignore s) (xargs :guard t))
  512)

(defun fn-csp-tick-p (s)
  ; A quantum is owed only when it can do work.  :held and :drain are pure
  ; waits -- no tick while nothing can advance -- EXCEPT a held record that
  ; can take (or open) a connection: one tick binds or opens it and the
  ; condition is gone.  No spin.
  (declare (xargs :guard t))
  (and (fn-cu-session-readyp (fn-csp-session s))
       (or (member-eq (fn-csp-mode s) '(:hash :terminator :replay-header :replay-body))
           (and (member-eq (fn-csp-mode s) '(:status :header :body))
                (consp (fn-csp-pending s)))
           (and (eq (fn-csp-mode s) :held)
                (or (fn-csp-free-conn (fn-csp-conns s) 0)
                    (fn-csp-unopened-conn (fn-csp-conns s) 0))))))

(defun fn-csp-work-units (s event)
  ; Selected logical framing/dispatch work, not a completed CPU/GC tariff.
  ; Hash ticks and I/O effects each require another actual metered draw.
  (declare (xargs :guard t))
  (let ((kind (car (fn-pull-list event))))
    (cond ((eq kind :tick)
           (+ 1 (len (fn-pull-list (fn-csp-header s)))
              (len (fn-pull-list (fn-csp-pending s)))))
          ((eq kind :remote)
           (+ 1 (len (fn-pull-list (cdr (fn-pull-list event))))))
          ((eq kind :local)
           (+ 1 (len (fn-pull-list (fn-csp-local-event-octets event)))))
          ((eq kind :spool-read)
           (+ 1 (len (fn-pull-list (fn-pull-at 3 event)))))
          (t 1))))

(defun fn-csp-io-work-units (operation count)
  (declare (xargs :guard t))
  (if (member-eq operation '(:write :replay :digest)) (1+ (nfix count)) 1))

; -----------------------------------------------------------------------------
; Keystones over the host-called step (host/native/pull-service.lisp drives
; fn-csp-step for every catch-up event): a round retains one bounded window,
; and a spooled emission is whole or refused by name.

(defthm fn-csp-write-spools-whole-or-fails-by-name
  ; KEYSTONE (no silent truncation). An emission reaches the spool whole, at
  ; the current offset, within the funded limit, or the round fails with the
  ; named refusal :spool-quota and no spool write; never a prefix.
  (let* ((r (fn-csp-write s emission resume))
         (s2 (car r)) (effects (cadr r))
         (bytes (fn-pull-list emission)))
    (or (and (equal (fn-csp-mode s2) :failed)
             (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session s2))) :spool-quota)
             (equal effects '((:close))))
        (and (atom bytes) (equal effects nil)
             (equal (fn-csp-offset s2) (fn-csp-offset s)))
        (and (equal effects (list (list :spool-write (fn-csp-offset s) bytes)))
             (equal (fn-csp-offset s2) (+ (fn-csp-offset s) (len bytes)))
             (<= (fn-csp-offset s2) (fn-csp-limit s))
             (equal (fn-csp-count s2) (len bytes))
             (equal (fn-csp-mode s2) :write)
             (equal (fn-csp-resume s2) resume))))
  :hints (("Goal" :in-theory (enable fn-csp-write fn-csp-append-admit fn-csp-fail
                                     fn-csp-session-with-round fn-cu-fail))))

(defun fn-csp-windowp (s)
  ; The controller's retained input: one header window, one pending window.
  (declare (xargs :guard t))
  (and (<= (len (fn-pull-list (fn-csp-header s))) 512)
       (<= (len (fn-pull-list (fn-csp-pending s))) 512)))

(local (defthm fn-csp-at-mostp-is-len
  (equal (fn-cbor-at-mostp xs n) (<= (len xs) (nfix n)))
  :hints (("Goal" :in-theory (enable fn-cbor-at-mostp)))))

(local (defthm fn-csp-header-window-bounded
  (implies (and (true-listp rev) (natp count) (<= (len rev) count) (<= count 512))
           (let ((hw (fn-csp-header-window rev crp input fuel used count)))
             (and (true-listp (cadr hw))
                  (<= (len (cadddr hw)) (len input))
                  (implies (not (equal (car hw) :line))
                           (<= (len (cadr hw)) 512)))))
  :hints (("Goal" :induct (fn-csp-header-window rev crp input fuel used count)
                  :in-theory (enable fn-csp-header-window)))))

(local (defthm fn-csp-len-nthcdr-bound
  (<= (len (nthcdr n x)) (len x))
  :rule-classes :linear))

(local (defthm fn-csp-framer-window-rest-shorter
  (<= (len (nth 3 (fn-csp-framer-window f input))) (len input))
  :hints (("Goal" :use fn-csp-framer-window-accounts-for-every-octet
                  :in-theory (disable fn-csp-framer-window-accounts-for-every-octet)))
  :rule-classes :linear))

(local (defthm fn-csp-fail-keeps-window
  (fn-csp-windowp (car (fn-csp-fail s reason)))
  :hints (("Goal" :in-theory (enable fn-csp-fail fn-csp-session-with-round)))))

(local (defthm fn-csp-session-with-round-keeps-window
  (implies (fn-csp-windowp s) (fn-csp-windowp (fn-csp-session-with-round s r)))
  :hints (("Goal" :in-theory (enable fn-csp-session-with-round)))))

(local (defthm fn-csp-write-keeps-window
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-write s emission resume))))
  :hints (("Goal" :in-theory (e/d (fn-csp-write) (fn-csp-fail fn-csp-windowp))
                  :use ((:instance fn-csp-fail-keeps-window (reason :spool-quota)))
           )
          ("Goal'" :in-theory (enable fn-csp-windowp)))))

(local (defthm fn-csp-session-with-round-fields
  (and (equal (fn-pull-at 2 (fn-csp-session-with-round s r)) (fn-pull-at 2 s))
       (equal (fn-pull-at 10 (fn-csp-session-with-round s r)) (fn-pull-at 10 s)))
  :hints (("Goal" :in-theory (enable fn-csp-session-with-round)))))

(local (defthm fn-csp-batch-finish-keeps-window
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-batch-finish s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-batch-finish) (fn-csp-session-with-round))))))

(local (defthm fn-csp-try-offer-keeps-window
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-try-offer s))))
  :hints (("Goal" :in-theory (enable fn-csp-try-offer)))))

(local (defthm fn-csp-with-keeps-window-untouched
  ; The with of record-done touches only the framer, msgid, skip and slot
  ; fields: both retained windows are untouched.
  (implies (fn-csp-windowp s)
           (fn-csp-windowp (fn-csp-with s :slot nil :skip nil :framer nil :msgid nil)))
  :hints (("Goal" :in-theory (enable fn-csp-windowp)))))

(local (defthm fn-csp-record-done-keeps-window
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-record-done s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-record-done) (fn-csp-batch-finish fn-csp-fail))
                  :use (fn-csp-with-keeps-window-untouched
                        (:instance fn-csp-batch-finish-keeps-window
                          (s (fn-csp-with s :slot nil :skip nil :framer nil :msgid nil))))))))

(local (defthm fn-csp-read-replay-keeps-window
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-read-replay s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-read-replay)
                                  (fn-csp-record-done fn-csp-fail))
                  :use (fn-csp-record-done-keeps-window
                        (:instance fn-csp-fail-keeps-window (reason :short-spool)))))))

(local (defthm fn-csp-conns-idlep-of-set-free
  ; The bridge: judging idleness on the conns with j freed is judging every
  ; OTHER entry of the pre-state's conns.
  (equal (fn-csp-conns-idlep (fn-csp-conns-set conns j :free))
         (fn-csp-conns-idlep-but conns (nfix j)))
  :hints (("Goal" :induct (fn-csp-conns-set conns j :free)))))

(local (defthm fn-csp-with-conns-keeps-window
  ; Binding/freeing connections and steering the mode/slot/skip touch no
  ; retained window.
  (implies (fn-csp-windowp s)
           (fn-csp-windowp (fn-csp-with s :conns c :mode m :slot k :skip sk)))
  :hints (("Goal" :in-theory (enable fn-csp-windowp)))))

(local (defthm fn-csp-local-window-keeps-window
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-local-window s j))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-window) (fn-csp-fail))
                  :use ((:instance fn-csp-fail-keeps-window (reason :local-refused)))))))

(local (defthm fn-csp-windowp-of-state
  ; A state's windows are its 3rd and 11th fields, whatever the other 18 hold.
  (equal (fn-csp-windowp (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19))
         (and (<= (len (fn-pull-list a2)) 512) (<= (len (fn-pull-list a10)) 512)))
  :hints (("Goal" :in-theory (enable fn-csp-windowp)))))

(local (defthm fn-csp-windowp-of-symbol
  ; The same rule for a state named by a variable: the two windows are the
  ; 3rd and 11th fields, whatever the other 18 hold.  Together with
  ; FN-CSP-WINDOWP-OF-STATE this collapses the per-mode case analysis of
  ; the keeps-window lemma class: a rebuilt state rewrites to the two
  ; length bounds without touching any other field.
  (implies (syntaxp (symbolp s))
           (equal (fn-csp-windowp s)
                  (and (<= (len (fn-pull-list (fn-pull-at 2 s))) 512)
                       (<= (len (fn-pull-list (fn-pull-at 10 s))) 512))))
  :hints (("Goal" :in-theory (enable fn-csp-windowp)))))

; Disabled at birth: fired on every folded windowp hypothesis downstream
; and its pull-list case splits broke the after-header proof chain.  The
; local-reply lemmas enable it in their own hints.
(in-theory (disable fn-csp-windowp-of-symbol))

(local (defthm fn-csp-with-session-round-conns-keeps-window
  ; Steering the session's round, then binding/freeing a connection and the
  ; mode/slot/skip fields, touches no retained window.
  (implies (fn-csp-windowp s)
           (fn-csp-windowp (fn-csp-with (fn-csp-session-with-round s r)
                                        :conns c :mode m :slot k :skip sk)))
  :hints (("Goal" :in-theory (disable fn-csp-session-with-round)))))

(local (defthm fn-csp-local-opened-keeps-window
  (implies (fn-csp-windowp s)
           (fn-csp-windowp (car (fn-csp-local-opened s j code conns))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-opened) (fn-csp-fail))
                  :use ((:instance fn-csp-fail-keeps-window (reason :local-refused)))))))

(local (defthm fn-csp-local-await335-keeps-window
  (implies (fn-csp-windowp s)
           (fn-csp-windowp (car (fn-csp-local-await335 s j code c conns round))))
  :hints (("Goal"
           :in-theory (e/d (fn-csp-local-await335 fn-csp-windowp-of-symbol)
                           (fn-csp-fail fn-csp-record-done fn-csp-batch-finish
                            fn-csp-session-with-round fn-cu-count fn-csp-windowp))
           :use ((:instance fn-csp-record-done-keeps-window
                  (s (fn-csp-with (fn-csp-session-with-round
                                    s (fn-cu-with round :counts
                                                  (fn-cu-count (fn-cu-r-counts round) 1)))
                                   :conns (fn-csp-conns-set conns j :free) :slot nil)))
                 (:instance fn-csp-fail-keeps-window (reason :local-deferred))
                 (:instance fn-csp-fail-keeps-window (reason :local-refused)))))))

(local (defthm fn-csp-local-verdict-keeps-window
  ; The settling reply frees its connection and moves its own count class;
  ; the last verdict of a drained batch is the one that makes the window
  ; idle, so the batch-finish instance is judged on the freed conns.
  (implies (fn-csp-windowp s)
           (fn-csp-windowp (car (fn-csp-local-verdict s j code conns round))))
  :hints (("Goal"
           :in-theory (e/d (fn-csp-local-verdict fn-csp-windowp-of-symbol)
                           (fn-csp-fail fn-csp-record-done fn-csp-batch-finish
                            fn-csp-session-with-round fn-cu-count fn-csp-windowp))
           :use ((:instance fn-csp-batch-finish-keeps-window
                  (s (fn-csp-with (fn-csp-session-with-round
                                    s (fn-cu-with round :counts
                                                  (fn-cu-count (fn-cu-r-counts round)
                                                               (if (equal code 235) 0 2))))
                                   :conns (fn-csp-conns-set conns j :free))))
                 (:instance fn-csp-fail-keeps-window (reason :local-deferred))
                 (:instance fn-csp-fail-keeps-window (reason :local-refused)))))))

(local (defthm fn-csp-local-keeps-window
  ; The per-phase helpers unfold with fn-csp-local; the leaves are the same
  ; instances the helper lemmas use.  (The helper RULES cannot fire here:
  ; their storage depends on the windowp type-prescription rune, which
  ; disabling fn-csp-windowp also disables.)
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-local s j octets))))
  :hints (("Goal"
           :in-theory (e/d (fn-csp-local fn-csp-local-opened fn-csp-local-await335
                                       fn-csp-local-verdict fn-csp-windowp-of-symbol)
                           (fn-csp-fail fn-csp-record-done fn-csp-batch-finish
                            fn-csp-session-with-round fn-cu-count fn-csp-windowp))
           :use ((:instance fn-csp-record-done-keeps-window
                  (s (fn-csp-with (fn-csp-session-with-round
                                    s (fn-cu-with (fn-cu-s-round (fn-pull-at 1 s))
                                                  :counts
                                                  (fn-cu-count (fn-cu-r-counts (fn-cu-s-round (fn-pull-at 1 s))) 1)))
                                   :conns (fn-csp-conns-set (fn-pull-at 18 s) j :free)
                                   :slot nil)))
                 (:instance fn-csp-batch-finish-keeps-window
                  (s (fn-csp-with (fn-csp-session-with-round
                                    s (fn-cu-with (fn-cu-s-round (fn-pull-at 1 s))
                                                  :counts
                                                  (fn-cu-count (fn-cu-r-counts (fn-cu-s-round (fn-pull-at 1 s)))
                                                               (if (equal (fn-pull-local-code octets) 235) 0 2))))
                                   :conns (fn-csp-conns-set (fn-pull-at 18 s) j :free))))
                 (:instance fn-csp-fail-keeps-window (s s) (reason :local-deferred))
                 (:instance fn-csp-fail-keeps-window (s s) (reason :local-refused)))))))

(local (defthm fn-csp-after-header-keeps-window
  (implies (and (fn-csp-windowp s) (<= (len (fn-pull-list rest)) 512))
           (fn-csp-windowp (car (fn-csp-after-header s line rest used))))
  :hints (("Goal" :in-theory (e/d (fn-csp-after-header)
                                  (fn-csp-fail fn-csp-write fn-csp-windowp
                                   fn-csp-try-offer fn-csp-session-with-round))))))

(local (defthm fn-csp-windowp-facts
  (implies (fn-csp-windowp s)
           (and (<= (len (fn-pull-list (fn-pull-at 2 s))) 512)
                (<= (len (fn-pull-list (fn-pull-at 10 s))) 512)))
  :hints (("Goal" :in-theory (enable fn-csp-windowp)))
  :rule-classes :forward-chaining))

(local (defthm fn-csp-hash-effect-keeps-window
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-hash-effect s))))
  :hints (("Goal" :in-theory (enable fn-csp-hash-effect)))))

(local (defthm fn-csp-len-pull-list-bound (<= (len (fn-pull-list x)) (len x)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-pull-list)))))

(local (defthm fn-csp-header-window-rest-shorter
  (<= (len (cadddr (fn-csp-header-window rev crp input fuel used count))) (len input))
  :hints (("Goal" :induct (fn-csp-header-window rev crp input fuel used count)
                  :in-theory (enable fn-csp-header-window)))
  :rule-classes :linear))

(local (defthm fn-csp-framer-window-rest-shorter-cadddr
  (<= (len (cadddr (fn-csp-framer-window f input))) (len input))
  :hints (("Goal" :use fn-csp-framer-window-accounts-for-every-octet
                  :in-theory (disable fn-csp-framer-window-rest-shorter
                                      fn-csp-framer-window-accounts-for-every-octet)))
  :rule-classes :linear))

(local (defthm fn-csp-framer-window-rest-shorter-pull-list
  (<= (len (fn-pull-list (cadddr (fn-csp-framer-window f input)))) (len input))
  :hints (("Goal" :in-theory (disable fn-csp-framer-window-accounts-for-every-octet fn-csp-framer-window)))
  :rule-classes :linear))

(local (defthm fn-csp-header-window-rest-shorter-pull-list
  (<= (len (fn-pull-list (cadddr (fn-csp-header-window rev crp input fuel used count)))) (len input))
  :hints (("Goal" :in-theory (disable fn-csp-header-window)))
  :rule-classes :linear))

(local (defthm fn-csp-write-keeps-window-f
  (implies (and (<= (len (fn-pull-list (fn-pull-at 2 s))) 512)
                (<= (len (fn-pull-list (fn-pull-at 10 s))) 512))
           (fn-csp-windowp (car (fn-csp-write s emission resume))))
  :hints (("Goal" :use fn-csp-write-keeps-window :in-theory (enable fn-csp-windowp)))))

(local (defthm fn-csp-after-header-keeps-window-f
  (implies (and (<= (len (fn-pull-list (fn-pull-at 2 s))) 512)
                (<= (len (fn-pull-list (fn-pull-at 10 s))) 512)
                (<= (len (fn-pull-list rest)) 512))
           (fn-csp-windowp (car (fn-csp-after-header s line rest used))))
  :hints (("Goal" :use fn-csp-after-header-keeps-window :in-theory (e/d (fn-csp-windowp) (fn-csp-after-header))))))

(local (defthm fn-csp-read-replay-keeps-window-f
  (implies (and (<= (len (fn-pull-list (fn-pull-at 2 s))) 512)
                (<= (len (fn-pull-list (fn-pull-at 10 s))) 512))
           (fn-csp-windowp (car (fn-csp-read-replay s))))
  :hints (("Goal" :use fn-csp-read-replay-keeps-window :in-theory (e/d (fn-csp-windowp) (fn-csp-read-replay))))))

(local (defthm fn-csp-hash-effect-keeps-window-f
  (implies (and (<= (len (fn-pull-list (fn-pull-at 2 s))) 512)
                (<= (len (fn-pull-list (fn-pull-at 10 s))) 512))
           (fn-csp-windowp (car (fn-csp-hash-effect s))))
  :hints (("Goal" :use fn-csp-hash-effect-keeps-window :in-theory (e/d (fn-csp-windowp) (fn-csp-hash-effect))))))

(local (defthm fn-csp-pull-list-of-non-list (implies (not (true-listp x)) (equal (fn-pull-list x) nil)) :hints (("Goal" :in-theory (enable fn-pull-list)))))

(local (defthm fn-csp-framer-window-rest-true-listp
  (implies (true-listp input) (true-listp (cadddr (fn-csp-framer-window f input))))
  :hints (("Goal" :use fn-csp-framer-window-accounts-for-every-octet
                  :in-theory (disable fn-csp-framer-window-accounts-for-every-octet fn-csp-framer-window)))))

(local (defthm fn-csp-header-window-rest-true-listp
  (implies (true-listp input) (true-listp (cadddr (fn-csp-header-window rev crp input fuel used count))))
  :hints (("Goal" :induct (fn-csp-header-window rev crp input fuel used count)
                  :in-theory (enable fn-csp-header-window)))))

(local (defthm fn-csp-next-keeps-window
  ; The functions stay disabled so the composite branches do not unfold;
  ; their keeps-window THEOREMS stay live as rewrites and fire at any depth.
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-next s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-next)
                                  (fn-csp-fail fn-csp-write fn-csp-after-header
                                   fn-csp-read-replay fn-csp-hash-effect fn-csp-header-window
                                   fn-csp-framer-window fn-csp-framer-window-accounts-for-every-octet
                                   fn-csp-record-done fn-csp-try-offer))
                  :use (fn-csp-windowp-facts
                        (:instance fn-csp-header-window-rest-shorter-pull-list
                                   (rev (fn-pull-list (fn-pull-at 2 s))) (crp (fn-pull-at 3 s))
                                   (input (fn-pull-list (fn-pull-at 10 s))) (fuel 512) (used 0
                                   )
                                   (count (len (fn-pull-list (fn-pull-at 2 s)))))
                        (:instance fn-csp-framer-window-rest-shorter-pull-list
                                   (f (fn-pull-at 4 s)) (input (fn-pull-list (fn-pull-at 10 s)))))))))

(defthm fn-csp-step-keeps-window
  ; KEYSTONE (a round is bounded). Whatever arrives -- a peer chunk, a spool
  ; read, a local reply, a tick -- the controller retains at most one 512-octet
  ; header window and one 512-octet pending window; no record, line list or
  ; article is retained, whatever its size.  The offer window changes the
  ; claim only by what a slot retains: one Message-ID per bound connection,
  ; at most W of them, W the begin's argument.
  (implies (fn-csp-windowp s)
           (fn-csp-windowp (car (fn-csp-step s event))))
  :hints (("Goal" :in-theory (e/d (fn-csp-step)
                                  (fn-csp-fail fn-csp-next fn-csp-local fn-csp-local-window
                                   fn-csp-windowp fn-cu-session-step-pair fn-cu-session-readyp
                                   fn-blake3-stobj fn-cu-chainp fn-pull-event-octets fn-csp-session))
                  :use (fn-csp-windowp-facts
                        (:instance fn-csp-local-window-keeps-window)))))

(in-theory (disable fn-csp-windowp))

; -----------------------------------------------------------------------------
; Settling exactly once, per record identity (PRF-1335, the K1 chain)

(local (defthm fn-cu-next-keeps-counts
  ; The batch-finish round fact: whichever branch fn-cu-next takes, the
  ; round's counts are untouched -- journals, requests and phase changes
  ; never move a record class.
  (equal (fn-cu-r-counts (mv-nth 0 (fn-cu-next r))) (fn-cu-r-counts r))
  :hints (("Goal" :in-theory (enable fn-cu-next)))))

(local (defthm fn-cu-next-nil-todo-effects
  ; The nil-todo variant.  With nothing left to offer, fn-cu-next does not
  ; emit an IHAVE: the effects are one (:journal . cursor) naming the cursor
  ; the produced round commits, then the next request or the quit and close.
  ; No second journal, no :local effect.  The consp-todo branch offers
  ; instead; fn-csp-batch-finish never takes it, because it forces todo nil.
  (implies (not (consp (fn-cu-r-todo r)))
           (let ((next (mv-nth 0 (fn-cu-next r)))
                 (effs (mv-nth 1 (fn-cu-next r))))
             (and (consp effs)
                  (equal (car effs)
                         (cons :journal (fn-cu-round-cursor next)))
                  (not (member-eq :journal (strip-cars (cdr effs))))
                  (not (member-eq :local (strip-cars effs)))
                  (equal (fn-cu-r-counts next) (fn-cu-r-counts r))
                  (equal (fn-cu-r-position next)
                         (fn-cu-batch-next (fn-cu-r-batch r)))
                  (equal (fn-cu-r-chain next)
                         (fn-cu-batch-claim (fn-cu-r-batch r)))
                  (or (equal (fn-cu-r-phase next) :reply)
                      (equal (fn-cu-r-phase next) :done)))))
  :hints (("Goal" :in-theory (enable fn-cu-next fn-cu-round-cursor)))))

(local (defthm fn-csp-fail-keeps-counts
  ; A named failure settles no record either.
  (equal (fn-cu-r-counts (fn-cu-s-round (fn-csp-session (car (fn-csp-fail s reason)))))
         (fn-cu-r-counts (fn-cu-s-round (fn-csp-session s))))
  :hints (("Goal" :in-theory (enable fn-csp-fail fn-cu-fail fn-csp-session-with-round)))))

(local (defthm fn-csp-fail-shape
  (and (equal (fn-csp-mode (car (fn-csp-fail s reason))) :failed)
       (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session (car (fn-csp-fail s reason)))))
              reason))
  :hints (("Goal" :in-theory (enable fn-csp-fail fn-cu-fail fn-csp-session-with-round)))))

(local (defthm fn-csp-conns-set-is-update-nth
  ; CONNS-SET is UPDATE-NTH's placement (nil-padded past the end), so the
  ; nth/len lemmas of UPDATE-NTH carry over to the window.
  (implies (natp j)
           (equal (fn-csp-conns-set conns j c) (update-nth j c conns)))
  :hints (("Goal" :induct (fn-csp-conns-set conns j c)
                  :in-theory (enable fn-csp-conns-set)))))

(local (defthm fn-csp-batch-finish-effects
  ; TODO is nil by construction (fn-csp-batch-finish forces it), so the
  ; session layer cannot emit its own IHAVE here: the effects are exactly
  ; one (:journal . cursor), first, naming the cursor the produced round
  ; commits, then the next request or the quit+close -- no :local effect,
  ; no second journal.
  (let* ((pair (fn-csp-batch-finish s)) (effs (cadr pair)))
    (and (consp effs)
         (eq (car (car effs)) :journal)
         (equal (cdr (car effs))
                (fn-cu-round-cursor (fn-cu-s-round (fn-csp-session (car pair)))))
         (not (member-eq :journal (strip-cars (cdr effs))))
         (not (member-eq :local (strip-cars effs)))))
  :hints (("Goal" :in-theory (enable fn-csp-batch-finish fn-csp-session-with-round fn-cu-next)))))

(local (defthm fn-csp-batch-finish-facts
  (and (equal (fn-cu-r-counts (fn-cu-s-round (fn-csp-session (car (fn-csp-batch-finish s)))))
              (fn-cu-r-counts (fn-cu-s-round (fn-csp-session s))))
       (equal (fn-pull-at 18 (car (fn-csp-batch-finish s))) (fn-pull-at 18 s))
       (not (equal (fn-pull-at 0 (car (fn-csp-batch-finish s))) :failed)))
  :hints (("Goal" :in-theory (enable fn-csp-batch-finish fn-csp-session-with-round)))))

(local (defthm fn-csp-batch-finish-state-consp
  (consp (car (fn-csp-batch-finish s)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable fn-csp-batch-finish)))))

(local (defthm fn-csp-conns-idlep-of-update-nth-free
  ; The book's idlep bridge, in the UPDATE-NTH normal form the conns-set
  ; rule produces.
  (implies (natp j)
           (equal (fn-csp-conns-idlep (update-nth j :free conns))
                  (fn-csp-conns-idlep-but conns j)))
  :hints (("Goal" :use ((:instance fn-csp-conns-idlep-of-set-free))
                  :in-theory (e/d (fn-csp-conns-set-is-update-nth)
                                  (fn-csp-conns-idlep-of-set-free))))))

(local (defthm fn-csp-local-verdict-settles
  ; The settling reply, at the helper: the count of the reply's own class is
  ; the only one that moves, by exactly one; the binding's connection is
  ; freed and no other conn touched; the non-final verdict moves no cursor
  ; field and emits nothing; the final verdict of a drained batch hands the
  ; batch to fn-csp-batch-finish (whose journal discipline is its own
  ; keystone's).  ROUND is pinned to the state's: the fail branches keep the
  ; state's own round.
  (implies (and (natp j)
                (not (equal (fn-csp-mode s) :failed))
                (equal round (fn-cu-s-round (fn-csp-session s))))
           (let* ((pair (fn-csp-local-verdict s j code conns round))
                  (s2 (car pair)))
             (if (member-equal code '(235 437))
                 (and (equal (fn-cu-r-counts (fn-cu-s-round (fn-csp-session s2)))
                             (fn-cu-count (fn-cu-r-counts round)
                                          (if (equal code 235) 0 2)))
                      (equal (fn-csp-conns s2) (fn-csp-conns-set conns j :free))
                      (implies (not (and (eq (fn-csp-mode s) :drain)
                                         (fn-csp-conns-idlep-but conns (nfix j))))
                               (and (equal (fn-cu-r-position (fn-cu-s-round (fn-csp-session s2)))
                                           (fn-cu-r-position round))
                                    (equal (fn-csp-replay s2) (fn-csp-replay s))
                                    (equal (fn-csp-offset s2) (fn-csp-offset s))
                                    (equal (fn-csp-mode s2) (fn-csp-mode s))
                                    (equal (cadr pair) nil))))
               (and (equal (fn-cu-r-counts (fn-cu-s-round (fn-csp-session s2)))
                           (fn-cu-r-counts round))
                    (equal (fn-csp-mode s2) :failed)
                    (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session s2)))
                           (if (equal code 436) :local-deferred :local-refused))))))
  :hints (("Goal"
           :in-theory (e/d (fn-csp-local-verdict fn-csp-fail fn-cu-fail
                             fn-csp-session-with-round)
                           (fn-csp-batch-finish))
           :use ((:instance fn-csp-batch-finish-facts
                  (s (fn-csp-with (fn-csp-session-with-round
                                   s (fn-cu-with round :counts
                                                 (fn-cu-count (fn-cu-r-counts round)
                                                              (if (equal code 235) 0 2))))
                                  :conns (fn-csp-conns-set conns j :free)))))))))

(local (defthm fn-csp-local-verdict-final-journals
  ; The drained batch's last settling reply.  Freeing j leaves the window
  ; idle, so the verdict hands the state to fn-csp-batch-finish, whose
  ; effects are the nil-todo journal: one (:journal . cursor) naming the
  ; cursor the produced round commits, and no :local effect.
  (implies (and (natp j)
                (equal round (fn-cu-s-round (fn-csp-session s)))
                (member-equal code '(235 437))
                (eq (fn-csp-mode s) :drain)
                (fn-csp-conns-idlep-but conns (nfix j)))
           (let* ((pair (fn-csp-local-verdict s j code conns round))
                  (effs (cadr pair))
                  (s2 (car pair)))
             (and (consp effs)
                  (eq (car (car effs)) :journal)
                  (equal (cdr (car effs))
                         (fn-cu-round-cursor
                          (fn-cu-s-round (fn-csp-session s2))))
                  (not (member-eq :journal (strip-cars (cdr effs))))
                  (not (member-eq :local (strip-cars effs))))))
  :hints (("Goal"
           :in-theory (e/d (fn-csp-local-verdict fn-csp-session-with-round)
                           (fn-csp-batch-finish fn-cu-next))
           :use ((:instance fn-csp-batch-finish-effects
                  (s (fn-csp-with
                      (fn-csp-session-with-round
                       s (fn-cu-with round :counts
                                     (fn-cu-count (fn-cu-r-counts round)
                                                  (if (equal code 235) 0 2))))
                      :conns (fn-csp-conns-set conns j :free)))))))))

(local (defthm fn-csp-conn-verdict-fc
  (implies (equal (fn-csp-conn j s) (cons msgid :verdict))
           (and (consp (fn-csp-conn j s))
                (equal (cdr (fn-csp-conn j s)) :verdict)))
  :rule-classes :forward-chaining))

(defthm fn-csp-step-settles-one-verdict-exactly-once
  ; KEYSTONE (PRF-1335, safety -- the exactly-once half).  The settling reply
  ; on connection j for the record whose terminator j carried: with the
  ; binding (msgid . :verdict) on j, only a 235 or a 437 settles -- the count
  ; of its OWN class (0 imported / 2 refused) is the only one that moves, by
  ; exactly one; conns[j] becomes :free and every other conn is untouched
  ; (conns-set is update-nth).  A 436 fails the round :local-deferred, any
  ; other code :local-refused, and NO count moves -- so the reply that arrives
  ; after a record settled (its slot :free) finds no binding and settles
  ; nothing.  When the freed slot was the drained batch's last outstanding
  ; verdict the same step finishes the batch and journals it
  ; (fn-csp-journals-only-a-settled-batch); the cursor fields are pinned here
  ; for the non-final verdict.
  (implies (and (fn-cu-session-readyp (fn-csp-session s))
                (natp j) (fn-pull-octetsp octets)
                (not (member-eq (fn-csp-mode s) '(:failed :done)))
                (equal (fn-csp-conn j s) (cons msgid :verdict)))
           (let* ((pair (fn-csp-step s (list* :local j octets)))
                  (s2 (car pair))
                  (r (fn-cu-s-round (fn-csp-session s)))
                  (r2 (fn-cu-s-round (fn-csp-session s2))))
             (if (member-equal (fn-pull-local-code octets) '(235 437))
                 (and (equal (fn-cu-r-counts r2)
                             (fn-cu-count (fn-cu-r-counts r)
                                          (if (equal (fn-pull-local-code octets) 235) 0 2)))
                      (equal (fn-csp-conns s2)
                             (fn-csp-conns-set (fn-csp-conns s) j :free))
                      (implies (not (and (eq (fn-csp-mode s) :drain)
                                         (fn-csp-conns-idlep-but (fn-csp-conns s) (nfix j))))
                               (and (equal (fn-cu-r-position r2) (fn-cu-r-position r))
                                    (equal (fn-csp-replay s2) (fn-csp-replay s))
                                    (equal (fn-csp-offset s2) (fn-csp-offset s))
                                    (equal (fn-csp-mode s2) (fn-csp-mode s))
                                    (equal (cadr pair) nil))))
               (and (equal (fn-cu-r-counts r2) (fn-cu-r-counts r))
                    (equal (fn-csp-mode s2) :failed)
                    (equal (fn-cu-r-refusal r2)
                           (if (equal (fn-pull-local-code octets) 436)
                               :local-deferred :local-refused))))))
  :hints (("Goal"
           :in-theory (e/d (fn-csp-step fn-csp-local fn-csp-local-event-octets)
                           (fn-csp-local-verdict))
           :use ((:instance fn-csp-local-verdict-settles
                  (s s) (j j) (code (fn-pull-local-code octets))
                  (conns (fn-csp-conns s))
                  (round (fn-cu-s-round (fn-csp-session s))))))))
