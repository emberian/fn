; Bounded catchup spool controller. Fixed metadata, one input/output window;
; no record index, article line list or complete IHAVE body is retained.
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
                         (skip 'nil skip-p))
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
     ,(if skip-p skip `(fn-pull-at 16 ,s))))

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

(defun fn-csp-session-with-round (s r)
  (declare (xargs :guard t))
  (let ((session (fn-csp-session s)))
    (fn-csp-with s :session (fn-cu-session (fn-cu-s-fc session) r
                               (fn-cu-s-refusal session) (fn-cu-s-security session)))))

(defun fn-csp-fail (s reason)
  (declare (xargs :guard t))
  (mv-let (round effects) (fn-cu-fail (fn-cu-s-round (fn-csp-session s)) reason)
    (list (fn-csp-with (fn-csp-session-with-round s round)
                      :mode :failed :pending nil :header nil) effects)))

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
                      :mode :local-greeting :verified t :replay 0 :pending nil)
                     '((:open-local))))
              (t (list (fn-csp-with s :mode :replay-header :verified t :replay 0 :pending nil) nil)))))
     (t
      (let ((header (fn-cu-parse-header line)))
        (if (not header) (fn-csp-fail s :malformed)
          (if (eq mode :replay-header)
              (if (not (fn-csp-verified s)) (fn-csp-fail s :unverified)
                (list (fn-csp-with s :mode :offer :msgid (car header)
                                  :framer (fn-csp-framer (cdr header) nil) :skip nil)
                      (list (cons :local (fn-cu-ihave (cons (car header) nil))))))
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

(defun fn-csp-read-replay (s)
  (declare (xargs :guard t))
  (let* ((position (nfix (fn-csp-replay s))) (end (nfix (fn-csp-offset s)))
         (count (min 512 (nfix (- end position)))))
    (if (zp count)
        (if (and (eq (fn-csp-mode s) :replay-header) (not (consp (fn-csp-header s)))
                 (not (fn-csp-crp s)))
            (fn-csp-batch-finish s)
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
                 (list (if (eq word :record-end) (fn-csp-with s :mode :replay-header) s) nil))
                ((atom emission) (list s nil))
                (t (list (fn-csp-with s :mode :local-write
                                     :resume (if (eq word :record-end) :terminator :replay-body))
                         (list (cons :local emission))))))))
     ((eq mode :terminator)
      (list (fn-csp-with s :mode :verdict) (list (cons :local '(46 13 10)))))
     (t (list s nil)))))

(defun fn-csp-local (s octets)
  (declare (xargs :guard t))
  (let ((code (fn-pull-local-code octets)) (mode (fn-csp-mode s))
        (round (fn-cu-s-round (fn-csp-session s))))
    (cond
     ((eq mode :local-greeting)
      (if (member-equal code '(200 201)) (list (fn-csp-with s :mode :replay-header) nil)
        (fn-csp-fail s :local-refused)))
     ((eq mode :offer)
      (cond ((equal code 335)
             (list (fn-csp-with s :mode (if (zp (nfix (fn-pull-at 3 (fn-csp-body-framer s))))
                                           :terminator :replay-body)) nil))
            ((equal code 435)
             (let ((s (fn-csp-session-with-round s (fn-cu-with round :counts (fn-cu-count (fn-cu-r-counts round) 1)))))
               (list (fn-csp-with s :mode (if (zp (nfix (fn-pull-at 3 (fn-csp-body-framer s))))
                                             :replay-header :replay-body) :skip t) nil)))
            ((equal code 436) (fn-csp-fail s :local-deferred))
            (t (fn-csp-fail s :local-refused))))
     ((eq mode :verdict)
      (cond ((member-equal code '(235 437))
             (list (fn-csp-with
                    (fn-csp-session-with-round s
                     (fn-cu-with round :counts (fn-cu-count (fn-cu-r-counts round) (if (equal code 235) 0 2))))
                    :mode :replay-header) nil))
            ((equal code 436) (fn-csp-fail s :local-deferred))
            (t (fn-csp-fail s :local-refused))))
     (t (fn-csp-fail s :local-refused)))))

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
     ((eq kind :local-window)
      (if (eq mode :local-write) (list (fn-csp-with s :mode (fn-csp-resume s)) nil)
        (fn-csp-fail s :local-refused)))
     ((eq kind :local) (fn-csp-local s (fn-pull-event-octets event)))
     ((eq kind :tick) (fn-csp-next s))
     (t (fn-csp-fail s :malformed)))))

; KEYSTONE SUBJECT (host/native/pull-service.lisp `fnn-pull-flight-begin').
; LIMIT is the spool allowance of the flight's bank lease, or nil when no
; lease was drawn: without one the round never dials and fails by name.
(defun fn-csp-begin (plan cursor credential limit)
  (declare (xargs :guard t))
  (let* ((pair (fn-cu-session-begin-pair plan cursor credential))
         (s (list :status (car pair) nil nil nil 0 0 nil (fn-cu-cursor-chain cursor)
                  nil nil 0 limit 0 nil nil nil)))
    (if (posp limit)
        (list s (cadr pair))
      (fn-csp-fail s :peer-flight-unfunded))))

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
  (declare (xargs :guard t))
  (and (fn-cu-session-readyp (fn-csp-session s))
       (or (member-eq (fn-csp-mode s) '(:hash :terminator :replay-header :replay-body))
           (and (member-eq (fn-csp-mode s) '(:status :header :body))
                (consp (fn-csp-pending s))))))

(defun fn-csp-work-units (s event)
  ; Selected logical framing/dispatch work, not a completed CPU/GC tariff.
  ; Hash ticks and I/O effects each require another actual metered draw.
  (declare (xargs :guard t))
  (let ((kind (car (fn-pull-list event))))
    (cond ((eq kind :tick)
           (+ 1 (len (fn-pull-list (fn-csp-header s)))
              (len (fn-pull-list (fn-csp-pending s)))))
          ((member-eq kind '(:remote :local))
           (+ 1 (len (fn-pull-list (cdr (fn-pull-list event))))))
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

(local (defthm fn-csp-read-replay-keeps-window
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-read-replay s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-read-replay)
                                  (fn-csp-batch-finish fn-csp-fail))
                  :use (fn-csp-batch-finish-keeps-window
                        (:instance fn-csp-fail-keeps-window (reason :short-spool)))))))

(local (defthm fn-csp-local-keeps-window
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-local s octets))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local) (fn-csp-fail))
                  :use ((:instance fn-csp-fail-keeps-window (reason :local-refused))
                        (:instance fn-csp-fail-keeps-window (reason :local-deferred)))))))

(local (defthm fn-csp-windowp-of-state
  (equal (fn-csp-windowp (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16))
         (and (<= (len (fn-pull-list a2)) 512) (<= (len (fn-pull-list a10)) 512)))
  :hints (("Goal" :in-theory (enable fn-csp-windowp)))))

(local (defthm fn-csp-after-header-keeps-window
  (implies (and (fn-csp-windowp s) (<= (len (fn-pull-list rest)) 512))
           (fn-csp-windowp (car (fn-csp-after-header s line rest used))))
  :hints (("Goal" :in-theory (e/d (fn-csp-after-header)
                                  (fn-csp-fail fn-csp-write fn-csp-windowp
                                   fn-csp-session-with-round))))))

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
  (implies (fn-csp-windowp s) (fn-csp-windowp (car (fn-csp-next s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-next)
                                  (fn-csp-fail fn-csp-write fn-csp-windowp fn-csp-after-header
                                   fn-csp-read-replay fn-csp-hash-effect fn-csp-header-window
                                   fn-csp-framer-window fn-csp-framer-window-accounts-for-every-octet
                                   fn-csp-write-keeps-window fn-csp-after-header-keeps-window
                                   fn-csp-read-replay-keeps-window fn-csp-hash-effect-keeps-window))
                  :use (fn-csp-windowp-facts
                        (:instance fn-csp-header-window-rest-shorter-pull-list
                                   (rev (fn-pull-list (fn-pull-at 2 s))) (crp (fn-pull-at 3 s))
                                   (input (fn-pull-list (fn-pull-at 10 s))) (fuel 512) (used 0)
                                   (count (len (fn-pull-list (fn-pull-at 2 s)))))
                        (:instance fn-csp-framer-window-rest-shorter-pull-list
                                   (f (fn-pull-at 4 s)) (input (fn-pull-list (fn-pull-at 10 s)))))))))

(defthm fn-csp-step-keeps-window
  ; KEYSTONE (a round is bounded). Whatever arrives -- a peer chunk, a spool
  ; read, a local reply, a tick -- the controller retains at most one 512-octet
  ; header window and one 512-octet pending window; no record, line list or
  ; article is retained, whatever its size.
  (implies (fn-csp-windowp s)
           (fn-csp-windowp (car (fn-csp-step s event))))
  :hints (("Goal" :in-theory (e/d (fn-csp-step)
                                  (fn-csp-fail fn-csp-next fn-csp-local fn-csp-windowp fn-cu-session-step-pair fn-cu-session-readyp fn-blake3-stobj fn-cu-chainp fn-pull-event-octets fn-csp-session))
                  :use (fn-csp-windowp-facts))))

(in-theory (disable fn-csp-windowp))
