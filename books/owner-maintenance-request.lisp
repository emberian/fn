; fn: maintenance verbs answered by the running owner, and a stopped store's
; status read from its checkpoint header (lane operability-2, row S3,
; 2026-09-29).
;
; `recover' and `store inspect' opened the store under its lock, so a running
; owner refused them (`store is already locked'), and `status' on a stopped
; store replayed the whole log on every call (`status --watch' per tick).
; Now:
;
;   fn-omr-route            the operator's route for a maintenance verb, from
;       the liveness word ACL2 decides over the socket and the writer lock
;       (books/native-control.lisp fn-native-control-liveness): a live owner
;       answers (:owner), an owner that holds the lock and answers nothing on
;       its socket refuses by name (:held), and only a free lock (no owner,
;       or a crashed one's stale socket) starts the offline executor.
;   fn-omr-recover-line     `recover' on a running owner: accepted, naming
;       that the owner's open recovered the store (its status follows); or
;       refused by name with what it would take.
;   fn-omr-inspect-*        `store inspect ID' on a running owner is the
;       owner's own lookup, sent back as a word; the client renders the SAME
;       report the offline verb renders (KEYSTONE
;       fn-omr-inspect-live-is-the-offline-report).
;   fn-omr-stopped-report   `status'/`health' on a stopped store: the record
;       count the newest checkpoint covers (its header's sequence field, 37
;       octets read, nothing replayed), the journal's octets, and the bound
;       they give on the transactions (KEYSTONE
;       fn-omr-transactions-at-most-bounds-the-count: every record frame is at
;       least *fn-omr-min-frame-octets* long).  The exact counts are the
;       running owner's, or `status --replay' / `recover' on a stopped store.
;
; Host subjects: host/native/operator.lisp fnn-operator-execute-recover-route,
; fnn-operator-execute-inspect (the live arm), fnn-command-stopped-report;
; host/native/admin.lisp fnn-owner-inspect-request.
(in-package "ACL2")
(include-book "native-operator")
(include-book "native-live-status")
(include-book "native-control-reason")
(include-book "store-checkpoint-codec")
(include-book "store-profile-open")
(include-book "native-health")

; -----------------------------------------------------------------------------
; The route

(defun fn-omr-route (liveness)
  (declare (xargs :guard t))
  (cond ((equal liveness :live) :owner)
        ((equal liveness :held) :held)
        (t :offline)))

; A verb refused because an owner holds the writer lock and answers nothing
; on its control socket (the :held liveness): by name, with what it would
; take.  VERB is the operator's word.
(defun fn-omr-held-line (verb)
  (declare (xargs :guard (stringp verb)))
  (concatenate 'string verb
               " refused reason=owner-holds-the-store: an owner holds the writer lock and answers nothing on its control socket; what it would take: wait for its start or its stop to finish, or stop it"))

; `status --replay': the operator asked for the report over the replayed
; log (books/native-operator.lisp, the status grammar).
(defun fn-omr-status-replayp (result)
  (declare (xargs :guard t))
  (and (member-equal :replay (fn-native-operator-result-arguments result)) t))

; The control socket an accepted operator plan's configuration names, as
; octets (what the client sends the owner's request to); nil otherwise.
(defun fn-omr-control-path-octets (result)
  (declare (xargs :guard t))
  (if (equal (fn-native-operator-result-status result) :accepted)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

; The octets the host reads of a checkpoint file for the stopped report:
; exactly its segment header.
(defun fn-omr-header-octets ()
  (declare (xargs :guard t))
  *fn-scc-segment-header-octets*)

(defthm fn-omr-offline-only-without-an-owner-by-definition
  (iff (equal (fn-omr-route liveness) :offline)
       (and (not (equal liveness :live)) (not (equal liveness :held)))))

; -----------------------------------------------------------------------------
; `recover' on a running owner

(defun fn-omr-recover-status (route)
  (declare (xargs :guard t))
  (cond ((equal route :owner) :accepted)
        ((equal route :held) :refused)
        (t :offline)))

(defun fn-omr-recover-line (route)
  (declare (xargs :guard t))
  (cond ((equal route :owner)
         "recover accepted owner=serving: the owner's open recovered the store and it is serving; nothing to recover; its status follows")
        ((equal route :held)
         "recover refused reason=owner-holds-the-store: an owner holds the writer lock and answers nothing on its control socket; what it would take: wait for its start or its stop to finish, or stop it")
        (t nil)))

; The verb never touches an owner: with a live owner it is a status read
; (accepted), with a held lock a refusal by name; the offline recover runs
; exactly when the route is :offline, where no owner holds the lock.
(defthm fn-omr-recover-is-a-read-or-a-refusal-by-definition
  (and (iff (stringp (fn-omr-recover-line (fn-omr-route liveness)))
            (or (equal liveness :live) (equal liveness :held)))
       (equal (fn-omr-recover-status (fn-omr-route liveness))
              (cond ((equal liveness :live) :accepted)
                    ((equal liveness :held) :refused)
                    (t :offline)))))

; -----------------------------------------------------------------------------
; `store inspect ID' on a running owner

(defun fn-omr-inspect-word (foundp)
  (declare (xargs :guard t))
  (if foundp :found :absent))

(defun fn-omr-inspect-status (word)
  (declare (xargs :guard t))
  (if (equal word :found) :accepted :refused))

; The client's reading of the owner's word (the reasoned reply carries
; fn-nctrl-reason-word's octets).
(defun fn-omr-inspect-foundp (word-octets)
  (declare (xargs :guard t))
  (equal word-octets (fn-nctrl-reason-word :found)))

(defun fn-omr-inspect-live-report (msgid-octets word-octets)
  (declare (xargs :guard t))
  (fn-native-operator-inspect-report msgid-octets (fn-omr-inspect-foundp word-octets)))

; KEYSTONE.  The served read renders as the offline one: for the owner's
; lookup FOUNDP, the report the client prints from the word on the wire is
; fn-native-operator-inspect-report of FOUNDP (exit, verdict and line).  The
; subject is host/native/operator.lisp fnn-operator-execute-inspect's live
; arm, over the word host/native/admin.lisp fnn-owner-inspect-request answers.
(defthm fn-omr-inspect-live-is-the-offline-report
  (equal (fn-omr-inspect-live-report
          msgid-octets (fn-nctrl-reason-word (fn-omr-inspect-word foundp)))
         (fn-native-operator-inspect-report msgid-octets foundp))
  :hints (("Goal" :in-theory (enable fn-native-operator-inspect-report
                                     fn-nop-inspect-verdict))))

; The owner's reply status accepts exactly when the offline verb's exit is 0.
(defthm fn-omr-inspect-status-is-the-offline-exit
  (iff (equal (fn-omr-inspect-status (fn-omr-inspect-word foundp)) :accepted)
       (equal (car (fn-native-operator-inspect-report msgid-octets foundp)) 0)))

; -----------------------------------------------------------------------------
; A stopped store's status from its checkpoint header

; A record frame is its header, its payload and its trailer: never shorter
; than the header and the trailer together.
(defconst *fn-omr-min-frame-octets*
  (+ *fn-frame-header-octets* *fn-frame-trailer-octets*))

; The record count the newest published checkpoint covers: the sequence
; field of its first *fn-scc-segment-header-octets* octets (nothing else of
; the file is read); nil with no checkpoint, or a header that does not parse.
(defun fn-omr-covered-sequence (header)
  (declare (xargs :guard t))
  (let ((h (and (fn-scc-octet-listp header) (fn-scc-parse-header header))))
    (and (consp h) (consp (cdr h)) (consp (cddr h)) (consp (cdddr h))
         (natp (cadddr h))
         (cadddr h))))

(defun fn-omr-transactions-at-most (covered journal-octets)
  (declare (xargs :guard t))
  (+ (nfix covered) (floor (nfix journal-octets) *fn-omr-min-frame-octets*)))

; KEYSTONE.  The bound holds the count: a suffix of R records past the
; covered prefix takes at least R frames' minimum octets of the journal, so
; the stopped report's transactions-at-most is at least COVERED + R.  The
; subject is host/native/io.lisp fnn-command-stopped-report's line.
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-omr-transactions-at-most-bounds-the-count
    (implies (and (natp covered) (natp records) (natp journal-octets)
                  (<= (* records *fn-omr-min-frame-octets*) journal-octets))
             (<= (+ covered records)
                 (fn-omr-transactions-at-most covered journal-octets)))))

(defun fn-omr-stopped-line (covered journal-octets)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nls-text "stopped checkpoint=")
          (if (natp covered) (fn-nls-nat covered) (fn-nls-text "none"))
          (fn-nls-field "journal-octets" (nfix journal-octets))
          (fn-nls-field "transactions-at-most"
                        (fn-omr-transactions-at-most covered journal-octets))
          *fn-nls-lf*))

; The checkpoint file's lstat, (OCTETS MODIFIED) or nil (host/native/io.lisp
; fnn-state-checkpoint-file-observation).
(defun fn-omr-checkpoint-file-words (obs)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp obs) (consp (cdr obs)) (natp (car obs)) (natp (cadr obs)))
      (append (fn-nls-text "checkpoint-file")
              (fn-nls-field "octets" (car obs))
              (fn-nls-field "modified" (cadr obs))
              *fn-nls-lf*)
    (append (fn-nls-text "checkpoint-file none") *fn-nls-lf*)))

; The refusal a stopped report prints when config.json does not open: the
; open's own line for another release's store (fn-spo-refusal-text), else a
; config that does not decode, by name with what it would take.
(defun fn-omr-open-refusal-text (open)
  (declare (xargs :guard t))
  (let ((text (fn-spo-refusal-text open)))
    (if (stringp text)
        text
      "open refused reason=config-unreadable: config.json does not decode as a store profile; what it would take: `recover' names the damage, or restore config.json from a backup")))

; (EXIT OCTETS): the stopped report, or the open's own refusal by name when
; config.json is not this release's store (fn-spo-config-open).
(defun fn-omr-stopped-report (config-octets header journal-octets obs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((open (fn-spo-config-open config-octets)))
    (if (equal (car open) :opened)
        (list 0
              (append (fn-omr-stopped-line (fn-omr-covered-sequence header)
                                           journal-octets)
                      (fn-nls-text "profile")
                      (fn-nls-profile-words (fn-bs-profile-report (cadr open)))
                      *fn-nls-lf*
                      (fn-omr-checkpoint-file-words obs)
                      (fn-nls-text "exact counts: the running owner's status; stopped: `status --replay' (replays the log) or `recover'")
                      *fn-nls-lf*))
      (list 1 (append (fn-nls-text (fn-omr-open-refusal-text open)) *fn-nls-lf*)))))

; `health' on a stopped store: the not-running header (its exit code is the
; header's, fn-nh-report-exit), how the last run ended, then the stopped
; report's lines; nothing replayed.  LAST is the last-run observation
; `fn-nh-last-run-words' takes (nil when the image keeps none).
(defun fn-omr-stopped-health-report (last config-octets header journal-octets obs)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nh-not-running-header)
          (fn-nh-last-run-words last)
          (cadr (fn-omr-stopped-report config-octets header journal-octets obs))))

; The stopped report never replays: its count line is a function of the
; header's sequence and the journal's octets alone.
(defthm fn-omr-stopped-line-is-header-and-octets-by-definition
  (equal (fn-omr-stopped-line covered journal-octets)
         (append (fn-nls-text "stopped checkpoint=")
                 (if (natp covered) (fn-nls-nat covered) (fn-nls-text "none"))
                 (fn-nls-field "journal-octets" (nfix journal-octets))
                 (fn-nls-field "transactions-at-most"
                               (fn-omr-transactions-at-most covered journal-octets))
                 *fn-nls-lf*)))
