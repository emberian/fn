; fn: the operator's health verdict, eight distinct states (PRF-112).
;
; `operator CONFIG health' says which of eight things is wrong, never one red
; bit (the mandate, section 11; PKT-098).  Each state has its own line and its
; own exit code, and each line is a function of the report the operator
; verbs already render (books/native-live-status.lisp): the Store state,
; its persisted profile, the configuration, the retention ledger, the
; running owner's outbound feed table, and one host observation of whether
; the shared Store is fenced.
;
;   0 fenced               the shared Store cannot be served: a clone fence
;                          awaits its rollover, an owner holds the lock and
;                          does not answer on the configured socket, or the
;                          socket answers nothing (`fn-nh-fence-reasonp');
;   1 exhausted            a namespace at its codec ceiling: the transaction
;                          id width or the retention ledger's uint32 count;
;                          no profile can raise either (terminal);
;   2 unqualified-profile  the persisted profile is not format 8, or is the
;                          development profile;
;   3 space-pressure       free headroom below the operator's
;                          [alerts] headroom_min_percent on transactions,
;                          history octets or retention charge (raisable);
;   4 no-route             forwarding obligations held and the configuration
;                          has no BP route (`fn-bprt-table' is empty);
;   5 stranded-transfer    a feed entry dropped at its retry bound: never
;                          offered again without the operator;
;   6 unavailable-peer     an outbound peer with pending work and no open
;                          connection, one that defers this node's
;                          articles, or one whose feed queue is saturated
;                          (PRF-335: every local post then refuses
;                          feed-queue-full);
;   7 receipt-debt         forwarding obligations held, awaiting the receipt
;                          that releases them.
;
; Each state is :held, :clear, or :unobserved (the source was not observed:
; offline there is no feed table; a fenced Store is not opened).  The exit
; code is 20 + the index of the first held state, 19 when none is held and
; some state is unobserved, and 0 when every state is clear
; (`fn-nh-exit-code'); the report's first line carries it and
; `fn-nh-report-exit' reads it back (`fn-nh-report-exit-of-render').
;
; Subjects the host calls (host/native-live-status-host.lisp):
;   fn-nh-offline-report  `fn-native-health-host-offline'
;                         (host/native/operator.lisp fnn-operator-health-offline);
;   fn-nh-health-step and fn-nh-fenced-report  `fn-native-health-host-step'
;                         (fnn-operator-health-report, PKT-454);
;   fn-nh-live-report     through `fn-nh-answer-report',
;                         `fn-native-live-status-host-answer'
;                         (host/native/control.lisp fnn-control-live-status-answer);
;   fn-nh-report-exit     `fn-native-health-host-exit' (fnn-operator-execute-health).
;
; Keystones: fn-nh-verdict-states (each line from the report),
; fn-nh-report-exit-of-render (the exit code the host returns is the
; verdict's), fn-nh-exit-code-decodes (the code names the first held state,
; 0 exactly when all is clear), fn-nh-first-held-monotone (more held states
; never a milder code), fn-nh-pressedp-monotone (more use or a higher
; threshold never clears pressure), fn-nh-live-report-is-the-store-report
; (the owner's words are the offline store's facts with its feed table).
;
; This book owns the prefix `fn-nh-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "native-live-status")
(include-book "outcome-class")
; PKT-220: the offline `store retention' figures.
(include-book "retention-figures")
; PKT-508: the owner's service-log sink, whose counts health prints.
(include-book "log-sink")

(defconst *fn-nh-states*
  '(:fenced :exhausted :unqualified-profile :space-pressure
    :no-route :stranded-transfer :unavailable-peer :receipt-debt))

(defconst *fn-nh-unobserved-exit* 19)
(defconst *fn-nh-first-exit* 20)

(defun fn-nh-nth (i x)
  (declare (xargs :guard (natp i)))
  (if (zp i)
      (if (consp x) (car x) nil)
    (fn-nh-nth (1- i) (if (consp x) (cdr x) nil))))

(defun fn-nh-nat (i x)
  (declare (xargs :guard (natp i)))
  (nfix (fn-nh-nth i x)))

; -----------------------------------------------------------------------------
; Store facts over the status report's headroom
;
; HR is `fn-sbud-headroom-at': (TX-USED TX-BUDGET BYTES-USED HISTORY-BOUND
; CHARGE-RESERVED CHARGE-CAPACITY), the line `status' prints as `headroom'.

(defun fn-nh-pressedp (used bound min)
  "Free headroom below MIN percent of a positive BOUND."
  (declare (xargs :guard t))
  (and (posp bound)
       (< (* 100 (- bound (nfix used))) (* (nfix min) bound))))

(defun fn-nh-exhaustedp (hr)
  "A namespace at its codec ceiling: transaction ids, or the ledger count."
  (declare (xargs :guard t))
  (or (<= *fn-bs-profile-transaction-ceiling* (fn-nh-nat 0 hr))
      (<= *fn-cbor-max-uint* (fn-nh-nat 4 hr))))

(defun fn-nh-space-pressedp (hr min)
  (declare (xargs :guard t))
  (and (not (fn-nh-exhaustedp hr))
       (or (fn-nh-pressedp (fn-nh-nat 0 hr) (fn-nh-nat 1 hr) min)
           (fn-nh-pressedp (fn-nh-nat 2 hr) (fn-nh-nat 3 hr) min)
           (fn-nh-pressedp (fn-nh-nat 4 hr) (fn-nh-nat 5 hr) min))
       t))

(defun fn-nh-profile-fields-equalp (i n a b)
  (declare (xargs :guard (and (natp i) (natp n)) :measure (nfix n)
                  :hints (("Goal" :in-theory (disable fn-bs-profile-field)))
                  :guard-hints (("Goal" :in-theory (disable fn-bs-profile-field)))))
  (if (zp n)
      t
    (and (equal (fn-bs-profile-field i a) (fn-bs-profile-field i b))
         (fn-nh-profile-fields-equalp (1+ i) (1- n) a b))))

(defun fn-nh-development-profilep (profile)
  "Fields 2 to 13 (every bound but the history marker) are the development
profile's."
  (declare (xargs :guard t))
  (fn-nh-profile-fields-equalp 2 12 profile *fn-bs-profile-development*))

(defun fn-nh-unqualifiedp (profile)
  (declare (xargs :guard t))
  (or (not (fn-bs-profile-validp profile))
      (fn-nh-development-profilep profile)))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-nh-forward-count-loop (rev acc)
  (declare (xargs :guard (rationalp acc) :verify-guards nil))
  (if (consp rev)
      (fn-nh-forward-count-loop (cdr rev)
                                (+ (if (and (consp (car rev))
                                            (equal (fn-nh-nth 2 (car rev)) :forward))
                                       1
                                     0)
                                   acc))
    acc))

(defun fn-nh-forward-count (pins)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp pins)
           (+ (if (and (consp (car pins))
                       (equal (fn-nh-nth 2 (car pins)) :forward))
                  1 0)
              (fn-nh-forward-count (cdr pins)))
         0)
       :exec (fn-nh-forward-count-loop (fn-ag-rev-onto pins nil) 0)))

(local
 (defthm fn-nh-forward-count-loop-of-rev-onto
   (equal (fn-nh-forward-count-loop (fn-ag-rev-onto pins zs) 0)
          (fn-nh-forward-count-loop zs (fn-nh-forward-count pins)))
   :hints (("Goal" :induct (fn-ag-rev-onto pins zs)
                   :in-theory (union-theories '(fn-nh-forward-count-loop fn-nh-forward-count fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-nh-forward-count-loop)

(verify-guards fn-nh-forward-count
  :hints (("Goal" :in-theory (union-theories '(fn-nh-forward-count fn-nh-forward-count-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-nh-forward-count-loop-of-rev-onto (zs nil))))))


; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-nh-forward-charge-loop (rev acc)
  (declare (xargs :guard (rationalp acc) :verify-guards nil))
  (if (consp rev)
      (fn-nh-forward-charge-loop (cdr rev)
                                 (+ (if (and (consp (car rev))
                                             (equal (fn-nh-nth 2 (car rev)) :forward))
                                        (fn-nh-nat 4 (car rev))
                                      0)
                                    acc))
    acc))

(defun fn-nh-forward-charge (pins)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp pins)
           (+ (if (and (consp (car pins))
                       (equal (fn-nh-nth 2 (car pins)) :forward))
                  (fn-nh-nat 4 (car pins)) 0)
              (fn-nh-forward-charge (cdr pins)))
         0)
       :exec (fn-nh-forward-charge-loop (fn-ag-rev-onto pins nil) 0)))

(local
 (defthm fn-nh-forward-charge-loop-of-rev-onto
   (equal (fn-nh-forward-charge-loop (fn-ag-rev-onto pins zs) 0)
          (fn-nh-forward-charge-loop zs (fn-nh-forward-charge pins)))
   :hints (("Goal" :induct (fn-ag-rev-onto pins zs)
                   :in-theory (union-theories '(fn-nh-forward-charge-loop fn-nh-forward-charge fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-nh-forward-charge-loop)

(verify-guards fn-nh-forward-charge
  :hints (("Goal" :in-theory (union-theories '(fn-nh-forward-charge fn-nh-forward-charge-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-nh-forward-charge-loop-of-rev-onto (zs nil))))))


(defun fn-nh-forward-pins (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-retain-pins (fn-nls-retention s)))

; -----------------------------------------------------------------------------
; Feed facts over the owner's outbound feed table
;
; TBL is `fn-own-feeds': entries (NAME RECORD FEED), books/owner-feed.lisp.

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-nh-dropped-count-loop (rev acc)
  (declare (xargs :guard (rationalp acc) :verify-guards nil))
  (if (consp rev)
      (fn-nh-dropped-count-loop (cdr rev)
                                (+ (if (equal (fn-feed-entry-state (car rev))
                                              '(:dropped :retry-bound))
                                       1
                                     0)
                                   acc))
    acc))

(defun fn-nh-dropped-count (xs)
  "Entries dropped at their retry bound (`fn-feed-give-up' :retry-bound)."
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp xs)
           (+ (if (equal (fn-feed-entry-state (car xs)) '(:dropped :retry-bound)) 1 0)
              (fn-nh-dropped-count (cdr xs)))
         0)
       :exec (fn-nh-dropped-count-loop (fn-ag-rev-onto xs nil) 0)))

(local
 (defthm fn-nh-dropped-count-loop-of-rev-onto
   (equal (fn-nh-dropped-count-loop (fn-ag-rev-onto xs zs) 0)
          (fn-nh-dropped-count-loop zs (fn-nh-dropped-count xs)))
   :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                   :in-theory (union-theories '(fn-nh-dropped-count-loop fn-nh-dropped-count fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-nh-dropped-count-loop)

(verify-guards fn-nh-dropped-count
  :hints (("Goal" :in-theory (union-theories '(fn-nh-dropped-count fn-nh-dropped-count-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-nh-dropped-count-loop-of-rev-onto (zs nil))))))


(defun fn-nh-feed-pendingp (f)
  (declare (xargs :guard t))
  (and (or (fn-feed-head-queued (fn-feed-queue f))
           (< 0 (fn-feed-inflight-count (fn-feed-queue f))))
       t))

;; PKT-711: entries the peer deferred (431/436: a full Store, a busy or
;; fenced peer) or that a lost connection returned: queued again with an
;; attempt counted.  While any is there the peer is not taking this node's
;; articles, even with a connection open.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-nh-deferred-count-loop (rev acc)
  (declare (xargs :guard (rationalp acc) :verify-guards nil))
  (if (consp rev)
      (fn-nh-deferred-count-loop (cdr rev)
                                 (+ (if (and (equal (fn-feed-entry-state (car rev))
                                                    :queued)
                                             (posp (fn-feed-entry-attempts (car rev))))
                                        1
                                      0)
                                    acc))
    acc))

(defun fn-nh-deferred-count (xs)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp xs)
           (+ (if (and (equal (fn-feed-entry-state (car xs)) :queued)
                       (posp (fn-feed-entry-attempts (car xs))))
                  1 0)
              (fn-nh-deferred-count (cdr xs)))
         0)
       :exec (fn-nh-deferred-count-loop (fn-ag-rev-onto xs nil) 0)))

(local
 (defthm fn-nh-deferred-count-loop-of-rev-onto
   (equal (fn-nh-deferred-count-loop (fn-ag-rev-onto xs zs) 0)
          (fn-nh-deferred-count-loop zs (fn-nh-deferred-count xs)))
   :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                   :in-theory (union-theories '(fn-nh-deferred-count-loop fn-nh-deferred-count fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-nh-deferred-count-loop)

(verify-guards fn-nh-deferred-count
  :hints (("Goal" :in-theory (union-theories '(fn-nh-deferred-count fn-nh-deferred-count-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-nh-deferred-count-loop-of-rev-onto (zs nil))))))


(defun fn-nh-feed-deferredp (f)
  (declare (xargs :guard t))
  (< 0 (fn-nh-deferred-count (fn-feed-queue f))))

;; PRF-335: the queue has no room for another obligation.  The owner's
;; submission intent then answers :capacity for any article this peer is a
;; target of (books/owner-feed.lisp fn-own-feed-target-capacityp), which POST
;; renders as the named feed-queue-full refusal.  The queue holds only
;; undelivered entries, so a saturated peer is one that is behind.
(defun fn-nh-feed-saturatedp (f)
  (declare (xargs :guard t))
  (<= (nfix (fn-feed-max-queue (fn-feed-limits-of f)))
      (len (fn-feed-queue f))))

(defun fn-nh-feed-unavailablep (f)
  (declare (xargs :guard t))
  (or (and (fn-nh-feed-pendingp f)
           (not (natp (fn-feed-conn f))))
      (fn-nh-feed-deferredp f)
      (fn-nh-feed-saturatedp f)))

(defun fn-nh-saturated-total (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (+ (if (fn-nh-feed-saturatedp (fn-own-feed-entry-feed (car tbl))) 1 0)
         (fn-nh-saturated-total (cdr tbl)))
    0))

(defun fn-nh-stranded-peers (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (if (< 0 (fn-nh-dropped-count
                (fn-feed-queue (fn-own-feed-entry-feed (car tbl)))))
          (cons (fn-own-feed-entry-name (car tbl))
                (fn-nh-stranded-peers (cdr tbl)))
        (fn-nh-stranded-peers (cdr tbl)))
    nil))

(defun fn-nh-stranded-count (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (+ (fn-nh-dropped-count (fn-feed-queue (fn-own-feed-entry-feed (car tbl))))
         (fn-nh-stranded-count (cdr tbl)))
    0))

(defun fn-nh-deferred-total (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (+ (fn-nh-deferred-count (fn-feed-queue (fn-own-feed-entry-feed (car tbl))))
         (fn-nh-deferred-total (cdr tbl)))
    0))

(defun fn-nh-unavailable-peers (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (if (fn-nh-feed-unavailablep (fn-own-feed-entry-feed (car tbl)))
          (cons (fn-own-feed-entry-name (car tbl))
                (fn-nh-unavailable-peers (cdr tbl)))
        (fn-nh-unavailable-peers (cdr tbl)))
    nil))

; -----------------------------------------------------------------------------
; Fence reasons: what the host observed before it could open the Store

(defun fn-nh-fence-reasonp (x)
  (declare (xargs :guard t))
  (and (member-equal x '(:clone-fence :starting :store-held :owner-unanswering)) t))

; The host's observations, in the order it takes them (host/native/operator.lisp
; fnn-operator-health-report): whether the control socket answered (ROUTE,
; `fn-nls-route'), the writer lock (`fnn-store-owner-observation': :held
; :free :absent :unknown), whether the clone fence file exists, and whether
; an owner would listen at all (LISTENER-EXPECTED: the configuration names a
; control socket and the image has one).  An owner that answered is not
; fenced.  A process that holds the lock where an owner would listen and
; nothing answers yet is :starting (PKT-283): an owner between taking the
; lock and listening, recovering its Store, or an offline command holding it;
; with no listener to expect, or a lock the probe could not read, it is
; :store-held.
(defun fn-nh-fence-of (route lock clone-fence-present listener-expected)
  (declare (xargs :guard t))
  (cond ((equal route :uncertain) :owner-unanswering)
        (clone-fence-present :clone-fence)
        ((and (equal lock :held) listener-expected) :starting)
        ((member-equal lock '(:held :unknown)) :store-held)
        (t nil)))

; -----------------------------------------------------------------------------
; Words

(defun fn-nh-state-word (name)
  (declare (xargs :guard t))
  (cond ((equal name :fenced) "fenced")
        ((equal name :exhausted) "exhausted")
        ((equal name :unqualified-profile) "unqualified-profile")
        ((equal name :space-pressure) "space-pressure")
        ((equal name :no-route) "no-route")
        ((equal name :stranded-transfer) "stranded-transfer")
        ((equal name :unavailable-peer) "unavailable-peer")
        ((equal name :receipt-debt) "receipt-debt")
        (t "healthy")))

(defun fn-nh-pair (name used bound)
  (declare (xargs :guard t))
  (append (fn-nls-text " ") (fn-nls-text name) (fn-nls-text "=")
          (fn-nls-nat used) (fn-nls-text "/") (fn-nls-nat bound)))

(defun fn-nh-headroom-words (hr min)
  (declare (xargs :guard t))
  (append (fn-nh-pair "transactions" (fn-nh-nat 0 hr) (fn-nh-nat 1 hr))
          (fn-nh-pair "history-octets" (fn-nh-nat 2 hr) (fn-nh-nat 3 hr))
          (fn-nh-pair "charge" (fn-nh-nat 4 hr) (fn-nh-nat 5 hr))
          (fn-nls-field "min-free-percent" (nfix min))))

(defun fn-nh-profile-words (profile)
  (declare (xargs :guard t))
  ;; The store's own format: 10 (the one format an image opens) for a
  ;; valid profile, 0 otherwise.
  (append (fn-nls-field "format" (if (fn-bs-profile-validp profile) 10 0))
          (if (fn-nh-development-profilep profile)
              (fn-nls-text " development")
            nil)))

(defun fn-nh-name-list-words (names)
  (declare (xargs :guard t))
  (if (consp names)
      (append (fn-nls-text " ")
              (if (stringp (car names)) (fn-nls-text (car names)) (fn-nls-text "?"))
              (fn-nh-name-list-words (cdr names)))
    nil))

(defun fn-nh-fence-words (reason)
  (declare (xargs :guard t))
  (cond ((equal reason :clone-fence)
         (fn-nls-text " reason=clone-fence (a clone awaits its incarnation rollover)"))
        ((equal reason :starting)
         (fn-nls-text " reason=starting (a process holds the store lock and nothing answers on the control socket yet: an owner starting or recovering, or an offline command; retry)"))
        ((equal reason :store-held)
         (fn-nls-text " reason=store-held (a process holds the store and the configured control socket does not reach it)"))
        ((equal reason :owner-unanswering)
         (fn-nls-text " reason=owner-unanswering (the control socket accepted and did not answer)"))
        (t (fn-nls-text " reason=unknown"))))

; -----------------------------------------------------------------------------
; The verdict: eight (OUTCOME . WORDS), in `*fn-nh-states*' order

(defun fn-nh-outcome (heldp words)
  (declare (xargs :guard t))
  (if heldp (cons :held words) (cons :clear nil)))

(defconst *fn-nh-no-store*
  (cons :unobserved (fn-record-string-octets " (the store was not opened)")))
(defconst *fn-nh-no-owner*
  (cons :unobserved (fn-record-string-octets " (no running owner: the feed table lives in the owner)")))

;; STORE is (PROFILE S BYTES CFG), or nil when the Store was not opened.
;; FEEDS is the owner's feed table, or :unobserved.  FENCE is a reason or nil.
(defun fn-nh-store-hr (store)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sbud-headroom-at (fn-nh-nth 0 store) (fn-nh-nth 1 store) (fn-nh-nth 2 store)))

(defun fn-nh-store-debt (store)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nh-forward-count (fn-nh-forward-pins (fn-nh-nth 1 store))))

(defun fn-nh-o-fenced (fence)
  (declare (xargs :guard t))
  (fn-nh-outcome fence (fn-nh-fence-words fence)))

(defun fn-nh-o-exhausted (store min)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp store)
      (fn-nh-outcome (fn-nh-exhaustedp (fn-nh-store-hr store))
                     (fn-nh-headroom-words (fn-nh-store-hr store) min))
    *fn-nh-no-store*))

(defun fn-nh-o-unqualified (store)
  (declare (xargs :guard t))
  (if (consp store)
      (fn-nh-outcome (fn-nh-unqualifiedp (fn-nh-nth 0 store))
                     (fn-nh-profile-words (fn-nh-nth 0 store)))
    *fn-nh-no-store*))

(defun fn-nh-o-pressure (store min)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp store)
      (fn-nh-outcome (fn-nh-space-pressedp (fn-nh-store-hr store) min)
                     (fn-nh-headroom-words (fn-nh-store-hr store) min))
    *fn-nh-no-store*))

(defun fn-nh-o-no-route (store)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp store)
      (fn-nh-outcome (and (posp (fn-nh-store-debt store))
                          (null (fn-bprt-table (fn-nh-nth 3 store))))
                     (fn-nls-field "forward-obligations" (fn-nh-store-debt store)))
    *fn-nh-no-store*))

(defun fn-nh-o-stranded (feeds)
  (declare (xargs :guard t))
  (if (equal feeds :unobserved)
      *fn-nh-no-owner*
    (fn-nh-outcome (consp (fn-nh-stranded-peers feeds))
                   (append (fn-nls-field "dropped" (fn-nh-stranded-count feeds))
                           (fn-nls-text " peers:")
                           (fn-nh-name-list-words (fn-nh-stranded-peers feeds))))))

(defun fn-nh-o-unavailable (feeds)
  (declare (xargs :guard t))
  (if (equal feeds :unobserved)
      *fn-nh-no-owner*
    (fn-nh-outcome (consp (fn-nh-unavailable-peers feeds))
                   (append (fn-nls-field "deferred" (fn-nh-deferred-total feeds))
                           (fn-nls-field "saturated" (fn-nh-saturated-total feeds))
                           (fn-nls-text " peers:")
                           (fn-nh-name-list-words (fn-nh-unavailable-peers feeds))))))

(defun fn-nh-o-debt (store)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp store)
      (fn-nh-outcome (posp (fn-nh-store-debt store))
                     (append (fn-nls-field "forward-obligations" (fn-nh-store-debt store))
                             (fn-nls-field "charge"
                                           (fn-nh-forward-charge
                                            (fn-nh-forward-pins (fn-nh-nth 1 store))))))
    *fn-nh-no-store*))

(defun fn-nh-verdict (fence store min feeds)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-nh-o-fenced fence)
        (fn-nh-o-exhausted store min)
        (fn-nh-o-unqualified store)
        (fn-nh-o-pressure store min)
        (fn-nh-o-no-route store)
        (fn-nh-o-stranded feeds)
        (fn-nh-o-unavailable feeds)
        (fn-nh-o-debt store)))

; -----------------------------------------------------------------------------
; The exit code

(defun fn-nh-first-held-index (v i)
  (declare (xargs :guard (natp i)))
  (if (consp v)
      (if (and (consp (car v)) (equal (car (car v)) :held))
          (nfix i)
        (fn-nh-first-held-index (cdr v) (1+ (nfix i))))
    nil))

(defun fn-nh-any-unobservedp (v)
  (declare (xargs :guard t))
  (if (consp v)
      (or (and (consp (car v)) (equal (car (car v)) :unobserved))
          (fn-nh-any-unobservedp (cdr v)))
    nil))

(defun fn-nh-exit-code (v)
  (declare (xargs :guard t))
  (let ((i (fn-nh-first-held-index v 0)))
    (cond ((natp i) (+ *fn-nh-first-exit* i))
          ((fn-nh-any-unobservedp v) *fn-nh-unobserved-exit*)
          (t 0))))

(defun fn-nh-code-state (code)
  "The state an exit code names; nil for 0 and 19."
  (declare (xargs :guard t))
  (if (and (natp code) (<= *fn-nh-first-exit* code) (< code 28))
      (fn-nh-nth (- code *fn-nh-first-exit*) *fn-nh-states*)
    nil))

(defun fn-nh-first-held (v)
  (declare (xargs :guard t))
  (let ((i (fn-nh-first-held-index v 0)))
    (if (natp i) (fn-nh-nth i *fn-nh-states*) nil)))

(defun fn-nh-outcomes-okp (v)
  (declare (xargs :guard t))
  (if (consp v)
      (and (consp (car v))
           (member-equal (car (car v)) '(:held :clear :unobserved))
           (fn-nh-outcomes-okp (cdr v)))
    t))

(defun fn-nh-verdict-shapep (v)
  "Eight outcomes, each :held, :clear or :unobserved."
  (declare (xargs :guard t))
  (and (true-listp v) (equal (len v) 8)
       (fn-nh-outcomes-okp v)
       t))

; -----------------------------------------------------------------------------
; Rendering

(defconst *fn-nh-exit-prefix* (fn-record-string-octets "health exit="))

(defun fn-nh-exit-prefix ()
  (declare (xargs :guard t))
  *fn-nh-exit-prefix*)

(defun fn-nh-digit2 (code)
  (declare (xargs :guard t))
  (let ((c (nfix code)))
    (list (+ 48 (floor (mod c 100) 10)) (+ 48 (mod c 10)))))

; When the first held state is the fence, the header also carries its
; reason, so the first line an operator reads says `starting' (or which other
; fence) rather than only `fenced' (PKT-283).
(defun fn-nh-header-reason (v)
  (declare (xargs :guard t))
  (if (and (equal (fn-nh-first-held v) :fenced)
           (consp v) (consp (car v)) (true-listp (cdr (car v))))
      (cdr (car v))
    nil))

(defun fn-nh-header (v)
  (declare (xargs :guard t))
  (append (fn-nh-exit-prefix) (fn-nh-digit2 (fn-nh-exit-code v))
          (fn-nls-text " state=")
          (fn-nls-text (if (and (not (fn-nh-first-held v)) (fn-nh-any-unobservedp v))
                           "none-held (some states unobserved)"
                         (fn-nh-state-word (fn-nh-first-held v))))
          (fn-nh-header-reason v)
          *fn-nls-lf*))

(defun fn-nh-outcome-word (o)
  (declare (xargs :guard t))
  (cond ((and (consp o) (equal (car o) :held)) "held")
        ((and (consp o) (equal (car o) :unobserved)) "unobserved")
        (t "clear")))

(defun fn-nh-lines (v names)
  (declare (xargs :guard t))
  (if (and (consp v) (consp names))
      (append (fn-nls-text (fn-nh-state-word (car names)))
              (fn-nls-text " ")
              (fn-nls-text (fn-nh-outcome-word (car v)))
              (if (and (consp (car v)) (true-listp (cdr (car v))))
                  (cdr (car v))
                nil)
              *fn-nls-lf*
              (fn-nh-lines (cdr v) (cdr names)))
    nil))

(defun fn-nh-render (v)
  (declare (xargs :guard t))
  (append (fn-nh-header v) (fn-nh-lines v *fn-nh-states*)))

(defun fn-nh-digit-value (d)
  (declare (xargs :guard t))
  (if (and (natp d) (<= 48 d) (<= d 57)) (- d 48) nil))

(defun fn-nh-report-exit (octets)
  "The exit code on the report's first line, or :malformed."
  (declare (xargs :guard t))
  (let ((a (fn-nh-digit-value (fn-nh-nth 12 octets)))
        (b (fn-nh-digit-value (fn-nh-nth 13 octets))))
    (if (and (true-listp octets)
             (equal (take 12 octets) (fn-nh-exit-prefix))
             a b)
        (+ (* 10 a) b)
      :malformed)))

; -----------------------------------------------------------------------------
; The three reports the host prints

(defun fn-nh-store-inputs (profile s bytes cfg)
  (declare (xargs :guard t))
  (list profile s bytes cfg))

(defun fn-nh-offline-report (profile s cfg min)
  "No owner is running and the Store opened: its facts, no feed table."
  (declare (xargs :guard t :verify-guards nil))
  (fn-nh-render (fn-nh-verdict nil (fn-nh-store-inputs profile s (fn-sbud-bytes-used s) cfg)
                               min :unobserved)))

(defun fn-nh-fenced-report (reason)
  "The Store was not opened because it is fenced: only the fence is observed."
  (declare (xargs :guard t :verify-guards nil))
  (fn-nh-render (fn-nh-verdict reason nil 0 :unobserved)))

(defun fn-nh-live-report (profile oc cache min)
  "The running owner's words over what it carries: its Store, configuration
and feed table, with the committed octets extended from the carried sum."
  (declare (xargs :guard t :verify-guards nil))
  (let ((s (fn-own-store (fn-ocfg-owner oc))))
    (fn-nh-render
     (fn-nh-verdict nil
                    (fn-nh-store-inputs
                     profile s (fn-sbud-bytes-extend cache (fn-sf-records (fn-sn-files s)))
                     (fn-ocfg-config oc))
                    min (fn-own-feeds (fn-ocfg-owner oc))))))

; What the owner renders for an FNLS request: the health report for :health,
; the status report of books/native-live-status.lisp otherwise.
(defun fn-nh-answer-report (kind profile oc cache obs min fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (equal kind :health)
      (fn-nh-live-report profile oc cache min)
    (fn-nls-live-report kind profile oc cache obs fn-arena)))

; -----------------------------------------------------------------------------
; Theorems

; KEYSTONE (each line from the report).  The subject is `fn-nh-verdict', which
; every report above renders.  It has eight outcomes, one per state in
; `*fn-nh-states*' order, and each is decided by the report's own values:
; the fence the host observed; the headroom `status' prints (exhausted,
; space pressure); the persisted profile (unqualified); the retention
; ledger's forwarding obligations and the configuration's BP route table (no
; route, receipt debt); the owner's feed table (stranded transfer,
; unavailable peer).  A source not observed is :unobserved, never :clear.
(local
 (defthm fn-nh-outcome-car
   (equal (car (fn-nh-outcome heldp words)) (if heldp :held :clear))))

(local
 (defthm fn-nh-outcome-consp
   (consp (fn-nh-outcome heldp words))))

(local (in-theory (disable fn-nh-outcome fn-nh-store-hr fn-nh-store-debt
                           fn-nh-exhaustedp fn-nh-space-pressedp fn-nh-unqualifiedp
                           fn-bprt-table fn-nh-stranded-peers fn-nh-unavailable-peers
                           fn-nh-fence-words fn-nh-headroom-words fn-nh-profile-words
                           fn-nls-field fn-nls-text fn-nh-name-list-words)))
(local
 (defthm fn-nh-o-fenced-car
   (and (consp (fn-nh-o-fenced fence))
        (equal (car (fn-nh-o-fenced fence)) (if fence :held :clear)))
   :hints (("Goal" :in-theory (enable fn-nh-o-fenced)))))
(local
 (defthm fn-nh-o-exhausted-car
   (and (consp (fn-nh-o-exhausted store min))
        (equal (car (fn-nh-o-exhausted store min)) (cond ((atom store) :unobserved) ((fn-nh-exhaustedp (fn-nh-store-hr store)) :held) (t :clear))))
   :hints (("Goal" :in-theory (enable fn-nh-o-exhausted)))))
(local
 (defthm fn-nh-o-unqualified-car
   (and (consp (fn-nh-o-unqualified store))
        (equal (car (fn-nh-o-unqualified store)) (cond ((atom store) :unobserved) ((fn-nh-unqualifiedp (fn-nh-nth 0 store)) :held) (t :clear))))
   :hints (("Goal" :in-theory (enable fn-nh-o-unqualified)))))
(local
 (defthm fn-nh-o-pressure-car
   (and (consp (fn-nh-o-pressure store min))
        (equal (car (fn-nh-o-pressure store min)) (cond ((atom store) :unobserved) ((fn-nh-space-pressedp (fn-nh-store-hr store) min) :held) (t :clear))))
   :hints (("Goal" :in-theory (enable fn-nh-o-pressure)))))
(local
 (defthm fn-nh-o-no-route-car
   (and (consp (fn-nh-o-no-route store))
        (equal (car (fn-nh-o-no-route store)) (cond ((atom store) :unobserved) ((and (posp (fn-nh-store-debt store)) (null (fn-bprt-table (fn-nh-nth 3 store)))) :held) (t :clear))))
   :hints (("Goal" :in-theory (enable fn-nh-o-no-route)))))
(local
 (defthm fn-nh-o-stranded-car
   (and (consp (fn-nh-o-stranded feeds))
        (equal (car (fn-nh-o-stranded feeds)) (cond ((equal feeds :unobserved) :unobserved) ((consp (fn-nh-stranded-peers feeds)) :held) (t :clear))))
   :hints (("Goal" :in-theory (enable fn-nh-o-stranded)))))
(local
 (defthm fn-nh-o-unavailable-car
   (and (consp (fn-nh-o-unavailable feeds))
        (equal (car (fn-nh-o-unavailable feeds)) (cond ((equal feeds :unobserved) :unobserved) ((consp (fn-nh-unavailable-peers feeds)) :held) (t :clear))))
   :hints (("Goal" :in-theory (enable fn-nh-o-unavailable)))))
(local
 (defthm fn-nh-o-debt-car
   (and (consp (fn-nh-o-debt store))
        (equal (car (fn-nh-o-debt store)) (cond ((atom store) :unobserved) ((posp (fn-nh-store-debt store)) :held) (t :clear))))
   :hints (("Goal" :in-theory (enable fn-nh-o-debt)))))

(defthm fn-nh-verdict-states
  (let ((v (fn-nh-verdict fence store min feeds))
        (hr (fn-nh-store-hr store))
        (debt (fn-nh-store-debt store)))
    (and (fn-nh-verdict-shapep v)
         (equal (car (fn-nh-nth 0 v)) (if fence :held :clear))
         (equal (car (fn-nh-nth 1 v))
                (cond ((atom store) :unobserved)
                      ((fn-nh-exhaustedp hr) :held)
                      (t :clear)))
         (equal (car (fn-nh-nth 2 v))
                (cond ((atom store) :unobserved)
                      ((fn-nh-unqualifiedp (fn-nh-nth 0 store)) :held)
                      (t :clear)))
         (equal (car (fn-nh-nth 3 v))
                (cond ((atom store) :unobserved)
                      ((fn-nh-space-pressedp hr min) :held)
                      (t :clear)))
         (equal (car (fn-nh-nth 4 v))
                (cond ((atom store) :unobserved)
                      ((and (posp debt) (null (fn-bprt-table (fn-nh-nth 3 store)))) :held)
                      (t :clear)))
         (equal (car (fn-nh-nth 5 v))
                (cond ((equal feeds :unobserved) :unobserved)
                      ((consp (fn-nh-stranded-peers feeds)) :held)
                      (t :clear)))
         (equal (car (fn-nh-nth 6 v))
                (cond ((equal feeds :unobserved) :unobserved)
                      ((consp (fn-nh-unavailable-peers feeds)) :held)
                      (t :clear)))
         (equal (car (fn-nh-nth 7 v))
                (cond ((atom store) :unobserved)
                      ((posp debt) :held)
                      (t :clear)))))
  :hints (("Goal" :in-theory (e/d (fn-nh-verdict fn-nh-verdict-shapep fn-nh-outcomes-okp)
                                  (fn-nh-o-fenced fn-nh-o-exhausted fn-nh-o-unqualified
                                   fn-nh-o-pressure fn-nh-o-no-route fn-nh-o-stranded
                                   fn-nh-o-unavailable fn-nh-o-debt)))))

;; KEYSTONE (PKT-711).  While a peer defers any of this node's articles (a
;; full Store answers 436), `health' holds unavailable-peer: the node is
;; never reported healthy while a peer is not taking its articles.  Host:
;; host/native-live-status-host.lisp's live health report renders
;; fn-nh-verdict over the owner's feed table.
(local
 (defthm fn-nh-unavailable-peers-of-a-deferring-member
   (implies (and (member-equal e tbl)
                 (fn-nh-feed-deferredp (fn-own-feed-entry-feed e)))
            (consp (fn-nh-unavailable-peers tbl)))
   :hints (("Goal" :induct (fn-nh-unavailable-peers tbl)
            :in-theory (e/d (fn-nh-unavailable-peers fn-nh-feed-unavailablep)
                            (fn-nh-feed-deferredp))))))

(defthm fn-nh-deferring-peer-is-held
  (implies (and (member-equal e feeds)
                (fn-nh-feed-deferredp (fn-own-feed-entry-feed e)))
           (equal (car (fn-nh-nth 6 (fn-nh-verdict fence store min feeds))) :held))
  :hints (("Goal" :in-theory (disable fn-nh-verdict fn-nh-feed-deferredp fn-nh-nth)
           :use ((:instance fn-nh-verdict-states)))))

;; KEYSTONE (PRF-335).  When the owner refuses a submission because a target
;; peer's feed queue has no room (`fn-own-feed-target-capacityp' false: the
;; intent answers :capacity, POST answers feed-queue-full), `health' holds
;; unavailable-peer.  Before PRF-335 the queue filled with delivered entries
;; and health said healthy while every post was refused
;; (the openbsd-rehearsal record of 2026-09-27, stop 1).  NAMES are
;; the submission's targets; each has an entry in the table
;; (books/owner-feed.lisp `fn-own-feed-target-has-an-entry').
(defun fn-nh-names-have-entriesp (names tbl)
  (declare (xargs :guard t))
  (if (consp names)
      (and (fn-own-feed-entry-of (car names) tbl)
           (fn-nh-names-have-entriesp (cdr names) tbl))
    t))

(local
 (defthm fn-nh-entry-of-is-a-member
   (implies (fn-own-feed-entry-of p tbl)
            (member-equal (fn-own-feed-entry-of p tbl) tbl))
   :hints (("Goal" :in-theory (enable fn-own-feed-entry-of)))))

;; The first target without room: its entry is in the table and its feed is
;; saturated.
(defun fn-nh-full-target (names tbl msgid)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((f (fn-own-feed-find (car names) tbl)))
        (if (or (consp (fn-feed-find msgid (fn-feed-queue f)))
                (< (len (fn-feed-queue f))
                   (nfix (fn-feed-max-queue (fn-feed-limits-of f)))))
            (fn-nh-full-target (cdr names) tbl msgid)
          (car names)))
    nil))

(local
 (defthm fn-nh-full-target-is-saturated
   (implies (and (fn-nh-names-have-entriesp names tbl)
                 (not (fn-own-feed-target-capacityp names tbl msgid)))
            (and (fn-own-feed-entry-of (fn-nh-full-target names tbl msgid) tbl)
                 (fn-nh-feed-saturatedp
                  (fn-own-feed-entry-feed
                   (fn-own-feed-entry-of (fn-nh-full-target names tbl msgid) tbl)))))
   :hints (("Goal" :in-theory (e/d (fn-own-feed-target-capacityp fn-own-feed-find)
                                   (fn-own-feed-entry-of))))))

(local
 (defthm fn-nh-unavailable-peers-of-a-saturated-member
   (implies (and (member-equal e tbl)
                 (fn-nh-feed-saturatedp (fn-own-feed-entry-feed e)))
            (consp (fn-nh-unavailable-peers tbl)))
   :hints (("Goal" :induct (fn-nh-unavailable-peers tbl)
            :in-theory (e/d (fn-nh-unavailable-peers fn-nh-feed-unavailablep)
                            (fn-nh-feed-saturatedp fn-nh-feed-deferredp))))))

(defthm fn-nh-saturated-peer-is-held
  (implies (and (member-equal e feeds)
                (fn-nh-feed-saturatedp (fn-own-feed-entry-feed e)))
           (equal (car (fn-nh-nth 6 (fn-nh-verdict fence store min feeds))) :held))
  :hints (("Goal" :in-theory (disable fn-nh-verdict fn-nh-feed-saturatedp fn-nh-nth)
           :use ((:instance fn-nh-verdict-states)))))

(defthm fn-nh-feed-queue-refusal-is-held
  (implies (and (fn-nh-names-have-entriesp names feeds)
                (not (fn-own-feed-target-capacityp names feeds msgid)))
           (equal (car (fn-nh-nth 6 (fn-nh-verdict fence store min feeds))) :held))
  :hints (("Goal" :use ((:instance fn-nh-full-target-is-saturated (tbl feeds))
                        (:instance fn-nh-saturated-peer-is-held
                                   (e (fn-own-feed-entry-of
                                       (fn-nh-full-target names feeds msgid) feeds))))
           :in-theory (disable fn-nh-full-target-is-saturated
                               fn-nh-saturated-peer-is-held
                               fn-nh-verdict fn-nh-nth fn-nh-feed-saturatedp
                               fn-own-feed-target-capacityp fn-nh-full-target
                               fn-own-feed-entry-of))))

;; The owner-level form, over the function the host calls for the intent
;; (host/owner-host.lisp fn-owner-submission-intent, through
;; fn-icar-submission-intent's reference `fn-own-submission-intent-result'):
;; a :capacity intent -- the feed-queue-full refusal -- holds
;; unavailable-peer in the running owner's health over the same table.
(local
 (defthm fn-nh-subsetp-cons
   (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(local
 (defthm fn-nh-subsetp-reflexive
   (subsetp-equal x x)))

(local
 (defthm fn-nh-feed-targets-have-entries
   (implies (and (fn-own-feed-tablep tbl)
                 (subsetp-equal names (fn-own-feed-targets tbl origin groups path)))
            (fn-nh-names-have-entriesp names tbl))
   :hints (("Goal" :induct (fn-nh-names-have-entriesp names tbl)
            :in-theory (disable fn-own-feed-targets fn-own-feed-tablep
                                fn-own-feed-entry-of)))))

(local
 (defthm fn-nh-distribution-targets-have-entries
   (implies (fn-nh-names-have-entriesp names tbl)
            (fn-nh-names-have-entriesp
             (fn-own-feed-distribution-targets names tbl dists) tbl))
   :hints (("Goal" :in-theory (e/d (fn-own-feed-distribution-targets)
                                   (fn-own-feed-distribution-admitsp
                                    fn-own-feed-dists-of fn-own-feed-entry-of))))))

(local
 (defthm fn-nh-new-targets-have-entries
   (implies (fn-nh-names-have-entriesp names tbl)
            (fn-nh-names-have-entriesp
             (fn-own-feed-new-targets names tbl msgid) tbl))
   :hints (("Goal" :in-theory (e/d (fn-own-feed-new-targets)
                                   (fn-own-feed-find fn-own-feed-entry-of))))))

(local
 (defthm fn-nh-names-have-entriesp-of-atom
   (implies (atom names) (fn-nh-names-have-entriesp names tbl))))

(local
 (defthm fn-nh-new-targets-of-atom
   (implies (atom names) (equal (fn-own-feed-new-targets names tbl msgid) nil))
   :hints (("Goal" :in-theory (enable fn-own-feed-new-targets)))))

(local
 (defthm fn-nh-submission-targets-have-entries
   (implies (fn-own-feed-tablep (fn-own-feeds o))
            (fn-nh-names-have-entriesp (fn-own-submission-targets o)
                                       (fn-own-feeds o)))
   :hints (("Goal" :in-theory (e/d (fn-own-submission-targets)
                                   (fn-own-feed-targets fn-own-feed-tablep
                                    fn-own-feed-distribution-targets
                                    fn-own-feed-new-targets
                                    fn-nh-names-have-entriesp))
            :use ((:instance fn-nh-feed-targets-have-entries
                             (tbl (fn-own-feeds o))
                             (names (fn-own-feed-targets
                                     (fn-own-feeds o)
                                     (fn-own-sub-origin (fn-own-inflight o))
                                     (fn-own-sub-feed-groups (fn-own-inflight o))
                                     (fn-own-feed-path-of
                                      (fn-own-sub-octets (fn-own-inflight o)))))
                             (origin (fn-own-sub-origin (fn-own-inflight o)))
                             (groups (fn-own-sub-feed-groups (fn-own-inflight o)))
                             (path (fn-own-feed-path-of
                                    (fn-own-sub-octets (fn-own-inflight o))))))))))

(defthm fn-nh-feed-queue-full-intent-is-held
  (implies (and (fn-own-feed-tablep (fn-own-feeds o))
                (equal (fn-own-submission-intent-result o evidence generation txid)
                       :capacity))
           (equal (car (fn-nh-nth 6 (fn-nh-verdict fence store min (fn-own-feeds o))))
                  :held))
  :hints (("Goal" :use ((:instance fn-nh-feed-queue-refusal-is-held
                                   (names (fn-own-submission-targets o))
                                   (feeds (fn-own-feeds o))
                                   (msgid (fn-own-sub-msgid (fn-own-inflight o))))
                        (:instance fn-nh-submission-targets-have-entries))
           :in-theory (e/d (fn-own-submission-intent-result)
                           (fn-nh-feed-queue-refusal-is-held
                            fn-nh-submission-targets-have-entries
                            fn-own-submission-targets fn-own-feed-tablep
                            fn-nh-verdict fn-nh-nth fn-own-feed-target-capacityp
                            fn-nh-names-have-entriesp)))))

(local
 (defthm fn-nh-first-held-index-bounds
   (implies (and (natp i) (fn-nh-first-held-index v i))
            (and (natp (fn-nh-first-held-index v i))
                 (<= i (fn-nh-first-held-index v i))
                 (< (fn-nh-first-held-index v i) (+ i (len v)))))
   :rule-classes nil))

; The scale (PKT-329).  For every verdict of at most eight outcomes (the
; verdict has exactly eight: fn-nh-verdict-states) the code is 0, 19, or
; 20..27.
(defthm fn-nh-exit-code-cases
  (implies (<= (len v) 8)
           (member-equal (fn-nh-exit-code v) '(0 19 20 21 22 23 24 25 26 27)))
  :hints (("Goal" :use ((:instance fn-nh-first-held-index-bounds (i 0)))
           :in-theory (disable fn-nh-first-held-index))))

; KEYSTONE (health's scale is the one exception, and it never overlaps the
; outcome codes; PKT-329, specs/host.md "CLI exit codes").  The subject is
; `fn-nh-exit-code', whose value the host returns: `fnn-operator-execute-health'
; (host/native/operator.lisp) returns `fn-native-health-host-exit' of the
; report, which is this code (fn-nh-report-exit-of-render).  For EVERY V, not
; only a well-shaped verdict: the code is 0 or at least 19, and it is one of
; the seven outcome codes of `*fn-outcome-codes*' (books/outcome-class.lisp)
; exactly when it is 0, the code of :accepted.  The theorem reads the table
; through `fn-outcome-codep', so a new outcome code at 19 or above makes it
; fail: the two tables cannot drift apart.
(defthm fn-nh-exit-code-is-zero-or-past-the-outcome-codes
  (and (or (equal (fn-nh-exit-code v) 0)
           (<= 19 (fn-nh-exit-code v)))
       (iff (fn-outcome-codep (fn-nh-exit-code v))
            (equal (fn-nh-exit-code v) (fn-outcome-code :accepted))))
  :hints (("Goal" :in-theory (enable fn-nh-exit-code fn-outcome-codep))))

; KEYSTONE (the code names the state).  For every verdict of at most eight
; outcomes (the verdict has exactly eight: fn-nh-verdict-states), the exit
; code the host returns names the first held state in `*fn-nh-states*' order,
; and it is 0 exactly when no state is held and none is unobserved.
(defthm fn-nh-exit-code-decodes
  (implies (<= (len v) 8)
           (and (equal (fn-nh-code-state (fn-nh-exit-code v)) (fn-nh-first-held v))
                (iff (equal (fn-nh-exit-code v) 0)
                     (and (not (fn-nh-first-held-index v 0))
                          (not (fn-nh-any-unobservedp v))))))
  :hints (("Goal" :use ((:instance fn-nh-first-held-index-bounds (i 0)))
            :in-theory (e/d (fn-nh-first-held fn-nh-code-state fn-nh-exit-code)
                            (fn-nh-first-held-index fn-nh-any-unobservedp)))))

(local
 (defthm fn-nh-take-len-append
   (implies (true-listp a)
            (equal (take (len a) (append a b)) a))))

(local
 (defthm fn-nh-take-12-append
   (implies (and (true-listp a) (equal (len a) 12))
            (equal (take 12 (append a b)) a))
   :hints (("Goal" :use fn-nh-take-len-append
            :in-theory (disable fn-nh-take-len-append)))))

(local
 (defthm fn-nh-nth-append-past
   (implies (and (natp i) (true-listp a) (<= (len a) i))
            (equal (fn-nh-nth i (append a b)) (fn-nh-nth (- i (len a)) b)))
   :hints (("Goal" :induct (fn-nh-nth i a) :in-theory (enable fn-nh-nth)))))

(local
 (defthm fn-nh-nth-append-within
   (implies (and (natp i) (< i (len a)))
            (equal (fn-nh-nth i (append a b)) (fn-nh-nth i a)))
   :hints (("Goal" :induct (fn-nh-nth i a) :in-theory (enable fn-nh-nth)))))

(local
 (defthm fn-nh-report-exit-of-code
   (implies (and (member-equal c '(0 19 20 21 22 23 24 25 26 27))
                 (true-listp rest))
            (equal (fn-nh-report-exit
                    (append (fn-nh-exit-prefix) (append (fn-nh-digit2 c) rest)))
                   c))
   :hints (("Goal" :in-theory (enable fn-nh-report-exit fn-nh-digit-value fn-nh-nth
                                      fn-nh-exit-prefix)
            :do-not-induct t))))

(local
 (defthm fn-nh-lines-true-listp
   (true-listp (fn-nh-lines v names))
   :rule-classes :type-prescription))

; KEYSTONE (the exit the host returns is the verdict's).  The host prints the
; octets `fn-nh-render' made, locally or over the control socket, and returns
; `fn-nh-report-exit' of the octets it holds (`fn-native-health-host-exit');
; for every verdict of at most eight outcomes that is the verdict's code.
(defthm fn-nh-report-exit-of-render
  (implies (<= (len v) 8)
           (equal (fn-nh-report-exit (fn-nh-render v)) (fn-nh-exit-code v)))
  :hints (("Goal" :in-theory (e/d (fn-nh-render fn-nh-header)
                                  (fn-nh-report-exit fn-nh-exit-code fn-nh-digit2 fn-nh-header-reason
                                   fn-nh-exit-prefix (:e fn-nh-exit-prefix) fn-nh-lines fn-nh-first-held fn-nh-any-unobservedp
                                   fn-nls-text fn-nh-state-word)))))

(defun fn-nh-held-covers (v w)
  "Every state held in V is held in W."
  (declare (xargs :guard t))
  (if (consp v)
      (and (or (not (and (consp (car v)) (equal (car (car v)) :held)))
               (and (consp w) (consp (car w)) (equal (car (car w)) :held)))
           (fn-nh-held-covers (cdr v) (if (consp w) (cdr w) nil)))
    t))

(local
 (defthm fn-nh-first-held-index-lower
   (implies (and (natp i) (fn-nh-first-held-index v i))
            (<= i (fn-nh-first-held-index v i)))
   :rule-classes :linear
   :hints (("Goal" :use fn-nh-first-held-index-bounds))))

; KEYSTONE (more held states never a milder verdict).  If W holds every
; state V holds, W's first held state is no later than V's: its exit code is
; no larger, so adding a fault input never makes the code less severe.
(defthm fn-nh-first-held-monotone
  (implies (and (fn-nh-held-covers v w)
                (natp i)
                (fn-nh-first-held-index v i))
           (and (fn-nh-first-held-index w i)
                (<= (fn-nh-first-held-index w i) (fn-nh-first-held-index v i))))
  :hints (("Goal" :induct (list (fn-nh-held-covers v w) (fn-nh-first-held-index v i)
                                (fn-nh-first-held-index w i))
           :in-theory (enable fn-nh-held-covers fn-nh-first-held-index))))

; KEYSTONE (pressure is monotone).  More use, or a higher operator threshold,
; never clears space pressure on a figure.
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-nh-pressedp-monotone
    (implies (and (fn-nh-pressedp used bound min)
                  (<= (nfix used) (nfix used2))
                  (<= (nfix min) (nfix min2)))
             (fn-nh-pressedp used2 bound min2))
    :hints (("Goal" :in-theory (enable fn-nh-pressedp)
             :nonlinearp t))))

; KEYSTONE (the owner's words are the store's facts with its feed table).  The
; subject is `fn-nh-live-report', which the owner renders for a :health FNLS
; request (`fn-nh-answer-report', host/native-live-status-host.lisp
; `fn-native-live-status-host-answer').  With the carried octet sum valid, the
; report is the verdict over the owner's Store, configuration and feed table
; with the Store's own committed octets: the same store facts the offline
; `fn-nh-offline-report' renders, plus the feed states only the owner has.
(defthm fn-nh-live-report-is-the-store-report
  (implies (fn-sbud-octets-cache-validp
            cache (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
           (equal (fn-nh-live-report profile oc cache min)
                  (fn-nh-render
                   (fn-nh-verdict nil
                                  (fn-nh-store-inputs
                                   profile (fn-own-store (fn-ocfg-owner oc))
                                   (fn-sbud-bytes-used (fn-own-store (fn-ocfg-owner oc)))
                                   (fn-ocfg-config oc))
                                  min (fn-own-feeds (fn-ocfg-owner oc))))))
  :hints (("Goal" :use ((:instance fn-sbud-bytes-used-is-kernel-sum
                                   (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-nh-live-report))))

; An owner that answered is never reported fenced; one whose socket accepted
; and did not answer always is, whatever the lock and the clone fence show.
; A held lock where an owner would listen is :starting, never :store-held
; (PKT-283); the lock alone never makes the fence :starting.
(defthm fn-nh-fence-of-route
  (and (implies (not (equal route :uncertain))
                (equal (fn-nh-fence-of route lock clone listener)
                       (cond (clone :clone-fence)
                             ((and (equal lock :held) listener) :starting)
                             ((member-equal lock '(:held :unknown)) :store-held)
                             (t nil))))
       (equal (fn-nh-fence-of :uncertain lock clone listener) :owner-unanswering)
       (implies (fn-nh-fence-of route lock clone listener)
                (fn-nh-fence-reasonp (fn-nh-fence-of route lock clone listener))))
  :hints (("Goal" :in-theory (enable fn-nh-fence-of fn-nh-fence-reasonp))))

; KEYSTONE (starting is not store-held; PKT-283).  The subject is
; `fn-nh-fence-of', which the host calls through `fn-nh-health-step'
; (host/native/operator.lisp fnn-operator-health-report).  With no clone
; fence and a route that did not reach an owner, the report says :starting
; exactly when the lock is held and an owner would listen; a free or absent
; lock is never fenced.
(defthm fn-nh-fence-of-starting-iff
  (implies (and (not (equal route :uncertain)) (not clone))
           (and (iff (equal (fn-nh-fence-of route lock clone listener) :starting)
                     (and (equal lock :held) listener))
                (implies (member-equal lock '(:free :absent))
                         (not (fn-nh-fence-of route lock clone listener)))))
  :hints (("Goal" :in-theory (enable fn-nh-fence-of))))

;; -----------------------------------------------------------------------------
;; One health observation, decided (PKT-454)
;;
;; The host takes its observations once per invocation: whether the configured
;; control socket node is present (SOCKET-PRESENT), the outcome of asking the
;; owner for its FNLS kind-6 report (OUTCOME: (:done OCTETS) when the owner
;; answered, else the transport stage), the writer lock, the clone fence and
;; whether an owner would listen.  The step names what the host does next:
;; (:answered OCTETS) prints the owner's report, (:refused) prints the refusal,
;; (:fenced REASON) prints `fn-nh-fenced-report', (:offline) opens the Store.
;; `fnn-operator-health-report' (host/native/operator.lisp) calls it through
;; `fn-native-health-host-step' (host/native-live-status-host.lisp).
(defun fn-nh-answeredp (socket-present outcome)
  (declare (xargs :guard t))
  (and socket-present (consp outcome) (equal (car outcome) :done)
       (consp (cdr outcome)) t))

(defun fn-nh-health-step (socket-present outcome lock clone-fence-present
                                         listener-expected)
  (declare (xargs :guard t))
  (if (fn-nh-answeredp socket-present outcome)
      (list :answered (cadr outcome))
    (let ((route (fn-nls-route socket-present outcome)))
      (if (equal route :refused)
          (list :refused)
        (let ((reason (fn-nh-fence-of route lock clone-fence-present
                                      listener-expected)))
          (cond (reason (list :fenced reason))
                ;; friend-path-2: where an owner would listen, nothing
                ;; answers and nothing holds the lock, the node is not
                ;; running; the host prints `fn-nh-not-running-report'.
                ((and (equal route :offline) listener-expected
                      (member-equal lock '(:free :absent)))
                 (list :not-running))
                (t (list :offline))))))))

;; KEYSTONE (PKT-454: starting is a reason of the fenced state, exit 20, and it
;; clears on LISTENING).  The subject is `fn-nh-health-step', the host's whole
;; decision for one `health' invocation.  A fence of :starting is reported
;; exactly while no clone fence is present, the lock is held, an owner would
;; listen and nothing answered (the route is :offline: no socket node, or a
;; connect that failed before anything was sent); and the same lock, fence and
;; listener with the owner answering on its socket yields the owner's report,
;; no fence at all: the step from starting to clear is taken on the one
;; observation LISTENING changes.
(defthm fn-nh-starting-clears-on-listening
  (and (iff (equal (fn-nh-health-step sp outcome lock clone listener)
                   '(:fenced :starting))
            (and (not clone) (equal lock :held) listener
                 (equal (fn-nls-route sp outcome) :offline)))
       (implies sp
                (equal (fn-nh-health-step sp (list :done octets) lock clone listener)
                       (list :answered octets))))
  :hints (("Goal" :in-theory (enable fn-nh-health-step fn-nh-answeredp
                                     fn-nh-fence-of fn-nls-route))))

(in-theory (disable fn-nh-verdict fn-nh-render fn-nh-report-exit fn-nh-exit-code
                    fn-nh-live-report fn-nh-offline-report fn-nh-fenced-report))

; PKT-220 (PRF-185).  `store ROOT retention' is offline only: it takes a
; store root, not a configuration, so it has no control socket to ask, and
; while an owner holds the Store its shared lock refuses.  The same two
; figures are live already: `operator CONFIG obligations' opens with them.
; KEYSTONE: the report the running owner renders for :obligations
; (`fn-nls-live-report', from host/native-live-status-host.lisp
; `fn-native-live-status-host-answer' through `fn-nh-answer-report') opens
; with exactly `fn-rtf-pin-count' and `fn-rtf-reserved' of the owner's Store
; node, the functions the offline verb prints (host/store-node-host.lisp
; `fn-store-sn-pin-count', `fn-store-sn-reserved', from host/native/io.lisp
; `fnn-command-retention').  On the same Store node the two verbs print the
; same figures.
(defthm fn-nls-obligations-figures-are-the-retention-figures
  (equal (fn-nls-live-report :obligations profile oc cache obs fn-arena)
         (let ((s (fn-own-store (fn-ocfg-owner oc))))
           (append (fn-nls-text "obligations=") (fn-nls-nat (fn-rtf-pin-count s))
                   (fn-nls-field "reserved" (fn-rtf-reserved s))
                   *fn-nls-lf*
                   (fn-nls-obligation-lines
                    (fn-retain-pins (fn-node-retention (fn-sn-node s)))))))
  :hints (("Goal" :in-theory '(fn-nls-live-report fn-nls-report fn-nls-retention
                               fn-rtf-pin-count fn-rtf-reserved))))

; -----------------------------------------------------------------------------
; PKT-508 (PRF-187): the owner's log sink after the eight states.
;
; The running owner's `health' ends with one line of its service-log sink
; (books/log-sink.lisp): the lines pending in the writer's queue, the lines
; dropped because the sink did not drain (or a write failed), and the lines
; written.  host/native-live-status-host.lisp `fn-native-live-status-host-answer'
; appends it, with the exposure lines, after `fn-nh-render''s report, from the
; sink the host carries (host/native/io.lisp `fnn-log-sink-snapshot').
(defun fn-nh-log-sink-line (sink)
  (declare (xargs :guard t))
  (append (fn-nls-text "log-sink")
          (fn-nls-field "pending" (fn-log-sink-pending-lines sink))
          (fn-nls-field "dropped" (fn-log-sink-dropped sink))
          (fn-nls-field "written" (fn-log-sink-written sink))
          *fn-nls-lf*))

; KEYSTONE (lines after the eight states leave the exit alone).  The host
; returns `fn-nh-report-exit' of the whole page it received, which carries
; the exposure lines and the log-sink line after the verdict's report; for
; every verdict of at most eight outcomes and whatever follows, that is the
; verdict's code.  So `log-sink dropped=N' is reported without a ninth code
; and without moving the scale monitors read (HST-007).
(local
 (defthm fn-nh-render-long-enough
   (<= 14 (len (fn-nh-render v)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-nh-render fn-nh-header)
                                   (fn-nh-digit2 fn-nh-header-reason fn-nh-lines
                                    fn-nls-text fn-nh-state-word))))))

(local
 (defthm fn-nh-nth-of-append-short
   (implies (< (nfix i) (len x))
            (equal (fn-nh-nth i (append x more)) (fn-nh-nth i x)))))

(local
 (defthm fn-nh-take-of-append-short
   (implies (<= (nfix n) (len x))
            (equal (take n (append x more)) (take n x)))))

(defthm fn-nh-report-exit-of-append
  (implies (and (true-listp x) (true-listp more) (<= 14 (len x)))
           (equal (fn-nh-report-exit (append x more)) (fn-nh-report-exit x)))
  :hints (("Goal" :in-theory (e/d (fn-nh-report-exit)
                                  (fn-nh-digit-value take (:e fn-nh-exit-prefix)
                                   fn-nh-exit-prefix)))))

(defthm fn-nh-report-exit-of-render-and-more
  (implies (and (<= (len v) 8) (true-listp more))
           (equal (fn-nh-report-exit (append (fn-nh-render v) more))
                  (fn-nh-exit-code v)))
  :hints (("Goal" :use (fn-nh-report-exit-of-render
                        (:instance fn-nh-report-exit-of-append (x (fn-nh-render v))))
                  :in-theory (disable fn-nh-render fn-nh-report-exit fn-nh-exit-code
                                      fn-nh-report-exit-of-append
                                      fn-nh-report-exit-of-render))))

(in-theory (disable fn-nh-report-exit-of-append))

; PKT-269 (PRF-187): the verdict and the three health reports run
; guard-verified, the owner's `fn-nh-live-report' (FNLS kind 6, under the
; owner mutex) included.  `fn-nh-answer-report' waits on
; books/native-live-status.lisp `fn-nls-live-report' for the other kinds
; (`fn-nls-report''s reclaim words call books/store-reclaim-holders.lisp
; `fn-rcl-store-counts', :verify-guards nil).
(verify-guards fn-nh-forward-pins)
(verify-guards fn-nh-store-hr)
(verify-guards fn-nh-store-debt)
(verify-guards fn-nh-o-exhausted)
(verify-guards fn-nh-o-pressure)
(verify-guards fn-nh-o-no-route)
(verify-guards fn-nh-o-debt)
(verify-guards fn-nh-verdict)
(verify-guards fn-nh-offline-report)
(verify-guards fn-nh-fenced-report)
(verify-guards fn-nh-live-report)

; -----------------------------------------------------------------------------
; The node that is not running (lane friend-path-2, 2026-09-27).
;
; A friend's node crash-looped under systemd and `health' said
; `exit=19 state=none-held (some states unobserved)': nothing said the node
; was not running, or why.  Now `fn-nh-health-step' answers (:not-running)
; when an owner would listen (a control socket is configured), nothing
; answers on it and nothing holds the writer lock; `health' then prints
; `fn-nh-not-running-report' (exit 18) and `status' prints
; `fn-nh-not-running-lines' before the store's facts.
;
; Why it stopped comes from the service log (`[log] path').  `run' writes
; `fn-nh-run-started-line' when it opens the log and `fn-nh-run-stopped-line'
; (its exit code and, when it did not stop cleanly, the reason: the owner's
; fault or the condition that ended the run) before it closes it.  The host
; reads at most `*fn-nh-log-tail-octets*' octets from the log's end and ACL2
; takes the last of those lines (`fn-nh-last-run'): the file is external
; data, scanned once, never read by the Lisp reader.

(defconst *fn-nh-not-running-exit* 18)
(defconst *fn-nh-log-tail-octets* 65536)
(defconst *fn-nh-reason-max-octets* 480)

(defun fn-nh-log-tail-octets ()
  (declare (xargs :guard t))
  *fn-nh-log-tail-octets*)

; A reason as one printable line: a control octet becomes a space, an octet
; outside ASCII a `?', and at most N octets are kept.
(defun fn-nh-clean-octets (x n)
  (declare (xargs :guard (natp n)))
  (if (and (consp x) (not (zp n)))
      (cons (let ((c (car x)))
              (cond ((not (natp c)) 63)
                    ((< c 32) 32)
                    ((< 126 c) 63)
                    (t c)))
            (fn-nh-clean-octets (cdr x) (1- n)))
    nil))

(defconst *fn-nh-run-started* (fn-record-string-octets "run started"))
(defconst *fn-nh-run-stopped-prefix* (fn-record-string-octets "run stopped "))

(defun fn-nh-run-started-line ()
  (declare (xargs :guard t))
  *fn-nh-run-started*)

; `run stopped exit=NN', then ` reason=' and the reason when one is given.
(defun fn-nh-code-octet (d)
  (declare (xargs :guard t))
  (if (and (natp d) (< d 10)) (+ 48 d) 63))

(defun fn-nh-code-words (code)
  (declare (xargs :guard t))
  (let ((c (nfix code)))
    (list (fn-nh-code-octet (floor (mod c 100) 10)) (fn-nh-code-octet (mod c 10)))))

(defun fn-nh-run-stopped-line (code reason)
  (declare (xargs :guard t))
  (append *fn-nh-run-stopped-prefix*
          (fn-nls-text "exit=") (fn-nh-code-words code)
          (if (consp reason)
              (append (fn-nls-text " reason=")
                      (fn-nh-clean-octets reason *fn-nh-reason-max-octets*))
            nil)))

(defun fn-nh-octet-prefixp (p x)
  (declare (xargs :guard t))
  (if (consp p)
      (and (consp x) (equal (car p) (car x)) (fn-nh-octet-prefixp (cdr p) (cdr x)))
    t))

(defun fn-nh-drop (n x)
  (declare (xargs :guard (natp n)))
  (if (and (consp x) (not (zp n))) (fn-nh-drop (1- n) (cdr x)) x))

; One log line (octets, no LF) over the last run line seen before it.
(defun fn-nh-run-of-line (line last)
  (declare (xargs :guard t))
  (cond ((equal line *fn-nh-run-started*) (list :started))
        ((fn-nh-octet-prefixp *fn-nh-run-stopped-prefix* line)
         (cons :stopped (fn-nh-clean-octets
                         (fn-nh-drop (len *fn-nh-run-stopped-prefix*) line)
                         (+ 16 *fn-nh-reason-max-octets*))))
        (t last)))

(defun fn-nh-hd (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun fn-nh-tl (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))

(defun fn-nh-rev (x acc)
  (declare (xargs :guard t))
  (if (consp x) (fn-nh-rev (cdr x) (cons (car x) acc)) acc))

; The scan's state: (the current line's octets, newest first . the last run
; line seen).  One pass, one step per octet.
(defun fn-nh-scan (octets st)
  (declare (xargs :guard t))
  (if (consp octets)
      (fn-nh-scan (cdr octets)
                  (if (equal (car octets) 10)
                      (cons nil (fn-nh-run-of-line (fn-nh-rev (fn-nh-hd st) nil)
                                                   (fn-nh-tl st)))
                    (cons (cons (car octets) (fn-nh-hd st)) (fn-nh-tl st))))
    st))

; KEYSTONE SUBJECT.  The last run line in the log's tail: (:started),
; (:stopped . WORDS) (the line after `run stopped '), or nil.  The host
; (host/native/operator.lisp fnn-operator-last-run) passes the tail's octets.
(defun fn-nh-last-run (tail)
  (declare (xargs :guard t))
  (let ((st (fn-nh-scan tail (cons nil nil))))
    (fn-nh-run-of-line (fn-nh-rev (fn-nh-hd st) nil) (fn-nh-tl st))))

(defun fn-nh-last-run-words (last)
  (declare (xargs :guard t))
  (append
   (cond ((and (consp last) (equal (car last) :stopped))
          (append (fn-nls-text "last-stop ")
                  (fn-nh-clean-octets (cdr last) (+ 16 *fn-nh-reason-max-octets*))))
         ((equal last '(:started))
          (fn-nls-text "last-stop none: the log's last run line is its start (the process was killed, or the machine stopped)"))
         (t (fn-nls-text "last-stop unrecorded: the service log holds no run line (the node has not run since it was set up, fn.toml names no [log] path, or it last ran an older release)")))
   *fn-nls-lf*))

(defconst *fn-nh-not-running-words*
  " (no process holds the store and nothing answers on its control socket: the node is not running)")

; What `status' prints first when no owner runs where one would listen.
(defun fn-nh-not-running-lines (last)
  (declare (xargs :guard t))
  (append (fn-nls-text "not-running") (fn-nls-text *fn-nh-not-running-words*)
          *fn-nls-lf*
          (fn-nh-last-run-words last)))

(defun fn-nh-not-running-header ()
  (declare (xargs :guard t))
  (append (fn-nh-exit-prefix) (fn-nh-digit2 *fn-nh-not-running-exit*)
          (fn-nls-text " state=not-running") (fn-nls-text *fn-nh-not-running-words*)
          *fn-nls-lf*))

; `health' when the step says (:not-running): the header, why it stopped,
; then the eight states over the Store this process opened read-only.
(defun fn-nh-not-running-report (profile s cfg min last)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nh-not-running-header)
          (fn-nh-last-run-words last)
          (fn-nh-lines (fn-nh-verdict nil (fn-nh-store-inputs profile s (fn-sbud-bytes-used s) cfg)
                                      min :unobserved)
                       *fn-nh-states*)))

(verify-guards fn-nh-not-running-report)

(defthm fn-nh-true-listp-of-lines
  (true-listp (fn-nh-lines v names)))

(defthm fn-nh-true-listp-of-last-run-words
  (true-listp (fn-nh-last-run-words last)))

; KEYSTONE (friend-path-2).  The subject is `fn-nh-health-step', the host's
; whole decision for one `health' (host/native/operator.lisp
; fnn-operator-health-report) and the same decision `status' takes
; (fnn-operator-status-once): it answers not-running exactly when an owner
; would listen, no clone fence is present, the lock is seen free or absent
; and nothing answered (the route is :offline); a node that answers, or a
; process that holds the lock, is never reported not running.
(defthm fn-nh-not-running-exactly-when-nothing-runs
  (iff (equal (fn-nh-health-step sp outcome lock clone listener) '(:not-running))
       (and (not clone) listener (member-equal lock '(:free :absent))
            (equal (fn-nls-route sp outcome) :offline)))
  :hints (("Goal" :in-theory (enable fn-nh-health-step fn-nh-answeredp
                                     fn-nh-fence-of fn-nls-route))))

(defthm fn-nh-true-listp-of-not-running-tail
  (true-listp (append (fn-nh-last-run-words last) (fn-nh-lines v names))))

(defthm fn-nh-report-exit-of-not-running-header-and-more
  (implies (true-listp more)
           (equal (fn-nh-report-exit (append (fn-nh-not-running-header) more))
                  *fn-nh-not-running-exit*))
  :hints (("Goal" :use ((:instance fn-nh-report-exit-of-append
                                   (x (fn-nh-not-running-header))))
           :in-theory (disable fn-nh-report-exit-of-append))))

; KEYSTONE.  The not-running report's exit is 18, its own code: never 0,
; never 19 (some state unobserved), never a held state's 20 to 27.
(defthm fn-nh-not-running-report-exit
  (equal (fn-nh-report-exit (fn-nh-not-running-report profile s cfg min last))
         *fn-nh-not-running-exit*)
  :hints (("Goal" :use ((:instance fn-nh-report-exit-of-not-running-header-and-more
                                   (more (append (fn-nh-last-run-words last)
                                                 (fn-nh-lines
                                                  (fn-nh-verdict
                                                   nil (fn-nh-store-inputs profile s (fn-sbud-bytes-used s) cfg)
                                                   min :unobserved)
                                                  *fn-nh-states*)))))
           :in-theory (union-theories
                       '(fn-nh-not-running-report fn-nh-true-listp-of-not-running-tail)
                       (theory 'minimal-theory)))))

; The round trip.  Lemmas: the scan composes over append, runs over an
;; LF-free stretch by pushing it, and the stop line holds no LF.
(defthm fn-nh-scan-of-append
  (equal (fn-nh-scan (append a b) st) (fn-nh-scan b (fn-nh-scan a st))))

(defun fn-nh-no-lf-p (x)
  (declare (xargs :guard t))
  (if (consp x) (and (not (equal (car x) 10)) (fn-nh-no-lf-p (cdr x))) t))

(defthm fn-nh-scan-of-no-lf
  (implies (fn-nh-no-lf-p x)
           (equal (fn-nh-scan x st)
                  (if (consp x)
                      (cons (fn-nh-rev x (fn-nh-hd st)) (fn-nh-tl st))
                    st))))

(defthm fn-nh-no-lf-p-of-append
  (equal (fn-nh-no-lf-p (append a b)) (and (fn-nh-no-lf-p a) (fn-nh-no-lf-p b))))

(defthm fn-nh-no-lf-p-of-clean
  (fn-nh-no-lf-p (fn-nh-clean-octets x n)))

(defthm fn-nh-no-lf-p-of-stopped-line
  (fn-nh-no-lf-p (fn-nh-run-stopped-line code reason)))

(defthm fn-nh-rev-rev
  (implies (true-listp x) (equal (fn-nh-rev (fn-nh-rev x acc) nil) (fn-nh-rev acc x))))

(defthm fn-nh-true-listp-of-stopped-line
  (true-listp (fn-nh-run-stopped-line code reason)))

(defthm fn-nh-stopped-line-has-its-prefix
  (fn-nh-octet-prefixp *fn-nh-run-stopped-prefix* (fn-nh-run-stopped-line code reason)))

(defthm fn-nh-stopped-line-is-not-started
  (not (equal (fn-nh-run-stopped-line code reason) *fn-nh-run-started*)))

(defthm fn-nh-scan-line-then-lf
  (implies (and (fn-nh-no-lf-p x) (true-listp x))
           (equal (fn-nh-scan (append x (list 10)) (cons nil l))
                  (cons nil (fn-nh-run-of-line x l))))
  :hints (("Goal" :in-theory (disable fn-nh-run-of-line))))

(defthm fn-nh-run-of-line-of-stopped
  (equal (fn-nh-run-of-line (fn-nh-run-stopped-line code reason) l)
         (cons :stopped
               (fn-nh-clean-octets
                (fn-nh-drop (len *fn-nh-run-stopped-prefix*)
                            (fn-nh-run-stopped-line code reason))
                (+ 16 *fn-nh-reason-max-octets*))))
  :hints (("Goal" :in-theory (disable fn-nh-run-stopped-line fn-nh-octet-prefixp
                                      (:e fn-nh-octet-prefixp) fn-nh-clean-octets
                                      fn-nh-drop))))

(defthm fn-nh-run-of-line-of-nil
  (equal (fn-nh-run-of-line nil l) l))

(defthm fn-nh-consp-of-stopped-line
  (consp (fn-nh-run-stopped-line code reason)))

; KEYSTONE (teeth for the log's round trip).  Whatever lines precede it,
; when the log's tail ends with the line `run' writes as it stops, the
; stop is what `fn-nh-last-run' reads: its words are the stop line's own
; words after `run stopped ' (the exit code and the reason).
(defthm fn-nh-last-run-reads-the-stop-line
  (equal (fn-nh-last-run (append pre (list 10) (fn-nh-run-stopped-line code reason) (list 10)))
         (cons :stopped
               (fn-nh-clean-octets
                (fn-nh-drop (len *fn-nh-run-stopped-prefix*)
                            (fn-nh-run-stopped-line code reason))
                (+ 16 *fn-nh-reason-max-octets*))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-nh-run-stopped-line fn-nh-clean-octets
                               fn-nh-drop fn-nh-run-of-line))))
