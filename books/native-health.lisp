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
;                          no profile upgrade can raise either (terminal);
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
;                          connection;
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
;   fn-nh-fenced-report   `fn-native-health-host-fenced' (the same caller);
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

(defun fn-nh-forward-count (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (+ (if (and (consp (car pins))
                  (equal (fn-nh-nth 2 (car pins)) :forward))
             1 0)
         (fn-nh-forward-count (cdr pins)))
    0))

(defun fn-nh-forward-charge (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (+ (if (and (consp (car pins))
                  (equal (fn-nh-nth 2 (car pins)) :forward))
             (fn-nh-nat 4 (car pins)) 0)
         (fn-nh-forward-charge (cdr pins)))
    0))

(defun fn-nh-forward-pins (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-retain-pins (fn-nls-retention s)))

; -----------------------------------------------------------------------------
; Feed facts over the owner's outbound feed table
;
; TBL is `fn-own-feeds': entries (NAME RECORD FEED), books/owner-feed.lisp.

(defun fn-nh-dropped-count (xs)
  "Entries dropped at their retry bound (`fn-feed-give-up' :retry-bound)."
  (declare (xargs :guard t))
  (if (consp xs)
      (+ (if (equal (fn-feed-entry-state (car xs)) '(:dropped :retry-bound)) 1 0)
         (fn-nh-dropped-count (cdr xs)))
    0))

(defun fn-nh-feed-pendingp (f)
  (declare (xargs :guard t))
  (and (or (fn-feed-head-queued (fn-feed-queue f))
           (< 0 (fn-feed-inflight-count (fn-feed-queue f))))
       t))

(defun fn-nh-feed-unavailablep (f)
  (declare (xargs :guard t))
  (and (fn-nh-feed-pendingp f)
       (not (natp (fn-feed-conn f)))))

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
  (and (member-equal x '(:clone-fence :store-held :owner-unanswering)) t))

; The host's observations, in the order it takes them (host/native/operator.lisp
; fnn-operator-execute-health): whether the control socket answered, the
; writer lock (`fnn-store-owner-observation': :held :free :absent :unknown),
; and whether the clone fence file exists.  An owner that answered is not
; fenced.
(defun fn-nh-fence-of (route lock clone-fence-present)
  (declare (xargs :guard t))
  (cond ((equal route :uncertain) :owner-unanswering)
        (clone-fence-present :clone-fence)
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
  (append (fn-nls-field "format" (cond ((fn-bs-profile-validp profile) 8)
                                       ((fn-bs-meta-format-7-valuesp profile) 7)
                                       (t 0)))
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
                   (append (fn-nls-text " peers:")
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

(defun fn-nh-header (v)
  (declare (xargs :guard t))
  (append (fn-nh-exit-prefix) (fn-nh-digit2 (fn-nh-exit-code v))
          (fn-nls-text " state=")
          (fn-nls-text (fn-nh-state-word (fn-nh-first-held v)))
          (if (and (not (fn-nh-first-held v)) (fn-nh-any-unobservedp v))
              (fn-nls-text " (some states unobserved)")
            nil)
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
(defun fn-nh-answer-report (kind profile oc cache obs min)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal kind :health)
      (fn-nh-live-report profile oc cache min)
    (fn-nls-live-report kind profile oc cache obs)))

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

(local
 (defthm fn-nh-first-held-index-bounds
   (implies (and (natp i) (fn-nh-first-held-index v i))
            (and (natp (fn-nh-first-held-index v i))
                 (<= i (fn-nh-first-held-index v i))
                 (< (fn-nh-first-held-index v i) (+ i (len v)))))
   :rule-classes nil))

(local
 (defthm fn-nh-exit-code-cases
   (implies (<= (len v) 8)
            (member-equal (fn-nh-exit-code v) '(0 19 20 21 22 23 24 25 26 27)))
   :hints (("Goal" :use ((:instance fn-nh-first-held-index-bounds (i 0)))
            :in-theory (disable fn-nh-first-held-index)))))

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
                                  (fn-nh-report-exit fn-nh-exit-code fn-nh-digit2
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
(defthm fn-nh-fence-of-route
  (and (implies (not (equal route :uncertain))
                (equal (fn-nh-fence-of route lock clone)
                       (cond (clone :clone-fence)
                             ((member-equal lock '(:held :unknown)) :store-held)
                             (t nil))))
       (equal (fn-nh-fence-of :uncertain lock clone) :owner-unanswering)
       (implies (fn-nh-fence-of route lock clone)
                (fn-nh-fence-reasonp (fn-nh-fence-of route lock clone))))
  :hints (("Goal" :in-theory (enable fn-nh-fence-of fn-nh-fence-reasonp))))

(in-theory (disable fn-nh-verdict fn-nh-render fn-nh-report-exit fn-nh-exit-code
                    fn-nh-live-report fn-nh-offline-report fn-nh-fenced-report))
