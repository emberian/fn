; Literal inbound witnesses from configured-reader IHAVE/TAKETHIS traces.
; Missing-completion witnesses are reachable eight-step traces.
; Names with corrupted-state are deliberately malformed states, not traces.
; Complete literal positive/removal teeth for both final inbound theorems.
; Registry and qualification remain open.
(in-package "ACL2")

(include-book "../../books/productive-inbound")

(include-book "../../books/owner-agent")

(defconst
  *pcit-peer*
  (fn-cfg-peer-make
    "p"
    "peer.example"
    (quote (:nntp "127.0.0.1" 1119))
    (quote ("fn.*" 32768 16))
    nil
    (quote (:source-address "127.0.0.1"))))

(defconst
  *pcit-config-record*
  (fn-cfg-record-make
    0
    0
    1
    (append
      *fn-cfg-default-change*
      (list (fn-cfg-set-policy "path-identity" "own.example") (fn-cfg-set-peer-delta *pcit-peer*)))
    *fn-cfg-default-stamp*))

(defconst *pcit-open* (fn-cpo-open-observed (list *pcit-config-record*) 0 nil))

(defconst
  *pcit-ready*
  (fn-sn-io
    (fn-sn-io
      (fn-sn-io (fn-sn-open-state *pcit-open*) :recovery-barrier :ok)
      :recovery-barrier
      :ok)
    :recovery-barrier
    :ok))

(defconst
  *pcit-config*
  (fn-cnode-config (fn-replay-result-node (fn-cpr-replay (list *pcit-config-record*) nil))))

(defconst
  *pcit-oc*
  (cdr
    (fn-ocfg-open-peer
      (fn-ocfg-make
        (fn-own-configure (fn-own-start *pcit-ready* 4) (fn-oag-post-config *pcit-config* 32768))
        *pcit-config*
        nil
        nil)
      "p"
      nil)))

(defconst *pcit-id* (fn-nntp-string-octets "<productive-inbound@x>"))

(defconst
  *pcit-body*
  (append
    (fn-nntp-string-octets "From: a@x")
    (quote (13 10))
    (fn-nntp-string-octets "Newsgroups: fn.test")
    (quote (13 10))
    (fn-nntp-string-octets "Subject: productive inbound")
    (quote (13 10))
    (fn-nntp-string-octets "Date: Mon, 21 Sep 2026 12:00:00 +0000")
    (quote (13 10))
    (fn-nntp-string-octets "Message-ID: <productive-inbound@x>")
    (quote (13 10 13 10))
    (fn-nntp-string-octets "durable transit")
    (quote (13 10))))

(defun
  pcit-read-in
  (kind fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv
    (fn-ocfg-read
      *pcit-oc*
      0
      (append
        (fn-nntp-string-octets kind)
        (quote (32))
        *pcit-id*
        (quote (13 10))
        *pcit-body*
        (quote (46 13 10)))
      fn-arena)
    fn-arena))

(defun
  pcit-read
  (kind)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena (mv-let (r fn-arena) (pcit-read-in kind fn-arena) r)))

(defun
  pcit-taken
  (kind)
  (declare (xargs :verify-guards nil))
  (let
    ((oc (cdr (pcit-read kind))))
    (fn-ocfg-with-owner oc (fn-own-take-submission (fn-ocfg-owner oc)))))

(defconst *pcit-ihave* (pcit-taken "IHAVE"))

(defconst *pcit-takethis* (pcit-taken "TAKETHIS"))

(defun
  pcit-payload
  (oc)
  (declare (xargs :guard t))
  (let
    ((o (fn-ocfg-owner oc)))
    (fn-own-sub-stored-octets *pcit-config* (fn-own-inflight o) (fn-own-node-secret o))))

(defun
  pcit-record
  (oc)
  (declare (xargs :guard (true-listp (pcit-payload oc))))
  (let
    ((payload (pcit-payload oc)))
    (fn-held-make
      0
      0
      0
      "<productive-inbound@x>"
      0
      (quote ("fn.test"))
      "o"
      "s"
      "e"
      1
      5
      (fn-held-facts-of payload)
      (fn-held-context-of payload nil 0)
      nil
      nil)))

(assert-event
  (and
    (equal (fn-sn-open-kind *pcit-open*) :ok)
    (fn-own-transit-subp (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
    (fn-own-transit-subp (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
    (equal
      (fn-peer-submission-kind
        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
      :ihave)))

(defthm
  pcit-ihave-complete-positive
  (let*
    ((o (fn-ocfg-owner *pcit-ihave*))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-ihave*) (list (pcit-payload *pcit-ihave*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
          (list (pcit-payload *pcit-ihave*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
          (list (pcit-payload *pcit-ihave*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-ihave*)))
      (out (fn-oop-transit-outcome (fn-ocfg-with-owner *pcit-ihave* o9) 0 :want nil :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-ihave*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-ihave*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (and
        (equal
          (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*))))
          *fn-pcx-post-steps*)
        (equal (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))) :durable)
        (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))))
        (fn-own-completion-consumedp o9)
        (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
        (equal
          (fn-sf-successes (fn-sn-files (fn-own-store o9)))
          (append (fn-sf-successes (fn-sn-files s)) (list pair)))
        (member-equal (pcit-record *pcit-ihave*) (fn-sf-records (fn-sn-files (fn-own-store o9))))
        (equal
          (fn-served-reply-octets (car out))
          (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))
      (equal
        (fn-served-reply-octets (car out))
        (quote
          (50
            51
            53
            32
            97
            114
            116
            105
            99
            108
            101
            32
            116
            114
            97
            110
            115
            102
            101
            114
            114
            101
            100
            32
            79
            75
            13
            10)))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-complete-positive
  (let*
    ((o (fn-ocfg-owner *pcit-takethis*))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-takethis*) (list (pcit-payload *pcit-takethis*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
          (list (pcit-payload *pcit-takethis*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
          (list (pcit-payload *pcit-takethis*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-takethis*)))
      (out (fn-oop-transit-outcome (fn-ocfg-with-owner *pcit-takethis* o9) 0 :want nil :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-takethis*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-takethis*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (and
        (equal
          (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*))))
          *fn-pcx-post-steps*)
        (equal
          (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*))))
          :durable)
        (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*)))))
        (fn-own-completion-consumedp o9)
        (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
        (equal
          (fn-sf-successes (fn-sn-files (fn-own-store o9)))
          (append (fn-sf-successes (fn-sn-files s)) (list pair)))
        (member-equal
          (pcit-record *pcit-takethis*)
          (fn-sf-records (fn-sn-files (fn-own-store o9))))
        (equal
          (fn-served-reply-octets (car out))
          (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))
      (equal
        (fn-served-reply-octets (car out))
        (quote
          (50
            51
            57
            32
            60
            112
            114
            111
            100
            117
            99
            116
            105
            118
            101
            45
            105
            110
            98
            111
            117
            110
            100
            64
            120
            62
            13
            10)))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-host-without-consumed-completion
  (let*
    ((o
       (fn-own-run
         (fn-ocfg-owner *pcit-ihave*)
         (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
         (list (pcit-payload *pcit-ihave*))))
      (sub (fn-own-inflight o))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (out (fn-oop-transit-outcome (fn-ocfg-with-owner *pcit-ihave* o) 0 :want nil :durable)))
    (and
      conn
      (equal (fn-own-sub-id sub) 0)
      (fn-own-transit-subp sub)
      (not (fn-own-completion-consumedp o))
      (not
        (equal
          (fn-served-reply-octets (car out))
          (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))
      (equal (fn-own-outcome-completion o :durable) :uncertain)
      (equal
        (fn-served-reply-octets (car out))
        (quote
          (52
            51
            54
            32
            116
            114
            97
            110
            115
            102
            101
            114
            32
            102
            97
            105
            108
            101
            100
            59
            32
            116
            104
            101
            32
            111
            117
            116
            99
            111
            109
            101
            32
            105
            115
            32
            117
            110
            99
            101
            114
            116
            97
            105
            110
            13
            10)))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-host-without-consumed-completion
  (let*
    ((o
       (fn-own-run
         (fn-ocfg-owner *pcit-takethis*)
         (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
         (list (pcit-payload *pcit-takethis*))))
      (sub (fn-own-inflight o))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (out (fn-oop-transit-outcome (fn-ocfg-with-owner *pcit-takethis* o) 0 :want nil :durable)))
    (and
      conn
      (equal (fn-own-sub-id sub) 0)
      (fn-own-transit-subp sub)
      (not (fn-own-completion-consumedp o))
      (not
        (equal
          (fn-served-reply-octets (car out))
          (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))
      (equal (fn-own-outcome-completion o :durable) :uncertain)
      (equal
        (fn-served-reply-octets (car out))
        (quote
          (52
            51
            54
            32
            60
            112
            114
            111
            100
            117
            99
            116
            105
            118
            101
            45
            105
            110
            98
            111
            117
            110
            100
            64
            120
            62
            13
            10)))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-corrupted-state-without-conn
  (let*
    ((o9
       (fn-own-run
         (fn-ocfg-owner *pcit-ihave*)
         (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
         (list (pcit-payload *pcit-ihave*))))
      (o
        (fn-own-make
          (fn-own-store o9)
          (fn-own-view o9)
          nil
          (fn-own-next-id o9)
          (fn-own-max-conns o9)
          (fn-own-pending o9)
          (fn-own-ledger-field o9)
          (fn-own-clock o9)
          (fn-own-facts o9)
          (fn-own-config o9)
          (fn-own-queue o9)
          (fn-own-inflight o9)
          (fn-own-feeds o9)
          (fn-own-node-secret o9)
          (fn-own-refused o9)))
      (oc (fn-ocfg-with-owner *pcit-ihave* o))
      (sub (fn-own-inflight o))
      (conn (fn-own-find-conn 0 (fn-own-conns o))))
    (and
      (and
        (equal (fn-own-sub-id sub) 0)
        (fn-own-transit-subp sub)
        (fn-own-completion-consumedp o))
      (not conn)
      (not
        (equal
          (fn-served-reply-octets (car (fn-oop-transit-outcome oc 0 :want nil :durable)))
          (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-corrupted-state-without-id
  (let*
    ((o9
       (fn-own-run
         (fn-ocfg-owner *pcit-ihave*)
         (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
         (list (pcit-payload *pcit-ihave*))))
      (sub9 (fn-own-inflight o9))
      (o
        (fn-own-make
          (fn-own-store o9)
          (fn-own-view o9)
          (fn-own-conns o9)
          (fn-own-next-id o9)
          (fn-own-max-conns o9)
          (fn-own-pending o9)
          (fn-own-ledger-field o9)
          (fn-own-clock o9)
          (fn-own-facts o9)
          (fn-own-config o9)
          (fn-own-queue o9)
          (fn-own-sub-make
            1
            (fn-own-sub-version sub9)
            (fn-own-sub-mark sub9)
            (fn-own-sub-decision sub9))
          (fn-own-feeds o9)
          (fn-own-node-secret o9)
          (fn-own-refused o9)))
      (oc (fn-ocfg-with-owner *pcit-ihave* o))
      (sub (fn-own-inflight o))
      (conn (fn-own-find-conn 0 (fn-own-conns o))))
    (and
      (and conn (fn-own-transit-subp sub) (fn-own-completion-consumedp o))
      (not (equal (fn-own-sub-id sub) 0))
      (not
        (equal
          (fn-served-reply-octets (car (fn-oop-transit-outcome oc 0 :want nil :durable)))
          (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-corrupted-state-without-transit
  (let*
    ((o9
       (fn-own-run
         (fn-ocfg-owner *pcit-ihave*)
         (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
         (list (pcit-payload *pcit-ihave*))))
      (sub9 (fn-own-inflight o9))
      (o
        (fn-own-make
          (fn-own-store o9)
          (fn-own-view o9)
          (fn-own-conns o9)
          (fn-own-next-id o9)
          (fn-own-max-conns o9)
          (fn-own-pending o9)
          (fn-own-ledger-field o9)
          (fn-own-clock o9)
          (fn-own-facts o9)
          (fn-own-config o9)
          (fn-own-queue o9)
          (fn-own-sub-make 0 (fn-own-sub-version sub9) (fn-own-sub-mark sub9) nil)
          (fn-own-feeds o9)
          (fn-own-node-secret o9)
          (fn-own-refused o9)))
      (oc (fn-ocfg-with-owner *pcit-ihave* o))
      (sub (fn-own-inflight o))
      (conn (fn-own-find-conn 0 (fn-own-conns o))))
    (and
      (and conn (equal (fn-own-sub-id sub) 0) (fn-own-completion-consumedp o))
      (not (fn-own-transit-subp sub))
      (not
        (equal
          (fn-served-reply-octets (car (fn-oop-transit-outcome oc 0 :want nil :durable)))
          (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-corrupted-state-without-conn
  (let*
    ((o9
       (fn-own-run
         (fn-ocfg-owner *pcit-takethis*)
         (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
         (list (pcit-payload *pcit-takethis*))))
      (o
        (fn-own-make
          (fn-own-store o9)
          (fn-own-view o9)
          nil
          (fn-own-next-id o9)
          (fn-own-max-conns o9)
          (fn-own-pending o9)
          (fn-own-ledger-field o9)
          (fn-own-clock o9)
          (fn-own-facts o9)
          (fn-own-config o9)
          (fn-own-queue o9)
          (fn-own-inflight o9)
          (fn-own-feeds o9)
          (fn-own-node-secret o9)
          (fn-own-refused o9)))
      (oc (fn-ocfg-with-owner *pcit-takethis* o))
      (sub (fn-own-inflight o))
      (conn (fn-own-find-conn 0 (fn-own-conns o))))
    (and
      (and
        (equal (fn-own-sub-id sub) 0)
        (fn-own-transit-subp sub)
        (fn-own-completion-consumedp o))
      (not conn)
      (not
        (equal
          (fn-served-reply-octets (car (fn-oop-transit-outcome oc 0 :want nil :durable)))
          (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-corrupted-state-without-id
  (let*
    ((o9
       (fn-own-run
         (fn-ocfg-owner *pcit-takethis*)
         (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
         (list (pcit-payload *pcit-takethis*))))
      (sub9 (fn-own-inflight o9))
      (o
        (fn-own-make
          (fn-own-store o9)
          (fn-own-view o9)
          (fn-own-conns o9)
          (fn-own-next-id o9)
          (fn-own-max-conns o9)
          (fn-own-pending o9)
          (fn-own-ledger-field o9)
          (fn-own-clock o9)
          (fn-own-facts o9)
          (fn-own-config o9)
          (fn-own-queue o9)
          (fn-own-sub-make
            1
            (fn-own-sub-version sub9)
            (fn-own-sub-mark sub9)
            (fn-own-sub-decision sub9))
          (fn-own-feeds o9)
          (fn-own-node-secret o9)
          (fn-own-refused o9)))
      (oc (fn-ocfg-with-owner *pcit-takethis* o))
      (sub (fn-own-inflight o))
      (conn (fn-own-find-conn 0 (fn-own-conns o))))
    (and
      (and conn (fn-own-transit-subp sub) (fn-own-completion-consumedp o))
      (not (equal (fn-own-sub-id sub) 0))
      (not
        (equal
          (fn-served-reply-octets (car (fn-oop-transit-outcome oc 0 :want nil :durable)))
          (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-corrupted-state-without-transit
  (let*
    ((o9
       (fn-own-run
         (fn-ocfg-owner *pcit-takethis*)
         (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
         (list (pcit-payload *pcit-takethis*))))
      (sub9 (fn-own-inflight o9))
      (o
        (fn-own-make
          (fn-own-store o9)
          (fn-own-view o9)
          (fn-own-conns o9)
          (fn-own-next-id o9)
          (fn-own-max-conns o9)
          (fn-own-pending o9)
          (fn-own-ledger-field o9)
          (fn-own-clock o9)
          (fn-own-facts o9)
          (fn-own-config o9)
          (fn-own-queue o9)
          (fn-own-sub-make 0 (fn-own-sub-version sub9) (fn-own-sub-mark sub9) nil)
          (fn-own-feeds o9)
          (fn-own-node-secret o9)
          (fn-own-refused o9)))
      (oc (fn-ocfg-with-owner *pcit-takethis* o))
      (sub (fn-own-inflight o))
      (conn (fn-own-find-conn 0 (fn-own-conns o))))
    (and
      (and conn (equal (fn-own-sub-id sub) 0) (fn-own-completion-consumedp o))
      (not (fn-own-transit-subp sub))
      (not
        (equal
          (fn-served-reply-octets (car (fn-oop-transit-outcome oc 0 :want nil :durable)))
          (fn-pct-inbound-success-octets (fn-own-sub-decision sub))))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-nine-step-corrupted-state-without-id
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-ihave*))
             (fn-own-view (fn-ocfg-owner *pcit-ihave*))
             (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
             (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
             (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
             (fn-own-config (fn-ocfg-owner *pcit-ihave*))
             (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
             (fn-own-sub-make
               1
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
             (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
             (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-ihave*) (list (pcit-payload *pcit-ihave*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
          (list (pcit-payload *pcit-ihave*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
          (list (pcit-payload *pcit-ihave*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-ihave*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-sub-make
                  1
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-ihave*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-ihave*))) :ok)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (equal (fn-own-sub-id sub) 0))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-ihave*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-nine-step-corrupted-state-without-conn
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-ihave*))
             (fn-own-view (fn-ocfg-owner *pcit-ihave*))
             nil
             (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
             (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
             (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
             (fn-own-config (fn-ocfg-owner *pcit-ihave*))
             (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
             (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
             (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-ihave*) (list (pcit-payload *pcit-ihave*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
          (list (pcit-payload *pcit-ihave*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
          (list (pcit-payload *pcit-ihave*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-ihave*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                nil
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-ihave*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-ihave*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not conn)
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-ihave*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-nine-step-corrupted-state-without-mark-natural
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-ihave*))
             (fn-own-view (fn-ocfg-owner *pcit-ihave*))
             (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
             (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
             (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
             (fn-own-config (fn-ocfg-owner *pcit-ihave*))
             (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               -1
               (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
             (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
             (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-ihave*) (list (pcit-payload *pcit-ihave*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
          (list (pcit-payload *pcit-ihave*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
          (list (pcit-payload *pcit-ihave*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-ihave*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  -1
                  (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-ihave*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-ihave*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (natp (fn-own-sub-mark sub)))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-ihave*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-nine-step-corrupted-state-without-mark-bounded
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-ihave*))
             (fn-own-view (fn-ocfg-owner *pcit-ihave*))
             (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
             (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
             (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
             (fn-own-config (fn-ocfg-owner *pcit-ihave*))
             (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               1
               (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
             (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
             (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-ihave*) (list (pcit-payload *pcit-ihave*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
          (list (pcit-payload *pcit-ihave*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
          (list (pcit-payload *pcit-ihave*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-ihave*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  1
                  (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-ihave*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-ihave*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (<= (fn-own-sub-mark sub) (len (fn-own-ledger o))))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-ihave*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-nine-step-corrupted-state-without-message-id
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-ihave*))
             (fn-own-view (fn-ocfg-owner *pcit-ihave*))
             (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
             (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
             (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
             (fn-own-config (fn-ocfg-owner *pcit-ihave*))
             (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-peer-make-submission
                 (fn-peer-submission-peer
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                 (fn-peer-submission-kind
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                 (fn-nntp-string-octets "<other@x>")
                 (fn-peer-submission-octets
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
             (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
             (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-ihave*) (list (pcit-payload *pcit-ihave*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
          (list (pcit-payload *pcit-ihave*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
          (list (pcit-payload *pcit-ihave*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-ihave*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-peer-make-submission
                    (fn-peer-submission-peer
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                    (fn-peer-submission-kind
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                    (fn-nntp-string-octets "<other@x>")
                    (fn-peer-submission-octets
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-ihave*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-ihave*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub))))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-ihave*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-nine-step-corrupted-state-without-payload
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-ihave*))
             (fn-own-view (fn-ocfg-owner *pcit-ihave*))
             (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
             (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
             (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
             (fn-own-config (fn-ocfg-owner *pcit-ihave*))
             (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-peer-make-submission
                 (fn-peer-submission-peer
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                 (fn-peer-submission-kind
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                 (fn-peer-submission-msgid
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                 nil))
             (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
             (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-ihave*) (list (pcit-payload *pcit-ihave*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
          (list (pcit-payload *pcit-ihave*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
          (list (pcit-payload *pcit-ihave*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-ihave*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-peer-make-submission
                    (fn-peer-submission-peer
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                    (fn-peer-submission-kind
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                    (fn-peer-submission-msgid
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                    nil))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-ihave*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-ihave*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub))))
      (not
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-ihave*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-nine-step-corrupted-state-without-id
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-takethis*))
             (fn-own-view (fn-ocfg-owner *pcit-takethis*))
             (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
             (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
             (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
             (fn-own-config (fn-ocfg-owner *pcit-takethis*))
             (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
             (fn-own-sub-make
               1
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
             (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
             (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-takethis*) (list (pcit-payload *pcit-takethis*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
          (list (pcit-payload *pcit-takethis*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
          (list (pcit-payload *pcit-takethis*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-takethis*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-sub-make
                  1
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-takethis*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-takethis*))) :ok)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (equal (fn-own-sub-id sub) 0))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-takethis*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-nine-step-corrupted-state-without-conn
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-takethis*))
             (fn-own-view (fn-ocfg-owner *pcit-takethis*))
             nil
             (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
             (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
             (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
             (fn-own-config (fn-ocfg-owner *pcit-takethis*))
             (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
             (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
             (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-takethis*) (list (pcit-payload *pcit-takethis*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
          (list (pcit-payload *pcit-takethis*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
          (list (pcit-payload *pcit-takethis*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-takethis*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                nil
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-takethis*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-takethis*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not conn)
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-takethis*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-nine-step-corrupted-state-without-mark-natural
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-takethis*))
             (fn-own-view (fn-ocfg-owner *pcit-takethis*))
             (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
             (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
             (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
             (fn-own-config (fn-ocfg-owner *pcit-takethis*))
             (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               -1
               (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
             (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
             (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-takethis*) (list (pcit-payload *pcit-takethis*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
          (list (pcit-payload *pcit-takethis*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
          (list (pcit-payload *pcit-takethis*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-takethis*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  -1
                  (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-takethis*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-takethis*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (natp (fn-own-sub-mark sub)))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-takethis*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-nine-step-corrupted-state-without-mark-bounded
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-takethis*))
             (fn-own-view (fn-ocfg-owner *pcit-takethis*))
             (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
             (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
             (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
             (fn-own-config (fn-ocfg-owner *pcit-takethis*))
             (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               1
               (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
             (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
             (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-takethis*) (list (pcit-payload *pcit-takethis*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
          (list (pcit-payload *pcit-takethis*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
          (list (pcit-payload *pcit-takethis*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-takethis*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  1
                  (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-takethis*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-takethis*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (<= (fn-own-sub-mark sub) (len (fn-own-ledger o))))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-takethis*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-nine-step-corrupted-state-without-message-id
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-takethis*))
             (fn-own-view (fn-ocfg-owner *pcit-takethis*))
             (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
             (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
             (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
             (fn-own-config (fn-ocfg-owner *pcit-takethis*))
             (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-peer-make-submission
                 (fn-peer-submission-peer
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                 (fn-peer-submission-kind
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                 (fn-nntp-string-octets "<other@x>")
                 (fn-peer-submission-octets
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
             (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
             (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-takethis*) (list (pcit-payload *pcit-takethis*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
          (list (pcit-payload *pcit-takethis*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
          (list (pcit-payload *pcit-takethis*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-takethis*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-peer-make-submission
                    (fn-peer-submission-peer
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                    (fn-peer-submission-kind
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                    (fn-nntp-string-octets "<other@x>")
                    (fn-peer-submission-octets
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-takethis*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-takethis*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub))))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-takethis*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-nine-step-corrupted-state-without-payload
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-takethis*))
             (fn-own-view (fn-ocfg-owner *pcit-takethis*))
             (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
             (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
             (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
             (fn-own-config (fn-ocfg-owner *pcit-takethis*))
             (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-peer-make-submission
                 (fn-peer-submission-peer
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                 (fn-peer-submission-kind
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                 (fn-peer-submission-msgid
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                 nil))
             (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
             (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-takethis*) (list (pcit-payload *pcit-takethis*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
          (list (pcit-payload *pcit-takethis*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
          (list (pcit-payload *pcit-takethis*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-takethis*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-peer-make-submission
                    (fn-peer-submission-peer
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                    (fn-peer-submission-kind
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                    (fn-peer-submission-msgid
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                    nil))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-takethis*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-takethis*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub))))
      (not
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-takethis*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

; Remaining main-theorem removals: explicitly corrupted state, not traces.
; Explicit corrupted-state removals: a local submission in the transit slot.
(defthm
  pcit-ihave-nine-step-corrupted-state-without-transit-shape
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-ihave*))
             (fn-own-view (fn-ocfg-owner *pcit-ihave*))
             (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
             (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
             (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
             (fn-own-config (fn-ocfg-owner *pcit-ihave*))
             (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
               (fn-inj-make-decision
                 :injected
                 nil
                 (fn-peer-submission-msgid
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                 (quote ("fn.test"))
                 (fn-peer-submission-octets
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
             (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
             (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w
        (fn-row-wire-of
          (pcit-record
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-inj-make-decision
                    :injected
                    nil
                    (fn-peer-submission-msgid
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                    (quote ("fn.test"))
                    (fn-peer-submission-octets
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*)))))
          (list
            (pcit-payload
              (fn-ocfg-with-owner
                *pcit-ihave*
                (fn-own-make
                  (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-sub-make
                    (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-inj-make-decision
                      :injected
                      nil
                      (fn-peer-submission-msgid
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                      (quote ("fn.test"))
                      (fn-peer-submission-octets
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                  (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store
            (fn-pcx-store-script
              (list
                :prepare
                (pcit-record
                  (fn-ocfg-with-owner
                    *pcit-ihave*
                    (fn-own-make
                      (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-sub-make
                        (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                        (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                        (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                        (fn-inj-make-decision
                          :injected
                          nil
                          (fn-peer-submission-msgid
                            (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                          (quote ("fn.test"))
                          (fn-peer-submission-octets
                            (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                      (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                      (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))))
          (list
            (pcit-payload
              (fn-ocfg-with-owner
                *pcit-ihave*
                (fn-own-make
                  (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-sub-make
                    (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-inj-make-decision
                      :injected
                      nil
                      (fn-peer-submission-msgid
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                      (quote ("fn.test"))
                      (fn-peer-submission-octets
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                  (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script
            (list
              :prepare
              (pcit-record
                (fn-ocfg-with-owner
                  *pcit-ihave*
                  (fn-own-make
                    (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-sub-make
                      (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                      (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                      (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                      (fn-inj-make-decision
                        :injected
                        nil
                        (fn-peer-submission-msgid
                          (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                        (quote ("fn.test"))
                        (fn-peer-submission-octets
                          (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                    (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-refused (fn-ocfg-owner *pcit-ihave*)))))))
          (list
            (pcit-payload
              (fn-ocfg-with-owner
                *pcit-ihave*
                (fn-own-make
                  (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-sub-make
                    (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-inj-make-decision
                      :injected
                      nil
                      (fn-peer-submission-msgid
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                      (quote ("fn.test"))
                      (fn-peer-submission-octets
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                  (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))))
      (pair
        (fn-sf-record-pair
          (pcit-record
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-inj-make-decision
                    :injected
                    nil
                    (fn-peer-submission-msgid
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                    (quote ("fn.test"))
                    (fn-peer-submission-octets
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*)))))))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-inj-make-decision
                    :injected
                    nil
                    (fn-peer-submission-msgid
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                    (quote ("fn.test"))
                    (fn-peer-submission-octets
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep
          s
          (pcit-record
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                  (fn-inj-make-decision
                    :injected
                    nil
                    (fn-peer-submission-msgid
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                    (quote ("fn.test"))
                    (fn-peer-submission-octets
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
        (eq
          (fn-th-at
            0
            (fn-th-prefix-step
              (fn-sn-topic s)
              (pcit-record
                (fn-ocfg-with-owner
                  *pcit-ihave*
                  (fn-own-make
                    (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-sub-make
                      (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                      (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                      (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                      (fn-inj-make-decision
                        :injected
                        nil
                        (fn-peer-submission-msgid
                          (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                        (quote ("fn.test"))
                        (fn-peer-submission-octets
                          (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                    (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                    (fn-own-refused (fn-ocfg-owner *pcit-ihave*)))))))
          :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (fn-own-transit-subp sub))
      (not
        (and
          (equal
            (len
              (fn-pcx-post-script
                (list
                  :prepare
                  (pcit-record
                    (fn-ocfg-with-owner
                      *pcit-ihave*
                      (fn-own-make
                        (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-sub-make
                          (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                          (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                          (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                          (fn-inj-make-decision
                            :injected
                            nil
                            (fn-peer-submission-msgid
                              (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                            (quote ("fn.test"))
                            (fn-peer-submission-octets
                              (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                        (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))))
            *fn-pcx-post-steps*)
          (equal
            (car
              (fn-own-finish
                o8
                *pcit-config*
                (list
                  (pcit-payload
                    (fn-ocfg-with-owner
                      *pcit-ihave*
                      (fn-own-make
                        (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-sub-make
                          (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                          (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                          (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                          (fn-inj-make-decision
                            :injected
                            nil
                            (fn-peer-submission-msgid
                              (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                            (quote ("fn.test"))
                            (fn-peer-submission-octets
                              (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                        (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))))
            :durable)
          (equal
            o9
            (cdr
              (fn-own-finish
                o8
                *pcit-config*
                (list
                  (pcit-payload
                    (fn-ocfg-with-owner
                      *pcit-ihave*
                      (fn-own-make
                        (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-sub-make
                          (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                          (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                          (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                          (fn-inj-make-decision
                            :injected
                            nil
                            (fn-peer-submission-msgid
                              (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                            (quote ("fn.test"))
                            (fn-peer-submission-octets
                              (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                        (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                        (fn-own-refused (fn-ocfg-owner *pcit-ihave*)))))))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record
              (fn-ocfg-with-owner
                *pcit-ihave*
                (fn-own-make
                  (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-sub-make
                    (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-ihave*)))
                    (fn-inj-make-decision
                      :injected
                      nil
                      (fn-peer-submission-msgid
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))
                      (quote ("fn.test"))
                      (fn-peer-submission-octets
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))))))
                  (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                  (fn-own-refused (fn-ocfg-owner *pcit-ihave*)))))
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-nine-step-corrupted-state-without-transit-shape
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-make
             (fn-own-store (fn-ocfg-owner *pcit-takethis*))
             (fn-own-view (fn-ocfg-owner *pcit-takethis*))
             (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
             (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
             (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
             (fn-own-config (fn-ocfg-owner *pcit-takethis*))
             (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
             (fn-own-sub-make
               (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
               (fn-inj-make-decision
                 :injected
                 nil
                 (fn-peer-submission-msgid
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                 (quote ("fn.test"))
                 (fn-peer-submission-octets
                   (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
             (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
             (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w
        (fn-row-wire-of
          (pcit-record
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-inj-make-decision
                    :injected
                    nil
                    (fn-peer-submission-msgid
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                    (quote ("fn.test"))
                    (fn-peer-submission-octets
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*)))))
          (list
            (pcit-payload
              (fn-ocfg-with-owner
                *pcit-takethis*
                (fn-own-make
                  (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-sub-make
                    (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-inj-make-decision
                      :injected
                      nil
                      (fn-peer-submission-msgid
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                      (quote ("fn.test"))
                      (fn-peer-submission-octets
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                  (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store
            (fn-pcx-store-script
              (list
                :prepare
                (pcit-record
                  (fn-ocfg-with-owner
                    *pcit-takethis*
                    (fn-own-make
                      (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-sub-make
                        (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                        (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                        (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                        (fn-inj-make-decision
                          :injected
                          nil
                          (fn-peer-submission-msgid
                            (fn-own-sub-decision
                              (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                          (quote ("fn.test"))
                          (fn-peer-submission-octets
                            (fn-own-sub-decision
                              (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                      (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                      (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))))
          (list
            (pcit-payload
              (fn-ocfg-with-owner
                *pcit-takethis*
                (fn-own-make
                  (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-sub-make
                    (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-inj-make-decision
                      :injected
                      nil
                      (fn-peer-submission-msgid
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                      (quote ("fn.test"))
                      (fn-peer-submission-octets
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                  (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script
            (list
              :prepare
              (pcit-record
                (fn-ocfg-with-owner
                  *pcit-takethis*
                  (fn-own-make
                    (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-sub-make
                      (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                      (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                      (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                      (fn-inj-make-decision
                        :injected
                        nil
                        (fn-peer-submission-msgid
                          (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                        (quote ("fn.test"))
                        (fn-peer-submission-octets
                          (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                    (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-refused (fn-ocfg-owner *pcit-takethis*)))))))
          (list
            (pcit-payload
              (fn-ocfg-with-owner
                *pcit-takethis*
                (fn-own-make
                  (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-sub-make
                    (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-inj-make-decision
                      :injected
                      nil
                      (fn-peer-submission-msgid
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                      (quote ("fn.test"))
                      (fn-peer-submission-octets
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                  (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))))
      (pair
        (fn-sf-record-pair
          (pcit-record
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-inj-make-decision
                    :injected
                    nil
                    (fn-peer-submission-msgid
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                    (quote ("fn.test"))
                    (fn-peer-submission-octets
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*)))))))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-inj-make-decision
                    :injected
                    nil
                    (fn-peer-submission-msgid
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                    (quote ("fn.test"))
                    (fn-peer-submission-octets
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep
          s
          (pcit-record
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-sub-make
                  (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                  (fn-inj-make-decision
                    :injected
                    nil
                    (fn-peer-submission-msgid
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                    (quote ("fn.test"))
                    (fn-peer-submission-octets
                      (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
        (eq
          (fn-th-at
            0
            (fn-th-prefix-step
              (fn-sn-topic s)
              (pcit-record
                (fn-ocfg-with-owner
                  *pcit-takethis*
                  (fn-own-make
                    (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-sub-make
                      (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                      (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                      (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                      (fn-inj-make-decision
                        :injected
                        nil
                        (fn-peer-submission-msgid
                          (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                        (quote ("fn.test"))
                        (fn-peer-submission-octets
                          (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                    (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                    (fn-own-refused (fn-ocfg-owner *pcit-takethis*)))))))
          :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (fn-own-transit-subp sub))
      (not
        (and
          (equal
            (len
              (fn-pcx-post-script
                (list
                  :prepare
                  (pcit-record
                    (fn-ocfg-with-owner
                      *pcit-takethis*
                      (fn-own-make
                        (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-sub-make
                          (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                          (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                          (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                          (fn-inj-make-decision
                            :injected
                            nil
                            (fn-peer-submission-msgid
                              (fn-own-sub-decision
                                (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                            (quote ("fn.test"))
                            (fn-peer-submission-octets
                              (fn-own-sub-decision
                                (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                        (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))))
            *fn-pcx-post-steps*)
          (equal
            (car
              (fn-own-finish
                o8
                *pcit-config*
                (list
                  (pcit-payload
                    (fn-ocfg-with-owner
                      *pcit-takethis*
                      (fn-own-make
                        (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-sub-make
                          (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                          (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                          (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                          (fn-inj-make-decision
                            :injected
                            nil
                            (fn-peer-submission-msgid
                              (fn-own-sub-decision
                                (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                            (quote ("fn.test"))
                            (fn-peer-submission-octets
                              (fn-own-sub-decision
                                (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                        (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))))
            :durable)
          (equal
            o9
            (cdr
              (fn-own-finish
                o8
                *pcit-config*
                (list
                  (pcit-payload
                    (fn-ocfg-with-owner
                      *pcit-takethis*
                      (fn-own-make
                        (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-sub-make
                          (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                          (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                          (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                          (fn-inj-make-decision
                            :injected
                            nil
                            (fn-peer-submission-msgid
                              (fn-own-sub-decision
                                (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                            (quote ("fn.test"))
                            (fn-peer-submission-octets
                              (fn-own-sub-decision
                                (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                        (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                        (fn-own-refused (fn-ocfg-owner *pcit-takethis*)))))))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record
              (fn-ocfg-with-owner
                *pcit-takethis*
                (fn-own-make
                  (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-sub-make
                    (fn-own-sub-id (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-own-sub-version (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-own-sub-mark (fn-own-inflight (fn-ocfg-owner *pcit-takethis*)))
                    (fn-inj-make-decision
                      :injected
                      nil
                      (fn-peer-submission-msgid
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))
                      (quote ("fn.test"))
                      (fn-peer-submission-octets
                        (fn-own-sub-decision (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))))))
                  (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                  (fn-own-refused (fn-ocfg-owner *pcit-takethis*)))))
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

; Explicit corrupted-state removals: only the named store field is changed.
(defthm
  pcit-ihave-nine-step-corrupted-state-without-store-state
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-make
             (fn-sn-make-v6
               (fn-sn-groups (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-capacity (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sf-make-fields
                 (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                 (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                 (fn-sf-frontier-candidate
                   (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                 (fn-sf-records-field (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                 (fn-sf-record-candidate
                   (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                 (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                 (fn-sf-successes-field (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                 -1)
               (fn-sn-node (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-keyring (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-index (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-verdicts (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-keyring-snapshots (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-identity-next (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-config-history (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-consumer (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-topic (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-event-index (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
             (fn-own-view (fn-ocfg-owner *pcit-ihave*))
             (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
             (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
             (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
             (fn-own-config (fn-ocfg-owner *pcit-ihave*))
             (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
             (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))
             (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
             (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-ihave*) (list (pcit-payload *pcit-ihave*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
          (list (pcit-payload *pcit-ihave*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
          (list (pcit-payload *pcit-ihave*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-ihave*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-sn-make-v6
                  (fn-sn-groups (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-capacity (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sf-make-fields
                    (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                    (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                    (fn-sf-frontier-candidate
                      (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                    (fn-sf-records-field
                      (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                    (fn-sf-record-candidate
                      (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                    (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                    (fn-sf-successes-field
                      (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                    -1)
                  (fn-sn-node (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-keyring (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-index (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-verdicts (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-keyring-snapshots (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-identity-next (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-config-history (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-consumer (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-topic (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-event-index (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-pcx-admissiblep s (pcit-record *pcit-ihave*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-ihave*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (fn-sn-statep s))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-ihave*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-nine-step-corrupted-state-without-admission
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-make
             (fn-sn-with-configuration
               (fn-own-store (fn-ocfg-owner *pcit-ihave*))
               (fn-sn-groups (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               0
               (fn-sn-node (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
               (fn-sn-config-history (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
             (fn-own-view (fn-ocfg-owner *pcit-ihave*))
             (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
             (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
             (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
             (fn-own-config (fn-ocfg-owner *pcit-ihave*))
             (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
             (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))
             (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
             (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-ihave*) (list (pcit-payload *pcit-ihave*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
          (list (pcit-payload *pcit-ihave*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
          (list (pcit-payload *pcit-ihave*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-ihave*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-sn-with-configuration
                  (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                  (fn-sn-groups (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  0
                  (fn-sn-node (fn-own-store (fn-ocfg-owner *pcit-ihave*)))
                  (fn-sn-config-history (fn-own-store (fn-ocfg-owner *pcit-ihave*))))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-ihave*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (fn-pcx-admissiblep s (pcit-record *pcit-ihave*)))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-ihave*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-ihave-nine-step-corrupted-state-without-topic-prefix
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-make
             (fn-sn-with-topic
               (fn-own-store (fn-ocfg-owner *pcit-ihave*))
               (fn-th-prefix-state :fault 0 nil nil nil nil :sequence))
             (fn-own-view (fn-ocfg-owner *pcit-ihave*))
             (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
             (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
             (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
             (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
             (fn-own-config (fn-ocfg-owner *pcit-ihave*))
             (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
             (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))
             (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
             (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-ihave*) (list (pcit-payload *pcit-ihave*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-ihave*))))
          (list (pcit-payload *pcit-ihave*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
          (list (pcit-payload *pcit-ihave*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-ihave*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-ihave*
              (fn-own-make
                (fn-sn-with-topic
                  (fn-own-store (fn-ocfg-owner *pcit-ihave*))
                  (fn-th-prefix-state :fault 0 nil nil nil nil :sequence))
                (fn-own-view (fn-ocfg-owner *pcit-ihave*))
                (fn-own-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-next-id (fn-ocfg-owner *pcit-ihave*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-ihave*))
                (fn-own-pending (fn-ocfg-owner *pcit-ihave*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-ihave*))
                (fn-own-clock (fn-ocfg-owner *pcit-ihave*))
                (fn-own-facts (fn-ocfg-owner *pcit-ihave*))
                (fn-own-config (fn-ocfg-owner *pcit-ihave*))
                (fn-own-queue (fn-ocfg-owner *pcit-ihave*))
                (fn-own-inflight (fn-ocfg-owner *pcit-ihave*))
                (fn-own-feeds (fn-ocfg-owner *pcit-ihave*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-ihave*))
                (fn-own-refused (fn-ocfg-owner *pcit-ihave*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-ihave*))
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-ihave*))) :ok))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-ihave*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-ihave*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-nine-step-corrupted-state-without-store-state
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-make
             (fn-sn-make-v6
               (fn-sn-groups (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-capacity (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sf-make-fields
                 (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                 (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                 (fn-sf-frontier-candidate
                   (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                 (fn-sf-records-field
                   (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                 (fn-sf-record-candidate
                   (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                 (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                 (fn-sf-successes-field
                   (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                 -1)
               (fn-sn-node (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-keyring (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-index (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-verdicts (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-keyring-snapshots (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-identity-next (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-config-history (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-consumer (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-topic (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-event-index (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
             (fn-own-view (fn-ocfg-owner *pcit-takethis*))
             (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
             (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
             (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
             (fn-own-config (fn-ocfg-owner *pcit-takethis*))
             (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
             (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))
             (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
             (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-takethis*) (list (pcit-payload *pcit-takethis*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
          (list (pcit-payload *pcit-takethis*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
          (list (pcit-payload *pcit-takethis*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-takethis*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-sn-make-v6
                  (fn-sn-groups (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-capacity (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sf-make-fields
                    (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                    (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                    (fn-sf-frontier-candidate
                      (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                    (fn-sf-records-field
                      (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                    (fn-sf-record-candidate
                      (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                    (fn-sf-completion
                      (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                    (fn-sf-successes-field
                      (fn-sn-files (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                    -1)
                  (fn-sn-node (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-keyring (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-index (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-verdicts (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-keyring-snapshots (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-identity-next (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-config-history (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-consumer (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-topic (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-event-index (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-pcx-admissiblep s (pcit-record *pcit-takethis*))
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-takethis*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (fn-sn-statep s))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-takethis*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-nine-step-corrupted-state-without-admission
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-make
             (fn-sn-with-configuration
               (fn-own-store (fn-ocfg-owner *pcit-takethis*))
               (fn-sn-groups (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               0
               (fn-sn-node (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
               (fn-sn-config-history (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
             (fn-own-view (fn-ocfg-owner *pcit-takethis*))
             (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
             (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
             (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
             (fn-own-config (fn-ocfg-owner *pcit-takethis*))
             (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
             (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))
             (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
             (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-takethis*) (list (pcit-payload *pcit-takethis*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
          (list (pcit-payload *pcit-takethis*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
          (list (pcit-payload *pcit-takethis*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-takethis*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-sn-with-configuration
                  (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                  (fn-sn-groups (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  0
                  (fn-sn-node (fn-own-store (fn-ocfg-owner *pcit-takethis*)))
                  (fn-sn-config-history (fn-own-store (fn-ocfg-owner *pcit-takethis*))))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-takethis*))) :ok)
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not (fn-pcx-admissiblep s (pcit-record *pcit-takethis*)))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-takethis*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-nine-step-corrupted-state-without-topic-prefix
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-make
             (fn-sn-with-topic
               (fn-own-store (fn-ocfg-owner *pcit-takethis*))
               (fn-th-prefix-state :fault 0 nil nil nil nil :sequence))
             (fn-own-view (fn-ocfg-owner *pcit-takethis*))
             (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
             (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
             (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
             (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
             (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
             (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
             (fn-own-config (fn-ocfg-owner *pcit-takethis*))
             (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
             (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))
             (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
             (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
             (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))))
      (s (fn-own-store o))
      (sub (fn-own-inflight o))
      (w (fn-row-wire-of (pcit-record *pcit-takethis*) (list (pcit-payload *pcit-takethis*))))
      (conn (fn-own-find-conn 0 (fn-own-conns o)))
      (o8
        (fn-own-run
          o
          (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare (pcit-record *pcit-takethis*))))
          (list (pcit-payload *pcit-takethis*))))
      (o9
        (fn-own-run
          o
          (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
          (list (pcit-payload *pcit-takethis*))))
      (pair (fn-sf-record-pair (pcit-record *pcit-takethis*)))
      (out
        (fn-oop-transit-outcome
          (fn-ocfg-with-owner
            (fn-ocfg-with-owner
              *pcit-takethis*
              (fn-own-make
                (fn-sn-with-topic
                  (fn-own-store (fn-ocfg-owner *pcit-takethis*))
                  (fn-th-prefix-state :fault 0 nil nil nil nil :sequence))
                (fn-own-view (fn-ocfg-owner *pcit-takethis*))
                (fn-own-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-next-id (fn-ocfg-owner *pcit-takethis*))
                (fn-own-max-conns (fn-ocfg-owner *pcit-takethis*))
                (fn-own-pending (fn-ocfg-owner *pcit-takethis*))
                (fn-own-ledger-field (fn-ocfg-owner *pcit-takethis*))
                (fn-own-clock (fn-ocfg-owner *pcit-takethis*))
                (fn-own-facts (fn-ocfg-owner *pcit-takethis*))
                (fn-own-config (fn-ocfg-owner *pcit-takethis*))
                (fn-own-queue (fn-ocfg-owner *pcit-takethis*))
                (fn-own-inflight (fn-ocfg-owner *pcit-takethis*))
                (fn-own-feeds (fn-ocfg-owner *pcit-takethis*))
                (fn-own-node-secret (fn-ocfg-owner *pcit-takethis*))
                (fn-own-refused (fn-ocfg-owner *pcit-takethis*))))
            o9)
          0
          :want
          nil
          :durable)))
    (and
      (and
        (fn-sn-statep s)
        (fn-pcx-admissiblep s (pcit-record *pcit-takethis*))
        (equal (fn-own-sub-id sub) 0)
        conn
        (fn-own-transit-subp sub)
        (natp (fn-own-sub-mark sub))
        (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
        (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
        (equal
          (fn-record-payload w)
          (fn-own-sub-stored-octets *pcit-config* sub (fn-own-node-secret o))))
      (not
        (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) (pcit-record *pcit-takethis*))) :ok))
      (not
        (and
          (equal
            (len (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*))))
            *fn-pcx-post-steps*)
          (equal
            (car (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*))))
            :durable)
          (equal o9 (cdr (fn-own-finish o8 *pcit-config* (list (pcit-payload *pcit-takethis*)))))
          (fn-own-completion-consumedp o9)
          (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
          (equal
            (fn-sf-successes (fn-sn-files (fn-own-store o9)))
            (append (fn-sf-successes (fn-sn-files s)) (list pair)))
          (member-equal
            (pcit-record *pcit-takethis*)
            (fn-sf-records (fn-sn-files (fn-own-store o9))))
          (equal
            (fn-served-reply-octets (car out))
            (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))))
  :rule-classes
  nil)

; Direct full antecedent/conclusion positives for the host-outcome theorem.
(defthm
  pcit-ihave-host-complete-positive
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-ihave*
           (fn-own-run
             (fn-ocfg-owner *pcit-ihave*)
             (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
             (list (pcit-payload *pcit-ihave*))))))
      (sub (fn-own-inflight o))
      (conn (fn-own-find-conn 0 (fn-own-conns o))))
    (and
      (and
        conn
        (equal (fn-own-sub-id sub) 0)
        (fn-own-transit-subp sub)
        (fn-own-completion-consumedp o))
      (equal
        (fn-served-reply-octets
          (car
            (fn-oop-transit-outcome
              (fn-ocfg-with-owner
                *pcit-ihave*
                (fn-own-run
                  (fn-ocfg-owner *pcit-ihave*)
                  (fn-pcx-post-script (list :prepare (pcit-record *pcit-ihave*)))
                  (list (pcit-payload *pcit-ihave*))))
              0
              :want
              nil
              :durable)))
        (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))
  :rule-classes
  nil)

(defthm
  pcit-takethis-host-complete-positive
  (let*
    ((o
       (fn-ocfg-owner
         (fn-ocfg-with-owner
           *pcit-takethis*
           (fn-own-run
             (fn-ocfg-owner *pcit-takethis*)
             (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
             (list (pcit-payload *pcit-takethis*))))))
      (sub (fn-own-inflight o))
      (conn (fn-own-find-conn 0 (fn-own-conns o))))
    (and
      (and
        conn
        (equal (fn-own-sub-id sub) 0)
        (fn-own-transit-subp sub)
        (fn-own-completion-consumedp o))
      (equal
        (fn-served-reply-octets
          (car
            (fn-oop-transit-outcome
              (fn-ocfg-with-owner
                *pcit-takethis*
                (fn-own-run
                  (fn-ocfg-owner *pcit-takethis*)
                  (fn-pcx-post-script (list :prepare (pcit-record *pcit-takethis*)))
                  (list (pcit-payload *pcit-takethis*))))
              0
              :want
              nil
              :durable)))
        (fn-pct-inbound-success-octets (fn-own-sub-decision sub)))))
  :rule-classes
  nil)
