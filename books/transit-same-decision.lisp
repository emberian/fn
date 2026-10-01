; fn: K6, one transit decision for both carriers (PKT-202, row Q3e of
; build/coordinator/COMPLETE-BEFORE-6.6.0.md; specs/bp-node-machine.md section 6).
;
; A peer's article reaches the Store by two carriers.  NNTP: IHAVE/TAKETHIS
; enqueue (fn-peer-make-submission PEER KIND MSGID OCTETS) under the session's
; peer; host/native/owner.lisp fnn-owner-drain-one takes it and decides.  BP:
; host/owner-host.lisp fn-owner-bp-transit-submit gates the delivery with
; fn-own-bp-transit-submit-result and enqueues the same record with KIND
; :takethis under the control id; host/native/owner.lisp
; fnn-owner-complete-bp-transit-submission takes it and decides.  Both
; decisions are host/owner-host.lisp fn-owner-transit-decide, which calls
; fn-pta-decide over the owner's in-flight submission; `fn-tsd-drain-decision'
; below is that call, argument for argument (the host's octet-to-string
; conversion of the obligation id and subject aside).  The keystones are
; MODEL-LEVEL: no host code calls fn-tsd-drain-decision yet, and no theorem
; equates it with fn-owner-transit-decide (its octet conversion, :bad arm and
; decision globals) or the direct submit/take composition with the host's
; fn-owner-step / fn-ocfg-step path.  That join is OPEN: the AUTHORITY-FIELD
; lane rewires fn-owner-transit-decide to call fn-tsd-drain-decision.
;
; KEYSTONES
;   fn-tsd-bp-gate-is-the-drain-decision: a BP delivery the gate submits is,
;     after the enqueue and the owner's take, the in-flight TAKETHIS record of
;     the same peer, Message-ID and octets, and the drain's byte decision is
;     the gate's own (fn-peer-decide-transfer-under over the same node,
;     clock and limits), :want.  The gate and the drain cannot disagree.
;   fn-tsd-nntp-and-bp-transit-decide-alike: an NNTP transit in flight with the
;     same peer, Message-ID and octets, over the same store, clock and limits,
;     gets the same byte decision.
;   fn-tsd-open-connection-pin-is-not-the-control-pin: in a configured owner
;     state, an open connection's pinned configuration is never the control
;     id's: while an NNTP transit's connection is open, the two carriers'
;     authority configurations differ, and the verdicts are compared by
;     fn-tsd-bp-transit-authority-is-ungoverned, not equated.  OPEN: no
;     carried invariant ties an in-flight or queued submission's id to an
;     open connection (fn-own-relation, fn-ocfg-statep do not); the tests
;     witness that fn-ocfg-close drops the connection's in-flight
;     submission, which is not a preservation proof.
;   Neither keystone needs (stringp peer): a submitted BP delivery names a
;   configured peer, whose name is a string (fn-tsd-submitted-names-a-string-peer).
;
; WHERE THEY CAN DIFFER (named, not hidden):
;   1. The principal.  NNTP's PEER is the session's (fn-peer-session-peer,
;      set at connect by fn-owner-peer-for-address); BP's is
;      fn-bpaj-ingress-peer (books/bp-transit-join.lisp, the D23 source
;      decision).  The keystones take PEER as an input: equal principals,
;      equal decisions.
;   2. The authority configuration.  fn-owner-transit-decide reads the
;      authority under (fn-ocfg-conn-config oc (fn-own-sub-id sub)); a BP
;      submission's id is :control, which no pin names, so its authority
;      verdict is :ungoverned (or :none off :want) whatever the groups'
;      configured authorities: fn-tsd-bp-transit-authority-is-ungoverned.  The
;      verdict is logged, not acted on (fn-owner-transit-log-line); BP
;      transit never carries a governed verdict.  A host fix (the live
;      configuration for the control id) is queued after stage 0.
(in-package "ACL2")
(include-book "owner-config")
(include-book "peer-transit-authority")
(include-book "transit-header-limits")

; The decision host/owner-host.lisp fn-owner-transit-decide makes for the
; owner's in-flight submission.  :verify-guards nil: fn-pta-decide's guard
; (fn-node-statep, fn-prin-keyringp) is the owner relation's; guards are owed
; when the host calls this (GEN: none; the host rewire is the next step).
(defun fn-tsd-drain-decision (o oc cfg id subject)
  (declare (xargs :guard t :verify-guards nil))
  (let ((sub (fn-own-inflight o)))
    (if (not (fn-own-transit-subp sub))
        (mv :not-transit :none)
      (let* ((decision (fn-own-sub-decision sub))
             (store (fn-own-store o))
             (acfg (fn-ocfg-conn-config oc (fn-own-sub-id sub))))
        (fn-pta-decide (fn-sn-index store) (fn-sn-keyring store)
                       (fn-cfg-value acfg) (fn-cfg-generation acfg)
                       (fn-sn-node store) cfg
                       (fn-peer-submission-peer decision)
                       (fn-peer-submission-msgid decision)
                       (fn-peer-submission-octets decision)
                       (fn-own-clock o) id subject
                       (fn-own-config-header-limits (fn-own-config o)))))))

(local (defthm fn-tsd-want-has-a-message-id
  (implies (equal (fn-peer-decision-kind
                   (fn-peer-decide-transfer node cfg peer msgid octets clock id subject))
                  :want)
           (fn-af-message-idp msgid))
  :hints (("Goal" :in-theory (e/d (fn-peer-decide-transfer)
                                  (fn-af-message-idp fn-article-parse
                                   fn-peer-intrinsic-refusal-of fn-peer-scope-groups
                                   fn-peer-date-futurep fn-peer-path-missingp
                                   fn-peer-history-hasp fn-path-names-p))))))

; A Message-ID is printable (RFC 5536 3.1.3's msg-id is visible ASCII), so the
; in-flight record is a peer submission without a separate token hypothesis.
(local (defthm fn-tsd-printable-of-append
  (equal (fn-nntp-printable-tokenp (append x y))
         (and (fn-nntp-printable-tokenp x) (fn-nntp-printable-tokenp y)))
  :hints (("Goal" :in-theory (enable fn-nntp-printable-tokenp)))))
(local (defthm fn-tsd-printable-of-revappend
  (equal (fn-nntp-printable-tokenp (revappend x y))
         (and (fn-nntp-printable-tokenp x) (fn-nntp-printable-tokenp y)))
  :hints (("Goal" :in-theory (enable fn-nntp-printable-tokenp revappend)))))
(local (defthm fn-tsd-printable-of-reverse
  (equal (fn-nntp-printable-tokenp (reverse x))
         (fn-nntp-printable-tokenp x))
  :hints (("Goal" :in-theory (enable fn-nntp-printable-tokenp reverse)))))
(local (defthm fn-tsd-dot-atom-is-printable
  (implies (fn-af-dot-atom-text-aux b w) (fn-nntp-printable-tokenp b))
  :hints (("Goal" :in-theory (enable fn-af-dot-atom-text-aux fn-af-atextp
                                     fn-nntp-printable-tokenp)))))
(local (defthm fn-tsd-literal-is-printable
  (implies (fn-af-no-fold-literal-restp b) (fn-nntp-printable-tokenp b))
  :hints (("Goal" :in-theory (enable fn-af-no-fold-literal-restp fn-af-mdtextp
                                     fn-nntp-printable-tokenp)))))
(local (defthm fn-tsd-id-right-is-printable
  (implies (fn-af-id-rightp b) (fn-nntp-printable-tokenp b))
  :hints (("Goal" :in-theory (enable fn-af-id-rightp fn-af-dot-atom-textp
                                     fn-nntp-printable-tokenp)))))
(local (defthm fn-tsd-core-is-printable
  (implies (fn-af-msg-id-core-aux b l) (fn-nntp-printable-tokenp (revappend l b)))
  :hints (("Goal" :induct (fn-af-msg-id-core-aux b l)
                  :in-theory (enable fn-af-msg-id-core-aux fn-af-dot-atom-textp
                                     fn-nntp-printable-tokenp)))))
(local (defthm fn-tsd-corep-is-printable
  (implies (fn-af-msg-id-corep b) (fn-nntp-printable-tokenp b))
  :hints (("Goal" :use ((:instance fn-tsd-core-is-printable (l nil)))
                  :in-theory (e/d (fn-af-msg-id-corep) (fn-tsd-core-is-printable))))))
(local (defthm fn-tsd-close-is-printable
  (implies (fn-af-msg-id-closep b r) (fn-nntp-printable-tokenp (revappend r b)))
  :hints (("Goal" :induct (fn-af-msg-id-closep b r)
                  :in-theory (e/d (fn-af-msg-id-closep fn-nntp-printable-tokenp)
                                  (fn-af-msg-id-corep))))))
(local (defthm fn-tsd-message-id-is-printable
  (implies (fn-af-message-idp m) (fn-nntp-printable-tokenp m))
  :hints (("Goal" :use ((:instance fn-tsd-close-is-printable (b (cdr m)) (r nil)))
                  :in-theory (e/d (fn-af-message-idp fn-nntp-printable-tokenp)
                                  (fn-tsd-close-is-printable))))))

; A submitted BP delivery names a configured peer, and a peer record's name
; is a configuration label, a string: the gate needs no string hypothesis.
(local (defthm fn-tsd-peer-record-is-named-by-a-string
  (implies (fn-cfg-peerp (fn-cfg-peer-make name pid transport inbound outbound auth))
           (stringp name))
  :hints (("Goal" :in-theory (e/d (fn-cfg-peerp fn-cfg-labelp fn-record-ascii-stringp)
                                  (fn-cfg-peer-transportp fn-cfg-peer-inboundp))))))
(local (defthm fn-tsd-found-peer-is-named-by-a-string
  (implies (fn-cfg-peer-find name peers)
           (stringp name))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-cfg-peer-find fn-cfg-peer-of-rows
                                fn-tsd-peer-record-is-named-by-a-string)
                              (theory 'minimal-theory))))))
(local (defthm fn-tsd-want-names-a-configured-peer
  (implies (equal (fn-peer-decision-kind
                   (fn-peer-decide-transfer node cfg peer msgid octets clock id subject))
                  :want)
           (stringp peer))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-tsd-found-peer-is-named-by-a-string
                                   (name peer) (peers (fn-cfg-peers (fn-cfg-value cfg)))))
                  :in-theory (e/d (fn-peer-decide-transfer)
                                  (fn-af-message-idp fn-article-parse
                                   fn-peer-intrinsic-refusal-of fn-peer-scope-groups
                                   fn-peer-date-futurep fn-peer-path-missingp
                                   fn-peer-history-hasp fn-path-names-p fn-cfg-peer-find))))))
(defthm fn-tsd-submitted-names-a-string-peer
  (implies (equal (fn-own-bp-transit-submit-result o cfg peer msgid octets id subject)
                  :submitted)
           (stringp peer))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-peer-decide-transfer-under-wants-only-what-transfer-wants
                                   (node (fn-sn-node (fn-own-store o)))
                                   (clock (fn-own-clock o))
                                   (limits (fn-own-config-header-limits (fn-own-config o))))
                        (:instance fn-tsd-want-names-a-configured-peer
                                   (node (fn-sn-node (fn-own-store o)))
                                   (clock (fn-own-clock o))))
                  :in-theory (e/d (fn-own-bp-transit-submit-result)
                                  (fn-peer-decide-transfer-under-wants-only-what-transfer-wants
                                   fn-peer-decide-transfer-under fn-peer-decide-transfer
                                   fn-own-config-header-limits fn-article-parse-under
                                   fn-peer-relayed-octets)))))

(local (defthm fn-tsd-bp-gate-for-a-string-peer
  (implies (and (equal (fn-own-bp-transit-submit-result o cfg peer msgid octets id subject)
                       :submitted)
                (stringp peer))
           (let ((o2 (fn-own-take-submission
                      (fn-own-bp-transit-submit o cfg peer msgid octets id subject))))
             (and (fn-own-transit-inflightp o2)
                  (equal (fn-own-sub-id (fn-own-inflight o2)) *fn-own-control-id*)
                  (equal (fn-own-sub-decision (fn-own-inflight o2))
                         (fn-peer-make-submission peer :takethis msgid octets))
                  (equal (mv-nth 0 (fn-tsd-drain-decision o2 oc cfg id subject))
                         (fn-peer-decide-transfer-under
                          (fn-sn-node (fn-own-store o)) cfg peer msgid octets
                          (fn-own-clock o) id subject
                          (fn-own-config-header-limits (fn-own-config o))))
                  (equal (fn-peer-decision-kind
                          (mv-nth 0 (fn-tsd-drain-decision o2 oc cfg id subject)))
                         :want))))
  :hints (("Goal" :use ((:instance fn-peer-decide-transfer-under-wants-only-what-transfer-wants
                                    (node (fn-sn-node (fn-own-store o)))
                                    (clock (fn-own-clock o))
                                    (limits (fn-own-config-header-limits (fn-own-config o)))))
                  :in-theory (e/d (fn-own-bp-transit-submit-result fn-own-bp-transit-submit
                                   fn-own-take-submission fn-own-enqueue
                                   fn-own-transit-inflightp fn-own-transit-subp)
                                  (fn-af-message-idp fn-peer-decide-transfer-under
                                   fn-peer-decide-transfer fn-pta-decide
                                   fn-own-config-header-limits))))))

; KEYSTONE (PKT-202).
(defthm fn-tsd-bp-gate-is-the-drain-decision
  (implies (equal (fn-own-bp-transit-submit-result o cfg peer msgid octets id subject)
                  :submitted)
           (let ((o2 (fn-own-take-submission
                      (fn-own-bp-transit-submit o cfg peer msgid octets id subject))))
             (and (fn-own-transit-inflightp o2)
                  (equal (fn-own-sub-id (fn-own-inflight o2)) *fn-own-control-id*)
                  (equal (fn-own-sub-decision (fn-own-inflight o2))
                         (fn-peer-make-submission peer :takethis msgid octets))
                  (equal (mv-nth 0 (fn-tsd-drain-decision o2 oc cfg id subject))
                         (fn-peer-decide-transfer-under
                          (fn-sn-node (fn-own-store o)) cfg peer msgid octets
                          (fn-own-clock o) id subject
                          (fn-own-config-header-limits (fn-own-config o))))
                  (equal (fn-peer-decision-kind
                          (mv-nth 0 (fn-tsd-drain-decision o2 oc cfg id subject)))
                         :want))))
  :hints (("Goal" :use (fn-tsd-bp-gate-for-a-string-peer fn-tsd-submitted-names-a-string-peer)
                  :in-theory (union-theories '((:definition mv-nth))
                                             (theory 'minimal-theory)))))

(local (defthm fn-tsd-bp-take-keeps-the-deciding-state
  (implies (equal (fn-own-bp-transit-submit-result o cfg peer msgid octets id subject)
                  :submitted)
           (let ((b (fn-own-take-submission
                     (fn-own-bp-transit-submit o cfg peer msgid octets id subject))))
             (and (equal (fn-own-store b) (fn-own-store o))
                  (equal (fn-own-clock b) (fn-own-clock o))
                  (equal (fn-own-config b) (fn-own-config o)))))
  :hints (("Goal" :in-theory (e/d (fn-own-bp-transit-submit-result fn-own-bp-transit-submit
                                   fn-own-take-submission fn-own-enqueue)
                                  (fn-af-message-idp fn-peer-decide-transfer-under
                                   fn-peer-decide-transfer))))))

(local (defthm fn-tsd-bp-take-inflight
  (implies (and (equal (fn-own-bp-transit-submit-result o cfg peer msgid octets id subject)
                       :submitted)
                (stringp peer))
           (let ((b (fn-own-take-submission
                     (fn-own-bp-transit-submit o cfg peer msgid octets id subject))))
             (and (fn-own-transit-subp (fn-own-inflight b))
                  (equal (fn-own-sub-id (fn-own-inflight b)) *fn-own-control-id*)
                  (equal (fn-own-sub-decision (fn-own-inflight b))
                         (fn-peer-make-submission peer :takethis msgid octets)))))
  :hints (("Goal" :use (fn-tsd-bp-gate-is-the-drain-decision)
                  :in-theory (e/d (fn-own-transit-inflightp)
                                  (fn-tsd-bp-gate-is-the-drain-decision fn-own-transit-subp
                                   fn-own-take-submission fn-own-bp-transit-submit
                                   fn-own-bp-transit-submit-result fn-tsd-drain-decision))))))

(local (defthm fn-tsd-car-of-pta-decide-by-definition
  (equal (car (fn-pta-decide index keyring v gen node cfg peer msgid octets clock id
                             subject limits))
         (fn-peer-decide-transfer-under node cfg peer msgid octets clock id subject limits))
  :hints (("Goal" :use fn-pta-decide-keeps-the-byte-decision-by-definition
                  :in-theory (disable fn-pta-decide-keeps-the-byte-decision-by-definition
                                      fn-peer-decide-transfer-under)))))

(local (defthm fn-tsd-decide-alike-for-a-string-peer
  (implies (and (equal (fn-own-bp-transit-submit-result o cfg peer msgid octets id subject)
                       :submitted)
                (stringp peer)
                (fn-own-transit-inflightp n)
                (equal (fn-own-sub-decision (fn-own-inflight n))
                       (fn-peer-make-submission peer kind msgid octets))
                (equal (fn-own-store n) (fn-own-store o))
                (equal (fn-own-clock n) (fn-own-clock o))
                (equal (fn-own-config-header-limits (fn-own-config n))
                       (fn-own-config-header-limits (fn-own-config o))))
           (let ((b (fn-own-take-submission
                     (fn-own-bp-transit-submit o cfg peer msgid octets id subject))))
             (and (equal (mv-nth 0 (fn-tsd-drain-decision n oc cfg id subject))
                         (mv-nth 0 (fn-tsd-drain-decision b oc cfg id subject)))
                  (implies (equal (fn-ocfg-conn-config oc (fn-own-sub-id (fn-own-inflight n)))
                                  (fn-ocfg-conn-config oc *fn-own-control-id*))
                           (equal (fn-tsd-drain-decision n oc cfg id subject)
                                  (fn-tsd-drain-decision b oc cfg id subject))))))
  :hints (("Goal" :in-theory (e/d (fn-tsd-drain-decision fn-own-transit-inflightp)
                                  (fn-pta-decide fn-pta-decide-keeps-the-byte-decision-by-definition
                                   fn-pta-verdict-only-on-want-by-definition
                                   fn-own-take-submission fn-own-bp-transit-submit
                                   fn-own-bp-transit-submit-result
                                   fn-af-message-idp fn-peer-decide-transfer-under
                                   fn-peer-decide-transfer
                                   fn-own-config-header-limits fn-own-transit-subp
                                   fn-ocfg-conn-config fn-tsd-bp-gate-is-the-drain-decision
                                   fn-peer-make-submission))))))

; KEYSTONE (PKT-202).
(defthm fn-tsd-nntp-and-bp-transit-decide-alike
  (implies (and (equal (fn-own-bp-transit-submit-result o cfg peer msgid octets id subject)
                       :submitted)
                (fn-own-transit-inflightp n)
                (equal (fn-own-sub-decision (fn-own-inflight n))
                       (fn-peer-make-submission peer kind msgid octets))
                (equal (fn-own-store n) (fn-own-store o))
                (equal (fn-own-clock n) (fn-own-clock o))
                (equal (fn-own-config-header-limits (fn-own-config n))
                       (fn-own-config-header-limits (fn-own-config o))))
           (equal (mv-nth 0 (fn-tsd-drain-decision n oc cfg id subject))
                  (mv-nth 0 (fn-tsd-drain-decision
                             (fn-own-take-submission
                              (fn-own-bp-transit-submit o cfg peer msgid octets id subject))
                             oc cfg id subject))))
  :hints (("Goal" :use (fn-tsd-decide-alike-for-a-string-peer
                        fn-tsd-submitted-names-a-string-peer)
                  :in-theory (theory 'minimal-theory))))

; Where the carriers differ: BP's authority verdict is over no configuration.
(local (defthm fn-tsd-pinned-id-is-a-connection
  (implies (and (fn-ocfg-pins-pin-conns-only pins conns)
                (fn-ocfg-pin-find id pins))
           (fn-own-find-conn id conns))
  :hints (("Goal" :in-theory (enable fn-ocfg-pins-pin-conns-only fn-ocfg-pin-find)))))
(local (defthm fn-tsd-control-is-no-connection
  (implies (fn-own-ids-below-next-p conns next)
           (not (fn-own-find-conn :control conns)))
  :hints (("Goal" :in-theory (enable fn-own-ids-below-next-p fn-own-find-conn)))))
(local (defthm fn-tsd-control-has-no-pin
  (implies (fn-ocfg-statep oc)
           (equal (fn-ocfg-conn-config oc :control) nil))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-statep fn-ocfg-conn-config fn-own-relation)
                                  (fn-tsd-pinned-id-is-a-connection))
                  :use ((:instance fn-tsd-pinned-id-is-a-connection
                                   (id :control)
                                   (pins (fn-ocfg-pins oc))
                                   (conns (fn-own-conns (fn-ocfg-owner oc))))
                        (:instance fn-tsd-control-is-no-connection
                                   (conns (fn-own-conns (fn-ocfg-owner oc)))
                                   (next (fn-own-next-id (fn-ocfg-owner oc)))))))))
;; An open connection holds a pin (fn-ocfg-conns-pinnedp), and a pin is a
;; well-formed configuration (fn-ocfg-pins-okp), never the control id's nil.
(local (defthm fn-tsd-open-conn-is-pinned
  (implies (and (fn-ocfg-conns-pinnedp conns pins)
                (fn-own-find-conn id conns))
           (fn-ocfg-pin-find id pins))
  :hints (("Goal" :in-theory (enable fn-ocfg-conns-pinnedp fn-own-find-conn)))))
(local (defthm fn-tsd-found-pin-is-a-configuration
  (implies (and (fn-ocfg-pins-okp pins)
                (fn-ocfg-pin-find id pins))
           (fn-cfgp (cdr (fn-ocfg-pin-find id pins))))
  :hints (("Goal" :in-theory (enable fn-ocfg-pins-okp fn-ocfg-pin-find)))))
; KEYSTONE (PKT-202).
(defthm fn-tsd-open-connection-pin-is-not-the-control-pin
  (implies (and (fn-ocfg-statep oc)
                (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
           (not (equal (fn-ocfg-conn-config oc id)
                       (fn-ocfg-conn-config oc *fn-own-control-id*))))
  :hints (("Goal" :use (fn-tsd-control-has-no-pin
                        (:instance fn-tsd-open-conn-is-pinned
                                   (conns (fn-own-conns (fn-ocfg-owner oc)))
                                   (pins (fn-ocfg-pins oc)))
                        (:instance fn-tsd-found-pin-is-a-configuration
                                   (pins (fn-ocfg-pins oc))))
                  :in-theory (e/d (fn-ocfg-statep fn-ocfg-conn-config (:e fn-cfgp))
                                  (fn-tsd-open-conn-is-pinned
                                   fn-tsd-found-pin-is-a-configuration
                                   fn-tsd-control-has-no-pin
                                   fn-own-relation fn-cfgp)))))
(local (defthm fn-tsd-no-configuration-group-authority
  (equal (fn-pta-group-authority nil nil name) nil)
  :hints (("Goal" :in-theory (enable fn-pta-group-authority fn-cfg-group-find)))))
(local (defthm fn-tsd-no-configuration-is-ungoverned
  (equal (fn-pta-groups-verdict index keyring nil nil names s) :ungoverned)
  :hints (("Goal" :in-theory (e/d (fn-pta-groups-verdict) (fn-pta-group-authority))))))
; The subject is the host's own call: fn-owner-transit-decide passes
; fn-pta-decide the authority configuration (fn-ocfg-conn-config oc ID) for the
; in-flight submission's ID, and a BP submission's ID is the control id.
(defthm fn-tsd-bp-transit-authority-is-ungoverned
  (implies (fn-ocfg-statep oc)
           (member-equal
            (mv-nth 1 (fn-pta-decide index keyring
                                     (fn-cfg-value (fn-ocfg-conn-config oc *fn-own-control-id*))
                                     (fn-cfg-generation
                                      (fn-ocfg-conn-config oc *fn-own-control-id*))
                                     node cfg peer msgid octets clock id subject limits))
            '(:ungoverned :none)))
  :hints (("Goal" :in-theory (e/d (fn-pta-decide)
                                  (fn-pta-groups-verdict fn-ocfg-statep
                                   fn-peer-decide-transfer-under
                                   fn-peer-injection-arguments fn-stx-parse
                                   fn-peer-relayed-octets)))))
