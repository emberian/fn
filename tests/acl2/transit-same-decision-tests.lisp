; Teeth for books/transit-same-decision (PKT-202, K6): per keystone a
; reachable witness asserting the whole antecedent and conclusion, a
; single-hypothesis removal per hypothesis that checks every retained
; hypothesis, the omitted one failing and the conclusion failing (REACHABLE
; unless labelled CORRUPTED), and a labelled MUTATION.  Both carriers run
; through the configured owner's own step (fn-ocfg-step, the host's
; fn-owner-step path): the NNTP transit opens a peer connection, reads IHAVE
; and the article, and takes; the BP transit is gated, enqueued and taken.
; Fixtures: tests/acl2/transit-header-limits-tests (an owner whose limits
; admit *pt-noloop* from the configured peer "innA"; *pt-cfg*).
(in-package "ACL2")
(include-book "../../books/transit-same-decision")
(include-book "../../books/config-records")
(include-book "transit-header-limits-tests")
(include-book "held-rows-tests")
(include-book "arena-lift")
(include-book "must-fail-checked")

;; No byte is read from the arena here.
(defconst *sr-arena* nil)
(bpr-lift fn-ocfg-step 2)
(defun tsdt-run (oc events)
  (if (consp events)
      (tsdt-run (in-arena-fn-ocfg-step *sr-arena* oc (car events)) (cdr events))
    oc))

; -----------------------------------------------------------------------------
; The BP delivery, gated, enqueued and taken as the host does
; (fn-owner-bp-transit-submit, then fnn-owner-take's (:take)).

(defconst *tsdt-o* (thlt-owner '(6 6 200)))
(defun tsdt-take (o peer octets)
  (fn-own-take-submission
   (fn-own-bp-transit-submit o *pt-cfg* peer *pt-idloop* octets "ob" "s")))
(defconst *tsdt-b* (tsdt-take *tsdt-o* "innA" *pt-noloop*))
; The decision as a list (its two values), for assertions.
(defun tsdt-drain (o oc)
  (mv-let (d verdict) (fn-tsd-drain-decision o oc *pt-cfg* "ob" "s")
    (list d verdict)))

; The same BP delivery through the configured owner's step: the gate's
; submit event, then the take.  It is the direct composition above.
(defun tsdt-bp-oc (o)
  (tsdt-run (fn-ocfg-make o *pt-cfg* nil nil)
            (list (list :bp-transit-submit *pt-cfg* "innA" *pt-idloop* *pt-noloop* "ob" "s")
                  (list :take))))
(assert-event (fn-ocfg-statep (fn-ocfg-make *tsdt-o* *pt-cfg* nil nil)))
(assert-event (equal (fn-ocfg-owner (tsdt-bp-oc *tsdt-o*)) *tsdt-b*))
(assert-event (fn-ocfg-statep (tsdt-bp-oc *tsdt-o*)))

; fn-tsd-bp-gate-is-the-drain-decision, REACHABLE positive: the antecedent ...
(assert-event (equal (fn-own-bp-transit-submit-result *tsdt-o* *pt-cfg* "innA" *pt-idloop*
                                                      *pt-noloop* "ob" "s")
                     :submitted))
; ... and every conjunct of the conclusion.
(assert-event (fn-own-transit-inflightp *tsdt-b*))
(assert-event (equal (fn-own-sub-id (fn-own-inflight *tsdt-b*)) *fn-own-control-id*))
(assert-event (equal (fn-own-sub-decision (fn-own-inflight *tsdt-b*))
                     (fn-peer-make-submission "innA" :takethis *pt-idloop* *pt-noloop*)))
(assert-event (equal (mv-nth 0 (tsdt-drain *tsdt-b* nil))
                     (fn-peer-decide-transfer-under
                      (fn-sn-node (fn-own-store *tsdt-o*)) *pt-cfg* "innA" *pt-idloop*
                      *pt-noloop* (fn-own-clock *tsdt-o*) "ob" "s"
                      (fn-own-config-header-limits (fn-own-config *tsdt-o*)))))
(assert-event (equal (fn-peer-decision-kind (mv-nth 0 (tsdt-drain *tsdt-b* nil))) :want))

; Hypothesis removal (REACHABLE): without :submitted, the keystone's only
; hypothesis.  The same delivery under limits one header octet short is
; refused by the gate; nothing is enqueued, and the take leaves no transit
; in flight, so the conclusion fails.  ((stringp peer) is not a hypothesis:
; fn-tsd-submitted-names-a-string-peer proves it from :submitted.)
(defconst *tsdt-o-short* (thlt-owner '(6 6 199)))
(assert-event (equal (fn-own-bp-transit-submit-result *tsdt-o-short* *pt-cfg* "innA"
                                                      *pt-idloop* *pt-noloop* "ob" "s")
                     :refused))
(assert-event (not (fn-own-transit-inflightp (tsdt-take *tsdt-o-short* "innA" *pt-noloop*))))
(must-fail-checked
 (defthm tsdt-gate-without-submitted
   (fn-own-transit-inflightp
    (fn-own-take-submission
     (fn-own-bp-transit-submit o cfg peer msgid octets id subject)))
   :hints (("Goal" :in-theory (disable fn-own-bp-transit-submit-result)))))

; MUTATION: the conclusion with the NNTP kind :ihave in place of :takethis.
; The record BP enqueues is TAKETHIS's, so the mutated conjunct fails at the
; reachable positive.
(assert-event (not (equal (fn-own-sub-decision (fn-own-inflight *tsdt-b*))
                          (fn-peer-make-submission "innA" :ihave *pt-idloop* *pt-noloop*))))

; -----------------------------------------------------------------------------
; fn-tsd-nntp-and-bp-transit-decide-alike.  The NNTP carrier, REACHABLE: a
; configured owner opens a peer connection for "innA", reads IHAVE and the
; dot-terminated article on it (the served read enqueues the transit
; submission), and takes it.

(defconst *tsdt-ihave* (append (fn-nntp-string-octets "IHAVE <loop@example.invalid>")
                               (list 13 10)))
(defun tsdt-nntp-offer (octets)
  (list (list :open-peer "innA" nil nil)
        (list :octets 0 *tsdt-ihave*)
        (list :octets 0 (append octets (list 46 13 10)))))
(defun tsdt-nntp-oc (o octets)
  (tsdt-run (fn-ocfg-make o *pt-cfg* nil nil)
            (append (tsdt-nntp-offer octets) (list (list :take)))))
(defconst *tsdt-ocn* (tsdt-nntp-oc *tsdt-o* *pt-noloop*))
(defconst *tsdt-n* (fn-ocfg-owner *tsdt-ocn*))
(assert-event (fn-ocfg-statep *tsdt-ocn*))
(assert-event (equal (fn-own-sub-id (fn-own-inflight *tsdt-n*)) 0))

; The hypotheses as one predicate, so each removal states which one fails.
(defun tsdt-alike-hyps (o n octets)
  (list (equal (fn-own-bp-transit-submit-result o *pt-cfg* "innA" *pt-idloop* octets "ob" "s")
               :submitted)
        (fn-own-transit-inflightp n)
        (equal (fn-own-sub-decision (fn-own-inflight n))
               (fn-peer-make-submission "innA" :ihave *pt-idloop* octets))
        (equal (fn-own-store n) (fn-own-store o))
        (equal (fn-own-clock n) (fn-own-clock o))
        (equal (fn-own-config-header-limits (fn-own-config n))
               (fn-own-config-header-limits (fn-own-config o)))))
(defun tsdt-alike-concl (o n)
  (equal (mv-nth 0 (tsdt-drain n nil))
         (mv-nth 0 (tsdt-drain (tsdt-take o "innA" *pt-noloop*) nil))))

; REACHABLE positive: the whole antecedent, and the conclusion (both :want).
(assert-event (equal (tsdt-alike-hyps *tsdt-o* *tsdt-n* *pt-noloop*) '(t t t t t t)))
(assert-event (tsdt-alike-concl *tsdt-o* *tsdt-n*))
(assert-event (equal (fn-peer-decision-kind (mv-nth 0 (tsdt-drain *tsdt-n* nil))) :want))

; Removal of :submitted (REACHABLE): both owners one header octet short.
; The gate refuses, so no BP transit is in flight (:not-transit), while the
; NNTP one is refused by the limit.
(defconst *tsdt-n-short* (fn-ocfg-owner (tsdt-nntp-oc *tsdt-o-short* *pt-noloop*)))
(assert-event (equal (tsdt-alike-hyps *tsdt-o-short* *tsdt-n-short* *pt-noloop*)
                     '(nil t t t t t)))
(assert-event (equal (mv-nth 0 (tsdt-drain *tsdt-n-short* nil))
                     (fn-peer-decision :refuse :header-octets-limit)))
(assert-event (not (tsdt-alike-concl *tsdt-o-short* *tsdt-n-short*)))

; Removal of the transit in flight (CORRUPTED): the in-flight record carries
; the same peer, Message-ID and octets under a kind no carrier produces, so
; it is no transit submission and the drain decides nothing.
(defconst *tsdt-n-kind*
  (update-nth 11 (fn-own-sub-make 0 0 nil
                                  (fn-peer-make-submission "innA" :post *pt-idloop*
                                                           *pt-noloop*)
                                  nil)
              *tsdt-n*))
(defun tsdt-alike-hyps-kind (o n octets kind)
  (list (equal (fn-own-bp-transit-submit-result o *pt-cfg* "innA" *pt-idloop* octets "ob" "s")
               :submitted)
        (fn-own-transit-inflightp n)
        (equal (fn-own-sub-decision (fn-own-inflight n))
               (fn-peer-make-submission "innA" kind *pt-idloop* octets))
        (equal (fn-own-store n) (fn-own-store o))
        (equal (fn-own-clock n) (fn-own-clock o))
        (equal (fn-own-config-header-limits (fn-own-config n))
               (fn-own-config-header-limits (fn-own-config o)))))
(assert-event (equal (tsdt-alike-hyps-kind *tsdt-o* *tsdt-n-kind* *pt-noloop* :post)
                     '(t nil t t t t)))
(assert-event (equal (tsdt-drain *tsdt-n-kind* nil) '(:not-transit :none)))
(assert-event (not (tsdt-alike-concl *tsdt-o* *tsdt-n-kind*)))

; Removal of the same submission (REACHABLE): the same peer offers the same
; Message-ID with a Path that already names this node.  The NNTP decision
; is the loop refusal.
(defconst *tsdt-n-loop* (fn-ocfg-owner (tsdt-nntp-oc *tsdt-o* *pt-loop*)))
(assert-event (equal (tsdt-alike-hyps *tsdt-o* *tsdt-n-loop* *pt-noloop*) '(t t nil t t t)))
(assert-event (equal (mv-nth 0 (tsdt-drain *tsdt-n-loop* nil)) (fn-peer-decision :refuse :loop)))
(assert-event (not (tsdt-alike-concl *tsdt-o* *tsdt-n-loop*)))

; Removal of the same store (REACHABLE): the offer is read, then a local
; post of the same Message-ID commits before the take (the stale offer of
; RFC 4644 section 2.4.2).  The drain finds it in history.
(defun tsdt-record (msgid)
  (fn-hrt-row-at
   (fn-record-make 0 0 0 msgid
                   (list 77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10
                         72 105 13 10)
                   '("fn.letters") "tsdt-pin" "tsdt-content" "tsdt-release" 2 841000000)
   0))
(defun tsdt-post-events (record)
  (list '(:begin 1)
        '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare record))
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))
        '(:complete)))
(defconst *tsdt-ocn-held*
  (tsdt-run (fn-ocfg-make *tsdt-o* *pt-cfg* nil nil)
            (append (tsdt-nntp-offer *pt-noloop*)
                    (tsdt-post-events (tsdt-record "<loop@example.invalid>"))
                    (list (list :take)))))
(defconst *tsdt-n-held* (fn-ocfg-owner *tsdt-ocn-held*))
(assert-event (fn-ocfg-statep *tsdt-ocn-held*))
(assert-event (equal (tsdt-alike-hyps *tsdt-o* *tsdt-n-held* *pt-noloop*) '(t t t nil t t)))
(assert-event (equal (mv-nth 0 (tsdt-drain *tsdt-n-held* nil)) (fn-peer-decision :have :history)))
(assert-event (not (tsdt-alike-concl *tsdt-o* *tsdt-n-held*)))

; Removal of the same clock (REACHABLE): an owner whose wall clock reads
; more than the margin before the article's Date.
(defconst *tsdt-o-early*
  (fn-own-configure
   (fn-own-observe (fn-own-start (fn-sn-initial '("fn.letters" "fn.test") 10) 4)
                   (fn-clock-observation 1000000 800000000000 500 t))
   (thlt-config '(6 6 200))))
(defconst *tsdt-n-early* (fn-ocfg-owner (tsdt-nntp-oc *tsdt-o-early* *pt-noloop*)))
(assert-event (equal (tsdt-alike-hyps *tsdt-o* *tsdt-n-early* *pt-noloop*) '(t t t t nil t)))
(assert-event (equal (mv-nth 0 (tsdt-drain *tsdt-n-early* nil))
                     (fn-peer-decision :refuse :date-future)))
(assert-event (not (tsdt-alike-concl *tsdt-o* *tsdt-n-early*)))

; Removal of the same limits (REACHABLE): the NNTP owner one header octet
; short, the BP owner at the limits.
(assert-event (equal (tsdt-alike-hyps *tsdt-o* *tsdt-n-short* *pt-noloop*) '(t t t t t nil)))
(assert-event (not (tsdt-alike-concl *tsdt-o* *tsdt-n-short*)))

; MUTATION: the NNTP copy's octets lose their last octet; the transfer
; decision reads them, so it no longer equals the BP one.
(defconst *tsdt-n-mutated*
  (update-nth 11 (fn-own-sub-make 0 0 nil
                                  (fn-peer-make-submission "innA" :ihave *pt-idloop*
                                                           (butlast *pt-noloop* 1))
                                  nil)
              *tsdt-n*))
(assert-event (fn-own-transit-inflightp *tsdt-n-mutated*))
(assert-event (not (tsdt-alike-concl *tsdt-o* *tsdt-n-mutated*)))

; -----------------------------------------------------------------------------
; fn-tsd-open-connection-pin-is-not-the-control-pin.

; REACHABLE positive: the configured owner with the NNTP transit in flight;
; its connection is open and pinned to the live configuration, and the
; control id has no pin.
(assert-event (fn-ocfg-statep *tsdt-ocn*))
(assert-event (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *tsdt-ocn*))))
(assert-event (not (equal (fn-ocfg-conn-config *tsdt-ocn* 0)
                          (fn-ocfg-conn-config *tsdt-ocn* *fn-own-control-id*))))
(assert-event (equal (fn-ocfg-conn-config *tsdt-ocn* 0) *pt-cfg*))
(assert-event (equal (fn-ocfg-conn-config *tsdt-ocn* *fn-own-control-id*) nil))

; Removal of the open connection (REACHABLE): the peer disconnects.  The
; state is still a configured owner, connection 0 is gone and both lookups
; are nil.  The close also drops the connection's in-flight submission:
; no NNTP transit is left to drain, so the drain never meets an unpinned
; NNTP transit.
(defconst *tsdt-ocn-closed* (tsdt-run *tsdt-ocn* (list (list :close 0))))
(assert-event (fn-ocfg-statep *tsdt-ocn-closed*))
(assert-event (not (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *tsdt-ocn-closed*)))))
(assert-event (equal (fn-ocfg-conn-config *tsdt-ocn-closed* 0)
                     (fn-ocfg-conn-config *tsdt-ocn-closed* *fn-own-control-id*)))
(assert-event (not (fn-own-transit-inflightp (fn-ocfg-owner *tsdt-ocn-closed*))))

; Removal of fn-ocfg-statep (CORRUPTED): the same owner with its pin table
; emptied while connection 0 is open.
(defconst *tsdt-ocn-unpinned* (fn-ocfg-make *tsdt-n* *pt-cfg* nil nil))
(assert-event (not (fn-ocfg-statep *tsdt-ocn-unpinned*)))
(assert-event (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *tsdt-ocn-unpinned*))))
(assert-event (equal (fn-ocfg-conn-config *tsdt-ocn-unpinned* 0)
                     (fn-ocfg-conn-config *tsdt-ocn-unpinned* *fn-own-control-id*)))

; MUTATION: the conclusion with the live configuration in place of the
; control id's pin.  An open connection's pin IS the live configuration it
; was opened under, so the mutated inequality fails.
(assert-event (equal (fn-ocfg-conn-config *tsdt-ocn* 0) (fn-ocfg-config *tsdt-ocn*)))

; -----------------------------------------------------------------------------
; fn-tsd-bp-transit-authority-is-ungoverned.  The live configuration governs
; fn.letters (the article's group) with an explicit authority; the owner
; configuration state is a real one (no connection open, nothing pinned).

(defconst *tsdt-hex* "5555555555555555555555555555555555555555555555555555555555555555")
(defconst *tsdt-auth-cfg*
  (fn-config-replay
   0 510
   (list (fn-cfg-record-make 0 0 1
                             (list (fn-cfg-create-group "fn.letters" "post-policy")
                                   (fn-cfg-set-capacity 65536))
                             *fn-cfg-default-stamp*)
         (fn-cfg-record-make 1 1 2
                             (list (fn-cfg-set-group-authority "fn.letters" *tsdt-hex*))
                             *fn-cfg-default-stamp*))))
(assert-event (fn-cfgp *tsdt-auth-cfg*))
(assert-event (fn-pta-group-authority (fn-cfg-value *tsdt-auth-cfg*)
                                      (fn-cfg-generation *tsdt-auth-cfg*) "fn.letters"))
(defconst *tsdt-oc*
  (fn-ocfg-make (fn-own-start (fn-sn-initial '("fn.letters" "fn.test") 10) 3)
                *tsdt-auth-cfg* nil nil))

; The host's call for the BP submission in flight (fn-owner-transit-decide).
(defun tsdt-host-verdict (oc)
  (let ((store (fn-own-store *tsdt-b*))
        (acfg (fn-ocfg-conn-config oc *fn-own-control-id*)))
    (mv-let (d verdict)
      (fn-pta-decide (fn-sn-index store) (fn-sn-keyring store)
                     (fn-cfg-value acfg) (fn-cfg-generation acfg)
                     (fn-sn-node store) *pt-cfg* "innA" *pt-idloop* *pt-noloop*
                     (fn-own-clock *tsdt-b*) "ob" "s"
                     (fn-own-config-header-limits (fn-own-config *tsdt-b*)))
      (declare (ignore d))
      verdict)))
; It is the drain's decision for that submission.
(assert-event (equal (tsdt-host-verdict *tsdt-oc*) (mv-nth 1 (tsdt-drain *tsdt-b* *tsdt-oc*))))

; REACHABLE positive: the antecedent, and the verdict is :ungoverned on a
; :want although the live configuration governs the group.
(assert-event (fn-ocfg-statep *tsdt-oc*))
(assert-event (equal (fn-peer-decision-kind (mv-nth 0 (tsdt-drain *tsdt-b* *tsdt-oc*))) :want))
(assert-event (member-equal (tsdt-host-verdict *tsdt-oc*) '(:ungoverned :none)))
(assert-event (equal (tsdt-host-verdict *tsdt-oc*) :ungoverned))

; Hypothesis removal (CORRUPTED owner configuration): a pin for the control
; id, which no connection owns.  fn-ocfg-statep (the only hypothesis) fails,
; and the governed group gets a verdict that is neither :ungoverned nor
; :none.  This is what the BP carrier would see were its authority read
; under the live configuration (the queued host fix).
(defconst *tsdt-oc-pinned*
  (fn-ocfg-make (fn-own-start (fn-sn-initial '("fn.letters" "fn.test") 10) 3)
                *tsdt-auth-cfg* (list (cons :control *tsdt-auth-cfg*)) nil))
(assert-event (not (fn-ocfg-statep *tsdt-oc-pinned*)))
(assert-event (not (member-equal (tsdt-host-verdict *tsdt-oc-pinned*)
                                 '(:ungoverned :none))))
(must-fail-checked
 (defthm tsdt-authority-without-ocfg-statep
   (member-equal
    (mv-nth 1 (fn-pta-decide index keyring
                             (fn-cfg-value (fn-ocfg-conn-config oc *fn-own-control-id*))
                             (fn-cfg-generation (fn-ocfg-conn-config oc *fn-own-control-id*))
                             node cfg peer msgid octets clock id subject limits))
    '(:ungoverned :none))
   :hints (("Goal" :in-theory (disable fn-pta-decide)))))

; MUTATION: the subject reading the live configuration in place of the
; control id's pin (the queued host fix).  On the reachable positive the
; governed group then gets a verdict that is neither :ungoverned nor :none.
(defun tsdt-live-verdict (oc)
  (let ((store (fn-own-store *tsdt-b*))
        (acfg (fn-ocfg-config oc)))
    (mv-let (d verdict)
      (fn-pta-decide (fn-sn-index store) (fn-sn-keyring store)
                     (fn-cfg-value acfg) (fn-cfg-generation acfg)
                     (fn-sn-node store) *pt-cfg* "innA" *pt-idloop* *pt-noloop*
                     (fn-own-clock *tsdt-b*) "ob" "s"
                     (fn-own-config-header-limits (fn-own-config *tsdt-b*)))
      (declare (ignore d))
      verdict)))
(assert-event (not (member-equal (tsdt-live-verdict *tsdt-oc*) '(:ungoverned :none))))
