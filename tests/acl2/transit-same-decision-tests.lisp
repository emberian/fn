; Teeth for books/transit-same-decision (PKT-202, K6): per keystone a
; reachable witness asserting the whole antecedent and conclusion, a
; single-hypothesis removal that checks every retained hypothesis, the
; omitted one failing and the conclusion failing, and a labelled mutation.
; Fixtures: tests/acl2/transit-header-limits-tests (an owner whose limits
; admit *pt-noloop* from the configured peer "innA"; *pt-cfg*).
(in-package "ACL2")
(include-book "../../books/transit-same-decision")
(include-book "../../books/config-records")
(include-book "transit-header-limits-tests")
(include-book "must-fail-checked")

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

; fn-tsd-bp-gate-is-the-drain-decision, REACHABLE positive: the antecedent ...
(assert-event (equal (fn-own-bp-transit-submit-result *tsdt-o* *pt-cfg* "innA" *pt-idloop*
                                                      *pt-noloop* "ob" "s")
                     :submitted))
(assert-event (stringp "innA"))
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

; Hypothesis removal (REACHABLE): without :submitted.  The same delivery
; under limits one header octet short is refused by the gate; the retained
; hypothesis holds, nothing is enqueued, and the take leaves no transit in
; flight, so the conclusion fails.
(defconst *tsdt-o-short* (thlt-owner '(6 6 199)))
(assert-event (stringp "innA"))
(assert-event (equal (fn-own-bp-transit-submit-result *tsdt-o-short* *pt-cfg* "innA"
                                                      *pt-idloop* *pt-noloop* "ob" "s")
                     :refused))
(assert-event (not (fn-own-transit-inflightp (tsdt-take *tsdt-o-short* "innA" *pt-noloop*))))
(must-fail-checked
 (defthm tsdt-gate-without-submitted
   (implies (stringp peer)
            (fn-own-transit-inflightp
             (fn-own-take-submission
              (fn-own-bp-transit-submit o cfg peer msgid octets id subject))))
   :hints (("Goal" :in-theory (disable fn-own-bp-transit-submit-result)))))

; -----------------------------------------------------------------------------
; fn-tsd-nntp-and-bp-transit-decide-alike.  An NNTP IHAVE of the same article
; from the same peer, in flight on connection 0 of an owner with the BP
; owner's store, clock and limits (CONSTRUCTED: the in-flight slot written
; directly, as fn-own-take-submission writes it).

(defun tsdt-nntp (peer octets)
  (update-nth 11 (fn-own-sub-make 0 0 nil
                                  (fn-peer-make-submission peer :ihave *pt-idloop* octets)
                                  nil)
              *tsdt-b*))
(defconst *tsdt-n* (tsdt-nntp "innA" *pt-noloop*))

; REACHABLE positive (the BP side reachable, the NNTP side constructed):
; the whole antecedent ...
(assert-event (equal (fn-own-bp-transit-submit-result *tsdt-o* *pt-cfg* "innA" *pt-idloop*
                                                      *pt-noloop* "ob" "s")
                     :submitted))
(assert-event (fn-own-transit-inflightp *tsdt-n*))
(assert-event (equal (fn-own-sub-decision (fn-own-inflight *tsdt-n*))
                     (fn-peer-make-submission "innA" :ihave *pt-idloop* *pt-noloop*)))
(assert-event (equal (fn-own-store *tsdt-n*) (fn-own-store *tsdt-o*)))
(assert-event (equal (fn-own-clock *tsdt-n*) (fn-own-clock *tsdt-o*)))
(assert-event (equal (fn-own-config-header-limits (fn-own-config *tsdt-n*))
                     (fn-own-config-header-limits (fn-own-config *tsdt-o*))))
; ... both conclusions (with no pins, the pinned configurations agree).
(assert-event (equal (mv-nth 0 (tsdt-drain *tsdt-n* nil)) (mv-nth 0 (tsdt-drain *tsdt-b* nil))))
(assert-event (equal (fn-ocfg-conn-config nil 0) (fn-ocfg-conn-config nil *fn-own-control-id*)))
(assert-event (equal (tsdt-drain *tsdt-n* nil) (tsdt-drain *tsdt-b* nil)))
(assert-event (equal (fn-peer-decision-kind (mv-nth 0 (tsdt-drain *tsdt-n* nil))) :want))

; Hypothesis removal: without the same submission (the principal differs:
; peer "innB" is not configured).  Every retained hypothesis holds, the
; omitted one fails, and the byte decisions differ (:refuse against :want).
(defconst *tsdt-n-other* (tsdt-nntp "innB" *pt-noloop*))
(assert-event (fn-own-transit-inflightp *tsdt-n-other*))
(assert-event (equal (fn-own-store *tsdt-n-other*) (fn-own-store *tsdt-o*)))
(assert-event (equal (fn-own-clock *tsdt-n-other*) (fn-own-clock *tsdt-o*)))
(assert-event (equal (fn-own-config-header-limits (fn-own-config *tsdt-n-other*))
                     (fn-own-config-header-limits (fn-own-config *tsdt-o*))))
(assert-event (not (equal (fn-own-sub-decision (fn-own-inflight *tsdt-n-other*))
                          (fn-peer-make-submission "innA" :ihave *pt-idloop* *pt-noloop*))))
(assert-event (equal (mv-nth 0 (tsdt-drain *tsdt-n-other* nil))
                     (fn-peer-decision :refuse :not-a-peer)))
(assert-event (not (equal (mv-nth 0 (tsdt-drain *tsdt-n-other* nil))
                          (mv-nth 0 (tsdt-drain *tsdt-b* nil)))))

; MUTATION: the NNTP copy's octets lose their last octet; the transfer
; decision reads them, so it no longer equals the BP one.
(defconst *tsdt-n-mutated* (tsdt-nntp "innA" (butlast *pt-noloop* 1)))
(assert-event (fn-own-transit-inflightp *tsdt-n-mutated*))
(assert-event (not (equal (mv-nth 0 (tsdt-drain *tsdt-n-mutated* nil))
                          (mv-nth 0 (tsdt-drain *tsdt-b* nil)))))

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
