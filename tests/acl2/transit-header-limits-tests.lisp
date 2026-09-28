; Teeth for books/transit-header-limits (PRF-230, PKT-660): per keystone a
; reachable witness with the whole antecedent and conclusion, each limit
; refused by its own name, and a must-fail per hypothesis over a concrete
; counterexample.  Fixtures: tests/acl2/peer-inbound-tests (*pt-cfg*, whose
; peer innA feeds fn.*, and *pt-node0*).
(in-package "ACL2")
(include-book "../../books/transit-header-limits")
(include-book "../../books/codec-attach")
(include-book "peer-inbound-tests")
(include-book "must-fail-checked")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-ap-at-most-is-length-bound))))

(defconst *thlt-stored* (fn-peer-relayed-octets *pt-cfg* "innA" *pt-noloop*))
; The census: the stored article (Path grown by this node's identity) has 6
; fields, 6 lines and 200 header octets; the received one 185.
(assert-event (equal (fn-article-header-census *thlt-stored*) '(6 6 200)))
(assert-event (equal (fn-article-header-census *pt-noloop*) '(6 6 185)))
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" *pt-idloop*
                                              *pt-noloop* nil "ob" "s")
                     (fn-peer-decision :want nil)))

(defun thlt-under (limits)
  (fn-peer-decide-transfer-under *pt-node0* *pt-cfg* "innA" *pt-idloop*
                                 *pt-noloop* nil "ob" "s" limits))

; -----------------------------------------------------------------------------
; fn-peer-decide-transfer-under-admits-exactly-the-limits

; Admitted at the limits exactly: the decision is the transfer's, and the
; parse under the limits is the reading parse.
(assert-event (equal (thlt-under '(6 6 200)) (fn-peer-decision :want nil)))
(assert-event (fn-article-result-okp (fn-article-parse-under *thlt-stored* '(6 6 200))))
(assert-event (equal (fn-article-parse-under *thlt-stored* '(6 6 200))
                     (fn-article-parse *thlt-stored*)))
; One past each limit: refused by that limit's name.
(assert-event (equal (thlt-under '(5 6 200)) (fn-peer-decision :refuse :header-fields-limit)))
(assert-event (equal (thlt-under '(6 5 200)) (fn-peer-decision :refuse :header-lines-limit)))
(assert-event (equal (thlt-under '(6 6 199)) (fn-peer-decision :refuse :header-octets-limit)))
; The census is of the stored octets: 190 header octets admit what was
; received (185) and refuse what would be stored (200).
(assert-event (fn-article-result-okp (fn-article-parse-under *pt-noloop* '(6 6 190))))
(assert-event (equal (thlt-under '(6 6 190)) (fn-peer-decision :refuse :header-octets-limit)))
(assert-event (not (fn-article-result-okp (fn-article-parse-under *thlt-stored* '(6 6 199)))))
(assert-event (fn-article-limit-reasonp (cadr (fn-article-parse-under *thlt-stored* '(6 6 199)))))
; The reply line names the limit (437 / 439 carry the reason text).
(assert-event (equal (fn-peer-reason-text :header-fields-limit)
                     "the header has more fields than the profile's max-header-fields"))
(assert-event (fn-peer-decisionp (thlt-under '(5 6 200))))

; Without the want-or-defer hypothesis: a path loop is refused :loop, past
; every limit, and :loop is not a limit's name.
(assert-event (equal (fn-peer-decide-transfer-under *pt-node0* *pt-cfg* "innA" *pt-idloop*
                                                    *pt-loop* nil "ob" "s" '(0 0 0))
                     (fn-peer-decision :refuse :loop)))
(assert-event (not (fn-article-limit-reasonp :loop)))
(must-fail-checked
 (defthm thlt-without-want-or-defer
   (let* ((u (fn-peer-decide-transfer-under node cfg peer msgid octets clock id
                                            subject limits))
          (p (fn-article-parse-under (fn-peer-relayed-octets cfg peer octets)
                                     limits)))
     (implies (not (fn-article-result-okp p))
              (fn-article-limit-reasonp (fn-peer-decision-reason u))))
   :hints (("Goal"
            :use ((:instance fn-peer-transfer-want-or-defer-parses-the-stored-article)
                  (:instance fn-article-census-refusal-is-the-parse
                             (octets (fn-peer-relayed-octets cfg peer octets))))
            :in-theory (union-theories
                        '(fn-peer-decide-transfer-under
                          fn-peer-header-limit-refusal
                          fn-peer-decision-kind-of-fn-peer-decision
                          fn-peer-decision-reason-of-fn-peer-decision
                          fn-article-census-refusal-is-a-limit-reason
                          member-equal)
                        (theory 'minimal-theory))))))

; -----------------------------------------------------------------------------
; fn-peer-decide-transfer-under-wants-only-what-transfer-wants

; Witness: above.  Without the want: the refusal past the fields limit is
; not the transfer's want.
(assert-event (not (equal (thlt-under '(5 6 200))
                          (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" *pt-idloop*
                                                   *pt-noloop* nil "ob" "s"))))
(must-fail-checked
 (defthm thlt-without-want
   (equal (fn-peer-decide-transfer-under node cfg peer msgid octets clock id
                                         subject limits)
          (fn-peer-decide-transfer node cfg peer msgid octets clock id subject))
   :hints (("Goal"
            :use ((:instance fn-peer-decide-transfer-under-admits-exactly-the-limits))
            :in-theory (union-theories
                        '(fn-peer-decide-transfer-under
                          fn-peer-decision-kind-of-fn-peer-decision
                          member-equal)
                        (theory 'minimal-theory))))))

; -----------------------------------------------------------------------------
; The owner's BP transit and control deliveries.  The owner's limits are its
; injection configuration's, built as the host builds it from a profile.

(defun thlt-config (limits)
  (fn-inj-make-config-full t (pt-o "fn.example.invalid") (list (pt-o "fn.letters"))
                           (fn-inj-post-bound 32768 limits) nil nil))
(defconst *thlt-owner0*
  (fn-own-observe (fn-own-start (fn-sn-initial '("fn.letters" "fn.test") 10) 4)
                  *pt-obs*))
(defun thlt-owner (limits) (fn-own-configure *thlt-owner0* (thlt-config limits)))
(assert-event (equal (fn-own-config-header-limits (fn-own-config (thlt-owner '(6 6 200))))
                     '(6 6 200)))
; An owner with no configuration installed reads the profile defaults.
(assert-event (equal (fn-own-config-header-limits nil) *fn-article-default-limits*))

(defun thlt-bp (limits)
  (fn-own-bp-transit-submit-result (thlt-owner limits) *pt-cfg* "innA" *pt-idloop*
                                   *pt-noloop* "ob" "s"))
(assert-event (equal (thlt-bp '(6 6 200)) :submitted))
(assert-event (equal (thlt-bp '(5 6 200)) :refused))
(assert-event (equal (thlt-bp '(6 5 200)) :refused))
(assert-event (equal (thlt-bp '(6 6 199)) :refused))
(assert-event (equal (fn-peer-decision-reason
                      (fn-peer-decide-transfer-under
                       (fn-sn-node (fn-own-store (thlt-owner '(6 6 199)))) *pt-cfg* "innA"
                       *pt-idloop* *pt-noloop* (fn-own-clock (thlt-owner '(6 6 199)))
                       "ob" "s" '(6 6 199)))
                     :header-octets-limit))
; fn-own-bp-transit-submits-only-within-the-limits: without :submitted, the
; refused delivery's parse under the limits fails.
(must-fail-checked
 (defthm thlt-bp-without-submitted
   (fn-article-result-okp
    (fn-article-parse-under (fn-peer-relayed-octets cfg peer octets)
                            (fn-own-config-header-limits (fn-own-config o))))
   :hints (("Goal" :in-theory (disable fn-article-parse-under
                                       fn-peer-relayed-octets
                                       fn-own-config-header-limits)))))
; fn-own-bp-transit-refuses-past-the-limits: without the failed parse, the
; delivery at the limits is submitted.
(must-fail-checked
 (defthm thlt-bp-without-past-the-limits
   (equal (fn-own-bp-transit-submit-result o cfg peer msgid octets id subject)
          :refused)
   :hints (("Goal" :in-theory (disable fn-own-bp-transit-submit-result)))))

(defun thlt-ctl (limits octets)
  (fn-own-control-decision (thlt-config limits) *pt-id1* (list (pt-o "fn.letters"))
                           octets))
(assert-event (fn-thl-control-gatep (thlt-config '(6 6 1000)) *pt-id1*
                                    (list (pt-o "fn.letters")) *pt-a1*))
(assert-event (equal (fn-article-header-census *pt-a1*) '(6 6 186)))
(assert-event (fn-inj-injectedp (thlt-ctl '(6 6 186) *pt-a1*)))
(assert-event (equal (fn-inj-decision-reason (thlt-ctl '(5 6 186) *pt-a1*)) :header-fields-limit))
(assert-event (equal (fn-inj-decision-reason (thlt-ctl '(6 5 186) *pt-a1*)) :header-lines-limit))
(assert-event (equal (fn-inj-decision-reason (thlt-ctl '(6 6 185) *pt-a1*)) :header-octets-limit))
(assert-event (not (fn-inj-injectedp (thlt-ctl '(5 6 186) *pt-a1*))))
; Without the gate: an owner that does not allow posting refuses
; :control-invalid, which is not a limit's name.
(assert-event (equal (fn-inj-decision-reason
                      (fn-own-control-decision
                       (fn-inj-make-config-full nil (pt-o "fn.example.invalid")
                                                (list (pt-o "fn.letters"))
                                                (fn-inj-post-bound 32768 '(5 6 186)) nil nil)
                       *pt-id1* (list (pt-o "fn.letters")) *pt-a1*))
                     :control-invalid))
(must-fail-checked
 (defthm thlt-ctl-without-gate
   (implies (and (fn-article-result-okp (fn-article-parse octets))
                 (not (fn-article-result-okp
                       (fn-article-parse-under octets (fn-own-config-header-limits cfg)))))
            (fn-article-limit-reasonp
             (fn-inj-decision-reason (fn-own-control-decision cfg msgid groups octets))))
   :hints (("Goal"
            :use ((:instance fn-article-census-refusal-is-the-parse
                             (limits (fn-own-config-header-limits cfg))))
            :in-theory (e/d (fn-own-control-decision fn-inj-refuse fn-inj-injectedp)
                            (fn-article-parse fn-article-parse-under
                             fn-article-result-okp fn-article-header-census
                             fn-article-census-refusal fn-own-config-header-limits
                             fn-af-message-idp fn-inj-group-namesp fn-octet-listp))))))
; Without the reading parse: octets that are no article, within the census,
; are injected by the control gate (the CLI hands an authored article), and
; their parse under the limits fails.
(defconst *thlt-garbage* (pt-o "garbage"))
(assert-event (not (fn-article-result-okp (fn-article-parse *thlt-garbage*))))
(assert-event (fn-inj-injectedp (thlt-ctl '(6 6 186) *thlt-garbage*)))
(assert-event (not (fn-article-result-okp (fn-article-parse-under *thlt-garbage* '(6 6 186)))))
(must-fail-checked
 (defthm thlt-ctl-inject-without-reading-parse
   (implies (fn-inj-injectedp (fn-own-control-decision cfg msgid groups octets))
            (fn-article-result-okp
             (fn-article-parse-under octets (fn-own-config-header-limits cfg))))
   :hints (("Goal"
            :use ((:instance fn-article-census-refusal-is-the-parse
                             (limits (fn-own-config-header-limits cfg))))
            :in-theory (e/d (fn-own-control-decision fn-inj-refuse fn-inj-injectedp)
                            (fn-article-parse fn-article-parse-under
                             fn-article-result-okp fn-article-header-census
                             fn-article-census-refusal fn-own-config-header-limits
                             fn-af-message-idp fn-inj-group-namesp fn-octet-listp))))))
; Without the injection: the refusal past the fields limit.
(assert-event (not (fn-article-result-okp (fn-article-parse-under *pt-a1* '(5 6 186)))))
(must-fail-checked
 (defthm thlt-ctl-without-injected
   (implies (fn-article-result-okp (fn-article-parse octets))
            (fn-article-result-okp
             (fn-article-parse-under octets (fn-own-config-header-limits cfg))))
   :hints (("Goal" :in-theory (disable fn-article-parse fn-article-parse-under
                                       fn-own-config-header-limits)))))
; Without the failed parse under the limits: injected.
(must-fail-checked
 (defthm thlt-ctl-refuse-without-past-the-limits
   (implies (and (fn-thl-control-gatep cfg msgid groups octets)
                 (fn-article-result-okp (fn-article-parse octets)))
            (not (fn-inj-injectedp (fn-own-control-decision cfg msgid groups octets))))
   :hints (("Goal" :in-theory (disable fn-own-control-decision fn-article-parse)))))
