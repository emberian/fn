; D23, the fourth question: receipt-authorizes-release (review of
; 2026-09-24, "carriage is not authorship, and authorship is not release
; authority").  A receipt releases a forwarding obligation only when its
; issuer is authorized for release at the delivering neighbour (its own
; enrolled EID, or on its `bp-boundary-releases-for' list) AND it names the
; exact held obligation.  The host's receipt path publishes only the record
; `fn-bpah-receipt-release-record' returns (host/native/bp-node.lisp,
; `fnn-bpnode-receipt-result', through `fn-owner-bp-receipt-release-record'
; in host/bp-native-app-host.lisp).
(in-package "ACL2")
(include-book "bp-app-handoff")
(include-book "bp-workflow-constructors")

; The held obligation a receipt names: the work with the receipt's work id
; in the recovered workflow image, or nil.
(defun fn-bpah-receipt-obligation (wf receipt)
  (declare (xargs :guard t))
  (fn-bp-find-work (fn-bpa-receipt-work-id receipt) (fn-bp-state-works wf)))

; The receipt names the exact held obligation: an outstanding work whose id,
; content subject, counterpart peer, policy, incarnation, authority context
; and terms are the receipt's, under the workflow's configured receipt
; authority.  This is the workflow's own `fn-bp-authorized-receiptp', asked
; before anything is published.  The requester is this node: the receipt's
; carrier is addressed to it (`fn-bpah-local-pendingp') and the work is in
; its own journal.
(defun fn-bpah-receipt-names-obligationp (wf receipt work)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bp-statep wf)
       (fn-bpa-receiptp receipt)
       (fn-bp-work-outstandingp work)
       (fn-bp-authorized-receiptp (fn-bp-state-config wf) work
                                  (fn-bprl-receipt-from-adu receipt))))

; D23 question 4: receipt-authorizes-release(issuer, work, subject, terms,
; evidence).  CARRIER and GENERATION are the delivering neighbour's ingress
; stamp, ISSUER a release-issuer EID, RECEIPT the decoded receipt ADU (the
; evidence), WORK the held obligation.  A carried-list entry is not an
; input.
(defun fn-bpah-receipt-authorizes-releasep
    (cfg carrier generation issuer wf receipt work)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bpah-release-issuer-authorizedp cfg carrier generation issuer)
       (equal (fn-bpaj-tagged-value issuer) (fn-bpa-receipt-issuer receipt))
       (fn-bpah-receipt-names-obligationp wf receipt work)))

(defun fn-bpah-view-release-authorizedp (view cfg wf)
  (declare (xargs :guard t :verify-guards nil))
  (let ((receipt (fn-bpah-view-receipt view)))
    (and (fn-bpah-receipt-trustedp view cfg)
         (fn-bpah-receipt-authorizes-releasep
          cfg (fn-bpah-view-carrier view) (fn-bpah-view-generation view)
          (fn-bpaj-issuer-eid (fn-bpn-nth 6 view)) wf receipt
          (fn-bpah-receipt-obligation wf receipt)))))

; THE HOST-CALLED FUNCTION.  The workflow receipt-intent record the host
; publishes for a delivered receipt, authorized by the release question over
; the live configuration and the recovered workflow image; nil publishes
; nothing and releases nothing.
(defun fn-bpah-receipt-release-record (view cfg wf)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bprl-receipt-auto-record
   wf (fn-bpn-nth 3 view)
   (if (fn-bpah-view-release-authorizedp view cfg wf) t nil)))

; The verdict the kind-7 delivery row keeps (`fn-bpah-release-detail').
(defun fn-bpah-receipt-release-verdict (view cfg wf)
  (declare (xargs :guard t :verify-guards nil))
  (let ((v (fn-bpah-release-issuer-verdict view cfg)))
    (cond ((not (member-equal v '(:self-issued :listed-issuer))) v)
          ((not (fn-bpah-view-release-authorizedp view cfg wf))
           :obligation-mismatch)
          ((not (fn-bpah-receipt-release-record view cfg wf))
           :workflow-refused)
          (t v))))

(local (defthm fn-bpah-auto-record-unauthorized-is-nil
  (equal (fn-bprl-receipt-auto-record s octets nil) nil)
  :hints (("Goal" :in-theory (enable fn-bprl-receipt-auto-record
                                     fn-bprl-receipt-intent-record)))))

(local (defthm fn-bpah-view-release-needs-trust
  (implies (not (fn-bpah-receipt-trustedp view cfg))
           (not (fn-bpah-view-release-authorizedp view cfg wf)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-view-release-authorizedp) (theory 'minimal-theory))))))

(local (defthm fn-bpah-release-record-needs-trust
  (implies (not (fn-bpah-receipt-trustedp view cfg))
           (equal (fn-bpah-receipt-release-record view cfg wf) nil))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-receipt-release-record
                               fn-bpah-auto-record-unauthorized-is-nil
                               fn-bpah-view-release-needs-trust) (theory 'minimal-theory))))))

; KEYSTONE 1.  A receipt whose issuer is not authorized for release at the
; delivering neighbour is refused by the host's gate and releases nothing:
; no record, so the workflow image and the pin are unchanged.
(defthm fn-bpah-unauthorized-issuer-releases-nothing
  (implies (not (fn-bpah-release-issuer-authorizedp
                 cfg (fn-bpah-view-carrier view)
                 (fn-bpah-view-generation view)
                 (fn-bpaj-issuer-eid (fn-bpn-nth 6 view))))
           (and (not (fn-bpah-receipt-trustedp view cfg))
                (equal (fn-bpah-receipt-release-record view cfg wf) nil)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-unauthorized-issuer-never-authorizes-receipt
                               fn-bpah-release-record-needs-trust) (theory 'minimal-theory)))))

(local (defthm fn-bpah-no-row-no-release-authority
  (implies (and (not (fn-bpaj-boundary-rowp
                      (fn-cfg-peers (fn-cfg-value cfg))
                      (fn-record-octets-string carrier) "transport-bp"
                      issuer 0))
                (not (fn-bpaj-boundary-rowp
                      (fn-cfg-peers (fn-cfg-value cfg))
                      (fn-record-octets-string carrier)
                      "bp-boundary-releases-for" issuer 0)))
           (not (fn-bpah-release-issuer-authorizedp
                 cfg carrier generation (fn-bpaj-issuer-eid issuer))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-release-issuer-authorizedp
                               fn-bpaj-issuer-eid fn-bpaj-tagged-value
                               car-cons cdr-cons) (theory 'minimal-theory))
           :use ((:instance fn-bpaj-current-peer-needs-own-transport-row
                            (principal carrier) (eid issuer))
                 (:instance fn-bpaj-release-listed-needs-a-release-row
                            (principal carrier)))))))

; KEYSTONE 1, over the configuration rows (the lab's negative case).  The
; delivering neighbour's boundary has neither its own transport-bp row nor
; a releases-for row for the receipt's issuer.  Its carried list is not a
; hypothesis: carrying the issuer's EID releases nothing.
(defthm fn-bpah-carrier-without-release-row-releases-nothing
  (let ((rows (fn-cfg-peers (fn-cfg-value cfg)))
        (name (fn-record-octets-string (fn-bpah-view-carrier view)))
        (issuer (fn-bpn-nth 6 view)))
    (implies (and (not (fn-bpaj-boundary-rowp rows name "transport-bp"
                                               issuer 0))
                  (not (fn-bpaj-boundary-rowp rows name
                                               "bp-boundary-releases-for"
                                               issuer 0)))
             (and (not (fn-bpah-receipt-trustedp view cfg))
                  (equal (fn-bpah-receipt-release-record view cfg wf) nil))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-unauthorized-issuer-releases-nothing) (theory 'minimal-theory))
           :use ((:instance fn-bpah-no-row-no-release-authority
                            (carrier (fn-bpah-view-carrier view))
                            (generation (fn-bpah-view-generation view))
                            (issuer (fn-bpn-nth 6 view)))))))

(local (defthm fn-bpah-release-record-needs-authorization
  (implies (fn-bpah-receipt-release-record view cfg wf)
           (fn-bpah-view-release-authorizedp view cfg wf))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-receipt-release-record
                               fn-bpah-auto-record-unauthorized-is-nil) (theory 'minimal-theory))))))

(local (defthm fn-bpah-release-record-is-the-authorized-intent
  (implies (fn-bpah-receipt-release-record view cfg wf)
           (equal (fn-bpah-receipt-release-record view cfg wf)
                  (fn-bprl-receipt-intent-record
                   wf (fn-bpn-nth 3 view)
                   (+ 1 (fn-bprl-max-used-txid (fn-bp-state-used-txs wf) 0))
                   0 t)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-receipt-release-record
                               fn-bprl-receipt-auto-record
                               fn-bpah-auto-record-unauthorized-is-nil) (theory 'minimal-theory))
           :use ((:instance fn-bprl-receipt-intent-record-preflights
                            (s wf) (octets (fn-bpn-nth 3 view))
                            (txid (+ 1 (fn-bprl-max-used-txid
                                        (fn-bp-state-used-txs wf) 0)))
                            (generation 0)
                            (authorizedp (fn-bpah-view-release-authorizedp
                                          view cfg wf))))))))

(local (defthm fn-bpah-intent-record-work-id
  (implies (fn-bprl-receipt-intent-record s octets txid generation t)
           (equal (fn-bp-journal-nth
                   4 (fn-bprl-receipt-intent-record s octets txid generation t))
                  (fn-bp-receipt-work-id
                   (fn-bprl-receipt-from-adu
                    (fn-bpa-result-message (fn-bpa-decode-exact octets))))))
  :hints (("Goal" :in-theory (e/d (fn-bprl-receipt-intent-record)
                                  (fn-bprl-apply-journal-record
                                   fn-bp-journal-recordp
                                   fn-bprl-receipt-from-adu
                                   fn-bp-receipt-work-id
                                   fn-bpa-decode-exact fn-bpa-receiptp))))))

(local (defthm fn-bpah-view-receipt-is-the-decoded-message
  (implies (fn-bpah-view-release-authorizedp view cfg wf)
           (equal (fn-bpah-view-receipt view)
                  (fn-bpa-result-message
                   (fn-bpa-decode-exact (fn-bpn-nth 3 view)))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-view-release-authorizedp
                               fn-bpah-receipt-authorizes-releasep
                               fn-bpah-receipt-names-obligationp
                               fn-bpah-view-receipt
                               (:executable-counterpart fn-bpa-receiptp))
                             (theory 'minimal-theory))))))

; KEYSTONE 2.  A receipt that releases anything names exactly one held
; obligation: the record exists only when the issuer is authorized at the
; delivering neighbour, the obligation the receipt's work id finds is
; outstanding and the workflow's exact-term check holds for it, and the
; record carries that work's id and the workflow image admits it.
(defthm fn-bpah-released-receipt-names-exactly-its-obligation
  (let* ((r (fn-bpah-receipt-release-record view cfg wf))
         (receipt (fn-bpah-view-receipt view))
         (work (fn-bpah-receipt-obligation wf receipt)))
    (implies r
             (and (fn-bpah-release-issuer-authorizedp
                   cfg (fn-bpah-view-carrier view)
                   (fn-bpah-view-generation view)
                   (fn-bpaj-issuer-eid (fn-bpn-nth 6 view)))
                  (fn-bp-work-outstandingp work)
                  (fn-bp-authorized-receiptp (fn-bp-state-config wf) work
                                             (fn-bprl-receipt-from-adu receipt))
                  (equal (fn-bp-journal-nth 4 r) (fn-bp-work-id work))
                  (car (fn-bprl-apply-journal-record wf r)))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpah-view-release-authorizedp
                                fn-bpah-receipt-authorizes-releasep
                                fn-bpah-receipt-names-obligationp
                                fn-bp-authorized-receiptp)
                              (theory 'minimal-theory))
           :use ((:instance fn-bpah-release-record-needs-authorization)
                 (:instance fn-bpah-release-record-is-the-authorized-intent)
                 (:instance fn-bpah-view-receipt-is-the-decoded-message)
                 (:instance fn-bpah-intent-record-work-id
                            (s wf) (octets (fn-bpn-nth 3 view))
                            (txid (+ 1 (fn-bprl-max-used-txid
                                        (fn-bp-state-used-txs wf) 0)))
                            (generation 0))
                 (:instance fn-bprl-receipt-intent-record-preflights
                            (s wf) (octets (fn-bpn-nth 3 view))
                            (txid (+ 1 (fn-bprl-max-used-txid
                                        (fn-bp-state-used-txs wf) 0)))
                            (generation 0) (authorizedp t))))))

(local (defthm fn-bpah-other-terms-name-no-obligation
  (implies (or (not (fn-bp-work-outstandingp work))
               (not (equal (fn-bpa-receipt-subject receipt)
                           (fn-bp-work-subject work)))
               (not (equal (fn-bpa-receipt-policy-id receipt)
                           (fn-bp-work-policy-id work)))
               (not (equal (fn-bpa-receipt-terms-id receipt)
                           (fn-bp-work-terms-id work))))
           (not (fn-bpah-receipt-names-obligationp wf receipt work)))
  :hints (("Goal" :in-theory (e/d (fn-bpah-receipt-names-obligationp
                                   fn-bp-authorized-receiptp
                                   fn-bprl-receipt-from-adu)
                                  (fn-bp-workp fn-bp-configp fn-bp-receiptp
                                   fn-bpa-receiptp fn-bp-statep
                                   fn-bp-work-outstandingp))))))

; KEYSTONE 3.  A receipt naming a different work, subject, policy or terms
; than the held obligation its work id finds releases nothing, whoever
; issued it.
(defthm fn-bpah-receipt-naming-other-terms-releases-nothing
  (let* ((receipt (fn-bpah-view-receipt view))
         (work (fn-bpah-receipt-obligation wf receipt)))
    (implies (or (not (fn-bp-work-outstandingp work))
                 (not (equal (fn-bpa-receipt-subject receipt)
                             (fn-bp-work-subject work)))
                 (not (equal (fn-bpa-receipt-policy-id receipt)
                             (fn-bp-work-policy-id work)))
                 (not (equal (fn-bpa-receipt-terms-id receipt)
                             (fn-bp-work-terms-id work))))
             (equal (fn-bpah-receipt-release-record view cfg wf) nil)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpah-view-release-authorizedp
                                fn-bpah-receipt-authorizes-releasep)
                              (theory 'minimal-theory))
           :use ((:instance fn-bpah-release-record-needs-authorization)
                 (:instance fn-bpah-other-terms-name-no-obligation
                            (receipt (fn-bpah-view-receipt view))
                            (work (fn-bpah-receipt-obligation
                                   wf (fn-bpah-view-receipt view))))))))

; KEYSTONE 4.  The request path is unchanged by the release list: two
; configurations at one generation that agree once release rows are
; dropped trust the same requests.
(defthm fn-bpah-request-trust-ignores-release-rows
  (implies (and (equal (fn-cfgp cfg1) (fn-cfgp cfg2))
                (equal (fn-cfg-generation cfg1) (fn-cfg-generation cfg2))
                (equal (fn-bpaj-without-release-rows
                        (fn-cfg-peers (fn-cfg-value cfg1)))
                       (fn-bpaj-without-release-rows
                        (fn-cfg-peers (fn-cfg-value cfg2)))))
           (equal (fn-bpah-request-trustedp view cfg1)
                  (fn-bpah-request-trustedp view cfg2)))
  :hints (("Goal" :in-theory (e/d (fn-bpah-request-trustedp
                                   fn-bpah-view-source-decision)
                                  (fn-bpaj-carried-source-decision
                                   fn-bpaj-source-decision-ignores-release-rows
                                   fn-bpaj-source-decision-trustedp
                                   fn-bpaj-without-release-rows))
           :use ((:instance fn-bpaj-source-decision-ignores-release-rows
                            (principal (fn-bpnf-ingress-principal
                                        (fn-bpn-nth 4 view)))
                            (generation (fn-bpn-nth 5 (fn-bpn-nth 4 view)))
                            (source (fn-bpn-nth 6 view)))))))
