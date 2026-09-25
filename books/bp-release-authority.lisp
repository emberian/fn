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
(include-book "hybrid-lifecycle")

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

;; ---------------------------------------------------------------------------
;; The signed receipt (lane signed-receipts, 2026-09-25).  The review of
;; 2026-09-24 asks that release through an untrusted intermediary bind and
;; verify the receipt itself against the authorized issuer and the exact
;; work, content subject, requester and terms.  The receipt ADU's nine
;; fields are the issuer EID, work, subject, counterpart, policy,
;; incarnation, authority context and terms; the signed body adds the
;; requester, and the article scheme's subject body adds the issuer's
;; principal and its two enrolled keys.  Table: specs/bp-node-machine.md
;; section 6.1, "The signed receipt bytes".

(defconst *fn-bpsr-domain-tag*
  '(102 110 45 98 112 45 114 101 99 101 105 112 116 45 104 121 98 114 105
    100 45 118 49)) ; fn-bp-receipt-hybrid-v1

; Two canonical CBOR byte strings: the requester's EID text (the node the
; receipt is addressed to) and the exact receipt ADU octets.
(defun fn-bpsr-signed-body (requester adu)
  (declare (xargs :guard t))
  (fn-bpa-encode-fields (list (fn-record-string-octets requester) adu)))

; The octets both primitives sign: the article scheme's subject body
; (`fn-hsig-subject-body': version, suite, principal, both keys, u16 length,
; body) under this domain tag instead of the authored-source tag, so no
; receipt signature is an article signature or the reverse.  Nil outside
; the profile.
(defun fn-bpsr-signed-preimage (principal keys requester adu)
  (declare (xargs :guard t :verify-guards nil))
  (let ((body (fn-bpsr-signed-body requester adu)))
    (if (and (stringp requester)
             (fn-hsig-subject-p principal keys body))
        (fn-digest-tagged-preimage *fn-bpsr-domain-tag*
                                   (fn-hsig-subject-body principal keys body))
      nil)))

(defconst *fn-bpah-signer-slot* "bp-boundary-receipt-signer")
(defconst *fn-bpah-require-signed-slot* "bp-boundary-require-signed-receipts")

; The delivering neighbour's boundary carries the policy flag
; `require-signed-receipts': receipts it delivers release only by their own
; signature.
(defun fn-bpah-require-signed-receiptsp (cfg carrier generation)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-cfgp cfg)
       (equal generation (fn-cfg-generation cfg))
       (fn-bpaj-boundary-rowp (fn-cfg-peers (fn-cfg-value cfg))
                              (fn-record-octets-string carrier)
                              *fn-bpah-require-signed-slot* "yes" 0)))

; The issuer's OWN enrollment at this node -- the unique boundary directly
; enrolled for the issuer EID, the author boundary, never the delivering
; carrier's -- names PRINCIPAL (rendered hex, compared as text) as its
; receipt signer.
(defun fn-bpah-receipt-signer-enrolledp (cfg generation issuer principal)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((rows (fn-cfg-peers (fn-cfg-value cfg)))
         (names (fn-bpaj-enrolled-source-names
                 rows rows (fn-bpaj-tagged-value issuer))))
    (and (fn-cfgp cfg)
         (equal generation (fn-cfg-generation cfg))
         (fn-bpaj-issuer-eidp issuer)
         (consp names)
         (null (cdr names))
         (fn-hsig-exact-octets-p principal 32)
         (fn-bpaj-boundary-rowp
          rows (car names) *fn-bpah-signer-slot*
          (fn-record-octets-string (fn-stx-hex-octets principal)) 0))))

; This Store's current enrolled key set for PRINCIPAL (its newest kind-3
; snapshot, not a revocation), or nil.
(defun fn-bpah-receipt-signer-keys (snapshots principal)
  (declare (xargs :guard t :verify-guards nil))
  (let ((value (fn-hsig-keyring-snapshot-value
                (fn-hl-current-for-principal principal snapshots))))
    (if (and (consp value) (equal (car value) principal)
             (consp (cdr value)))
        (cadr value)
      nil)))

; The third way.  SIGNED is the decoded signed receipt, REQUESTER this
; node's EID text, OBS the host's two primitive observations over
; `fn-bpsr-signed-preimage' as (observed-ml-key ed25519 ml-dsa-65).  The
; verdict is `fn-hsig-authorize', the article scheme's conjunction.
(defun fn-bpah-receipt-signature-verifiedp
    (cfg snapshots generation issuer requester signed obs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((principal (fn-bpsr-principal signed))
         (keys (fn-bpah-receipt-signer-keys snapshots principal)))
    (and (fn-bpsr-signedp signed)
         (stringp requester)
         (fn-bpah-receipt-signer-enrolledp cfg generation issuer principal)
         keys
         (fn-hsig-authorize principal keys
                            (fn-bpsr-signed-body requester
                                                 (fn-bpsr-adu signed))
                            (fn-bpsr-signatures signed)
                            (fn-bpa-nth 0 obs) (fn-bpa-nth 1 obs)
                            (fn-bpa-nth 2 obs)))))

; D23 question 4: receipt-authorizes-release(issuer, work, subject, terms,
; evidence).  CARRIER and GENERATION are the delivering neighbour's ingress
; stamp, ISSUER a release-issuer EID, RECEIPT the decoded receipt ADU, WORK
; the held obligation, SIGNED the signed receipt carrying RECEIPT (nil for
; a bare one), REQUESTER this node's EID and SNAPSHOTS/OBS the keyring and
; observations the signature is judged under.  Three ways:
;   1. the carrier is the issuer (its own enrolled EID),
;   2. the issuer is on the carrier's release list,
;   3. the receipt's own signature verifies under the issuer's enrollment.
; A signed receipt is judged by 3 alone: a signature that fails is
; evidence of tampering, not a reason to fall back to the carrier's word.
; A carrier flagged `require-signed-receipts' admits 3 alone.  A
; carried-list entry is not an input.
(defun fn-bpah-receipt-authorizes-releasep
    (cfg carrier generation issuer wf receipt work
         snapshots signed requester obs)
  (declare (xargs :guard t :verify-guards nil))
  (and (if signed
           (fn-bpah-receipt-signature-verifiedp
            cfg snapshots generation issuer requester signed obs)
         (and (not (fn-bpah-require-signed-receiptsp cfg carrier generation))
              (fn-bpah-release-issuer-authorizedp cfg carrier generation
                                                  issuer)))
       (equal (fn-bpaj-tagged-value issuer) (fn-bpa-receipt-issuer receipt))
       (fn-bpah-receipt-names-obligationp wf receipt work)))

(defun fn-bpah-view-signed (view)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpsr-decode (fn-bpn-nth 3 view)))

(defun fn-bpah-view-adu-octets (view)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpsr-adu-octets (fn-bpn-nth 3 view)))

; A delivered receipt's shape, whichever way it is authorized: addressed as
; a receipt, stamped with its ingress, and naming its bundle source as both
; issuer and counterpart.
(defun fn-bpah-receipt-shapep (view)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp view)
       (equal (car view) :delivery)
       (equal (fn-bpah-view-class view) :receipt)
       (fn-bpnf-cl-ingressp (fn-bpn-nth 4 view))
       (stringp (fn-bpn-nth 6 view))
       (stringp (fn-bpn-nth 7 view))
       (let ((receipt (fn-bpah-view-receipt view)))
         (and receipt
              (equal (fn-bpa-receipt-issuer receipt) (fn-bpn-nth 6 view))
              (equal (fn-bpa-receipt-peer-eid receipt)
                     (fn-bpn-nth 6 view))))))

; THE HOST'S GATE (host/native/bp-node.lisp, `fnn-bpnode-receipt-result').
(defun fn-bpah-receipt-gatep (view cfg snapshots obs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((signed (fn-bpah-view-signed view)))
    (if signed
        (and (fn-bpah-receipt-shapep view)
             (fn-bpah-receipt-signature-verifiedp
              cfg snapshots (fn-bpah-view-generation view)
              (fn-bpaj-issuer-eid (fn-bpn-nth 6 view)) (fn-bpn-nth 7 view)
              signed obs))
      (and (not (fn-bpah-require-signed-receiptsp
                 cfg (fn-bpah-view-carrier view)
                 (fn-bpah-view-generation view)))
           (fn-bpah-receipt-trustedp view cfg)))))

(defun fn-bpah-view-release-authorizedp (view cfg wf snapshots obs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((receipt (fn-bpah-view-receipt view)))
    (and (fn-bpah-receipt-gatep view cfg snapshots obs)
         (fn-bpah-receipt-authorizes-releasep
          cfg (fn-bpah-view-carrier view) (fn-bpah-view-generation view)
          (fn-bpaj-issuer-eid (fn-bpn-nth 6 view)) wf receipt
          (fn-bpah-receipt-obligation wf receipt)
          snapshots (fn-bpah-view-signed view) (fn-bpn-nth 7 view) obs))))

; THE HOST-CALLED FUNCTION.  The workflow receipt-intent record the host
; publishes for a delivered receipt, authorized by the release question over
; the live configuration, this Store's keyring, the host's two primitive
; observations and the recovered workflow image; nil publishes nothing and
; releases nothing.  The workflow reads the receipt ADU the payload carries.
(defun fn-bpah-receipt-release-record (view cfg wf snapshots obs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bprl-receipt-auto-record
   wf (fn-bpah-view-adu-octets view)
   (if (fn-bpah-view-release-authorizedp view cfg wf snapshots obs) t nil)))

; What the host verifies at A: (preimage ed25519-key ml-dsa-65-key
; signatures) for a signed receipt whose principal this Store has enrolled,
; else nil (nothing to observe).  The host asks both primitives over exactly
; this preimage (`fnn-hsig-observe-raw', the transit path's) and hands the
; observations back; it decides nothing.
(defun fn-bpah-receipt-signature-plan (view snapshots)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((signed (fn-bpah-view-signed view))
         (principal (fn-bpsr-principal signed))
         (keys (and signed
                    (fn-bpah-receipt-signer-keys snapshots principal)))
         (preimage (and keys
                        (fn-bpsr-signed-preimage principal keys
                                                 (fn-bpn-nth 7 view)
                                                 (fn-bpsr-adu signed)))))
    (if preimage
        (list preimage (fn-bpa-cdr (fn-bpa-car keys))
              (fn-bpa-cdr (fn-bpa-car (fn-bpa-cdr keys)))
              (fn-bpsr-signatures signed))
      nil)))

; What B signs: the preimage for its own receipt ADU addressed to REQUESTER,
; and the signed-receipt octets it queues.
(defun fn-bpsr-host-preimage (principal keys requester adu)
  (declare (xargs :guard t :verify-guards nil))
  (let ((decoded (fn-bpa-decode-exact adu)))
    (if (and (fn-bpa-result-okp decoded)
             (fn-bpa-receiptp (fn-bpa-result-message decoded)))
        (fn-bpsr-signed-preimage principal keys requester adu)
      nil)))

(defun fn-bpsr-host-encode (adu principal ed ml)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpsr-encode (fn-bpsr-make adu principal ed ml)))

; The signature half of the verdict: nil when the receipt is bare and the
; carrier does not require a signature.
(defun fn-bpah-receipt-signature-verdict (view cfg snapshots obs)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-bpah-view-signed view)
         (if (fn-bpah-receipt-gatep view cfg snapshots obs)
             :signed-issuer :signature-refused))
        ((fn-bpah-require-signed-receiptsp
          cfg (fn-bpah-view-carrier view) (fn-bpah-view-generation view))
         :signature-required)
        (t nil)))

; The verdict before the workflow is asked: ingress, generation and shape
; first, then the signature half, then the issuer half.
(defun fn-bpah-receipt-issuer-verdict (view cfg snapshots obs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((base (fn-bpah-release-issuer-verdict view cfg)))
    (if (member-equal base '(:ingress :generation :not-a-receipt))
        base
      (or (fn-bpah-receipt-signature-verdict view cfg snapshots obs) base))))

; The verdict the kind-7 delivery row keeps (`fn-bpah-release-detail').
(defun fn-bpah-receipt-release-verdict (view cfg wf snapshots obs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((v (fn-bpah-receipt-issuer-verdict view cfg snapshots obs)))
    (cond ((not (member-equal v '(:self-issued :listed-issuer :signed-issuer)))
           v)
          ((not (fn-bpah-view-release-authorizedp view cfg wf snapshots obs))
           :obligation-mismatch)
          ((not (fn-bpah-receipt-release-record view cfg wf snapshots obs))
           :workflow-refused)
          (t v))))

; The line the host prints for a receipt, before its gate.
(defun fn-bpah-receipt-release-line (view cfg snapshots obs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((issuer (fn-bpn-nth 6 view)))
    (string-append
     (fn-bpah-release-verdict-name
      (fn-bpah-receipt-issuer-verdict view cfg snapshots obs))
     (string-append
      " carrier="
      (string-append
       (fn-record-octets-string (fn-bpah-view-carrier view))
       (string-append " issuer=" (if (stringp issuer) issuer "")))))))

(local (defthm fn-bpah-auto-record-unauthorized-is-nil
  (equal (fn-bprl-receipt-auto-record s octets nil) nil)
  :hints (("Goal" :in-theory (enable fn-bprl-receipt-auto-record
                                     fn-bprl-receipt-intent-record)))))

(local (defthm fn-bpah-view-release-needs-gate
  (implies (not (fn-bpah-receipt-gatep view cfg snapshots obs))
           (not (fn-bpah-view-release-authorizedp view cfg wf snapshots obs)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-view-release-authorizedp) (theory 'minimal-theory))))))

(local (defthm fn-bpah-release-record-needs-gate
  (implies (not (fn-bpah-receipt-gatep view cfg snapshots obs))
           (equal (fn-bpah-receipt-release-record view cfg wf snapshots obs)
                  nil))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-receipt-release-record
                               fn-bpah-auto-record-unauthorized-is-nil
                               fn-bpah-view-release-needs-gate) (theory 'minimal-theory))))))

(local (defthm fn-bpah-unsigned-gate-is-trust
  (implies (not (fn-bpah-view-signed view))
           (equal (fn-bpah-receipt-gatep view cfg snapshots obs)
                  (and (not (fn-bpah-require-signed-receiptsp
                             cfg (fn-bpah-view-carrier view)
                             (fn-bpah-view-generation view)))
                       (fn-bpah-receipt-trustedp view cfg))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-receipt-gatep) (theory 'minimal-theory))))))

; KEYSTONE 1.  A bare (unsigned) receipt whose issuer is not authorized for
; release at the delivering neighbour is refused by the host's gate and
; releases nothing: no record, so the workflow image and the pin are
; unchanged.  A signed receipt is the third way's (keystones 5 and 6).
(defthm fn-bpah-unauthorized-issuer-releases-nothing
  (implies (and (not (fn-bpah-view-signed view))
                (not (fn-bpah-release-issuer-authorizedp
                      cfg (fn-bpah-view-carrier view)
                      (fn-bpah-view-generation view)
                      (fn-bpaj-issuer-eid (fn-bpn-nth 6 view)))))
           (and (not (fn-bpah-receipt-gatep view cfg snapshots obs))
                (equal (fn-bpah-receipt-release-record view cfg wf snapshots obs)
                       nil)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-unauthorized-issuer-never-authorizes-receipt
                               fn-bpah-unsigned-gate-is-trust
                               fn-bpah-release-record-needs-gate) (theory 'minimal-theory)))))

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
; a releases-for row for the issuer of a bare receipt.  Its carried list is
; not a hypothesis: carrying the issuer's EID releases nothing.
(defthm fn-bpah-carrier-without-release-row-releases-nothing
  (let ((rows (fn-cfg-peers (fn-cfg-value cfg)))
        (name (fn-record-octets-string (fn-bpah-view-carrier view)))
        (issuer (fn-bpn-nth 6 view)))
    (implies (and (not (fn-bpah-view-signed view))
                  (not (fn-bpaj-boundary-rowp rows name "transport-bp"
                                               issuer 0))
                  (not (fn-bpaj-boundary-rowp rows name
                                               "bp-boundary-releases-for"
                                               issuer 0)))
             (and (not (fn-bpah-receipt-gatep view cfg snapshots obs))
                  (equal (fn-bpah-receipt-release-record view cfg wf snapshots obs)
                         nil))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-unauthorized-issuer-releases-nothing) (theory 'minimal-theory))
           :use ((:instance fn-bpah-no-row-no-release-authority
                            (carrier (fn-bpah-view-carrier view))
                            (generation (fn-bpah-view-generation view))
                            (issuer (fn-bpn-nth 6 view)))))))

(local (defthm fn-bpah-release-record-needs-authorization
  (implies (fn-bpah-receipt-release-record view cfg wf snapshots obs)
           (fn-bpah-view-release-authorizedp view cfg wf snapshots obs))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-receipt-release-record
                               fn-bpah-auto-record-unauthorized-is-nil) (theory 'minimal-theory))))))

(local (defthm fn-bpah-release-record-is-the-authorized-intent
  (implies (fn-bpah-receipt-release-record view cfg wf snapshots obs)
           (equal (fn-bpah-receipt-release-record view cfg wf snapshots obs)
                  (fn-bprl-receipt-intent-record
                   wf (fn-bpah-view-adu-octets view)
                   (+ 1 (fn-bprl-max-used-txid (fn-bp-state-used-txs wf) 0))
                   0 t)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-receipt-release-record
                               fn-bprl-receipt-auto-record
                               fn-bpah-auto-record-unauthorized-is-nil) (theory 'minimal-theory))
           :use ((:instance fn-bprl-receipt-intent-record-preflights
                            (s wf) (octets (fn-bpah-view-adu-octets view))
                            (txid (+ 1 (fn-bprl-max-used-txid
                                        (fn-bp-state-used-txs wf) 0)))
                            (generation 0)
                            (authorizedp (fn-bpah-view-release-authorizedp
                                          view cfg wf snapshots obs))))))))

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
  (implies (fn-bpah-view-release-authorizedp view cfg wf snapshots obs)
           (equal (fn-bpah-view-receipt view)
                  (fn-bpa-result-message
                   (fn-bpa-decode-exact (fn-bpah-view-adu-octets view)))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpah-view-release-authorizedp
                               fn-bpah-receipt-authorizes-releasep
                               fn-bpah-receipt-names-obligationp
                               fn-bpah-view-receipt
                               fn-bpah-view-adu-octets
                               (:executable-counterpart fn-bpa-receiptp))
                             (theory 'minimal-theory))))))

; KEYSTONE 2.  A receipt that releases anything names exactly one held
; obligation: the record exists only when the receipt is authorized (a
; signed receipt by its own verified signature under the issuer's
; enrollment, a bare one by the issuer's authority at the delivering
; neighbour), the obligation the receipt's work id finds is outstanding and
; the workflow's exact-term check holds for it, and the record carries that
; work's id and the workflow image admits it.
(defthm fn-bpah-released-receipt-names-exactly-its-obligation
  (let* ((r (fn-bpah-receipt-release-record view cfg wf snapshots obs))
         (receipt (fn-bpah-view-receipt view))
         (work (fn-bpah-receipt-obligation wf receipt))
         (signed (fn-bpah-view-signed view))
         (carrier (fn-bpah-view-carrier view))
         (generation (fn-bpah-view-generation view))
         (issuer (fn-bpaj-issuer-eid (fn-bpn-nth 6 view))))
    (implies r
             (and (if signed
                      (fn-bpah-receipt-signature-verifiedp
                       cfg snapshots generation issuer (fn-bpn-nth 7 view)
                       signed obs)
                    (fn-bpah-release-issuer-authorizedp
                     cfg carrier generation issuer))
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
                            (s wf) (octets (fn-bpah-view-adu-octets view))
                            (txid (+ 1 (fn-bprl-max-used-txid
                                        (fn-bp-state-used-txs wf) 0)))
                            (generation 0))
                 (:instance fn-bprl-receipt-intent-record-preflights
                            (s wf) (octets (fn-bpah-view-adu-octets view))
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
; issued it and whoever signed it: for a signed receipt these are the
; signed fields.
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
             (equal (fn-bpah-receipt-release-record view cfg wf snapshots obs)
                    nil)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpah-view-release-authorizedp
                                fn-bpah-receipt-authorizes-releasep)
                              (theory 'minimal-theory))
           :use ((:instance fn-bpah-release-record-needs-authorization)
                 (:instance fn-bpah-other-terms-name-no-obligation
                            (receipt (fn-bpah-view-receipt view))
                            (work (fn-bpah-receipt-obligation
                                   wf (fn-bpah-view-receipt view))))))))

; KEYSTONE 5.  The third way: a signed receipt whose signature verifies
; under the issuer's own enrollment at this node, and which names the held
; obligation, is released by the host's function exactly as the workflow
; releases an authorized receipt ADU -- through ANY delivering neighbour.
; No hypothesis mentions the carrier's rows: it need be neither the issuer
; nor list it, and its require-signed-receipts flag does not matter.
(defthm fn-bpah-signed-receipt-releases-through-any-carrier
  (let* ((receipt (fn-bpah-view-receipt view))
         (signed (fn-bpah-view-signed view)))
    (implies (and signed
                  (fn-bpah-receipt-shapep view)
                  (fn-bpah-receipt-signature-verifiedp
                   cfg snapshots (fn-bpah-view-generation view)
                   (fn-bpaj-issuer-eid (fn-bpn-nth 6 view))
                   (fn-bpn-nth 7 view) signed obs)
                  (fn-bpah-receipt-names-obligationp
                   wf receipt (fn-bpah-receipt-obligation wf receipt)))
             (equal (fn-bpah-receipt-release-record view cfg wf snapshots obs)
                    (fn-bprl-receipt-auto-record
                     wf (fn-bpsr-adu signed) t))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpah-receipt-release-record
                                fn-bpah-view-release-authorizedp
                                fn-bpah-receipt-authorizes-releasep
                                fn-bpah-receipt-gatep
                                fn-bpah-receipt-shapep
                                fn-bpah-view-adu-octets
                                fn-bpah-view-signed
                                fn-bpsr-adu-octets
                                fn-bpaj-issuer-eid fn-bpaj-tagged-value
                                car-cons cdr-cons)
                              (theory 'minimal-theory)))))

; KEYSTONE 6.  A signed receipt whose signature does not verify under the
; issuer's enrollment releases nothing, whoever delivered it: a direct
; neighbour or a listed relay does not rescue it.
(defthm fn-bpah-unverified-signed-receipt-releases-nothing
  (let ((signed (fn-bpah-view-signed view)))
    (implies (and signed
                  (not (fn-bpah-receipt-signature-verifiedp
                        cfg snapshots (fn-bpah-view-generation view)
                        (fn-bpaj-issuer-eid (fn-bpn-nth 6 view))
                        (fn-bpn-nth 7 view) signed obs)))
             (and (not (fn-bpah-receipt-gatep view cfg snapshots obs))
                  (equal (fn-bpah-receipt-release-record
                          view cfg wf snapshots obs)
                         nil))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpah-receipt-gatep
                                fn-bpah-release-record-needs-gate)
                              (theory 'minimal-theory)))))

; KEYSTONE 7.  The signature verdict is the article scheme's conjunction:
; unless both primitive observations are :verified, the signature is not
; verified (the lab's flipped-bytes case: ML-DSA-65 and Ed25519 refuse).
(defthm fn-bpah-receipt-signature-needs-both-observations
  (implies (fn-bpah-receipt-signature-verifiedp
            cfg snapshots generation issuer requester signed obs)
           (and (equal (fn-bpa-nth 1 obs) :verified)
                (equal (fn-bpa-nth 2 obs) :verified)
                (fn-bpah-receipt-signer-enrolledp
                 cfg generation issuer (fn-bpsr-principal signed))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpah-receipt-signature-verifiedp)
                              (theory 'minimal-theory))
           :use ((:instance fn-hsig-authorization-requires-both-components-by-definition
                            (principal (fn-bpsr-principal signed))
                            (keys (fn-bpah-receipt-signer-keys
                                   snapshots (fn-bpsr-principal signed)))
                            (source (fn-bpsr-signed-body
                                     requester (fn-bpsr-adu signed)))
                            (signatures (fn-bpsr-signatures signed))
                            (observed (fn-bpa-nth 0 obs))
                            (ed (fn-bpa-nth 1 obs))
                            (ml (fn-bpa-nth 2 obs)))))))

; KEYSTONE 8.  The delegation profile, stated honestly: a bare receipt the
; gate trusts (its issuer is the delivering neighbour or on its release
; list) and that names the held obligation is released -- nothing here
; says the issuer wrote it, so a listed relay's forgery naming the exact
; obligation releases too.  Unless the carrier requires signed receipts:
; KEYSTONE 9.
(defthm fn-bpah-trusted-bare-receipt-releases
  (let ((receipt (fn-bpah-view-receipt view)))
    (implies (and (not (fn-bpah-view-signed view))
                  (not (fn-bpah-require-signed-receiptsp
                        cfg (fn-bpah-view-carrier view)
                        (fn-bpah-view-generation view)))
                  (fn-bpah-receipt-trustedp view cfg)
                  (fn-bpah-receipt-names-obligationp
                   wf receipt (fn-bpah-receipt-obligation wf receipt)))
             (equal (fn-bpah-receipt-release-record view cfg wf snapshots obs)
                    (fn-bprl-receipt-auto-record wf (fn-bpn-nth 3 view) t))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpah-receipt-release-record
                                fn-bpah-view-release-authorizedp
                                fn-bpah-receipt-authorizes-releasep
                                fn-bpah-receipt-trustedp
                                fn-bpah-unsigned-gate-is-trust
                                fn-bpah-view-adu-octets
                                fn-bpah-view-signed
                                fn-bpsr-adu-octets-of-unsigned
                                fn-bpaj-issuer-eid fn-bpaj-tagged-value
                                car-cons cdr-cons)
                              (theory 'minimal-theory)))))

; KEYSTONE 9.  Under `require-signed-receipts' on the delivering
; neighbour's boundary, a bare receipt releases nothing, whoever issued it
; and whatever the carrier's release list says.
(defthm fn-bpah-required-signature-refuses-bare-receipts
  (implies (and (not (fn-bpah-view-signed view))
                (fn-bpah-require-signed-receiptsp
                 cfg (fn-bpah-view-carrier view)
                 (fn-bpah-view-generation view)))
           (and (not (fn-bpah-receipt-gatep view cfg snapshots obs))
                (equal (fn-bpah-receipt-release-record
                        view cfg wf snapshots obs)
                       nil)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpah-unsigned-gate-is-trust
                                fn-bpah-release-record-needs-gate)
                              (theory 'minimal-theory)))))

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
