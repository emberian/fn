; A3 handoff selection from the single FNBS held list.  This book makes no
; network or Store decision.  Its result is the application work the native
; owner must drive through the existing Store/FNRJ or release join.
(in-package "ACL2")
(include-book "bp-node-foundation")
(include-book "bp-adu")
(include-book "bp-native-app")
(include-book "bp-session-admission")
(verify-guards fn-bpaj-eid-text)

(defun fn-bpah-local-pendingp (held node)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :do-not-induct t
                    :use ((:instance fn-bpnf-heldp-primary-blockp))
                    :in-theory (disable fn-bpnf-heldp fn-bpb-bundlep
                                        fn-bpp-blockp fn-bpp-eidp
                                        fn-bpah-held-class)))))
  ;; A fragment is never a local delivery: the header answers that before
  ;; fn-bpnf-heldp re-encodes the row (PRF-136).
  (mbe :logic
    (and (fn-bpnf-heldp held)
         (fn-bpp-eidp node)
         (let ((bundle (fn-bpnf-held-bundle held)))
           (and (fn-bpb-bundlep bundle)
                (let ((primary (fn-bpb-bundle-primary bundle)))
                  (and (fn-bpp-blockp primary)
                       (natp (fn-bpp-flags primary))
                       (not (fn-bpp-fragmentp (fn-bpp-flags primary)))
                       (equal (fn-bpp-destination primary) node)
                       (null (fn-bpn-nth 10 held))
                       (equal (fn-bpn-nth 12 held) '(:dispatch-pending))
                       (null (fn-bpn-nth 14 held))
                       (member-equal (fn-bpah-held-class held)
                                     '(:request :receipt)))))))
       :exec (and (fn-bpnf-held-nonfragment-headerp held)
         (and (fn-bpnf-heldp held)
              (fn-bpp-eidp node)
              (let ((bundle (fn-bpnf-held-bundle held)))
                (and (fn-bpb-bundlep bundle)
                     (let ((primary (fn-bpb-bundle-primary bundle)))
                       (and (fn-bpp-blockp primary)
                            (natp (fn-bpp-flags primary))
                            (not (fn-bpp-fragmentp (fn-bpp-flags primary)))
                            (equal (fn-bpp-destination primary) node)
                            (null (fn-bpn-nth 10 held))
                            (equal (fn-bpn-nth 12 held) '(:dispatch-pending))
                            (null (fn-bpn-nth 14 held))
                            (member-equal (fn-bpah-held-class held)
                                          '(:request :receipt))))))))))

;; PRF-136: the executable body's header prefilter refuses only rows the
;; definition refuses (the guard proof's equality, stated).
(defthm fn-bpah-local-pendingp-has-a-nonfragment-header
  (implies (fn-bpah-local-pendingp held node)
           (fn-bpnf-held-nonfragment-headerp held))
  :hints (("Goal" :use ((:instance fn-bpnf-heldp-primary-blockp))
           :in-theory (disable fn-bpnf-heldp fn-bpb-bundlep fn-bpp-blockp
                               fn-bpp-eidp fn-bpah-held-class)))
  :rule-classes nil)

(defun fn-bpah-select-oldest (held-list node selected)
  (declare (xargs :guard t))
  (if (atom held-list)
      selected
    (let* ((candidate (car held-list))
           (selected
             (if (and (fn-bpah-local-pendingp candidate node)
                      (or (null selected)
                          (< (nfix (fn-bpn-nth 3 candidate))
                             (nfix (fn-bpn-nth 3 selected)))))
                 candidate selected)))
      (fn-bpah-select-oldest (cdr held-list) node selected))))

(defun fn-bpah-pending-view (st node)
  (declare (xargs :guard t))
  (let ((held (fn-bpah-select-oldest (fn-bpnf-held-list st) node nil)))
    (if (not (fn-bpnf-heldp held))
        nil
      (let* ((bundle (fn-bpnf-held-bundle held))
             (primary (fn-bpb-bundle-primary bundle)))
        (if (and (fn-bpb-bundlep bundle) (fn-bpp-blockp primary))
            (list :delivery
                  (fn-bpnf-held-key (fn-bpnf-held-principal held)
                                     (fn-bpnf-held-id held))
                  (fn-bpah-held-class held)
                  (fn-bpb-payload bundle)
                  (fn-bpn-nth 4 held)
                  (fn-bpp-primary-identity primary)
                  (fn-bpaj-eid-text (fn-bpp-source primary))
                  (fn-bpaj-eid-text (fn-bpp-destination primary)))
          nil)))))

; The native bp-node caller asks this selector before invoking Store.  A
; fragment can carry bytes that happen to decode as a complete request ADU;
; those bytes are not eligible until a durable family replacement has made a
; new whole-bundle held row.
(defthm fn-bpah-local-pending-excludes-fragment
  (implies (fn-bpah-local-pendingp held node)
           (not (fn-bpp-fragmentp
                 (fn-bpp-flags (fn-bpb-bundle-primary
                                (fn-bpnf-held-bundle held))))))
  :hints (("Goal" :in-theory (enable fn-bpah-local-pendingp))))

(defthm fn-bpah-select-oldest-retains-pending
  (implies (or (null selected) (fn-bpah-local-pendingp selected node))
           (let ((h (fn-bpah-select-oldest held-list node selected)))
             (or (null h) (fn-bpah-local-pendingp h node))))
  :hints (("Goal" :induct (fn-bpah-select-oldest held-list node selected)
           :in-theory (disable fn-bpah-local-pendingp fn-bpah-held-class))))

(defthm fn-bpah-host-pending-view-excludes-fragment
  (implies (equal (car (fn-bpah-pending-view st node)) :delivery)
           (not (fn-bpp-fragmentp
                 (fn-bpp-flags
                  (fn-bpb-bundle-primary
                   (fn-bpnf-held-bundle
                    (fn-bpah-select-oldest (fn-bpnf-held-list st)
                                            node nil)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpah-select-oldest-retains-pending
                            (held-list (fn-bpnf-held-list st))
                            (selected nil))
                 (:instance fn-bpah-local-pending-excludes-fragment
                            (held (fn-bpah-select-oldest
                                   (fn-bpnf-held-list st) node nil))))
           :in-theory (e/d (fn-bpah-pending-view)
                           (fn-bpah-select-oldest-retains-pending
                            fn-bpah-local-pending-excludes-fragment
                            fn-bpah-local-pendingp fn-bpah-select-oldest
                            fn-bpah-held-class fn-bpp-fragmentp))))
  :rule-classes nil)

(defun fn-bpah-view-class (view)
  (declare (xargs :guard t))
  (fn-bpn-nth 2 view))

;; D23: the one source decision for a delivered view.  The ingress is the
;; TCPCL neighbour stamped at reception; element 6 is the bundle's source EID
;; text.  `fn-bpaj-carried-source-decision' (bp-session-admission) decides
;; direct, carried (judged under the author's own enrollment) or refused.
(defun fn-bpah-view-source-decision (view cfg)
  (declare (xargs :guard t))
  (let ((ingress (fn-bpn-nth 4 view)))
    (if (and (fn-bpnf-cl-ingressp ingress)
             (stringp (fn-bpn-nth 6 view)))
        (fn-bpaj-carried-source-decision
         cfg (fn-bpnf-ingress-principal ingress)
         (fn-bpn-nth 5 ingress) (fn-bpn-nth 6 view))
      (list :refused :ingress))))

(defun fn-bpah-request-trustedp (view cfg)
  (declare (xargs :guard t))
  (and (consp view)
       (equal (car view) :delivery)
       (equal (fn-bpah-view-class view) :request)
       (fn-bpaj-source-decision-trustedp
        (fn-bpah-view-source-decision view cfg))))

;; D23, question 3: author publication.  AUTHOR (a principal) is this
;; node's own direct enrollment for SOURCE (a BP source EID) at GENERATION:
;; its trust profile and transport-bp row.  It is the enrollment a carried
;; request is judged under (`fn-bpaj-ingress-peer' names this principal to
;; the transit plan); the inbound groups and limits under that principal are
;; the plan's own scope check and are not repeated here.
(defun fn-bpah-author-publication-authorizedp (cfg author generation source)
  (declare (xargs :guard t))
  (and (fn-bpaj-principal-idp author)
       (fn-bpaj-source-eidp source)
       (fn-bpaj-current-peer-eidp cfg (fn-bpaj-tagged-value author) generation
                                  (fn-bpaj-tagged-value source))))

;; D23, question 4, its issuer half (the whole question, with the held
;; obligation, is `fn-bpah-receipt-authorizes-releasep' in
;; bp-release-authority).  The delivering neighbour CARRIER may bring a
;; receipt issued by ISSUER (a release-issuer EID) when ISSUER is the
;; carrier's own enrolled EID -- a neighbour speaking for itself, the direct
;; trusted-local-observation-v0 profile -- or ISSUER is on the carrier's
;; release list (`bp-boundary-releases-for').  The carried list is not an
;; input: a neighbour allowed to carry Alice's article is not thereby
;; entitled to assert Bob's receipt.  In the trusted-relay profile the
;; release list is a finite delegation: the node trusts that CARRIER
;; faithfully relays ISSUER's receipts; nothing here authenticates ISSUER.
(defun fn-bpah-release-issuer-authorizedp (cfg carrier generation issuer)
  (declare (xargs :guard t))
  (and (fn-bpaj-issuer-eidp issuer)
       (or (fn-bpaj-current-peer-eidp cfg carrier generation
                                      (fn-bpaj-tagged-value issuer))
           (fn-bpaj-release-issuer-listedp cfg carrier generation issuer))))

(defun fn-bpah-view-carrier (view)
  (declare (xargs :guard t))
  (fn-bpnf-ingress-principal (fn-bpn-nth 4 view)))

(defun fn-bpah-view-generation (view)
  (declare (xargs :guard t))
  (fn-bpn-nth 5 (fn-bpn-nth 4 view)))

; The receipt ADU of a view, or nil.  A signed receipt
; (books/bp-signed-receipt.lisp) is read through the ADU it carries.
(defun fn-bpah-view-receipt (view)
  (declare (xargs :guard t))
  (let ((decoded (fn-bpa-decode-exact (fn-bpsr-adu-octets (fn-bpn-nth 3 view)))))
    (if (and (fn-bpa-result-okp decoded)
             (fn-bpa-receiptp (fn-bpa-result-message decoded)))
        (fn-bpa-result-message decoded)
      nil)))

; The host's receipt gate reads the release question, not the carriage one.
(defun fn-bpah-receipt-trustedp (view cfg)
  (declare (xargs :guard t))
  (and (consp view)
       (equal (car view) :delivery)
       (equal (fn-bpah-view-class view) :receipt)
       (fn-bpnf-cl-ingressp (fn-bpn-nth 4 view))
       (stringp (fn-bpn-nth 6 view))
       (fn-bpah-release-issuer-authorizedp
        cfg (fn-bpah-view-carrier view) (fn-bpah-view-generation view)
        (fn-bpaj-issuer-eid (fn-bpn-nth 6 view)))
       (let ((receipt (fn-bpah-view-receipt view)))
         (and receipt
              (equal (fn-bpa-receipt-issuer receipt) (fn-bpn-nth 6 view))
              (equal (fn-bpa-receipt-peer-eid receipt)
                     (fn-bpn-nth 6 view))))))

; ACL2's reason for the issuer half, as a keyword the host prints and the
; kind-7 delivery row keeps.
(defun fn-bpah-release-issuer-verdict (view cfg)
  (declare (xargs :guard t))
  (let ((carrier (fn-bpah-view-carrier view))
        (generation (fn-bpah-view-generation view))
        (source (fn-bpn-nth 6 view)))
    (cond ((not (and (fn-bpnf-cl-ingressp (fn-bpn-nth 4 view))
                     (stringp source)))
           :ingress)
          ((not (and (fn-cfgp cfg) (equal generation (fn-cfg-generation cfg))))
           :generation)
          ((not (fn-bpah-view-receipt view)) :not-a-receipt)
          ((fn-bpaj-current-peer-eidp cfg carrier generation source)
           :self-issued)
          ((fn-bpaj-release-issuer-listedp cfg carrier generation
                                           (fn-bpaj-issuer-eid source))
           :listed-issuer)
          ((fn-bpaj-origin-carriage-permittedp cfg carrier generation
                                               (fn-bpaj-source-eid source))
           :carried-not-released)
          (t :issuer-not-released))))

(defun fn-bpah-release-verdict-name (verdict)
  (declare (xargs :guard t))
  (cond ((equal verdict :self-issued) "self-issued")
        ((equal verdict :listed-issuer) "listed-issuer")
        ((equal verdict :carried-not-released) "carried-not-released")
        ((equal verdict :issuer-not-released) "issuer-not-released")
        ((equal verdict :generation) "generation")
        ((equal verdict :not-a-receipt) "not-a-receipt")
        ((equal verdict :obligation-mismatch) "obligation-mismatch")
        ((equal verdict :workflow-refused) "workflow-refused")
        ((equal verdict :signed-issuer) "signed-issuer")
        ((equal verdict :signature-refused) "signature-refused")
        ((equal verdict :signature-required) "signature-required")
        (t "ingress")))

(defconst *fn-bpah-release-verdicts*
  '(:self-issued :listed-issuer :carried-not-released :issuer-not-released
    :generation :not-a-receipt :obligation-mismatch :workflow-refused
    :signed-issuer :signature-refused :signature-required :ingress))

(defun fn-bpah-release-verdict-of-name (name verdicts)
  (declare (xargs :guard t))
  (if (consp verdicts)
      (if (equal (fn-bpah-release-verdict-name (car verdicts)) name)
          (car verdicts)
        (fn-bpah-release-verdict-of-name name (cdr verdicts)))
    nil))

; The kind-7 delivery detail of a receipt: "release=<verdict>" as octets.
; With the kind-5 row's ingress (received from R, at generation G) and the
; bundle's source (claimed S) it is the durable provenance of the receipt.
(defun fn-bpah-release-detail (verdict)
  (declare (xargs :guard t))
  (fn-record-string-octets
   (string-append "release=" (fn-bpah-release-verdict-name verdict))))

; The line the host prints for a receipt, before its gate.
(defun fn-bpah-release-line (view cfg)
  (declare (xargs :guard t))
  (let ((carrier (fn-bpah-view-carrier view))
        (issuer (fn-bpn-nth 6 view)))
    (string-append
     (fn-bpah-release-verdict-name (fn-bpah-release-issuer-verdict view cfg))
     (string-append
      " carrier="
      (string-append
       (fn-record-octets-string carrier)
       (string-append " issuer=" (if (stringp issuer) issuer "")))))))

;; Durable provenance (D23): a reader of the FNBS journal tells apart the
;; four facts of a delivered item from its held row alone.  R and G are the
;; kind-5 ingress stamp; S is the bundle's primary source; V is the kind-7
;; release detail for a receipt; P is the configuration row V names, of R's
;; boundary for S.  A request's kind-7 detail is its receipt id, so for a
;; request V and P are re-derived from R, G, S and the configuration record
;; of generation G (`fn-bpah-held-source-decision').

(defun fn-bpah-held-received-from (h)
  (declare (xargs :guard t))
  (let ((ingress (fn-bpn-nth 4 h)))
    (list :received-from
          (fn-bpaj-principal-id (fn-bpnf-ingress-principal ingress))
          (fn-bpaj-eid-text (fn-bpn-nth 3 ingress))
          (fn-bpn-nth 5 ingress))))

(defun fn-bpah-held-claimed-source (h)
  (declare (xargs :guard t))
  (let* ((bundle (fn-bpnf-held-bundle h))
         (primary (fn-bpb-bundle-primary bundle)))
    (fn-bpaj-source-eid
     (if (and (fn-bpb-bundlep bundle) (fn-bpp-blockp primary))
         (fn-bpaj-eid-text (fn-bpp-source primary))
       nil))))

(defun fn-bpah-held-verdict (h)
  (declare (xargs :guard t))
  (let* ((marker (fn-bpn-nth 10 h))
         (detail (fn-bpn-nth 2 marker)))
    (if (and (equal (fn-bpn-nth 0 marker) :delivered)
             (member-equal (fn-bpn-nth 1 marker)
                           '(:receipt-accepted :receipt-refused))
             (fn-cbor-octet-listp detail)
             (< 8 (len detail))
             (equal (take 8 detail) (fn-record-string-octets "release=")))
        (fn-bpah-release-verdict-of-name
         (fn-record-octets-string (nthcdr 8 detail))
         *fn-bpah-release-verdicts*)
      nil)))

(defun fn-bpah-held-policy-row (h)
  (declare (xargs :guard t))
  (let ((verdict (fn-bpah-held-verdict h))
        (name (fn-record-octets-string
               (fn-bpnf-ingress-principal (fn-bpn-nth 4 h))))
        (source (fn-bpaj-tagged-value (fn-bpah-held-claimed-source h))))
    (cond ((equal verdict :self-issued)
           (fn-cfg-row-make name "transport-bp" source 0))
          ((equal verdict :listed-issuer)
           (fn-cfg-row-make name "bp-boundary-releases-for" source 0))
          (t nil))))

(defun fn-bpah-held-source-decision (h cfg)
  (declare (xargs :guard t))
  (let ((ingress (fn-bpn-nth 4 h)))
    (fn-bpaj-carried-source-decision
     cfg (fn-bpnf-ingress-principal ingress) (fn-bpn-nth 5 ingress)
     (fn-bpaj-tagged-value (fn-bpah-held-claimed-source h)))))

; The line the host prints for every dispatched request or receipt: ACL2's
; decision, its principal(s) as configured names, or its refusal reason.
(defun fn-bpah-source-decision-line (view cfg)
  (declare (xargs :guard t))
  (let ((d (fn-bpah-view-source-decision view cfg)))
    (cond ((equal (car d) :direct)
           (string-append "direct principal="
                          (fn-record-octets-string (fn-bpn-nth 1 d))))
          ((equal (car d) :carried)
           (string-append
            "carried carrier="
            (string-append
             (fn-record-octets-string (fn-bpn-nth 1 d))
             (string-append " author="
                            (fn-record-octets-string (fn-bpn-nth 2 d))))))
          (t (string-append
              "refused reason="
              (let ((r (fn-bpn-nth 1 d)))
                (cond ((equal r :generation) "generation")
                      ((equal r :source-not-carried) "source-not-carried")
                      ((equal r :carried-source-unenrolled)
                       "carried-source-unenrolled")
                      (t "ingress"))))))))

; The owed handoff is an application obligation, not TCPCL custody evidence.
; Bind it back to the exact delivered held request before the host asks FNRJ
; for the durable receipt ADU and enqueues a return bundle.
(defun fn-bpah-outbox-work-id (rid arrival)
  (declare (xargs :guard t))
  (fn-bpn-append
   (fn-record-string-octets "bp-receipt:")
   (fn-bpn-append
    rid (cons 58
              (fn-record-string-octets
               (fn-prov-nat-string arrival))))))

(defun fn-bpah-outbox-view-for (st handoff)
  (declare (xargs :guard t))
  (let* ((key (fn-bpn-nth 2 handoff))
         (held (fn-bpnf-find-held key (fn-bpnf-held-list st)))
         (bundle (fn-bpnf-held-bundle held))
         (primary (fn-bpb-bundle-primary bundle)))
    (if (and (fn-bpnf-handoffp handoff)
             (equal (fn-bpn-nth 3 handoff) :owed)
             (fn-bpnf-heldp held)
             (fn-bpb-bundlep bundle)
             (fn-bpp-blockp primary)
             (equal (fn-bpah-held-class held) :request)
             (equal (fn-bpn-nth 12 held) '(:dispatch-done))
             (member-equal (fn-bpn-nth 1 (fn-bpn-nth 10 held))
                           '(:request-accepted :request-duplicate
                             :request-returned))
             (equal (fn-bpn-nth 10 held)
                    (list :delivered
                          (fn-bpn-nth 1 (fn-bpn-nth 10 held))
                          (fn-bpn-nth 1 handoff)))
             (fn-frame-textp (fn-bpn-nth 1 handoff)))
        (list :outbox (fn-bpn-nth 1 handoff) key
              (fn-bpb-payload bundle)
              (fn-bpaj-eid-text (fn-bpp-source primary))
              (fn-bpah-outbox-work-id (fn-bpn-nth 1 handoff)
                                      (fn-bpn-nth 3 held))
              (fn-record-string-octets "return")
              0)
      nil)))

(defun fn-bpah-select-owed (st handoffs)
  (declare (xargs :guard t))
  (if (atom handoffs)
      nil
    (or (fn-bpah-outbox-view-for st (car handoffs))
        (fn-bpah-select-owed st (cdr handoffs)))))

(defun fn-bpah-select-owed-after (st handoffs after)
  (declare (xargs :guard t))
  (if (atom handoffs)
      nil
    (if (equal (fn-bpn-nth 2 (car handoffs)) after)
        (fn-bpah-select-owed st (cdr handoffs))
      (fn-bpah-select-owed-after st (cdr handoffs) after))))

(defun fn-bpah-outbox-view-after (st after)
  (declare (xargs :guard t))
  (if after
      (fn-bpah-select-owed-after st (fn-bpnf-handoffs st) after)
    (fn-bpah-select-owed st (fn-bpnf-handoffs st))))

(defun fn-bpah-outbox-view (st)
  (declare (xargs :guard t))
  (fn-bpah-outbox-view-after st nil))

(defun fn-bpah-outbox-peer-matchp (view configured-peer)
  (declare (xargs :guard t))
  (and (equal (fn-bpn-nth 0 view) :outbox)
       (stringp configured-peer)
       (equal (fn-bpn-nth 4 view) configured-peer)))

(defun fn-bpah-outbox-job-matchp (st view receipt-adu peer)
  (declare (xargs :guard t))
  (let ((job (fn-bpn-find-job
              (list (fn-bpn-nth 5 view) (fn-bpn-nth 6 view)
                    (fn-bpn-nth 7 view))
              (fn-bpn-machine-state-jobs (fn-bpnf-base st)))))
    (and (equal (fn-bpn-nth 0 view) :outbox)
         (fn-bpn-jobp job)
         (equal (fn-bpn-job-peer job) peer)
         ;; The return job carries FNRJ's exact receipt ADU, bare or under
         ;; the issuer's signature (hedged ML-DSA-65: a re-signed receipt
         ;; has other signature bytes, the same ADU).
         (equal (fn-bpsr-adu-octets (fn-bpb-payload (fn-bpn-job-bundle job)))
                receipt-adu))))

(defthm fn-bpah-no-held-no-delivery
  (equal (fn-bpah-pending-view
          (fn-bpnf-state base nil outcomes handoffs correlation issued waits
                         epoch next-op)
          node)
         nil))

; The receipt gate is the release question's issuer half: without it no
; receipt is trusted, whatever the carried list says.
(defthm fn-bpah-unauthorized-issuer-never-authorizes-receipt
  (implies (not (fn-bpah-release-issuer-authorizedp
                 cfg (fn-bpah-view-carrier view)
                 (fn-bpah-view-generation view)
                 (fn-bpaj-issuer-eid (fn-bpn-nth 6 view))))
           (not (fn-bpah-receipt-trustedp view cfg)))
  :hints (("Goal" :in-theory (e/d (fn-bpah-receipt-trustedp)
                                  (fn-bpah-release-issuer-authorizedp
                                   fn-bpah-view-receipt)))))

(defthm fn-bpah-untrusted-source-never-authorizes-request
  (implies (not (fn-bpaj-source-decision-trustedp
                 (fn-bpah-view-source-decision view cfg)))
           (not (fn-bpah-request-trustedp view cfg)))
  :hints (("Goal" :in-theory (e/d (fn-bpah-request-trustedp)
                                  (fn-bpah-view-source-decision
                                   fn-bpaj-source-decision-trustedp)))))
