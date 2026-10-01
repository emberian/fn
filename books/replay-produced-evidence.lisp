; One actual sized STXE parse retained for replay binding consumers.
; This carrier borrows the selected wire event/octet lists; it does not copy them.
; The outer owner continuation retains ORIGINAL context/raw-event/epoch identity.
; Producer work/encode allocations belong to the pending executor, not this guard.
(in-package "ACL2")
(include-book "replay-identity-effects")
(include-book "stx-evidence-size-reader")

(defun fn-rpe-event (evidence) (declare (xargs :guard t)) (fn-cbor-ag-car (fn-cbor-ag-cdr evidence)))
(defun fn-rpe-octets (evidence) (declare (xargs :guard t)) (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr evidence))))
(defun fn-rpe-result (evidence) (declare (xargs :guard t)) (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr evidence)))))
(defun fn-rpe-lengths (evidence) (declare (xargs :guard t)) (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr evidence))))))
(defun fn-rpe-typedp (evidence) (declare (xargs :guard t)) (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr evidence)))))))
(defun fn-rpe-canonicalp (evidence) (declare (xargs :guard t)) (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr evidence))))))))

(defun fn-rpe-produce (event)
  (declare (xargs :guard t))
  (let ((octets (fn-stxa-verdict-event event)))
    (mv-let (result sizes) (fn-stxs-decode octets)
      (let* ((child (fn-stmt-value result))
             (typed (and (fn-stmt-okp result) (fn-stxe-p child)))
             (canonical (and typed (equal (fn-stxe-encode child) octets))))
        (list :stxe-produced event octets result sizes typed canonical)))))

; Logical provenance only. Never used as a served guard or runtime reparse.
(defun fn-rpe-originp (event evidence)
  (declare (xargs :guard t))
  (equal evidence (fn-rpe-produce event)))

(defthm fn-rpe-producer-retains-exact-event-and-parser-values
  (let ((evidence (fn-rpe-produce event)))
    (and (equal (fn-rpe-event evidence) event)
         (equal (fn-rpe-octets evidence) (fn-stxa-verdict-event event))
         (equal (fn-rpe-result evidence)
                (mv-nth 0 (fn-stxs-decode (fn-stxa-verdict-event event))))
         (equal (fn-rpe-lengths evidence)
                (mv-nth 1 (fn-stxs-decode (fn-stxa-verdict-event event))))))
  :hints (("Goal" :in-theory (e/d (fn-cbor-ag-car fn-cbor-ag-cdr fn-rpe-produce fn-rpe-event fn-rpe-octets
                                 fn-rpe-result fn-rpe-lengths)
                                (fn-stxs-decode fn-stxe-p fn-stxe-encode)))))

(defthm fn-rpe-success-lengths-are-actual-typed-child-lengths
  (implies (fn-stmt-okp (fn-rpe-result (fn-rpe-produce event)))
    (equal (fn-rpe-lengths (fn-rpe-produce event))
      (let ((child (fn-stmt-value (fn-rpe-result (fn-rpe-produce event)))))
        (list (length (fn-stxe-msgid child))
              (len (fn-stxe-detail child)) (len (fn-stxe-profile child))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stxs-success-byte-lengths-correspond
                          (octets (fn-stxa-verdict-event event))))
                   :in-theory (e/d (fn-cbor-ag-car fn-cbor-ag-cdr fn-rpe-produce fn-rpe-result fn-rpe-lengths)
                        (fn-stxs-decode fn-stmt-okp fn-stmt-value fn-stxe-p
                         fn-stxe-encode length len fn-stxe-msgid fn-stxe-detail fn-stxe-profile)))))

(defun fn-rpe-stxa-bindsp (evidence)
  (declare (xargs :guard t))
  (let ((e (fn-rpe-event evidence)))
  (and
   (fn-stxa-p e)
   (let* ((rr (fn-record-decode-exact (fn-stxa-article-record e)))
          (vr (fn-rpe-result evidence)))
     (and (fn-record-result-okp rr)
          (fn-stmt-okp vr)
          (let ((record (fn-record-result-record rr))
                (verdict (fn-stmt-value vr)))
            (and (fn-record-p record)
                 (fn-rpe-typedp evidence)
                 (equal (fn-record-encode record)
                        (fn-stxa-article-record e))
                 (fn-rpe-canonicalp evidence)
                 (equal (fn-stxa-sequence e) (fn-record-sequence record))
                 (equal (fn-stxa-sequence e) (fn-stxe-sequence verdict))
                 (equal (fn-stxa-txid e) (fn-record-txid record))
                 (equal (fn-stxa-txid e) (fn-stxe-txid verdict))
                 (equal (fn-stxa-generation e)
                        (fn-record-generation record))
                 (equal (fn-stxa-generation e)
                        (fn-stxe-generation verdict))
                 (equal (fn-record-msgid record) (fn-stxe-msgid verdict))
                 (equal (fn-stxa-keyring-generation e)
                        (fn-stxe-keyring-generation verdict))
                 (equal (fn-stxa-profile e) (fn-stxe-profile verdict))
                 (equal (fn-stxa-content-subject e)
                        (fn-record-string-octets
                         (fn-record-content-subject record))))))))))

(defun fn-rpe-carried-bindsp (evidence)
  (declare (xargs :guard t))
  (let ((event (fn-rpe-event evidence)))
  (if (not (and (fn-stxa-p event)
                (equal (fn-stxa-schema event) *fn-stxa-carried-version*)
                (equal (fn-stxa-keyring-generation event) 0)
                (equal (fn-stxa-profile event)
                       (fn-hsig-evidence-tag (fn-stxa-authored-source event)))))
      nil
    (let* ((article (fn-record-decode-exact (fn-stxa-article-record event)))
           (verdict (fn-rpe-result evidence))
           (received (and (fn-record-result-okp article)
                          (fn-record-payload (fn-record-result-record article))))
           (plan (fn-hc-received-plan received)))
      (and (fn-rpe-stxa-bindsp evidence)
           (fn-record-result-okp article)
           (fn-hsig-carried-record-metadatap
            (fn-stxa-authored-source event) received
            (fn-record-result-record article))
           (fn-hc-okp plan)
           (true-listp (fn-hc-value plan))
           (equal (len (fn-hc-value plan)) 2)
           (let ((carrier (cadr (fn-hc-value plan))))
             (and (true-listp carrier) (equal (len carrier) 3)
                  (equal (car (fn-hc-value plan))
                         (fn-stxa-authored-source event))
                  (equal (fn-stxa-authored-id event)
                         (fn-hsig-authored-source-id
                          (fn-stxa-authored-source event)))
                  (fn-hsig-exact-octets-p (first carrier) 32)
                  (fn-stmt-okp verdict)
                  (equal (fn-stxe-token (fn-stmt-value verdict)) :carried)
                  (equal (fn-stxe-detail (fn-stmt-value verdict))
                         (first carrier)))))))))

(defun fn-rpe-revoked-bindsp (evidence)
  (declare (xargs :guard t))
  (let ((event (fn-rpe-event evidence)))
  (if (not (and (fn-stxa-p event)
                (equal (fn-stxa-schema event) *fn-stxa-carried-version*)
                (posp (fn-stxa-keyring-generation event))
                (equal (fn-stxa-profile event)
                       (fn-hsig-evidence-tag (fn-stxa-authored-source event)))))
      nil
    (let* ((article (fn-record-decode-exact (fn-stxa-article-record event)))
           (verdict (fn-rpe-result evidence))
           (received (and (fn-record-result-okp article)
                          (fn-record-payload (fn-record-result-record article))))
           (plan (fn-hc-received-plan received)))
      (and (fn-rpe-stxa-bindsp evidence)
           (fn-record-result-okp article)
           (fn-hsig-carried-record-metadatap
            (fn-stxa-authored-source event) received
            (fn-record-result-record article))
           (fn-hc-okp plan)
           (true-listp (fn-hc-value plan))
           (equal (len (fn-hc-value plan)) 2)
           (let ((carrier (cadr (fn-hc-value plan))))
             (and (true-listp carrier) (equal (len carrier) 3)
                  (equal (car (fn-hc-value plan))
                         (fn-stxa-authored-source event))
                  (equal (fn-stxa-authored-id event)
                         (fn-hsig-authored-source-id
                          (fn-stxa-authored-source event)))
                  (fn-hsig-exact-octets-p (first carrier) 32)
                  (fn-hsig-signatures-p (third carrier))
                  (fn-stmt-okp verdict)
                  (equal (fn-stxe-token (fn-stmt-value verdict)) :revoked)
                  (equal (fn-stxe-keyring-generation (fn-stmt-value verdict))
                         (fn-stxa-keyring-generation event))
                  (equal (fn-stxe-detail (fn-stmt-value verdict))
                         (first carrier)))))))))

(defun fn-rpe-snapshot-v0-bindsp (evidence snapshot)
  (declare (xargs :guard t))
  (let ((event (fn-rpe-event evidence)))
  (and (fn-stxa-p event)
       (equal (fn-stxa-authored-source event) :legacy)
       (fn-stxk-p snapshot)
       (equal (fn-stxa-keyring-generation event)
              (fn-stxk-keyring-generation snapshot))
       (equal (fn-stxa-profile event) *fn-hsig-profile-tag*)
       (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)
       (let ((key-items (fn-stmt-decode-items 5 (fn-stxk-snapshot snapshot)))
             (verdict (fn-rpe-result evidence)))
         (and (fn-stmt-okp key-items)
              (fn-stmt-okp verdict)
              (let* ((items (fn-stmt-value key-items))
                     (detail-items
                      (fn-stmt-decode-items
                       9 (fn-stxe-detail (fn-stmt-value verdict)))))
                (and (equal (fn-stxk-snapshot snapshot)
                            (fn-stxe-encode-items items))
                     (true-listp items) (equal (len items) 5)
                     (fn-stmt-bytes-item-p (nth 0 items))
                     (fn-hsig-exact-octets-p (cdr (nth 0 items)) 32)
                     (fn-stmt-uint-item-p (nth 1 items))
                     (equal (cdr (nth 1 items)) *fn-hsig-ed25519-algorithm*)
                     (fn-stmt-bytes-item-p (nth 2 items))
                     (fn-hsig-exact-octets-p
                      (cdr (nth 2 items)) *fn-hsig-ed25519-public-key-octets*)
                     (fn-stmt-uint-item-p (nth 3 items))
                     (equal (cdr (nth 3 items)) *fn-hsig-ml-dsa-65-algorithm*)
                     (fn-stmt-bytes-item-p (nth 4 items))
                     (fn-hsig-exact-octets-p
                      (cdr (nth 4 items)) *fn-hsig-ml-dsa-65-public-key-octets*)
                     (fn-stmt-okp detail-items)
                     (let ((details (fn-stmt-value detail-items)))
                       (and (equal (fn-stxe-detail (fn-stmt-value verdict))
                                   (fn-stxe-encode-items details))
                            (true-listp details) (equal (len details) 9)
                            (equal items (take 5 details))
                            (fn-stmt-uint-item-p (nth 5 details))
                            (equal (cdr (nth 5 details))
                                   *fn-hsig-ed25519-algorithm*)
                            (fn-stmt-bytes-item-p (nth 6 details))
                            (fn-hsig-exact-octets-p
                             (cdr (nth 6 details))
                             *fn-hsig-ed25519-signature-octets*)
                            (fn-stmt-uint-item-p (nth 7 details))
                            (equal (cdr (nth 7 details))
                                   *fn-hsig-ml-dsa-65-algorithm*)
                            (fn-stmt-bytes-item-p (nth 8 details))
                            (fn-hsig-exact-octets-p
                             (cdr (nth 8 details))
                             *fn-hsig-ml-dsa-65-signature-octets*))))))))))

(defun fn-rpe-snapshot-v1-bindsp (evidence snapshot)
  (declare (xargs :guard t))
  (let ((event (fn-rpe-event evidence)))
  (if (not (and (fn-stxa-p event)
                (fn-stxk-p snapshot)
                (equal (fn-stxa-schema event) *fn-stxa-carried-version*)
                (equal (fn-stxa-keyring-generation event)
                       (fn-stxk-keyring-generation snapshot))
                (equal (fn-stxa-profile event)
                       (fn-hsig-evidence-tag (fn-stxa-authored-source event)))
                (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)))
      nil
    (let* ((enrolled (fn-hsig-keyring-snapshot-value snapshot))
           (article (fn-record-decode-exact (fn-stxa-article-record event)))
           (verdict (fn-rpe-result evidence))
           (received (and (fn-record-result-okp article)
                          (fn-record-payload (fn-record-result-record article))))
           (plan (fn-hc-received-plan received)))
      (and (fn-rpe-stxa-bindsp evidence)
           (fn-record-result-okp article)
           (fn-hsig-carried-record-metadatap
            (fn-stxa-authored-source event) received
            (fn-record-result-record article))
           (true-listp enrolled) (equal (len enrolled) 2)
           (fn-hc-okp plan)
           (true-listp (fn-hc-value plan))
           (equal (len (fn-hc-value plan)) 2)
           (let ((carrier (cadr (fn-hc-value plan))))
             (and (true-listp carrier) (equal (len carrier) 3)
                  (equal (car (fn-hc-value plan))
                         (fn-stxa-authored-source event))
                  (equal (fn-stxa-authored-id event)
                         (fn-hsig-authored-source-id
                          (fn-stxa-authored-source event)))
                  (equal (first carrier) (first enrolled))
                  (equal (second carrier) (second enrolled))
                  (fn-hsig-signatures-p (third carrier))
                  (fn-stmt-okp verdict)
                  (equal (fn-stxe-token (fn-stmt-value verdict)) :verified)
                  (equal (fn-stxe-detail (fn-stmt-value verdict))
                         (first enrolled)))))))))

(defun fn-rpe-snapshot-bindsp (evidence snapshot)
  (declare (xargs :guard t))
  (if (equal (fn-stxa-schema (fn-rpe-event evidence)) *fn-stxa-carried-version*)
      (fn-rpe-snapshot-v1-bindsp evidence snapshot)
    (fn-rpe-snapshot-v0-bindsp evidence snapshot)))

(defthm fn-rpe-stxa-bindsp-refines-public
  (equal (fn-rpe-stxa-bindsp (fn-rpe-produce event)) (fn-stxa-bindsp event))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stxs-decode-ok-is-public (octets (fn-stxa-verdict-event event)))
             (:instance fn-stxs-decode-success-value-is-public (octets (fn-stxa-verdict-event event))))
    :in-theory (e/d (fn-cbor-ag-car fn-cbor-ag-cdr fn-rpe-stxa-bindsp fn-stxa-bindsp fn-rpe-produce fn-rpe-result fn-rpe-event fn-rpe-typedp fn-rpe-canonicalp)
       (fn-stxs-decode fn-stxe-decode-exact fn-stmt-okp fn-stmt-value
        fn-stxa-p fn-stxe-p fn-stxe-encode 
        fn-record-p fn-hc-received-plan
        fn-hsig-carried-record-metadatap fn-hsig-keyring-snapshot-value)))))

(defthm fn-rpe-carried-bindsp-refines-public
  (equal (fn-rpe-carried-bindsp (fn-rpe-produce event)) (fn-hsig-article-event-carried-bindsp event))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stxs-decode-ok-is-public (octets (fn-stxa-verdict-event event)))
             (:instance fn-stxs-decode-success-value-is-public (octets (fn-stxa-verdict-event event)))
             fn-rpe-stxa-bindsp-refines-public)
    :in-theory (e/d (fn-cbor-ag-car fn-cbor-ag-cdr fn-rpe-carried-bindsp fn-hsig-article-event-carried-bindsp fn-rpe-produce fn-rpe-result fn-rpe-event fn-rpe-typedp fn-rpe-canonicalp)
       (fn-stxs-decode fn-stxe-decode-exact fn-stmt-okp fn-stmt-value
        fn-stxa-p fn-stxe-p fn-stxe-encode 
        fn-record-p fn-rpe-stxa-bindsp fn-stxa-bindsp fn-hc-received-plan
        fn-hsig-carried-record-metadatap fn-hsig-keyring-snapshot-value)))))

(defthm fn-rpe-revoked-bindsp-refines-public
  (equal (fn-rpe-revoked-bindsp (fn-rpe-produce event)) (fn-hsig-article-event-revoked-bindsp event))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stxs-decode-ok-is-public (octets (fn-stxa-verdict-event event)))
             (:instance fn-stxs-decode-success-value-is-public (octets (fn-stxa-verdict-event event)))
             fn-rpe-stxa-bindsp-refines-public)
    :in-theory (e/d (fn-cbor-ag-car fn-cbor-ag-cdr fn-rpe-revoked-bindsp fn-hsig-article-event-revoked-bindsp fn-rpe-produce fn-rpe-result fn-rpe-event fn-rpe-typedp fn-rpe-canonicalp)
       (fn-stxs-decode fn-stxe-decode-exact fn-stmt-okp fn-stmt-value
        fn-stxa-p fn-stxe-p fn-stxe-encode 
        fn-record-p fn-rpe-stxa-bindsp fn-stxa-bindsp fn-hc-received-plan
        fn-hsig-carried-record-metadatap fn-hsig-keyring-snapshot-value)))))

(defthm fn-rpe-snapshot-v0-bindsp-refines-public
  (equal (fn-rpe-snapshot-v0-bindsp (fn-rpe-produce event) snapshot) (fn-hsig-article-event-snapshot-bindsp-v0 event snapshot))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stxs-decode-ok-is-public (octets (fn-stxa-verdict-event event)))
             (:instance fn-stxs-decode-success-value-is-public (octets (fn-stxa-verdict-event event)))
             fn-rpe-stxa-bindsp-refines-public)
    :in-theory (e/d (fn-cbor-ag-car fn-cbor-ag-cdr fn-rpe-snapshot-v0-bindsp fn-hsig-article-event-snapshot-bindsp-v0 fn-rpe-produce fn-rpe-result fn-rpe-event fn-rpe-typedp fn-rpe-canonicalp)
       (fn-stxs-decode fn-stxe-decode-exact fn-stmt-okp fn-stmt-value
        fn-stxa-p fn-stxe-p fn-stxe-encode 
        fn-record-p fn-rpe-stxa-bindsp fn-stxa-bindsp fn-hc-received-plan
        fn-hsig-carried-record-metadatap fn-hsig-keyring-snapshot-value)))))

(defthm fn-rpe-snapshot-v1-bindsp-refines-public
  (equal (fn-rpe-snapshot-v1-bindsp (fn-rpe-produce event) snapshot) (fn-hsig-article-event-snapshot-bindsp-v1 event snapshot))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stxs-decode-ok-is-public (octets (fn-stxa-verdict-event event)))
             (:instance fn-stxs-decode-success-value-is-public (octets (fn-stxa-verdict-event event)))
             fn-rpe-stxa-bindsp-refines-public)
    :in-theory (e/d (fn-cbor-ag-car fn-cbor-ag-cdr fn-rpe-snapshot-v1-bindsp fn-hsig-article-event-snapshot-bindsp-v1 fn-rpe-produce fn-rpe-result fn-rpe-event fn-rpe-typedp fn-rpe-canonicalp)
       (fn-stxs-decode fn-stxe-decode-exact fn-stmt-okp fn-stmt-value
        fn-stxa-p fn-stxe-p fn-stxe-encode 
        fn-record-p fn-rpe-stxa-bindsp fn-stxa-bindsp fn-hc-received-plan
        fn-hsig-carried-record-metadatap fn-hsig-keyring-snapshot-value)))))

(defthm fn-rpe-snapshot-bindsp-refines-public
  (equal (fn-rpe-snapshot-bindsp (fn-rpe-produce event) snapshot)
         (fn-hsig-article-event-snapshot-bindsp event snapshot))
  :rule-classes nil
  :hints (("Goal" :use (fn-rpe-snapshot-v0-bindsp-refines-public
                        fn-rpe-snapshot-v1-bindsp-refines-public)
    :in-theory (e/d (fn-rpe-snapshot-bindsp fn-hsig-article-event-snapshot-bindsp
                     fn-rpe-event fn-rpe-produce fn-cbor-ag-car fn-cbor-ag-cdr)
                    (fn-rpe-snapshot-v0-bindsp fn-rpe-snapshot-v1-bindsp
                     fn-hsig-article-event-snapshot-bindsp-v0
                     fn-hsig-article-event-snapshot-bindsp-v1 fn-stxs-decode
                     fn-stxe-p fn-stxe-encode)))))

; Pending executor: only the selected composite arm produces parser evidence.
(defun fn-rpe-verdict-effect (ctx child sizes)
 (declare (xargs :guard t))
 (mv ctx (if (equal (fn-stxk-context-kind ctx) :ok) :verdict :none)
     (if (equal (fn-stxk-context-kind ctx) :ok) child nil)
     (if (equal (fn-stxk-context-kind ctx) :ok) sizes nil)))

(defun fn-rpe-produced-effects (ctx event)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (equal (fn-stxk-context-kind ctx) :ok)) (mv ctx :none nil nil)
    (if (not (equal (fn-store-event-sequence event)
                    (fn-stxk-context-next ctx)))
        (mv (fn-stxk-fault ctx :sequence) :none nil nil)
     (let ((event (fn-replay-identity-wire event)))
      (cond
       ((fn-stxk-p event)
        (let* ((checked (fn-stxk-apply-snapshot ctx event))
               (changed (not (equal (fn-stxk-context-current-generation checked)
                                    (fn-stxk-context-current-generation ctx)))))
          (mv checked (if changed :snapshot :none) (if changed event nil) nil)))
       ((fn-stxe-p event)
        (let ((checked (fn-stxk-apply-verdict ctx event)))
          (mv (if (not (equal (fn-stxk-context-kind checked) :ok)) checked
                (fn-stxk-context :ok (fn-stxk-context-next checked)
                                 (fn-stxk-context-snapshots checked)
                                 (fn-stxk-context-verdicts ctx)
                                 (fn-stxk-context-current-generation checked) nil))
              :none nil nil)))
       (t
        (if (not (fn-stxa-p event))
            (mv (fn-replay-identity-advance ctx) :none nil nil)
          (let* ((evidence (fn-rpe-produce event))
                 (decoded (fn-rpe-result evidence))
                 (sizes (fn-rpe-lengths evidence))
                 (child (fn-stmt-value decoded)))
           (cond
            ((fn-rpe-carried-bindsp evidence)
             (fn-rpe-verdict-effect
              (fn-replay-apply-carried-verdict ctx child) child sizes))
            ((fn-rpe-revoked-bindsp evidence)
             (fn-rpe-verdict-effect
              (fn-replay-apply-revoked-verdict
               ctx child (fn-hsig-article-event-carrier-keys event)) child sizes))
            (t
             (let ((snapshot (fn-stxk-find (fn-stxa-keyring-generation event)
                                          (fn-stxk-context-snapshots ctx))))
              (if (or (not (fn-rpe-stxa-bindsp evidence)) (not snapshot)
                      (not (fn-rpe-snapshot-bindsp evidence snapshot)))
                  (mv (fn-stxk-fault ctx :composite-binding) :none nil nil)
                (if (not (fn-stmt-okp decoded))
                    (mv (fn-stxk-fault ctx :composite-verdict) :none nil nil)
                  (fn-rpe-verdict-effect (fn-stxk-apply-verdict ctx child)
                                         child sizes))))))))))))))
(verify-guards fn-rpe-produced-effects)
(defthm fn-rpe-produced-preserves-original-context-and-effects
 (and (equal (mv-nth 0 (fn-rpe-produced-effects ctx event))
             (mv-nth 0 (fn-replay-identity-effects ctx event)))
      (equal (mv-nth 1 (fn-rpe-produced-effects ctx event))
             (mv-nth 1 (fn-replay-identity-effects ctx event)))
      (equal (mv-nth 2 (fn-rpe-produced-effects ctx event))
             (mv-nth 2 (fn-replay-identity-effects ctx event))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-rpe-stxa-bindsp-refines-public
            (event (fn-replay-identity-wire event)))
        (:instance fn-rpe-carried-bindsp-refines-public
            (event (fn-replay-identity-wire event)))
        (:instance fn-rpe-revoked-bindsp-refines-public
            (event (fn-replay-identity-wire event)))
        (:instance fn-rpe-snapshot-bindsp-refines-public
            (event (fn-replay-identity-wire event))
            (snapshot (fn-stxk-find
              (fn-stxa-keyring-generation (fn-replay-identity-wire event))
              (fn-stxk-context-snapshots ctx))))(:instance fn-stxs-decode-ok-is-public
          (octets (fn-stxa-verdict-event (fn-replay-identity-wire event))))
        (:instance fn-stxs-decode-success-value-is-public
          (octets (fn-stxa-verdict-event (fn-replay-identity-wire event))))
        (:instance fn-hsig-article-event-carried-bindsp-facts
          (event (fn-replay-identity-wire event)))
        (:instance fn-hsig-article-event-revoked-bindsp-facts
          (event (fn-replay-identity-wire event))))
  :in-theory
   (e/d (fn-rpe-produced-effects fn-rpe-produce fn-rpe-result fn-rpe-lengths
         fn-cbor-ag-car fn-cbor-ag-cdr fn-replay-identity-effects
         fn-rpe-verdict-effect fn-replay-identity-verdict-effect)
        (fn-rpe-carried-bindsp fn-rpe-revoked-bindsp fn-rpe-stxa-bindsp
         fn-rpe-snapshot-bindsp fn-stxe-encode
         fn-replay-identity-wire fn-stxs-decode fn-stxe-decode-exact
         fn-stmt-okp fn-stmt-value fn-stxk-p fn-stxe-p fn-stxa-p
         fn-stxk-apply-snapshot fn-stxk-apply-verdict fn-stxk-find
         fn-stxa-bindsp fn-hsig-article-event-carried-bindsp
         fn-hsig-article-event-revoked-bindsp fn-hsig-article-event-snapshot-bindsp
         fn-replay-apply-carried-verdict fn-replay-apply-revoked-verdict)))))

(defthm fn-rpe-binding-consumers-require-parser-success
 (implies (or (fn-rpe-carried-bindsp evidence)
              (fn-rpe-revoked-bindsp evidence)
              (fn-rpe-snapshot-bindsp evidence snapshot))
          (fn-stmt-okp (fn-rpe-result evidence)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rpe-carried-bindsp fn-rpe-revoked-bindsp fn-rpe-snapshot-bindsp
        fn-rpe-snapshot-v0-bindsp fn-rpe-snapshot-v1-bindsp)
       (fn-rpe-result fn-rpe-event fn-stmt-okp fn-stmt-value
        fn-rpe-stxa-bindsp fn-hc-received-plan
        fn-hsig-keyring-snapshot-value fn-hsig-carried-record-metadatap)))))

(defthm fn-rpe-produced-verdict-lengths-are-actual
 (implies (equal (mv-nth 1 (fn-rpe-produced-effects ctx event)) :verdict)
  (let ((child (mv-nth 2 (fn-rpe-produced-effects ctx event))))
   (equal (mv-nth 3 (fn-rpe-produced-effects ctx event))
          (list (length (fn-stxe-msgid child))
                (len (fn-stxe-detail child)) (len (fn-stxe-profile child))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-rpe-success-lengths-are-actual-typed-child-lengths
          (event (fn-replay-identity-wire event)))
        (:instance fn-rpe-binding-consumers-require-parser-success
          (evidence (fn-rpe-produce (fn-replay-identity-wire event)))
          (snapshot (fn-stxk-find
           (fn-stxa-keyring-generation (fn-replay-identity-wire event))
           (fn-stxk-context-snapshots ctx)))))
  :in-theory (e/d (fn-rpe-produced-effects fn-rpe-verdict-effect)
   (fn-replay-identity-wire fn-rpe-produce fn-rpe-result fn-rpe-lengths
    fn-rpe-carried-bindsp fn-rpe-revoked-bindsp fn-rpe-stxa-bindsp
    fn-rpe-snapshot-bindsp fn-stmt-okp fn-stmt-value fn-stxk-p fn-stxe-p
    fn-stxa-p fn-stxk-apply-snapshot fn-stxk-apply-verdict fn-stxk-find
    fn-replay-apply-carried-verdict fn-replay-apply-revoked-verdict
    fn-stxe-msgid fn-stxe-detail fn-stxe-profile length len)))))

(defthm fn-rpe-nonverdict-has-no-child-lengths
 (implies (not (equal (mv-nth 1 (fn-rpe-produced-effects ctx event)) :verdict))
          (equal (mv-nth 3 (fn-rpe-produced-effects ctx event)) nil))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rpe-produced-effects fn-rpe-verdict-effect)
       (fn-rpe-produce fn-rpe-result fn-rpe-lengths
        fn-rpe-carried-bindsp fn-rpe-revoked-bindsp fn-rpe-stxa-bindsp
        fn-rpe-snapshot-bindsp fn-replay-identity-wire fn-stxk-p fn-stxe-p
        fn-stxa-p fn-stmt-okp fn-stmt-value fn-stxk-apply-snapshot
        fn-stxk-apply-verdict fn-stxk-find fn-replay-apply-carried-verdict
        fn-replay-apply-revoked-verdict)))))

(defthm fn-rpe-produced-complete-result-refines-public
 (equal (fn-rpe-produced-effects ctx event)
  (let* ((checked (mv-nth 0 (fn-replay-identity-effects ctx event)))
         (effect (mv-nth 1 (fn-replay-identity-effects ctx event)))
         (child (mv-nth 2 (fn-replay-identity-effects ctx event))))
   (list checked effect child
         (if (equal effect :verdict)
             (list (length (fn-stxe-msgid child))
                   (len (fn-stxe-detail child)) (len (fn-stxe-profile child)))
           nil))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-rpe-produced-preserves-original-context-and-effects
        fn-rpe-produced-verdict-lengths-are-actual
        fn-rpe-nonverdict-has-no-child-lengths)
  :in-theory (e/d (fn-rpe-produced-effects fn-rpe-verdict-effect)
   (fn-replay-identity-effects fn-rpe-produce fn-rpe-result fn-rpe-lengths
    fn-rpe-carried-bindsp fn-rpe-revoked-bindsp fn-rpe-stxa-bindsp
    fn-rpe-snapshot-bindsp fn-replay-identity-wire fn-stxk-p fn-stxe-p fn-stxa-p
    fn-stmt-okp fn-stmt-value fn-stxk-apply-snapshot fn-stxk-apply-verdict
    fn-stxk-find fn-replay-apply-carried-verdict fn-replay-apply-revoked-verdict
    fn-stxe-msgid fn-stxe-detail fn-stxe-profile length len)))))
