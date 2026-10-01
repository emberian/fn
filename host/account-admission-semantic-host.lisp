; First actual private-account E continuation. All semantic inputs are read
; from registered internal BEGIN/NODE holders under the same serialized owner
; span. Native callers cannot supply a node, CP, effect or full decision.
; High host assembly remains unadmitted until its modern include basis joins.
(in-package "ACL2")
(include-book "admission-semantic-node-host")
(include-book "../books/consumer-account-operation-state")
(include-book "../books/consumer-account-carries-state")
(include-book "../books/consumer-account-state")
(include-book "../books/consumer-account-transaction-driver")
(include-book "../books/consumer-configured-authority-finish")
(include-book "../books/consumer-account-config-row-carry")

; Capture happens immediately after the real reserved BEGIN retained its old
; Store/config/view, before node staging. It borrows the old account root at
; that point, never a current root read after a yielding semantic step.
(defun fn-owner-admission-account-capture (state)
 (declare (xargs :stobjs state :mode :program :guard t))
 (let* ((current (fn-apr-owner-current state)) (token (fn-prl-nth 0 current))
        (intent (and (boundp-global 'fn-owner-canonical-admission-executor state)
                     (f-get-global 'fn-owner-canonical-admission-executor state)))
        (source (and (boundp-global 'fn-owner-history-semantic-source state)
                     (f-get-global 'fn-owner-history-semantic-source state)))
        (reader (and (boundp-global 'fn-owner-history-semantic-reader-base state)
                     (f-get-global 'fn-owner-history-semantic-reader-base state)))
        (selection (fn-owner-account-adoption-operation state))
        (one (fn-prl-nth 3 selection)) (row (fn-cp-nth 1 one))
        (base (fn-prl-nth 5 intent)) (canonical (fn-prl-nth 6 intent))
        (cp (fn-sn-consumer base)) (metadata (fn-owner-account-carries-read state))
        (authority (fn-cp-nth 6 cp)) (job (fn-prl-nth 4 selection))
        (view (fn-prl-nth 2 reader)) (root (fn-owner-account-root-state state))
        (prior (and (boundp-global 'fn-owner-history-account-capture state)
                    (f-get-global 'fn-owner-history-account-capture state))))
  (cond
   (prior (mv :account-capture-busy state))
   ((not (and (fn-apr-tokenp token) (fn-apr-livep token current)
               (eq (fn-prl-nth 2 current) :reserved)
               (eq (fn-owner-history-writer-gate token state) :writer-current)
               (fn-apr-widthp 8 intent) (eq (fn-prl-nth 0 intent) :admission-prepare-intent)
               (equal token (fn-prl-nth 1 intent))
               (fn-apr-widthp 4 source) (eq (fn-prl-nth 0 source) :history-semantic-source)
               (equal token (fn-prl-nth 1 source))
               (fn-apr-widthp 4 reader) (eq (fn-prl-nth 0 reader) :history-reader-base)
               (equal token (fn-prl-nth 1 reader))
               (fn-apr-widthp 14 selection)
               (eq (fn-prl-nth 0 selection) :account-adoption-operation)
               (eq (fn-cp-nth 0 one) :publish)
               (or (fn-cac-eventp row) (fn-cab-eventp row))
               (equal (fn-cp-nth 1 row) (fn-prl-nth 4 token))
               (equal (fn-cp-nth 2 row) (fn-prl-nth 5 token))
               (equal (fn-prl-nth 5 selection) (fn-prl-nth 2 intent))
               (equal (fn-prl-nth 7 selection) (fn-prl-nth 3 intent))
               (equal (fn-prl-nth 3 intent) (fn-prl-nth 3 token))
               (equal (fn-prl-nth 6 selection)
                      (fn-cfg-generation (fn-prl-nth 3 source)))
               (or (null (fn-prl-nth 10 selection))
                   (fn-cp-authority-namespacep (fn-prl-nth 10 selection)))
               (or (null (fn-cp-nth 3 authority))
                   (fn-cp-authority-namespacep (fn-cp-nth 3 authority)))
               (equal (fn-prl-nth 10 selection) (fn-cp-nth 3 authority))
               (equal (fn-prl-nth 11 selection) (fn-cp-nth 1 authority))
               (equal (fn-cp-nth 3 cp) (fn-cp-nth 1 row))
               (fn-apr-widthp 10 canonical) (eq (fn-prl-nth 0 canonical) :ready)
               (equal (fn-prl-nth 1 canonical) (fn-prl-nth 2 intent))
               (equal (fn-prl-nth 2 canonical) (fn-prl-nth 3 intent))
               (fn-apr-widthp 5 metadata) (eq (fn-prl-nth 0 metadata) :account-carries)
               ; Full alias/size correspondence is the installed producer
               ; invariant, not a new EQUAL of the shared CP or size graph.
               (or (fn-cra-availablep cp (fn-prl-nth 2 intent)
                                    (fn-prl-nth 3 intent) root)
                   (and (null (fn-cp-nth 4 authority)) (null root)))))
    (mv :account-source-unavailable state))
   (t
    (let* ((publication (list :ok cp (fn-cp-nth 5 root) (fn-cp-nth 4 root)))
           (seed (fn-capr-state
                  (fn-cnode-make (fn-sn-node base) (fn-prl-nth 3 source))
                  (fn-prl-nth 3 canonical) (fn-prl-nth 4 canonical)
                  cp metadata (fn-catd-preparation job) publication
                  (fn-cp-nth 11 job)
                  (fn-own-view-withdrawals view) (fn-own-view-archive view)
                  (fn-own-view-verdicts view)
                  ; E-only capture never invents a persisted C sequence from
                  ; generation. The separate typed-C producer owns that seed.
                  nil (fn-cp-nth 1 row) nil (list row) nil))
           (state (f-put-global 'fn-owner-history-account-capture
                    (list :history-account-capture token seed root selection) state)))
     (mv :account-source-retained state))))))

(defun fn-owner-admission-account-step (state)
 (declare (xargs :stobjs state :mode :program :guard t))
 (let* ((current (fn-apr-owner-current state)) (token (fn-prl-nth 0 current))
        (capture (and (boundp-global 'fn-owner-history-account-capture state)
                      (f-get-global 'fn-owner-history-account-capture state)))
        (prior (and (boundp-global 'fn-owner-history-account-state state)
                    (f-get-global 'fn-owner-history-account-state state))))
  (cond
   ((not (and (fn-apr-tokenp token) (fn-apr-livep token current)
               (fn-apr-widthp 5 capture)
               (eq (fn-prl-nth 0 capture) :history-account-capture)
               (equal token (fn-prl-nth 1 capture))
               (eq (fn-owner-history-writer-gate token state) :writer-current)))
    (mv :account-source-changed state))
   (prior
    (mv (if (and (fn-apr-widthp 5 prior)
                  (eq (fn-prl-nth 0 prior) :history-account-ready)
                  (equal token (fn-prl-nth 1 prior)))
             :account-ready :recovery-required) state))
   (t
    (mv-let (word row produced next-cn delta)
      (fn-owner-admission-node-result state)
     (declare (ignore delta))
     (let* ((seed (fn-prl-nth 2 capture)) (prep (fn-cp-nth 6 seed)))
      (cond
       ((not (eq word :node-ready)) (mv :node-unavailable state))
       ; Both private authority grammars have bounded complete record size.
       ; This ties the real node decision to the saved selected event; it is
       ; not an equality of history, CP, metadata, or credential-table graphs.
       ((not (and (or (fn-cac-eventp row) (fn-cab-eventp row))
                   (equal row (fn-cp-nth 0 (fn-cp-nth 15 seed)))))
        (mv :account-selected-event-changed state))
       ; The selected CFG row is a fixed spine of scalar fields. Its actual
       ; size constructor reads string lengths, never string octets or a
       ; shared tree. Reject a corrupted source leaf before reconstruction.
       ((and (eq (fn-cp-nth 4 prep) :scan) (consp (fn-cp-nth 11 prep))
             (not (fn-bcpr-row-domainp (car (fn-cp-nth 11 prep)))))
        (mv :configuration-row-source-unavailable state))
       (t
        (let* ((rowcarry (and (eq (fn-cp-nth 4 prep) :scan)
                             (consp (fn-cp-nth 11 prep))
                             (fn-bcpr-row-carry (car (fn-cp-nth 11 prep)))))
               (state (f-put-global 'fn-owner-history-account-state
                       (list :history-account-intent token) state))
               (result (fn-cape-authority-finish seed produced next-cn
                         (fn-cnode-config (fn-cp-nth 1 seed)) rowcarry
                         (fn-prl-nth 3 token))))
         (if (eq (fn-cp-nth 0 result) :advanced)
             (let ((state (f-put-global 'fn-owner-history-account-state
                            (list :history-account-ready token
                                  (fn-cp-nth 1 result) (fn-cp-nth 2 result)
                                  (fn-prl-nth 3 capture)) state)))
              (mv :account-ready state))
           (let ((state (f-put-global 'fn-owner-history-account-state nil state)))
            (mv (fn-cp-nth 0 result) state))))))))))))

; Readonly current source gate. This returns the once-produced complete full7
; and the BEGIN root alias. No shape-only setter or deep graph comparison.
(defun fn-owner-admission-account-result (state)
 (declare (xargs :stobjs state :guard t))
 (let* ((current (fn-apr-owner-current state)) (token (fn-prl-nth 0 current))
        (result (and (boundp-global 'fn-owner-history-account-state state)
                     (f-get-global 'fn-owner-history-account-state state))))
  (if (and (fn-apr-tokenp token) (fn-apr-livep token current)
           (fn-apr-widthp 5 result) (eq (fn-prl-nth 0 result) :history-account-ready)
           (fn-apr-tokenp (fn-prl-nth 1 result))
           (equal token (fn-prl-nth 1 result))
           (eq (fn-owner-history-writer-gate token state) :writer-current))
      (mv :account-ready (fn-prl-nth 2 result) (fn-prl-nth 3 result)
          (fn-prl-nth 4 result))
    (mv :unavailable nil nil nil))))
