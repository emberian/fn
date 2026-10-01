; Actual pending request response/parser custody. Internal registered producers
; only: no host actor/root setter, category bitmap or supplied joined flag.
(in-package "ACL2")
(include-book "index-reader-request-shape")
(include-book "index-reader-request")



(defun fn-ira-pending-bind (token fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (request (fn-irr-receipt-request receipt))
        (nonce (fn-omk-at 2 receipt))
        (ordinal (fn-omk-at 3 receipt))
        (generation (fn-irq-receipt-request-generation receipt))
        (root (fn-ira-receipt-root receipt)))
  (cond
   ((not (and (posp nonce) (natp ordinal) (posp generation)
              (equal token (fn-irq-candidate-token nonce ordinal generation))))
    (mv :stale fn-index-backing))
   (root
    (if (and (fn-omk-widthp root 6)
             (eq (fn-omk-at 0 root) :reader-actor)
             (equal token (fn-omk-at 1 root))
             (equal (fn-irr-request-input-source request) (fn-omk-at 2 root))
             (member-eq (fn-omk-at 3 root) '(:parser-owned :response-owned)))
        (mv :actor-already-retained fn-index-backing)
      (mv :recovery-required fn-index-backing)))
   ((not (and (eq (fn-omk-at 7 receipt) :reserved)
              (fn-omk-widthp request 10)
              (fn-irr-request-input-source request)
              (null (fn-irr-request-rc request))))
    (mv :unavailable-actor fn-index-backing))
   (t
    (let* ((root (list :reader-actor token
                 (fn-irr-request-input-source request) :parser-owned request nil))
           (fn-index-backing
            (update-fn-ibp-request-pending
             (list (fn-omk-at 0 receipt) (fn-omk-at 1 receipt)
                   (fn-omk-at 2 receipt) (fn-omk-at 3 receipt)
                   (fn-omk-at 4 receipt) (fn-omk-at 5 receipt)
                   request (fn-omk-at 7 receipt) (fn-omk-at 8 receipt)
                   (fn-omk-at 9 receipt) root) fn-index-backing)))
     (mv :actor-retained fn-index-backing))))))

; Only the actual committed receipt can give the actor its RC/step pointers.
; Repetition observes the same root and never creates a second actor identity.
(defun fn-ira-pending-commit-response (token fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (request (fn-irr-receipt-request receipt))
        (root (fn-ira-receipt-root receipt)))
  (cond
   ((not (and (fn-irr-receipt-committedp receipt)
              (fn-omk-widthp root 6) (eq (fn-omk-at 0 root) :reader-actor)
              (equal token (fn-omk-at 1 root))
              (equal (fn-irr-request-input-source request) (fn-omk-at 2 root))))
    (mv :unavailable-actor fn-index-backing))
   ((eq (fn-omk-at 3 root) :response-owned)
    (mv :actor-already-retained fn-index-backing))
   ((not (eq (fn-omk-at 3 root) :parser-owned))
    (mv :recovery-required fn-index-backing))
   (t
    (let* ((next-root (list :reader-actor (fn-omk-at 1 root)
                     (fn-omk-at 2 root) :response-owned request
                     (fn-irr-receipt-step receipt)))
           (fn-index-backing
            (update-fn-ibp-request-pending
             (list (fn-omk-at 0 receipt) (fn-omk-at 1 receipt)
                   (fn-omk-at 2 receipt) (fn-omk-at 3 receipt)
                   (fn-omk-at 4 receipt) (fn-omk-at 5 receipt)
                   request (fn-omk-at 7 receipt) (fn-omk-at 8 receipt)
                   (fn-omk-at 9 receipt) next-root) fn-index-backing)))
     (mv :response-actor-retained fn-index-backing))))))
