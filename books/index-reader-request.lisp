; Registered producer request vocabulary and its actual range controller.
; Internal functions only. Public entry takes an issued request token, never
; source refs, effects, resource operands or a prepared controller.
(in-package "ACL2")
(logic)
(include-book "index-query-slot-issuer")
(include-book "index-backing-generations")
(include-book "index-range-controller")

(defun fn-irr-receipt-request (receipt)
 (declare (xargs :guard t)) (fn-omk-at 6 receipt))
(defun fn-irr-receipt-committedp (receipt)
 (declare (xargs :guard t))
 (and (equal (fn-omk-at 0 receipt) :index-request-receipt)
      (equal (fn-omk-at 7 receipt) :committed)))
(defun fn-irr-receipt-step (receipt)
 (declare (xargs :guard t))
 (if (fn-irr-receipt-committedp receipt) (fn-omk-at 8 receipt) nil))
(defun fn-irr-request-effects (request)
 (declare (xargs :guard t)) (fn-omk-at 6 request))
(defun fn-irr-request-rc (request)
 (declare (xargs :guard t)) (fn-omk-at 5 request))
(defun fn-irr-request-pin (request)
 (declare (xargs :guard t)) (fn-omk-at 2 request))
(defun fn-irr-request-publication (request)
 (declare (xargs :guard t)) (fn-omk-at 3 request))
(defun fn-irr-request-origin (request)
 (declare (xargs :guard t)) (fn-omk-at 7 request))

; Token-only read of the actual current pending receipt. After adoption the
; index resource driver reads the same receipt from registered context8.
; A reserved receipt is not a committed response and cannot expose its step.
(defun fn-irr-pending-read (token fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (request (fn-irr-receipt-request receipt))
        (ordinal (fn-omk-at 3 receipt))
        (nonce (fn-omk-at 2 receipt))
        (generation (fn-ipub-generation (fn-irr-request-publication request))))
  (if (not (and (fn-ibp-query-tokenp token) (natp ordinal)
                (posp nonce) (posp generation)
                (equal token (fn-irq-candidate-token nonce ordinal generation))))
      (mv :stale nil)
    (if (fn-irr-receipt-committedp receipt) (mv :committed receipt)
      (mv :pending nil)))))

; Called after the exact registered query grant has been admitted. Generation
; and immutable effects/pin are projections of the retained producer request.
(defun fn-irr-range-control (receipt resource)
 (declare (xargs :guard t))
 (let ((request (fn-irr-receipt-request receipt)))
  (fn-ibr-begin (fn-omk-at 2 receipt)
    (fn-ipub-generation (fn-irr-request-publication request))
    (fn-irr-request-effects request) (fn-irr-request-pin request)
    resource (fn-irr-request-origin request))))

; Provider context slot5 is the exact registered payload token used by the
; existing SAMEpool resource driver. Other fields retain the original request
; refs/receipt; no byte, root or effect list is copied.
(defun fn-irr-query-context (receipt payload)
 (declare (xargs :guard t))
 (let ((request (fn-irr-receipt-request receipt)))
  (list :reader-context (fn-omk-at 1 request) (fn-omk-at 2 request)
        (fn-omk-at 3 request) (fn-omk-at 4 request) payload
        (fn-irr-request-effects request) (fn-irr-request-origin request) receipt)))

; Read-only bounded descent to the SAME live registered context.
(defun fn-irr-node-context-read (token fuel slot depth fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :measure (nfix depth)
                  :guard (and (fn-ibp-query-tokenp token) (natp fuel)
                              (natp slot) (natp depth)) :verify-guards nil))
  (cond ((<= fuel depth) (mv :yield nil fuel))
        ((zp depth) (if (not (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node))
        (mv :unavailable nil fuel)
      (stobj-let ((fn-ibp-query-segment
                   (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                             (create-fn-ibp-query-segment))))
        (status context)
        (if (fn-ibp-query-slot-livep token fn-ibp-query-segment)
            (let ((local-slot (nth 3 token)))
              (mv :live (fn-ibp-qs-inputsi local-slot fn-ibp-query-segment)))
          (mv :stale nil))
        (mv status context (- fuel 1)))))
        ((equal (mod slot 2) 0) (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable nil fuel)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
        (status context fuel-left)
        (fn-irr-node-context-read token (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-left)
        (mv status context fuel-left))))
        (t (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable nil fuel)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
        (status context fuel-left)
        (fn-irr-node-context-read token (- fuel 1) (floor slot 2) (- depth 1) fn-ibp-node-right)
        (mv status context fuel-left))))))
(verify-guards fn-irr-node-context-read)

; Checks bounded scalar correspondence of the retained committed request.
; The registered publisher still owns the immutable root/object association;
; these scalar checks do not manufacture source authority from a tuple.
(defun fn-irr-context-matchesp (token capture context)
 (declare (xargs :guard t))
 (let* ((receipt (fn-omk-at 8 context))
        (request (fn-irr-receipt-request receipt))
        (publication (fn-irr-request-publication request)))
  (and (equal (fn-omk-at 0 context) :reader-context)
       (fn-irr-receipt-committedp receipt)
       (equal (fn-omk-at 2 receipt) (fn-omk-at 1 token))
       (equal (fn-ipub-generation publication) (fn-omk-at 4 token))
       (equal (fn-ipub-generation publication) (fn-ibp-capture-generation capture))
       (equal (fn-ipub-count publication) (fn-ibp-capture-count capture))
       (equal (fn-ipub-frontier publication) (fn-ibp-capture-frontier capture))
       (equal (fn-ipub-table-id publication) (fn-ibp-capture-table-root-id capture))
       (equal (fn-ipub-row-id publication) (fn-ibp-capture-row-root-id capture)))))

; Reads registered control only after BOTH the current slot's exact active
; query claim and the same indexed payload row authorize it. No control,
; grant, plan or source object is accepted from the host.
(defun fn-irr-node-render-control (token fuel slot depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node
                 :guard (and (fn-ibp-query-tokenp token) (natp fuel)
                             (natp slot) (natp depth)) :verify-guards nil))
 (mv-let (word payload grant left)
   (fn-ibp-node-query-authorization token fuel slot depth fn-ibp-node)
   (if (not (and (eq word :authorized) (fn-qpg-tokenp payload)
                 (fn-iqr-tokenp grant) (natp left)))
       (mv (if (eq word :authorized) :recovery-required word) nil left)
     (mv-let (payload-word unused-payload unused-grant after-payload)
       (fn-ibp-node-payload-live payload grant left slot depth fn-ibp-node)
       (declare (ignore unused-payload unused-grant))
       (if (not (and (eq payload-word :authorized) (natp after-payload)))
           (mv (if (eq payload-word :authorized) :recovery-required payload-word) nil after-payload)
         (mv-let (read-word control capture borrow after-read)
           (fn-ibp-node-query-read token after-payload slot depth fn-ibp-node)
           (declare (ignore borrow))
           (if (not (eq read-word :live)) (mv read-word nil after-read)
             (mv-let (context-word context after-context)
               (fn-irr-node-context-read token after-read slot depth fn-ibp-node)
              (if (not (eq context-word :live)) (mv context-word nil after-context)
               (if (and (fn-irr-context-matchesp token capture context)
                        (fn-ibp-control-kindp :range control)
                      (equal (fn-omk-at 1 control) (nth 1 token))
                      (equal (fn-omk-at 2 control) (nth 4 token))
                      (equal (fn-spp-resource (fn-omk-at 4 control)) grant))
                 (mv :authorized control after-context)
               (mv :recovery-required nil after-context)))))))))))
(verify-guards fn-irr-node-render-control)

(defun fn-irr-render-install (token fuel fn-mio$c fn-render-holder)
 (declare (xargs :stobjs (fn-mio$c fn-render-holder) :guard (natp fuel)))
 (cond ((fn-rh-live fn-render-holder) (mv :busy fuel fn-mio$c fn-render-holder))
       ((not (fn-ibp-query-tokenp token)) (mv :stale fuel fn-mio$c fn-render-holder))
       (t
        (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
          (word control left)
          (let ((depth (fn-ibp-slot-depth fn-index-backing)))
           (if (>= (1- (nth 2 token)) (fn-ibp-pool-capacity fn-index-backing))
               (mv :stale nil fuel)
             (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
               (word control left)
               (fn-irr-node-render-control token fuel (1- (nth 2 token)) depth fn-ibp-node)
               (mv word control left))))
          (if (not (eq word :authorized)) (mv word left fn-mio$c fn-render-holder)
            (mv-let (installed fn-render-holder)
              (fn-ibr-render-install control fn-render-holder)
              (mv installed left fn-mio$c fn-render-holder)))))))
