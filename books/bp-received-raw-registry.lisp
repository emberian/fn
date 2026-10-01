; Registered raw TCPCL source, before decoded bundle/held constructors.
; Internal SAMEPRS/storage composition. Supplied-demand kernel is NOT a
; genuine operation-family installer; public native entry remains uninstalled.
(in-package "ACL2")
(include-book "bp-received-raw-source")
(include-book "tcpcl-received-source")
(include-book "page-read-ledger")
(set-verify-guards-eagerness 2)
(defstobj fn-bprx-tcpcl-controller
 (fn-bprtc-slot :type (integer 0 *) :initially 0)
 (fn-bprtc-nonce :type (integer 0 *) :initially 0)
 (fn-bprtc-session :initially nil)
 (fn-bprtc-revision :type (integer 0 *) :initially 0)
 (fn-bprtc-phase :initially :uninstalled)
 (fn-bprtc-claim :initially nil)
 (fn-bprtc-pending :initially nil)
 :inline t)
(defstobj fn-bprx-raw-registry
 (fn-bprr-sources :type fn-bprx-byte-node)
 (fn-bprr-controllers :type fn-bprx-byte-node)
 (fn-bprr-intent :initially nil)
 :inline t)
(set-verify-guards-eagerness 0)
(local (include-book "arithmetic-5/top" :dir :system))
(defun fn-bprr-at (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (fn-cbor-ag-car x) (fn-bprr-at (1- n) (fn-cbor-ag-cdr x))))
(defun fn-bprr-refp (ref)
 (declare (xargs :guard t))
 (and (consp ref) (eq (car ref) :bps-ref) (consp (cdr ref)) (natp (cadr ref)) (<= (cadr ref) 18446744073709551615)
      (consp (cddr ref)) (natp (caddr ref)) (<= (caddr ref) 18446744073709551615) (null (cdddr ref))))
; Source completion is exactly the second event of the actual completion
; producer, whose first event is the still-held END ACK. Never scan raw bytes.
(defun fn-bprr-completion (result)
 (declare (xargs :guard t))
 (let ((event (fn-bprr-at 1 (fn-tcl-result-events result))))
  (if (and (consp event) (eq (car event) :bundle-segments-received)
           (consp (cdr event)) (natp (cadr event))
           (consp (cddr event)) (consp (cdddr event)) (natp (cadddr event))
           (null (cddddr event))) event nil)))
; Core-only actual completion + SAMEPRS issue. Source identity and physical
; address are derived from NEXT, not from native ref/slot/nonce parameters.
; Reserve before source directory/holder/leaf constructors. Earlier native
; TCPCL buffer/spine constructors require their own enclosing family reserve.
(defun fn-bprr-prepare-completion (result owner demand ledger fn-bprx-raw-registry)
 (declare (xargs :stobjs fn-bprx-raw-registry :guard t :verify-guards nil))
 (let ((event (fn-bprr-completion result)))
  (cond ((fn-bprr-intent fn-bprx-raw-registry)
         (mv :source-busy nil ledger fn-bprx-raw-registry))
        ((not event) (mv :no-source-completion nil ledger fn-bprx-raw-registry))
        ((not (and (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
         (mv :invalid-source-demand nil ledger fn-bprx-raw-registry))
        ((not (and (natp (fn-prl-nth 2 ledger))
                   (<= (fn-prl-nth 2 ledger) 18446744073709551615)
                   (<= (cadddr event) 18446744073709551615)))
         (mv :source-format-exhausted nil ledger fn-bprx-raw-registry))
        (t
         (let ((next (fn-prl-nth 2 ledger)))
          (mv-let (word issued charged)
           (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
             '(0 0 0 0 0) (fn-prl-nth 1 ledger) next
             (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
           (if (not (eq word :admitted)) (mv word nil ledger fn-bprx-raw-registry)
            (let* ((ref (list :bps-ref next next))
                   (ledger (fn-prl-build (fn-prl-nth 0 ledger) charged issued
                             (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)))
                   (fn-bprx-raw-registry
                    (update-fn-bprr-intent
                     (list :raw-source-intent ref owner (cadr event) (caddr event)
                           (cadddr event) demand :reserved) fn-bprx-raw-registry)))
             (mv :source-reserved ref ledger fn-bprx-raw-registry)))))))))
; Actual caller composition: RESULT is computed here, not supplied by native.
; UNHOOKED until genuine receive family has reserved original TCPCL work.
(defun fn-bprr-receive-step (session message now owner demand ledger fn-bprx-raw-registry)
 (declare (xargs :stobjs fn-bprx-raw-registry :guard t :verify-guards nil))
 (if (fn-bprr-intent fn-bprx-raw-registry)
  (mv :source-busy nil nil ledger fn-bprx-raw-registry)
  (let ((result (fn-tcl-step-source session message now)))
  (mv-let (word ref ledger fn-bprx-raw-registry)
   (fn-bprr-prepare-completion result owner demand ledger fn-bprx-raw-registry)
   (mv word ref result ledger fn-bprx-raw-registry)))))

; One actual lazy constructor per action. This stored intent is not a BODY
; grant: future installed parent must prepay the complete family and commit
; SAMEpool before entering this internal constructor path.
(defun fn-bprr-node-install (intent address fuel fn-bprx-byte-node)
 (declare (xargs :stobjs fn-bprx-byte-node :measure (nfix address)
  :guard (and (natp address) (natp fuel)) :verify-guards nil))
 (cond ((zp fuel) (mv :yield fuel fn-bprx-byte-node))
       ((zp address)
        (if (fn-bprxb-children-boundp 'fn-bprx-raw-source fn-bprx-byte-node)
         (mv :source-slot-occupied (1- fuel) fn-bprx-byte-node)
         (stobj-let ((fn-bprx-raw-source (fn-bprxb-children-get 'fn-bprx-raw-source
                       fn-bprx-byte-node (create-fn-bprx-raw-source))))
          (word ref fn-bprx-raw-source)
          (fn-bprx-source-retain (fn-bprr-at 1 (fn-bprr-at 1 intent))
            (fn-bprr-at 2 (fn-bprr-at 1 intent)) (fn-bprr-at 2 intent)
            (fn-bprr-at 3 intent) (fn-bprr-at 4 intent) (fn-bprr-at 5 intent)
            (fn-bprr-at 6 intent) fn-bprx-raw-source)
          (mv word (1- fuel) fn-bprx-byte-node))))
       ((equal (mod address 2) 0)
        (let ((present (fn-bprxb-children-boundp 'fn-bprx-byte-left fn-bprx-byte-node)))
         (stobj-let ((fn-bprx-byte-left (fn-bprxb-children-get 'fn-bprx-byte-left
                           fn-bprx-byte-node (create-fn-bprx-byte-left))))
          (word left fn-bprx-byte-left)
          (if present (fn-bprr-node-install intent (floor address 2) (1- fuel) fn-bprx-byte-left)
           (mv :source-directory-created (1- fuel) fn-bprx-byte-left))
          (mv word left fn-bprx-byte-node))))
       (t
        (let ((present (fn-bprxb-children-boundp 'fn-bprx-byte-right fn-bprx-byte-node)))
         (stobj-let ((fn-bprx-byte-right (fn-bprxb-children-get 'fn-bprx-byte-right
                           fn-bprx-byte-node (create-fn-bprx-byte-right))))
          (word left fn-bprx-byte-right)
          (if present (fn-bprr-node-install intent (floor address 2) (1- fuel) fn-bprx-byte-right)
           (mv :source-directory-created (1- fuel) fn-bprx-byte-right))
          (mv word left fn-bprx-byte-node))))
))
(defun fn-bprr-install-step (fuel fn-bprx-raw-registry)
 (declare (xargs :stobjs fn-bprx-raw-registry :guard (natp fuel) :verify-guards nil))
 (let* ((intent (fn-bprr-intent fn-bprx-raw-registry)) (ref (fn-bprr-at 1 intent)))
  (cond ((zp fuel) (mv :yield fuel fn-bprx-raw-registry))
        ((not (and (fn-bprr-refp ref) (eq (fn-bprr-at 7 intent) :reserved)))
         (mv :source-install-fenced fuel fn-bprx-raw-registry))
        (t
         (let* ((address (cadr ref))
                (fn-bprx-raw-registry
                 (update-fn-bprr-intent (update-nth 7 :constructing intent) fn-bprx-raw-registry)))
          (stobj-let ((fn-bprx-byte-node (fn-bprr-sources fn-bprx-raw-registry)))
           (word left fn-bprx-byte-node)
           (fn-bprr-node-install intent address fuel fn-bprx-byte-node)
           (let ((fn-bprx-raw-registry
                  (update-fn-bprr-intent
                   (cond ((eq word :source-retained) nil)
                         ((member-eq word '(:yield :source-directory-created)) intent)
                         (t (update-nth 7 :fenced intent))) fn-bprx-raw-registry)))
            (mv word left fn-bprx-raw-registry))))))))
; Token-selected operations, no authoritative source/leaf snapshot supplied
; by native. Recursive directory read/write checks boundp before every GET.
(defun fn-bprr-node-action (ref address operation pin-token pin-claim at count fuel fn-bprx-byte-node)
 (declare (xargs :stobjs fn-bprx-byte-node :measure (nfix address)
  :guard (and (natp address) (natp at) (natp count) (<= count 64) (natp fuel))
  :verify-guards nil))
 (cond ((zp fuel) (mv :yield nil fuel fn-bprx-byte-node))
       ((zp address)
        (if (not (fn-bprxb-children-boundp 'fn-bprx-raw-source fn-bprx-byte-node))
         (mv :stale-source nil (1- fuel) fn-bprx-byte-node)
         (stobj-let ((fn-bprx-raw-source (fn-bprxb-children-get 'fn-bprx-raw-source
                         fn-bprx-byte-node (create-fn-bprx-raw-source))))
          (word bytes left fn-bprx-raw-source)
          (cond
           ((eq operation :copy)
            (mv-let (word bytes left) (fn-bprx-source-copy ref pin-token at count (1- fuel) fn-bprx-raw-source)
             (mv word bytes left fn-bprx-raw-source)))
           ((eq operation :populate)
            (mv-let (word left fn-bprx-raw-source) (fn-bprx-source-populate ref (1- fuel) fn-bprx-raw-source)
             (mv word nil left fn-bprx-raw-source)))
           ((eq operation :construct)
            (mv-let (word left fn-bprx-raw-source) (fn-bprx-source-construct ref (1- fuel) fn-bprx-raw-source)
             (mv word nil left fn-bprx-raw-source)))
           ((eq operation :pin-state)
            (mv (cond ((not (fn-bprx-source-matchp ref fn-bprx-raw-source)) :stale-source)
                      ((not (eq (fn-bprxs-phase fn-bprx-raw-source) :published)) :source-unpublished)
                      ((fn-bprxs-pin fn-bprx-raw-source) :source-busy)
                      (t :source-pinnable)) nil (1- fuel) fn-bprx-raw-source))
           ((eq operation :pin)
            (mv-let (word fn-bprx-raw-source) (fn-bprx-source-pin ref pin-token pin-claim fn-bprx-raw-source)
             (mv word nil (1- fuel) fn-bprx-raw-source)))
           ((eq operation :fence)
            (mv-let (word fn-bprx-raw-source) (fn-bprx-source-fence ref fn-bprx-raw-source)
             (mv word nil (1- fuel) fn-bprx-raw-source)))
           (t (mv :source-operation-refused nil (1- fuel) fn-bprx-raw-source)))
          (mv word bytes left fn-bprx-byte-node))))
       ((equal (mod address 2) 0)
        (if (not (fn-bprxb-children-boundp 'fn-bprx-byte-left fn-bprx-byte-node))
         (mv :stale-source nil (1- fuel) fn-bprx-byte-node)
         (stobj-let ((fn-bprx-byte-left (fn-bprxb-children-get 'fn-bprx-byte-left
                          fn-bprx-byte-node (create-fn-bprx-byte-left))))
          (word bytes left fn-bprx-byte-left)
          (fn-bprr-node-action ref (floor address 2) operation pin-token pin-claim at count (1- fuel) fn-bprx-byte-left)
          (mv word bytes left fn-bprx-byte-node))))
       (t
        (if (not (fn-bprxb-children-boundp 'fn-bprx-byte-right fn-bprx-byte-node))
         (mv :stale-source nil (1- fuel) fn-bprx-byte-node)
         (stobj-let ((fn-bprx-byte-right (fn-bprxb-children-get 'fn-bprx-byte-right
                          fn-bprx-byte-node (create-fn-bprx-byte-right))))
          (word bytes left fn-bprx-byte-right)
          (fn-bprr-node-action ref (floor address 2) operation pin-token pin-claim at count (1- fuel) fn-bprx-byte-right)
          (mv word bytes left fn-bprx-byte-node))))
))
(defun fn-bprr-action (ref operation pin-token pin-claim at count fuel fn-bprx-raw-registry)
 (declare (xargs :stobjs fn-bprx-raw-registry
  :guard (and (natp at) (natp count) (<= count 64) (natp fuel)) :verify-guards nil))
 (cond ((not (fn-bprr-refp ref)) (mv :stale-source nil fuel fn-bprx-raw-registry))
       (t (let ((address (cadr ref)))
         (stobj-let ((fn-bprx-byte-node (fn-bprr-sources fn-bprx-raw-registry)))
          (word bytes left fn-bprx-byte-node)
          (fn-bprr-node-action ref address operation pin-token pin-claim at count fuel fn-bprx-byte-node)
          (mv word bytes left fn-bprx-raw-registry))))))

(defun fn-bprr-address-depth (address)
 (declare (xargs :guard (natp address) :measure (nfix address) :verify-guards nil))
 (if (zp address) 0 (1+ (fn-bprr-address-depth (floor address 2)))))
; Internal SAMEPRS pin issuer. No native supplied pin nonce; demand is a
; storage-test/internal algebra input, never a substituted public BODY grant.
; Pin claim remains with source even on fence, no release API from booleans.
(defun fn-bprr-pin-issue (ref demand ledger fuel fn-bprx-raw-registry)
 (declare (xargs :stobjs fn-bprx-raw-registry :guard (natp fuel) :verify-guards nil))
 (cond
  ((not (fn-bprr-refp ref)) (mv :stale-source nil ledger fuel fn-bprx-raw-registry))
  ((fn-bprr-intent fn-bprx-raw-registry) (mv :source-busy nil ledger fuel fn-bprx-raw-registry))
  ((not (and (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
   (mv :invalid-source-demand nil ledger fuel fn-bprx-raw-registry))
  ((< fuel (* 2 (1+ (fn-bprr-address-depth (cadr ref)))))
   (mv :yield nil ledger fuel fn-bprx-raw-registry))
  (t
   (mv-let (word ignored left fn-bprx-raw-registry)
    (fn-bprr-action ref :pin-state nil nil 0 0 fuel fn-bprx-raw-registry)
    (declare (ignore ignored))
    (if (not (eq word :source-pinnable)) (mv word nil ledger left fn-bprx-raw-registry)
     (let ((next (fn-prl-nth 2 ledger)))
      (mv-let (word issued charged)
       (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
        (fn-prl-nth 1 ledger) next (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
       (if (not (eq word :admitted)) (mv word nil ledger left fn-bprx-raw-registry)
        (let* ((pin (list :bps-source-pin next (cadr ref) (caddr ref)))
               (ledger (fn-prl-build (fn-prl-nth 0 ledger) charged issued
                         (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)))
               (fn-bprx-raw-registry
                (update-fn-bprr-intent (list :raw-source-pin-intent ref pin demand :issuing)
                                      fn-bprx-raw-registry)))
         (mv-let (word ignored left fn-bprx-raw-registry)
          (fn-bprr-action ref :pin pin demand 0 0 left fn-bprx-raw-registry)
          (declare (ignore ignored))
          (let ((fn-bprx-raw-registry
                 (if (eq word :source-pinned)
                  (update-fn-bprr-intent nil fn-bprx-raw-registry) fn-bprx-raw-registry)))
           (mv word (if (eq word :source-pinned) pin nil) ledger left fn-bprx-raw-registry)))))))))))
)

; Registered TCPCL state eliminates native session snapshots as source
; registration authority. Separate dynamically-addressed controller directory.
(defun fn-bprr-controller-refp (ref)
 (declare (xargs :guard t))
 (and (consp ref) (eq (car ref) :bps-tcpcl-ref)
      (consp (cdr ref)) (natp (cadr ref)) (<= (cadr ref) 18446744073709551615)
      (consp (cddr ref)) (natp (caddr ref)) (<= (caddr ref) 18446744073709551615)
      (null (cdddr ref))))
(defun fn-bprr-controller-reserve (role params now demand ledger fn-bprx-raw-registry)
 (declare (xargs :stobjs fn-bprx-raw-registry :guard t :verify-guards nil))
 (cond
  ((fn-bprr-intent fn-bprx-raw-registry) (mv :source-busy nil ledger fn-bprx-raw-registry))
  ((not (and (fn-tcl-rolep role) (fn-tcl-paramsp params) (fn-clock-timep now)))
   (mv :tcpcl-config-refused nil ledger fn-bprx-raw-registry))
  ((not (and (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
   (mv :invalid-source-demand nil ledger fn-bprx-raw-registry))
  ((not (and (natp (fn-prl-nth 2 ledger)) (<= (fn-prl-nth 2 ledger) 18446744073709551615)))
   (mv :source-format-exhausted nil ledger fn-bprx-raw-registry))
  (t (let ((next (fn-prl-nth 2 ledger)))
   (mv-let (word issued charged)
    (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
     (fn-prl-nth 1 ledger) next (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
    (if (not (eq word :admitted)) (mv word nil ledger fn-bprx-raw-registry)
     (let* ((ref (list :bps-tcpcl-ref next next))
            (ledger (fn-prl-build (fn-prl-nth 0 ledger) charged issued
                       (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)))
            (fn-bprx-raw-registry
             (update-fn-bprr-intent (list :raw-tcpcl-intent ref role params now nil demand :reserved)
                                   fn-bprx-raw-registry)))
      (mv :tcpcl-reserved ref ledger fn-bprx-raw-registry))))))))
(defun fn-bprr-controller-install-node (intent address fuel fn-bprx-byte-node)
 (declare (xargs :stobjs fn-bprx-byte-node :measure (nfix address)
  :guard (and (natp address) (natp fuel)) :verify-guards nil))
 (cond ((zp fuel) (mv :yield fuel fn-bprx-byte-node))
       ((zp address)
        (if (fn-bprxb-children-boundp 'fn-bprx-tcpcl-controller fn-bprx-byte-node)
         (mv :tcpcl-slot-occupied (1- fuel) fn-bprx-byte-node)
         (stobj-let ((fn-bprx-tcpcl-controller
           (fn-bprxb-children-get 'fn-bprx-tcpcl-controller fn-bprx-byte-node
                                  (create-fn-bprx-tcpcl-controller))))
          (fn-bprx-tcpcl-controller)
          (let* ((ref (fn-bprr-at 1 intent))
                 (fn-bprx-tcpcl-controller (update-fn-bprtc-slot (cadr ref) fn-bprx-tcpcl-controller))
                 (fn-bprx-tcpcl-controller (update-fn-bprtc-nonce (caddr ref) fn-bprx-tcpcl-controller))
                 (fn-bprx-tcpcl-controller
                  (update-fn-bprtc-session (fn-tcl-initial-session (fn-bprr-at 2 intent)
                    (fn-bprr-at 3 intent) (fn-bprr-at 4 intent)) fn-bprx-tcpcl-controller))
                 (fn-bprx-tcpcl-controller (update-fn-bprtc-claim (fn-bprr-at 6 intent) fn-bprx-tcpcl-controller)))
           (update-fn-bprtc-phase :live fn-bprx-tcpcl-controller))
          (mv :tcpcl-registered (1- fuel) fn-bprx-byte-node))))
       ((equal (mod address 2) 0)
        (let ((present (fn-bprxb-children-boundp 'fn-bprx-byte-left fn-bprx-byte-node)))
         (stobj-let ((fn-bprx-byte-left (fn-bprxb-children-get 'fn-bprx-byte-left
                      fn-bprx-byte-node (create-fn-bprx-byte-left))))
          (word left fn-bprx-byte-left)
          (if present (fn-bprr-controller-install-node intent (floor address 2) (1- fuel) fn-bprx-byte-left)
           (mv :source-directory-created (1- fuel) fn-bprx-byte-left))
          (mv word left fn-bprx-byte-node))))
       (t
        (let ((present (fn-bprxb-children-boundp 'fn-bprx-byte-right fn-bprx-byte-node)))
         (stobj-let ((fn-bprx-byte-right (fn-bprxb-children-get 'fn-bprx-byte-right
                      fn-bprx-byte-node (create-fn-bprx-byte-right))))
          (word left fn-bprx-byte-right)
          (if present (fn-bprr-controller-install-node intent (floor address 2) (1- fuel) fn-bprx-byte-right)
           (mv :source-directory-created (1- fuel) fn-bprx-byte-right))
          (mv word left fn-bprx-byte-node))))
))
(defun fn-bprr-controller-install (fuel fn-bprx-raw-registry)
 (declare (xargs :stobjs fn-bprx-raw-registry :guard (natp fuel) :verify-guards nil))
 (let* ((intent (fn-bprr-intent fn-bprx-raw-registry)) (ref (fn-bprr-at 1 intent)))
  (cond ((zp fuel) (mv :yield fuel fn-bprx-raw-registry))
        ((not (and (eq (car intent) :raw-tcpcl-intent) (fn-bprr-controller-refp ref)
                   (eq (fn-bprr-at 7 intent) :reserved)))
         (mv :tcpcl-install-fenced fuel fn-bprx-raw-registry))
        (t (let* ((address (cadr ref))
                  (fn-bprx-raw-registry
                   (update-fn-bprr-intent (update-nth 7 :constructing intent) fn-bprx-raw-registry)))
         (stobj-let ((fn-bprx-byte-node (fn-bprr-controllers fn-bprx-raw-registry)))
          (word left fn-bprx-byte-node)
          (fn-bprr-controller-install-node intent address fuel fn-bprx-byte-node)
          (let ((fn-bprx-raw-registry
                 (update-fn-bprr-intent
                  (cond ((eq word :tcpcl-registered) nil)
                        ((member-eq word '(:yield :source-directory-created)) intent)
                        (t (update-nth 7 :fenced intent))) fn-bprx-raw-registry)))
           (mv word left fn-bprx-raw-registry))))))))
; Read/update is core-only composition. Native never supplies CURRENT/session.
; Revision fence is scalar, never deep session/received-chain equality.
(defun fn-bprr-controller-node (ref address operation expected-revision next-session fuel fn-bprx-byte-node)
 (declare (xargs :stobjs fn-bprx-byte-node :measure (nfix address)
  :guard (and (natp address) (natp expected-revision) (natp fuel)) :verify-guards nil))
 (cond ((zp fuel) (mv :yield nil 0 fuel fn-bprx-byte-node))
       ((zp address)
        (if (not (fn-bprxb-children-boundp 'fn-bprx-tcpcl-controller fn-bprx-byte-node))
         (mv :stale-tcpcl nil 0 (1- fuel) fn-bprx-byte-node)
         (stobj-let ((fn-bprx-tcpcl-controller
           (fn-bprxb-children-get 'fn-bprx-tcpcl-controller fn-bprx-byte-node
                                  (create-fn-bprx-tcpcl-controller))))
          (word session revision fn-bprx-tcpcl-controller)
          (let ((revision (fn-bprtc-revision fn-bprx-tcpcl-controller)))
           (cond
            ((not (and (equal (cadr ref) (fn-bprtc-slot fn-bprx-tcpcl-controller))
                       (equal (caddr ref) (fn-bprtc-nonce fn-bprx-tcpcl-controller))))
             (mv :stale-tcpcl nil revision fn-bprx-tcpcl-controller))
            ((not (eq (fn-bprtc-phase fn-bprx-tcpcl-controller) :live))
             (mv :tcpcl-fenced nil revision fn-bprx-tcpcl-controller))
            ((eq operation :read)
             (mv :tcpcl-current (fn-bprtc-session fn-bprx-tcpcl-controller) revision fn-bprx-tcpcl-controller))
            ((not (equal revision expected-revision))
             (mv :stale-tcpcl-action nil revision fn-bprx-tcpcl-controller))
            ((eq operation :defer)
             ; Retain the exact completion, including raw root and held END ACK.
             ; No protocol event escapes this fenced recovery path.
             (let* ((fn-bprx-tcpcl-controller (update-fn-bprtc-pending next-session fn-bprx-tcpcl-controller))
                    (fn-bprx-tcpcl-controller (update-fn-bprtc-phase :fenced fn-bprx-tcpcl-controller)))
              (mv :tcpcl-deferred nil revision fn-bprx-tcpcl-controller)))
            ((eq operation :replace)
             (let* ((fn-bprx-tcpcl-controller (update-fn-bprtc-session next-session fn-bprx-tcpcl-controller))
                    (fn-bprx-tcpcl-controller (update-fn-bprtc-revision (1+ revision) fn-bprx-tcpcl-controller)))
              (mv :tcpcl-updated nil (1+ revision) fn-bprx-tcpcl-controller)))
            ((eq operation :fence)
             (let ((fn-bprx-tcpcl-controller (update-fn-bprtc-phase :fenced fn-bprx-tcpcl-controller)))
              (mv :tcpcl-fenced nil revision fn-bprx-tcpcl-controller)))
            (t (mv :tcpcl-operation-refused nil revision fn-bprx-tcpcl-controller))))
          (mv word session revision (1- fuel) fn-bprx-byte-node))))
       ((equal (mod address 2) 0)
        (if (not (fn-bprxb-children-boundp 'fn-bprx-byte-left fn-bprx-byte-node))
         (mv :stale-tcpcl nil 0 (1- fuel) fn-bprx-byte-node)
         (stobj-let ((fn-bprx-byte-left (fn-bprxb-children-get 'fn-bprx-byte-left
                         fn-bprx-byte-node (create-fn-bprx-byte-left))))
          (word session revision left fn-bprx-byte-left)
          (fn-bprr-controller-node ref (floor address 2) operation expected-revision next-session (1- fuel) fn-bprx-byte-left)
          (mv word session revision left fn-bprx-byte-node))))
       (t
        (if (not (fn-bprxb-children-boundp 'fn-bprx-byte-right fn-bprx-byte-node))
         (mv :stale-tcpcl nil 0 (1- fuel) fn-bprx-byte-node)
         (stobj-let ((fn-bprx-byte-right (fn-bprxb-children-get 'fn-bprx-byte-right
                         fn-bprx-byte-node (create-fn-bprx-byte-right))))
          (word session revision left fn-bprx-byte-right)
          (fn-bprr-controller-node ref (floor address 2) operation expected-revision next-session (1- fuel) fn-bprx-byte-right)
          (mv word session revision left fn-bprx-byte-node))))
))
(defun fn-bprr-controller-action (ref operation expected-revision next-session fuel fn-bprx-raw-registry)
 (declare (xargs :stobjs fn-bprx-raw-registry
  :guard (and (natp expected-revision) (natp fuel)) :verify-guards nil))
 (if (not (fn-bprr-controller-refp ref)) (mv :stale-tcpcl nil 0 fuel fn-bprx-raw-registry)
  (let ((address (cadr ref)))
   (stobj-let ((fn-bprx-byte-node (fn-bprr-controllers fn-bprx-raw-registry)))
    (word session revision left fn-bprx-byte-node)
    (fn-bprr-controller-node ref address operation expected-revision next-session fuel fn-bprx-byte-node)
    (mv word session revision left fn-bprx-raw-registry)))))
; Exact registered caller. Original source root never appears in output.
; Protocol result SENDs are core-produced; source completion is replaced with
; fixed ref event, so native cannot pass chain/count back as an authority.
(defun fn-bprr-public-events (events source-ref)
 (declare (xargs :guard t :measure (acl2-count events) :verify-guards nil))
 (if (atom events) nil
  (cons (if (eq (fn-cbor-ag-car (car events)) :bundle-segments-received)
         (list :source-registered source-ref) (car events))
        (fn-bprr-public-events (cdr events) source-ref))))
(defun fn-bprr-registered-receive (controller message now demand ledger fuel fn-bprx-raw-registry)
 (declare (xargs :stobjs fn-bprx-raw-registry :guard (natp fuel) :verify-guards nil))
 (cond
  ((not (fn-bprr-controller-refp controller))
   (mv :stale-tcpcl nil nil ledger fuel fn-bprx-raw-registry))
  ((fn-bprr-intent fn-bprx-raw-registry)
   (mv :source-busy nil nil ledger fuel fn-bprx-raw-registry))
  ((< fuel (* 2 (1+ (fn-bprr-address-depth (cadr controller)))))
   (mv :yield nil nil ledger fuel fn-bprx-raw-registry))
  (t
   (mv-let (word session revision left fn-bprx-raw-registry)
    (fn-bprr-controller-action controller :read 0 nil fuel fn-bprx-raw-registry)
    (if (not (eq word :tcpcl-current)) (mv word nil nil ledger left fn-bprx-raw-registry)
     (mv-let (source-word ref result ledger fn-bprx-raw-registry)
      (fn-bprr-receive-step session message now controller demand ledger fn-bprx-raw-registry)
      (mv-let (word ignored new-revision left fn-bprx-raw-registry)
       (fn-bprr-controller-action controller
         (if (and (fn-bprr-completion result) (not ref)) :defer :replace) revision
         (if (and (fn-bprr-completion result) (not ref)) result (fn-tcl-result-session result)) left fn-bprx-raw-registry)
       (declare (ignore ignored new-revision))
       (if (eq word :tcpcl-updated)
        (mv source-word ref (fn-bprr-public-events (fn-tcl-result-events result) ref)
            ledger left fn-bprx-raw-registry)
        ; No rollback of generated source/counter/intent. Caller must fence
        ; allocation and recover, retaining both roots/charges/ACK custody.
        (mv (if (eq word :tcpcl-deferred) source-word :source-controller-uncertain)
            ref nil ledger left fn-bprx-raw-registry)))))))))

; Literal readonly provider subject. All identity and pin checks select actual
; retained registry storage; no native byte/window argument is accepted.
(defun fn-bprr-readcopy (ref pin-token absolute-at count fuel fn-bprx-raw-registry)
 (declare (xargs :stobjs fn-bprx-raw-registry
  :guard (and (natp absolute-at) (natp count) (<= count 64) (natp fuel))
  :verify-guards nil))
 (fn-bprr-action ref :copy pin-token nil absolute-at count fuel fn-bprx-raw-registry))
