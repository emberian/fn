; Actual retained decoded controller. Internal source candidate; no installer.
(in-package "ACL2")
(include-book "page-window-worker-storage")
(include-book "decoded-window-begin")

; Presence never authorizes construction or operation allocation. Missing reads
; do not GET/create children. The sanctioned factory/issuer is a separate gate.
(defun fn-dwc-boundp (fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard t))
 (and (fn-pww-storage-boundp fn-pww-node)
      (fn-pww-children-boundp 'fn-zin-st fn-pww-node)
      (fn-pww-children-boundp 'fn-zin-win fn-pww-node)
      (fn-pww-children-boundp 'fn-zin-tab fn-pww-node)
      (fn-pww-children-boundp 'fn-zin-out fn-pww-node)))

; Only internally captured CURRENT token/source and actual children reach BEGIN.
; Public acquisition remains unavailable until the issuer installs that carry
; using actual source authority and the SAME-pool complete operation allowance.
(defun fn-dwc-begin (token fn-pww-carry pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
 (declare (xargs :stobjs (fn-pww-carry pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                 :guard t :verify-guards nil))
 (if (not (and (fn-pwz-tokenp token)
               (equal token (fn-pww-token fn-pww-carry))
               (eq (fn-pww-phase fn-pww-carry) :assigned)
               (eq (fn-pww-borrow-phase fn-pww-carry) :owned)
               (consp (fn-pww-root fn-pww-carry))
               (null (fn-pww-controller fn-pww-carry))))
     (mv :stale-decoded-worker fn-pww-carry pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
   (let ((fn-pww-carry (update-fn-pww-phase :initializing fn-pww-carry)))
    (mv-let (z pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
     (fn-pwz-begin token (fn-pww-source-incarnation fn-pww-carry)
                   pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
     (let* ((fn-pww-carry (update-fn-pww-controller z fn-pww-carry))
            (fn-pww-carry (update-fn-pww-observation :decoded-started fn-pww-carry))
            (fn-pww-carry (update-fn-pww-phase :running fn-pww-carry)))
      (mv :decoded-started fn-pww-carry pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))))

; Exactly one actual semantic quantum, no external controller/effect input.
; :READ is separately issued and completed by a registered I/O observation
; wrapper; this subject cannot overwrite input merely from a native tuple.
(defun fn-dwc-one (token fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
 (declare (xargs :stobjs (fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
                 :guard t :verify-guards nil))
 (let ((z (fn-pww-controller fn-pww-carry)))
  (if (not (and (fn-pwz-tokenp token)
                (equal token (fn-pww-token fn-pww-carry))
                (eq (fn-pww-phase fn-pww-carry) :running)
                (eq (fn-pww-borrow-phase fn-pww-carry) :owned)
                (null (fn-pww-pending-action fn-pww-carry))
                (true-listp z) (true-listp (nth 1 z))))
      (mv :stale-decoded-worker nil fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
    (let ((action (fn-ewz-next-action z pgs-digest-state)))
     (case (car action)
      (:codec
       (let ((fn-pww-carry (update-fn-pww-phase :codec-acting fn-pww-carry)))
       (mv-let (word next fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
        (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
        (let* ((fn-pww-carry (update-fn-pww-controller next fn-pww-carry))
               (fn-pww-carry (update-fn-pww-observation word fn-pww-carry))
               (fn-pww-carry (update-fn-pww-phase :running fn-pww-carry)))
         (mv word nil fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))))
      (:tick
       (let ((fn-pww-carry (update-fn-pww-phase :hash-acting fn-pww-carry)))
       (mv-let (word next pgs-digest-state)
        (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)
        (let* ((fn-pww-carry (update-fn-pww-controller next fn-pww-carry))
               (fn-pww-carry (update-fn-pww-observation word fn-pww-carry))
               (fn-pww-carry (update-fn-pww-phase :running fn-pww-carry)))
         (mv word nil fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))))
      (:read
       ; Persist the actual core effect before exposing I/O. A second ONE
       ; cannot issue another effect until this exact pending action settles.
       (let* ((fn-pww-carry (update-fn-pww-phase :read-issuing fn-pww-carry))
              (revision (+ 1 (fn-pww-action-revision fn-pww-carry)))
              (fn-pww-carry (update-fn-pww-action-revision revision fn-pww-carry))
              (fn-pww-carry (update-fn-pww-pending-action action fn-pww-carry))
              (fn-pww-carry (update-fn-pww-phase :running fn-pww-carry)))
        (mv :read (list :decoded-read token revision (cadr action)) fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
      (otherwise
       (mv (car action) (cdr action) fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))))))

; Actual parent selects/persists all children at the SAME physical leaf.
(defun fn-dwc-node-one (token fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard t :verify-guards nil))
 (if (not (fn-dwc-boundp fn-pww-node))
     (mv :decoded-worker-storage-unavailable nil fn-pww-node)
   (stobj-let
    ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry)))
     (fn-octets (fn-pww-children-get 'fn-octets fn-pww-node (create-fn-octets)))
     (pgs-digest-state (fn-pww-children-get 'pgs-digest-state fn-pww-node (create-pgs-digest-state)))
     (fn-zin-st (fn-pww-children-get 'fn-zin-st fn-pww-node (create-fn-zin-st)))
     (fn-zin-win (fn-pww-children-get 'fn-zin-win fn-pww-node (create-fn-zin-win)))
     (fn-zin-tab (fn-pww-children-get 'fn-zin-tab fn-pww-node (create-fn-zin-tab)))
     (fn-zin-out (fn-pww-children-get 'fn-zin-out fn-pww-node (create-fn-zin-out)))
     (fn-ew-buffer (fn-pww-children-get 'fn-ew-buffer fn-pww-node (create-fn-ew-buffer))))
    (word effect fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
    (fn-dwc-one token fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
    (mv word effect fn-pww-node))))

; Revision arithmetic/representation requires the actual installed successor
; domain before production entry; no unbounded-integer tariff is claimed here.
; Actual read completion consumes the CURRENT issued effect, never a host
; snapshot of that effect/controller. Native status is an I/O observation;
; integrity and coordinate decisions remain in the actual combined core.
(defun fn-dwc-read-observation (token revision io-status fn-pww-carry fn-octets pgs-digest-state fn-ew-buffer)
 (declare (xargs :stobjs (fn-pww-carry fn-octets pgs-digest-state fn-ew-buffer)
                 :guard t :verify-guards nil))
 (let ((z (fn-pww-controller fn-pww-carry))
       (action (fn-pww-pending-action fn-pww-carry)))
  (if (not (and (fn-pwz-tokenp token)
                (equal token (fn-pww-token fn-pww-carry))
                (eq (fn-pww-phase fn-pww-carry) :running)
                (eq (fn-pww-borrow-phase fn-pww-carry) :owned)
                (natp revision)
                (equal revision (fn-pww-action-revision fn-pww-carry))
                (consp action) (true-listp action)
                (eq (car action) :read)
                (true-listp z) (true-listp (nth 1 z))))
      (mv :stale-decoded-read fn-pww-carry fn-octets pgs-digest-state fn-ew-buffer)
    (let ((fn-pww-carry (update-fn-pww-phase :read-settling fn-pww-carry)))
    (mv-let (word next pgs-digest-state fn-ew-buffer)
     (fn-ewz-read (cadr action) io-status z fn-octets pgs-digest-state fn-ew-buffer)
     (let* ((fn-pww-carry (update-fn-pww-controller next fn-pww-carry))
            (fn-pww-carry (update-fn-pww-observation word fn-pww-carry))
            (fn-pww-carry (update-fn-pww-pending-action nil fn-pww-carry))
            (fn-pww-carry (update-fn-pww-phase :running fn-pww-carry)))
      (mv word fn-pww-carry fn-octets pgs-digest-state fn-ew-buffer)))))))

(defun fn-dwc-node-begin (token fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard t :verify-guards nil))
 (if (not (fn-dwc-boundp fn-pww-node))
     (mv :decoded-worker-storage-unavailable fn-pww-node)
   (stobj-let
    ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry)))
     (pgs-digest-state (fn-pww-children-get 'pgs-digest-state fn-pww-node (create-pgs-digest-state)))
     (fn-zin-st (fn-pww-children-get 'fn-zin-st fn-pww-node (create-fn-zin-st)))
     (fn-zin-win (fn-pww-children-get 'fn-zin-win fn-pww-node (create-fn-zin-win)))
     (fn-zin-tab (fn-pww-children-get 'fn-zin-tab fn-pww-node (create-fn-zin-tab)))
     (fn-zin-out (fn-pww-children-get 'fn-zin-out fn-pww-node (create-fn-zin-out))))
    (word fn-pww-carry pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (fn-dwc-begin token fn-pww-carry pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (mv word fn-pww-node))))

(defun fn-dwc-node-read-observation (token revision io-status fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard t :verify-guards nil))
 (if (not (fn-dwc-boundp fn-pww-node))
     (mv :decoded-worker-storage-unavailable fn-pww-node)
   (stobj-let
    ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry)))
     (fn-octets (fn-pww-children-get 'fn-octets fn-pww-node (create-fn-octets)))
     (pgs-digest-state (fn-pww-children-get 'pgs-digest-state fn-pww-node (create-pgs-digest-state)))
     (fn-ew-buffer (fn-pww-children-get 'fn-ew-buffer fn-pww-node (create-fn-ew-buffer))))
    (word fn-pww-carry fn-octets pgs-digest-state fn-ew-buffer)
    (fn-dwc-read-observation token revision io-status fn-pww-carry fn-octets pgs-digest-state fn-ew-buffer)
    (mv word fn-pww-node))))

; Exact six guard events admitted in the matched protected source world.
(verify-guards fn-dwc-begin)
(verify-guards fn-dwc-one)
(verify-guards fn-dwc-node-one)
(verify-guards fn-dwc-read-observation)
(verify-guards fn-dwc-node-begin)
(verify-guards fn-dwc-node-read-observation)
