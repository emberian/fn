; Actual internally derived selected-cell demand boundary.
; Guard safety is carried domain only. Authenticated modern captured-row
; publication/incarnation establishment and runtime activation remain open.
(in-package "ACL2")
(include-book "index-range-held-row-controller")
(include-book "index-backing-provider")
(include-book "index-publication-shape")

(defun fn-ibr-joint-segment-demand (token fn-ibp-query-segment fn-query-payload-grants fn-arena)
 (declare (ignorable fn-arena)
          (xargs :stobjs (fn-ibp-query-segment fn-query-payload-grants fn-arena)
  :guard (and (fn-ibp-query-tokenp token)
          (implies (fn-ibp-query-slot-livep token fn-ibp-query-segment)
          (fn-ibr-held-current-ready-p
            (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment) fn-arena)))))
 (if (not (fn-ibp-query-slot-livep token fn-ibp-query-segment))
  (mv :stale nil)
  (let* ((slot (nth 3 token))
         (control (fn-ibp-qs-controlsi slot fn-ibp-query-segment))
         (capture (fn-ibp-qs-capturesi slot fn-ibp-query-segment))
         (context (fn-ibp-qs-inputsi slot fn-ibp-query-segment))
         (payload (fn-omk-at 5 context))
         (admission (fn-ibp-qs-admissionsi slot fn-ibp-query-segment))
         (claim (fn-omk-at 0 admission))
         (pin (fn-spp-at 5 control))
         (publication (fn-spp-at 2 pin)))
   (if (not (and (eq (fn-spp-at 0 control) :fn-ibr)
                 (equal (fn-spp-at 1 control) (nth 1 token))
                 (equal (fn-spp-at 2 control) (nth 4 token))
                 (eq (fn-spp-at 0 pin) :publication-pin)
                 (equal (fn-ipub-generation publication) (nth 4 token))
                 (equal (fn-ipub-table-id publication) (fn-ibp-capture-table-root-id capture))
                 (equal (fn-ipub-row-id publication) (fn-ibp-capture-row-root-id capture))
                 (equal (fn-ipub-count publication) (fn-ibp-capture-count capture))
                 (equal (fn-ipub-frontier publication) (fn-ibp-capture-frontier capture))
                 (eq (fn-omk-at 2 admission) :active)
                 (fn-omk-widthp claim 12)
                 (eq (fn-omk-at 0 claim) :query-grant)
                 (equal (fn-omk-at 1 claim) (nth 1 token))
                 (equal (fn-omk-at 2 claim) (nth 2 token))
                 (equal (fn-omk-at 3 claim) slot)
                 (equal (fn-omk-at 4 claim) (nth 4 token))
                 (equal (fn-omk-at 5 claim) (fn-ibp-capture-table-root-id capture))
                 (equal (fn-omk-at 6 claim) (fn-ibp-capture-row-root-id capture))
                 (equal (fn-omk-at 7 claim) (fn-ibp-capture-count capture))
                 (equal (fn-omk-at 8 claim) (fn-ibp-capture-frontier capture))
                 (equal (fn-omk-at 9 claim) (nth 4 token))
                 (fn-qpg-livep payload fn-query-payload-grants)
                 (equal (fn-omk-at 1 payload) (nth 1 token))
                 (equal (fn-omk-at 2 payload) slot)
                 (equal (fn-omk-at 3 payload) (nth 4 token))
                 (equal (fn-omk-at 6 payload) (nth 2 token))
                 (equal (fn-omk-at 10 claim) (fn-omk-at 4 payload))
                 (equal (fn-omk-at 11 claim) (fn-omk-at 5 payload))))
    (mv :recovery-required nil)
    (let ((payload-row (fn-qpg-rowsi (fn-qpg-slot payload) fn-query-payload-grants)))
     (if (not (and (eq (fn-omk-at 2 payload-row) :active)
                   (equal (fn-omk-at 1 payload-row) claim)))
      (mv :recovery-required nil)
      (let* ((cell (fn-spp-at 4 (fn-spp-at 8 control)))
             (held (fn-hmid-at 3 cell)))
       (mv-let (word handle index origin) (fn-osh-byte-demand cell)
        (if (eq word :payload)
            (mv :payload (list :render-byte token payload held handle index origin))
          (mv :none nil))))))))))

(defun fn-ibr-node-demand-ready-p (token address depth fn-ibp-node fn-arena)
 (declare (xargs :stobjs (fn-ibp-node fn-arena)
                 :guard (and (fn-ibp-query-tokenp token)
                             (natp address) (natp depth))))
 (mv-let (status control capture borrow left)
  (fn-ibp-node-query-read token (+ 1 depth) address depth fn-ibp-node)
  (declare (ignore capture borrow left))
  (implies (eq status :live) (fn-ibr-held-current-ready-p control fn-arena))))

(defun fn-ibr-node-demand (token fuel address depth fn-ibp-node fn-arena)
 (declare (xargs :stobjs (fn-ibp-node fn-arena) :measure (nfix depth) :verify-guards nil
  :guard (and (fn-ibp-query-tokenp token) (natp fuel) (natp address) (natp depth)
              (fn-ibr-node-demand-ready-p token address depth fn-ibp-node fn-arena))))
 (cond
  ((<= fuel depth) (mv :yield nil fuel))
  ((zp depth)
   (if (not (and (zp address)
                 (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node)
                 (fn-ibp-node-children-boundp 'fn-query-payload-grants fn-ibp-node)))
    (mv :unavailable nil fuel)
    (stobj-let ((fn-ibp-query-segment
                 (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                           (create-fn-ibp-query-segment)))
                (fn-query-payload-grants
                 (fn-ibp-node-children-get 'fn-query-payload-grants fn-ibp-node
                                           (create-fn-query-payload-grants))))
     (word demand)
     (fn-ibr-joint-segment-demand token fn-ibp-query-segment fn-query-payload-grants fn-arena)
     (mv word demand (- fuel 1)))))
  ((equal (mod address 2) 0)
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
    (mv :unavailable nil fuel)
    (stobj-let ((fn-ibp-node-left
                 (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                           (create-fn-ibp-node-left))))
     (word demand remaining)
     (fn-ibr-node-demand token (- fuel 1) (floor address 2) (- depth 1)
                            fn-ibp-node-left fn-arena)
     (mv word demand remaining))))
  (t
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
    (mv :unavailable nil fuel)
    (stobj-let ((fn-ibp-node-right
                 (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                           (create-fn-ibp-node-right))))
     (word demand remaining)
     (fn-ibr-node-demand token (- fuel 1) (floor address 2) (- depth 1)
                            fn-ibp-node-right fn-arena)
     (mv word demand remaining))))))

(verify-guards fn-ibr-node-demand
 :hints (("Goal"
  :expand ((:free (token fuel address depth)
             (fn-ibp-node-query-read token fuel address depth fn-ibp-node)))
  :in-theory
  (e/d (fn-ibr-node-demand-ready-p)
       (fn-ibp-node-query-read fn-ibr-joint-segment-demand
        fn-ibr-held-current-ready-p)))))

; Domain-only ghost. Strong registered captured-row/publication source carry
; must imply this before the actual source-ready host adapter is installed.
(defun fn-ibr-render-cell-ready-p (fn-render-holder fn-mio$c fn-arena)
 (declare (xargs :stobjs (fn-render-holder fn-mio$c fn-arena) :guard t))
 (let ((token (fn-rh-query fn-render-holder)))
  (and (fn-ibp-query-tokenp token)
   (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (ready)
    (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
     (ready)
     (fn-ibr-node-demand-ready-p token (- (nth 2 token) 1)
        (fn-ibp-slot-depth fn-index-backing) fn-ibp-node fn-arena)
     ready)
    ready))))

(defun fn-ibr-render-byte-demand
 (fuel fn-render-holder fn-mio$c fn-arena state)
 (declare (xargs :stobjs (fn-render-holder fn-mio$c fn-arena state)
  :guard (and (natp fuel)
              (fn-ibr-render-cell-ready-p fn-render-holder fn-mio$c fn-arena))
  :verify-guards nil))
 (declare (ignore state))
 (let ((token (fn-rh-query fn-render-holder)))
  (if (not (and (fn-rh-live fn-render-holder) (fn-ibp-query-tokenp token)))
      (mv :unavailable nil fuel fn-mio$c)
   (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (word demand left)
    (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
     (word demand left)
     (fn-ibr-node-demand token fuel (- (nth 2 token) 1)
       (fn-ibp-slot-depth fn-index-backing) fn-ibp-node fn-arena)
     (mv word demand left))
    (mv word demand left fn-mio$c)))))

; CONDITIONAL domain result, not registered source/capture establishment.
(defthm fn-ibr-joint-demand-is-same-held-payload-and-origin
 (implies
  (and (fn-ibp-query-tokenp token)
       (fn-ibp-query-slot-livep token fn-ibp-query-segment)
       (fn-ibr-held-current-ready-p
        (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment) fn-arena))
  (let ((answer (fn-ibr-joint-segment-demand
                  token fn-ibp-query-segment fn-query-payload-grants fn-arena)))
   (implies (eq (mv-nth 0 answer) :payload)
    (let ((demand (mv-nth 1 answer)))
     (and (equal (fn-omk-at 0 demand) :render-byte)
          (equal (fn-omk-at 1 demand) token)
          (equal (fn-omk-at 4 demand)
                 (fn-record-payload (fn-omk-at 3 demand)))
          (natp (fn-omk-at 4 demand)) (natp (fn-omk-at 5 demand))
          (< (fn-omk-at 4 demand) (fn-arena-count fn-arena))
          (< (fn-omk-at 5 demand)
             (fn-arena-payload-len (fn-omk-at 4 demand) fn-arena)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-osh-byte-demand-retains-selected-source
           (cell (fn-spp-at 4 (fn-spp-at 8
                    (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment)))))
        (:instance fn-osh-byte-demand-is-in-current-payload
           (cell (fn-spp-at 4 (fn-spp-at 8
                    (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment))))))
  :in-theory
  (e/d (fn-ibr-joint-segment-demand fn-ibr-held-current-ready-p fn-omk-at)
       (fn-osh-byte-demand fn-osh-ready-p fn-osh-selected-source-p
        fn-ibp-query-tokenp fn-ibp-query-slot-livep fn-spp-at fn-hmid-at
        fn-qpg-livep fn-omk-widthp fn-record-payload)))))

; Actual external domain guard; strong captured source authority remains open.
(verify-guards fn-ibr-render-byte-demand
 :hints (("Goal"
  :in-theory (enable fn-ibr-render-cell-ready-p))))
