; INTERNAL accepted-view-change continuation. The actual serialized owner
; caller supplies acceptance from its once-produced result, not a host guess.
; Capture of the offered source and any query reference precede that result.
(in-package "ACL2")
(include-book "index-connection-issuer")

(defun fn-icr-repin-preflight (id old-token new-token fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let ((receipt (fn-ibp-connection-pending fn-index-backing)))
  (cond
   ((not (and (natp id) (fn-ich-tokenp old-token) (fn-ich-tokenp new-token)
              (not (equal old-token new-token))
              (fn-omk-widthp receipt 8)
              (eq (fn-omk-at 0 receipt) :connection-reservation)
              (equal (fn-omk-at 1 receipt) new-token)
              (equal (fn-omk-at 2 receipt) id))) :stale)
   ((not (eq (fn-omk-at 6 receipt) :source-owned)) :recovery-required)
   ; Old lookup, new finish, old close, then four settlement traversals.
   ((< fuel (* 7 (+ 1 (fn-ibp-slot-depth fn-index-backing)))) :yield)
   (t :ready))))

; This does not close the logical connection: it retires its OLD holder.
; :repinned means that holder actually settled; :repinned-held means its
; aliases still own the exact pin/grant and the caller retains OLD-TOKEN.
; Any other outcome after acceptance fences the owner with BOTH tokens held.
; In particular a raw escape is not permission to repeat this transition.
(defun fn-icr-repin-accept
 (id old-token new-token fuel fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard (natp fuel)))
 (let ((ready (fn-icr-repin-preflight id old-token new-token fuel fn-index-backing)))
  (if (not (eq ready :ready))
      (mv ready fuel fn-index-backing fn-page-read-pool)
   (mv-let (found old-row left) (fn-ibp-connection-read old-token fuel fn-index-backing)
    (mv-let (source old-pin) (fn-ich-row-source id old-row)
     (declare (ignore old-pin))
     (if (not (and (eq found :present) (eq source :current)))
         (mv :recovery-required left fn-index-backing fn-page-read-pool)
      (mv-let (finished remaining fn-index-backing)
       (fn-icr-finish-open id new-token (nfix left) fn-index-backing)
       (if (not (eq finished :opened))
           (mv :recovery-required remaining fn-index-backing fn-page-read-pool)
        (mv-let (closed ignored after fn-index-backing)
         (fn-ibp-connection-event old-token :close id nil (nfix remaining) fn-index-backing)
         (declare (ignore ignored))
         (if (not (eq closed :closing))
             (mv :recovery-required after fn-index-backing fn-page-read-pool)
          (mv-let (settled final fn-index-backing fn-page-read-pool)
           (fn-icr-settle old-token (nfix after) fn-index-backing fn-page-read-pool)
           (mv (case settled
                 (:released :repinned)
                 (:held :repinned-held)
                 (otherwise :recovery-required))
               final fn-index-backing fn-page-read-pool))))))))))))

(defun fn-mio-connection-repin-accept
 (id old-token new-token fuel fn-mio$c fn-page-read-pool)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool) :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing fn-page-read-pool)
  (fn-icr-repin-accept id old-token new-token fuel fn-index-backing fn-page-read-pool)
  (mv word left fn-mio$c fn-page-read-pool)))
