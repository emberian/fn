; Operational writer publication boundary. Builder input is the provider's
; registered private continuation, never a host root/row setter. Full builder
; issuance/page construction and the installed runtime gate remain open.
(in-package "ACL2")
(logic)
(include-book "index-backing-generations")

; Builder20: tag,phase,newGen,oldGen,key,pages,preC,pcToken,assigned8,
; tableRoot,tableDepth,tableID,rowRoot,rowDepth,rowID,numberRoot,numberID,
; ready-count,physical continuation,shared reservation receipt.
(defun fn-ibp-writer-ready-p (builder pc)
 (declare (xargs :guard t))
 (and (fn-omk-widthp builder 20)
      (eq (fn-omk-at 0 builder) :index-builder)
      (eq (fn-omk-at 1 builder) :ready)
      (fn-ibp-generation-tokenp (fn-omk-at 2 builder))
      (or (null (fn-omk-at 3 builder))
          (fn-ibp-generation-tokenp (fn-omk-at 3 builder)))
      (natp (fn-omk-at 6 builder))
      (equal (fn-omk-at 6 builder) (fn-pc-expected pc))
      (equal (fn-omk-at 7 builder) (fn-pc-token pc))
      (equal (fn-omk-at 17 builder) (+ 1 (fn-omk-at 6 builder)))
      (let ((assigned (fn-omk-at 8 builder)))
       (and (fn-omk-widthp assigned 8)
            (eq (fn-omk-at 0 assigned) :assigned)
            (equal (fn-omk-at 2 assigned) (fn-pc-token pc))
            (equal (fn-omk-at 3 assigned) (fn-pc-expected pc))))))

(defun fn-ibp-node-generation-publish (token publication fuel address depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
                 :guard (and (natp fuel) (natp address) (natp depth))))
 (cond ((<= fuel depth) (mv :yield fuel fn-ibp-node))
       ((zp depth)
        (if (not (and (zp address)
                      (fn-ibp-node-children-boundp 'fn-ibp-generation-segment fn-ibp-node)))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-generation-segment
                       (fn-ibp-node-children-get 'fn-ibp-generation-segment fn-ibp-node
                                                 (create-fn-ibp-generation-segment))))
           (status fn-ibp-generation-segment)
           (fn-ibp-generation-install-publication token publication fn-ibp-generation-segment)
           (mv status (- fuel 1) fn-ibp-node))))
       ((evenp address)
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-left
                       (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                                 (create-fn-ibp-node-left))))
           (status remaining fn-ibp-node-left)
           (fn-ibp-node-generation-publish token publication (- fuel 1)
                                            (floor address 2) (- depth 1) fn-ibp-node-left)
           (mv status remaining fn-ibp-node))))
       (t
        (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
            (mv :unavailable fuel fn-ibp-node)
          (stobj-let ((fn-ibp-node-right
                       (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                                 (create-fn-ibp-node-right))))
           (status remaining fn-ibp-node-right)
           (fn-ibp-node-generation-publish token publication (- fuel 1)
                                            (floor address 2) (- depth 1) fn-ibp-node-right)
           (mv status remaining fn-ibp-node))))))
(verify-guards fn-ibp-node-generation-publish)

(defun fn-ibp-generation-publish (token publication fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let ((depth (fn-ibp-slot-depth fn-index-backing)))
  (if (not (fn-ibp-generation-tokenp token))
      (mv :stale fuel fn-index-backing)
    (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
      (status remaining fn-ibp-node)
      (fn-ibp-node-generation-publish token publication fuel (- (nth 2 token) 1) depth fn-ibp-node)
      (mv status remaining fn-index-backing)))))

; Read the registered child before any durable publication mutation.  The
; caller preflights the entire bounded traversal envelope, so a small quantum
; leaves the old current association and the ready builder untouched.
(defun fn-ibp-generation-read (token fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let ((depth (fn-ibp-slot-depth fn-index-backing)))
  (if (not (fn-ibp-generation-tokenp token))
      (mv :stale nil fuel)
    (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
     (status row remaining)
     (fn-ibp-node-generation-read token fuel (- (nth 2 token) 1) depth fn-ibp-node)
     (mv status row remaining)))))

(defun fn-ibp-writer-publication (builder pc frontier version visibility row)
 (declare (xargs :guard t))
 (fn-ipub-make (fn-omk-at 1 (fn-omk-at 2 builder))
   (fn-omk-at 4 builder) (fn-omk-at 5 builder)
   (fn-omk-at 17 builder) frontier version
   (fn-omk-at 9 builder) (fn-omk-at 10 builder) (fn-omk-at 11 builder)
   (fn-omk-at 12 builder) (fn-omk-at 13 builder) (fn-omk-at 14 builder)
   (fn-omk-at 15 builder) (fn-omk-at 16 builder)
   (fn-pc-token pc) visibility (fn-omk-at 9 row) (fn-omk-at 10 row)))

; INTERNAL completion adapter. PC/F/V/visibility must be obtained from the
; actual completed owner transition. This is not a host-supplied-root entry.
; Its caller must also carry the builder write/coverage invariant; the ready
; shape check below deliberately does not claim that invariant by inspection.
(defun fn-ibp-writer-complete (pc frontier version visibility fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)
                 :verify-guards nil))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (current (fn-ibp-current fn-index-backing))
        (new (fn-omk-at 2 builder)) (old (fn-omk-at 3 builder))
        (depth (fn-ibp-slot-depth fn-index-backing)))
  (cond
   ((< fuel (* 4 (+ 1 depth))) (mv :yield fuel fn-index-backing))
   ((not (and (fn-ibp-writer-ready-p builder pc)
              (natp frontier) (natp version) (not (equal new old))
              (if old
                  (and (fn-omk-widthp current 3)
                       (eq (fn-omk-at 0 current) :installed-publication)
                       (equal (fn-omk-at 1 current) old))
                (null current))))
    (mv :recovery-required fuel fn-index-backing))
   (t
    (mv-let (word row remaining) (fn-ibp-generation-read new fuel fn-index-backing)
     (if (not (and (eq word :present) (natp remaining)
                   (eq (fn-omk-at 7 row) :building)
                   (equal (fn-omk-at 6 row) 1)))
         (mv :recovery-required fuel fn-index-backing)
       (mv-let (old-word old-row remaining)
        (if old (fn-ibp-generation-read old remaining fn-index-backing)
          (mv :present nil remaining))
        (let ((publication
               (fn-ibp-writer-publication builder pc frontier version visibility row)))
         (if (not (and (natp remaining) (fn-ipub-shapep publication)
                       (eq old-word :present)
                       (or (null old)
                           (and (eq (fn-omk-at 7 old-row) :live)
                                (equal (fn-omk-at 3 old-row) 1)))))
             (mv :recovery-required fuel fn-index-backing)
           (mv-let (status remaining fn-index-backing)
            (fn-ibp-generation-publish new publication remaining fn-index-backing)
            (if (not (and (eq status :published) (natp remaining)))
                (mv :recovery-required fuel fn-index-backing)
              (mv-let (drop-word ignored remaining fn-index-backing)
               (if old
                   (fn-ibp-generation-reference old :drop :current nil remaining fn-index-backing)
                 (mv :live nil remaining fn-index-backing))
               (declare (ignore ignored))
               (if (not (member-eq drop-word '(:live :retiring)))
                   (mv :recovery-required fuel fn-index-backing)
                 (let* ((fn-index-backing
                          (update-fn-ibp-current
                            (list :installed-publication new publication) fn-index-backing))
                        (fn-index-backing (update-fn-ibp-builder nil fn-index-backing)))
                  (mv :published remaining fn-index-backing))))))))))))))
)
(verify-guards fn-ibp-writer-complete)
