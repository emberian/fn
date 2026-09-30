; Core-only stored-intent composition. No public/native allocating installation.
; Reserved intent must be established by the SAME-pool source-qualified issuer;
; shape and non-NIL allowance are never a qualification receipt by themselves.
(in-package "ACL2")
(include-book "bp-controller-checkpoint-capture")
(include-book "bp-digest-install-intent")
(include-book "page-read-pool-state")

(defun fn-bpdi-stored-source-matches-jobp (source job payload)
 (declare (xargs :guard t))
 (and (consp source) (eq (car source) :bp-checkpoint-stage)
      (consp (cdr source)) (consp (cddr source)) (null (cdddr source))
      (fn-bpcc-job-tokenp job)
      (equal (cadr source) job)
      (equal (fn-bpn-nth 1 (fn-bpck-control-job payload)) job)
      (equal (caddr source) (fn-bpn-nth 3 (fn-bpck-control-job payload)))))

(defun fn-owner-bp-digest-install-plan (controller workspace-token fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
                 :guard-hints (("Goal" :in-theory
                    (disable fn-bpcc-pending-capture fn-bpcc-directory-payload
                             fn-bpdi-payload-intent fn-bpdi-token-matches-jobp
                             fn-bpdi-stored-source-matches-jobp)))))
 (mv-let (word job current claim payload phase revision left)
  (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
  (declare (ignore current claim))
  (let ((intent (fn-bpdi-payload-intent payload)))
   (cond ((not (eq word :checkpoint-current))
          (mv word nil left fn-bp-controller-registry))
         ((not (and (natp left) (<= left fuel) (natp revision)))
          (mv :invalid-checkpoint-carry nil fuel fn-bp-controller-registry))
         ((not (and (member-eq phase '(:reserved :running))
                    (fn-bpdi-token-matches-jobp workspace-token controller job)
                    (equal workspace-token (fn-bpdi-token intent))
                    (eq (fn-bpdi-phase intent) :constructing)
                    (fn-bpdi-stored-source-matches-jobp (fn-bpdi-source intent) job payload)))
          (mv :stale-install nil left fn-bp-controller-registry))
         ((zp left) (mv :yield nil left fn-bp-controller-registry))
         (t (mv :stored-plan
                (list :bp-digest-install workspace-token controller job
                      (fn-bpdi-source intent) :constructing revision)
                (- left 1) fn-bp-controller-registry))))))

(defun fn-owner-bp-digest-install-constructing
 (controller workspace-token fuel fn-bp-controller-registry fn-page-read-pool)
 (declare (xargs :stobjs (fn-bp-controller-registry fn-page-read-pool)
                 :guard (natp fuel)
                 :guard-hints (("Goal" :in-theory
                    (disable fn-bpcc-pending-capture fn-bpcc-directory-payload
                             fn-bpdi-payload-intent fn-bpdi-token-matches-jobp
                             fn-bpdi-stored-source-matches-jobp)))))
 (mv-let (word job current claim payload phase revision left)
  (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
  (declare (ignore current claim))
  (let ((intent (fn-bpdi-payload-intent payload)))
   (cond ((not (eq word :checkpoint-current))
          (mv word left fn-bp-controller-registry fn-page-read-pool))
         ((not (and (natp left) (<= left fuel) (natp revision)))
          (mv :invalid-checkpoint-carry fuel fn-bp-controller-registry fn-page-read-pool))
         ((not (and (member-eq phase '(:reserved :running))
                    (fn-bpdi-token-matches-jobp workspace-token controller job)
                    (equal workspace-token (fn-bpdi-token intent))
                    (eq (fn-bpdi-phase intent) :reserved)
                    (fn-bpdi-stored-source-matches-jobp (fn-bpdi-source intent) job payload)))
          (mv :stale-install left fn-bp-controller-registry fn-page-read-pool))
         ((or (zp left) (<= left (+ 1 (fn-bpcr-depth fn-bp-controller-registry))))
          (mv :yield left fn-bp-controller-registry fn-page-read-pool))
         (t
          (let* ((next-intent (fn-bpdi-make workspace-token :constructing
                                (fn-bpdi-source intent) (fn-bpdi-claim intent)
                                (fn-bpdi-allowance intent)))
                 (next-payload (fn-bpdi-with-intent payload next-intent)))
           (mv-let (result current1 claim1 payload1 phase1 revision1 left1 fn-bp-controller-registry)
            (fn-bpcc-directory-payload controller job :replace revision phase :running
                                       next-payload (- left 1) fn-bp-controller-registry)
            (declare (ignore current1 claim1 payload1 phase1 revision1))
            (mv (if (eq result :checkpoint-updated) :constructing result)
                left1 fn-bp-controller-registry fn-page-read-pool))))))))

(verify-guards fn-bpdi-stored-source-matches-jobp)
(verify-guards fn-owner-bp-digest-install-plan)
(verify-guards fn-owner-bp-digest-install-constructing)
