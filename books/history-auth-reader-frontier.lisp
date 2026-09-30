; Proof-only physical read ordering for the actual page digest machine.
(in-package "ACL2")
(include-book "pagestore-digest-cursor-domain")
(local (include-book "arithmetic/top" :dir :system))

(defun-nx fn-hsr-digest-frontier (pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (case (pgs-dc-mode pgs-digest-state)
    ((:node :split) (pgs-dc-start pgs-digest-state))
    (:chunk (pgs-dc-pos pgs-digest-state))
    (otherwise (pgs-dc-end pgs-digest-state))))

; A left frame's current child ends at its pending right child start. A right
; frame's current child ends at its outer end. Recursing accounts for every
; ancestor, not just the next read's branch. No ghost list executes in a guard.
(defun-nx fn-hsr-digest-end-stackp (depth end total pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix depth) :verify-guards nil))
  (if (zp depth) (equal end total)
    (let* ((index (1- depth)) (frame (pgs-dc-framesi index pgs-digest-state))
           (side (fn-b3-nthx 0 frame)) (right (fn-b3-nthx 1 frame))
           (outer-end (fn-b3-nthx 2 frame)))
      (and (member-eq side '(:left :right))
           (natp right) (natp outer-end) (<= right outer-end)
           (equal end (if (equal side :left) right outer-end))
           (fn-hsr-digest-end-stackp index outer-end total pgs-digest-state)))))

(defun-nx fn-hsr-digest-orderp (pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (and (member-eq (pgs-dc-mode pgs-digest-state) '(:node :split :chunk :return :root :done))
       (natp (pgs-dc-total pgs-digest-state)) (natp (pgs-dc-start pgs-digest-state))
       (natp (pgs-dc-pos pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))
       (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
       (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
       (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
       (natp (pgs-dc-depth pgs-digest-state)) (<= (pgs-dc-depth pgs-digest-state) 64)
       (implies (member-eq (pgs-dc-mode pgs-digest-state) '(:root :done))
                (equal (pgs-dc-depth pgs-digest-state) 0))
       (fn-hsr-digest-end-stackp (pgs-dc-depth pgs-digest-state)
                                (pgs-dc-end pgs-digest-state)
                                (pgs-dc-total pgs-digest-state) pgs-digest-state)))

(local
 (defthm fn-hsr-digest-stack-scalar-update
  (implies (and (natp field) (not (equal field *pgs-dc-framesi*)))
           (equal (fn-hsr-digest-end-stackp depth end total (update-nth field value pgs-digest-state))
                  (fn-hsr-digest-end-stackp depth end total pgs-digest-state)))
  :hints (("Goal" :induct (fn-hsr-digest-end-stackp depth end total pgs-digest-state)
                  :expand ((fn-hsr-digest-end-stackp depth end total (update-nth field value pgs-digest-state)))
                  :in-theory (e/d (fn-hsr-digest-end-stackp pgs-dc-framesi)
                                   (nth update-nth fn-b3-nthx))))))
(local
 (defthm fn-hsr-digest-stack-frame-update-prefix
  (implies (and (natp index) (<= (nfix depth) index))
           (equal (fn-hsr-digest-end-stackp depth end total
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                  (fn-hsr-digest-end-stackp depth end total pgs-digest-state)))
  :hints (("Goal" :induct (fn-hsr-digest-end-stackp depth end total pgs-digest-state)
                  :expand ((:free (end cursor) (fn-hsr-digest-end-stackp depth end total cursor)))
                  :in-theory (e/d (pgs-dc-framesi (:induction fn-hsr-digest-end-stackp))
                                   ((:definition fn-hsr-digest-end-stackp) nth update-nth fn-b3-nthx))))))
(local
 (defthm fn-hsr-digest-stack-top-unfolds
  (implies (and (posp depth) (fn-hsr-digest-end-stackp depth end total pgs-digest-state))
           (let ((frame (pgs-dc-framesi (- depth 1) pgs-digest-state)))
             (and (member-eq (fn-b3-nthx 0 frame) '(:left :right))
                  (natp (fn-b3-nthx 1 frame)) (natp (fn-b3-nthx 2 frame))
                  (<= (fn-b3-nthx 1 frame) (fn-b3-nthx 2 frame))
                  (equal end (if (equal (fn-b3-nthx 0 frame) :left)
                                 (fn-b3-nthx 1 frame) (fn-b3-nthx 2 frame)))
                  (fn-hsr-digest-end-stackp (- depth 1) (fn-b3-nthx 2 frame) total pgs-digest-state))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-hsr-digest-end-stackp depth end total pgs-digest-state))
                  :in-theory (disable fn-hsr-digest-end-stackp fn-b3-nthx)))))
(local
 (defthm fn-hsr-digest-stack-top-update
  (implies (and (natp index) (equal depth (+ 1 index)))
           (equal (fn-hsr-digest-end-stackp depth end total
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                  (and (member-eq (fn-b3-nthx 0 frame) '(:left :right))
                       (natp (fn-b3-nthx 1 frame)) (natp (fn-b3-nthx 2 frame))
                       (<= (fn-b3-nthx 1 frame) (fn-b3-nthx 2 frame))
                       (equal end (if (equal (fn-b3-nthx 0 frame) :left) (fn-b3-nthx 1 frame) (fn-b3-nthx 2 frame)))
                       (fn-hsr-digest-end-stackp index (fn-b3-nthx 2 frame) total pgs-digest-state))))
  :hints (("Goal" :expand ((fn-hsr-digest-end-stackp depth end total
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                     (:free (cursor) (fn-hsr-digest-end-stackp (+ 1 index) end total cursor)))
                  :in-theory (e/d (pgs-dc-framesi)
                                   (nth update-nth fn-hsr-digest-end-stackp fn-b3-cv8 expt))))))

(defthm fn-hsr-digest-begin-establishes-order
  (implies (natp nb)
           (fn-hsr-digest-orderp (pgs-dc-begin sel base nb capture lease pgs-digest-state)))
  :hints (("Goal" :in-theory (enable fn-hsr-digest-orderp fn-hsr-digest-end-stackp pgs-dc-begin))))

(defthm fn-hsr-digest-step-preserves-order
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (fn-hsr-digest-orderp pgs-digest-state))
           (fn-hsr-digest-orderp (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal"
           :use ((:instance pgs-dcd-top-frame-unfolds
                            (depth (pgs-dc-depth pgs-digest-state))
                            (total (pgs-dc-total pgs-digest-state)))
                 (:instance fn-hsr-digest-stack-top-unfolds
                            (depth (pgs-dc-depth pgs-digest-state))
                            (end (pgs-dc-end pgs-digest-state))
                            (total (pgs-dc-total pgs-digest-state)))
                 (:instance pgs-dcd-powerp-bound
                            (power (pgs-dc-power pgs-digest-state))
                            (limit (- (- limit (pgs-dc-depth pgs-digest-state)) 1))))
           :in-theory (e/d (fn-hsr-digest-orderp pgs-dcd-domainp pgs-dc-step
                            pgs-dc-framesi update-pgs-dc-framesi fn-b3-nthx)
                           (nth update-nth fn-hsr-digest-end-stackp fn-b3-cv8 expt
                            pgs-dcd-framesp pgs-dcd-powerp pgs-dcd-powerp-bound pgs-dcd-top-frame-unfolds
                            fn-b3-output fn-b3-output-cv fn-b3-output-root pgs-octets-be-nat))
           :do-not-induct t)))

(defthm fn-hsr-digest-step-advances-exact-read-frontier
  (implies (fn-hsr-digest-orderp pgs-digest-state)
           (equal (fn-hsr-digest-frontier (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (+ (fn-hsr-digest-frontier pgs-digest-state)
                     (pgs-dc-read-demand pgs-digest-state))))
  :hints (("Goal"
           :use ((:instance fn-hsr-digest-stack-top-unfolds
                            (depth (pgs-dc-depth pgs-digest-state))
                            (end (pgs-dc-end pgs-digest-state))
                            (total (pgs-dc-total pgs-digest-state))))
           :in-theory (e/d (fn-hsr-digest-frontier fn-hsr-digest-orderp pgs-dc-step
                            pgs-dc-read-demand pgs-dc-needs-block pgs-dc-framesi fn-b3-nthx)
                           (nth update-nth fn-hsr-digest-end-stackp fn-b3-cv8 expt
                            pgs-dcd-framesp pgs-dcd-powerp fn-b3-output fn-b3-output-cv
                            fn-b3-output-root pgs-octets-be-nat))
           :do-not-induct t)))
