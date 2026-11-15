; Actual POST -> journal -> cold recovery substitution control. Reuse the
; same two live manifests as the served read control. Preserve the target's
; valid header but replace its entries with another article's valid entries.
; The clean device recovers intact; the substituted device is ambiguous.
; This finite control does not prove cryptographic collision resistance.
(in-package "ACL2")
(include-book "manifest-binding-served-unit")
(defun fn2-rmb-recover (store)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (result fn2-core)
   (b* ((fn2-core (fn2-init-executor *fn2-mbs-profile* :echo nil fn2-core))
        (id (fn2-machine-global-id *fn2-recovery-machine-kind* 0 *fn2-mbs-profile*))
        ((mv code fn2-core) (fn2-recovery-start id 2 0 fn2-core))
        ((mv status & & fn2-core) (fn2-cw-loop 400000 0 0 nil store fn2-core)))
    (mv (list code status (fn2-core-stop-reason fn2-core)
              (equal (fn2-machine-phase id fn2-core) *fn2-recovery-machine-state-done*)
              (nth (fn2-machine-rc-class id fn2-core) *fn2-rec-classes*)
              (fn2-machine-rc-ambiguous id fn2-core)) fn2-core))
   result)))
(defun fn2-rmb-control (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor *fn2-mbs-profile* :echo nil fn2-core))
      ((mv ec fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
        (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
      (post (fn2-cw-crlf-octets (append '("POST") *fn2-mbs-a* '("." "POST") *fn2-mbs-b* '("." "QUIT"))))
      ((mv status clients store fn2-core)
       (fn2-cw-loop 20000 0 0 (fn2-cw-clients (list (list post (list (len post))))) nil fn2-core))
      (posted (fn2-cw-crlf-octets '("200 fn-nntp experimental server ready"
                  "340 send article to be posted" "240 article received OK"
                  "340 send article to be posted" "240 article received OK" "205 closing connection")))
      (header (fn2-mbs-header *fn2-mbs-a*))
      (a (fn2-mbs-find header store))
      (b (fn2-mbs-find (fn2-mbs-header *fn2-mbs-b*) store))
      ((unless (and (eq ec :ok) (eq status :quiet)
                    (equal (fn2-cw-results clients) (list (list posted t)))
                    a b (not (equal (car a) (car b))) (not (equal (cdr a) (cdr b)))))
       (mv (list :setup ec status (and a t) (and b t)) fn2-core))
      (replacement (append header (nthcdr (len header) (cdr b))))
      (clean (fn2-rmb-recover store))
      (changed (fn2-rmb-recover (cons (cons (car a) replacement) store))))
  (mv (if (and (equal clean '(:ok :quiet 0 t :intact 0))
               (equal (take 4 changed) '(:ok :quiet 0 t))
               (not (equal (nth 4 changed) :intact)) (equal (nth 5 changed) 1))
          :ok (list :recovery-control clean changed)) fn2-core)))
(assert-event
 (with-local-stobj fn2-core
  (mv-let (result fn2-core) (fn2-rmb-control fn2-core) (equal result :ok))))
