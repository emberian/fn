; PRF-1115: nonempty actual configured suffix and literal removals.
(in-package "ACL2")
(include-book "../../books/snapshot-config-alpha")
(defconst *osac-cfg-initial*
 (fn-cnode-initial (fn-cfg-apply-record (fn-cfg-initial) *fn-cfg-default-record*)))
(defconst *osac-cfg-source* '((99) (65 13 10)))
(defconst *osac-cfg-target* '((65 13 10)))
(defconst *osac-cfg-a*
 (fn-cnode-complete
  (fn-cnode-prepare *osac-cfg-initial* 1 0 "<cfg-alpha@example>" 1 '("fn.test")
                    "cfg-alpha" "cfg-subject" "cfg-evidence" 1 841000000)
  0 0 :durable))
(defconst *osac-cfg-b*
 (fn-cnode-complete
  (fn-cnode-prepare *osac-cfg-initial* 1 0 "<cfg-alpha@example>" 0 '("fn.test")
                    "cfg-alpha" "cfg-subject" "cfg-evidence" 1 841000000)
  0 0 :durable))
(defconst *osac-cfg-suffix*
 (list (fn-cfg-record-make 1 1 2
        (list (fn-cfg-create-group "fn.alpha" *fn-cfg-default-policy-id*))
        *fn-cfg-default-stamp*)))
(defthm osac-config-suffix-positive-tooth
 (let ((ra (fn-cpr-loop *osac-cfg-a* *osac-cfg-suffix* nil 1 1))
       (rb (fn-cpr-loop *osac-cfg-b* *osac-cfg-suffix* nil 1 1)))
  (and (fn-cnode-statep *osac-cfg-a*) (fn-cnode-statep *osac-cfg-b*)
       (equal (fn-osa-cnode-alpha *osac-cfg-a* *osac-cfg-source*)
              (fn-osa-cnode-alpha *osac-cfg-b* *osac-cfg-target*))
       (consp *osac-cfg-suffix*)
       (consp (fn-state-articles (fn-node-acceptance (fn-cnode-node *osac-cfg-a*))))
       (not (equal *osac-cfg-a* *osac-cfg-b*))
       (equal (fn-replay-result-kind ra) :ok)
       (equal (fn-cfg-generation (fn-cnode-config (fn-replay-result-node ra))) 2)
       (member-equal "fn.alpha" (fn-cnode-domain (fn-replay-result-node ra)))
       (equal (fn-osa-cpr-result-alpha ra *osac-cfg-source*)
              (fn-osa-cpr-result-alpha rb *osac-cfg-target*))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-osa-cpr-result-alpha fn-osa-cnode-alpha
                                   fn-osa-node-alpha fn-osa-acceptance-alpha
                                   fn-osa-pending-alpha fn-articles-wire-of fn-handle-bytes))))
; Corrupted-state witnesses; they are logical tests, outside execution guards.
(defun osac-cfg-corrupt-payload (cn)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((node (fn-cnode-node cn)) (acc (fn-node-acceptance node))
        (bad-acc (update-nth 2 (list (update-nth 1 -1
                         (car (fn-state-articles acc)))) acc)))
  (fn-cnode-make (update-nth 0 bad-acc node) (fn-cnode-config cn))))
(defthm osac-config-suffix-source-type-removal-tooth
 (let ((a (osac-cfg-corrupt-payload *osac-cfg-a*)) (b *osac-cfg-b*)
       (source '((99) nil)) (target '(nil)))
  (and (not (fn-cnode-statep a)) (fn-cnode-statep b)
       (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target))
       (not (equal (fn-osa-cpr-result-alpha
                      (fn-cpr-loop a *osac-cfg-suffix* nil 1 1) source)
                   (fn-osa-cpr-result-alpha
                      (fn-cpr-loop b *osac-cfg-suffix* nil 1 1) target)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-osa-cpr-result-alpha fn-osa-cnode-alpha
                                   fn-osa-node-alpha fn-osa-acceptance-alpha
                                   fn-osa-pending-alpha fn-articles-wire-of fn-handle-bytes))))
(defthm osac-config-suffix-target-type-removal-tooth
 (let ((a *osac-cfg-a*) (b (osac-cfg-corrupt-payload *osac-cfg-b*))
       (source '((99) nil)) (target '(nil)))
  (and (fn-cnode-statep a) (not (fn-cnode-statep b))
       (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target))
       (not (equal (fn-osa-cpr-result-alpha
                      (fn-cpr-loop a *osac-cfg-suffix* nil 1 1) source)
                   (fn-osa-cpr-result-alpha
                      (fn-cpr-loop b *osac-cfg-suffix* nil 1 1) target)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-osa-cpr-result-alpha fn-osa-cnode-alpha
                                   fn-osa-node-alpha fn-osa-acceptance-alpha
                                   fn-osa-pending-alpha fn-articles-wire-of fn-handle-bytes))))
(defthm osac-config-suffix-incoming-alpha-removal-tooth
 (let ((a *osac-cfg-a*) (b *osac-cfg-initial*)
       (source *osac-cfg-source*) (target *osac-cfg-target*))
  (and (fn-cnode-statep a) (fn-cnode-statep b)
       (not (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target)))
       (not (equal (fn-osa-cpr-result-alpha
                      (fn-cpr-loop a *osac-cfg-suffix* nil 1 1) source)
                   (fn-osa-cpr-result-alpha
                      (fn-cpr-loop b *osac-cfg-suffix* nil 1 1) target)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-osa-cpr-result-alpha fn-osa-cnode-alpha
                                   fn-osa-node-alpha fn-osa-acceptance-alpha
                                   fn-osa-pending-alpha fn-articles-wire-of fn-handle-bytes))))
