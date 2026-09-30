; Literal source-core teeth. The :model family is never installed authority;
; actual native getters refuse it. These fixtures exercise the real internal
; evaluator/issuer/role/growth code, not a native allocation qualification.
(in-package "ACL2")
(include-book "../../books/snapshot-initial-custody")
(include-book "../../books/snapshot-maintenance-demand")
(defconst *snit-source* '(:recovery-source 3 11 0))
(defconst *snit-descriptor* '(:recovery-census (:recovery-source 3 11 0) 11 8 nil nil 0 0 nil))
(defconst *snit-table* '((:model-primary :heap :model-body)
                       (:model-caller :stack :model-caller-body)))
(defconst *snit-family*
 '(:runtime-operation-family :initial :model-runtime :model-image :model-profile
   :model-pool :model-creator ((:request :model-primary :model-body 32 2))
   ((:request :model-caller :model-caller-body 8 1)) nil nil nil nil
   :model-borrowed-roots :model-cleanup))
(defconst *snit-ledger* (fn-prl-make '(1000000 1000000 4 4 100)))
(defconst *snit-issued* (mv-list 2 (fn-sni-issue *snit-ledger* *snit-source* *snit-descriptor* *snit-family* *snit-table*)))
(defconst *snit-maintenance* (fn-prl-nth 2 (mv-nth 0 *snit-issued*)))
(defconst *snit-live* (mv-nth 1 *snit-issued*))
(defconst *snit-hpi-source* '(0 (3 0) 0 0))
(defconst *snit-hpi-request* '(:checkpoint-growth (0 (3 0) 0 0) 0 (:maintenance 0 0 0) 0 0 1 49152 0 0))
(defconst *snit-ordinary* (mv-list 3 (fn-pmn-admit *snit-ledger* 0 0 '(72 16384 3 1 1))))

(defthm snit-issued-literal-positive
 (let ((ledger *snit-ledger*) (source *snit-source*) (descriptor *snit-descriptor*) (family *snit-family*) (table *snit-table*))
  (and (equal (fn-prl-nth 0
                  (mv-nth 0 (fn-sni-issue ledger source descriptor family table)))
                  :admitted) (let* ((answer (mv-nth 0 (fn-sni-issue ledger source descriptor family table)))
                  (maintenance (fn-prl-nth 2 answer))
                  (next (mv-nth 1 (fn-sni-issue ledger source descriptor family table)))
                  (context (fn-osrc-source-context
                            (fn-prl-nth 5 descriptor) (fn-prl-nth 6 descriptor)
                            (fn-prl-nth 7 descriptor) :ready)))
             (and (fn-sni-sourcep source descriptor)
                  (equal (fn-prl-nth 1 answer) source)
                  (equal maintenance (fn-prl-nth 3 answer))
                  (equal maintenance
                         (list :maintenance (fn-prl-nth 2 ledger)
                               (fn-prl-nth 1 context) (fn-prl-nth 4 context)))
                  (equal (fn-prl-nth 4 answer) (fn-sni-reserved-roles))
                  (equal (fn-prl-nth 3
                          (cdr (fn-prl-binding maintenance (fn-prl-nth 3 next))))
                         (list :initial source descriptor context family table
                               (fn-sni-reserved-roles)))
                  (fn-sni-livep next source maintenance)))))
 :rule-classes nil)

(defthm snit-issued-remove-admitted
 (let ((ledger *snit-ledger*) (source *snit-source*) (descriptor *snit-descriptor*) (family (update-nth 7 '((:request :model-primary :wrong-body 32 2)) *snit-family*)) (table *snit-table*))
  (and (not (equal (fn-prl-nth 0
                  (mv-nth 0 (fn-sni-issue ledger source descriptor family table)))
                  :admitted)) (not (let* ((answer (mv-nth 0 (fn-sni-issue ledger source descriptor family table)))
                  (maintenance (fn-prl-nth 2 answer))
                  (next (mv-nth 1 (fn-sni-issue ledger source descriptor family table)))
                  (context (fn-osrc-source-context
                            (fn-prl-nth 5 descriptor) (fn-prl-nth 6 descriptor)
                            (fn-prl-nth 7 descriptor) :ready)))
             (and (fn-sni-sourcep source descriptor)
                  (equal (fn-prl-nth 1 answer) source)
                  (equal maintenance (fn-prl-nth 3 answer))
                  (equal maintenance
                         (list :maintenance (fn-prl-nth 2 ledger)
                               (fn-prl-nth 1 context) (fn-prl-nth 4 context)))
                  (equal (fn-prl-nth 4 answer) (fn-sni-reserved-roles))
                  (equal (fn-prl-nth 3
                          (cdr (fn-prl-binding maintenance (fn-prl-nth 3 next))))
                         (list :initial source descriptor context family table
                               (fn-sni-reserved-roles)))
                  (fn-sni-livep next source maintenance))))))
 :rule-classes nil)

(defthm snit-role-claim-literal-positive
 (let ((ledger *snit-live*) (maintenance *snit-maintenance*) (source *snit-source*) (role :source-root) (token '(:model-root 9)))
  (and (equal (mv-nth 0
                  (fn-sni-role-claim ledger maintenance source role token)) :claimed) (let ((next (mv-nth 1
                        (fn-sni-role-claim ledger maintenance source role token))))
             (and (fn-sni-livep next source maintenance)
                  (equal (fn-prl-nth 0 next) (fn-prl-nth 0 ledger))
                  (equal (fn-prl-nth 1 next) (fn-prl-nth 1 ledger))
                  (equal (fn-prl-nth 2 next) (fn-prl-nth 2 ledger))
                  (equal (fn-prl-nth 4 next) (fn-prl-nth 4 ledger))))))
 :rule-classes nil)

(defthm snit-role-remove-claimed
 (let ((ledger *snit-live*) (maintenance *snit-maintenance*) (source '(:recovery-source 4 11 0)) (role :source-root) (token '(:model-root 9)))
  (and (not (equal (mv-nth 0
                  (fn-sni-role-claim ledger maintenance source role token)) :claimed)) (not (let ((next (mv-nth 1
                        (fn-sni-role-claim ledger maintenance source role token))))
             (and (fn-sni-livep next source maintenance)
                  (equal (fn-prl-nth 0 next) (fn-prl-nth 0 ledger))
                  (equal (fn-prl-nth 1 next) (fn-prl-nth 1 ledger))
                  (equal (fn-prl-nth 2 next) (fn-prl-nth 2 ledger))
                  (equal (fn-prl-nth 4 next) (fn-prl-nth 4 ledger)))))))
 :rule-classes nil)

(defthm snit-pmn-growth-unconditional-positive
 (let ((ledger *snit-live*) (token *snit-maintenance*) (delta '(0 32768 0 0 0)))
  (and t (equal
            (fn-prl-nth 3
             (cdr (fn-prl-binding
                   token (fn-prl-nth 3
                          (mv-nth 1 (fn-pmn-grow ledger token delta))))))
            (fn-prl-nth 3
             (cdr (fn-prl-binding token (fn-prl-nth 3 ledger)))))))
 :rule-classes nil)

(defthm snit-pmn-release-custody-positive
 (let ((ledger *snit-live*) (token *snit-maintenance*))
  (and (fn-prl-nth 3
            (cdr (fn-prl-binding token (fn-prl-nth 3 ledger)))) (equal (fn-pmn-release ledger token)
                  (mv :initial-custody-retained ledger))))
 :rule-classes nil)

(defthm snit-pmn-release-remove-custody
 (let ((ledger (mv-nth 2 *snit-ordinary*)) (token (mv-nth 1 *snit-ordinary*)))
  (and (not (fn-prl-nth 3
            (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))) (not (equal (fn-pmn-release ledger token)
                  (mv :initial-custody-retained ledger)))))
 :rule-classes nil)

(defthm snit-hpi-growth-custody-positive
 (let ((ledger *snit-live*) (maintenance *snit-maintenance*) (source *snit-hpi-source*) (stage 0) (request *snit-hpi-request*))
  (and t (equal
   (fn-prl-nth 3
    (cdr (fn-prl-binding
          maintenance (fn-prl-nth 3
                       (mv-nth 1 (fn-osj-grow ledger maintenance source stage request))))))
   (fn-prl-nth 3 (cdr (fn-prl-binding maintenance (fn-prl-nth 3 ledger)))))))
 :rule-classes nil)

(defthm snit-demand-roles-positive
 (let ((family *snit-family*) (table *snit-table*))
  (and (equal (mv-nth 0 (fn-sni-initial-demand family table)) :available) (let ((d (mv-nth 1 (fn-sni-initial-demand family table))))
             (and (fn-prs-vectorp d)
                  (equal (fn-prl-nth 1 d) 16384)
                  (equal (fn-prl-nth 2 d) 3)
                  (equal (fn-prl-nth 3 d) 1)
                  (equal (fn-prl-nth 4 d) 1)))))
 :rule-classes nil)

(defthm snit-demand-remove-available
 (let ((family *snit-family*) (table '((:model-primary :disk :model-body))))
  (and (not (equal (mv-nth 0 (fn-sni-initial-demand family table)) :available)) (not (let ((d (mv-nth 1 (fn-sni-initial-demand family table))))
             (and (fn-prs-vectorp d)
                  (equal (fn-prl-nth 1 d) 16384)
                  (equal (fn-prl-nth 2 d) 3)
                  (equal (fn-prl-nth 3 d) 1)
                  (equal (fn-prl-nth 4 d) 1))))))
 :rule-classes nil)

(defthm snit-role-dependent-hold-refuses-view-release
 (let* ((a (mv-list 2 (fn-sni-role-claim *snit-live* *snit-maintenance* *snit-source* :payload-view '(:model-view 2))))
        (b (mv-list 2 (fn-sni-role-claim (mv-nth 1 a) *snit-maintenance* *snit-source* :workspace '(:model-workspace 0)))))
  (and (equal (mv-nth 0 a) :claimed) (equal (mv-nth 0 b) :claimed)
       (not (fn-sni-role-releasablep (mv-nth 1 b) *snit-maintenance* *snit-source* :payload-view '(:model-view 2)))
       (equal (fn-sni-role-return (mv-nth 1 b) *snit-maintenance* *snit-source* :payload-view '(:model-view 2))
              (mv :initial-custody-retained (mv-nth 1 b))))) :rule-classes nil)
(defthm snit-role-return-retains-all-credit-and-initial
 (let* ((a (mv-list 2 (fn-sni-role-claim *snit-live* *snit-maintenance* *snit-source* :payload-view '(:model-view 2))))
        (b (mv-list 2 (fn-sni-role-return (mv-nth 1 a) *snit-maintenance* *snit-source* :payload-view '(:model-view 2)))))
  (and (equal (mv-nth 0 b) :returned)
       (equal (fn-prl-nth 1 (mv-nth 1 b)) (fn-prl-nth 1 *snit-live*))
       (equal (fn-pmn-release (mv-nth 1 b) *snit-maintenance*)
              (mv :initial-custody-retained (mv-nth 1 b))))) :rule-classes nil)
