; Constructed internal source fixtures. These are not an installed runtime
; constructor/scratch receipt, persisted publication or native activation.
(in-package "ACL2")
(include-book "../../books/index-incoming-request")

(defconst *iiq-test-context*
 (list :incoming-context (list :incoming 17) 4 nil "<incoming@test>" nil nil nil nil
       (list nil (make-list 32 :initial-element 0) nil)))
(defconst *iiq-test-publication*
 (fn-ipub-make 7 nil 1 0 0 nil nil 0 11 nil 0 12 nil 13 nil nil 0 0))
(defconst *iiq-test-generation* '(:index-generation 7 1 0))
(defconst *iiq-test-demand* '(32 0 0 0 1))

(defun-nx iiq-reservation-positive ()
 (let* ((backing (update-fn-ibp-pool-capacity 1 (create-fn-index-backing)))
        (pool (fn-owner-page-read-keep-ledger
                (fn-prl-make '(1024 8 8 8 16)) (create-fn-page-read-pool)))
        (result (mv-list 4 (fn-iiq-reserve-request *iiq-test-context*
                    *iiq-test-publication* *iiq-test-generation* *iiq-test-demand* backing pool)))
        (receipt (fn-ibp-request-pending (nth 2 result)))
        (ledger (fn-owner-page-read-ledger (nth 3 result))))
  (and (equal (nth 0 result) :reserved)
       (equal (nth 1 result) 1)
       (equal (fn-omk-at 1 receipt) 0)
       (equal (fn-omk-at 2 receipt) 1) (posp (fn-omk-at 2 receipt))
       (equal (fn-prl-nth 2 ledger) 1)
       (equal (fn-prl-nth 1 ledger) *iiq-test-demand*)
       (equal (fn-ibp-request-highwater (nth 2 result)) 0)
       (null (fn-ibp-request-free (nth 2 result)))
       (not (equal (nth 2 result) backing)))))
(defthm iiq-reservation-complete-positive (iiq-reservation-positive) :rule-classes nil)

(defun-nx iiq-reserved-hypothesis-removal ()
 (let* ((backing (update-fn-ibp-pool-capacity 1 (create-fn-index-backing)))
        (pool (fn-owner-page-read-keep-ledger
                (fn-prl-build '(1024 8 8 8 16) '(0 0 0 0 0) 9 nil nil)
                (create-fn-page-read-pool)))
        (result (mv-list 4 (fn-iiq-reserve-request nil *iiq-test-publication*
                    *iiq-test-generation* *iiq-test-demand* backing pool)))
        (receipt (fn-ibp-request-pending (nth 2 result))))
  (and (not (equal (nth 0 result) :reserved))
       (equal (nth 2 result) backing) (equal (nth 3 result) pool)
       (not (and (equal (fn-omk-at 1 receipt) 9)
                 (equal (fn-omk-at 2 receipt) 10)
                 (posp (fn-omk-at 2 receipt))
                 (equal (fn-prl-nth 2 (fn-owner-page-read-ledger (nth 3 result)))
                        (fn-omk-at 2 receipt)))))))
(defthm iiq-reserved-hypothesis-removal-tooth (iiq-reserved-hypothesis-removal)
 :rule-classes nil)
; The positive above affirmatively omits unreserved and fails its custody frame.

(defun-nx iiq-resume-and-scratch-once ()
 (let* ((backing (update-fn-ibp-pool-capacity 1 (create-fn-index-backing)))
        (pool (fn-owner-page-read-keep-ledger
                (fn-prl-make '(1024 8 8 8 16)) (create-fn-page-read-pool)))
        (first (mv-list 4 (fn-iiq-reserve-request *iiq-test-context* *iiq-test-publication*
                           *iiq-test-generation* *iiq-test-demand* backing pool)))
        (resume (mv-list 4 (fn-iiq-reserve-or-resume *iiq-test-context* *iiq-test-publication*
                            *iiq-test-generation* *iiq-test-demand* (nth 2 first) (nth 3 first))))
        (scratch (mv-list 3 (fn-iiq-reserve-scratch 1 '(8 0 0 0 0) (nth 2 first) (nth 3 first))))
        (repeat (mv-list 3 (fn-iiq-reserve-scratch 1 '(8 0 0 0 0) (nth 1 scratch) (nth 2 scratch)))))
  (and (equal first resume)
       (equal (nth 0 scratch) :reserved) (equal scratch repeat)
       (equal (fn-prl-nth 1 (fn-owner-page-read-ledger (nth 2 scratch))) '(40 0 0 0 1))
       (equal (fn-prl-nth 2 (fn-owner-page-read-ledger (nth 2 scratch))) 1)
       (equal (fn-ibp-request-highwater (nth 1 scratch)) 0))))
(defthm iiq-resume-and-scratch-once-positive (iiq-resume-and-scratch-once) :rule-classes nil)

(defun-nx iiq-shape-is-not-runtime-authority ()
 (let ((backing (update-fn-ibp-request-runtime '(:runtime :ready (32 0 0 0 1))
                  (create-fn-index-backing))))
  (equal (mv-list 3 (fn-iiq-installed-runtime-source backing)) '(:unavailable nil nil))))
(defthm iiq-shape-is-not-runtime-authority-positive (iiq-shape-is-not-runtime-authority)
 :rule-classes nil)

; Complete internal producer fixture: actual generation registration and actual
; child adoption. The :source-fixture grant is not an installed runtime issuer.
(defun-nx iiq-complete-internal-capture ()
 (let* ((gs (update-fn-ibp-gs-id 1 (create-fn-ibp-generation-segment)))
        (begun (mv-list 2 (fn-ibp-generation-begin *iiq-test-generation* :source-fixture gs)))
        (arena (mv-list 2 (fn-ibp-generation-capture-arena *iiq-test-generation* 0 0 (nth 1 begun))))
        (installed (mv-list 2 (fn-ibp-generation-install-publication *iiq-test-generation*
                              *iiq-test-publication* (nth 1 arena))))
        (node (fn-ibp-node-children-put 'fn-ibp-generation-segment (nth 1 installed)
                 (create-fn-ibp-node)))
        (node (fn-ibp-node-children-put 'fn-ibp-query-segment
                 (update-fn-ibp-qs-id 1 (create-fn-ibp-query-segment)) node))
        (node (fn-ibp-node-children-put 'fn-query-payload-grants
                 (update-fn-qpg-segment-id 1 (create-fn-query-payload-grants)) node))
        (backing (update-fn-ibp-current
                   (list :installed-publication *iiq-test-generation* *iiq-test-publication*)
                   (update-fn-ibp-pool-capacity 1
                    (update-fn-ibp-registry node (create-fn-index-backing)))))
        (pool (fn-owner-page-read-keep-ledger
                (fn-prl-make '(1024 8 8 8 16)) (create-fn-page-read-pool)))
        (reserved (mv-list 4 (fn-iiq-reserve-request *iiq-test-context* *iiq-test-publication*
                              *iiq-test-generation* *iiq-test-demand* backing pool)))
        (scratch (mv-list 3 (fn-iiq-reserve-scratch 1 '(8 0 0 0 0)
                             (nth 2 reserved) (nth 3 reserved))))
        (retained (mv-list 3 (fn-iiq-retain-generation 100 (nth 1 scratch))))
        (captured (mv-list 5 (fn-iiq-adopt-pending 100 (nth 2 retained) (nth 2 scratch)))))
  (list (nth 0 retained) (nth 0 captured) (nth 1 captured)
        (fn-ibp-request-highwater (nth 3 captured))
        (fn-ibp-request-pending (nth 3 captured))
        (fn-ibp-request-capture (nth 3 captured))
        (fn-prl-nth 1 (fn-owner-page-read-ledger (nth 4 captured)))
        (fn-prl-nth 2 (fn-owner-page-read-ledger (nth 4 captured))))))
(defthm iiq-complete-internal-capture-positive
 (equal (iiq-complete-internal-capture)
 '(:retained :captured (:index-query 1 1 0 7) 1 nil nil (40 0 0 0 1) 1))
 :rule-classes nil)

(defun-nx iiq-adopt-intent-refuses-repeat ()
 (let* ((token '(:index-query 1 1 0 7))
        (backing (update-fn-ibp-request-capture
                  (list :incoming-capture-scratch 1 '(8 0 0 0 0)
                        (list :adopt-intent token)) (create-fn-index-backing)))
        (pool (create-fn-page-read-pool))
        (result (mv-list 5 (fn-iiq-adopt-pending 100 backing pool))))
  (and (equal (nth 0 result) :recovery-required)
       (equal (nth 1 result) token) (equal (nth 2 result) 100)
       (equal (nth 3 result) backing) (equal (nth 4 result) pool))))
(defthm iiq-adopt-intent-refuses-repeat-corrupted-state
 (iiq-adopt-intent-refuses-repeat) :rule-classes nil)

(defun-nx iiq-completed-observation-not-interrupted ()
 (let* ((answer (iiq-complete-internal-capture))
        (marker (nth 5 answer)))
  (and (equal (nth 0 answer) :retained)
       (equal (nth 1 answer) :captured)
       (null marker)
       (not (member-eq (fn-omk-at 0 (fn-omk-at 3 marker))
                      '(:adopt-intent :adopt-uncertain)))
       (not (equal (nth 1 answer) :recovery-required)))))
(defthm iiq-completed-observation-not-interrupted-tooth
 (iiq-completed-observation-not-interrupted) :rule-classes nil)
