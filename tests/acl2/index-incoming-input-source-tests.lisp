; Actual exported controller/source calls over constructed internal model state.
; :copied outcomes are fixture observations, not native octet-copy evidence.
(in-package "ACL2")
(include-book "../../books/index-incoming-input-source")

(defun-nx iiqt-copy-ticks (n token copy)
 (declare (xargs :measure (nfix n)))
 (if (zp n) copy
  (let* ((next (mv-list 5 (fn-input-copy-next token copy)))
         (ack (mv-list 2 (fn-input-copy-ack token (nth 1 next) (nth 2 next)
                          (nth 3 next) :copied (nth 4 next)))))
   (iiqt-copy-ticks (1- n) token (nth 1 ack)))))

(defun-nx iiqt-input-source-fixture (ticks)
 (let* ((ledger (fn-prl-make '(65536 0 0 0 8)))
        (issued (mv-list 4 (fn-ioh-admit ledger nil '(32768 0 0 0 1))))
        (holder (nth 1 issued))
        (opened (mv-list 2 (fn-input-copy-open holder 8193 16384 4096
                            (create-fn-input-copy))))
        (copy (iiqt-copy-ticks ticks holder (nth 1 opened)))
        (row (list holder :setup '(32768 0 0 0 1) (list :incoming-controller holder)))
        (row (if (equal ticks 3) (mv-nth 1 (fn-ioh-seal row holder)) row))
        (descriptor (fn-ibc-descriptor 97 16384))
        (pool (update-fn-prp-incoming-slot (fn-ibc-carrier descriptor row)
                (fn-owner-page-read-keep-ledger (nth 2 issued) (create-fn-page-read-pool))))
        (context (list :incoming-context holder 4 nil "<wide@test>" nil nil nil nil nil))
        (result (mv-list 2 (fn-iiq-completed-input-source context copy pool))))
  (list result context copy pool)))

(defun-nx iiqt-wide-input-complete-antecedent-and-conclusion ()
 (let* ((fixture (iiqt-input-source-fixture 3))
        (result (nth 0 fixture)) (context (nth 1 fixture))
        (copy (nth 2 fixture)) (pool (nth 3 fixture))
        (source (nth 1 result)) (holder (fn-cp-nth 1 context))
        (view (fn-cp-nth 5 source)))
  (and (fn-input-copy-p copy) (fn-page-read-poolp pool)
       (equal (nth 0 result) :source-current)
       (equal (fn-cp-nth 1 source) holder)
       (equal (fn-cp-nth 2 source) (fn-owner-incoming-backing pool))
       (fn-owner-incoming-copy-associatedp holder copy pool)
       (equal (fn-ioh-access (fn-owner-incoming-row pool) holder :read) :holder-readonly)
       (equal (fn-prl-nth 0 view) holder)
       (equal (fn-prl-nth 6 view) :complete)
       (equal (fn-prl-nth 1 view) (fn-prl-nth 4 view))
       (null (fn-prl-nth 5 view))
       (<= (fn-prl-nth 1 view) (fn-prl-nth 2 view))
       (equal (fn-prl-nth 1 view) 8193) (> (fn-prl-nth 1 view) 4096)
       (equal (fn-cp-nth 1 (fn-cp-nth 2 source)) 97)
       (not (equal 97 (fn-cp-nth 1 holder))))))
(defthm iiqt-wide-input-positive
 (iiqt-wide-input-complete-antecedent-and-conclusion) :rule-classes nil
 :hints (("Goal" :expand ((:free (token copy) (iiqt-copy-ticks 3 token copy))
                          (:free (token copy) (iiqt-copy-ticks 2 token copy))
                          (:free (token copy) (iiqt-copy-ticks 1 token copy))
                          (:free (token copy) (iiqt-copy-ticks 0 token copy))))))

(defun-nx iiqt-incomplete-input-hypothesis-removal ()
 (let* ((fixture (iiqt-input-source-fixture 2))
        (result (nth 0 fixture)) (source (nth 1 result))
        (holder (fn-cp-nth 1 (nth 1 fixture))))
  (and (not (equal (nth 0 result) :source-current))
       (equal (nth 0 result) :source-unavailable)
       ; This failed conjunct affirmatively refutes the complete conclusion.
       (not (equal (fn-cp-nth 1 source) holder)))))
(defthm iiqt-incomplete-input-removal-tooth
 (iiqt-incomplete-input-hypothesis-removal) :rule-classes nil
 :hints (("Goal" :expand ((:free (token copy) (iiqt-copy-ticks 2 token copy))
                          (:free (token copy) (iiqt-copy-ticks 1 token copy))
                          (:free (token copy) (iiqt-copy-ticks 0 token copy))))))
