; SOURCE MODEL: outgoing storage/job are seeded, not admission authority.
(in-package "ACL2")
(include-book "../../books/receiver-turn-controller")
(defconst *fn-rxpa-provider* '(nil ((:rx-capacity 0 0 4096) 0 4096)))
(defconst *fn-rxpa-idle* '(nil nil :idle nil nil (:receiver-install (:rx-capacity 0 0 4096) 0)))
(defconst *fn-rxpa-pool*
 (list (list (fn-prl-build '(8192 0 0 0 8) '(0 0 0 0 1) 1 nil '(4608 0 0 0 0))
             nil nil nil nil) :served nil))
(defthm fn-rxpa-output-current-episode-and-busy-literal
(let* ((rxpa-start  (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
   *fn-rxpa-provider* *fn-rxpa-idle* *fn-rxpa-pool*))
(rxpa-next  (fn-owner-rx-turn-copy-next (mv-nth 1 rxpa-start) 6 nil 16
  *fn-rxpa-provider* (mv-nth 2 rxpa-start) (mv-nth 3 rxpa-start)))
(rxpa-filled  (fn-owner-rx-turn-copy-ack (mv-nth 1 rxpa-start) 0 6 :copied
   (update-nth 0 '(1 2 3 4 5 6) (mv-nth 4 rxpa-next))
   (mv-nth 5 rxpa-next) (mv-nth 6 rxpa-next)))
(rxpa-acquired  (fn-owner-rx-turn-parser-acquire (mv-nth 1 rxpa-start) :preOC :wire
   (mv-nth 1 rxpa-filled) (mv-nth 2 rxpa-filled) (mv-nth 3 rxpa-filled))))
 (let* ((ticket (mv-nth 1 rxpa-start)) (pool (mv-nth 2 rxpa-acquired))
        (stage (fn-owner-rx-turn-parser-stage ticket :actualRC (mv-nth 1 rxpa-filled) (mv-nth 1 rxpa-acquired) pool))
        (finish (fn-owner-rx-turn-parser-finish ticket :wire-after
                    '(:served-step nil t nil nil 0 nil nil)
                    (mv-nth 1 stage) (mv-nth 2 stage) pool))
        (episode (mv-nth 1 finish)) (provider (mv-nth 2 finish)) (turn (mv-nth 3 finish))
        ; SOURCE MODEL storage only, not an admitted outgoing allocation.
        (bundle (list :reader-response-roots (fn-rxt-job turn) nil '(:output-fixture)))
        (held (update-fn-rxt-output-bundle bundle turn))
        (busy (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
                 *fn-rxpa-provider* (update-fn-rxt-output-bundle bundle *fn-rxpa-idle*)
                 *fn-rxpa-pool*)))
  (and (equal (mv-nth 0 stage) :parser-staged)
       (equal (mv-nth 0 finish) :response-recorded)
       (null (fn-rxp-capacity provider))
       (equal (fn-owner-rx-turn-response-source episode provider turn pool)
              (fn-rxt-source turn))
       (not (fn-owner-rx-turn-parser-acquirablep ticket provider turn pool))
       (null (fn-owner-rx-turn-response-source '(:receiver-response (:receiver-turn 1) 0) provider turn pool))
       (null (fn-owner-rx-turn-response-source '(:receiver-response (:receiver-turn 9) 1) provider turn pool))
       (equal (fn-owner-rx-turn-response-result episode provider turn pool)
              (list :response-result (fn-rxt-source turn) :preOC :actualRC
                    '(:served-step nil t nil nil 0 nil nil)))
       (equal (fn-owner-rx-turn-response-result '(:receiver-response (:receiver-turn 1) 0) provider turn pool)
              '(:receiver-unavailable nil nil nil nil))
       (equal (fn-owner-rx-turn-output-current episode provider held pool)
              (list :output-retained bundle))
       (equal (fn-owner-rx-turn-output-current
                 '(:receiver-response (:receiver-turn 1) 0) provider held pool)
              '(:receiver-unavailable nil))
       (equal (mv-nth 0 busy) :receiver-turn-busy)
       (null (mv-nth 1 busy))
       (equal (mv-nth 2 busy) (update-fn-rxt-output-bundle bundle *fn-rxpa-idle*))
       (equal (mv-nth 3 busy) *fn-rxpa-pool*)
       (not (fn-rxt-live-claim-p ticket *fn-rxpa-provider*
                 (update-fn-rxt-output-bundle bundle (mv-nth 2 rxpa-start)) pool))
       (equal (mv-nth 4 finish) pool))))
 :rule-classes nil)
