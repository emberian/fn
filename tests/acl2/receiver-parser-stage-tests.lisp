; Source-model witnesses only; supplied demand is not runtime authority.
(in-package "ACL2")
(include-book "../../books/receiver-turn-controller")
(defconst *fn-rxpa-provider* '(nil ((:rx-capacity 0 0 4096) 0 4096)))
(defconst *fn-rxpa-idle* '(nil nil :idle nil nil (:receiver-install (:rx-capacity 0 0 4096) 0)))
(defconst *fn-rxpa-pool*
 (list (list (fn-prl-build '(8192 0 0 0 8) '(0 0 0 0 1) 1 nil '(4608 0 0 0 0))
             nil nil nil nil) :served nil))
(defthm fn-rxpa-stage-finish-full-positive-source-model-literal
 (let* ((rxpa-start  (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
   *fn-rxpa-provider* *fn-rxpa-idle* *fn-rxpa-pool*))
(rxpa-next  (fn-owner-rx-turn-copy-next (mv-nth 1 rxpa-start) 6 nil 16
  *fn-rxpa-provider* (mv-nth 2 rxpa-start) (mv-nth 3 rxpa-start)))
(rxpa-filled  (fn-owner-rx-turn-copy-ack (mv-nth 1 rxpa-start) 0 6 :copied
   (update-nth 0 '(1 2 3 4 5 6) (mv-nth 4 rxpa-next))
   (mv-nth 5 rxpa-next) (mv-nth 6 rxpa-next)))
(rxpa-acquired  (fn-owner-rx-turn-parser-acquire (mv-nth 1 rxpa-start) :preOC :wire
   (mv-nth 1 rxpa-filled) (mv-nth 2 rxpa-filled) (mv-nth 3 rxpa-filled))))
 (let* ((ticket (mv-nth 1 rxpa-start))
        (pool (mv-nth 2 rxpa-acquired))
        (stage (fn-owner-rx-turn-parser-stage ticket :actualRC (mv-nth 1 rxpa-filled) (mv-nth 1 rxpa-acquired) pool))
        (read (fn-owner-rx-turn-parser-staged-rc ticket (mv-nth 1 stage) (mv-nth 2 stage) (mv-nth 3 stage)))
        (finish (fn-owner-rx-turn-parser-finish ticket :wire-after '(:served-step nil nil nil nil 3 nil nil)
                  (mv-nth 1 stage) (mv-nth 2 stage) (mv-nth 3 stage))))
  (and (equal (mv-nth 0 stage) :parser-staged)
       (equal (fn-rxt-phase (mv-nth 2 stage)) :parser-installing)
       (null (fn-rxp-capacity (mv-nth 1 stage)))
       (not (fn-owner-rx-turn-consumablep ticket (mv-nth 1 stage) (mv-nth 2 stage) pool))
       (equal read '(:staged-result :actualRC))
       (equal (mv-nth 3 stage) pool)
       (equal (fn-rxt-source (mv-nth 2 stage)) (fn-rxt-source (mv-nth 1 rxpa-acquired)))
       (equal (fn-rxt-demand (mv-nth 2 stage)) (fn-rxt-demand (mv-nth 1 rxpa-acquired)))
       (equal (mv-nth 0 finish) :parser-progress-recorded)
       (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 3 finish))) :actualRC)
       (equal (fn-prl-nth 4 (fn-rxt-job (mv-nth 3 finish))) 3)
       (equal (fn-rxp-capacity (mv-nth 2 finish)) 4096)
       (equal (mv-nth 4 finish) pool))))
 :rule-classes nil)

(defthm fn-rxpa-progress-before-capacity-cut-source-model-literal
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
        (recorded (fn-owner-rx-turn-parser-progress ticket :actualRC :partialWire
                    '(:served-step nil nil nil nil 3 nil nil)
                    (mv-nth 1 stage) (mv-nth 2 stage) pool))
        (cut-turn (update-fn-rxt-phase :parser-owned (mv-nth 1 recorded)))
        (fenced (fn-owner-rx-turn-parser-fence ticket :actualRC :partialWire
                  '(:served-step nil nil nil nil 3 nil nil) (mv-nth 1 stage) cut-turn pool)))
  (and (equal (mv-nth 0 stage) :parser-staged)
       (equal (mv-nth 0 recorded) :parser-progress-recorded)
       (null (fn-rxp-capacity (mv-nth 1 stage)))
       (equal (fn-rxt-phase cut-turn) :parser-owned)
       (not (fn-owner-rx-turn-consumablep ticket (mv-nth 1 stage) cut-turn pool))
       (equal (fn-prl-nth 4 (fn-rxt-job cut-turn)) 3)
       (equal (fn-prl-nth 7 (fn-rxt-job cut-turn)) :actualRC)
       (equal (mv-nth 0 fenced) :parser-fenced)
       (equal (fn-rxt-phase (mv-nth 2 fenced)) :parser-recovery)
       (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 2 fenced))) :actualRC)
       (equal (mv-nth 3 fenced) pool))))
 :rule-classes nil)

(defthm fn-rxpa-staged-success-removal-source-model-literal
(let* ((rxpa-start  (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
   *fn-rxpa-provider* *fn-rxpa-idle* *fn-rxpa-pool*))
(rxpa-next  (fn-owner-rx-turn-copy-next (mv-nth 1 rxpa-start) 6 nil 16
  *fn-rxpa-provider* (mv-nth 2 rxpa-start) (mv-nth 3 rxpa-start)))
(rxpa-filled  (fn-owner-rx-turn-copy-ack (mv-nth 1 rxpa-start) 0 6 :copied
   (update-nth 0 '(1 2 3 4 5 6) (mv-nth 4 rxpa-next))
   (mv-nth 5 rxpa-next) (mv-nth 6 rxpa-next)))
(rxpa-acquired  (fn-owner-rx-turn-parser-acquire (mv-nth 1 rxpa-start) :preOC :wire
   (mv-nth 1 rxpa-filled) (mv-nth 2 rxpa-filled) (mv-nth 3 rxpa-filled))))
 (let* ((pool (mv-nth 2 rxpa-acquired))
        (out (fn-owner-rx-turn-parser-stage :foreign-ticket :differentRC
               (mv-nth 1 rxpa-filled) (mv-nth 1 rxpa-acquired) pool)))
  (and (not (equal (mv-nth 0 out) :parser-staged))
       (not (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 2 out))) :differentRC))
       (equal (mv-nth 1 out) (mv-nth 1 rxpa-filled))
       (equal (mv-nth 2 out) (mv-nth 1 rxpa-acquired))
       (equal (mv-nth 3 out) pool))))
 :rule-classes nil)

(defthm fn-rxpa-staged-response-source-positive-and-stale-literal
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
        (episode (mv-nth 1 finish)) (provider (mv-nth 2 finish)) (turn (mv-nth 3 finish)))
  (and (equal (mv-nth 0 stage) :parser-staged)
       (equal (mv-nth 0 finish) :response-recorded)
       (null (fn-rxp-capacity provider))
       (equal (fn-owner-rx-turn-response-source episode provider turn pool)
              (fn-rxt-source turn))
       (not (fn-owner-rx-turn-consumablep ticket provider turn pool))
       (null (fn-owner-rx-turn-response-source '(:receiver-response (:receiver-turn 1) 0) provider turn pool))
       (null (fn-owner-rx-turn-response-source '(:receiver-response (:receiver-turn 9) 1) provider turn pool))
       (equal (mv-nth 4 finish) pool))))
 :rule-classes nil)

(defthm fn-rxpa-staged-response-result-positive-and-stale-literal
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
        (episode (mv-nth 1 finish)) (provider (mv-nth 2 finish)) (turn (mv-nth 3 finish)))
  (and (equal (mv-nth 0 stage) :parser-staged)
       (equal (mv-nth 0 finish) :response-recorded)
       (null (fn-rxp-capacity provider))
       (equal (fn-owner-rx-turn-response-source episode provider turn pool)
              (fn-rxt-source turn))
       (not (fn-owner-rx-turn-consumablep ticket provider turn pool))
       (null (fn-owner-rx-turn-response-source '(:receiver-response (:receiver-turn 1) 0) provider turn pool))
       (null (fn-owner-rx-turn-response-source '(:receiver-response (:receiver-turn 9) 1) provider turn pool))
       (equal (fn-owner-rx-turn-response-result episode provider turn pool)
              (list :response-result (fn-rxt-source turn) :preOC :actualRC
                    '(:served-step nil t nil nil 0 nil nil)))
       (equal (fn-owner-rx-turn-response-result '(:receiver-response (:receiver-turn 1) 0) provider turn pool)
              '(:receiver-unavailable nil nil nil nil))
       (equal (mv-nth 4 finish) pool))))
 :rule-classes nil)
