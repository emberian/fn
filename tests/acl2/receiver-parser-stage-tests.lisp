; Source-model witnesses only; supplied demand is not runtime authority.
(in-package "ACL2")
(include-book "../../books/receiver-turn-controller")
(defconst *fn-rxpa-provider* '(nil ((:rx-capacity 0 0 4096) 0 4096)))
(defconst *fn-rxpa-idle* '(nil nil :idle nil nil (:receiver-install (:rx-capacity 0 0 4096) 0)))
(defconst *fn-rxpa-pool*
 (list (list (fn-prl-build '(8192 0 0 0 8) '(0 0 0 0 1) 1 nil '(4608 0 0 0 0))
             nil nil nil nil) :served nil
       ;; the allocation epoch (fn-page-read-pool's fields 3-9): active, as
       ;; 19603e149's counter publication requires
       nil :active 0 0 0 0 nil))
(defthm fn-rxpa-stage-finish-positive-source-model-literal
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
