; Source-model only: actual source PRS issuance, not NNTP/physical detachment.
(in-package "ACL2")
(include-book "../../books/receiver-turn-controller")
(defconst *fn-rxpa-provider* '(nil ((:rx-capacity 0 0 4096) 0 4096)))
(defconst *fn-rxpa-idle* '(nil nil :idle nil nil (:receiver-install (:rx-capacity 0 0 4096) 0)))
(defconst *fn-rxpa-pool*
 (list (list (fn-prl-build '(8192 0 0 0 8) '(0 0 0 0 1) 1 nil '(4608 0 0 0 0))
             nil nil nil nil) :served nil))
(defthm fn-rxpa-parser-acquire-positive-source-model-literal
 (let* ((rxpa-start  (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
   *fn-rxpa-provider* *fn-rxpa-idle* *fn-rxpa-pool*))
(rxpa-next  (fn-owner-rx-turn-copy-next (mv-nth 1 rxpa-start) 6 nil 16
  *fn-rxpa-provider* (mv-nth 2 rxpa-start) (mv-nth 3 rxpa-start)))
(rxpa-filled  (fn-owner-rx-turn-copy-ack (mv-nth 1 rxpa-start) 0 6 :copied
   (update-nth 0 '(1 2 3 4 5 6) (mv-nth 4 rxpa-next))
   (mv-nth 5 rxpa-next) (mv-nth 6 rxpa-next)))
(rxpa-acquired  (fn-owner-rx-turn-parser-acquire (mv-nth 1 rxpa-start) :preOC :wire
   (mv-nth 1 rxpa-filled) (mv-nth 2 rxpa-filled) (mv-nth 3 rxpa-filled))))
  (and (equal (mv-nth 0 rxpa-start) :admitted)
      (equal (mv-nth 0 rxpa-filled) :receive-recorded)
      (equal (mv-nth 0 rxpa-acquired) :parser-acquired)
      (equal (fn-rxt-phase (mv-nth 1 rxpa-acquired)) :parser-owned)
      (equal (fn-prl-nth 6 (fn-rxt-job (mv-nth 1 rxpa-acquired))) :preOC)
      (null (fn-prl-nth 7 (fn-rxt-job (mv-nth 1 rxpa-acquired))))
      (equal (fn-prl-nth 8 (fn-rxt-job (mv-nth 1 rxpa-acquired))) :wire)))
 :rule-classes nil)
(defthm fn-rxpa-response-positive-source-model-literal
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
        (provider (mv-nth 1 rxpa-filled))
        (turn (mv-nth 1 rxpa-acquired))
        (pool (mv-nth 2 rxpa-acquired))
        (step '(:served-step nil t nil nil 0 nil nil))
        (a (fn-owner-rx-turn-parser-commit ticket :actualRC :currentWire step provider turn pool)))
  (and (equal (mv-nth 0 a) :response-recorded)
       (equal (mv-nth 1 a) '(:receiver-response (:receiver-turn 1) 1))
       (fn-owner-rx-turn-response-currentp (mv-nth 1 a) provider (mv-nth 2 a) pool)
       (not (fn-owner-rx-turn-response-currentp '(:receiver-response (:receiver-turn 1) 0)
                                              provider (mv-nth 2 a) pool))
       (not (fn-owner-rx-turn-consumablep ticket provider (mv-nth 2 a) pool))
       (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 2 a))) :actualRC)
       (equal (fn-prl-nth 8 (fn-rxt-job (mv-nth 2 a))) :currentWire)
       (equal (fn-prl-nth 9 (fn-rxt-job (mv-nth 2 a))) step)
       (equal (mv-nth 3 a) pool))))
 :rule-classes nil)
(defthm fn-rxpa-progress-retains-partial-source-model-literal
 (let* ((rxpa-start  (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
   *fn-rxpa-provider* *fn-rxpa-idle* *fn-rxpa-pool*))
(rxpa-next  (fn-owner-rx-turn-copy-next (mv-nth 1 rxpa-start) 6 nil 16
  *fn-rxpa-provider* (mv-nth 2 rxpa-start) (mv-nth 3 rxpa-start)))
(rxpa-filled  (fn-owner-rx-turn-copy-ack (mv-nth 1 rxpa-start) 0 6 :copied
   (update-nth 0 '(1 2 3 4 5 6) (mv-nth 4 rxpa-next))
   (mv-nth 5 rxpa-next) (mv-nth 6 rxpa-next)))
(rxpa-acquired  (fn-owner-rx-turn-parser-acquire (mv-nth 1 rxpa-start) :preOC :wire
   (mv-nth 1 rxpa-filled) (mv-nth 2 rxpa-filled) (mv-nth 3 rxpa-filled))))
  (let* ((provider (mv-nth 1 rxpa-filled)) (turn (mv-nth 1 rxpa-acquired))
        (pool (mv-nth 2 rxpa-acquired))
        (a (fn-owner-rx-turn-parser-progress (mv-nth 1 rxpa-start) :partialRC :partialWire
             '(:served-step nil nil nil nil 3 nil nil) provider turn pool)))
  (and (equal (mv-nth 0 a) :parser-progress-recorded)
       (equal (fn-rxt-phase (mv-nth 1 a)) :parser-owned)
       (equal (fn-prl-nth 4 (fn-rxt-job (mv-nth 1 a))) 3)
       (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 1 a))) :partialRC)
       (equal (fn-prl-nth 8 (fn-rxt-job (mv-nth 1 a))) :partialWire)
       (equal (fn-prl-nth 10 (fn-rxt-job (mv-nth 1 a))) 0)
       (equal (mv-nth 2 a) pool)
       (equal (mv-nth 0 (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
                         provider (mv-nth 1 a) pool)) :receiver-turn-busy))))
 :rule-classes nil)
(defthm fn-rxpa-zero-nonclosing-response-refusal-source-model-literal
 (let* ((rxpa-start  (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
   *fn-rxpa-provider* *fn-rxpa-idle* *fn-rxpa-pool*))
(rxpa-next  (fn-owner-rx-turn-copy-next (mv-nth 1 rxpa-start) 6 nil 16
  *fn-rxpa-provider* (mv-nth 2 rxpa-start) (mv-nth 3 rxpa-start)))
(rxpa-filled  (fn-owner-rx-turn-copy-ack (mv-nth 1 rxpa-start) 0 6 :copied
   (update-nth 0 '(1 2 3 4 5 6) (mv-nth 4 rxpa-next))
   (mv-nth 5 rxpa-next) (mv-nth 6 rxpa-next)))
(rxpa-acquired  (fn-owner-rx-turn-parser-acquire (mv-nth 1 rxpa-start) :preOC :wire
   (mv-nth 1 rxpa-filled) (mv-nth 2 rxpa-filled) (mv-nth 3 rxpa-filled))))
  (let* ((ticket (mv-nth 1 rxpa-start)) (provider (mv-nth 1 rxpa-filled))
        (turn (mv-nth 1 rxpa-acquired)) (pool (mv-nth 2 rxpa-acquired))
        (step '(:served-step (:retained-effect) nil nil nil 0 nil nil))
        (a (fn-owner-rx-turn-parser-commit ticket :actualRC :currentWire step provider turn pool))
        (f (fn-owner-rx-turn-parser-fence ticket :actualRC :currentWire step provider turn pool)))
  (and (equal a (mv :receiver-unavailable nil turn pool))
       (equal (mv-nth 0 f) :parser-fenced)
       (null (fn-rxp-capacity (mv-nth 1 f)))
       (equal (fn-rxt-phase (mv-nth 2 f)) :parser-recovery)
       (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 2 f))) :actualRC)
       (equal (fn-prl-nth 8 (fn-rxt-job (mv-nth 2 f))) :currentWire)
       (equal (fn-prl-nth 9 (fn-rxt-job (mv-nth 2 f))) step)
       (equal (mv-nth 3 f) pool))))
 :rule-classes nil)

(defthm fn-rxpa-response-success-hypothesis-removal-source-model-literal
 (let* ((rxpa-start  (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
   *fn-rxpa-provider* *fn-rxpa-idle* *fn-rxpa-pool*))
(rxpa-next  (fn-owner-rx-turn-copy-next (mv-nth 1 rxpa-start) 6 nil 16
  *fn-rxpa-provider* (mv-nth 2 rxpa-start) (mv-nth 3 rxpa-start)))
(rxpa-filled  (fn-owner-rx-turn-copy-ack (mv-nth 1 rxpa-start) 0 6 :copied
   (update-nth 0 '(1 2 3 4 5 6) (mv-nth 4 rxpa-next))
   (mv-nth 5 rxpa-next) (mv-nth 6 rxpa-next)))
(rxpa-acquired  (fn-owner-rx-turn-parser-acquire (mv-nth 1 rxpa-start) :preOC :wire
   (mv-nth 1 rxpa-filled) (mv-nth 2 rxpa-filled) (mv-nth 3 rxpa-filled))))
  (let* ((turn (mv-nth 1 rxpa-acquired)) (pool (mv-nth 2 rxpa-acquired))
         (a (fn-owner-rx-turn-parser-commit (mv-nth 1 rxpa-start) :actualRC :currentWire '(:served-step nil nil nil nil 0 nil nil)
                      (mv-nth 1 rxpa-filled) turn pool)))
   (and (equal (mv-nth 0 rxpa-start) :admitted)
        (equal (mv-nth 0 rxpa-acquired) :parser-acquired)
        (not (equal (mv-nth 0 a) :response-recorded))
        (not (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 2 a))) :actualRC)))))
 :rule-classes nil)
(defthm fn-rxpa-progress-success-hypothesis-removal-source-model-literal
 (let* ((rxpa-start  (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
   *fn-rxpa-provider* *fn-rxpa-idle* *fn-rxpa-pool*))
(rxpa-next  (fn-owner-rx-turn-copy-next (mv-nth 1 rxpa-start) 6 nil 16
  *fn-rxpa-provider* (mv-nth 2 rxpa-start) (mv-nth 3 rxpa-start)))
(rxpa-filled  (fn-owner-rx-turn-copy-ack (mv-nth 1 rxpa-start) 0 6 :copied
   (update-nth 0 '(1 2 3 4 5 6) (mv-nth 4 rxpa-next))
   (mv-nth 5 rxpa-next) (mv-nth 6 rxpa-next)))
(rxpa-acquired  (fn-owner-rx-turn-parser-acquire (mv-nth 1 rxpa-start) :preOC :wire
   (mv-nth 1 rxpa-filled) (mv-nth 2 rxpa-filled) (mv-nth 3 rxpa-filled))))
  (let* ((turn (mv-nth 1 rxpa-acquired)) (pool (mv-nth 2 rxpa-acquired))
         (a (fn-owner-rx-turn-parser-progress (mv-nth 1 rxpa-start) :actualRC :currentWire '(:served-step nil t nil nil 0 nil nil)
                      (mv-nth 1 rxpa-filled) turn pool)))
   (and (equal (mv-nth 0 rxpa-start) :admitted)
        (equal (mv-nth 0 rxpa-acquired) :parser-acquired)
        (not (equal (mv-nth 0 a) :parser-progress-recorded))
        (not (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 1 a))) :actualRC)))))
 :rule-classes nil)

(defthm fn-rxpa-response-episode-bound-positive-source-model-literal
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
        (provider (mv-nth 1 rxpa-filled))
        (turn (mv-nth 1 rxpa-acquired))
        (pool (mv-nth 2 rxpa-acquired))
        (step '(:served-step nil t nil nil 0 nil nil))
        (a (fn-owner-rx-turn-parser-commit ticket :actualRC :currentWire step provider turn pool)))
  (and (equal (mv-nth 0 a) :response-recorded)
       (posp (fn-prl-nth 2 (mv-nth 1 a)))
       (<= (fn-prl-nth 2 (mv-nth 1 a)) 4097)
       (equal (mv-nth 1 a) '(:receiver-response (:receiver-turn 1) 1))
       (fn-owner-rx-turn-response-currentp (mv-nth 1 a) provider (mv-nth 2 a) pool)
       (not (fn-owner-rx-turn-response-currentp '(:receiver-response (:receiver-turn 1) 0)
                                              provider (mv-nth 2 a) pool))
       (not (fn-owner-rx-turn-consumablep ticket provider (mv-nth 2 a) pool))
       (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 2 a))) :actualRC)
       (equal (fn-prl-nth 8 (fn-rxt-job (mv-nth 2 a))) :currentWire)
       (equal (fn-prl-nth 9 (fn-rxt-job (mv-nth 2 a))) step)
       (equal (mv-nth 3 a) pool))))
 :rule-classes nil)
(defthm fn-rxpa-response-episode-success-hypothesis-removal-source-model-literal
 (let* ((rxpa-start  (fn-owner-rx-turn-start '(:rx-capacity 0 0 4096) '(256 0 0 0 1)
   *fn-rxpa-provider* *fn-rxpa-idle* *fn-rxpa-pool*))
(rxpa-next  (fn-owner-rx-turn-copy-next (mv-nth 1 rxpa-start) 6 nil 16
  *fn-rxpa-provider* (mv-nth 2 rxpa-start) (mv-nth 3 rxpa-start)))
(rxpa-filled  (fn-owner-rx-turn-copy-ack (mv-nth 1 rxpa-start) 0 6 :copied
   (update-nth 0 '(1 2 3 4 5 6) (mv-nth 4 rxpa-next))
   (mv-nth 5 rxpa-next) (mv-nth 6 rxpa-next)))
(rxpa-acquired  (fn-owner-rx-turn-parser-acquire (mv-nth 1 rxpa-start) :preOC :wire
   (mv-nth 1 rxpa-filled) (mv-nth 2 rxpa-filled) (mv-nth 3 rxpa-filled))))
  (let* ((turn (mv-nth 1 rxpa-acquired)) (pool (mv-nth 2 rxpa-acquired))
         (a (fn-owner-rx-turn-parser-commit (mv-nth 1 rxpa-start) :actualRC :currentWire '(:served-step nil nil nil nil 0 nil nil)
                      (mv-nth 1 rxpa-filled) turn pool)))
   (and (equal (mv-nth 0 rxpa-start) :admitted)
        (equal (mv-nth 0 rxpa-acquired) :parser-acquired)
        (not (equal (mv-nth 0 a) :response-recorded))
        (not (posp (fn-prl-nth 2 (mv-nth 1 a))))
        (not (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 2 a))) :actualRC)))))
 :rule-classes nil)

(defthm fn-rxt-recorded-response-remainder-positive-source-model-literal
 (let ((job '(:receiver-parser (:receiver-turn 1)
              (:receiver-source (:receiver-turn 1) (:rx-capacity 0 0 4096) 0)
              (:receiver-copy 0 6 10) 0 6 :preOC :RC :wire
              (:served-step (:response) nil nil nil 3 nil nil) 1)))
  (and (fn-rxt-parser-jobp job)
       (equal (fn-rxt-recorded-response-continuation job)
              (mv :same-input-remainder 3 6))))
 :rule-classes nil)
(defthm fn-rxt-recorded-response-exposure-terminal-positive-source-model-literal
 (let ((job '(:receiver-parser (:receiver-turn 1)
              (:receiver-source (:receiver-turn 1) (:rx-capacity 0 0 4096) 0)
              (:receiver-copy 0 6 10) 0 6 :preOC :RC :wire
              (:served-step nil nil nil nil 0 nil (52 48 48)) 1)))
  (and (fn-rxt-parser-jobp job)
       (equal (fn-rxt-recorded-response-continuation job)
              (mv :terminal-response 0 6))))
 :rule-classes nil)
(defthm fn-rxt-recorded-response-job-domain-hypothesis-removal-source-model-literal
 (let* ((job '(:receiver-parser (:receiver-turn 1)
              (:receiver-source (:receiver-turn 1) (:rx-capacity 0 0 4096) 0)
              (:receiver-copy 0 -1 10) 0 -1 :preOC :RC :wire
              (:served-step (:response) nil nil nil 7 nil nil) 1))
        (a (fn-rxt-recorded-response-continuation job)))
  (and (not (fn-rxt-parser-jobp job))
       (equal (mv-nth 0 a) :invalid-response)
       (not (natp (mv-nth 2 a)))))
 :rule-classes nil)
