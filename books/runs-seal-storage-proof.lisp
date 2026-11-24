; The page sealer writes its digest into a separate table. Every call,
; including an intermediate or refused call, leaves the page pool intact.
(in-package "ACL2")
(include-book "runs-page-seal")

(local
 (defmacro fn2-run-page-pool-frame (name op args idx disabled &optional induct)
   (let ((call (append (list op) args '(fc ctx b3 f pool ds))))
     `(defthm ,name
        (equal (mv-nth ,idx ,call) pool)
        :hints (("Goal" ,@(and induct (list :induct call))
                 :in-theory (e/d (,op) ,disabled)))))))

(local (fn2-run-page-pool-frame fn2-run-page-byte-frame fn2-fc-byte
 (row :page t slot gen off len base pk ps pg) 3
 (fn2-b3-byte fn2-b3-finalize fn2-b3-read fn2-fc-check-byte fn2-fc-digest-byte fn2-fc-context-hash-word fn2-pool-write)))
(local (fn2-run-page-pool-frame fn2-run-page-advance-frame fn2-fc-advance
 (fuel row :page t slot gen off len base pk ps pg) 4 (fn2-fc-byte fn2-fc-page-span)))
(local (fn2-run-page-pool-frame fn2-run-page-bytes-frame fn2-fc-run-bytes
 (fuel row :page t slot gen off len base pk ps pg) 3 (fn2-fc-advance) t))
(local (fn2-run-page-pool-frame fn2-run-page-step-frame fn2-fc-step
 (row :page t slot gen off len base pk ps pg budget) 4
 (fn2-fc-run-bytes fn2-fc-decoded fn2-fc-decode-step fn2-fc-start fn2-b3-init fn2-layout-range-code)))
(local (fn2-run-page-pool-frame fn2-run-page-format-frame fn2-format-run
 (:page t row slot gen off len base pk ps pg budget) 4 (fn2-fc-step fn2-fc-reset)))

(defthm fn2-run-seal-keeps-page-storage
  (equal (mv-nth 5 (fn2-run-seal-step w row hrow budget writers fc ctx b3 f pool ds)) pool)
  :hints (("Goal" :in-theory (e/d (fn2-run-seal-step)
                   (fn2-format-run fn2-digest-rowp fn2-b3-ready fn2-fields-rows)))))

(defthmd fn2-run-seal-keeps-writer-address
  (let* ((seal (fn2-run-seal-step w row hrow budget writers fc ctx b3 f pool ds))
         (after (mv-nth 1 seal)))
    (and (equal (fn2-run-writers-unit w after) (fn2-run-writers-unit w writers))
         (equal (fn2-run-writers-counter w after) (fn2-run-writers-counter w writers))
         (equal (fn2-run-writers-slot w after) (fn2-run-writers-slot w writers))
         (equal (fn2-run-writers-gen w after) (fn2-run-writers-gen w writers))))
  :hints (("Goal" :in-theory (e/d (fn2-run-seal-step fn2-run-writers-set-phase update-fn2-run-writers-phase$ai
                                fn2-run-writers-unit fn2-run-writers-counter fn2-run-writers-slot fn2-run-writers-gen)
                     (fn2-run-writers-rows fn2-format-run fn2-digest-rowp fn2-b3-ready fn2-fields-rows
                      nth update-nth unsigned-byte-p)))))
