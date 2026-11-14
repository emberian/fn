; Shared real machine-language fixture: its issue subarm also probes residual budgets.
(in-package "ACL2")
(include-book "../books/machines-a-run")
(include-book "../books/accounts-core")

(defmachine fn2-arms-probe
 :phases (:free :work :wait :done :loop :take)
 :fields ((pending :u32) (stopped :bool) (tgt :link) (count :u32) (cap-index :u32) (cap-nonce :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 1)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*) (tgt *fn2-none*))
 :stops (:probe-overflow :probe-refused)
 :subarms
 ;; a sub-arm with its own refusal posture (D F1): close's unrouted answers go there
 ((close :on-refusal ((:stop :probe-refused))
   (:issue (fn2-issue-close row-cap-index row-cap-nonce :principal row-principal-slot)
    :ok ((:set (pending 1)) (:next :wait) (:charge :steps *fn2-work-small* :descriptors 1)))))
 :arms
 ((:free (:idle))
  (:work
   (:cond ((>= row-count 100) (:stop :probe-overflow))
          ((equal row-tgt *fn2-none*) (:set (count (+ 1 row-count))) (:charge :steps *fn2-work-empty* :runnable t))
          ;; row-slot (D F7) and a wake of another row (D F5)
          (t (:wake-row row-tgt) (:set (count row-slot)) (:goto close))))
  (:wait (:charge :steps *fn2-work-empty*))
  (:done (:idle))
  ;; a bounded loop (D F6): at most 4 passes, each reading the row afresh
  (:loop (:repeat 4 ((:set (count (+ 1 row-count)))) :until (>= row-count 10))
         (:next :done) (:charge :steps *fn2-work-small*))
  ;; a range handed to this row is accepted as its own (D F9)
  (:take (:do (code) (fn2-core-accept-hand row-tgt 0)
          :case (((:ok) (:next :done) (:charge :steps *fn2-work-small*))
                 (:otherwise (:stop :probe-refused))))))
 :observes
 ((:close-result :from (:wait) (:set (pending 0)) (:next :done) (:wake))))
