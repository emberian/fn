; The machine form's language, exercised on a kind of its own (MACHINE-FORM
; 6.10 G2): the kind is declared and its arms are generated and proved in
; child form here, with no core and no assembly. Refusals are must-fails.
(in-package "ACL2")
(include-book "../books/machines-a-run")
(include-book "std/testing/must-fail" :dir :system)

(defmachine fn2-arms-probe
 :phases (:free :work :wait :done :loop :take)
 :fields ((pending :u32) (stopped :bool) (target :link) (count :u32) (cap-index :u32) (cap-nonce :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 1)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*) (target *fn2-none*))
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
          ((equal row-target *fn2-none*) (:set (count (+ 1 row-count))) (:charge :steps *fn2-work-empty* :runnable t))
          ;; row-slot (D F7) and a wake of another row (D F5)
          (t (:wake-row row-target) (:set (count row-slot)) (:goto close))))
  (:wait (:charge :steps *fn2-work-empty*))
  (:done (:idle))
  ;; a bounded loop (D F6): at most 4 passes, each reading the row afresh
  (:loop (:repeat 4 ((:set (count (+ 1 row-count)))) :until (>= row-count 10))
         (:next :done) (:charge :steps *fn2-work-small*))
  ;; a range handed to this row is accepted as its own (D F9)
  (:take (:do (code) (fn2-core-accept-hand row-target 0)
          :case (((:ok) (:next :done) (:charge :steps *fn2-work-small*))
                 (:otherwise (:stop :probe-refused))))))
 :observes
 ((:close-result :from (:wait) (:set (pending 0)) (:next :done) (:wake))))
(defmachine-arms fn2-arms-probe :children)

(assert-event (equal (fn2-machine-declared 'fn2-arms-probe :stops (w state)) '(:probe-overflow :probe-refused)))
(assert-event (fn2-assert-compliant-p '(fn2-arms-probe-run-work-children fn2-arms-probe-sub-close-children
                                        fn2-arms-probe-run-loop-children fn2-arms-probe-repeat-loop-0
                                        fn2-arms-probe-run-take-children
                                        fn2-arms-probe-on-close-result-children) (w state)))

;; Refused at expansion: two wakes on one path; an unknown stop reason; an
;; :issue on a kind with no descriptors is checked elsewhere.
(defmachine fn2-arms-probe2
 :phases (:free :work)
 :fields ((target :link))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle)) (:work (:wake-row row-target) (:wake-row row-target) (:idle)))
 :observes ())
(must-fail (defmachine-arms fn2-arms-probe2 :children))
(defmachine fn2-arms-probe3
 :phases (:free :work)
 :fields ((target :link))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle)) (:work (:stop :no-such-reason)))
 :observes ())
(must-fail (defmachine-arms fn2-arms-probe3 :children))
(value-triple (cw "MACHINE ARMS UNIT: kind stops, sub-arm refusal, row-slot, wake-row, repeat, accept-hand in child form; two wakes and an unknown stop refused PASS~%"))
