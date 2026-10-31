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
;; Two extra children (the tuple's EXTRA, MACHINE-FORM P3): an operation
;; whose :child takes two registered core children beyond the five; the
;; kind's arms are generated over (K fn2-machines fn2-pool fn2-ops
;; fn2-control fn2-arms-tx fn2-arms-ty), in the registry's order.
(defcolumns fn2-arms-tx ((value :u32)))
(defcolumns fn2-arms-ty ((value :u32)))
(defcorechild fn2-core-arms-tx fn2-arms-tx
 :init (fn2-arms-tx-init 1 fn2-arms-tx) :profilep t :why "Test-only extra child of an arm tuple.")
(defcorechild fn2-core-arms-ty fn2-arms-ty
 :init (fn2-arms-ty-init 1 fn2-arms-ty) :profilep t :why "Test-only extra child of an arm tuple.")
(defun fn2-arms-t-move (v fn2-arms-ty fn2-arms-tx)
  ; formals name ty before tx: the tuple's order is the registry's, not the callee's
  (declare (xargs :stobjs (fn2-arms-ty fn2-arms-tx)
                  :guard (and (fn2-arms-tx-wfp fn2-arms-tx) (fn2-arms-ty-wfp fn2-arms-ty))))
  (if (and (< 0 (fn2-arms-tx-rows fn2-arms-tx)) (< 0 (fn2-arms-ty-rows fn2-arms-ty)) (unsigned-byte-p 32 v))
      (let* ((fn2-arms-tx (fn2-arms-tx-put 0 (value v)))
             (fn2-arms-ty (fn2-arms-ty-put 0 (value v))))
        (mv :ok fn2-arms-ty fn2-arms-tx))
    (mv :refused fn2-arms-ty fn2-arms-tx)))
(fn2-arms-tx-preserves fn2-arms-t-move (v fn2-arms-ty fn2-arms-tx)
  :carriers ((fn2-arms-ty 1 :prefix "-TY") (fn2-arms-tx 2 :prefix "-TX")))
;; the core face fn2-arms-t-move-core is the assembly's (no core here); child form calls the :child
(defcost fn2-arms-t-move-core :answers t :child fn2-arms-t-move :tables (fn2-core-arms-tx fn2-core-arms-ty)
 :doc "Test: write a value into two extra children.")
(defmachine fn2-arms-probe4
 :phases (:free :work :done)
 :fields ((count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :stops (:probe-refused)
 :arms ((:free (:idle))
        (:work (:do (code) (fn2-arms-t-move-core row-count)
                :case (((:ok) (:next :done) (:charge :steps *fn2-work-small*))
                       (:otherwise (:stop :probe-refused)))))
        (:done (:idle)))
 :observes ())
(defmachine-arms fn2-arms-probe4 :children)
; Per-arm tuples: :work takes the children its paths touch (the move's two,
; the stop's control, the write's table and directory), not the pool or ops;
; :done (idle) takes only the row's table and directory and returns none.
(assert-event (equal (getpropc 'fn2-arms-probe4-run-work-children 'stobjs-in nil (w state))
                     '(nil nil nil nil nil fn2-arms-probe4 fn2-machines fn2-control fn2-arms-tx fn2-arms-ty)))
(assert-event (equal (getpropc 'fn2-arms-probe4-run-done-children 'stobjs-in nil (w state))
                     '(nil nil nil nil nil fn2-arms-probe4 fn2-machines)))
(assert-event (equal (getpropc 'fn2-arms-probe4-run-done-children 'stobjs-out nil (w state))
                     '(nil nil nil nil)))
(assert-event (fn2-assert-compliant-p '(fn2-arms-probe4-run-work-children) (w state)))
;; An operation over a stobj no defcorechild registers is refused.
(defcolumns fn2-arms-tz ((value :u32)))
(defun fn2-arms-t-touch (fn2-arms-tz)
  (declare (xargs :stobjs fn2-arms-tz :guard (fn2-arms-tz-wfp fn2-arms-tz))) (mv :ok fn2-arms-tz))
(defcost fn2-arms-t-touch-core :answers t :child fn2-arms-t-touch :doc "Test: an unregistered child.")
(defmachine fn2-arms-probe5
 :phases (:free :work)
 :fields ((count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle)) (:work (:do (code) (fn2-arms-t-touch-core) :case ((:otherwise (:idle))))))
 :observes ())
(must-fail (defmachine-arms fn2-arms-probe5 :children))
(value-triple (cw "MACHINE ARMS UNIT: kind stops, sub-arm refusal, row-slot, wake-row, repeat, accept-hand in child form; a tuple with two extra children in registry order; two wakes and an unknown stop and an unregistered child refused PASS~%"))
;; An operation that never answers :ok (C's reads): its answers are a list
;; without :ok, :accept of one needs no :why, and every member is routed.
(defun fn2-arms-t-peek (v) (declare (xargs :guard t)) (if (equal v 0) :end :found))
(defcost fn2-arms-t-peek :answers (:found :end) :child fn2-arms-t-peek :doc "Test: answers without :ok.")
(defmachine fn2-arms-probe6
 :phases (:free :work :done)
 :fields ((count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle))
        (:work (:do (code) (fn2-arms-t-peek row-count) :accept (:found)
                :case (((:end) (:next :done) (:charge :steps *fn2-work-small*))))
               (:set (count 0)) (:charge :steps *fn2-work-small*))
        (:done (:idle)))
 :observes ())
(defmachine-arms fn2-arms-probe6 :children)
;; ... and an unrouted member is still refused (no :on-refusal here)
(defmachine fn2-arms-probe7
 :phases (:free :work)
 :fields ((count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle))
        (:work (:do (code) (fn2-arms-t-peek row-count) :accept (:found)) (:idle)))
 :observes ())
(must-fail (defmachine-arms fn2-arms-probe7 :children))
