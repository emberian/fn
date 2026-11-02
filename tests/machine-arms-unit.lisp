; The machine form's language, exercised on a kind of its own (MACHINE-FORM
; 6.10 G2): the kind is declared and its arms are generated and proved in
; child form here, with no core and no assembly. Refusals are must-fails.
(in-package "ACL2")
(include-book "../books/machines-a-run")
(include-book "../books/accounts-core")
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

;; G3: the loop's work is derived, never stated: the arm's charge after the
;; :repeat adds the passes made (4 less the passes left, which the pass
;; function returns first) times the pass's bound, and its static cost the
;; four passes.
(defun fn2-arms-test-mentions (x tree)
  (declare (xargs :guard t))
  (if (atom tree) (equal x tree)
    (or (fn2-arms-test-mentions x (car tree)) (fn2-arms-test-mentions x (cdr tree)))))
(assert-event (fn2-arms-test-mentions 'fn2-arms-probe-repeat-loop-0-left
                                      (getpropc 'fn2-arms-probe-run-loop-children 'unnormalized-body nil (w state))))
(assert-event (equal (caddr (cdr (assoc-eq 'fn2-arms-probe-repeat-loop-0 (table-alist 'fn2-arms-child-sigs (w state))))) 1))

;; G3 (D F13): D0's move check counts holds and effects per call. A move
;; into a phase holding two windows needs two acquiring calls, and one is
;; refused; leaving it needs two releases.
(assert-event (and (fn2-arm-msubsetp '(:w :w) '(:w :x :w)) (not (fn2-arm-msubsetp '(:w :w) '(:w :x)))
                   (equal (fn2-arm-mminus '(:w :w :x) '(:w)) '(:w :x))))
(assert-event (and (null (fn2-arm-moves-problem (fn2-arm-moves '(:p) '(:q) '((:p) (:q :storage-window :storage-window)))
                                                '(:storage-window :storage-window) nil))
                   (fn2-arm-moves-problem (fn2-arm-moves '(:p) '(:q) '((:p) (:q :storage-window :storage-window)))
                                          '(:storage-window) nil)
                   (fn2-arm-moves-problem (fn2-arm-moves '(:q) '(:p) '((:p) (:q :storage-window :storage-window)))
                                          nil '(:storage-window))
                   (null (fn2-arm-moves-problem (fn2-arm-moves '(:q) '(:p) '((:p) (:q :storage-window :storage-window)))
                                                nil '(:storage-window :storage-window)))))

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
;; G3 (D F10): a phase-valued field. The reply arm's :next is the field, so
;; it reaches exactly the subset; the writes are checked against it.
(defmachine fn2-arms-phase-field
 :phases (:free :reply :command :query)
 :fields ((after (:phase-subset (:command :query))))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*) (after :command))
 :arms ((:free (:idle))
        (:reply (:next row-after) (:charge :steps *fn2-work-small*))
        (:command (:set (after :query)) (:charge :steps *fn2-work-small*))
        (:query (:set (after :command)) (:next :reply) (:charge :steps *fn2-work-small*)))
 :observes ())
(defmachine-arms fn2-arms-phase-field :children)
(assert-event (equal (fn2-machine-declared 'fn2-arms-phase-field :phase-fields (w state)) '((after :command :query))))
;; a write outside the subset is refused
(defmachine fn2-arms-phase-bad-write
 :phases (:free :reply :command :query)
 :fields ((after (:phase-subset (:command :query))))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*) (after :command))
 :arms ((:free (:idle)) (:reply (:set (after :reply)) (:charge :steps *fn2-work-small*))
        (:command (:idle)) (:query (:idle)))
 :observes ())
(must-fail (defmachine-arms fn2-arms-phase-bad-write :children))
;; a phase field that would start outside its subset (no :initial) is refused
(must-fail (defmachine fn2-arms-phase-bad-start
            :phases (:free :reply :command)
            :fields ((after (:phase-subset (:command))))
            :budget (:bytes 4096 :steps 32 :descriptors 0)
            :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
            :arms ((:free (:idle)) (:reply (:next row-after) (:idle)) (:command (:idle)))
            :observes ()))

;; G3: the contracts the generator derives for a kind, read without
;; registering them (child form registers none).
(defun fn2-arms-test-conts (kind world)
  (declare (xargs :mode :program))
  (mv-let (err form) (fn2-arms-events kind :wrappers world)
    (and (not err) (cadr (member-eq :continuations (cadr (cadddr (cadr form))))))))
(defun fn2-arms-test-next (tag conts)
  (declare (xargs :mode :program))
  (cadr (member-eq :next (cddr (assoc-eq tag conts)))))
;; G3 (D F11): a shared sub-arm's leaves count only where the caller's phase
;; reaches them: :a reaches :c alone and :b :d alone, though both go to work.
(defmachine fn2-arms-shared
 :phases (:free :a :b :c :d)
 :fields ((count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :subarms ((work (:cond ((equal row-phase *fn2-arms-shared-state-a*) (:next :c) (:charge :steps *fn2-work-small*))
                        ((not (equal row-phase *fn2-arms-shared-state-b*)) (:stop :machine-phase))
                        (t (:next :d) (:charge :steps *fn2-work-small*)))))
 :arms ((:free (:idle)) (:a (:goto work)) (:b (:goto work)) (:c (:idle)) (:d (:idle)))
 :observes ())
(defmachine-arms fn2-arms-shared :children)
(make-event
 (let ((conts (fn2-arms-test-conts 'fn2-arms-shared (w state))))
   (if (and (equal (fn2-arms-test-next :a conts) '(:c)) (equal (fn2-arms-test-next :b conts) '(:d)))
       '(value-triple :f11-ok)
     (er hard 'f11 "shared sub-arm nexts ~x0" conts))))
;; G3 (D F14): holds per path. :cmd holds the window only while reserved is
;; :held; a path acquires it exactly when it starts without it and ends where
;; it is held. A refused reservation acquires nothing (an operation with
;; answers acts on its :ok paths).
(defmachine fn2-arms-per-path
 :phases (:free :cmd :rep)
 :fields ((reserved (:enum fn2-arms-res (:none :held))) (wslot :u32) (wgen :u60))
 :holds ((:cmd (:storage-window :while (reserved :held))) (:rep :storage-window))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :subarms ((answer (:next :rep) (:charge :steps *fn2-work-small*)))
 :arms ((:free (:idle))
        (:cmd (:if (equal row-reserved *fn2-arms-res-held*)
                   ((:goto answer))
                   ((:do (code ws wg) (fn2-core-reserve 1) :effects ((:acquire (:storage-window)))
                     :case (((:ok) (:set (reserved *fn2-arms-res-held*) (wslot ws) (wgen wg)) (:goto answer))
                            (:otherwise (:charge :steps *fn2-work-small*)))))))
        (:rep (:do (code) (fn2-core-release row-wslot row-wgen) :effects ((:release (:storage-window)))
               :case (((:ok) (:set (reserved *fn2-arms-res-none*)) (:next :cmd) (:charge :steps *fn2-work-small*))
                      (:otherwise (:stop :machine-phase))))))
 :observes ())
(defmachine-arms fn2-arms-per-path :children)
(assert-event (equal (fn2-machine-declared 'fn2-arms-per-path :holds-while (w state))
                     '((:cmd :storage-window reserved :held))))
(make-event
 (let ((p (fn2-machine-arms-problem 'fn2-arms-per-path (fn2-arms-test-conts 'fn2-arms-per-path (w state)) nil (w state))))
   (if p (er hard 'f14 "~@0" p) '(value-triple :f14-ok))))
;; the same arm without the test: entering :cmd with the window held, its
;; reservation would acquire it twice, and D0 refuses the path
(defmachine fn2-arms-per-path-blind
 :phases (:free :cmd :rep)
 :fields ((reserved (:enum fn2-arms-res2 (:none :held))) (wslot :u32) (wgen :u60))
 :holds ((:cmd (:storage-window :while (reserved :held))) (:rep :storage-window))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :subarms ((answer (:next :rep) (:charge :steps *fn2-work-small*)))
 :arms ((:free (:idle))
        (:cmd (:do (code ws wg) (fn2-core-reserve 1) :effects ((:acquire (:storage-window)))
               :case (((:ok) (:set (reserved *fn2-arms-res2-held*) (wslot ws) (wgen wg)) (:goto answer))
                      (:otherwise (:charge :steps *fn2-work-small*)))))
        (:rep (:do (code) (fn2-core-release row-wslot row-wgen) :effects ((:release (:storage-window)))
               :case (((:ok) (:set (reserved *fn2-arms-res2-none*)) (:next :cmd) (:charge :steps *fn2-work-small*))
                      (:otherwise (:stop :machine-phase))))))
 :observes ())
(defmachine-arms fn2-arms-per-path-blind :children)
(assert-event (fn2-machine-arms-problem 'fn2-arms-per-path-blind
                                        (fn2-arms-test-conts 'fn2-arms-per-path-blind (w state)) nil (w state)))
;; a conditional hold names an enum field and its values
(must-fail (defmachine fn2-arms-per-path-bad
            :phases (:free :cmd)
            :fields ((count :u32))
            :holds ((:cmd (:storage-window :while (count 1))))
            :budget (:bytes 4096 :steps 32 :descriptors 0)
            :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
            :arms ((:free (:idle)) (:cmd (:idle)))
            :observes ()))

;; G3 (D F8): a typed link. The generator emits the link's liveness and its
;; reads over the probe's table (which joins the tuple), and :owner L stands
;; for the link's owner triple.
(defmachine fn2-arms-linker
 :phases (:free :work :done)
 :fields ((peer :link) (peer-gen :u60) (peer-kind :u8) (seen :u32) (wslot :u32) (wgen :u60))
 :links ((peer :kind fn2-arms-probe :slot peer :gen peer-gen :kind-field peer-kind :back (target) :reads (count)))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*) (peer *fn2-none*))
 :arms ((:free (:idle))
        (:work (:if (:live peer)
                    ((:set (seen (:read peer count)))
                     (:do (code) (fn2-core-truncate row-wslot row-wgen 0 :owner peer) :accept ()
                      :case ((:otherwise (:next :done) (:charge :steps *fn2-work-small*)))))
                    ((:next :done) (:charge :steps *fn2-work-small*))))
        (:done (:idle)))
 :observes ())
(defmachine-arms fn2-arms-linker :children)
(assert-event (fn2-assert-compliant-p '(fn2-arms-linker-link-peer-live-p fn2-arms-linker-link-peer-count
                                        fn2-arms-linker-run-work-children) (w state)))
;; a linked kind names its owner only through a link, and reads only the
;; link's read set
(defmachine fn2-arms-linker-hand
 :phases (:free :work)
 :fields ((peer :link) (peer-gen :u60) (peer-kind :u8) (wslot :u32) (wgen :u60))
 :links ((peer :kind fn2-arms-probe :slot peer :gen peer-gen :kind-field peer-kind))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*) (peer *fn2-none*))
 :arms ((:free (:idle))
        (:work (:do (code) (fn2-core-truncate row-wslot row-wgen 0 :okind row-peer-kind :oslot row-peer :ogen row-peer-gen)
                :accept () :case ((:otherwise (:charge :steps *fn2-work-small*))))))
 :observes ())
(must-fail (defmachine-arms fn2-arms-linker-hand :children))
(defmachine fn2-arms-linker-wide
 :phases (:free :work)
 :fields ((peer :link) (peer-gen :u60) (seen :u32))
 :links ((peer :kind fn2-arms-probe :slot peer :gen peer-gen :reads (count)))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*) (peer *fn2-none*))
 :arms ((:free (:idle)) (:work (:set (seen (:read peer cap-index))) (:charge :steps *fn2-work-small*)))
 :observes ())
(must-fail (defmachine-arms fn2-arms-linker-wide :children))

;; G3 (C gap 4): an inner state machine. The sealer-like row runs its inner
;; machine from :work; the inner phase is the field step, each inner arm a
;; clause on it, and the outer arm's phases are only the inner arms' (idle
;; stays, build moves on to :done).
(defmachine fn2-arms-inner
 :phases (:free :work :done)
 :fields ((count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :sub ((seal :field step :phases (:idle :build)
        :arms ((:idle (:sub-next seal :build) (:charge :steps *fn2-work-small* :runnable t))
               (:build (:sub-next seal :idle) (:set (count (+ 1 row-count))) (:next :done) (:charge :steps *fn2-work-small*)))))
 :arms ((:free (:idle)) (:work (:goto seal)) (:done (:idle)))
 :observes ())
(defmachine-arms fn2-arms-inner :children)
(assert-event (equal *fn2-arms-inner-seal-build* 1))
(make-event
 (let ((conts (fn2-arms-test-conts 'fn2-arms-inner (w state))))
   (if (let ((n (fn2-arms-test-next :work conts))) (and (subsetp-eq n '(:work :done)) (subsetp-eq '(:work :done) n)))
       '(value-triple :sub-ok)
     (er hard 'sub "inner machine nexts ~x0" conts))))
;; an inner machine names one arm per inner phase, in order
(must-fail (defmachine fn2-arms-inner-bad
            :phases (:free :work)
            :fields ((count :u32))
            :budget (:bytes 4096 :steps 32 :descriptors 0)
            :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
            :sub ((seal :field step :phases (:idle :build) :arms ((:idle (:idle)))))
            :arms ((:free (:idle)) (:work (:goto seal)))
            :observes ()))

;; A :goto after a :repeat: the sub-arm's charge cannot carry the loop's passes.
(defmachine fn2-arms-loop-goto
 :phases (:free :work)
 :fields ((count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :subarms ((rest (:charge :steps *fn2-work-small*)))
 :arms ((:free (:idle))
        (:work (:repeat 2 ((:set (count (+ 1 row-count)))) :until (>= row-count 3)) (:goto rest)))
 :observes ())
(must-fail (defmachine-arms fn2-arms-loop-goto :children))
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

;; G3 (C gap 5): a genesis arm, run once on each row by the executor's init
;; (fn2-exec-genesis), is walked as an arm from the row's initial phase
;; (:ready here), named K-GENESIS, and registered as the kind's :genesis-arm;
;; its :next is its paths' ends (staying is the initial phase), and a phase
;; only it reaches is reached.
(defmachine fn2-arms-born
 :phases (:free :ready :parked)
 :fields ((seen :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*) (phase *fn2-arms-born-state-ready*))
 :genesis ((:if (equal row-seen 0)
                ((:set (seen 1)) (:charge :steps *fn2-work-small* :runnable t))
                ((:next :parked) (:charge :steps *fn2-work-small*))))
 :arms ((:free (:idle)) (:ready (:set (seen 2)) (:charge :steps *fn2-work-small*)) (:parked (:idle)))
 :observes ())
(defmachine-arms fn2-arms-born :children)
(assert-event (fn2-assert-compliant-p '(fn2-arms-born-genesis-children) (w state)))
(defun fn2-arms-test-genesis (kind world)
  (declare (xargs :mode :program))
  (mv-let (err form) (fn2-arms-events kind :wrappers world)
    (and (not err) (cadr (member-eq :genesis-arm (cadr (cadddr (cadr form))))))))
(defun fn2-arms-test-unreached (kind world)
  (declare (xargs :mode :program))
  (mv-let (err form) (fn2-arms-events kind :wrappers world)
    (and (not err) (cadr (member-eq :unreached (cadr (cadddr (cadr form))))))))
(make-event
 (let ((g (fn2-arms-test-genesis 'fn2-arms-born (w state))))
   (if (and (equal (len g) 1) (eq (car (car g)) :ready) (eq (cadr (car g)) 'fn2-arms-born-genesis)
            (subsetp-eq (fn2-arms-test-next :ready g) '(:ready :parked))
            (subsetp-eq '(:ready :parked) (fn2-arms-test-next :ready g))
            (null (fn2-arms-test-unreached 'fn2-arms-born (w state))))
       '(value-triple :genesis-ok)
     (er hard 'genesis "genesis entry ~x0" g))))
;; a kind without :genesis registers none
(assert-event (null (fn2-arms-test-genesis 'fn2-arms-probe6 (w state))))
;; the genesis arm is the arm language: an undeclared operation is refused
(defmachine fn2-arms-born-bad
 :phases (:free :ready)
 :fields ((seen :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :genesis ((:do (code) (fn2-arms-t-undeclared row-seen) :case ((:otherwise (:idle)))))
 :arms ((:free (:idle)) (:ready (:idle)))
 :observes ())
(must-fail (defmachine-arms fn2-arms-born-bad :children))
(value-triple (cw "MACHINE ARMS UNIT: genesis arm walked from the initial phase, registered, an undeclared call refused PASS~%"))

;; G3 (D F4): a defwait park's named formals (:park K :F E ...): in child
;; form, fn2-account-request-park's :child takes (id principal fn2-accounts
;; fn2-machines); :principal E supplies the formal, and omitting it is refused.
(defmachine fn2-arms-park-wait
 :phases (:free :work)
 :fields ((seen :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle))
        (:work (:park :principal-reservation :principal row-principal-slot)))
 :observes ())
(defmachine-arms fn2-arms-park-wait :children)
(assert-event (fn2-assert-compliant-p '(fn2-arms-park-wait-run-work-children) (w state)))
(defmachine fn2-arms-park-wait-bad
 :phases (:free :work)
 :fields ((seen :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle))
        (:work (:park :principal-reservation)))
 :observes ())
(must-fail (defmachine-arms fn2-arms-park-wait-bad :children))
(value-triple (cw "MACHINE ARMS UNIT: defwait park named formals supplied and unnamed formal refused PASS~%"))

;; Brick F2 teeth:
;; 1. Sequential D0 resource acquisition order check: acquiring a higher-ranked
;; resource (:identity-reservation) before a lower-ranked one (:transaction-row)
;; in the same arm is caught even when the source phase holds neither.
(defun fn2-arms-t-acq-hi () (declare (xargs :guard t)) :ok)
(defun fn2-arms-t-acq-lo () (declare (xargs :guard t)) :ok)
(defcost fn2-arms-t-acq-hi :answers (:ok) :child fn2-arms-t-acq-hi
  :effects ((:acquire (:identity-reservation))) :doc "Test: acquire higher-ranked resource.")
(defcost fn2-arms-t-acq-lo :answers (:ok) :child fn2-arms-t-acq-lo
  :effects ((:acquire (:transaction-row))) :doc "Test: acquire lower-ranked resource.")
(assert-event
 (not (fn2-resource-effects-p
       (fn2-arm-effect-rows 'fn2-arms-probe '(:work) '(fn2-arms-t-acq-hi fn2-arms-t-acq-lo)
                            '((:work) (:done :transaction-row :identity-reservation)) (w state))
       *fn2-resource-order*)))
(assert-event
 (fn2-resource-effects-p
  (fn2-arm-effect-rows 'fn2-arms-probe '(:work) '(fn2-arms-t-acq-lo fn2-arms-t-acq-hi)
                       '((:work) (:done :transaction-row :identity-reservation)) (w state))
  *fn2-resource-order*))

;; 2. Derived call-cost summation: two sequential :do calls of 3072 bytes each
;; sum to 6144 bytes in the derived contract cost, even when :charge states 0.
(defun fn2-arms-t-work3k (v) (declare (xargs :guard t)) (nfix v))
(defcost fn2-arms-t-work3k :bytes 3072 :child fn2-arms-t-work3k :doc "Test: 3 KiB operation.")
(defmachine fn2-arms-cost-sum
 :phases (:free :work :done)
 :fields ((count :u32))
 :budget (:bytes 8192 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle))
        (:work (:do (a) (fn2-arms-t-work3k row-count))
               (:do (b) (fn2-arms-t-work3k a))
               (:set (count b)) (:next :done) (:charge :steps *fn2-work-small*))
        (:done (:idle)))
 :observes ())
(defmachine-arms fn2-arms-cost-sum :children)
(make-event
 (let* ((conts (fn2-arms-test-conts 'fn2-arms-cost-sum (w state)))
        (cost (cadr (member-eq :cost (cddr (assoc-eq :work conts))))))
   (if (equal (cadr (member-eq :bytes cost)) 6144)
       '(value-triple :cost-sum-ok)
     (er hard 'cost-sum "expected 6144 derived bytes, got ~x0" cost))))

;; 3. :faults on defcost + (:refuse WORD) in :on-refusal + :do-chain auto-split (> 4 :do steps):
(defun fn2-arms-t-fop (v) (declare (xargs :guard t)) (mv :ok (nfix v)))
(defcost fn2-arms-t-fop :answers (:ok :soft :fault) :faults (:fault) :child fn2-arms-t-fop
  :doc "Test: operation with soft refusal and fault.")
(defmachine fn2-arms-f2-probe
 :phases (:free :work :refused :done)
 :fields ((word :u8) (count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle))
        (:work :on-refusal (:refuse 7)
               (:do (c1 v1) (fn2-arms-t-fop row-count))
               (:do (c2 v2) (fn2-arms-t-fop v1))
               (:do (c3 v3) (fn2-arms-t-fop v2))
               (:do (c4 v4) (fn2-arms-t-fop v3))
               (:do (c5 v5) (fn2-arms-t-fop v4))
               (:set (count v5)) (:next :done) (:charge :steps *fn2-work-small*))
        (:refused (:idle))
        (:done (:idle)))
 :observes ())
(defmachine-arms fn2-arms-f2-probe :children)
(assert-event (function-symbolp 'fn2-arms-f2-probe-chain-work-0-children (w state)))
;; leaving a non-fault answer (:soft) unrouted to a :stop :on-refusal is refused
(defmachine fn2-arms-f2-bad
 :phases (:free :work)
 :fields ((word :u8))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle))
        (:work :on-refusal ((:stop :machine-phase))
               (:do (c1 v1) (fn2-arms-t-fop row-word))
               (:charge :steps *fn2-work-small*)))
 :observes ())
(must-fail (defmachine-arms fn2-arms-f2-bad :children))
(value-triple (cw "MACHINE ARMS UNIT: Brick F2 sequential D0 holdings, derived call-cost summation, :faults + (:refuse WORD), and :do-chain auto-split PASS~%"))
