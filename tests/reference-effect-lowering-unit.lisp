; Structural source controls for the effect compiler; execution/correspondence
; of generated callbacks remains a separate full-R proof obligation.
(in-package "ACL2")
(include-book "../books/reference-effect-lowering")
(defcolumns fn2-sched ((link :u8)))
(defcolumns fn2-effect-extra ((value :u8)))
(defcorechild fn2-core-sched fn2-sched
 :init (fn2-sched-init 1 fn2-sched) :profilep t :why "Fixture scheduler child; forbidden outside the declared boundary.")
(defcorechild fn2-core-extra fn2-effect-extra
 :init (fn2-effect-extra-init 1 fn2-effect-extra) :profilep t :why "Unrelated child retained through the generated callback.")
(defstobj fn2-core (fn2-core-sched :type fn2-sched)
                  (fn2-core-extra :type fn2-effect-extra))

(defun fn2-effect-test-boundary (id fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :guard t))
 (stobj-let ((fn2-sched (fn2-core-sched fn2-core))) (fn2-sched)
  (fn2-sched-set-link 0 (if (unsigned-byte-p 8 id) id 0) fn2-sched) fn2-core))
(defun fn2-effect-test-replacement (id fn2-core fifo)
 (declare (xargs :stobjs fn2-core :verify-guards nil :guard t))
 (mv fn2-core (append fifo (list id))))
(defun fn2-effect-test-wrong-replacement (id fn2-core fifo)
 (declare (xargs :stobjs fn2-core :verify-guards nil :guard t))
 (mv (append fifo (list id)) fn2-core))
(defun fn2-effect-test-leaf (x fn2-effect-extra)
 (declare (xargs :stobjs fn2-effect-extra :verify-guards nil :guard t))
 (mv x (fn2-effect-extra-set-value 0 (if (unsigned-byte-p 8 x) x 0) fn2-effect-extra)))
(defun fn2-effect-test-mv (x fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :guard t))
 (stobj-let ((fn2-effect-extra (fn2-core-extra fn2-core)))
  (answer fn2-effect-extra) (fn2-effect-test-leaf x fn2-effect-extra)
  (let ((fn2-core (if (equal answer 0) (fn2-effect-test-boundary 7 fn2-core)
                   (fn2-effect-test-boundary answer fn2-core))))
   (mv answer fn2-core))))
(defun fn2-effect-test-order (x fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :guard t))
 (let ((fn2-core (fn2-effect-test-boundary x fn2-core)))
  (if (equal x 0)
      (fn2-effect-test-mv 1 fn2-core)
    (fn2-effect-test-mv 2 fn2-core))))
(defun fn2-effect-test-bad-mv (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :guard t))
 (let ((fn2-core (fn2-effect-test-boundary 1 fn2-core))) (mv fn2-core 9)))
(defun fn2-effect-test-bad-queue (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :guard t))
 (stobj-let ((fn2-sched (fn2-core-sched fn2-core))) (link) (fn2-sched-link 0 fn2-sched)
  (fn2-effect-test-boundary link fn2-core)))
(defun fn2-effect-test-shape (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :guard t))
 (stobj-let ((fn2-sched (fn2-core-sched fn2-core))) (yes) (fn2-sched-wfp fn2-sched) yes))
(defun fn2-effect-test-recursive (fuel fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :guard t :measure (nfix fuel)))
 (if (zp fuel) fn2-core
  (let ((fn2-core (fn2-effect-test-boundary fuel fn2-core)))
   (fn2-effect-test-recursive (1- fuel) fn2-core))))
(mutual-recursion
 (defun fn2-effect-test-scc-a (fuel fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :guard t :measure (nfix fuel)))
  (if (zp fuel) (fn2-effect-test-boundary 1 fn2-core)
   (fn2-effect-test-scc-b (1- fuel) fn2-core)))
 (defun fn2-effect-test-scc-b (fuel fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :guard t :measure (nfix fuel)))
  (if (zp fuel) fn2-core (fn2-effect-test-scc-a (1- fuel) fn2-core))))

(defun fn2-effect-test-plan (fn world)
 (declare (xargs :verify-guards nil))
 (fn2-effect-plan-one fn 'fn2-effect-test-boundary nil world nil nil 10000))
(defun fn2-effect-test-compiled-p (fn world)
 (declare (xargs :verify-guards nil))
 (mv-let (err rows) (fn2-effect-test-plan fn world)
  (let ((row (cdr (assoc-eq fn rows))))
   (mv-let (err2 stages ir counter)
    (fn2-effect-compile (fn2-decl-get :body row)
     (fn2-effect-env (fn2-decl-get :formals row) (fn2-decl-get :inputs row))
     rows 'fn2-effect-test-boundary 'fn2-effect-test-replacement world 0 10000)
    (declare (ignore counter))
    (mv-let (err3 tail) (fn2-effect-tail ir)
     (and (not err) (not err2) (not err3)
          (fn2-effect-output-shape-p ir (fn2-decl-get :outputs row))
          (consp (fn2-product-block stages tail))
          (member-eq 'fn2-effect-test-replacement
             (fn2-lower-call-names (fn2-product-block stages tail)))
          ; The separate child helper must retain its exact original ABI.
          (not (fn2-decl-get :effect (cdr (assoc-eq 'fn2-effect-test-leaf rows))))))))))

; Real admitted fixture metadata, not invented function arities. The lambda,
; branch and multi-carrier child patterns exercise the shared tuple IR.
(make-event
 (value `(assert-event
  ',(and (fn2-effect-boundary-abi-p 'fn2-effect-test-boundary 'fn2-effect-test-replacement (w state))
          (not (fn2-effect-boundary-abi-p 'fn2-effect-test-boundary 'fn2-effect-test-wrong-replacement (w state)))
          (fn2-effect-test-compiled-p 'fn2-effect-test-mv (w state))
          (fn2-effect-test-compiled-p 'fn2-effect-test-order (w state))
          (fn2-effect-test-compiled-p 'fn2-effect-test-recursive (w state))))))
(make-event
 (mv-let (bad-mv rows) (fn2-effect-test-plan 'fn2-effect-test-bad-mv (w state))
  (declare (ignore rows))
  (mv-let (queue rows) (fn2-effect-test-plan 'fn2-effect-test-bad-queue (w state))
   (declare (ignore rows))
   (mv-let (scc rows) (fn2-effect-test-plan 'fn2-effect-test-scc-a (w state))
    (declare (ignore rows))
    (value `(assert-event ',(and (equal (car bad-mv) :effectful-mv-abi)
                                (equal (car queue) :native-queue-outside-boundary)
                                (equal (car scc) :unsupported-scc))))))))

; An admitted but unrelated theorem is not a shape/frame contract. Raw
; logical inspection of a core carrier cannot hide behind a pure helper.
(make-event
 (mv-let (err rows)
  (fn2-effect-plan-one 'fn2-effect-test-shape 'fn2-effect-test-boundary
   (fn2-effect-leaf-bindings '((fn2-effect-test-shape . fn2-product-spine-consp))
                            :shape 'fn2-representation-relation)
   (w state) nil nil 10000)
  (declare (ignore rows))
  (value `(assert-event
    ',(and (equal (car err) :invalid-leaf-contract)
           (fn2-effect-raw-core-use-p '(nth '0 fn2-core))
           (fn2-effect-raw-core-use-p '(update-nth '0 x fn2-core))
           (not (fn2-effect-raw-core-use-p '(cons x (cons fn2-core 'nil)))))))))

; A lambda alias cannot smuggle the core into an ordinary list primitive.
; This validates opaque core helpers too, even if they have no enqueue path.
(make-event
 (mv-let (err stages ir counter)
  (fn2-effect-compile '((lambda (alias) (nth '0 alias)) fn2-core)
   '((fn2-core . (:child fn2-core))) nil
   'fn2-effect-test-boundary 'fn2-effect-test-replacement (w state) 0 1000)
  (declare (ignore stages ir counter))
  (value `(assert-event ',(consp err)))))

; Two constrained symbols selecting one implementation must retain distinct
; binding records. Direct-call records cannot masquerade as either binding.
(assert-event
 (and (equal (fn2-effect-selection-key 'implementation 'stub-a) 'stub-a)
      (equal (fn2-effect-selection-key 'implementation 'stub-b) 'stub-b)
      (not (equal (fn2-effect-selection-key 'implementation nil)
                  (fn2-effect-selection-key 'implementation 'stub-a)))))
