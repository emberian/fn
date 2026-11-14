(in-package "ACL2")
(include-book "../books/core-product-lowering")
(include-book "std/testing/must-fail" :dir :system)
(defcolumns fn2-update-config ((value :u8)))
(defcolumns fn2-update-sibling ((value :u8)))
(defcorechild fn2-core-config fn2-update-config
 :init (fn2-update-config-init 1 fn2-update-config) :profilep t
 :why "Fixture child updated by generated product lowering.")
(defcorechild fn2-core-sibling fn2-update-sibling
 :init (fn2-update-sibling-init 1 fn2-update-sibling) :profilep t
 :why "Unrelated child witnesses whole-core reconstruction.")
(defstobj fn2-core (fn2-core-config :type fn2-update-config)
                  (fn2-core-sibling :type fn2-update-sibling))
(defun fn2-core-wfp (fn2-core)
 (declare (xargs :stobjs fn2-core))
 (stobj-let ((fn2-update-config (fn2-core-config fn2-core))
             (fn2-update-sibling (fn2-core-sibling fn2-core))) (ok)
   (and (fn2-update-config-wfp fn2-update-config)
        (fn2-update-sibling-wfp fn2-update-sibling)) ok))
(defun fn2-update-source (i value fn2-core)
 (declare (xargs :stobjs fn2-core :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (stobj-let ((fn2-update-config (fn2-core-config fn2-core))) (code fn2-update-config)
   (if (< i (fn2-update-config-rows fn2-update-config))
       (let ((fn2-update-config (fn2-update-config-set-value i value fn2-update-config)))
         (mv :ok fn2-update-config))
     (mv :bounds fn2-update-config))
   (mv code fn2-core)))
(defcore-product-child fn2-update-source fn2-update-child
 :teeth (fn2-update-runtime-witness fn2-update-mutation-runtime-witness))
;; The entire two-child logical state is asserted, not just the written cell.
(defthm fn2-update-positive-witness
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 0) (unsigned-byte-p 8 42)
      (equal (fn2-update-child-core-face 0 42 '(((37) 1) ((91) 1)))
             '(:ok (((42) 1) ((91) 1)))))
 :rule-classes nil)
(defthm fn2-update-refusal-witness
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 9) (unsigned-byte-p 8 42)
      (equal (fn2-update-child-core-face 9 42 '(((37) 1) ((91) 1)))
             '(:bounds (((37) 1) ((91) 1)))))
 :rule-classes nil)
(defun fn2-update-fixture-init (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-update-config (fn2-core-config fn2-core))
             (fn2-update-sibling (fn2-core-sibling fn2-core)))
  (fn2-update-config fn2-update-sibling)
  (let* ((fn2-update-config (fn2-update-config-init 1 fn2-update-config))
         (fn2-update-sibling (fn2-update-sibling-init 1 fn2-update-sibling))
         (fn2-update-config (fn2-update-config-set-value 0 37 fn2-update-config))
         (fn2-update-sibling (fn2-update-sibling-set-value 0 91 fn2-update-sibling)))
    (mv fn2-update-config fn2-update-sibling))
  fn2-core))
(defun fn2-update-fixture-snapshot (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-update-config (fn2-core-config fn2-core))
             (fn2-update-sibling (fn2-core-sibling fn2-core))) (answer)
   (list (fn2-update-config-rows fn2-update-config) (fn2-update-config-value 0 fn2-update-config)
         (fn2-update-sibling-rows fn2-update-sibling) (fn2-update-sibling-value 0 fn2-update-sibling)) answer))
(defun fn2-update-runtime-witness ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-update-fixture-init fn2-core))
          (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp 0) (unsigned-byte-p 8 42))))
    (mv-let (source-code fn2-core) (fn2-update-source 0 42 fn2-core)
     (let* ((source-after (fn2-update-fixture-snapshot fn2-core))
            (fn2-core (fn2-update-fixture-init fn2-core)))
      (mv-let (code fn2-core) (fn2-update-child-core-face 0 42 fn2-core)
       (let ((after (fn2-update-fixture-snapshot fn2-core)))
        (mv-let (refusal fn2-core) (fn2-update-child-core-face 9 99 fn2-core)
         (mv (and pre (eq source-code code) (eq code :ok) (equal source-after after)
                  (equal after '(1 42 1 91)) (eq refusal :bounds)
                  (equal after (fn2-update-fixture-snapshot fn2-core))) fn2-core)))))))
   answer)))
(assert-event (fn2-update-runtime-witness))

;; A repeated primitive call would preserve values but violate step cost.
;; Count the actual admitted source and generated bodies, not declarations.
(mutual-recursion
 (defun fn2-update-call-count (fn term)
  (declare (xargs :verify-guards nil))
  (cond ((atom term) 0) ((eq (car term) 'quote) 0)
        (t (+ (if (eq (car term) fn) 1 0)
              (if (consp (car term)) (fn2-update-call-count fn (caddar term)) 0)
              (fn2-update-call-count-list fn (cdr term))))))
 (defun fn2-update-call-count-list (fn terms)
  (declare (xargs :verify-guards nil))
  (if (atom terms) 0 (+ (fn2-update-call-count fn (car terms)) (fn2-update-call-count-list fn (cdr terms))))))
(assert-event
 (and (equal (fn2-update-call-count 'fn2-update-config-set-value
               (getpropc 'fn2-update-source 'unnormalized-body nil (w state))) 1)
      (equal (fn2-update-call-count 'fn2-update-config-set-value
               (getpropc 'fn2-update-child 'unnormalized-body nil (w state))) 1)))
;; A whole-core predicate is not silently treated as a child projection.
(defun fn2-update-unsupported (i value fn2-core)
 (declare (xargs :stobjs fn2-core :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (declare (ignore i value))
 (mv (fn2-corep fn2-core) fn2-core))
(must-fail (defcore-product-child fn2-update-unsupported fn2-update-unsupported-child))
(assert-event (not (assoc-eq 'fn2-update-unsupported (table-alist 'fn2-core-lowered (w state)))))
(defun fn2-update-collision (fn2-product-value-0 fn2-core)
 (declare (xargs :stobjs fn2-core)) (mv fn2-product-value-0 fn2-core))
(must-fail (defcore-product-child fn2-update-collision fn2-update-collision-child))
(must-fail (defcore-product-closure fn2-update-unsupported fn2-update-unsupported-family))
(defun fn2-update-recursive (n fn2-core)
 (declare (xargs :stobjs fn2-core :measure (nfix n)
                 :guard (and (natp n) (fn2-core-wfp fn2-core))))
 (if (zp n) fn2-core (fn2-update-recursive (1- n) fn2-core)))
(must-fail (defcore-product-closure fn2-update-recursive fn2-update-recursive-family))
(assert-event
 (and (not (function-symbolp 'fn2-update-unsupported-family (w state)))
      (not (function-symbolp 'fn2-update-recursive-family (w state)))))
;; Mutation control: retaining the answer and changed child is insufficient.
;; This deliberately broken reconstruction also clobbers the unrelated child.
(defun fn2-update-mutant-core-face (i value fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (mv-let (code fn2-core) (fn2-update-child-core-face i value fn2-core)
  (let ((fn2-core
         (stobj-let ((fn2-update-sibling (fn2-core-sibling fn2-core))) (fn2-update-sibling)
          (fn2-update-sibling-set-value 0 0 fn2-update-sibling) fn2-core)))
   (mv code fn2-core))))
(defthm fn2-update-reconstruction-mutation-witness
 (let ((core '(((37) 1) ((91) 1))))
  (and (fn2-corep core) (fn2-core-wfp core) (natp 0) (unsigned-byte-p 8 42)
       (equal (mv-nth 0 (fn2-update-mutant-core-face 0 42 core))
              (mv-nth 0 (fn2-update-source 0 42 core)))
       (equal (fn2-core-config (mv-nth 1 (fn2-update-mutant-core-face 0 42 core)))
              (fn2-core-config (mv-nth 1 (fn2-update-source 0 42 core))))
       (not (equal (fn2-update-mutant-core-face 0 42 core)
                   (fn2-update-source 0 42 core)))))
 :rule-classes nil)

(must-fail (fn2-check-lowering-teeth fn2-update-source))
(defun fn2-update-mutation-runtime-witness ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-update-fixture-init fn2-core))
          (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp 0) (unsigned-byte-p 8 42))))
    (mv-let (source-code fn2-core) (fn2-update-source 0 42 fn2-core)
     (let* ((source-after (fn2-update-fixture-snapshot fn2-core))
            (fn2-core (fn2-update-fixture-init fn2-core)))
      (mv-let (mutant-code fn2-core) (fn2-update-mutant-core-face 0 42 fn2-core)
       (let ((mutant-after (fn2-update-fixture-snapshot fn2-core)))
        (mv (and pre (eq source-code :ok) (eq mutant-code source-code)
                 (equal (take 2 mutant-after) (take 2 source-after))
                 (not (equal mutant-after source-after))) fn2-core))))))
   answer)))
(fn2-check-lowering-teeth fn2-update-source)
(assert-event
 (let ((row (fn2-decl-row '(:square fn2-update-child-refines-core) (w state))))
  (and (eq (fn2-decl-get :claim row) :compiler)
       (equal (fn2-decl-get :sides row) '(:concrete fn2-update-child-core-face :reference fn2-update-source))
       (equal (fn2-decl-get :proof row) '(:proved fn2-update-child-refines-core)))))
;; Compose two original core operations. A refusal in the second preserves
;; the first operation's legitimate update, rather than rolling it back.
(defun fn2-update-composed (second i value fn2-core)
 (declare (xargs :stobjs fn2-core
                 :guard (and (natp second) (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))
                 :guard-hints (("Goal" :in-theory (enable fn2-update-source)))))
 (mv-let (code fn2-core) (fn2-update-source i value fn2-core)
  (if (eq code :ok) (fn2-update-source second 43 fn2-core) (mv code fn2-core))))
(encapsulate ()
 ; Shared core lenses support opaque representation definitions.

 (local (in-theory (disable fn2-corep fn2-core-config update-fn2-core-config)))
 (defcore-product-child fn2-update-composed fn2-update-composed-child))
(defthm fn2-update-composed-positive-witness
 (let ((core '(((37 38) 2) ((91) 1))))
  (and (fn2-corep core) (fn2-core-wfp core) (natp 0) (natp 1) (unsigned-byte-p 8 42)
       (equal (fn2-update-composed-child-core-face 1 0 42 core)
              '(:ok (((42 43) 2) ((91) 1))))))
 :rule-classes nil)
(defthm fn2-update-composed-partial-refusal-witness
 (let ((core '(((37 38) 2) ((91) 1))))
  (and (fn2-corep core) (fn2-core-wfp core) (natp 0) (natp 9) (unsigned-byte-p 8 42)
       (equal (fn2-update-composed-child-core-face 9 0 42 core)
              '(:bounds (((42 38) 2) ((91) 1))))))
 :rule-classes nil)
(assert-event
 (and (equal (fn2-update-call-count 'fn2-update-child
               (getpropc 'fn2-update-composed-child 'unnormalized-body nil (w state))) 2)
      (equal (fn2-update-call-count 'fn2-update-config-set-value
               (getpropc 'fn2-update-composed-child 'unnormalized-body nil (w state))) 0)))
(defun fn2-update-composed-init (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (let ((fn2-core (fn2-update-fixture-init fn2-core)))
  (stobj-let ((fn2-update-config (fn2-core-config fn2-core))) (fn2-update-config)
   (let* ((fn2-update-config (fn2-update-config-init 2 fn2-update-config))
          (fn2-update-config (fn2-update-config-set-value 0 37 fn2-update-config))
          (fn2-update-config (fn2-update-config-set-value 1 38 fn2-update-config))) fn2-update-config)
   fn2-core)))
(defun fn2-update-composed-snapshot (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-update-config (fn2-core-config fn2-core))
             (fn2-update-sibling (fn2-core-sibling fn2-core))) (answer)
  (list (list (list (fn2-update-config-value 0 fn2-update-config)
                    (fn2-update-config-value 1 fn2-update-config))
              (fn2-update-config-rows fn2-update-config))
        (list (list (fn2-update-sibling-value 0 fn2-update-sibling))
              (fn2-update-sibling-rows fn2-update-sibling))) answer))
(defun fn2-update-composed-runtime-witness (second mutant)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-update-composed-init fn2-core))
          (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                    (natp second) (natp 0) (unsigned-byte-p 8 42))))
    (mv-let (source-code fn2-core) (fn2-update-composed second 0 42 fn2-core)
     (let* ((source-after (fn2-update-composed-snapshot fn2-core))
            (fn2-core (fn2-update-composed-init fn2-core)))
      (mv-let (child-code fn2-core) (fn2-update-composed-child-core-face second 0 42 fn2-core)
       (let* ((fn2-core (if mutant
                            (stobj-let ((fn2-update-sibling (fn2-core-sibling fn2-core))) (fn2-update-sibling)
                              (fn2-update-sibling-set-value 0 0 fn2-update-sibling) fn2-core)
                          fn2-core))
              (child-after (fn2-update-composed-snapshot fn2-core)))
        (mv (and pre (equal source-code child-code)
                 (equal (car source-after) (car child-after))
                 (if mutant (not (equal source-after child-after)) (equal source-after child-after)))
            fn2-core))))))
   answer)))
(defun fn2-update-composed-child-refines-core-positive ()
 (declare (xargs :verify-guards nil))
 (and (fn2-update-composed-runtime-witness 1 nil) (fn2-update-composed-runtime-witness 9 nil)))
(defun fn2-update-composed-child-refines-core-negative ()
 (declare (xargs :verify-guards nil))
 (and (fn2-update-composed-runtime-witness 1 t) (fn2-update-composed-runtime-witness 9 t)))
(fn2-check-lowering-teeth fn2-update-composed)

;; A read after a write uses the proved reader boundary over the updated child.
(defun fn2-update-read (i fn2-core)
 (declare (xargs :stobjs fn2-core :guard (and (natp i) (fn2-core-wfp fn2-core))))
 (stobj-let ((fn2-update-config (fn2-core-config fn2-core))) (answer)
  (if (< i (fn2-update-config-rows fn2-update-config))
      (nfix (fn2-update-config-value i fn2-update-config)) 0) answer))
(in-theory (disable fn2-update-read))

(defun fn2-update-read-after (i value fn2-core)
 (declare (xargs :stobjs fn2-core :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (mv-let (code fn2-core) (fn2-update-source i value fn2-core)
  (declare (ignore code))
  (mv (fn2-update-read i fn2-core) fn2-core)))
(in-theory (disable fn2-update-read-after))
(defcore-product-closure fn2-update-read-after fn2-update-read-after-child)
(assert-event
 (equal (fn2-update-call-count 'fn2-update-read-lowered-child
          (getpropc 'fn2-update-read-after-child 'unnormalized-body nil (w state))) 1))
(defthm fn2-update-read-after-positive
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 0) (unsigned-byte-p 8 42)
      (equal (fn2-update-read-after-child-core-face 0 42 '(((37) 1) ((91) 1)))
             '(42 (((42) 1) ((91) 1)))))
 :hints (("Goal" :in-theory
          (e/d (fn2-update-read-after fn2-update-read)
               ((:executable-counterpart fn2-update-read-after)
                (:executable-counterpart fn2-update-read)))))
 :rule-classes nil)
(defthm fn2-update-read-after-refusal
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 9) (unsigned-byte-p 8 42)
      (equal (fn2-update-read-after-child-core-face 9 42 '(((37) 1) ((91) 1)))
             '(0 (((37) 1) ((91) 1)))))
 :hints (("Goal" :in-theory
          (e/d (fn2-update-read-after fn2-update-read)
               ((:executable-counterpart fn2-update-read-after)
                (:executable-counterpart fn2-update-read)))))
 :rule-classes nil)
(assert-event
 (and (equal (fn2-update-call-count 'fn2-update-child
               (getpropc 'fn2-update-read-after-child 'unnormalized-body nil (w state))) 1)
      (equal (fn2-update-call-count 'fn2-update-config-set-value
               (getpropc 'fn2-update-read-after-child 'unnormalized-body nil (w state))) 0)))
;; Mutating evaluation order keeps the same effects but returns stale data.
(defun fn2-update-read-before-mutant (i value fn2-core)
 (declare (xargs :stobjs fn2-core :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (let ((old (fn2-update-read i fn2-core)))
  (mv-let (code fn2-core) (fn2-update-source i value fn2-core)
   (declare (ignore code)) (mv old fn2-core))))
(defthm fn2-update-read-after-order-mutation
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 0) (unsigned-byte-p 8 42)
      (equal (fn2-update-read-before-mutant 0 42 '(((37) 1) ((91) 1)))
             '(37 (((42) 1) ((91) 1))))
      (not (equal (fn2-update-read-after-child-core-face 0 42 '(((37) 1) ((91) 1)))
                  (fn2-update-read-before-mutant 0 42 '(((37) 1) ((91) 1))))))
 :hints (("Goal" :in-theory
          (e/d (fn2-update-read-after fn2-update-read)
               ((:executable-counterpart fn2-update-read-after)
                (:executable-counterpart fn2-update-read)))))
 :rule-classes nil)

(defun fn2-update-reader-live (mutant)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-update-fixture-init fn2-core))
          (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp 0)))
          (source (fn2-update-read 0 fn2-core)))
    (stobj-let ((fn2-update-config (fn2-core-config fn2-core))) (answer)
     (let ((child (fn2-update-read-lowered-child 0 fn2-update-config)))
      (and pre (equal source 37) (equal source child)
           (if mutant (not (equal source (+ 1 child))) t)))
     (mv answer fn2-core)))
   answer)))
(defun fn2-update-read-lowered-child-refines-core-positive ()
 (declare (xargs :verify-guards nil)) (fn2-update-reader-live nil))
(defun fn2-update-read-lowered-child-refines-core-negative ()
 (declare (xargs :verify-guards nil)) (fn2-update-reader-live t))
(defun fn2-update-read-after-live (mutant)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-update-fixture-init fn2-core))
          (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                    (natp 0) (unsigned-byte-p 8 42))))
    (mv-let (source fn2-core) (fn2-update-read-after 0 42 fn2-core)
     (let* ((source-after (fn2-update-fixture-snapshot fn2-core))
            (fn2-core (fn2-update-fixture-init fn2-core)))
      (mv-let (candidate fn2-core)
       (if mutant (fn2-update-read-before-mutant 0 42 fn2-core)
         (fn2-update-read-after-child-core-face 0 42 fn2-core))
       (let ((after (fn2-update-fixture-snapshot fn2-core)))
        (mv-let (refusal fn2-core) (fn2-update-read-after-child-core-face 9 42 fn2-core)
         (mv (and pre (equal source 42) (equal after '(1 42 1 91))
                  (equal source-after after) (equal refusal 0)
                  (equal after (fn2-update-fixture-snapshot fn2-core))
                  (if mutant (and (equal candidate 37) (not (equal source candidate)))
                    (equal source candidate))) fn2-core)))))))
   answer)))
(defun fn2-update-read-after-child-refines-core-positive ()
 (declare (xargs :verify-guards nil)) (fn2-update-read-after-live nil))
(defun fn2-update-read-after-child-refines-core-negative ()
 (declare (xargs :verify-guards nil)) (fn2-update-read-after-live t))
(fn2-check-lowering-teeth fn2-update-read fn2-update-read-after)

;; A read-only sibling is an input, not an update in the reconstructed core.
(defun fn2-update-sibling-read (i fn2-core)
 (declare (xargs :stobjs fn2-core :guard (and (natp i) (fn2-core-wfp fn2-core))))
 (stobj-let ((fn2-update-sibling (fn2-core-sibling fn2-core))) (answer)
  (if (< i (fn2-update-sibling-rows fn2-update-sibling))
      (nfix (fn2-update-sibling-value i fn2-update-sibling)) 0) answer))
(in-theory (disable fn2-update-sibling-read))
(defcore-readonly-child fn2-update-sibling-read fn2-update-sibling-read-child)
(defun fn2-update-with-sibling-read (i value fn2-core)
 (declare (xargs :stobjs fn2-core :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (mv-let (code fn2-core) (fn2-update-source i value fn2-core)
  (declare (ignore code))
  (mv (fn2-update-sibling-read i fn2-core) fn2-core)))
(in-theory (disable fn2-update-with-sibling-read))
(defcore-product-child fn2-update-with-sibling-read fn2-update-with-sibling-read-child)
(assert-event
 (and (equal (getpropc 'fn2-update-with-sibling-read-child 'stobjs-in nil (w state))
             '(nil nil fn2-update-config fn2-update-sibling))
      (equal (getpropc 'fn2-update-with-sibling-read-child 'stobjs-out nil (w state))
             '(nil fn2-update-config))))
(defthm fn2-update-with-sibling-read-positive
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 0) (unsigned-byte-p 8 42)
      (equal (fn2-update-with-sibling-read-child-core-face 0 42 '(((37) 1) ((91) 1)))
             '(91 (((42) 1) ((91) 1)))))
 :hints (("Goal" :in-theory
          (e/d (fn2-update-with-sibling-read fn2-update-sibling-read)
               ((:executable-counterpart fn2-update-with-sibling-read)
                (:executable-counterpart fn2-update-sibling-read)))))
 :rule-classes nil)
;; Unconditional refinement also preserves the shape of a malformed core.
(defthm fn2-update-with-sibling-read-no-canonicalization
 (and (not (fn2-corep '(((37) 1))))
      (equal (fn2-update-with-sibling-read-child-core-face 0 42 '(((37) 1)))
             '(0 (((42) 1)))))
 :hints (("Goal" :in-theory
          (e/d (fn2-update-with-sibling-read fn2-update-sibling-read)
               ((:executable-counterpart fn2-update-with-sibling-read)
                (:executable-counterpart fn2-update-sibling-read)))))
 :rule-classes nil)
(defun fn2-update-readonly-writeback-mutant (i value fn2-core)
 (declare (xargs :stobjs fn2-core :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (mv-let (answer fn2-core) (fn2-update-with-sibling-read i value fn2-core)
  (stobj-let ((fn2-update-sibling (fn2-core-sibling fn2-core))) (fn2-update-sibling)
   fn2-update-sibling (mv answer fn2-core))))
(defthm fn2-update-readonly-writeback-counterexample
 (and (not (fn2-corep '(((37) 1))))
      (equal (fn2-update-readonly-writeback-mutant 0 42 '(((37) 1)))
             '(0 (((42) 1) nil)))
      (not (equal (fn2-update-with-sibling-read-child-core-face 0 42 '(((37) 1)))
                  (fn2-update-readonly-writeback-mutant 0 42 '(((37) 1))))))
 :hints (("Goal" :in-theory
          (e/d (fn2-update-with-sibling-read fn2-update-sibling-read
                fn2-update-readonly-writeback-mutant)
               ((:executable-counterpart fn2-update-with-sibling-read)
                (:executable-counterpart fn2-update-sibling-read)
                (:executable-counterpart fn2-update-readonly-writeback-mutant)))))
 :rule-classes nil)

(defun fn2-update-sibling-reader-live (mutant)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-update-fixture-init fn2-core))
          (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp 0)))
          (source (fn2-update-sibling-read 0 fn2-core)))
    (stobj-let ((fn2-update-sibling (fn2-core-sibling fn2-core))) (answer)
     (let ((child (fn2-update-sibling-read-child 0 fn2-update-sibling)))
      (and pre (equal source 91) (equal source child)
           (if mutant (not (equal source (+ 1 child))) t)))
     (mv answer fn2-core)))
   answer)))
(defun fn2-update-sibling-read-child-refines-core-positive ()
 (declare (xargs :verify-guards nil)) (fn2-update-sibling-reader-live nil))
(defun fn2-update-sibling-read-child-refines-core-negative ()
 (declare (xargs :verify-guards nil)) (fn2-update-sibling-reader-live t))
(defun fn2-update-sibling-write-live (mutant)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-update-fixture-init fn2-core))
          (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                    (natp 0) (unsigned-byte-p 8 42))))
    (mv-let (source fn2-core) (fn2-update-with-sibling-read 0 42 fn2-core)
     (let* ((source-after (fn2-update-fixture-snapshot fn2-core))
            (fn2-core (fn2-update-fixture-init fn2-core)))
      (mv-let (candidate fn2-core) (fn2-update-with-sibling-read-child-core-face 0 42 fn2-core)
       (let* ((fn2-core (if mutant
                            (stobj-let ((fn2-update-sibling (fn2-core-sibling fn2-core))) (fn2-update-sibling)
                             (fn2-update-sibling-set-value 0 0 fn2-update-sibling) fn2-core)
                          fn2-core))
              (after (fn2-update-fixture-snapshot fn2-core)))
        (mv (and pre (equal source 91) (equal source candidate)
                 (equal source-after '(1 42 1 91))
                 (if mutant (and (equal after '(1 42 1 0)) (not (equal source-after after)))
                   (equal source-after after))) fn2-core))))))
   answer)))
(defun fn2-update-with-sibling-read-child-refines-core-positive ()
 (declare (xargs :verify-guards nil)) (fn2-update-sibling-write-live nil))
(defun fn2-update-with-sibling-read-child-refines-core-negative ()
 (declare (xargs :verify-guards nil)) (fn2-update-sibling-write-live t))
(fn2-check-lowering-teeth fn2-update-sibling-read fn2-update-with-sibling-read)

;; Preserve the actual conditional-write counterexample before totalization.
(defun fn2-conditional-source (flag i value fn2-core)
 (declare (xargs :stobjs fn2-core :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (if flag (fn2-update-source i value fn2-core) (mv :off fn2-core)))
(defun fn2-conditional-writeback-mutant (flag i value fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (mv-let (answer fn2-core) (fn2-conditional-source flag i value fn2-core)
  (stobj-let ((fn2-update-config (fn2-core-config fn2-core))) (fn2-update-config)
   fn2-update-config (mv answer fn2-core))))
(defthm fn2-conditional-writeback-counterexample
 (and (not (fn2-corep nil))
      (equal (fn2-conditional-source nil 0 42 nil) '(:off nil))
      (equal (fn2-conditional-writeback-mutant nil 0 42 nil) '(:off (nil)))
      (not (equal (fn2-conditional-source nil 0 42 nil)
                  (fn2-conditional-writeback-mutant nil 0 42 nil))))
 :hints (("Goal" :in-theory
          (e/d (fn2-conditional-source fn2-conditional-writeback-mutant)
               ((:executable-counterpart fn2-conditional-source)
                (:executable-counterpart fn2-conditional-writeback-mutant)))))
 :rule-classes nil)
(defcore-product-child fn2-conditional-source fn2-conditional-child)
(assert-event
 (let ((row (cdr (assoc-eq 'fn2-conditional-source (table-alist 'fn2-core-lowered (w state))))))
  (and (eq (fn2-decl-get :execution row) 'fn2-conditional-child-exec-core-face)
       (eq (fn2-decl-get :guarded-refinement row) 'fn2-conditional-child-guarded-execution-refines-core)
       (eq (fn2-decl-get :execution-correspondence row) 'fn2-conditional-child-execution-correspondence)
       (eq (fn2-decl-get :execution-obligation row) 'fn2-conditional-child-guarded-execution-refines-core)
       (equal (fn2-update-call-count 'fn2-corep
                (getpropc 'fn2-conditional-child-exec-core-face 'unnormalized-body nil (w state))) 0)
       (equal (fn2-update-call-count 'fn2-conditional-source
                (getpropc 'fn2-conditional-child-exec-core-face 'unnormalized-body nil (w state))) 0)
       (equal (fn2-update-call-count 'fn2-conditional-source
                (getpropc 'fn2-conditional-child 'unnormalized-body nil (w state))) 0))))
(defthm fn2-conditional-totalization-control
 (and (not (fn2-corep nil))
      (equal (fn2-conditional-child-core-face nil 0 42 nil) '(:off nil))
      (equal (fn2-conditional-child-exec-core-face nil 0 42 nil) '(:off (nil))))
 :hints (("Goal" :in-theory
          (e/d (fn2-conditional-child-exec-core-face fn2-conditional-child fn2-conditional-source)
               ((:executable-counterpart fn2-conditional-child-exec-core-face)
                (:executable-counterpart fn2-conditional-source)))))
 :rule-classes nil)
(assert-event
 (and (eq (symbol-class 'fn2-conditional-child (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn2-conditional-child-exec-core-face (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn2-conditional-child-core-face (w state)) :common-lisp-compliant)))
(defun fn2-conditional-flip-mutant (flag i value fn2-core)
 (declare (xargs :stobjs fn2-core :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (fn2-conditional-source (not flag) i value fn2-core))
(defun fn2-conditional-live (flag mutant)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-update-fixture-init fn2-core))
          (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                    (natp 0) (unsigned-byte-p 8 42))))
    (mv-let (source fn2-core) (fn2-conditional-source flag 0 42 fn2-core)
     (let* ((source-after (fn2-update-fixture-snapshot fn2-core))
            (fn2-core (fn2-update-fixture-init fn2-core)))
      (mv-let (candidate fn2-core)
       (if mutant (fn2-conditional-flip-mutant flag 0 42 fn2-core)
         (fn2-conditional-child-exec-core-face flag 0 42 fn2-core))
       (let* ((after (fn2-update-fixture-snapshot fn2-core))
              (fn2-core (fn2-update-fixture-init fn2-core)))
        (mv-let (totalized fn2-core) (fn2-conditional-child-core-face flag 0 42 fn2-core)
         (mv (and pre
                  (if flag (and (eq source :ok) (equal source-after '(1 42 1 91)))
                    (and (eq source :off) (equal source-after '(1 37 1 91))))
                  (equal totalized source)
                  (equal source-after (fn2-update-fixture-snapshot fn2-core))
                  (if mutant (not (equal (cons source source-after) (cons candidate after)))
                    (equal (cons source source-after) (cons candidate after)))) fn2-core)))))))
   answer)))
(defun fn2-conditional-child-refines-core-positive ()
 (declare (xargs :verify-guards nil))
 (and (fn2-conditional-live nil nil) (fn2-conditional-live t nil)))
(defun fn2-conditional-child-refines-core-negative ()
 (declare (xargs :verify-guards nil))
 (and (fn2-conditional-live nil t) (fn2-conditional-live t t)))
(fn2-check-lowering-teeth fn2-conditional-source)

; Production core fields are opaque. A branch may write only one of the
; declared output children; reconstruction must not disturb the other one.
(defun fn2-update-branch-children (flag i value fn2-core)
 (declare (xargs :stobjs fn2-core
                 :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (if flag (fn2-update-source i value fn2-core)
  (stobj-let ((fn2-update-sibling (fn2-core-sibling fn2-core))) (code fn2-update-sibling)
   (if (< i (fn2-update-sibling-rows fn2-update-sibling))
       (let ((fn2-update-sibling (fn2-update-sibling-set-value i value fn2-update-sibling)))
         (mv :sibling fn2-update-sibling))
     (mv :bounds fn2-update-sibling))
   (mv code fn2-core))))
(encapsulate ()
 (local (in-theory (disable fn2-corep fn2-core-config fn2-core-sibling
                            update-fn2-core-config update-fn2-core-sibling)))
 (defcore-product-closure fn2-update-branch-children fn2-update-branch-children-child))
(defthm fn2-update-branch-children-positive
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 0) (unsigned-byte-p 8 42)
      (equal (fn2-update-branch-children-child-exec-core-face t 0 42 '(((37) 1) ((91) 1)))
             '(:ok (((42) 1) ((91) 1))))
      (equal (fn2-update-branch-children-child-exec-core-face nil 0 42 '(((37) 1) ((91) 1)))
             '(:sibling (((37) 1) ((42) 1)))))
 :hints (("Goal" :in-theory
   (e/d (fn2-update-branch-children-child-exec-core-face fn2-update-branch-children-child)
        ((:executable-counterpart fn2-update-branch-children-child-exec-core-face)))))
 :rule-classes nil)
(defthm fn2-update-branch-children-refusal
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 9) (unsigned-byte-p 8 42)
      (equal (fn2-update-branch-children-child-exec-core-face t 9 42 '(((37) 1) ((91) 1)))
             '(:bounds (((37) 1) ((91) 1))))
      (equal (fn2-update-branch-children-child-exec-core-face nil 9 42 '(((37) 1) ((91) 1)))
             '(:bounds (((37) 1) ((91) 1)))))
 :hints (("Goal" :in-theory
   (e/d (fn2-update-branch-children-child-exec-core-face fn2-update-branch-children-child)
        ((:executable-counterpart fn2-update-branch-children-child-exec-core-face)))))
 :rule-classes nil)

; The source writes in the opposite order from the declared child product.
; Both results and distinct new values must survive reconstruction.
(defun fn2-update-reverse-order (i value fn2-core)
 (declare (xargs :stobjs fn2-core
                 :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (mv-let (first fn2-core) (fn2-update-branch-children nil i 43 fn2-core)
  (mv-let (second fn2-core) (fn2-update-source i value fn2-core)
   (mv first second fn2-core))))
(encapsulate ()
 ; Shared core lenses generate the corresponding read-over-write matrix.




 (local (in-theory (disable fn2-corep fn2-core-config fn2-core-sibling
                            update-fn2-core-config update-fn2-core-sibling)))
 (defcore-product-closure fn2-update-reverse-order fn2-update-reverse-order-child))
(defthm fn2-update-reverse-order-positive
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 0) (unsigned-byte-p 8 42)
      (equal (fn2-update-reverse-order-child-exec-core-face 0 42 '(((37) 1) ((91) 1)))
             '(:sibling :ok (((42) 1) ((43) 1)))))
 :hints (("Goal" :in-theory
   (e/d (fn2-update-reverse-order-child-exec-core-face fn2-update-reverse-order-child)
        ((:executable-counterpart fn2-update-reverse-order-child-exec-core-face)))))
 :rule-classes nil)
(defthm fn2-update-reverse-order-refusal
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 9) (unsigned-byte-p 8 42)
      (equal (fn2-update-reverse-order-child-exec-core-face 9 42 '(((37) 1) ((91) 1)))
             '(:bounds :bounds (((37) 1) ((91) 1)))))
 :hints (("Goal" :in-theory
   (e/d (fn2-update-reverse-order-child-exec-core-face fn2-update-reverse-order-child)
        ((:executable-counterpart fn2-update-reverse-order-child-exec-core-face)))))
 :rule-classes nil)

; The compositional lemma covers a proper core spine even when a child's
; logical contents violate its type. This is not an executable guard claim.
(defthm fn2-update-spine-with-invalid-child-control
 (let ((core '(((999) 1) ((91) 1))))
  (and (fn2-product-spinep 2 core)
       (not (fn2-corep core))
       (equal (fn2-update-source 0 42 core) '(:ok (((42) 1) ((91) 1))))
       (equal (fn2-update-child-exec-core-face 0 42 core)
              (fn2-update-source 0 42 core))))
 :hints (("Goal" :in-theory
    (e/d (fn2-product-spinep fn2-update-source fn2-update-child-exec-core-face fn2-update-child
          fn2-update-config-set-value update-fn2-update-config-value$ai)
         ((:executable-counterpart fn2-update-child-exec-core-face)
          (:executable-counterpart fn2-update-config-set-value)
          (:executable-counterpart update-fn2-update-config-value$ai)))))
 :rule-classes nil)
(defthm fn2-update-spine-hypothesis-removal-control
 (and (not (fn2-product-spinep 2 nil))
      (equal (fn2-conditional-source nil 0 42 nil) '(:off nil))
      (equal (fn2-conditional-child-exec-core-face nil 0 42 nil) '(:off (nil)))
      (not (equal (fn2-conditional-source nil 0 42 nil)
                  (fn2-conditional-child-exec-core-face nil 0 42 nil))))
 :hints (("Goal" :in-theory
    (e/d (fn2-product-spinep fn2-conditional-source fn2-conditional-child-exec-core-face fn2-conditional-child)
         ((:executable-counterpart fn2-conditional-child-exec-core-face)))))
 :rule-classes nil)
(assert-event
 (let ((row (cdr (assoc-eq 'fn2-update-source (table-alist 'fn2-core-lowered (w state))))))
  (and (eq (fn2-decl-get :shape-refinement row) 'fn2-update-child-spine-execution-refines-core)
       (eq (fn2-decl-get :shape-reverse row) 'fn2-update-child-core-to-execution)
       (eq (fn2-decl-get :shape-preserved row) 'fn2-update-child-core-spine-preserved)
       (equal (fn2-update-call-count 'fn2-product-spinep
               (getpropc 'fn2-update-child-exec-core-face 'unnormalized-body nil (w state))) 0))))

; Reusing a mutable boundary must preserve its full ABI and verified guard.
(must-fail
 (encapsulate ()
  (local
   (make-event
    (value `(table fn2-core-lowered 'fn2-update-branch-children
             ',(append '(:written (fn2-update-config))
                (cdr (assoc-eq 'fn2-update-branch-children
                       (table-alist 'fn2-core-lowered (w state)))))))))
  (defcore-product-child fn2-update-reverse-order fn2-update-refused-abi)))
(defun fn2-update-unverified-callee (flag i value fn2-update-config fn2-update-sibling)
 (declare (ignore flag i value)
          (xargs :stobjs (fn2-update-config fn2-update-sibling) :verify-guards nil))
 (mv :opaque fn2-update-config fn2-update-sibling))
(must-fail
 (encapsulate ()
  (local
   (make-event
    (value `(table fn2-core-lowered 'fn2-update-branch-children
             ',(append '(:child fn2-update-unverified-callee)
                (cdr (assoc-eq 'fn2-update-branch-children
                       (table-alist 'fn2-core-lowered (w state)))))))))
  (defcore-product-child fn2-update-reverse-order fn2-update-refused-guard)))
(assert-event
 (and (not (function-symbolp 'fn2-update-refused-abi (w state)))
      (not (function-symbolp 'fn2-update-refused-guard (w state)))))

; The intermediate mutable boundary is deliberately undeclared: the closure
; must derive it before the caller, then retain one call per source occurrence.
(defun fn2-update-auto-inner (i value fn2-core)
 (declare (xargs :stobjs fn2-core
                 :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (fn2-update-source i value fn2-core))
(defun fn2-update-auto-outer (i value fn2-core)
 (declare (xargs :stobjs fn2-core
                 :guard (and (natp i) (unsigned-byte-p 8 value) (fn2-core-wfp fn2-core))))
 (mv-let (first fn2-core) (fn2-update-auto-inner i value fn2-core)
  (mv-let (second fn2-core) (fn2-update-auto-inner i 43 fn2-core)
   (mv first second fn2-core))))
(defcore-product-closure fn2-update-auto-outer fn2-update-auto-outer-child)
(assert-event
 (and (equal (fn2-update-call-count 'fn2-update-auto-inner-lowered-child
               (getpropc 'fn2-update-auto-outer-child 'unnormalized-body nil (w state))) 2)
      (equal (fn2-update-call-count 'fn2-update-child
               (getpropc 'fn2-update-auto-inner-lowered-child 'unnormalized-body nil (w state))) 1)
      (equal (fn2-update-call-count 'fn2-update-config-set-value
               (getpropc 'fn2-update-auto-outer-child 'unnormalized-body nil (w state))) 0)))
(defthm fn2-update-auto-outer-positive
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 0) (unsigned-byte-p 8 42)
      (equal (fn2-update-auto-outer-child-core-face 0 42 '(((37) 1) ((91) 1)))
             '(:ok :ok (((43) 1) ((91) 1)))))
 :rule-classes nil)
(defthm fn2-update-auto-outer-refusal
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 9) (unsigned-byte-p 8 42)
      (equal (fn2-update-auto-outer-child-core-face 9 42 '(((37) 1) ((91) 1)))
             '(:bounds :bounds (((37) 1) ((91) 1)))))
 :rule-classes nil)

; Original preservation contracts select optional summaries. The child facts
; are proved independently, and caller guards must use them without unfolding.
(defun fn2-update-invariant-source (fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (fn2-update-source 0 42 fn2-core))
(defthm fn2-update-invariant-source-preserves-type
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
          (fn2-corep (mv-nth 1 (fn2-update-invariant-source fn2-core)))))
(defthm fn2-update-invariant-source-preserves-wfp
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
          (fn2-core-wfp (mv-nth 1 (fn2-update-invariant-source fn2-core)))))
(defcore-product-child fn2-update-invariant-source fn2-update-invariant-child)
(assert-event
 (let ((row (cdr (assoc-eq 'fn2-update-invariant-source (table-alist 'fn2-core-lowered (w state))))))
  (and (equal (fn2-decl-get :child-invariants row)
               '(fn2-update-invariant-child-outputs-preserved
                 fn2-update-invariant-child-output-fn2-update-config-invariants))
       (equal (fn2-product-guard-callees '(fn2-update-invariant-source) (w state)) nil))))
(defun fn2-update-invariant-caller (fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (mv-let (first fn2-core) (fn2-update-invariant-source fn2-core)
  (mv-let (second fn2-core) (fn2-update-invariant-source fn2-core)
   (mv first second fn2-core))))
; Names alone must not select summaries: these formulas are unrelated.
(defthm fn2-update-invariant-caller-preserves-type t :rule-classes nil)
(defthm fn2-update-invariant-caller-preserves-wfp t :rule-classes nil)
(assert-event
 (not (fn2-product-source-invariantp 'fn2-update-invariant-caller
         'fn2-corep "-PRESERVES-TYPE" (w state))))
(defcore-product-child fn2-update-invariant-caller fn2-update-invariant-caller-child)
(defthm fn2-update-invariant-caller-positive
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (equal (fn2-update-invariant-caller-child-core-face '(((37) 1) ((91) 1)))
             '(:ok :ok (((42) 1) ((91) 1)))))
 :rule-classes nil)

(defthm fn2-update-invariant-guard-removal
 (and (not (fn2-update-config-wfp '((37) 2)))
      (not (fn2-update-config-wfp
             (mv-nth 1 (fn2-update-invariant-child '((37) 2)))))))
(assert-event
 (not (fn2-decl-get :child-invariants
        (cdr (assoc-eq 'fn2-update-invariant-caller (table-alist 'fn2-core-lowered (w state)))))))

; A one-child, no-scalar product returns that stobj directly, not an MV tuple.
(defun fn2-update-single-source (fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (mv-let (code fn2-core) (fn2-update-invariant-source fn2-core)
  (declare (ignore code)) fn2-core))
(defthm fn2-update-single-source-preserves-type
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
          (fn2-corep (fn2-update-single-source fn2-core))))
(defthm fn2-update-single-source-preserves-wfp
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
          (fn2-core-wfp (fn2-update-single-source fn2-core))))
(defcore-product-child fn2-update-single-source fn2-update-single-child)
(assert-event
 (and (equal (getpropc 'fn2-update-single-child 'stobjs-out nil (w state)) '(fn2-update-config))
      (consp (fn2-decl-get :child-invariants
        (cdr (assoc-eq 'fn2-update-single-source (table-alist 'fn2-core-lowered (w state))))))))
(defthm fn2-update-single-positive-and-wrong-projection-control
 (and (fn2-update-configp '((37) 1))
      (fn2-update-config-wfp '((37) 1))
      (equal (fn2-update-single-child '((37) 1)) '((42) 1))
      (fn2-update-configp (fn2-update-single-child '((37) 1)))
      (fn2-update-config-wfp (fn2-update-single-child '((37) 1)))
      (not (fn2-update-configp (mv-nth 0 (fn2-update-single-child '((37) 1))))))
 :rule-classes nil)
(defun fn2-update-single-caller (fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (let ((fn2-core (fn2-update-single-source fn2-core)))
  (fn2-update-single-source fn2-core)))
(defcore-product-child fn2-update-single-caller fn2-update-single-caller-child)
(defthm fn2-update-single-whole-core-positive
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (equal (fn2-update-single-caller-child-core-face '(((37) 1) ((91) 1)))
             '(((42) 1) ((91) 1))))
 :rule-classes nil)

; Singleton scalar recursion reuses the same product emitter and proof contract.
(defun fn2-update-toggle (fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (stobj-let ((fn2-update-config (fn2-core-config fn2-core))) (code fn2-update-config)
  (if (< 0 (fn2-update-config-rows fn2-update-config))
      (let* ((old (fn2-update-config-value 0 fn2-update-config))
             (fn2-update-config (fn2-update-config-set-value 0 (if (equal old 37) 42 37) fn2-update-config)))
        (mv :ok fn2-update-config))
    (mv :bounds fn2-update-config))
  (mv code fn2-core)))
(defthm fn2-update-toggle-preserves-type
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
          (fn2-corep (mv-nth 1 (fn2-update-toggle fn2-core)))))
(defthm fn2-update-toggle-preserves-wfp
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
          (fn2-core-wfp (mv-nth 1 (fn2-update-toggle fn2-core)))))
(defcore-product-child fn2-update-toggle fn2-update-toggle-child)
(defun fn2-update-repeat (n count fn2-core)
 (declare (xargs :stobjs fn2-core :measure (nfix n)
                 :guard (and (natp n) (natp count) (fn2-core-wfp fn2-core))))
 (if (zp n) (mv :ok count fn2-core)
  (mv-let (code fn2-core) (fn2-update-toggle fn2-core)
   (if (eq code :ok) (fn2-update-repeat (- n 1) (+ count 1) fn2-core)
    (mv code count fn2-core)))))
(defthm fn2-update-repeat-preserves-type
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
          (fn2-corep (mv-nth 2 (fn2-update-repeat n count fn2-core)))))
(defthm fn2-update-repeat-preserves-wfp
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
          (fn2-core-wfp (mv-nth 2 (fn2-update-repeat n count fn2-core)))))
(defcore-recursive-product-child fn2-update-repeat fn2-update-repeat-child)

(defthm fn2-update-repeat-whole-result-controls
 (and (fn2-corep '(((37) 1) ((91) 1)))
      (fn2-core-wfp '(((37) 1) ((91) 1)))
      (natp 2) (natp 10)
      (equal (fn2-update-repeat-child-core-face 1 10 '(((37) 1) ((91) 1)))
             '(:ok 11 (((42) 1) ((91) 1))))
      (equal (fn2-update-repeat-child-core-face 2 10 '(((37) 1) ((91) 1)))
             '(:ok 12 (((37) 1) ((91) 1))))
      (equal (fn2-update-repeat-child-core-face 2 10 '((nil 0) ((91) 1)))
             '(:bounds 10 ((nil 0) ((91) 1))))
      (equal (fn2-update-repeat-child-core-face 2 10 '(((37) 1) ((91) 1)))
             (fn2-update-repeat 2 10 '(((37) 1) ((91) 1)))))
 :hints (("Goal" :expand ((:free (n count fn2-core) (fn2-update-repeat n count fn2-core))) :in-theory (e/d (fn2-update-repeat fn2-update-toggle)
   ((:executable-counterpart fn2-update-repeat) (:executable-counterpart fn2-update-toggle)))))
 :rule-classes nil)
(defthm fn2-update-repeat-spine-removal-control
 (and (not (fn2-product-spinep 2 nil))
      (equal (fn2-update-repeat-child-core-face 0 10 nil)
             (fn2-update-repeat 0 10 nil))
      (not (equal (fn2-update-repeat-child-exec-core-face 0 10 nil)
                  (fn2-update-repeat 0 10 nil))))
 :hints (("Goal" :expand ((fn2-update-repeat-child 0 10 nil))
   :in-theory (e/d (fn2-update-repeat-child-exec-core-face fn2-update-repeat-child)
    ((:executable-counterpart fn2-update-repeat-child-exec-core-face)
     (:executable-counterpart fn2-update-repeat-child)))))
 :rule-classes nil)
(assert-event
 (and (equal (fn2-update-call-count 'fn2-update-repeat-child
               (getpropc 'fn2-update-repeat-child 'unnormalized-body nil (w state))) 1)
      (equal (fn2-update-call-count 'fn2-update-toggle-child
               (getpropc 'fn2-update-repeat-child 'unnormalized-body nil (w state))) 1)
      (equal (getpropc 'fn2-update-repeat-child 'stobjs-out nil (w state))
             '(nil nil fn2-update-config))
      (eq (symbol-class 'fn2-update-repeat-child (w state)) :common-lisp-compliant)))
(defun fn2-update-state-measure (n fn2-core)
 (declare (xargs :stobjs fn2-core :guard (natp n) :measure (+ (nfix n) (acl2-count fn2-core))))
 (if (zp n) (mv :ok fn2-core)
  (fn2-update-state-measure (- n 1) fn2-core)))
(must-fail (defcore-recursive-product-child fn2-update-state-measure fn2-update-state-measure-child))
(mutual-recursion
 (defun fn2-update-mutual-a (n fn2-core)
  (declare (xargs :stobjs fn2-core :guard (natp n) :measure (nfix n)))
  (if (zp n) (mv :ok fn2-core) (fn2-update-mutual-b (- n 1) fn2-core)))
 (defun fn2-update-mutual-b (n fn2-core)
  (declare (xargs :stobjs fn2-core :guard (natp n) :measure (nfix n)))
  (if (zp n) (mv :ok fn2-core) (fn2-update-mutual-a (- n 1) fn2-core))))
(must-fail (defcore-recursive-product-child fn2-update-mutual-a fn2-update-mutual-child))
(assert-event
 (and (not (assoc-eq 'fn2-update-state-measure (table-alist 'fn2-core-lowered (w state))))
      (not (assoc-eq 'fn2-update-mutual-a (table-alist 'fn2-core-lowered (w state))))
      (not (function-symbolp 'fn2-update-state-measure-child (w state)))
      (not (function-symbolp 'fn2-update-mutual-child (w state)))))

(defun fn2-update-repeat-runtime-witness ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-update-fixture-init fn2-core))
          (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp 2) (natp 10))))
    (mv-let (source-code source-count fn2-core) (fn2-update-repeat 2 10 fn2-core)
     (let* ((source-after (fn2-update-fixture-snapshot fn2-core))
            (fn2-core (fn2-update-fixture-init fn2-core)))
      (mv-let (code count fn2-core) (fn2-update-repeat-child-core-face 2 10 fn2-core)
       (let* ((after (fn2-update-fixture-snapshot fn2-core))
              (fn2-core (fn2-update-fixture-init fn2-core)))
        (mv-let (mutant-code mutant-count fn2-core) (fn2-update-repeat-child-core-face 1 10 fn2-core)
         (mv (and pre (eq source-code code) (eq code :ok) (equal source-count count)
                  (equal count 12) (equal source-after after) (equal after '(1 37 1 91))
                  (eq mutant-code :ok) (equal mutant-count 11)
                  (not (equal mutant-count count))
                  (equal (fn2-update-fixture-snapshot fn2-core) '(1 42 1 91))) fn2-core)))))))
   answer)))
(assert-event (fn2-update-repeat-runtime-witness))
