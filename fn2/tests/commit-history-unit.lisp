; Real B3 sealing and independent B2/root-recipe recovery controls, before I/O.
(in-package "ACL2")
(include-book "../sim/commit-history")
(local (defthm fn2-b-probe-countdown
 (implies (not (zp left)) (o< (nfix (- left 1)) (nfix left))) :rule-classes nil))
(local (defthm fn2-b-probe-count-op (o-p (nfix left)) :rule-classes nil))
(defun fn2-b-format-probe-loop (left turn a b fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix left)
  :hints (("Goal" :use (fn2-b-probe-countdown fn2-b-probe-count-op) :in-theory nil))))
 (b* ((pa (fn2-machine-phase a fn2-core)) (pb (fn2-machine-phase b fn2-core))
      ((when (or (zp left) (and (= pa *fn2-commit-state-dependencies*)
                                (= pb *fn2-commit-state-dependencies*)))) fn2-core)
      (id (cond ((= pa *fn2-commit-state-dependencies*) b)
                ((= pb *fn2-commit-state-dependencies*) a)
                ((equal (mod (nfix turn) 2) 0) a) (t b)))
      ((mv & & & & fn2-core) (fn2-commit-run id 4 fn2-core)))
  (fn2-b-format-probe-loop (- left 1) (+ 1 (nfix turn)) a b fn2-core)))
(defun fn2-b-node-controls (indices node manifest previous)
 (declare (xargs :verify-guards nil))
 (if (atom indices) nil
  (cons (not (fn2-b-nodep
         (update-nth (car indices) (if (equal (car indices) 0) *fn2-b-zero-digest*
                                    (+ 1 (nfix (nth (car indices) node)))) node)
         manifest previous))
        (fn2-b-node-controls (cdr indices) node manifest previous))))
(defun fn2-b-ref-controls (indices seal manifest records-frame previous)
 (declare (xargs :verify-guards nil))
 (if (atom indices) nil
  (cons (not (fn2-b-seal-rootp (update-nth (car indices) 0 seal)
                             manifest records-frame previous))
        (fn2-b-ref-controls (cdr indices) seal manifest records-frame previous))))
(defun fn2-b-root-recipe-controls (manifest page records-frame seal-frame previous)
 (declare (xargs :verify-guards nil))
 (b* (((mv code bytes) (fn2-b-frame-payload seal-frame *frame-kind-seal*))
      ((mv parsed seal &) (fn2-layout-parse *fn2-format-sealed-batch* bytes))
      ((mv nc node rest) (fn2-layout-parse *fn2-commit-manifest-node* (take 73 (nthcdr 96 page)))))
  (append
   (fn2-b-node-controls '(0 1 2 3 4 5 6) node manifest previous)
   (fn2-b-ref-controls
    (list *fn2-format-sealed-batch-field-dependencies-page-kind*
          *fn2-format-sealed-batch-field-metadata-edits-page-kind*
          *fn2-format-sealed-batch-field-output-physical-manifest-page-kind*
          *fn2-format-sealed-batch-field-allocation-retirement-page-kind*
          *fn2-format-sealed-batch-field-output-allocation-changes-page-kind*
          *fn2-format-sealed-batch-field-event-frontier-page-kind*
          *fn2-format-sealed-batch-field-output-event-frontier-page-kind*)
    seal manifest records-frame previous)
  (list
   (and (eq nc :ok) (null rest) (fn2-b-nodep node manifest previous))
   (and (eq code :ok) (eq parsed :ok) (not (equal previous *fn2-b-zero-digest*))
        (fn2-b-seal-rootp seal manifest records-frame previous))
   (not (fn2-b-seal-rootp
         (update-nth *fn2-format-sealed-batch-field-input-root* *fn2-b-zero-digest* seal)
         manifest records-frame previous))
   (not (fn2-b-seal-rootp
         (update-nth *fn2-format-sealed-batch-field-output-suffix-first* 2 seal)
         manifest records-frame previous))
   (not (fn2-b-seal-rootp
         (update-nth *fn2-format-sealed-batch-field-output-checkpoint-base-physical-unit* 1 seal)
         manifest records-frame previous))))))
; Each mutation reaches the actual BH1 checker: its logical adapter loads
; the changed named expectation into a digest row, not a byte-list comparison.
(defun fn2-b-digest-binding-controls (manifest page seal-frame previous)
 (declare (xargs :verify-guards nil))
 (b* (((mv & seal-bytes) (fn2-b-frame-payload seal-frame *frame-kind-seal*))
      ((mv & & rest) (fn2-layout-parse *fn2-format-sealed-batch* seal-bytes))
      (page-context (fn2-b-context manifest 0 previous))
      (seal-context (fn2-b-context manifest 2 previous))
      (seal-bytes (take (- (len seal-bytes) (len rest)) seal-bytes)))
  (list
   (not (fn2-fc-acceptedp :page page
         (update-fn2-fc-expected-hash-0 (logxor 1 (fn2-fc-expected-hash-0 page-context)) page-context)))
   (not (fn2-fc-acceptedp :page page
         (update-fn2-fc-expected-hash-1 (logxor 1 (fn2-fc-expected-hash-1 page-context)) page-context)))
   (not (fn2-fc-acceptedp :page page
         (update-fn2-fc-expected-hash-2 (logxor 1 (fn2-fc-expected-hash-2 page-context)) page-context)))
   (not (fn2-fc-acceptedp :page page
         (update-fn2-fc-expected-hash-3 (logxor 1 (fn2-fc-expected-hash-3 page-context)) page-context)))
   (not (fn2-fc-acceptedp :page page
         (update-fn2-fc-expected-hash-4 (logxor 1 (fn2-fc-expected-hash-4 page-context)) page-context)))
   (not (fn2-fc-acceptedp :page page
         (update-fn2-fc-expected-hash-5 (logxor 1 (fn2-fc-expected-hash-5 page-context)) page-context)))
   (not (fn2-fc-acceptedp :page page
         (update-fn2-fc-expected-hash-6 (logxor 1 (fn2-fc-expected-hash-6 page-context)) page-context)))
   (not (fn2-fc-acceptedp :page page
         (update-fn2-fc-expected-hash-7 (logxor 1 (fn2-fc-expected-hash-7 page-context)) page-context)))
   (not (fn2-fc-acceptedp :seal seal-bytes
         (update-fn2-fc-expected-previous-seal-0 (logxor 1 (fn2-fc-expected-previous-seal-0 seal-context)) seal-context)))
   (not (fn2-fc-acceptedp :seal seal-bytes
         (update-fn2-fc-expected-previous-seal-1 (logxor 1 (fn2-fc-expected-previous-seal-1 seal-context)) seal-context)))
   (not (fn2-fc-acceptedp :seal seal-bytes
         (update-fn2-fc-expected-previous-seal-2 (logxor 1 (fn2-fc-expected-previous-seal-2 seal-context)) seal-context)))
   (not (fn2-fc-acceptedp :seal seal-bytes
         (update-fn2-fc-expected-previous-seal-3 (logxor 1 (fn2-fc-expected-previous-seal-3 seal-context)) seal-context)))
   (not (fn2-fc-acceptedp :seal seal-bytes
         (update-fn2-fc-expected-previous-seal-4 (logxor 1 (fn2-fc-expected-previous-seal-4 seal-context)) seal-context)))
   (not (fn2-fc-acceptedp :seal seal-bytes
         (update-fn2-fc-expected-previous-seal-5 (logxor 1 (fn2-fc-expected-previous-seal-5 seal-context)) seal-context)))
   (not (fn2-fc-acceptedp :seal seal-bytes
         (update-fn2-fc-expected-previous-seal-6 (logxor 1 (fn2-fc-expected-previous-seal-6 seal-context)) seal-context)))
   (not (fn2-fc-acceptedp :seal seal-bytes
         (update-fn2-fc-expected-previous-seal-7 (logxor 1 (fn2-fc-expected-previous-seal-7 seal-context)) seal-context))))))

; Deliberate test-only row corruptions, captured through the real visibility
; reader. These are projection controls, not legal machine executions.
(defun fn2-b-notification-controls (id events fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((ids (list id)) (before (fn2-b-visibility ids fn2-core))
      (batch (fn2-machine-batch-no id fn2-core))
      (fn2-core (fn2-commit-put-core id (cb-acks 3)))
      (over (fn2-b-visibility ids fn2-core))
      (fn2-core (fn2-commit-put-core id (cb-acks 2)))
      (at-limit (fn2-b-visibility ids fn2-core))
      (fn2-core (fn2-commit-put-core id (cb-acks 1)))
      (lower (fn2-b-visibility ids fn2-core))
      (fn2-core (fn2-commit-put-core id (cb-acks 0))))
  (mv (list (equal (fn2-b-project-visible before before events) events)
            (equal (fn2-b-project-visible at-limit at-limit events) events)
            (equal (car (fn2-b-project-visible before over events))
                   (list :projection-error :notification batch))
            (equal (car (fn2-b-project-visible at-limit lower events))
                   (list :projection-error :notification batch))) fn2-core)))

(defun fn2-b-format-probe-execute (mode fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((profile (fn2-b-test-profile *fn2-profile-tiny* mode))
      (fn2-core (fn2-core-init profile fn2-core))
      ((mv ec fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
        (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
      (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
      (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
      ((mv ca ea & fn2-core) (fn2-b-start a 2 1 mode b fn2-core))
      ((mv cb eb & fn2-core) (fn2-b-start b 2 3 mode a fn2-core))
      (fn2-core (fn2-b-format-probe-loop 600 0 a b fn2-core))
      (ma (fn2-b-manifest a fn2-core)) (mb (fn2-b-manifest b fn2-core))
      ((unless (and ma mb))
       (mv (list :missing-manifest ec ca cb
                 (fn2-machine-phase a fn2-core) (fn2-machine-cb-stage a fn2-core)
                 (fn2-machine-phase b fn2-core) (fn2-machine-cb-stage b fn2-core)) fn2-core))
      ((mv a0 pagea) (fn2-b-pool-image a 0 fn2-core))
      ((mv a1 recordsa) (fn2-b-pool-image a 1 fn2-core))
      ((mv a2 seala) (fn2-b-pool-image a 2 fn2-core))
      ((mv b0 pageb) (fn2-b-pool-image b 0 fn2-core))
      ((mv b1 recordsb) (fn2-b-pool-image b 1 fn2-core))
      ((mv b2 sealb) (fn2-b-pool-image b 2 fn2-core))
      ((mv rc0 batcha previous) (fn2-b-recover-images ma *fn2-b-zero-digest* pagea recordsa seala))
      ((mv rc1 batchb &) (fn2-b-recover-images mb previous pageb recordsb sealb))
      (controls (append (fn2-b-root-recipe-controls mb pageb recordsb sealb previous)
                        (fn2-b-digest-binding-controls mb pageb sealb previous)))
      ((mv notification-controls fn2-core)
       (fn2-b-notification-controls a (reverse (append ea eb)) fn2-core))
      (controls (append controls notification-controls)))
  (mv (list (and (equal (list ec ca cb a0 a1 a2 b0 b1 b2 rc0 rc1)
                       '(:ok :ok :ok :ok :ok :ok :ok :ok :ok :ok :ok))
                  (equal batcha (fn2-b-manifest-batch ma))
                  (equal batchb (fn2-b-manifest-batch mb)) (and (equal (len controls) 39) (not (member-equal nil controls))))
            ec ca cb a0 a1 a2 b0 b1 b2 rc0 rc1 controls) fn2-core)))
(defun fn2-b-format-probe (mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (result fn2-core) (fn2-b-format-probe-execute mode fn2-core) result)))

(assert-event (equal (car (fn2-b-format-probe 0)) t))
(assert-event (equal (car (fn2-b-format-probe 1)) t))
