; Admit every machine's callbacks before generating final dispatch.
(in-package "ACL2")
(include-book "core-child-assembly-access")
; the machine form's generator, as the served callbacks section includes it
(include-book "../books/machine-arms")

; Each admitted kind's admission and reclamation operations (D 4.5).
(fn2-machine-admission-events)
(fn2-scribe-events)
(fn2-machine-a-events)
(fn2-test-machine-events)

; R7 restricted-arm-language refusals (decision 2) in MACHINE-FORM, each
; beside the shape it refuses; each fails at expansion with a named message.
(include-book "std/testing/must-fail" :dir :system)
(defun fn2-arm-test-hidden-write (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-echo-put-core 0 (off 7)))
; 1. a write to an undeclared field
(must-fail (defmachine-arms fn2-test-machine :core
             :arms ((:step (:set (undeclared 1)) (:charge :steps 1))))
  :with-output-off nil)
; 2. a move to an unknown phase
(must-fail (defmachine-arms fn2-test-machine :core
             :arms ((:step (:next :nowhere) (:charge :steps 1))))
  :with-output-off nil)
; 3. a helper that hides a foreign-table write (no defcost)
(must-fail (defmachine-arms fn2-test-machine :core
             :arms ((:step (:do () (fn2-arm-test-hidden-write)) (:charge :steps 1))))
  :with-output-off nil)
; 4. a stale row read: the field is read after this arm wrote it
(must-fail (defmachine-arms fn2-test-machine :core
             :arms ((:step (:set (stopped 1))
                           (:charge :steps (if (equal row-stopped 1) 1 0)))))
  :with-output-off nil)
; 5. setting phase via :set instead of :next
(must-fail (defmachine-arms fn2-test-machine :core
             :arms ((:step (:set (phase *fn2-test-machine-state-step*)) (:charge :steps 1))))
  :with-output-off nil)
; 6. an undeclared resource effect: an arm in a phase holding nothing that
;    takes a row credit no successor phase holds (refused by the run check).
(assert-event
 (fn2-arm-resource-problem '(:step) '(:step) nil '(fn2-listener-take-credit) (w state)))
(assert-event
 (not (fn2-arm-resource-problem '(:admitting) '(:accepting :closing)
        '((:accepting :accept-credit) (:admitting :accept-credit :connection-row) (:closing :accept-credit))
        '(fn2-machine-admit fn2-listener-return-credit) (w state))))
; 7. over budget and the cap-reaching arm without its own phase: run checks.
(assert-event
 (fn2-machine-arm-problem 'fn2-test-machine
   '(:step fn2-test-machine-run-step :cost (:bytes 5000) :writes () :next (:step) :uses ()) nil nil (w state)))
(assert-event
 (fn2-machine-arm-problem 'fn2-test-machine
   '(:step fn2-test-machine-run-step :cost (:bytes 4096) :writes () :next () :uses ()) nil nil (w state)))
(assert-event
 (not (fn2-machine-arm-problem 'fn2-test-machine
        '(:step fn2-test-machine-run-step :cost (:bytes 4096) :writes () :next (:step) :uses ()) nil nil (w state))))
(value-triple (cw "R7 ARM LANGUAGE: undeclared write, unknown next, hidden helper, stale read, phase-via-set, undeclared resource effect, over budget, cap without continuation refused; positives admitted PASS~%"))

(fn2-resolve :callbacks)
