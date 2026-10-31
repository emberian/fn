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

; R7 restricted-arm-language refusals (decision 2), each beside the shape it
; refuses; each fails at expansion with a named message.
(include-book "std/testing/must-fail" :dir :system)
(defun fn2-arm-test-hidden-write (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-echo-put-core 0 (off 7)))
; 1. a write to a field outside :writes
(must-fail (defmachine-callback fn2-arm-bad-write fn2-test-machine (id budget) 4
  :contract (:cost (:steps 1) :writes () :next () :uses ())
  (let ((fn2-core (fn2-test-machine-put-core id (stopped 1)))) (fn2-machine-result 0 1 0 nil fn2-core)))
  :with-output-off nil)
; 2. a move to a phase outside :next
(must-fail (defmachine-callback fn2-arm-bad-next fn2-test-machine (id budget) 4
  :contract (:cost (:steps 1) :writes () :next () :uses ())
  (let ((fn2-core (fn2-test-machine-put-core id (phase *fn2-test-machine-state-step*))))
    (fn2-machine-result 0 1 0 nil fn2-core)))
  :with-output-off nil)
; 3. a helper that hides a foreign-table write (no defcost, not in :uses)
(must-fail (defmachine-callback fn2-arm-bad-helper fn2-test-machine (id budget) 4
  :contract (:cost (:steps 1) :writes () :next () :uses ())
  (let ((fn2-core (fn2-arm-test-hidden-write fn2-core))) (fn2-machine-result 0 1 0 nil fn2-core)))
  :with-output-off nil)
; ... and declaring it in :uses does not help: it has no defcost.
(must-fail (defmachine-callback fn2-arm-bad-helper-used fn2-test-machine (id budget) 4
  :contract (:cost (:steps 1) :writes () :next () :uses (fn2-arm-test-hidden-write))
  (let ((fn2-core (fn2-arm-test-hidden-write fn2-core))) (fn2-machine-result 0 1 0 nil fn2-core)))
  :with-output-off nil)
; 4. a stale row read: the field is read after this arm wrote it
(must-fail (defmachine-callback fn2-arm-bad-stale fn2-test-machine (id budget) 4
  :contract (:cost (:steps 1) :writes (stopped) :next () :uses ())
  (let ((fn2-core (fn2-test-machine-put-core id (stopped 1))))
    (fn2-machine-result 0 (if (equal row-stopped 1) 1 0) 0 nil fn2-core)))
  :with-output-off nil)
; 5. a cost that cites an undeclared call
(must-fail (defmachine-callback fn2-arm-bad-cost fn2-test-machine (id budget) 4
  :contract (:cost (:steps (:cost fn2-arm-test-hidden-write :steps)) :writes () :next ()
             :uses (fn2-arm-test-hidden-write))
  (fn2-machine-result 0 1 0 nil fn2-core))
  :with-output-off nil)
; Positive control: the same shapes within their contract are admitted.
(defmachine-callback fn2-arm-good fn2-test-machine (id budget) 4
  :contract (:cost (:steps 1) :writes (stopped) :next (:step) :uses ())
  (let* ((was row-stopped)
         (fn2-core (fn2-test-machine-put-core id (stopped 1) (phase *fn2-test-machine-state-step*))))
    (fn2-machine-result 0 (if (equal was 1) 1 0) 0 nil fn2-core)))
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
   '(:step fn2-test-machine-step :cost (:bytes 5000) :writes () :next (:step) :uses ()) nil (w state)))
(assert-event
 (fn2-machine-arm-problem 'fn2-test-machine
   '(:step fn2-test-machine-step :cost (:bytes 4096) :writes () :next () :uses ()) nil (w state)))
(assert-event
 (not (fn2-machine-arm-problem 'fn2-test-machine
        '(:step fn2-test-machine-step :cost (:bytes 4096) :writes () :next (:step) :uses ()) nil (w state))))
(value-triple (cw "R7 ARM LANGUAGE: undeclared write, undeclared next, hidden helper (twice), stale read, uncosted call, undeclared resource effect, over budget, cap without continuation refused; positives admitted PASS~%"))

(fn2-resolve :callbacks)
