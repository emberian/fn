(in-package "ACL2")
(include-book "../../books/owner-commit-held-durability")
(include-book "../../books/owner-commit-durability-concrete")
(include-book "must-fail-checked")

(defconst *gc-held-init* (fn-ocp-gc-init 512 65536 2 4096))
(defconst *gc-held-events*
  '((:start) (:reserve :current 1) (:take :current (65) 1)
    (:member :current (:accepted t)) (:seal-held)))
(defconst *gc-held-sealed* (fn-ocp-gc-run *gc-held-init* *gc-held-events*))
(defconst *gc-held-done*
  (fn-ocp-gc-run *gc-held-sealed*
    '((:io :current :ok) (:io :current :ok) (:io :current :ok)
      (:io :current :ok) (:io :current :ok) (:collect))))
(defconst *gc-held-finished* (fn-ocp-gc-entry-reader-advance *gc-held-done*))

; Entire initial and preservation antecedents/conclusions, with a real record.
(assert-event
 (and (fn-ocp-gc-held-coherentp *gc-held-init*)
      (fn-ocp-gc-linkedp *gc-held-sealed*)
      (fn-ocp-gc-held-coherentp *gc-held-sealed*)
      (fn-otm-held (nth 1 *gc-held-sealed*))
      (equal (nth 4 *gc-held-sealed*) :intents)
      (equal (car (nth 14 *gc-held-sealed*)) :held)
      (equal (cadr (nth 14 *gc-held-sealed*)) :sync)
      (fn-ocp-gc-held-coherentp (fn-ocp-gc-entry-start-next *gc-held-sealed*))
      (equal (nth 5 (fn-ocp-gc-entry-start-next *gc-held-sealed*)) :idle)
      (equal (fn-lgk-pipe-d (nth 0 *gc-held-sealed*)) 0)))
(assert-event
 (and (fn-ocp-gc-linkedp *gc-held-done*)
      (fn-ocp-gc-held-coherentp *gc-held-done*)
      (fn-otm-held (nth 1 *gc-held-done*))
      (equal (nth 4 *gc-held-done*) :collected)
      (equal (fn-lgk-pipe-d (nth 0 *gc-held-done*)) 1)
      (fn-ocp-gc-held-coherentp *gc-held-finished*)
      (fn-ocp-gc-linkedp *gc-held-finished*)
      (not (fn-otm-held (nth 1 *gc-held-finished*)))
      (equal (nth 14 *gc-held-finished*) :submit)
      (equal (fn-ocvm-c (nth 2 *gc-held-finished*)) 1)))
(assert-event
 (let ((failed (fn-ocp-gc-entry-syncer *gc-held-sealed* :current :uncertain)))
   (and (fn-ocp-gc-linkedp failed) (fn-ocp-gc-held-coherentp failed)
        (equal (nth 4 failed) :stopped)
        (equal (nth 9 failed) '(:uncertain-reply))
        (not (equal (nth 14 (fn-ocp-gc-entry-reader-advance failed)) :submit)))))
(assert-event
 (let ((empty (fn-ocp-gc-entry-seal-held (fn-ocp-gc-entry-start *gc-held-init*))))
   (and (fn-ocp-gc-linkedp empty) (fn-ocp-gc-held-coherentp empty)
        (not (fn-otm-held (nth 1 empty)))
        (equal (cadr (nth 14 empty)) :submit))))

; Removal: the signed LINKEDP admits a stray held flag at idle; the separate
; held invariant excludes it. No narrowing of LINKEDP conceals this witness.
(defconst *gc-held-malformed*
  (update-nth 1 (update-nth 3 t (nth 1 *gc-held-init*)) *gc-held-init*))
(assert-event (and (fn-ocp-gc-linkedp *gc-held-malformed*)
                   (not (fn-ocp-gc-held-coherentp *gc-held-malformed*))))
(must-fail-checked
 (assert-event (fn-ocp-gc-held-coherentp (fn-ocp-gc-entry-start *gc-held-malformed*))))
; Removing the fence: neither early collection nor reader advance submits.
(must-fail-checked
 (assert-event
   (equal (nth 14 (fn-ocp-gc-entry-reader-advance
                   (fn-ocp-gc-entry-complete *gc-held-sealed*))) :submit)))
(value-triple :held-positive-and-removal-witnesses-passed)
