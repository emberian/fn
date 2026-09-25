; Witnesses and teeth for the general per-step K0
; (books/byte-store-k0-step.lisp, fn-bs-program-step-preserves-relation).
; The witnesses are reachable: the K5 fixture's second publication at its
; completing pair (two retained records, kernel :completing 1 1) and the
; committed-history marker program run from it, and the same fixture's record
; program at its link and barrier pairs.  Each witness checks that the step's
; precondition holds and so does the conclusion, for :ok and for an error
; outcome.
(in-package "ACL2")
(include-book "../../books/byte-store-k0-step")
(include-book "byte-store-k0-marker-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bsks-concl (bs ks step outcome)
  (mv-let (r bs1 ks1) (fn-bs-step bs ks step outcome *bsk5-groups* *bsk5-capacity*)
    (declare (ignore r))
    (and (fn-bs-k0-coveredp bs1 ks1)
         (or (equal ks1 ks) (equal (car step) :observe)))))
(defun bsks-ok (bs ks step outcome)
  (and (fn-bs-k0-coveredp bs ks)
       (fn-bs-k0-step-inputp bs ks step outcome)
       (bsks-concl bs ks step outcome)))
(defconst *bsks-stage* ".stage-marker-k0")
(defun bsks-b (k) (car (nth k (bskm-good))))
(defun bsks-k () (cdr (bskm-pair)))
(defun bsks-frame () (fn-hm-after-commit 1))

; :create (ok, EIO), :write-all (ok, a short write), :fsync-file (ok, EIO
; landing nothing), :rename onto the marker (ok, an issued EIO, an unissued
; EIO), :fsync-dir :root over the pending marker (ok, EIO dropping it), :cut
; at the covered-not-related pair, :unlink in :staging.
(assert-event (bsks-ok (car (bskm-pair)) (bsks-k) (list :create :staging *bsks-stage*) :ok))
(assert-event (bsks-ok (car (bskm-pair)) (bsks-k) (list :create :staging *bsks-stage*) :eio))
(assert-event (bsks-ok (bsks-b 1) (bsks-k) (list :write-all :staging *bsks-stage* (bsks-frame)) :ok))
(assert-event (bsks-ok (bsks-b 1) (bsks-k) (list :write-all :staging *bsks-stage* (bsks-frame)) '(:eio . 3)))
(assert-event (bsks-ok (bsks-b 3) (bsks-k) (list :fsync-file :staging *bsks-stage*) :ok))
(assert-event (bsks-ok (bsks-b 3) (bsks-k) (list :fsync-file :staging *bsks-stage*) '(:eio . nil)))
(assert-event (bsks-ok (bsks-b 5) (bsks-k) (list :rename :staging *bsks-stage* :root *fn-bs-history-marker-name*) :ok))
(assert-event (bsks-ok (bsks-b 5) (bsks-k) (list :rename :staging *bsks-stage* :root *fn-bs-history-marker-name*) '(:eio . :issued)))
(assert-event (bsks-ok (bsks-b 5) (bsks-k) (list :rename :staging *bsks-stage* :root *fn-bs-history-marker-name*) '(:eio . :lost)))
(assert-event (and (not (fn-bs-store-relation (bsks-b 7) (bsks-k)))
                   (fn-bs-k0-coveredp (bsks-b 7) (bsks-k))))
(assert-event (bsks-ok (bsks-b 7) (bsks-k) (list :fsync-dir :root) :ok))
(assert-event (bsks-ok (bsks-b 7) (bsks-k) (list :fsync-dir :root) '(:eio . nil)))
(assert-event (bsks-ok (bsks-b 7) (bsks-k) (list :cut "marker-replaced") :ok))
(assert-event (bsks-ok (bsks-b 9) (bsks-k) (list :unlink :staging *bsks-stage*) :ok))
; :observe: the completion observations from the completing pair.
(assert-event (bsks-ok (car (bskm-pair)) (bsks-k) (list :observe (list :core-completion 1 1)) :ok))

; Teeth.  Drop coverage: the completing kernel over the initial byte image
; (every precondition of the create holds; the conclusion does not).
(assert-event (fn-bs-k0-step-inputp (bsk5-initial) (bsks-k) (list :create :staging *bsks-stage*) :ok))
(must-fail (assert-event (bsks-ok (bsk5-initial) (bsks-k) (list :create :staging *bsks-stage*) :ok)))
(assert-event (not (bsks-concl (bsk5-initial) (bsks-k) (list :create :staging *bsks-stage*) :ok)))
; Drop the step precondition: a write to the configuration inode (D2) from
; the related completing pair.
(assert-event (fn-bs-k0-coveredp (car (bskm-pair)) (bsks-k)))
(assert-event (not (fn-bs-k0-step-inputp (car (bskm-pair)) (bsks-k) (list :write-all :root "config.json" '(1 2 3)) :ok)))
(must-fail (assert-event (bsks-concl (car (bskm-pair)) (bsks-k) (list :write-all :root "config.json" '(1 2 3)) :ok)))
