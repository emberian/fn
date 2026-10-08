(in-package "ACL2")
(include-book "../../books/owner-commit-durability-concrete")

; Diagnose the exact transition, rather than equating failed proof search
; with a counterexample. The matrix includes out-of-order host receipts.
(defun fn-gc-drain-probe (x events)
  (declare (xargs :measure (len events)
    :hints (("Goal" :in-theory (e/d (len) (fn-ocp-gc-host-step fn-ocp-gc-linkedp
                                      fn-ocp-gc-reveals-okp fn-lgk-pipe-d))))))
  (if (atom events) :ok
    (let ((y (fn-ocp-gc-host-step x (car events))))
      (if (and (fn-ocp-gc-linkedp x) (fn-ocp-gc-linkedp y)
               (fn-ocp-gc-reveals-okp y)
               (equal (fn-ocp-gc-project y)
                      (fn-ocp-gc-host-step (fn-ocp-gc-project x) (car events)))
               (<= (fn-lgk-pipe-d (nth 0 x)) (fn-lgk-pipe-d (nth 0 y))))
          (fn-gc-drain-probe x (cdr events))
        (list :bad-step (car events) x y)))))
(defun fn-gc-drain-matrix (x trace events)
  (declare (xargs :measure (len trace)
    :hints (("Goal" :in-theory (e/d (len) (fn-gc-drain-probe fn-ocp-gc-host-step))))))
  (let ((answer (fn-gc-drain-probe x events)))
    (if (or (not (equal answer :ok)) (atom trace)) answer
      (fn-gc-drain-matrix (fn-ocp-gc-host-step x (car trace)) (cdr trace) events))))
(defconst *gc-drain-events*
  '((:begin :current) (:reserve :current 1) (:take :current (65) 1)
    (:member :current (:durable t)) (:seal :current)
    (:io :current :ok) (:io :current :ok) (:io :current :ok)
    (:begin :next) (:reserve :next 4) (:take :next (66) 4)
    (:member :next (:durable t)) (:seal :next)
    (:io :next :ok) (:io :next :ok) (:append-issue) (:io :next :ok)
    (:io :current :ok) (:io :current :ok) (:collect) (:advance)
    (:io :current :ok) (:io :current :ok) (:collect) (:advance)
    ; Two zero-record dependent-member jobs, including a next job.
    (:begin :current) (:member :current (:duplicate t)) (:seal :current)
    (:io :current :ok) (:io :current :ok) (:io :current :ok)
    (:begin :next) (:member :next (:conflict nil)) (:seal :next)
    (:io :next :ok) (:io :next :ok) (:append-issue) (:io :next :ok)
    (:io :current :ok) (:io :current :ok) (:collect) (:advance)
    (:io :current :ok) (:io :current :ok) (:io :current :ok)
    (:collect) (:advance)))
(defconst *gc-drain-probes*
  '((:begin :current) (:begin :next) (:reserve :current 1) (:reserve :next 100)
    (:take :current (67) 1) (:take :current (67) 100)
    (:take :next (67) 1) (:take :next (67) 100)
    (:member :current (:durable t)) (:member :next (:refused nil))
    (:seal :current) (:seal :next) (:append-issue) (:abort :current) (:abort :next)
    (:io :current :ok) (:io :current :uncertain) (:io :current :fault)
    (:io :next :ok) (:io :next :uncertain) (:io :next :fault)
    (:reader) (:collect) (:advance) (:pick (1 1 1 1 1 1))
    (:start) (:reserve :current 4) (:take :current (68) 4) (:member :current (:durable t)) (:seal :current) (:next) (:reserve :next 4) (:take :next (68) 4) (:member :next (:durable t)) (:seal :next) (:unknown)))
(defconst *gc-drain-initial* (fn-ocp-gc-init 512 512 2 4096))
(defconst *gc-drain-matrix-result*
  (fn-gc-drain-matrix *gc-drain-initial* *gc-drain-events* *gc-drain-probes*))
(value-triple *gc-drain-matrix-result*)
(assert-event (equal *gc-drain-matrix-result* :ok))
(defconst *gc-drain-final* (fn-ocp-gc-run *gc-drain-initial* *gc-drain-events*))
(assert-event
 (and (equal (nth 4 *gc-drain-final*) :idle)
      (equal (fn-lgk-pipe-acked (nth 0 *gc-drain-final*)) 2)
      (equal (fn-lgk-pipe-d (nth 0 *gc-drain-final*)) 2)
      (equal (fn-lgk-next-txid (fn-lgk-pipe-ks (nth 0 *gc-drain-final*))) 5)))
(defconst *gc-drain-aborted*
  (fn-ocp-gc-run *gc-drain-initial*
    '((:begin :current) (:reserve :current 1) (:take :current (65) 1)
      (:member :current (:durable t)) (:abort :current))))
(assert-event
 (and (fn-ocp-gc-linkedp *gc-drain-aborted*)
      (equal (nth 4 *gc-drain-aborted*) :stopped-drain)
      (equal (nth 9 *gc-drain-aborted*) '(:uncertain-reply))
      (equal (fn-lgk-pipe-acked (nth 0 *gc-drain-aborted*)) 0)))
(value-triple (list :drain-matrix-cases
                    (* (+ 1 (len *gc-drain-events*)) (len *gc-drain-probes*))))
