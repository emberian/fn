(in-package "ACL2")
(include-book "../../books/consumer-account-metadata-domain")

; Reachable actual account adoption sequence. Logical transition evidence,
; not durable publication, account authority or native funding evidence.
(defconst *caamdt-bytes32* (make-list 32 :initial-element 9))
(defconst *caamdt-initial* (fn-cp-state *caamdt-bytes32* *caamdt-bytes32* 0 1 nil))
(defun fn-caamdt-event (s txid op)
  (declare (xargs :guard t))
  (list :consumer-authority (fn-cp-nth 3 s) txid 0 op))
(defun fn-caamdt-result-authority (one)
  (declare (xargs :guard t))
  (fn-cp-nth 6 (fn-cp-nth 1 one)))
(defun fn-caamdt-final-op (s kind)
  (declare (xargs :guard t))
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 s))))
    (list kind (fn-cp-nth 1 p) (fn-cp-nth 2 p)
          (fn-cp-nth 3 p) (fn-cp-nth 7 p))))
(defconst *caamdt-begin-op* '(:authority-begin (65) 0 1 7))
(defconst *caamdt-begin-event* (fn-caamdt-event *caamdt-initial* 1 *caamdt-begin-op*))
(defconst *caamdt-begin-result*
  (fn-caa-begin *caamdt-initial* (fn-cp-nth 6 *caamdt-initial*)
                *caamdt-begin-event* *caamdt-begin-op*))
(defconst *caamdt-begun* (fn-cp-nth 1 *caamdt-begin-result*))
(defconst *caamdt-row-op*
  (list :authority-row '(65) 0 '(97) 2 *caamdt-bytes32*
        (make-list 16 :initial-element 8) *caamdt-bytes32*
        *caamdt-bytes32* *caamdt-bytes32* 1))
(defconst *caamdt-row-event* (fn-caamdt-event *caamdt-begun* 2 *caamdt-row-op*))
(defconst *caamdt-row-result* (fn-caa-step *caamdt-begun* *caamdt-row-event*))
(defconst *caamdt-staged* (fn-cp-nth 1 *caamdt-row-result*))
(defconst *caamdt-row* (car (fn-cp-nth 3 (fn-cp-nth 5
                         (fn-cp-nth 5 (fn-cp-nth 6 *caamdt-staged*))))))
(defconst *caamdt-index* (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5
                         (fn-cp-nth 5 (fn-cp-nth 6 *caamdt-staged*))))))
(defconst *caamdt-seal-op* (fn-caamdt-final-op *caamdt-staged* :authority-seal))
(defconst *caamdt-seal-event* (fn-caamdt-event *caamdt-staged* 3 *caamdt-seal-op*))
(defconst *caamdt-seal-result*
  (fn-caa-seal *caamdt-staged* (fn-cp-nth 6 *caamdt-staged*)
               *caamdt-seal-event* *caamdt-seal-op*))
(defconst *caamdt-sealed* (fn-cp-nth 1 *caamdt-seal-result*))
(defconst *caamdt-prepare-event*
  (fn-caamdt-event *caamdt-sealed* 4 '(:authority-prepare (65) 0)))
(defconst *caamdt-prepare-result*
  (fn-caa-prepare *caamdt-sealed* (fn-cp-nth 6 *caamdt-sealed*) *caamdt-prepare-event*))
(defconst *caamdt-ready* (fn-cp-nth 1 *caamdt-prepare-result*))
(defconst *caamdt-fence-op* (fn-caamdt-final-op *caamdt-ready* :authority-fence))
(defconst *caamdt-fence-event* (fn-caamdt-event *caamdt-ready* 5 *caamdt-fence-op*))
(defconst *caamdt-fence-result*
  (fn-caa-fence *caamdt-ready* (fn-cp-nth 6 *caamdt-ready*)
                *caamdt-fence-event* *caamdt-fence-op*))

;@positive fn-caam-begin-establishes-size-domain
(assert-event
 (and (fn-caam-authority-sizep (fn-cp-nth 6 *caamdt-initial*))
      (fn-scc-octet-listp (fn-cp-nth 1 *caamdt-begin-op*))
      (integerp (fn-cp-nth 4 *caamdt-begin-op*))
      (equal (fn-cp-nth 0 *caamdt-begin-result*) :ok)
      (fn-caam-authority-sizep (fn-caamdt-result-authority *caamdt-begin-result*))))
;@positive fn-caam-stage-indexed-preserves-size-domain
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-begun*))
        (one (fn-caa-stage-indexed *caamdt-begun* a *caamdt-row-event*
                                   *caamdt-row* *caamdt-index* nil)))
   (and (fn-caam-authority-sizep a) (consp (fn-cp-nth 5 a))
        (fn-scc-octet-listp (fn-cp-nth 1 *caamdt-row*))
        (true-listp *caamdt-index*) (true-listp nil)
        (equal one *caamdt-row-result*)
        (fn-caam-authority-sizep (fn-caamdt-result-authority one)))))
;@positive fn-caam-seal-preserves-size-domain
(assert-event
 (and (fn-caam-authority-sizep (fn-cp-nth 6 *caamdt-staged*))
      (equal (fn-cp-nth 0 *caamdt-seal-result*) :ok)
      (fn-caam-authority-sizep (fn-caamdt-result-authority *caamdt-seal-result*))))
;@positive fn-caam-prepare-preserves-size-domain
(assert-event
 (and (fn-caam-authority-sizep (fn-cp-nth 6 *caamdt-sealed*))
      (equal (fn-cp-nth 0 *caamdt-prepare-result*) :ok)
      (fn-caam-authority-sizep (fn-caamdt-result-authority *caamdt-prepare-result*))))
;@positive fn-caam-fence-preserves-size-domain
(assert-event
 (and (fn-caam-authority-sizep (fn-cp-nth 6 *caamdt-ready*))
      (equal (fn-cp-nth 0 *caamdt-fence-result*) :ok)
      (fn-caam-authority-sizep (fn-caamdt-result-authority *caamdt-fence-result*))))
;@positive fn-caam-discard-preserves-size-domain
(assert-event
 (let ((a (fn-cp-nth 6 *caamdt-begun*)))
   (and (fn-caam-authority-sizep a)
        (fn-caam-authority-sizep (fn-caa-authority-pending a nil)))))

; Explicit corrupted-state witnesses preserve each other literal premise.
;@hypothesis-removal fn-caam-begin-establishes-size-domain candidate-octets
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-initial*)) (op '(:authority-begin (300) 0 1 7))
        (one (fn-caa-begin *caamdt-initial* a *caamdt-begin-event* op)))
   (and (fn-caam-authority-sizep a) (not (fn-scc-octet-listp (fn-cp-nth 1 op)))
        (integerp (fn-cp-nth 4 op)) (equal (fn-cp-nth 0 one) :ok)
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-begin-establishes-size-domain policy-integer
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-initial*)) (op '(:authority-begin (65) 0 1 bad))
        (one (fn-caa-begin *caamdt-initial* a *caamdt-begin-event* op)))
   (and (fn-caam-authority-sizep a) (fn-scc-octet-listp (fn-cp-nth 1 op))
        (not (integerp (fn-cp-nth 4 op))) (equal (fn-cp-nth 0 one) :ok)
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-begin-establishes-size-domain successful-result
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-begun*))
        (one (fn-caa-begin *caamdt-begun* a *caamdt-begin-event* *caamdt-begin-op*)))
   (and (fn-caam-authority-sizep a)
        (fn-scc-octet-listp (fn-cp-nth 1 *caamdt-begin-op*))
        (integerp (fn-cp-nth 4 *caamdt-begin-op*))
        (not (equal (fn-cp-nth 0 one) :ok))
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-begin-establishes-size-domain authority-domain
(assert-event
 (let* ((a '(:authority bad 1 nil nil nil))
        (op '(:authority-begin (65) bad 1 7))
        (one (fn-caa-begin *caamdt-initial* a *caamdt-begin-event* op)))
   (and (not (fn-caam-authority-sizep a)) (fn-scc-octet-listp (fn-cp-nth 1 op))
        (integerp (fn-cp-nth 4 op)) (equal (fn-cp-nth 0 one) :ok)
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-stage-indexed-preserves-size-domain authority-domain
(assert-event
 (let* ((a (update-nth 1 'bad (fn-cp-nth 6 *caamdt-begun*)))
        (one (fn-caa-stage-indexed *caamdt-begun* a *caamdt-row-event*
                                   *caamdt-row* *caamdt-index* nil)))
   (and (not (fn-caam-authority-sizep a)) (consp (fn-cp-nth 5 a))
        (fn-scc-octet-listp (fn-cp-nth 1 *caamdt-row*))
        (true-listp *caamdt-index*) (true-listp nil)
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-stage-indexed-preserves-size-domain pending-present
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-initial*))
        (one (fn-caa-stage-indexed *caamdt-initial* a *caamdt-row-event*
                                   *caamdt-row* *caamdt-index* nil)))
   (and (fn-caam-authority-sizep a) (not (consp (fn-cp-nth 5 a)))
        (fn-scc-octet-listp (fn-cp-nth 1 *caamdt-row*))
        (true-listp *caamdt-index*) (true-listp nil)
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-stage-indexed-preserves-size-domain row-name-octets
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-begun*)) (row (update-nth 1 '(300) *caamdt-row*))
        (one (fn-caa-stage-indexed *caamdt-begun* a *caamdt-row-event*
                                   row *caamdt-index* nil)))
   (and (fn-caam-authority-sizep a) (consp (fn-cp-nth 5 a))
        (not (fn-scc-octet-listp (fn-cp-nth 1 row)))
        (true-listp *caamdt-index*) (true-listp nil)
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-stage-indexed-preserves-size-domain index-proper
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-begun*)) (index 17)
        (one (fn-caa-stage-indexed *caamdt-begun* a *caamdt-row-event*
                                   *caamdt-row* index nil)))
   (and (fn-caam-authority-sizep a) (consp (fn-cp-nth 5 a))
        (fn-scc-octet-listp (fn-cp-nth 1 *caamdt-row*))
        (not (true-listp index)) (true-listp nil)
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-stage-indexed-preserves-size-domain old-rest-proper
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-begun*)) (old-rest 17)
        (one (fn-caa-stage-indexed *caamdt-begun* a *caamdt-row-event*
                                   *caamdt-row* *caamdt-index* old-rest)))
   (and (fn-caam-authority-sizep a) (consp (fn-cp-nth 5 a))
        (fn-scc-octet-listp (fn-cp-nth 1 *caamdt-row*))
        (true-listp *caamdt-index*) (not (true-listp old-rest))
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-seal-preserves-size-domain authority-domain
(assert-event
 (let* ((a (update-nth 1 'bad (fn-cp-nth 6 *caamdt-staged*)))
        (one (fn-caa-seal *caamdt-staged* a *caamdt-seal-event* *caamdt-seal-op*)))
   (and (not (fn-caam-authority-sizep a)) (equal (fn-cp-nth 0 one) :ok)
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-seal-preserves-size-domain successful-result
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-staged*)) (op (update-nth 3 99 *caamdt-seal-op*))
        (one (fn-caa-seal *caamdt-staged* a *caamdt-seal-event* op)))
   (and (fn-caam-authority-sizep a) (not (equal (fn-cp-nth 0 one) :ok))
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-prepare-preserves-size-domain authority-domain
(assert-event
 (let* ((a (update-nth 1 'bad (fn-cp-nth 6 *caamdt-sealed*)))
        (one (fn-caa-prepare *caamdt-sealed* a *caamdt-prepare-event*)))
   (and (not (fn-caam-authority-sizep a)) (equal (fn-cp-nth 0 one) :ok)
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-prepare-preserves-size-domain successful-result
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-begun*))
        (one (fn-caa-prepare *caamdt-begun* a *caamdt-prepare-event*)))
   (and (fn-caam-authority-sizep a) (not (equal (fn-cp-nth 0 one) :ok))
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-fence-preserves-size-domain authority-domain
(assert-event
 (let* ((old-a (fn-cp-nth 6 *caamdt-ready*))
        (a (update-nth 5 (update-nth 4 'bad (fn-cp-nth 5 old-a)) old-a))
        (one (fn-caa-fence *caamdt-ready* a *caamdt-fence-event* *caamdt-fence-op*)))
   (and (not (fn-caam-authority-sizep a)) (equal (fn-cp-nth 0 one) :ok)
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-fence-preserves-size-domain successful-result
(assert-event
 (let* ((a (fn-cp-nth 6 *caamdt-staged*))
        (one (fn-caa-fence *caamdt-staged* a *caamdt-fence-event* *caamdt-fence-op*)))
   (and (fn-caam-authority-sizep a) (not (equal (fn-cp-nth 0 one) :ok))
        (not (fn-caam-authority-sizep (fn-caamdt-result-authority one))))))
;@hypothesis-removal fn-caam-discard-preserves-size-domain authority-domain
(assert-event
 (let ((a (update-nth 1 'bad (fn-cp-nth 6 *caamdt-begun*))))
   (and (not (fn-caam-authority-sizep a))
        (not (fn-caam-authority-sizep (fn-caa-authority-pending a nil))))))
