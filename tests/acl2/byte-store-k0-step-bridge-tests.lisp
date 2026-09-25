; Witnesses and teeth for lane k0-corollaries: the record program's two :ok
; observations (fn-sf-record-file-result-ok-preserves-store-relation,
; fn-sf-record-link-result-ok-preserves-store-relation, and their kind in
; fn-bs-k0-step-inputp) and the marker error arms
; (fn-bs-step-at-marker-pairs-preserves-k0-coverage).  Witnesses are
; reachable: the K5 fixture's second record run (its file-barrier pair 4
; and linked pair 8) and the committed-history marker run from its
; completing pair.
(in-package "ACL2")
(include-book "../../books/byte-store-k0-step-bridge")
(include-book "byte-store-k0-step-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bskb-rec (k) (nth k (bsk5-record-2-run)))
(defun bskb-file-ok (bs ks) (fn-bs-store-relation bs (fn-sf-record-file-result ks :ok)))
(defun bskb-link-ok (bs ks) (fn-bs-store-relation bs (fn-sf-record-link-result ks :ok)))

; The record-file observation at the file-barrier pair: related before, in
; :record-staged, related after, in :record-data-durable; and the general
; theorem's precondition and conclusion hold for the observe step there.
(assert-event (fn-bs-store-relation (car (bskb-rec 4)) (cdr (bskb-rec 4))))
(assert-event (equal (fn-sf-phase (cdr (bskb-rec 4))) :record-staged))
(assert-event (bskb-file-ok (car (bskb-rec 4)) (cdr (bskb-rec 4))))
(assert-event (equal (fn-sf-phase (fn-sf-record-file-result (cdr (bskb-rec 4)) :ok)) :record-data-durable))
(assert-event (bsks-ok (car (bskb-rec 4)) (cdr (bskb-rec 4)) '(:observe (:record-file :ok)) :ok))
; The record-link observation at the linked pair (a transaction link pending).
(assert-event (fn-bs-store-relation (car (bskb-rec 8)) (cdr (bskb-rec 8))))
(assert-event (equal (fn-sf-phase (cdr (bskb-rec 8))) :record-data-durable))
(assert-event (bskb-link-ok (car (bskb-rec 8)) (cdr (bskb-rec 8))))
(assert-event (equal (fn-sf-phase (fn-sf-record-link-result (cdr (bskb-rec 8)) :ok)) :record-attempted))
(assert-event (bsks-ok (car (bskb-rec 8)) (cdr (bskb-rec 8)) '(:observe (:record-link :ok)) :ok))
; Teeth: each lemma's one hypothesis is the relation.  Without it (the
; initial byte image under the same kernels) the conclusion fails.
(assert-event (not (fn-bs-store-relation (bsk5-initial) (cdr (bskb-rec 4)))))
(must-fail (assert-event (bskb-file-ok (bsk5-initial) (cdr (bskb-rec 4)))))
(assert-event (not (fn-bs-store-relation (bsk5-initial) (cdr (bskb-rec 8)))))
(must-fail (assert-event (bskb-link-ok (bsk5-initial) (cdr (bskb-rec 8)))))

; The marker error arms.
(defconst *bskb-stage* ".stage-marker-k0")
(defun bskb-octets () (fn-hm-after-commit 1))
(defun bskb-concl (bs ks stage octets outcome)
  (let ((run (bskm-run bs ks stage octets)) (prog (fn-bs-marker-program stage octets)))
    (and (fn-bs-k0b-marker-step-coveredp (cons bs ks) (nth 0 prog) outcome ks *bsk5-groups* *bsk5-capacity*)
         (fn-bs-k0b-marker-step-coveredp (nth 1 run) (nth 2 prog) outcome ks *bsk5-groups* *bsk5-capacity*)
         (fn-bs-k0b-marker-step-coveredp (nth 3 run) (nth 4 prog) outcome ks *bsk5-groups* *bsk5-capacity*)
         (fn-bs-k0b-marker-step-coveredp (nth 5 run) (nth 6 prog) outcome ks *bsk5-groups* *bsk5-capacity*)
         (fn-bs-k0b-marker-step-coveredp (nth 7 run) (nth 8 prog) outcome ks *bsk5-groups* *bsk5-capacity*))))
(defun bskb-hyps (bs ks stage octets outcome)
  (and (fn-bs-store-relation bs ks)
       (fn-bs-finish-inputp ks (car (fn-sf-completion ks)) (cdr (fn-sf-completion ks)))
       (stringp stage) (not (fn-bs-lookup bs :staging stage))
       (fn-cbor-octet-listp octets) (consp octets)
       (fn-bs-k0b-marker-fsync-outcomep bs stage octets outcome)))
(defun bskb-b () (car (bskm-pair)))
(defun bskb-k () (cdr (bskm-pair)))
; Witnesses: the completing pair, every step, an :ok outcome and the error
; outcomes the host sees (EIO from create, fsync and the root barrier; a
; short write; an issued and an unissued failed rename).
(assert-event (bskb-hyps (bskb-b) (bskb-k) *bskb-stage* (bskb-octets) :ok))
(assert-event (bskb-concl (bskb-b) (bskb-k) *bskb-stage* (bskb-octets) :ok))
(assert-event (bskb-hyps (bskb-b) (bskb-k) *bskb-stage* (bskb-octets) '(:eio . nil)))
(assert-event (bskb-concl (bskb-b) (bskb-k) *bskb-stage* (bskb-octets) '(:eio . nil)))
(assert-event (bskb-concl (bskb-b) (bskb-k) *bskb-stage* (bskb-octets) '(:eio . 3)))
(assert-event (bskb-concl (bskb-b) (bskb-k) *bskb-stage* (bskb-octets) '(:eio . :issued)))
(assert-event (bskb-concl (bskb-b) (bskb-k) *bskb-stage* (bskb-octets) '(:eio . :lost)))
; Teeth, one per hypothesis that has one.
; The relation: the initial byte image under the completing kernel.
(must-fail (assert-event (bskb-concl (bsk5-initial) (bskb-k) *bskb-stage* (bskb-octets) :ok)))
; The completion window: the related record-attempted pair of the record run.
(assert-event (fn-bs-store-relation (car (bskb-rec 10)) (cdr (bskb-rec 10))))
(assert-event (not (fn-bs-finish-inputp (cdr (bskb-rec 10)) (car (fn-sf-completion (cdr (bskb-rec 10))))
                                        (cdr (fn-sf-completion (cdr (bskb-rec 10)))))))
(must-fail (assert-event (bskb-concl (car (bskb-rec 10)) (cdr (bskb-rec 10)) *bskb-stage* (bskb-octets) :ok)))
; A string stage name.
(must-fail (assert-event (bskb-concl (bskb-b) (bskb-k) 7 (bskb-octets) :ok)))
; An absent stage: the stage the marker run itself created.
(assert-event (fn-bs-lookup (car (nth 1 (bskm-good))) :staging *bskb-stage*))
(must-fail (assert-event (bskb-concl (car (nth 1 (bskm-good))) (bskb-k) *bskb-stage* (bskb-octets) :ok)))
; Typed octets.
(must-fail (assert-event (bskb-concl (bskb-b) (bskb-k) *bskb-stage* '(300) :ok)))
