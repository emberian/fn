; Ground physical cuts: two writes, only the captured prefix acknowledged.
(in-package "ACL2")
(include-book "../../books/store-log-pipeline-durable")
(include-book "must-fail-checked")
(defconst *gcp-genesis* (make-list 32 :initial-element 0))
(defconst *gcp-ks*
  (fn-lgk-make nil *gcp-genesis* 0 3 '((66)) '((65)) 0 :appended))
(defconst *gcp-p* (fn-lgk-pipe-make *gcp-ks* nil))
(defconst *gcp-base*
  (fn-bs-make 512 (list (cons 0 (make-list 2048 :initial-element 0))) nil
    (list (list :write 0 0 (fn-lg-log '((65)) *gcp-genesis* 512))) 1))
(defconst *gcp-written*
  (mv-let (word after) (fn-lgk-pipe-physical-append *gcp-base* *gcp-p* 0 2048 :ok) (declare (ignore word)) after))
(defconst *gcp-tail* (nthcdr 1 (fn-bs-pending *gcp-written*)))
(defconst *gcp-fenced*
  (mv-let (word after) (fn-bs-pipe-fsync-prefix *gcp-written* 0 1 :ok) (declare (ignore word)) after))
(defconst *gcp-kf* (fn-lgk-fence *gcp-ks* 512))
(defconst *gcp-acked* (fn-lgk-pipe-ack (fn-lgk-pipe-make *gcp-kf* t) 1))
(assert-event
 (and (fn-bs-shapep *gcp-base*) (true-listp (fn-bs-pending *gcp-base*))
      (fn-lgk-pipe-okp *gcp-p* '((65) (66)))
      (fn-lgk-relp *gcp-base* *gcp-ks* 0 *gcp-genesis* 100)
      (equal (fn-lgk-phase *gcp-ks*) :appended)
      (fn-lgk-behind-admitsp *gcp-p* 512 2048)
      (equal (mv-let (word after) (fn-lgk-pipe-physical-append *gcp-base* *gcp-p* 0 2048 :ok) (declare (ignore after)) word) :ok)
      (equal (len (fn-bs-pending *gcp-written*)) 2)
      (fn-lgk-pipe-store-linkp *gcp-written* *gcp-base* *gcp-ks* *gcp-tail* 0 *gcp-genesis* 100)
      (equal (fn-lgk-acked *gcp-ks*) 0)))
(assert-event
 (and (fn-lgk-pipe-store-linkp *gcp-written* *gcp-base* *gcp-ks* *gcp-tail* 0 *gcp-genesis* 100)
      (equal (fn-bs-pending *gcp-fenced*) *gcp-tail*)
      (fn-lgu-safep *gcp-fenced* *gcp-kf* 0 *gcp-genesis* 100)
      (equal (fn-lgk-committed *gcp-kf*) '((65)))
      (equal (fn-lgk-batch *gcp-kf*) '((66)))
      (fn-lgk-pipe-okp (fn-lgk-pipe-make *gcp-kf* t) '((65) (66)))
      (fn-lgu-safep *gcp-fenced* (fn-lgk-pipe-ks *gcp-acked*) 0 *gcp-genesis* 100)
      (equal (fn-lgk-pipe-acked *gcp-acked*) 1)))
; Every listed failure outcome retains the old durable prefix, even though
; the interrupted barrier may have discarded its unlanded write.
(assert-event
 (and (fn-lgk-pipe-store-linkp *gcp-written* *gcp-base* *gcp-ks* *gcp-tail* 0 *gcp-genesis* 100)
      (fn-lgu-safep
       (mv-let (word after) (fn-bs-pipe-fsync-prefix *gcp-written* 0 1 '(:eio)) (declare (ignore word)) after)
       *gcp-ks* 0 *gcp-genesis* 100)
      (fn-lgu-safep
       (mv-let (word after) (fn-bs-pipe-fsync-prefix *gcp-written* 0 1 '(:enospc :all)) (declare (ignore word)) after)
       *gcp-ks* 0 *gcp-genesis* 100)))
; Removing the completed barrier premise: treating append as a fence is unsafe.
(must-fail-checked
 (assert-event (fn-lgu-safep *gcp-written* (fn-lgk-pipe-ks *gcp-acked*) 0 *gcp-genesis* 100)))
; Removing the prefix cut: A's barrier did not make B recoverably committed.
(must-fail-checked
 (assert-event
  (equal (car (fn-lg-scan (fn-bs-durable-content *gcp-fenced* 0) *gcp-genesis* 512 100))
         '((65) (66)))))
(value-triple :physical-prefix-positives-and-removals-passed)

(assert-event
 (and (fn-bs-shapep *gcp-base*) (true-listp (fn-bs-pending *gcp-base*))
      (fn-lgk-pipe-okp *gcp-p* '((65) (66)))
      (fn-lgk-relp *gcp-base* *gcp-ks* 0 *gcp-genesis* 100)
      (equal (fn-lgk-phase *gcp-ks*) :appended)
      (fn-lgk-behind-admitsp *gcp-p* 512 2048)
      (fn-lgk-fitsp *gcp-kf* 512 2048)
      (fn-lgk-relp *gcp-fenced* (fn-lgk-append *gcp-kf* 512 2048)
                   0 *gcp-genesis* 100)))
