(in-package "ACL2")
(include-book "node-binding-fixture")
(include-book "../../books/retention-obligation-view-node")

(in-theory (disable (:executable-counterpart fn-rov-correspondp)
                    (:executable-counterpart fn-vdc-correspondp)))
(defconst *rovn-empty* (fn-node-initial-state '("fn.test") 100))
(defconst *rovn-prepared*
  (fn-node-prepare *rovn-empty* 9 "<a@example.invalid>" 0 '("fn.test")
                   "hold-a" "subject-a" "release-a" 7 841000000 *nbft-binding*))
(defconst *rovn-completed* (fn-node-complete *rovn-prepared* 0 9 :durable))
(defconst *rovn-v0* (fn-rov-build nil))
(defconst *rovn-v1*
  (fn-rov-update (fn-node-retention *rovn-prepared*)
                 (fn-node-retention *rovn-completed*) *rovn-v0*))

(defthm rovn-initial-relation
  (fn-rov-correspondp *rovn-v0* (fn-retain-pins (fn-node-retention *rovn-prepared*)))
  :hints (("Goal" :use ((:instance fn-rov-build-corresponds (pins nil))))))
(defthm rovn-durable-completion-complete-positive
  (and (fn-node-statep *rovn-prepared*)
       (fn-node-pending-matchesp *rovn-prepared* 0 9)
       (fn-rov-correspondp *rovn-v0* (fn-retain-pins (fn-node-retention *rovn-prepared*)))
       (fn-rov-correspondp *rovn-v1* (fn-retain-pins (fn-node-retention *rovn-completed*))))
  :hints (("Goal" :use (rovn-initial-relation
           (:instance fn-rov-node-complete-preserves-correspondence
            (node *rovn-prepared*) (view *rovn-v0*) (txid 0) (generation 9) (status :durable))))))
(assert-event
 (and (fn-node-statep *rovn-empty*) (fn-node-statep *rovn-prepared*)
      (fn-node-statep *rovn-completed*)
      (fn-node-pending-matchesp *rovn-prepared* 0 9)
      (equal (fn-rov-update-arm (fn-node-retention *rovn-prepared*)
                               (fn-node-retention *rovn-completed*)) :arrival)
      (equal (fn-rov-count *rovn-v0*) 0)
      (equal (fn-rov-count *rovn-v1*) 1)
      (equal (fn-rov-subject "subject-a" *rovn-v1*) '(1 . 7))
      (equal (fn-rov-subject "absent" *rovn-v1*) '(0 . 0))))

; Hypothesis removal: the node is valid and completion is reachable, but
; a corrupted carried total violates the only projection hypothesis and
; the resulting projection still violates the correspondence conclusion.
(defconst *rovn-bad0* (cons 100 nil))
(defconst *rovn-bad1*
  (fn-rov-update (fn-node-retention *rovn-prepared*)
                 (fn-node-retention *rovn-completed*) *rovn-bad0*))
(assert-event
 (and (fn-node-statep *rovn-prepared*)
      (fn-node-pending-matchesp *rovn-prepared* 0 9)
      (not (equal (fn-rov-count *rovn-bad0*)
                   (len (fn-retain-pins (fn-node-retention *rovn-prepared*)))))
      (not (equal (fn-rov-count *rovn-bad1*)
                   (len (fn-retain-pins (fn-node-retention *rovn-completed*)))))))
(defthm rovn-hypothesis-removal-correspondence-fails
  (and (not (fn-rov-correspondp *rovn-bad0*
              (fn-retain-pins (fn-node-retention *rovn-prepared*))))
       (not (fn-rov-correspondp *rovn-bad1*
              (fn-retain-pins (fn-node-retention *rovn-completed*)))))
  :hints (("Goal" :use ((:instance fn-rov-count-is-pin-count
                        (view *rovn-bad0*)
                        (pins (fn-retain-pins (fn-node-retention *rovn-prepared*))))
                       (:instance fn-rov-count-is-pin-count
                        (view *rovn-bad1*)
                        (pins (fn-retain-pins (fn-node-retention *rovn-completed*))))))))
