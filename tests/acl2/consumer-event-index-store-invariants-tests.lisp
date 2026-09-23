; The index is derived from actual durable consumer publication, not an
; independent source of Store history.
(in-package "ACL2")
(include-book "../../books/consumer-event-index-store-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defun ceist-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun ceist-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))
(defun ceist-commit (s event)
  (fn-sn-finish (ceist-publish (fn-sn-prepare-consumer
                               (ceist-reserve s) event))))

(defconst *ceist-boot* (fn-cpe-make 0 0 0 '(:bootstrap (1) (2))))
(defconst *ceist-reg* (fn-cpe-make 1 1 1 '(:register (3) (4) (5) 1 1 1)))
(defconst *ceist-ack*
  (fn-cpe-make 2 2 2
               (list :ack (fn-cp-cursor '(1) '(2) '(3) '(4) '(5)
                                         1 1 1 2))))
(defconst *ceist-initial* (fn-sn-initial '("g") 32))
(defconst *ceist-after-boot* (ceist-commit *ceist-initial* *ceist-boot*))
(defconst *ceist-after-reg* (ceist-commit *ceist-after-boot* *ceist-reg*))
(defconst *ceist-after-ack* (ceist-commit *ceist-after-reg* *ceist-ack*))

(assert-event (fn-ceis-relatedp *ceist-initial*))
(assert-event (fn-ceis-relatedp *ceist-after-boot*))
(assert-event (fn-ceis-relatedp *ceist-after-reg*))
(assert-event (fn-ceis-relatedp *ceist-after-ack*))
(assert-event (equal (fn-cei-get 2 (fn-sn-event-index *ceist-after-ack*))
                     *ceist-ack*))
(assert-event
 (fn-ceis-relatedp
  (fn-sn-recover (fn-sn-crash *ceist-after-ack* :old :absent))))

; A well-shaped but stale derived index cannot justify selection.  The
; correspondence premise is substantive even when the Store projection is
; otherwise valid.
(must-fail
 (defthm fn-ceis-stale-index-does-not-satisfy-correspondence
   (implies (fn-sn-statep s)
            (fn-ceis-relatedp (fn-sn-with-event-index s nil)))))
