; Teeth for books/store-checkpoint-digest.lisp (PKT-854): the checkpoint's
; verifiable digest reads the tables and the arena's payloads, never the F
; row's REVISION or LOG.
(in-package "ACL2")
(include-book "../../books/store-checkpoint-digest")
(include-book "../../books/crypto-attach")
(include-book "must-fail-checked")

; The host's two calls are guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-sckd-tables-digest (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sckd-combine (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sckd-digest (w state)) :common-lisp-compliant)))

(defconst *sckdt-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "forward-sct" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "forward-sct" "subject" "evidence" 0)))
(defconst *sckdt-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(defconst *sckdt-capture* (fn-sco-capture *sckdt-configs* *sckdt-events*))
(defconst *sckdt-genesis* (make-list 32 :initial-element 7))
; An arena digest (fn-sdg-arena-pool's shape: 32 octets).
(defconst *sckdt-pool* (make-list 32 :initial-element 5))

; Two writers of one prefix: different images (REVISION) and rotation
; histories (LOG).  Their tables differ (the checkpoint files differ) ...
(defconst *sckdt-a* (fn-sct-tables-of-capture *sckdt-capture* 9 "rev-a" nil))
(defconst *sckdt-b* (fn-sct-tables-of-capture *sckdt-capture* 9 "rev-b"
                                              (list 3 *sckdt-genesis*)))
(assert-event (fn-sct-log-positionp (list 3 *sckdt-genesis*)))
(assert-event (not (equal *sckdt-a* *sckdt-b*)))
; ... and their checkpoint digests are equal
; (fn-sckd-digest-ignores-revision-and-log's positive witness).
(assert-event (equal (fn-sckd-digest *sckdt-a* *sckdt-pool*)
                     (fn-sckd-digest *sckdt-b* *sckdt-pool*)))
(assert-event (equal (len (fn-sckd-digest *sckdt-a* *sckdt-pool*)) 32))
; The host's two calls compose to the digest.
(assert-event (equal (fn-sckd-combine (fn-sckd-tables-digest *sckdt-b*) *sckdt-pool*)
                     (fn-sckd-digest *sckdt-a* *sckdt-pool*)))

; Not constant: a different frontier, a different prefix or a different
; arena digests differently.
(must-fail-checked
 (assert-event (equal (fn-sckd-digest *sckdt-a* *sckdt-pool*)
                      (fn-sckd-digest (fn-sct-tables-of-capture *sckdt-capture* 8 "rev-a" nil)
                                      *sckdt-pool*))))
(must-fail-checked
 (assert-event (equal (fn-sckd-digest *sckdt-a* *sckdt-pool*)
                      (fn-sckd-digest (fn-sct-tables-of-capture
                                       (fn-sco-capture *sckdt-configs*
                                                       (list (car *sckdt-events*)))
                                       9 "rev-a" nil)
                                      *sckdt-pool*))))
(must-fail-checked
 (assert-event (equal (fn-sckd-digest *sckdt-a* *sckdt-pool*)
                      (fn-sckd-digest *sckdt-a* (make-list 32 :initial-element 6)))))
; The file's own digest (the tables whole) does read REVISION: the reason a
; peer compares this digest, never the bytes.
(must-fail-checked
 (assert-event (equal (fn-sdg-digest *sckdt-a*) (fn-sdg-digest *sckdt-b*))))
