; Refusal/abort gaps mixed with publication and actual crash replay.
(in-package "ACL2")
(include-book "../../books/store-node-resolution")

(defconst *snrt-groups* '("fn.test"))
(defconst *snrt-reserve*
  '((:io :start-frontier nil) (:io :frontier-file :ok)
    (:io :frontier-replace :ok) (:io :frontier-directory :ok)))
(defconst *snrt-staged*
  (fn-record-make 0 1 1 "<staged@example>" '(65) *snrt-groups*
                  "staged-pin" "staged-content" "staged-release" 1))
(defconst *snrt-written*
  (fn-record-make 0 2 2 "<written@example>" '(66) *snrt-groups*
                  "written-pin" "written-content" "written-release" 1))
(defconst *snrt-committed*
  (fn-record-make 0 3 3 "<committed@example>" '(67) *snrt-groups*
                  "committed-pin" "committed-content" "committed-release" 1))
(defconst *snrt-later-abort*
  (fn-record-make 1 5 5 "<later-abort@example>" '(68) *snrt-groups*
                  "later-pin" "later-content" "later-release" 1))

; Refuse txid 0, abort staged txid 1, abort written-but-unpublished txid 2.
; Every next operation uses the unchanged history sequence and advanced txid.
(defconst *snrt-before-publish*
  (fn-snrt-run
   (fn-sn-initial *snrt-groups* 10)
   (append *snrt-reserve* '((:refuse-reservation 99) (:refuse-reservation 0)
                          (:refuse-reservation 0))
           *snrt-reserve* (list (list :prepare *snrt-staged*))
           '((:known-abort) (:known-abort))
           *snrt-reserve* (list (list :prepare *snrt-written*))
           '((:io :record-file :ok) (:known-abort)))))
(assert-event (fn-snt-relation *snrt-before-publish*))
(assert-event (equal (fn-sf-phase (fn-sn-files *snrt-before-publish*)) :ready))
(assert-event (equal (fn-sn-node *snrt-before-publish*)
                     (fn-sf-replay-node *snrt-groups* 10 nil 3)))
(assert-event (not (fn-sf-successes (fn-sn-files *snrt-before-publish*))))

(defconst *snrt-linked*
  (fn-snrt-run *snrt-before-publish*
   (append *snrt-reserve* (list (list :prepare *snrt-committed*))
           '((:io :record-file :ok) (:io :record-link :ok)))))
; A post-publication abort request cannot resolve unknown durable presence.
(assert-event (equal (fn-snrt-step *snrt-linked* '(:known-abort)) *snrt-linked*))
(defconst *snrt-accepted*
  (fn-snrt-run *snrt-linked* '((:io :record-directory :ok) (:finish))))
(assert-event (equal (fn-sf-successes (fn-sn-files *snrt-accepted*)) '((0 . 3))))
(assert-event (fn-sn-committed-recordp (fn-sn-node *snrt-accepted*) *snrt-committed*))

(defconst *snrt-final*
  (fn-snrt-run *snrt-accepted*
   (append *snrt-reserve* '((:refuse-reservation 4))
           *snrt-reserve* (list (list :prepare *snrt-later-abort*))
           '((:known-abort) (:crash :old :absent) (:recover)
             (:io :recovery-barrier :ok) (:io :recovery-barrier :ok)
             (:io :recovery-barrier :ok) (:io :recovery-barrier :ok)
             (:io :recovery-barrier :ok)))))
(assert-event (fn-snt-relation *snrt-final*))
(assert-event (equal (fn-sf-phase (fn-sn-files *snrt-final*)) :ready))
(assert-event (equal (fn-sf-successes (fn-sn-files *snrt-final*)) '((0 . 3))))
(assert-event (equal (fn-sf-records (fn-sn-files *snrt-final*))
                     (list *snrt-committed*)))
(assert-event (equal (fn-sn-node *snrt-final*)
                     (fn-sf-replay-node *snrt-groups* 10 (list *snrt-committed*) 6)))
(assert-event (fn-sn-committed-recordp (fn-sn-node *snrt-final*) *snrt-committed*))
