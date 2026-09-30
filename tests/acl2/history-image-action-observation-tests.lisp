(in-package "ACL2")
(include-book "../../books/history-image-action-observation")

(assert-event
 (equal (fn-hpi-effect-observation-disposition
         '(:written (11 (3 1) 0 0) 7 4 2 :ok)) :ready))
(assert-event
 (equal (fn-hpi-effect-observation-disposition
         '(:spool-written (11 (3 1) 0 0) 7 4 :data 0 2 :ok)) :ready))
(assert-event
 (equal (fn-hpi-effect-observation-disposition
         '(:image-read (11 (3 1) 0 0) 7 4 :data 0 2 :ok (1 2))) :ready))
(assert-event
 (equal (fn-hpi-effect-observation-disposition
         '(:spool-read (11 (3 1) 0 0) 7 4 :table 0 2 :ok (1 2))) :ready))
; Returned uncertainty and lost post-I/O authority must stop the writer.
(assert-event
 (equal (fn-hpi-effect-observation-disposition
         '(:written (11 (3 1) 0 0) 7 4 2 :uncertain)) :recovery-required))
(assert-event
 (equal (fn-hpi-effect-observation-disposition
         '(:image-read (11 (3 1) 0 0) 7 4 :data 0 2 :uncertain nil))
        :recovery-required))
(assert-event
 (equal (fn-hpi-effect-observation-disposition
         '(:retained :image-effect-observation)) :recovery-required))
(assert-event
 (equal (fn-hpi-effect-observation-disposition '(:refused :image-effect)) :refused))
; A truncated or fabricated envelope cannot become an executable continuation.
(assert-event
 (equal (fn-hpi-effect-observation-disposition
         '(:written (11 (3 1) 0 0) 7 4 2 :ok extra)) :recovery-required))
(assert-event
 (equal (fn-hpi-effect-observation-disposition
         '(:unknown (11 (3 1) 0 0) 7 4 :data 0 2 :ok nil)) :recovery-required))
(assert-event (equal (fn-hpi-effect-observation-disposition nil) :recovery-required))
