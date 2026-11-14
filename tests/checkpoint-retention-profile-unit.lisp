; Source fixtures for exact dedicated checker/hash stripe selection.
(in-package "ACL2")
(include-book "../books/machines-b")
(defconst *fn2-retention-profile-control*
 '((:large-upload-windows . 2) (:control-connections . 1)))
(assert-event (equal (fn2-b-format-floor *fn2-retention-profile-control*) 12))
(assert-event
 (let* ((n (fn2-b-format-slots *fn2-retention-profile-control*))
        (semantic (fn2-b-semantic-retention-row n)) (payload (fn2-b-payload-retention-row n))
        (control (fn2-b-ctl-runtime-row 0 1 n)))
  (and (equal control (fn2-b-ctl-slot 0 *fn2-retention-profile-control*))
       (no-duplicatesp-equal (list 0 1 2 3 4 5 control semantic payload
                                 (fn2-b-event-row n) (fn2-b-block-read-row n) (fn2-b-checkpoint-row n)))
       (<= (+ (fn2-b-semantic-retention-field-base n) 128) (fn2-b-payload-retention-field-base n))
       (<= (+ (fn2-b-payload-retention-field-base n) 128) (* 128 (fn2-b-event-row n)))
       (<= (* 128 n) (fn2-b-field-rows *fn2-retention-profile-control*)))))
; Extra admitted format capacity must not move controls onto source stripes.
(assert-event
 (let ((n 20))
  (and (< (fn2-b-ctl-runtime-row 0 1 n) (fn2-b-semantic-retention-row n))
       (< (fn2-b-semantic-retention-row n) (fn2-b-payload-retention-row n))
       (< (fn2-b-payload-retention-row n) (fn2-b-event-row n))
       (< (fn2-b-event-row n) (fn2-b-block-read-row n))
       (< (fn2-b-block-read-row n) (fn2-b-checkpoint-row n)))))
