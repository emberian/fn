(in-package "ACL2")
(include-book "../sim/native-device-effects")
(defconst *fn2-nde-test-write* '(:submit 1 (17 4 7 :write 1 3 (8 9 10))))
(assert-event
 (mv-let (code effects)
  (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1) '(:return 1 2 0 nil)) 17)
  (and (eq code :ok) (equal effects '((:write 1 2 (8 9 10))))
       (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(0 8 9 0 0))
       (not (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(0 8 9 10 0)))
       (not (fn2-native-device-image-slice-p nil 0 '(0 0 0 0 0) '(0 8 9 0 0))))))
; A missing return is potentially effectful. It neither means zero bytes nor
; licenses arbitrary changes elsewhere in the image.
(assert-event
 (mv-let (code effects) (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1)) 17)
  (and (eq code :ok) (equal effects '((:uncertain 1 3 :pending (8 9 10))))
       (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(0 4 5 6 0))
       (not (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(1 4 5 6 0))))))
(assert-event
 (mv-let (code effects) (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1) '(:return 1 -1 5 nil)) 17)
  (and (eq code :ok) (equal effects '((:uncertain 1 3 (:error -1 5) (8 9 10)))))))
; No interpretation of malformed/missing identities or impossible counts.
(defun fn2-nde-test-verdict (records)
 (declare (xargs :verify-guards nil))
 (mv-let (code effects) (fn2-native-device-effects records 17)
  (declare (ignore effects)) code))
(assert-event
 (and (eq (fn2-nde-test-verdict (list *fn2-nde-test-write* '(:return 1 2 0 nil))) :malformed)
      (eq (fn2-nde-test-verdict (list *fn2-nde-test-write* '(:begin 1) '(:return 1 4 0 nil))) :malformed)
      (eq (fn2-nde-test-verdict (list *fn2-nde-test-write* '(:begin 1) '(:return 2 2 0 nil))) :malformed)
      (eq (fn2-nde-test-verdict (list *fn2-nde-test-write* '(:begin 1) '(:begin 1))) :malformed)))
; A Fence record is not itself a byte change or proof of power-loss truth.
(assert-event
 (mv-let (code effects)
  (fn2-native-device-effects
   (list *fn2-nde-test-write* '(:begin 1) '(:return 1 2 0 nil)
         '(:submit 2 (17 5 7 :fence 0 0 nil)) '(:begin 2) '(:return 2 0 0 nil)) 17)
  (and (eq code :ok) (equal effects '((:write 1 2 (8 9 10)) (:fence 0 0)))
       (fn2-native-device-image-slice-p effects 0 '(0 0 0 0) '(0 8 9 0))
       (not (fn2-native-device-image-slice-p effects 0 '(0 0 0 0) '(0 0 0 0))))))
; Requested bytes/offset matter, and physical order matters for overlaps.
(assert-event
 (and (not (fn2-native-device-image-slice-p '((:write 2 2 (8 9))) 0 '(0 0 0 0) '(0 8 9 0)))
      (not (fn2-native-device-image-slice-p '((:write 1 2 (9 8))) 0 '(0 0 0 0) '(0 8 9 0)))
      (fn2-native-device-image-slice-p '((:write 1 2 (8 9)) (:write 2 1 (7))) 0 '(0 0 0 0) '(0 8 7 0))
      (not (fn2-native-device-image-slice-p '((:write 2 1 (7)) (:write 1 2 (8 9))) 0 '(0 0 0 0) '(0 8 7 0)))))

; Read results are checked at their physical position, not against final image.
(assert-event
 (and (fn2-native-device-image-slice-p
        '((:write 1 2 (8 9)) (:read 1 2 (8 9)) (:write 1 1 (7)))
        0 '(0 0 0 0) '(0 7 9 0))
      (not (fn2-native-device-image-slice-p
        '((:write 1 2 (8 9)) (:read 1 2 (7 9)) (:write 1 1 (7)))
        0 '(0 0 0 0) '(0 7 9 0)))))
(assert-event
 (mv-let (code cursor)
  (fn2-native-device-image-chunk '((:write 1 2 (8 9))) 4 0 0 '(0 0) '(0 8))
  (and (eq code :ok) (equal cursor 2)
       (eq (fn2-native-device-image-finish nil 4 4 cursor) :incomplete-image)
       (mv-let (bad ignored) (fn2-native-device-image-chunk nil 4 cursor 3 '(0) '(0))
        (declare (ignore ignored)) (eq bad :mismatch))
       (mv-let (code cursor)
        (fn2-native-device-image-chunk '((:write 1 2 (8 9))) 4 cursor 2 '(0 0) '(9 0))
        (and (eq code :ok)
             (eq (fn2-native-device-image-finish nil 4 4 cursor) :exact-process-view)
             (eq (fn2-native-device-image-finish nil 4 5 cursor) :incomplete-image)
             (eq (fn2-native-device-image-finish '((:uncertain 1 1 :pending (8))) 4 4 cursor)
                 :uncertain-effect-bound))))))

; Submit order is FIFO, not merely a chosen serial physical order.
(assert-event
 (eq (fn2-nde-test-verdict
       (list *fn2-nde-test-write* '(:submit 2 (17 5 7 :read 1 1 nil)) '(:begin 2))) :malformed))
; A successful Read constrains an unknown byte until a later effect changes it.
(assert-event
 (and (fn2-native-device-image-slice-p
        '((:uncertain 0 1 (:error -1 5) (8)) (:read 0 1 (7)) (:read 0 1 (7)))
        0 '(0) '(7))
      (not (fn2-native-device-image-slice-p
        '((:uncertain 0 1 (:error -1 5) (8)) (:read 0 1 (7)) (:read 0 1 (8)))
        0 '(0) '(8)))
      (not (fn2-native-device-image-slice-p
        '((:uncertain 0 1 (:error -1 5) (8)) (:read 0 1 (7)))
        0 '(0) '(8)))))
