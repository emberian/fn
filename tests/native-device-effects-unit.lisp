(in-package "ACL2")
(include-book "../sim/native-device-effects")
(defconst *fn2-nde-test-write* '(:submit 1 (17 4 7 :write 1 3 (8 9 10))))
(assert-event
 (mv-let (code effects)
  (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1) '(:return 1 2 0)) 17)
  (and (eq code :ok) (equal effects '((:write 1 2 (8 9 10))))
       (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(0 8 9 0 0))
       (not (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(0 8 9 10 0)))
       (not (fn2-native-device-image-slice-p nil 0 '(0 0 0 0 0) '(0 8 9 0 0))))))
; A missing return is potentially effectful. It neither means zero bytes nor
; licenses arbitrary changes elsewhere in the image.
(assert-event
 (mv-let (code effects) (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1)) 17)
  (and (eq code :ok) (equal effects '((:uncertain 1 3)))
       (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(0 4 5 6 0))
       (not (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(1 4 5 6 0))))))
(assert-event
 (mv-let (code effects) (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1) '(:return 1 -1 5)) 17)
  (and (eq code :ok) (equal effects '((:uncertain 1 3))))))
; No interpretation of malformed/missing identities or impossible counts.
(assert-event
 (and (eq (mv-nth 0 (fn2-native-device-effects (list *fn2-nde-test-write* '(:return 1 2 0)) 17)) :malformed)
      (eq (mv-nth 0 (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1) '(:return 1 4 0)) 17)) :malformed)
      (eq (mv-nth 0 (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1) '(:return 2 2 0)) 17)) :malformed)
      (eq (mv-nth 0 (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1) '(:begin 1)) 17)) :malformed)))
; A Fence record is not itself a byte change or proof of power-loss truth.
(assert-event
 (mv-let (code effects)
  (fn2-native-device-effects
   (list *fn2-nde-test-write* '(:begin 1) '(:return 1 2 0)
         '(:submit 2 (17 5 7 :fence 0 0 nil)) '(:begin 2) '(:return 2 0 0)) 17)
  (and (eq code :ok) (equal effects '((:write 1 2 (8 9 10)) (:fence 0 0)))
       (fn2-native-device-image-slice-p effects 0 '(0 0 0 0) '(0 8 9 0))
       (not (fn2-native-device-image-slice-p effects 0 '(0 0 0 0) '(0 0 0 0))))))
; Requested bytes/offset matter, and physical order matters for overlaps.
(assert-event
 (and (not (fn2-native-device-image-slice-p '((:write 2 2 (8 9))) 0 '(0 0 0 0) '(0 8 9 0)))
      (not (fn2-native-device-image-slice-p '((:write 1 2 (9 8))) 0 '(0 0 0 0) '(0 8 9 0)))
      (fn2-native-device-image-slice-p '((:write 1 2 (8 9)) (:write 2 1 (7))) 0 '(0 0 0 0) '(0 8 7 0))
      (not (fn2-native-device-image-slice-p '((:write 2 1 (7)) (:write 1 2 (8 9))) 0 '(0 0 0 0) '(0 8 7 0)))))
