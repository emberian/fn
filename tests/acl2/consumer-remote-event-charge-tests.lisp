(in-package "ACL2")
(include-book "../../books/consumer-remote-event-charge")
(defconst *crct-event*
 '(:consumer 1 2 3 (:remote-register (99) (112) (99) 1 2 1 ((97) (98)) (65))))
; Both helper and whole actual scalar-charge theorem complete positives.
(assert-event
 (let* ((event *crct-event*) (groups (fn-cp-nth 7 (fn-cp-nth 4 event)))
        (count 2) (wire 6))
  (and (fn-crev-groupsp groups nil)
       (equal (fn-crw-groups-charge groups) (len (fn-crev-groups-encode groups)))
       (fn-crev-eventp event) (posp count) (fn-cp-uintp count)
       (equal wire (fn-crw-groups-charge groups))
       (equal (fn-crc-event-charge event count wire)
              (len (fn-crev-encode-reference event))))))
; Helper sole hypothesis removal: improper name is not an accepted name.
(assert-event
 (let ((groups '((97 . 98))))
  (and (not (fn-crev-groupsp groups nil))
       (not (equal (fn-crw-groups-charge groups) (len (fn-crev-groups-encode groups)))))))
; Whole theorem every retained hypothesis removal, all other premises true.
(assert-event
 (let* ((event '(:consumer 1 2 3 (:remote-register (99) (112) (99) 1 2 1 ((97) (97)) (65))))
        (count 2) (groups (fn-cp-nth 7 (fn-cp-nth 4 event))) (wire 6))
  (and (not (fn-crev-eventp event)) (posp count) (fn-cp-uintp count)
       (equal wire (fn-crw-groups-charge groups))
       (not (equal (fn-crc-event-charge event count wire) (len (fn-crev-encode-reference event)))))))
(assert-event
 (let* ((event *crct-event*) (count 0) (wire 6))
  (and (fn-crev-eventp event) (not (posp count)) (fn-cp-uintp count)
       (equal wire (fn-crw-groups-charge (fn-cp-nth 7 (fn-cp-nth 4 event))))
       (not (equal (fn-crc-event-charge event count wire) (len (fn-crev-encode-reference event)))))))
(assert-event
 (let* ((event *crct-event*) (count 4294967296) (wire 6))
  (and (fn-crev-eventp event) (posp count) (not (fn-cp-uintp count))
       (equal wire (fn-crw-groups-charge (fn-cp-nth 7 (fn-cp-nth 4 event))))
       (not (equal (fn-crc-event-charge event count wire) (len (fn-crev-encode-reference event)))))))
(assert-event
 (let* ((event *crct-event*) (count 2) (wire 7))
  (and (fn-crev-eventp event) (posp count) (fn-cp-uintp count)
       (not (equal wire (fn-crw-groups-charge (fn-cp-nth 7 (fn-cp-nth 4 event)))))
       (not (equal (fn-crc-event-charge event count wire) (len (fn-crev-encode-reference event)))))))
; Count equality is unnecessary for byte sizing: uint32 width is fixed.
; Stream terminal count/name correspondence remains a distinct invariant.
(assert-event
 (and (fn-crev-eventp *crct-event*) (posp 3) (fn-cp-uintp 3)
      (not (equal 3 (len (fn-cp-nth 7 (fn-cp-nth 4 *crct-event*)))))
      (equal 6 (fn-crw-groups-charge (fn-cp-nth 7 (fn-cp-nth 4 *crct-event*))))
      (equal (fn-crc-event-charge *crct-event* 3 6)
             (len (fn-crev-encode-reference *crct-event*)))))
