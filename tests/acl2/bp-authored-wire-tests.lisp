; Reachable operation and hypothesis teeth for authored-wire publication.
(in-package "ACL2")
(include-book "../../books/bp-authored-wire")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpaw-a* (cons :dtn '(47 47 102 110 45 97 47)))
(defconst *bpaw-b* (cons :dtn '(47 47 102 110 45 98 47)))
(defconst *bpaw-config* (fn-bpn-config *bpaw-a* 3600000 2 32 1048576))
(defconst *bpaw-adu* '(104 101 108 108 111))
(defconst *bpaw-obs* (fn-clock-observation 1000 100 0 t))
(defconst *bpaw-reservation* (fn-bpn-sequence-reserve 7))
(defconst *bpaw-operation*
  (fn-bpn-authored-wire-authorize
   *bpaw-config* *bpaw-b* *bpaw-adu* *bpaw-reservation* *bpaw-obs* t t))

(assert-event (fn-bpn-authored-wire-operationp *bpaw-operation*))
(assert-event
 (equal (fn-bpn-authored-wire-operation-name-chars *bpaw-operation*)
        '(#\a #\u #\t #\h #\o #\r #\e #\d #\- #\7
          #\. #\w #\i #\r #\e)))
(assert-event
 (equal (fn-bpn-authored-wire-operation-sequence *bpaw-operation*) 7))
(assert-event
 (equal (fn-bpn-authored-wire-operation-wire *bpaw-operation*)
        (fn-bpn-send *bpaw-config* *bpaw-b* *bpaw-adu* 7 *bpaw-obs*)))
(assert-event
 (equal (fn-bpp-sequence
          (fn-bpb-bundle-primary
          (fn-bpb-decode
           (fn-bpn-authored-wire-operation-wire *bpaw-operation*) 1048576)))
        7))

; The reservation determines a different durable name for the next sequence.
(assert-event
 (not (equal
       (fn-bpn-authored-wire-name-for-reservation
        (fn-bpn-sequence-reserve 7))
       (fn-bpn-authored-wire-name-for-reservation
        (fn-bpn-sequence-reserve 8)))))

; Both authority observations have teeth.  Dropping the held shared lock or
; observing the exact final name occupied cannot yield a publication operation.
(assert-event
 (not (fn-bpn-authored-wire-operationp
       (fn-bpn-authored-wire-authorize
        *bpaw-config* *bpaw-b* *bpaw-adu* *bpaw-reservation* *bpaw-obs* nil t))))
(must-fail
 (assert-event
  (fn-bpn-authored-wire-operationp
   (fn-bpn-authored-wire-authorize
    *bpaw-config* *bpaw-b* *bpaw-adu* *bpaw-reservation* *bpaw-obs* nil t))))

(assert-event
 (not (fn-bpn-authored-wire-operationp
       (fn-bpn-authored-wire-authorize
        *bpaw-config* *bpaw-b* *bpaw-adu* *bpaw-reservation* *bpaw-obs* t nil))))
(must-fail
 (assert-event
  (fn-bpn-authored-wire-operationp
   (fn-bpn-authored-wire-authorize
    *bpaw-config* *bpaw-b* *bpaw-adu* *bpaw-reservation* *bpaw-obs* t nil))))

; A value in the sequence domain is not enough: authorization consumes the
; actual reservation token that also carries the durable successor record.
(assert-event
 (not (fn-bpn-authored-wire-operationp
       (fn-bpn-authored-wire-authorize
        *bpaw-config* *bpaw-b* *bpaw-adu* 7 *bpaw-obs* t t))))
(must-fail
 (assert-event
  (fn-bpn-authored-wire-operationp
   (fn-bpn-authored-wire-authorize
    *bpaw-config* *bpaw-b* *bpaw-adu* 7 *bpaw-obs* t t))))
