(in-package "ACL2")
(include-book "../../books/served-plan-byte-cursor")

(defun sppbt-token ()
  (mv-let (owners pins status) (fn-rpin-step nil '(31 nil nil) '(:acquire 7))
    (declare (ignore pins status)) (fn-rpin-token 7 owners)))

(defun sppbt-empty-returned-one (fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat))
         (pin (sppbt-token))
         (holder (fn-spp-make nil '((:audit retained))
                   (list (list :over-cursor (fn-ovw-cursor "fn.test" 1 0 0 nil t))
                         '(:close)) pin '(:captured-source 305))))
    (mv-let (status begun) (fn-spbc-begin holder pin 1)
      (let* ((ready (fn-spbc-ready-p begun fn-arena fn-cat))
             (one (fn-spbc-one begun fn-arena fn-cat))
             (finished (fn-spbc-finish one)))
        (mv (and (eq status :ok) ready
                 (eq (fn-spbc-status begun) :continue)
                 (fn-spp-holderp begun) (fn-spp-holderp one) (fn-spp-holderp finished)
                 (equal (fn-spbc-quantum one)
                        (fn-obc-quantum-one (fn-spbc-quantum begun) fn-arena fn-cat))
                 (equal (fn-spp-prefix begun) (fn-spp-prefix holder))
                 (equal (fn-spp-prefix one) (fn-spp-prefix holder))
                 (equal (fn-spp-prefix finished) (fn-spp-prefix holder))
                 (equal (fn-spp-origin begun) pin)
                 (equal (fn-spp-origin one) pin)
                 (equal (fn-spp-origin finished) pin)
                 (equal (fn-spp-resource begun) (fn-spp-resource holder))
                 (equal (fn-spp-resource one) (fn-spp-resource holder))
                 (equal (fn-spp-resource finished) (fn-spp-resource holder))
                 (equal (fn-spbc-tail one) '((:close)))
                 (equal (fn-spbc-cur finished) nil)) fn-arena fn-cat)))))

; Reachable actual ONE: the complete carried guard and each ownership
; conclusion are checked, with the response token obtained from ACQUIRE.
(assert-event
 (mv-let (good fn-arena fn-cat) (sppbt-empty-returned-one fn-arena fn-cat)
   (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))

; Origin mismatch rejects the unchanged complete holder before any ONE.
(assert-event
 (let* ((pin (sppbt-token))
        (p (fn-spp-make nil '((:audit retained))
             (list (list :over-cursor (fn-ovw-cursor "fn.test" 1 0 0 nil t)))
             pin '(:captured-source 305))))
   (mv-let (status next) (fn-spbc-begin p '(:response 7 32) 1)
     (and (fn-spp-holderp p)
          (not (equal (fn-spp-origin p) '(:response 7 32)))
          (equal status :stale-pin) (equal next p)))))
