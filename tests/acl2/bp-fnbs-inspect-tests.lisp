; Exact ADU projection and same-length damage rejection from a real kind-5 row.
(in-package "ACL2")
(include-book "../../books/bp-fnbs-inspect")
(include-book "bp-fnbs-codec-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-bpnfi-corrupt-last (frame)
  (declare (xargs :guard t :verify-guards nil))
  (update-nth (nfix (1- (len frame)))
              (mod (1+ (nfix (car (last frame)))) 256)
              frame))

(assert-event
 (equal (fn-bpnf-inspect-adu
         (fn-bpnf-stored-record-frame *bpnfc-record*))
        '(:ready (1 2 3 4))))
(assert-event
 (let* ((frame (fn-bpnf-stored-record-frame *bpnfc-record*))
        (bad (fn-bpnfi-corrupt-last frame)))
   (and (equal (len bad) (len frame))
        (not (equal bad frame)))))
(assert-event
 (equal (fn-bpnf-inspect-adu
         (fn-bpnfi-corrupt-last
          (fn-bpnf-stored-record-frame *bpnfc-record*)))
        '(:fault :invalid-fnbs)))
(must-fail
 (assert-event
  (equal (fn-bpnf-inspect-adu
          (fn-bpnfi-corrupt-last
           (fn-bpnf-stored-record-frame *bpnfc-record*)))
         '(:ready (1 2 3 4)))))
