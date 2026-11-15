;;; Foreign raw-DEFLATE primitive only: no admission, framing or budget policy.
;;; Caller owns the handle and pinned input/output windows. The logical carrier
;;; must validate exact used/made observations before moving any cursor.
(in-package "ACL2")

(sb-alien:define-alien-routine ("fn2_deflate_new" fn2-deflate-%new)
 sb-sys:system-area-pointer)
(sb-alien:define-alien-routine ("fn2_deflate_free" fn2-deflate-%free) sb-alien:void
 (handle sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn2_deflate_step" fn2-deflate-%step) sb-alien:int
 (handle sb-sys:system-area-pointer) (encode sb-alien:int)
 (input sb-sys:system-area-pointer) (input-length sb-alien:unsigned-int)
 (output sb-sys:system-area-pointer) (output-length sb-alien:unsigned-int)
 (used (* sb-alien:unsigned-int)) (made (* sb-alien:unsigned-int)))

(defun fn2-native-deflate-step (handle encode input input-length output output-length)
 (sb-alien:with-alien ((used sb-alien:unsigned-int) (made sb-alien:unsigned-int))
  (let ((status (fn2-deflate-%step handle encode input input-length output output-length
                  (sb-alien:addr used) (sb-alien:addr made))))
   (values status used made))))
