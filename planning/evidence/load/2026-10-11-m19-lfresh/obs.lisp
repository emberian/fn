(sb-int:encapsulate (quote acl2::fnn-heap-image-observation) (quote m19) (lambda (f) (let ((r (funcall f))) (format *error-output* "M19-CORE ~s~%" r) r)))
