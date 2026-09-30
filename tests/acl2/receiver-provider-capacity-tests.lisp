(in-package "ACL2")
(include-book "../../books/receiver-provider-capacity")
(defun rxpc-observe-in (capacity bytes fn-octets$c)
 (declare (xargs :stobjs fn-octets$c :verify-guards nil))
 (let ((fn-octets$c (fn-octets$c-reserve capacity fn-octets$c)))
  (let ((before (fn-octets$c-buf-length fn-octets$c)))
   (let ((fn-octets$c (fn-octets$c-from-list bytes fn-octets$c)))
    (mv (list (<= 4096 before) (<= (len bytes) 4096)
              (and (equal (fn-octets$c-buf-length fn-octets$c) before)
                   (equal (fn-octets$c-fill fn-octets$c) (len bytes)))
              (equal (fn-octets$c-list fn-octets$c) bytes))
        fn-octets$c)))))
(defun rxpc-observe (capacity bytes)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-octets$c
  (mv-let (answer fn-octets$c) (rxpc-observe-in capacity bytes fn-octets$c)
   answer)))
; Positive witness: complete two premises and complete resource conclusion.
(assert-event (equal (rxpc-observe 4096 '(1 2 3 4)) '(t t t t)))
; Hypothesis removal: installed capacity, retained length premise affirmative.
(assert-event (equal (rxpc-observe 0 '(1 2 3 4)) '(nil t nil t)))
; Hypothesis removal: chunk length, retained installed capacity affirmative.
(assert-event (equal (rxpc-observe 4096 (make-list 4097 :initial-element 0))
                     '(t nil nil t)))
