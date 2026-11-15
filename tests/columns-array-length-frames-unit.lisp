; Actual ACL2 expansion controls for the selected extra-array observer API.
(in-package "ACL2")
(include-book "../books/columns-observation-frames")
(include-book "std/testing/must-fail" :dir :system)
(defcolumns fn2-length-frame-fixture ((value :u8) (phase :u8))
 :extra-fields ((fn2-length-frame-buffer :type (array (unsigned-byte 8) (0))
                :initially 0 :resizable t :why "Dimension interface fixture.")
                (fn2-length-frame-count :type (unsigned-byte 32) :initially 0
                 :why "Scalar observer refusal fixture.")))
(defcolumns-array-length-frames fn2-length-frame-fixture fn2-length-frame-buffer)
(assert-event
 (equal (getpropc 'fn2-length-frame-buffer-length-after-fn2-length-frame-fixture-set-value
                 'theorem nil (w state))
        '(equal (fn2-length-frame-buffer-length (fn2-length-frame-fixture-set-value i v fn2-length-frame-fixture))
                (fn2-length-frame-buffer-length fn2-length-frame-fixture))))
; An extra scalar, an ordinary column, and a missing field are not array
; observers. The actual world-backed producer must reject each request.
(must-fail (defcolumns-array-length-frames fn2-length-frame-fixture fn2-length-frame-count))
(must-fail (defcolumns-array-length-frames fn2-length-frame-fixture value))
(must-fail (defcolumns-array-length-frames fn2-length-frame-fixture missing))
