; READ's octet credit counts items. Its envelope must still fit both limits.
(in-package "ACL2")
(include-book "../books/xfnc-batch-codec")

(defun fn2-pull-budget-frame (header n)
 (declare (xargs :verify-guards nil))
 (fn2-fnct-seal *fn2-fnct-port-reply-kind*
                (fn2-layout-octets *fn2-fnct-port-reply-layout*
                 (list 0 nil (append header (make-list (nfix n) :initial-element 0))))))

(assert-event
 (b* ((identity '(:cursor 0 (1 2 3) (4 5 6) (7 8 9) (10 11) (12 13) 1 1 1 0))
      (cursor (fn2-fncu-encode identity))
      (chain (cons 1 (make-list 32 :initial-element 0)))
      (header (fn2-layout-octets *fn2-xfnc-batch-header*
               (list 1 1 1 1 chain 1 1 1 0 1 1 1 cursor)))
      (small (fn2-xfnc-batch-read-budget (len cursor) 512))
      (large (fn2-xfnc-batch-read-budget (len cursor) 65536)))
   (and (equal (fn2-fncu-decode cursor) (list :ok identity))
        (equal (len cursor) 39) (equal (len header) 138)
        (equal small 325) (equal (len (fn2-pull-budget-frame header small)) 512)
        (equal (len (fn2-pull-budget-frame header (+ 1 small))) 513)
        (equal large 3941)
        (equal (- (len (fn2-pull-budget-frame header large)) *fn2-fnct-trailer-octets*)
               *fn2-pool-block-bytes*))))
