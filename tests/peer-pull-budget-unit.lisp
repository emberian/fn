; READ's octet credit counts items. Its envelope must still fit both limits.
(in-package "ACL2")
(include-book "../books/xfnc-batch-codec")

(defun fn2-pull-budget-frame (header n)
 (declare (xargs :verify-guards nil))
 (fn2-fnct-seal *fn2-fnct-port-reply-kind*
                (fn2-layout-octets *fn2-fnct-port-reply-layout*
                 (list 0 nil (append header (make-list (nfix n) :initial-element 0))))))

(assert-event
 (b* ((before '(:cursor 0 (1 2 3) (4 5 6) (7 8 9) (10 11) (12 13) 1 1 1 4294967295))
      (after (update-nth 10 4294967296 before))
      (request (fn2-fncu-encode before)) (reply (fn2-fncu-encode after))
      (old-version (nth 4 request)) (new-version (nth 4 reply))
      (chain (cons 1 (make-list 32 :initial-element 0)))
      (header (fn2-layout-octets *fn2-xfnc-batch-header*
               (list 1 1 1 1 chain 1 1 1 4294967296 4294967296 0 1 reply)))
      (credit (fn2-xfnc-batch-read-budget old-version (len request) 512))
      (large (fn2-xfnc-batch-read-budget old-version (len request) 65536)))
   (and (equal (fn2-fncu-decode request) (list :ok before))
        (equal (fn2-fncu-decode reply) (list :ok after))
        (equal old-version 1) (equal new-version 2)
        (equal (len request) 39) (equal (len reply) 59) (equal (len header) 158)
        (equal (fn2-xfnc-next-cursor-bound old-version (len request)) (len reply))
        (equal (fn2-xfnc-batch-read-budget new-version (len reply) 512) credit)
        (equal (len (fn2-pull-budget-frame header 325)) 532)
        (equal credit 305) (equal (len (fn2-pull-budget-frame header credit)) 512)
        (equal (len (fn2-pull-budget-frame header (+ 1 credit))) 513)
        (equal large 3921)
        (equal (- (len (fn2-pull-budget-frame header large)) *fn2-fnct-trailer-octets*)
               *fn2-pool-block-bytes*))))
