; Explicitly unfunded local storage fixture, not a received-source issuer.
(in-package "ACL2")
(include-book "../../books/bp-received-byte-storage")
(defun fn-bprx-storage-test ()
 (with-local-stobj fn-bprx-segment
  (mv-let (result fn-bprx-segment)
   (mv-let (unpublished empty) (fn-bprx-segment-window 0 0 0 0 fn-bprx-segment)
    (mv-let (begin fn-bprx-segment) (fn-bprx-segment-begin 7 2 fn-bprx-segment)
     (mv-let (p0 fn-bprx-segment) (fn-bprx-segment-put 7 2 0 65 fn-bprx-segment)
      (mv-let (stale fn-bprx-segment) (fn-bprx-segment-put 7 2 0 90 fn-bprx-segment)
       (mv-let (p1 fn-bprx-segment) (fn-bprx-segment-put 7 2 1 66 fn-bprx-segment)
        (mv-let (freeze fn-bprx-segment) (fn-bprx-segment-freeze 7 2 2 fn-bprx-segment)
         (mv-let (mutation fn-bprx-segment) (fn-bprx-segment-put 7 2 2 67 fn-bprx-segment)
          (mv-let (word bytes) (fn-bprx-segment-window 7 2 0 2 fn-bprx-segment)
           (mv-let (foreign wrong) (fn-bprx-segment-window 8 2 0 2 fn-bprx-segment)
            (mv-let (range beyond) (fn-bprx-segment-window 7 2 1 2 fn-bprx-segment)
             (mv (list unpublished empty begin p0 stale p1 freeze mutation
                       word bytes foreign wrong range beyond
                       (fn-bprx-used fn-bprx-segment)
                       (fn-bprx-phase fn-bprx-segment)) fn-bprx-segment)))))))))))
   result)))
(assert-event
 (equal (fn-bprx-storage-test)
  '(:source-unpublished nil :source-filling :source-byte :stale-source-offset
    :source-byte :source-frozen :source-immutable :source-window (65 66)
    :stale-source nil :source-range nil 2 :frozen)))
