(in-package "ACL2")
(include-book "query-payload-length-boundary")
; Actual readonly selected-byte wrapper boundary; no native installation claim.
(defthm fn-miq-ready-payload-byte-denotes-selected-arena
  (implies
   (equal (car (fn-miq-selected-payload-byte selected index fuel fn-mio$c fn-arena state)) :ready)
   (let ((held (mv-nth 1 (fn-miq-selected-read selected fuel fn-mio$c)))
         (grant (mv-nth 2 (fn-miq-selected-read selected fuel fn-mio$c)))
         (left (mv-nth 3 (fn-miq-selected-read selected fuel fn-mio$c))))
     (equal (mv-list 3 (fn-miq-selected-payload-byte selected index fuel fn-mio$c fn-arena state))
            (list :ready
                  (list :payload-byte selected grant (fn-held-payload held) index
                        (nth index (nth (fn-held-payload held) fn-arena)))
                  (- left 1)))))
  :hints (("Goal" :in-theory (e/d (fn-miq-selected-payload-byte fn-qps-selected-byte)
                                  (fn-miq-selected-read fn-qps-eligiblep
                                   fn-owner-query-payload-ledger))))
  :rule-classes nil)
