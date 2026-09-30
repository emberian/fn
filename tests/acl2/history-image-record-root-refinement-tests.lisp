(in-package "ACL2")
(include-book "../../books/history-image-record-root-refinement")

; Execute the actual reference with its actual scratch stobjs and legal bounds.
(defun hpir-test-reference (txid address count digest)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (root pgs-mem)
      (with-local-stobj fn-octets-pg
        (mv-let (root pgs-mem fn-octets-pg)
          (let ((pgs-mem (resize-pgs-m 20 pgs-mem)))
            (pgs-x-write-rec 0 txid address count digest pgs-mem fn-octets-pg))
          (mv root pgs-mem)))
      root)))

; Reachable literal positives for the complete unconditional equality.
(assert-event
 (and (equal (fn-hpir-root 1 1 6 0) (hpir-test-reference 1 1 6 0))
      (equal (fn-hpir-root 9 37 1025 12345678901234567890)
             (hpir-test-reference 9 37 1025 12345678901234567890))
      (equal (fn-hpir-root 17 8192 342
               115792089237316195423570985008687907853269984665640564039457584007913129639935)
             (hpir-test-reference 17 8192 342
               115792089237316195423570985008687907853269984665640564039457584007913129639935))))

; Corrupted-record witnesses, not hypothesis-removal or collision assertions.
(assert-event
 (let ((root (hpir-test-reference 9 37 1025 12345678901234567890)))
   (and (equal (fn-hpir-root 9 37 1025 12345678901234567890) root)
        (equal (len root) 6)
        (not (equal root (update-nth 3 1024 root)))
        (not (equal root (update-nth 5 (+ 1 (nth 5 root)) root))))))
