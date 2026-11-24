; The served POSTED matcher uses one checked pool read per Path octet.
; The disabled naive spec records the original per-start behavior.
; Original books/upload-scan.lisp at 522e12181: SHA-256
; 9ba10aa98a0aba7e970aae698efd21fd96d397547152c4531223c2227c195c1d.
(in-package "ACL2")
(include-book "upload-scan-unit")

(defun fn2-upl-run (text stale)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-pool
  (mv-let (result fn2-pool)
   (b* ((fn2-pool (fn2-pool-init '((1 . 65536)) 1 1000 fn2-pool))
        ((mv reserve slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool))
        (octets (fn2-usu-octets (coerce text 'list)))
        (fn2-pool (fn2-usu-feed octets slot gen fn2-pool))
        (read-gen (if stale (+ 1 gen) gen))
        (new (fn2-upload-posted (len octets) 0 slot read-gen 1 1 1 fn2-pool))
        (old (fn2-upload-posted-naive-spec (len octets) 0 slot read-gen 1 1 1 fn2-pool))
        (path (fn2-upload-path-ok 0 (len octets) slot read-gen 1 1 1 fn2-pool)))
    (mv (list reserve new old path) fn2-pool))
   result)))

(assert-event
 (and (equal (fn2-upl-run "posted" nil) '(:ok t t nil))
      (equal (fn2-upl-run "pPoStEd" nil) '(:ok t t nil))
      (equal (fn2-upl-run "posXposted" nil) '(:ok t t nil))
      (equal (fn2-upl-run "poPOSTED" nil) '(:ok t t nil))
      (equal (fn2-upl-run "postex" nil) '(:ok nil nil t))
      (equal (fn2-upl-run "POSXED" nil) '(:ok nil nil t))
      (equal (fn2-upl-run "xposted" t) '(:ok nil nil nil))
      (equal (fn2-upl-run (concatenate 'string (fn2-usu-long-line 992) "POSTED") nil)
             '(:ok t t nil))))
