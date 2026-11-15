; Pending source-byte loop induction; no admission claim.
(in-package "ACL2")
(include-book "envelope-output-segment")
(defthm fn2-eo-phase7-completes-segment
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 7)
       (fn2-eo-octets-p (fn2-eo-bytes fn2-envelope-output-state))
       (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state))
       (fn2-eo-octets-p rest) (fn2-eo-segments-p following)
       (equal (fn2-eo-suffix fn2-envelope-output-state)
              (fn2-eo-language-row following (fn2-eo-peer fn2-envelope-output-state)))
       (equal (fn2-eo-row fn2-envelope-output-state)
        (fn2-eo-language-row
         (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact) rest) following)
         (fn2-eo-peer fn2-envelope-output-state))))
  (let ((finished (fn2-envelope-output-run
                   (+ 1 (* (len (fn2-eo-bytes fn2-envelope-output-state))
                           (+ 4 (len (fn2-eo-peer fn2-envelope-output-state))
                                (len (fn2-eo-peer fn2-envelope-output-state)))))
                   fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 5)
        (equal (fn2-eo-bytes finished) nil)
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state))
        (equal (fn2-eo-row finished)
         (fn2-eo-language-row
          (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact)
                      (revappend (fn2-eo-bytes fn2-envelope-output-state) rest)) following)
          (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil)
