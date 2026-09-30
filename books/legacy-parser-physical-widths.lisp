; Selected physical descriptor ABI binds actual parser source scalar widths.
; The descriptor-to-arena authorization provider remains a separate boundary.
(in-package "ACL2")
(include-book "legacy-parser-scalars")
(include-book "cold-read-window")

(local
 (defthm fn-lpw-descriptor-naturals
  (implies (fn-crw-naturals 7 descriptor)
           (and (natp (fn-crw-nth 0 descriptor)) (natp (fn-crw-nth 1 descriptor)) (natp (fn-crw-nth 2 descriptor)) (natp (fn-crw-nth 3 descriptor)) (natp (fn-crw-nth 4 descriptor)) (natp (fn-crw-nth 5 descriptor)) (natp (fn-crw-nth 6 descriptor))))
  :hints (("Goal" :in-theory (enable fn-crw-naturals fn-crw-nth)
           :expand ((fn-crw-naturals 7 descriptor)
                    (fn-crw-nth 0 descriptor)
                    (fn-crw-naturals 6 (cdr descriptor))
                    (fn-crw-nth 1 descriptor)
                    (fn-crw-nth 0 (cdr descriptor))
                    (fn-crw-naturals 5 (cdr (cdr descriptor)))
                    (fn-crw-nth 2 descriptor)
                    (fn-crw-nth 1 (cdr descriptor))
                    (fn-crw-nth 0 (cdr (cdr descriptor)))
                    (fn-crw-naturals 4 (cdr (cdr (cdr descriptor))))
                    (fn-crw-nth 3 descriptor)
                    (fn-crw-nth 2 (cdr descriptor))
                    (fn-crw-nth 1 (cdr (cdr descriptor)))
                    (fn-crw-nth 0 (cdr (cdr (cdr descriptor))))
                    (fn-crw-naturals 3 (cdr (cdr (cdr (cdr descriptor)))))
                    (fn-crw-nth 4 descriptor)
                    (fn-crw-nth 3 (cdr descriptor))
                    (fn-crw-nth 2 (cdr (cdr descriptor)))
                    (fn-crw-nth 1 (cdr (cdr (cdr descriptor))))
                    (fn-crw-nth 0 (cdr (cdr (cdr (cdr descriptor)))))
                    (fn-crw-naturals 2 (cdr (cdr (cdr (cdr (cdr descriptor))))))
                    (fn-crw-nth 5 descriptor)
                    (fn-crw-nth 4 (cdr descriptor))
                    (fn-crw-nth 3 (cdr (cdr descriptor)))
                    (fn-crw-nth 2 (cdr (cdr (cdr descriptor))))
                    (fn-crw-nth 1 (cdr (cdr (cdr (cdr descriptor)))))
                    (fn-crw-nth 0 (cdr (cdr (cdr (cdr (cdr descriptor))))))
                    (fn-crw-naturals 1 (cdr (cdr (cdr (cdr (cdr (cdr descriptor)))))))
                    (fn-crw-nth 6 descriptor)
                    (fn-crw-nth 5 (cdr descriptor))
                    (fn-crw-nth 4 (cdr (cdr descriptor)))
                    (fn-crw-nth 3 (cdr (cdr (cdr descriptor))))
                    (fn-crw-nth 2 (cdr (cdr (cdr (cdr descriptor)))))
                    (fn-crw-nth 1 (cdr (cdr (cdr (cdr (cdr descriptor))))))
                    (fn-crw-nth 0 (cdr (cdr (cdr (cdr (cdr (cdr descriptor))))))))))))

(defthm fn-lpw-supported-payload-length-within-off-t
 (implies (fn-crw-supportedp descriptor ticket)
          (and (natp (fn-crw-nth 4 descriptor))
               (<= (fn-crw-nth 4 descriptor) (- (expt 2 63) 33))))
 :rule-classes nil
 :hints (("Goal" :use fn-lpw-descriptor-naturals
          :in-theory (e/d (fn-crw-supportedp)
                          (fn-crw-naturals fn-crw-nth fn-lpw-descriptor-naturals)))))

; Carry the authorized source-length binding, not a fresh per-tick authorization scan.
(defun fn-lpw-descriptor-bound-p (s descriptor)
 (declare (xargs :guard t))
 (equal (fn-lpc-at 1 s) (fn-crw-nth 4 descriptor)))

(defthm fn-lpw-tick-preserves-descriptor-bound-by-definition
 (implies (fn-lpw-descriptor-bound-p s descriptor)
          (fn-lpw-descriptor-bound-p
           (mv-nth 0 (fn-lpc-tick s fuel fn-arena)) descriptor))
 :hints (("Goal" :in-theory (enable fn-lpw-descriptor-bound-p))))

(defthm fn-lpw-begin-binds-descriptor-length-by-definition
 (fn-lpw-descriptor-bound-p
  (fn-lpc-begin h (fn-crw-nth 4 descriptor) pin) descriptor)
 :hints (("Goal" :in-theory (enable fn-lpw-descriptor-bound-p fn-lpc-begin fn-lpc-at))))

(defthm fn-lpw-actual-tick-scalars-within-selected-abi
 (implies (and (fn-crw-supportedp descriptor ticket)
               (fn-lpw-descriptor-bound-p s descriptor)
               (fn-lps-scalars-p s) (fn-lpc-ready-p s fn-arena))
          (let* ((out (mv-nth 0 (fn-lpc-tick s fuel fn-arena)))
                 (header (fn-lpc-at 4 out)) (body (fn-lpc-at 6 out))
                 (limit (- (expt 2 63) 33)))
           (and (natp (fn-lpc-at 3 out)) (<= (fn-lpc-at 3 out) limit)
                (natp (fn-lpc-at 1 header)) (<= (fn-lpc-at 1 header) limit)
                (natp (fn-lpc-at 4 header)) (<= (fn-lpc-at 4 header) limit)
                (natp (fn-lpc-at 5 header)) (<= (fn-lpc-at 5 header) limit)
                (natp (fn-lpc-at 1 body)) (<= (fn-lpc-at 1 body) limit))))
 :hints (("Goal"
          :use (fn-lpw-supported-payload-length-within-off-t
                (:instance fn-lps-tick-scalars-fit-source-width
                           (limit (- (expt 2 63) 33))))
          :in-theory (e/d (fn-lpw-descriptor-bound-p)
                          (fn-crw-supportedp fn-lpc-tick fn-lpc-at
                           fn-lps-tick-scalars-fit-source-width
                           )))))
