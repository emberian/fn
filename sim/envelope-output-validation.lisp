; Actual bounded validation, separately from language semantics.
(in-package "ACL2")
(include-book "envelope-output-language")

(defthm fn2-eo-terminal-run-identity
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 10)
          (equal (fn2-envelope-output-run fuel fn2-envelope-output-state)
                 fn2-envelope-output-state))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-run))))

(defthm fn2-eo-phase11-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 11)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (cond ((consp (fn2-eo-bytes fn2-envelope-output-state))
          (if (unsigned-byte-p 8 (car (fn2-eo-bytes fn2-envelope-output-state)))
              (update-fn2-eo-bytes (cdr (fn2-eo-bytes fn2-envelope-output-state)) fn2-envelope-output-state) (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))
         ((equal (fn2-eo-bytes fn2-envelope-output-state) nil) (update-fn2-eo-phase 0 fn2-envelope-output-state))
         (t (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase11-validates-octets
 (implies (and (natp fuel) (equal (fn2-eo-phase fn2-envelope-output-state) 11)
               (equal fuel (+ 1 (len (fn2-eo-bytes fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state))
        (equal (fn2-eo-ordered finished) (fn2-eo-ordered fn2-envelope-output-state))
        (if (fn2-eo-octets-p (fn2-eo-bytes fn2-envelope-output-state))
            (and (equal (fn2-eo-phase finished) 0)
                 (equal (fn2-eo-bytes finished) nil))
          (and (equal (fn2-eo-phase finished) 10)
               (equal (fn2-eo-result finished) nil))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run))
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step)))))

(defthm fn2-eo-phase12-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 12)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (cond ((consp (fn2-eo-scan fn2-envelope-output-state))
          (if (unsigned-byte-p 8 (car (fn2-eo-scan fn2-envelope-output-state)))
              (update-fn2-eo-scan (cdr (fn2-eo-scan fn2-envelope-output-state)) fn2-envelope-output-state) (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))
         ((equal (fn2-eo-scan fn2-envelope-output-state) nil) (update-fn2-eo-phase 1 fn2-envelope-output-state))
         (t (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase12-validates-octets
 (implies (and (natp fuel) (equal (fn2-eo-phase fn2-envelope-output-state) 12)
               (equal fuel (+ 1 (len (fn2-eo-scan fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state))
        (equal (fn2-eo-ordered finished) (fn2-eo-ordered fn2-envelope-output-state))
        (if (fn2-eo-octets-p (fn2-eo-scan fn2-envelope-output-state))
            (and (equal (fn2-eo-phase finished) 1)
                 (equal (fn2-eo-scan finished) nil))
          (and (equal (fn2-eo-phase finished) 10)
               (equal (fn2-eo-result finished) nil))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run))
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step)))))
