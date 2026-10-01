; Shallow control/numeric invariant. It never rescans payload or accumulated data.
(in-package "ACL2")
(include-book "substrate-commit-profile-codec")
(defconst *fn-stcp-max-argument-refusal* (+ (* 256 *fn-cbor-max-uint64*) 255))
(defun fn-stcp-dec-boundedp (p c)
 (declare (xargs :guard t))
 (let ((phase (fn-stcp-at 0 c)) (index (fn-stcp-at 1 c))
       (offset (fn-stcp-at 3 c)) (ai (fn-stcp-at 4 c))
       (left (fn-stcp-at 5 c)) (arg (fn-stcp-at 6 c))
       (body (fn-stcp-at 7 c)) (wire (fn-stcp-at 12 c)))
  (and (fn-stcp-widthp c 14)
       (member-eq phase '(:head :argument :body :reverse :done :refused))
       (natp index) (<= index 5)
       (implies (member-eq phase '(:argument :body :reverse)) (< index 5))
       (natp offset) (natp wire) (equal offset wire)
       (<= wire *fn-cbor-max-uint64*) (<= wire (nfix (fn-stcp-at 1 p)))
       (natp ai) (<= ai (if (eq phase :refused) 31 27)) (natp left) (<= left 8)
       (natp arg) (<= arg (if (eq phase :refused) *fn-stcp-max-argument-refusal* *fn-cbor-max-uint64*))
       (natp body) (<= body *fn-cbor-max-uint*)
       (<= body (nfix (fn-stcp-at 2 p))))))
(defthm fn-stcp-decode-start-is-bounded
 (fn-stcp-dec-boundedp p (fn-stcp-decode-start p source))
 :hints (("Goal" :in-theory (e/d (fn-stcp-decode-start fn-stcp-dec-c
                                  fn-stcp-dec-boundedp fn-stcp-at fn-stcp-widthp)
                              (fn-stcp-profile-check)))))
(local (include-book "arithmetic/top" :dir :system))
(defthm fn-stcp-dec-tick-preserves-bounds
 (implies (fn-stcp-dec-boundedp p c)
  (fn-stcp-dec-boundedp p (fn-stcp-dec-tick p c)))
 :hints (("Goal" :in-theory (e/d (fn-stcp-dec-boundedp fn-stcp-dec-tick
                    fn-stcp-dec-c fn-stcp-dec-refuse fn-stcp-dec-value
                    fn-stcp-terminalp fn-stcp-profilep fn-stcp-profile-check)
                  (fn-stcp-source-byte fn-stcp-source-empty fn-stcp-source-next
                   floor mod fn-stcp-canonicalp fn-stx-op-of-code)))))
(defthm fn-stcp-dec-drive-preserves-bounds
 (implies (fn-stcp-dec-boundedp p c)
  (fn-stcp-dec-boundedp p (mv-nth 0 (fn-stcp-dec-drive p c fuel))))
 :hints (("Goal" :induct (fn-stcp-dec-drive p c fuel)
  :in-theory (e/d (fn-stcp-dec-drive)
                 (fn-stcp-dec-tick fn-stcp-dec-boundedp fn-stcp-terminalp)))))
(defthm fn-stcp-decode-resume-preserves-bounds
 (implies (fn-stcp-dec-boundedp p c)
  (fn-stcp-dec-boundedp p (mv-nth 0 (fn-stcp-decode-resume p c))))
 :hints (("Goal" :in-theory (e/d (fn-stcp-decode-resume)
             (fn-stcp-dec-drive fn-stcp-dec-boundedp fn-stcp-profilep mv-nth nfix)))))
(defun fn-stcp-enc-boundedp (p c)
 (declare (xargs :guard t))
 (let ((phase (fn-stcp-at 0 c)) (count (fn-stcp-at 3 c)) (wire (fn-stcp-at 9 c)))
  (and (fn-stcp-widthp c 11)
       (member-eq phase '(:choose :count :header :body :reverse :done :refused))
       (natp count) (<= count *fn-cbor-max-uint*)
       (<= count (nfix (fn-stcp-at 2 p)))
       (natp wire) (<= wire *fn-cbor-max-uint64*)
       (<= wire (nfix (fn-stcp-at 1 p))))))
(defthm fn-stcp-encode-start-is-bounded
 (fn-stcp-enc-boundedp p (fn-stcp-encode-start p commit))
 :hints (("Goal" :in-theory (e/d (fn-stcp-encode-start fn-stcp-enc-c
                                  fn-stcp-enc-boundedp fn-stcp-at fn-stcp-widthp)
                              (fn-stcp-profile-check fn-me-opp)))))
(defthm fn-stcp-enc-tick-preserves-bounds
 (implies (fn-stcp-enc-boundedp p c)
  (fn-stcp-enc-boundedp p (fn-stcp-enc-tick p c)))
 :hints (("Goal" :in-theory (e/d (fn-stcp-enc-boundedp fn-stcp-enc-tick
                    fn-stcp-enc-c fn-stcp-enc-refuse fn-stcp-terminalp
                    fn-stcp-profilep fn-stcp-profile-check)
                  (fn-cbor-encode-uint-wide fn-stcp-byte-head)))))
(defthm fn-stcp-enc-drive-preserves-bounds
 (implies (fn-stcp-enc-boundedp p c)
  (fn-stcp-enc-boundedp p (mv-nth 0 (fn-stcp-enc-drive p c fuel))))
 :hints (("Goal" :induct (fn-stcp-enc-drive p c fuel)
  :in-theory (e/d (fn-stcp-enc-drive)
                 (fn-stcp-enc-tick fn-stcp-enc-boundedp fn-stcp-terminalp)))))
(defthm fn-stcp-encode-resume-preserves-bounds
 (implies (fn-stcp-enc-boundedp p c)
  (fn-stcp-enc-boundedp p (mv-nth 0 (fn-stcp-encode-resume p c))))
 :hints (("Goal" :in-theory (e/d (fn-stcp-encode-resume)
             (fn-stcp-enc-drive fn-stcp-enc-boundedp fn-stcp-profilep mv-nth nfix)))))
