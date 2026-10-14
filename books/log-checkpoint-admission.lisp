; Independent scalar admission decisions and their complete teeth.
(in-package "ACL2")
(include-book "log-checkpoint-values")
(include-book "defkeystone")
(verify-guards fn-lc-record-admission)

; Standing rule: no input-domain hypothesis is needed for this total
; equivalence; the exact-boundary mutation still bites (DROPS.md).
(defthm fn-lc-record-too-large-is-refused-by-name
  (iff (equal (fn-lc-record-admission encoded-record segment-unit)
              '(:refused :record-exceeds-segment))
       (< segment-unit (len encoded-record)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-lc-record-admission))))

(defteeth fn-lc-record-too-large-is-refused-by-name
  :claim (() (iff (equal (fn-lc-record-admission encoded-record segment-unit)
                        '(:refused :record-exceeds-segment))
                  (< segment-unit (len encoded-record))))
  :subject fn-lc-record-admission
  :witness ((encoded-record '(0 1)) (segment-unit 1))
  :breaks nil
  :mutations ((boundary
               (:conclusion
                (iff (equal (fn-lc-record-admission encoded-record segment-unit)
                            '(:refused :record-exceeds-segment))
                     (<= segment-unit (len encoded-record))))
               ((encoded-record '(0)) (segment-unit 1))
               :fault "incorrect refusal at the exact segment boundary")))

(verify-guards fn-lc-allocate-segment)

; Standing rule: exhaustedp booleanity is unnecessary for the conclusion.
(defthm fn-lc-allocator-refuses-before-wraparound
  (implies (unsigned-byte-p 64 next-id)
           (let ((out (fn-lc-allocate-segment next-id exhaustedp)))
             (and (iff (equal (mv-nth 0 out) '(:refused :segment-id-exhausted))
                       exhaustedp)
                  (implies (not exhaustedp)
                           (and (equal (mv-nth 1 out) next-id)
                                (unsigned-byte-p 64 (mv-nth 2 out))
                                (if (equal next-id 18446744073709551615)
                                    (and (equal (mv-nth 2 out) next-id)
                                         (equal (mv-nth 3 out) t))
                                  (and (equal (mv-nth 2 out) (+ 1 next-id))
                                       (equal (mv-nth 3 out) nil))))))))
  :rule-classes nil)

(defteeth fn-lc-allocator-refuses-before-wraparound
  :claim (((id (unsigned-byte-p 64 next-id)))
    (let ((out (fn-lc-allocate-segment next-id exhaustedp)))
             (and (iff (equal (mv-nth 0 out) '(:refused :segment-id-exhausted))
                       exhaustedp)
                  (implies (not exhaustedp)
                           (and (equal (mv-nth 1 out) next-id)
                                (unsigned-byte-p 64 (mv-nth 2 out))
                                (if (equal next-id 18446744073709551615)
                                    (and (equal (mv-nth 2 out) next-id)
                                         (equal (mv-nth 3 out) t))
                                  (and (equal (mv-nth 2 out) (+ 1 next-id))
                                       (equal (mv-nth 3 out) nil))))))))
  :subject fn-lc-allocate-segment
  :witness ((next-id 22) (exhaustedp nil))
  :breaks ((id ((next-id -2) (exhaustedp nil))
            :logical "outside the allocator's u64 guard; its next value is negative"))
  :mutations ((advance (:conclusion
    (let ((out (fn-lc-allocate-segment next-id exhaustedp)))
             (and (iff (equal (mv-nth 0 out) '(:refused :segment-id-exhausted))
                       exhaustedp)
                  (implies (not exhaustedp)
                           (and (equal (mv-nth 1 out) next-id)
                                (unsigned-byte-p 64 (mv-nth 2 out))
                                (if (equal next-id 18446744073709551615)
                                    (and (equal (mv-nth 2 out) next-id)
                                         (equal (mv-nth 3 out) t))
                                  (and (equal (mv-nth 2 out) next-id)
                                       (equal (mv-nth 3 out) nil))))))))
               ((next-id 22) (exhaustedp nil))
               :fault "allocator leaves next-id unchanged instead of advancing")))

