; Canonical planning and allocation facts for the final-placement build.
(in-package "ACL2")
(include-book "history-image-open")
(include-book "history-image-plan-proof")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-his-layout-canonical
 (implies (fn-hp-okp h salt)
  (equal (fn-his-layout (list (len h) (fn-hp-lens h salt)))
         (list nil (fn-hp-starts h salt) (fn-hp-npages h salt))))
 :hints (("Goal" :do-not-induct t
          :use fn-hp-okp-u64-facts
          :in-theory (e/d (fn-his-layout fn-hp-regs fn-hp-okp fn-hp-image fn-hp-lens fn-hp-starts fn-hp-npages)
                          (fn-his-canonical-lens fn-hp-end-is-caps-sum fn-hp-rows fn-hp-events-okp
                           adt-regs adt-ser adt-lens adt-starts-l adt-end-l fn-hp-okp-u64-facts)))))

(defthm fn-his-layout-acceptance-implies-holdable
 (implies (and (fn-hp-events-okp h)
               (not (mv-nth 0 (fn-his-layout (list (len h) (fn-hp-lens h salt))))))
          (fn-hp-okp h salt))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-his-layout fn-hp-regs fn-hp-okp fn-hp-image fn-hp-lens)
                          (fn-his-canonical-lens fn-hp-end-is-caps-sum fn-hp-rows
                           fn-hp-events-okp adt-regs adt-ser adt-lens adt-starts-l adt-end-l)))))

(defthm fn-his-image-open-canonical-layout
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) 0)
               (equal (pgs-v-length pgs-mem) 0)
               (equal (pgs-d-length pgs-mem) 0))
  (let ((res (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem)))
   (and (equal (mv-nth 0 res) nil)
        (equal (mv-nth 1 res) (fn-hp-starts h salt))
        (equal (mv-nth 2 res) (fn-hp-npages h salt)))))
 :hints (("Goal" :in-theory (e/d (fn-his-image-open)
                                (fn-his-layout fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages
                                 fn-his-canonical-lens pgs-x-grow-image fn-hp-x-put fn-hp-x-mark
                                 fn-hp-hdr2)))))

(defthm fn-his-mark-keeps-d-length
 (implies (and (natp i) (natp k) (<= k (pgs-d-length pgs-mem)))
          (equal (pgs-d-length (fn-hp-x-mark i k pgs-mem)) (pgs-d-length pgs-mem)))
 :hints (("Goal" :induct (fn-hp-x-mark i k pgs-mem)
          :in-theory (enable fn-hp-x-mark))))

(defthm fn-his-image-open-canonical-lengths
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) 0)
               (equal (pgs-v-length pgs-mem) 0)
               (equal (pgs-d-length pgs-mem) 0))
  (let ((mem (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem))))
   (and (equal (pgs-w-length mem) (* 2048 (fn-hp-npages h salt)))
        (equal (pgs-d-length mem) (fn-hp-npages h salt))
        (equal (pgs-v-length mem) (fn-hp-npages h salt)))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hp-grow-image-lengths (np 0) (npn (fn-hp-npages h salt)))
                (:instance fn-his-mark-keeps-d-length
                  (i 0) (k (fn-hp-npages h salt))
                  (pgs-mem (fn-hp-x-put 0
                            (fn-hp-hdr2 (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) (fn-hp-npages h salt))
                            (pgs-x-grow-image (fn-hp-npages h salt) pgs-mem)))))
          :in-theory (e/d (fn-his-image-open)
                                (fn-his-layout fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages
                                 fn-his-canonical-lens pgs-x-grow-image fn-hp-x-put fn-hp-x-mark
                                 fn-hp-hdr2 floor)))))
