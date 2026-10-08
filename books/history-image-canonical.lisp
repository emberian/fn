; Canonical image refinement of the two-pass, single-allocation page-store build.
(in-package "ACL2")
(include-book "history-image-build-proof")
(include-book "history-image-all-proof")
(include-book "history-image-open-content")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-his-canonical-empty-placement
 (adt-placement-ok (fn-hp-starts h salt) '(0 0 0 0 0) (fn-hp-npages h salt))
 :hints (("Goal" :do-not-induct t
          :use (fn-hp-placement-ok-of-image
                (:instance fn-hp-placement-mono (starts (fn-hp-starts h salt)) (np (fn-hp-npages h salt))
                  (lens '(0 0 0 0 0)) (lens2 (fn-hp-lens h salt)))
                (:instance fn-hp-caps-le-x-add (lens '(0 0 0 0 0)) (d (fn-hp-lens h salt))))
          :in-theory (disable fn-hp-placement-mono fn-hp-caps-le-x-add fn-hp-caps-le
                              fn-hp-x-add fn-hp-lens fn-hp-starts fn-hp-npages fn-his-canonical-lens
                              adt-placement-ok))))

(defthm fn-his-open-starts-empty-prefix
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
               (equal (pgs-d-length pgs-mem) 0))
  (equal
   (nth *pgs-wi*
    (fn-his-rcs-flush-write (caddr *fn-his-pw0*) (fn-hp-starts h salt)
     (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem))))
   (fn-hp-rep (fn-hp-piw nil salt (fn-hp-starts h salt) (fn-hp-npages h salt)) 0
               (fn-hp-hdr2 (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) (fn-hp-npages h salt)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-canonical-empty-placement fn-his-image-open-words
                (:instance fn-his-empty-fixed-header (starts (fn-hp-starts h salt)) (np (fn-hp-npages h salt))
                  (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) (fn-hp-npages h salt)))))
          :in-theory (e/d (fn-his-rcs-flush-write)
                          (fn-his-image-open fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages fn-his-canonical-lens
                           fn-hp-piw fn-hp-piw-caps-extend fn-hp-rep fn-hp-hdr2 fn-his-image-open-words
                           fn-his-empty-fixed-header adt-placement-ok nth adt-nth-0 adt-nth-1+)))))

(defthm fn-his-place-drive-canonical-words
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
               (equal (pgs-d-length pgs-mem) 0))
  (let ((res (fn-his-place-drive (+ 1 (len h)) h salt *fn-his-pw0*
              (fn-hp-starts h salt) (fn-hp-npages h salt)
              (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem)))))
   (equal (nth *pgs-wi* (fn-his-rcs-flush-write (caddr (mv-nth 1 res)) (fn-hp-starts h salt) (mv-nth 2 res)))
          (fn-hp-piw h salt (fn-hp-starts h salt) (fn-hp-npages h salt)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-hp-placement-ok-of-image fn-his-open-starts-empty-prefix
                (:instance fn-his-place-all-extends-prefix
                  (seen nil) (pw *fn-his-pw0*) (starts (fn-hp-starts h salt)) (np (fn-hp-npages h salt))
                  (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) (fn-hp-npages h salt)))
                  (pgs-mem (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem))))
                (:instance fn-his-place-drive-is-place-all
                  (evs h) (pw *fn-his-pw0*) (starts (fn-hp-starts h salt)) (np (fn-hp-npages h salt))
                  (pgs-mem (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem)))))
          :in-theory (disable fn-his-place-all fn-his-place-drive fn-his-image-open fn-his-rcs-flush-write
                              fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages fn-his-canonical-lens
                              fn-hp-piw fn-hp-piw-caps-extend fn-hp-rep fn-hp-hdr2
                              fn-hp-x-add fn-his-cursors-at fn-his-pwp adt-placement-ok
                              fn-his-place-all-extends-prefix nth adt-nth-0 adt-nth-1+))))

(defthm fn-his-image-close-flushes-by-definition
 (implies (equal (mv-nth 0 (fn-his-image-close plan pw starts pgs-mem)) :ok)
          (equal (mv-nth 1 (fn-his-image-close plan pw starts pgs-mem))
                 (fn-his-rcs-flush-write (caddr pw) starts pgs-mem)))
 :hints (("Goal" :in-theory (e/d (fn-his-image-close fn-his-rcs-flush)
                                (fn-his-pwp fn-his-rcs-flush-fitp fn-his-rcs-flush-write)))))

(defthm fn-his-image-build-pgs-words
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
               (equal (pgs-d-length pgs-mem) 0))
  (equal (nth *pgs-wi* (mv-nth 5 (fn-his-image-build-pgs h salt pgs-mem)))
         (fn-hp-iw h salt)))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-image-build-pgs-accepts fn-his-place-drive-after-open-accepts
                fn-his-place-drive-canonical-words fn-hp-piw-canonical)
          :in-theory (e/d (fn-his-image-build-pgs)
                          (fn-his-plan-drive fn-his-place-drive fn-his-image-open fn-his-image-close
                           fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages fn-his-canonical-lens
                           fn-hp-piw fn-hp-piw-canonical fn-hp-piw-caps-extend fn-hp-iw
                           fn-his-rcs-flush-write fn-his-image-build-pgs-accepts
                           nth adt-nth-0 adt-nth-1+)))))

(defthm fn-his-place-drive-keeps-all-dirty
 (implies (and (natp p) (natp np) (fn-his-all-dirty p np (nth *pgs-di* pgs-mem)))
  (fn-his-all-dirty p np
   (nth *pgs-di* (mv-nth 2 (fn-his-place-drive (+ 1 (len evs)) evs salt pw starts np pgs-mem)))))
 :hints (("Goal" :use fn-his-place-drive-is-place-all
          :in-theory (disable fn-his-place-drive fn-his-place-all fn-his-all-dirty nth adt-nth-1+))))

(defthm fn-his-image-build-pgs-all-dirty
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
               (equal (pgs-d-length pgs-mem) 0))
  (fn-his-all-dirty 0 (fn-hp-npages h salt)
   (nth *pgs-di* (mv-nth 5 (fn-his-image-build-pgs h salt pgs-mem)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-place-drive-after-open-accepts fn-his-image-open-all-dirty)
          :in-theory (e/d (fn-his-image-build-pgs)
                          (fn-his-plan-drive fn-his-place-drive fn-his-image-open fn-his-image-close
                           fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages fn-his-canonical-lens
                           fn-his-all-dirty nth adt-nth-1+)))))

; Signed MEM-013 page-store statement, unchanged.
(defthm fn-his-image-build-pgs-is-canonical-image
  (implies (and (fn-hp-okp h salt)
                (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
                (equal (pgs-d-length pgs-mem) 0))
           (let* ((res (fn-his-image-build-pgs h salt pgs-mem))
                  (n (mv-nth 1 res)) (lens (mv-nth 2 res)) (starts (mv-nth 3 res))
                  (np (mv-nth 4 res)) (mem2 (mv-nth 5 res)))
             (and (equal (mv-nth 0 res) :ok)
                  (equal (nth *pgs-wi* mem2) (fn-hp-iw h salt))
                  (equal (pgs-w-length mem2) (* 2048 (fn-hp-npages h salt)))
                  (equal (pgs-v-length mem2) (fn-hp-npages h salt))
                  (equal (pgs-d-length mem2) (fn-hp-npages h salt))
                  (equal n (len h)) (equal lens (fn-hp-lens h salt))
                  (equal starts (fn-hp-starts h salt)) (equal np (fn-hp-npages h salt))
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h salt starts np))
                  (fn-his-all-dirty 0 np (nth *pgs-di* mem2)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-image-build-pgs-accepts fn-his-image-build-pgs-words fn-his-image-build-pgs-all-dirty
                fn-hp-piw-canonical
                (:instance fn-hp-vhold-own-words (p 0)
                  (np (pgs-v-length (mv-nth 5 (fn-his-image-build-pgs h salt pgs-mem))))
                  (mem (mv-nth 5 (fn-his-image-build-pgs h salt pgs-mem)))))
          :in-theory (theory 'minimal-theory)))
  :rule-classes nil)
