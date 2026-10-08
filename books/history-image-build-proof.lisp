; Composition of canonical planning, one allocation, and final placement.
(in-package "ACL2")
(include-book "history-image-build")
(include-book "history-image-open-proof")
(include-book "history-image-place-proof")
(include-book "history-image-dirty-proof")
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-his-u64-list-natural
  (implies (fn-hp-u64-listp x) (nat-listp x))
  :hints (("Goal" :in-theory (enable fn-hp-u64-listp)))))

(defthm fn-his-canonical-plan-fields
 (implies (fn-hp-okp h salt)
  (and (fn-hp-events-okp h)
       (nat-listp (fn-hp-starts h salt))
       (fn-hp-u64-listp (fn-hp-lens h salt))))
 :hints (("Goal" :do-not-induct t
          :use fn-hp-okp-u64-facts
          :in-theory (e/d (fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-x-add)
                          (fn-hp-regs fn-hp-image fn-hp-events-okp fn-his-canonical-lens
                           fn-hp-okp-u64-facts adt-lens adt-starts-l)))))

(defthm fn-his-zero-add-canonical
 (equal (fn-hp-x-add '(0 0 0 0 0) (fn-hp-lens h salt)) (fn-hp-lens h salt))
 :hints (("Goal" :in-theory (e/d (fn-hp-x-add)
                                (fn-hp-lens fn-hp-pe fn-hp-pes-len fn-hp-pe-is-pad8)))))

(defthm fn-his-place-drive-after-open-accepts
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
               (equal (pgs-d-length pgs-mem) 0))
  (let* ((opened (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem))
         (res (fn-his-place-drive (+ 1 (len h)) h salt *fn-his-pw0*
                                  (mv-nth 1 opened) (mv-nth 2 opened) (mv-nth 3 opened)))
         (pw (mv-nth 1 res)))
   (and (equal (mv-nth 0 res) :ok)
        (equal (car pw) (len h))
        (equal (cadr pw) (fn-hp-lens h salt))
        (fn-his-cursors-at (caddr pw) (cadr pw)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-hp-placement-ok-of-image
                (:instance fn-his-place-all-accepts-planned
                  (pw *fn-his-pw0*) (starts (fn-hp-starts h salt)) (np (fn-hp-npages h salt))
                  (pgs-mem (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem))))
                (:instance fn-his-place-drive-is-place-all
                  (evs h) (pw *fn-his-pw0*) (starts (fn-hp-starts h salt)) (np (fn-hp-npages h salt))
                  (pgs-mem (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem)))))
          :in-theory (disable fn-his-place-all fn-his-place-drive fn-his-image-open
                              fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages fn-his-canonical-lens
                              fn-hp-x-add fn-his-cursors-at fn-his-pwp adt-placement-ok))))

(defthm fn-his-image-close-accepts-filled-plan
 (implies
  (and (fn-his-pwp pw) (fn-his-cursors-at (caddr pw) (cadr pw))
       (nat-listp starts) (equal (len starts) 5) (natp np)
       (adt-placement-ok starts (cadr pw) np)
       (equal (pgs-w-length pgs-mem) (* 2048 np)) (equal (pgs-d-length pgs-mem) np))
  (equal (mv-nth 0 (fn-his-image-close (list (car pw) (cadr pw)) pw starts pgs-mem)) :ok))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-his-cursors-at-shape (rcs (caddr pw)) (lens (cadr pw)))
                (:instance fn-his-cursors-at-fit-flush (rcs (caddr pw)) (lens (cadr pw))))
          :in-theory (e/d (fn-his-image-close fn-his-rcs-flush fn-his-pwp)
                          (fn-his-cursors-at fn-his-rcs-flush-fitp fn-his-rcs-flush-write
                           adt-placement-ok fn-his-cursors-at-shape fn-his-cursors-at-fit-flush)))))

(defthm fn-his-image-close-lengths-and-verified
 (let ((out (mv-nth 1 (fn-his-image-close plan pw starts pgs-mem))))
  (and (equal (pgs-w-length out) (pgs-w-length pgs-mem))
       (equal (pgs-d-length out) (pgs-d-length pgs-mem))
       (equal (pgs-v-length out) (pgs-v-length pgs-mem))
       (equal (nth *pgs-vi* out) (nth *pgs-vi* pgs-mem))))
 :hints (("Goal" :in-theory
          (e/d (fn-his-image-close fn-his-rcs-flush)
               (fn-his-pwp fn-his-rcs-flush-fitp fn-his-rcs-flush-write nth adt-nth-1+)))))

(defthm fn-his-place-drive-canonical-state
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) (* 2048 (fn-hp-npages h salt)))
               (equal (pgs-d-length pgs-mem) (fn-hp-npages h salt)))
  (let* ((res (fn-his-place-drive (+ 1 (len h)) h salt *fn-his-pw0*
                                  (fn-hp-starts h salt) (fn-hp-npages h salt) pgs-mem))
         (pw (mv-nth 1 res)) (mem (mv-nth 2 res)))
   (and (equal (mv-nth 0 res) :ok) (fn-his-pwp pw)
        (equal (car pw) (len h)) (equal (cadr pw) (fn-hp-lens h salt))
        (fn-his-cursors-at (caddr pw) (cadr pw))
        (equal (pgs-w-length mem) (pgs-w-length pgs-mem))
        (equal (pgs-d-length mem) (pgs-d-length pgs-mem))
        (equal (pgs-v-length mem) (pgs-v-length pgs-mem))
        (equal (nth *pgs-vi* mem) (nth *pgs-vi* pgs-mem)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-hp-placement-ok-of-image
                (:instance fn-his-place-all-accepts-planned
                  (pw *fn-his-pw0*) (starts (fn-hp-starts h salt)) (np (fn-hp-npages h salt)))
                (:instance fn-his-place-drive-is-place-all
                  (evs h) (pw *fn-his-pw0*) (starts (fn-hp-starts h salt)) (np (fn-hp-npages h salt))))
          :in-theory (disable fn-his-place-all fn-his-place-drive
                              fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages fn-his-canonical-lens
                              fn-hp-x-add fn-his-cursors-at fn-his-pwp adt-placement-ok nth adt-nth-1+))))

(defthm fn-his-image-build-pgs-accepts
 (implies (and (fn-hp-okp h salt)
               (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
               (equal (pgs-d-length pgs-mem) 0))
  (let ((res (fn-his-image-build-pgs h salt pgs-mem)))
   (and (equal (mv-nth 0 res) :ok)
        (equal (mv-nth 1 res) (len h))
        (equal (mv-nth 2 res) (fn-hp-lens h salt))
        (equal (mv-nth 3 res) (fn-hp-starts h salt))
        (equal (mv-nth 4 res) (fn-hp-npages h salt))
        (equal (pgs-w-length (mv-nth 5 res)) (* 2048 (fn-hp-npages h salt)))
        (equal (pgs-d-length (mv-nth 5 res)) (fn-hp-npages h salt))
        (equal (pgs-v-length (mv-nth 5 res)) (fn-hp-npages h salt)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-place-drive-after-open-accepts
                (:instance fn-his-place-drive-canonical-state
                 (pgs-mem (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem))))
                fn-hp-placement-ok-of-image
                (:instance fn-his-image-close-accepts-filled-plan
                 (starts (fn-hp-starts h salt)) (np (fn-hp-npages h salt))
                 (pw (mv-nth 1 (fn-his-place-drive (+ 1 (len h)) h salt *fn-his-pw0*
                                  (fn-hp-starts h salt) (fn-hp-npages h salt)
                                  (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem)))))
                 (pgs-mem (mv-nth 2 (fn-his-place-drive (+ 1 (len h)) h salt *fn-his-pw0*
                                  (fn-hp-starts h salt) (fn-hp-npages h salt)
                                  (mv-nth 3 (fn-his-image-open (list (len h) (fn-hp-lens h salt)) pgs-mem)))))))
          :in-theory (e/d (fn-his-image-build-pgs)
                          (fn-his-plan-drive fn-his-place-drive fn-his-image-open fn-his-image-close
                           fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages fn-his-canonical-lens
                           fn-hp-x-add fn-his-cursors-at fn-his-pwp adt-placement-ok nth adt-nth-1+)))))

(defthm fn-his-layout-refuses-unholdable-events
 (implies (and (fn-hp-events-okp h) (not (fn-hp-okp h salt)))
          (equal (mv-nth 0 (fn-his-layout (list (len h) (fn-hp-lens h salt))))
                 '(:refused :out-of-range)))
 :hints (("Goal" :use fn-his-layout-acceptance-implies-holdable
          :in-theory (e/d (fn-his-layout)
                          (fn-hp-okp fn-hp-lens fn-his-canonical-lens fn-hp-events-okp
                           fn-his-layout-acceptance-implies-holdable adt-starts-l adt-end-l)))))

(defthm fn-his-image-build-pgs-refuses-unholdable
 (implies (not (fn-hp-okp h salt))
          (not (equal (mv-nth 0 (fn-his-image-build-pgs h salt pgs-mem)) :ok)))
 :hints (("Goal" :do-not-induct t :cases ((fn-hp-events-okp h))
          :in-theory (e/d (fn-his-image-build-pgs fn-his-image-open)
                          (fn-his-plan-drive fn-his-place-drive fn-his-layout fn-his-image-close
                           fn-hp-okp fn-hp-lens fn-hp-starts fn-hp-npages fn-his-canonical-lens
                           fn-hp-events-okp pgs-x-grow-image fn-hp-x-put fn-hp-x-mark fn-hp-hdr2)))))
