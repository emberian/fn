; Host entries on fn-hrecs$c wrap the generated page-store quanta.
(in-package "ACL2")
(include-book "history-image-canonical")

(defun fn-his-build-open (plan fn-hrecs$c)
 (declare (xargs :stobjs fn-hrecs$c :guard (fn-his-planp plan)))
 (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
            (v starts np pgs-mem)
            (fn-his-image-open plan pgs-mem)
            (mv v starts np fn-hrecs$c)))

(defun fn-his-build-place-run (k evs pw starts np fn-hrecs$c)
 (declare (xargs :stobjs fn-hrecs$c :guard (natp k)))
 (let ((salt (fn-hrc-salt fn-hrecs$c)))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (v rest pw2 pgs-mem)
             (fn-his-place-run k evs salt pw starts np pgs-mem)
             (mv v rest pw2 fn-hrecs$c))))

(defun fn-his-build-place-drive (fuel evs pw starts np fn-hrecs$c)
 ; The driver is the same generated page-store driver, under the same wrapper.
 ; Its equation below is over fn-his-build-place-run, the entry the host calls.
 (declare (xargs :stobjs fn-hrecs$c :guard (natp fuel)))
 (let ((salt (fn-hrc-salt fn-hrecs$c)))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (v pw2 pgs-mem)
             (fn-his-place-drive fuel evs salt pw starts np pgs-mem)
             (mv v pw2 fn-hrecs$c))))

(defun fn-his-build-close (plan pw starts np fn-hrecs$c)
 (declare (xargs :stobjs fn-hrecs$c :guard (and (fn-his-pwp pw) (natp np))
                 :guard-hints (("Goal" :in-theory (enable fn-his-pwp)))))
 (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
            (v pgs-mem)
            (fn-his-image-close plan pw starts pgs-mem)
            (if (eq v :ok)
                (let* ((fn-hrecs$c (update-fn-hrc-img 1 fn-hrecs$c))
                       (fn-hrecs$c (update-fn-hrc-nimg (car pw) fn-hrecs$c))
                       (fn-hrecs$c (update-fn-hrc-lens (cadr pw) fn-hrecs$c))
                       (fn-hrecs$c (update-fn-hrc-starts starts fn-hrecs$c))
                       (fn-hrecs$c (update-fn-hrc-npages np fn-hrecs$c)))
                  (mv :ok fn-hrecs$c))
              (mv v fn-hrecs$c))))

(defthm fn-his-build-place-drive-preserves-pwp
 (implies (fn-his-pwp pw)
  (fn-his-pwp (mv-nth 1 (fn-his-build-place-drive (+ 1 (len evs)) evs pw starts np fn-hrecs$c))))
 :hints (("Goal" :in-theory (e/d (fn-his-build-place-drive)
                                (fn-his-place-drive fn-his-pwp)))))

(defthm fn-his-build-open-npages-natural
 (natp (mv-nth 2 (fn-his-build-open plan fn-hrecs$c)))
 :hints (("Goal" :in-theory (e/d (fn-his-build-open fn-his-image-open fn-his-layout)
                                (pgs-x-grow-image fn-hp-x-put fn-hp-x-mark fn-hp-hdr2 adt-end-l adt-starts-l))))
 :rule-classes :type-prescription)

(defun fn-his-image-build-c (h salt fn-hrecs$c)
 (declare (xargs :stobjs fn-hrecs$c :guard (natp salt)
                 :guard-hints (("Goal" :in-theory
                   (disable fn-his-build-open fn-his-build-place-drive fn-his-build-close
                            fn-his-plan-drive fn-his-planp fn-his-pwp)))))
 (let ((fn-hrecs$c (fn-his-build-begin salt fn-hrecs$c)))
  (mv-let (v plan) (fn-his-plan-drive (+ 1 (len h)) h (list 0 '(0 0 0 0 0)))
   (if v (mv v fn-hrecs$c)
    (mv-let (v starts np fn-hrecs$c) (fn-his-build-open plan fn-hrecs$c)
     (if v (mv v fn-hrecs$c)
      (mv-let (v pw fn-hrecs$c) (fn-his-build-place-drive (+ 1 (len h)) h *fn-his-pw0* starts np fn-hrecs$c)
       (if (not (eq v :ok)) (mv v fn-hrecs$c)
        (fn-his-build-close plan pw starts np fn-hrecs$c)))))))))

(local
 (defthm fn-his-pgs-update-overwrite
  (equal (update-fn-hrc-pgs b (update-fn-hrc-pgs a c)) (update-fn-hrc-pgs b c))
  :hints (("Goal" :in-theory (enable update-fn-hrc-pgs update-nth)))))
(local
 (defthm fn-his-pgs-update-same
  (implies (consp c) (equal (update-fn-hrc-pgs (fn-hrc-pgs c) c) c))
  :hints (("Goal" :in-theory (enable fn-hrc-pgs update-fn-hrc-pgs update-nth)))))

(defthm fn-his-build-place-drive-unfolds
 (implies (consp fn-hrecs$c)
  (equal (fn-his-build-place-drive fuel evs pw starts np fn-hrecs$c)
   (if (zp fuel) (list '(:refused :fuel) pw fn-hrecs$c)
    (mv-let (v rest pw2 c2)
     (fn-his-build-place-run *fn-his-build-yield-rows* evs pw starts np fn-hrecs$c)
     (cond ((eq v :done) (list :ok pw2 c2))
           ((eq v :more) (fn-his-build-place-drive (1- fuel) rest pw2 starts np c2))
           (t (list v pw2 c2)))))))
 :hints (("Goal" :do-not-induct t
          :expand ((fn-his-place-drive fuel evs (fn-hrc-salt fn-hrecs$c) pw starts np (fn-hrc-pgs fn-hrecs$c)))
          :in-theory (e/d (fn-his-build-place-drive fn-his-build-place-run)
                          (fn-his-place-drive fn-his-place-run fn-hrc-fields fn-hrc-updaters)))))

(defthm fn-his-build-begin-fields
 (let ((c (fn-his-build-begin salt fn-hrecs$c)))
  (and (equal (fn-hrc-img c) 0) (equal (fn-hrc-nimg c) 0)
       (equal (fn-hrc-salt c) salt) (equal (fn-hrc-lens c) '(0 0 0 0 0))
       (equal (fn-hrc-starts c) '(1 1 1 1 1)) (equal (fn-hrc-npages c) 0)
       (equal (fn-hrc-txid c) 0) (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0)
       (equal (fn-hrc-sfx-length c) 0)
       (equal (pgs-w-length (fn-hrc-pgs c)) 0)
       (equal (pgs-v-length (fn-hrc-pgs c)) 0)
       (equal (pgs-d-length (fn-hrc-pgs c)) 0)))
 :hints (("Goal" :in-theory (e/d (fn-his-build-begin fn-hrc-reset fn-hrs-pgs-empty resize-pgs-tv pgs-w-length pgs-v-length pgs-d-length)
                                (fn-hrc-fields fn-hrc-updaters)))))

(defthm fn-his-image-open-status
 (not (equal (mv-nth 0 (fn-his-image-open plan pgs-mem)) :ok))
 :hints (("Goal" :in-theory (e/d (fn-his-image-open fn-his-layout)
                                (pgs-x-grow-image fn-hp-x-put fn-hp-x-mark fn-hp-hdr2 adt-end-l adt-starts-l)))))

(defthm fn-his-image-build-c-refines-pgs
 (let* ((c0 (fn-his-build-begin salt fn-hrecs$c))
        (pgs (fn-his-image-build-pgs h salt (fn-hrc-pgs c0)))
        (res (fn-his-image-build-c h salt fn-hrecs$c)) (c2 (mv-nth 1 res)))
  (and (equal (mv-nth 0 res) (mv-nth 0 pgs))
       (equal (fn-hrc-pgs c2) (mv-nth 5 pgs))
       (equal (fn-hrc-img c2) (if (eq (mv-nth 0 pgs) :ok) 1 0))
       (equal (fn-hrc-nimg c2) (if (eq (mv-nth 0 pgs) :ok) (mv-nth 1 pgs) 0))
       (equal (fn-hrc-lens c2) (if (eq (mv-nth 0 pgs) :ok) (mv-nth 2 pgs) '(0 0 0 0 0)))
       (equal (fn-hrc-starts c2) (if (eq (mv-nth 0 pgs) :ok) (mv-nth 3 pgs) '(1 1 1 1 1)))
       (equal (fn-hrc-npages c2) (if (eq (mv-nth 0 pgs) :ok) (mv-nth 4 pgs) 0))
       (equal (fn-hrc-salt c2) salt) (equal (fn-hrc-txid c2) 0)
       (equal (fn-hrc-lo c2) 0) (equal (fn-hrc-hi c2) 0) (equal (fn-hrc-sfx-length c2) 0)))
 :hints (("Goal" :do-not-induct t
          :in-theory (union-theories
            '(fn-his-image-build-c fn-his-build-open fn-his-build-place-drive fn-his-build-close
              fn-his-image-build-pgs fn-his-build-begin-fields fn-his-image-open-status fn-his-plan-drive-verdict
              fn-hrc-row-pgs fn-hrc-row-img fn-hrc-row-nimg fn-hrc-row-lens fn-hrc-row-starts fn-hrc-row-npages
              car-cons cdr-cons mv-nth fn-hp-mv-nth-cons eq)
            (theory 'minimal-theory)))))

(defun fn-his-build-quantum ()
 (declare (xargs :guard t))
 *fn-his-build-yield-rows*)

(defun fn-his-plan-begin ()
 (declare (xargs :guard t))
 '(0 (0 0 0 0 0)))

(defun fn-his-place-begin ()
 (declare (xargs :guard t))
 *fn-his-pw0*)
