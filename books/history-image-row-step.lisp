; Native private scratch row continuation. Encoding/writing the event and
; flat-array growth retain their current costs; relocation schedules one
; existing page primitive per turn. No intermediate backing is served.
(in-package "ACL2")
(include-book "history-image-build-rows")
(include-book "history-pages-relocate-run")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-his-row-cursorp (cursor)
  (declare (xargs :guard t))
  (or (equal cursor '(:append))
      (and (true-listp cursor) (equal (len cursor) 2)
           (eq (car cursor) :relocate) (fn-hpr-cursorp (cadr cursor)))))

(defun fn-his-row-begin (ev fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)
                  :guard-hints (("Goal" :in-theory
                    (disable fn-hrc-wfp fn-hrc-append fn-hrc-flush-init)))))
  (if (not (and (equal (fn-hrc-lo fn-hrecs$c) 0)
                (equal (fn-hrc-hi fn-hrecs$c) 0)))
      (mv '(:refused :pending-suffix) nil fn-hrecs$c)
    (let ((fn-hrecs$c (fn-hrc-append ev fn-hrecs$c)))
      (mv-let (v fn-hrecs$c)
        (if (equal (fn-hrc-img fn-hrecs$c) 1)
            (mv :ok fn-hrecs$c)
          (fn-hrc-flush-init fn-hrecs$c))
        (mv (if (eq v :ok) :yield v)
            (and (eq v :ok) '(:append)) fn-hrecs$c)))))

(defun fn-his-row-append-step (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c
                  :guard (and (fn-hrc-wfp fn-hrecs$c)
                              (equal (fn-hrc-img fn-hrecs$c) 1)
                              (< (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)))
                  :verify-guards nil))
  (let ((ev (fn-hrc-sfxi (fn-hrc-lo fn-hrecs$c) fn-hrecs$c))
        (salt (fn-hrc-salt fn-hrecs$c))
        (n (fn-hrc-nimg fn-hrecs$c)) (lens (fn-hrc-lens fn-hrecs$c))
        (starts (fn-hrc-starts fn-hrecs$c)) (np (fn-hrc-npages fn-hrecs$c)))
    (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
               (v n2 lens2 pgs-mem)
               (fn-hp-x-append ev salt n lens starts np pgs-mem)
               (cond
                ((eq v :ok)
                 (let* ((fn-hrecs$c (update-fn-hrc-nimg n2 fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-lens lens2 fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-lo (+ 1 (fn-hrc-lo fn-hrecs$c)) fn-hrecs$c))
                        (fn-hrecs$c (fn-his-build-recycle fn-hrecs$c)))
                   (mv :done nil fn-hrecs$c)))
                ((and (consp v) (eq (car v) :grow))
                 (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
                            (rv cursor pgs-mem)
                            (fn-hpr-begin (cadr v) (caddr v) n lens starts np pgs-mem)
                            (mv rv (and (eq rv :yield) (list :relocate cursor)) fn-hrecs$c)))
                (t (mv v nil fn-hrecs$c))))))

(defun fn-his-row-relocate-step (grow cursor fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c
                  :guard (and (booleanp grow) (fn-hpr-cursorp cursor)
                              (fn-hrc-wfp fn-hrecs$c))
                  :verify-guards nil))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (v next pgs-mem)
             (if grow (fn-hpr-grow-image cursor pgs-mem)
               (fn-hpr-step cursor pgs-mem))
             (if (eq v :done)
                 (let* ((placement (fn-hpr-final-placement next))
                        (fn-hrecs$c (update-fn-hrc-starts (car placement) fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-npages (cadr placement) fn-hrecs$c)))
                   (mv :yield '(:append) fn-hrecs$c))
               (mv v (list :relocate next) fn-hrecs$c))))

(defun fn-his-row-step (cursor fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c
                  :guard (and (fn-his-row-cursorp cursor) (fn-hrc-wfp fn-hrecs$c))
                  :verify-guards nil))
  (if (equal cursor '(:append))
      (if (and (equal (fn-hrc-img fn-hrecs$c) 1)
               (< (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)))
          (fn-his-row-append-step fn-hrecs$c)
        (mv '(:refused :pending-suffix) nil fn-hrecs$c))
    (fn-his-row-relocate-step nil (cadr cursor) fn-hrecs$c)))

(defun fn-his-row-grow (cursor fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c
                  :guard (and (fn-his-row-cursorp cursor) (fn-hrc-wfp fn-hrecs$c))
                  :verify-guards nil))
  (if (equal cursor '(:append))
      (mv '(:refused :continuation-state) cursor fn-hrecs$c)
    (fn-his-row-relocate-step t (cadr cursor) fn-hrecs$c)))

(verify-guards fn-his-row-append-step
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-types
                            (ev (fn-hrc-sfxi (fn-hrc-lo fn-hrecs$c) fn-hrecs$c))
                            (salt (fn-hrc-salt fn-hrecs$c))
                            (n (fn-hrc-nimg fn-hrecs$c))
                            (lens (fn-hrc-lens fn-hrecs$c))
                            (starts (fn-hrc-starts fn-hrecs$c))
                            (np (fn-hrc-npages fn-hrecs$c))
                            (pgs-mem (fn-hrc-pgs fn-hrecs$c)))
                 (:instance fn-hp-x-append-grow-shape
                            (ev (fn-hrc-sfxi (fn-hrc-lo fn-hrecs$c) fn-hrecs$c))
                            (salt (fn-hrc-salt fn-hrecs$c))
                            (n (fn-hrc-nimg fn-hrecs$c))
                            (lens (fn-hrc-lens fn-hrecs$c))
                            (starts (fn-hrc-starts fn-hrecs$c))
                            (np (fn-hrc-npages fn-hrecs$c))
                            (pgs-mem (fn-hrc-pgs fn-hrecs$c))))
           :in-theory (e/d (fn-hrc-wfp)
                            (fn-hp-x-append fn-hpr-begin fn-his-build-recycle
                             fn-hp-x-append-grow-shape fn-hp-x-append-plan
                             fn-hp-x-lens-after fn-hp-x-add fn-hp-x-unfit
                             fn-hp-x-append-types fn-hp-x-append-ok-unfolds
                             fn-hp-x-append-grow-is-plan fn-hp-x-append-grow-region
                             fn-hp-x-append-plan-grow
                             fn-hrecs$cp fn-hrc-fields fn-hrc-updaters)))))

(local
 (defthm fn-his-nat-list-update
   (implies (and (nat-listp xs) (natp i) (< i (len xs)) (natp x))
            (nat-listp (update-nth i x xs)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-his-relocation-placement-shape
   (implies (fn-hpr-cursorp cursor)
            (and (nat-listp (car (fn-hpr-final-placement cursor)))
                 (equal (len (car (fn-hpr-final-placement cursor))) 5)
                 (natp (cadr (fn-hpr-final-placement cursor)))))
   :hints (("Goal" :in-theory (e/d (fn-hpr-final-placement fn-hpr-cursorp)
                                    (nth update-nth))))))

(verify-guards fn-his-row-relocate-step
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-his-relocation-placement-shape
                            (cursor (mv-nth 1 (fn-hpr-step cursor (fn-hrc-pgs fn-hrecs$c)))))
                 (:instance fn-his-relocation-placement-shape
                            (cursor (mv-nth 1 (fn-hpr-grow-image cursor (fn-hrc-pgs fn-hrecs$c))))))
           :in-theory (e/d (fn-hrc-wfp fn-hpr-final-placement)
                            (fn-hpr-step fn-hpr-grow-image fn-hpr-cursorp
                             fn-his-relocation-placement-shape fn-hrecs$cp
                             fn-hrc-fields fn-hrc-updaters)))))

(verify-guards fn-his-row-step
  :hints (("Goal" :in-theory (e/d (fn-his-row-cursorp fn-hrc-wfp)
                                    (fn-his-row-append-step fn-his-row-relocate-step
                                     fn-hpr-cursorp fn-hrecs$cp
                                     fn-hrc-fields fn-hrc-updaters)))))

(verify-guards fn-his-row-grow
  :hints (("Goal" :in-theory (e/d (fn-his-row-cursorp)
                                    (fn-his-row-relocate-step fn-hrc-wfp
                                     fn-hpr-cursorp)))))

(defthm fn-his-row-begin-appends-history
  (implies (and (fn-hrc-wfp c) (fn-hrs-rel h c))
           (let ((next (mv-nth 2 (fn-his-row-begin ev c))))
             (and (fn-hrc-wfp next)
                  (if (and (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0))
                      (fn-hrs-rel (append h (list ev)) next)
                    (and (equal next c)
                         (equal (mv-nth 0 (fn-his-row-begin ev c))
                                '(:refused :pending-suffix)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrc-append-rel (fn-hrecs$c c))
                 (:instance fn-hrc-wfp-img-cases (fn-hrecs$c (fn-hrc-append ev c)))
                 (:instance fn-hrc-flush-init-frame (fn-hrecs$c (fn-hrc-append ev c)))
                 (:instance fn-hrc-flush-init-rel
                            (fn-hrecs$c (fn-hrc-append ev c))
                            (h (append h (list ev)))))
           :in-theory (e/d (fn-his-row-begin)
                          (fn-hrc-wfp fn-hrs-rel fn-hrc-append fn-hrc-flush-init
                           fn-hrc-flush-init-shape fn-hrc-flush-init-rel
                           fn-hrc-flush-init-frame)))))

(defthm fn-his-row-append-step-keeps-shape
  (implies (and (fn-hrc-wfp c) (equal (fn-hrc-img c) 1)
                (< (fn-hrc-lo c) (fn-hrc-hi c)))
           (fn-hrc-wfp (mv-nth 2 (fn-his-row-append-step c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-his-row-append-step fn-hrc-wfp fn-his-build-recycle)
                          (fn-hp-x-append fn-hpr-begin
                           fn-hp-x-append-plan fn-hp-x-append-ok-unfolds
                           fn-hrc-fields fn-hrc-updaters)))))

(defthm fn-his-row-relocate-step-keeps-shape
  (implies (and (fn-hrc-wfp c) (fn-hpr-cursorp cursor))
           (fn-hrc-wfp (mv-nth 2 (fn-his-row-relocate-step grow cursor c))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-his-relocation-placement-shape
                            (cursor (mv-nth 1 (fn-hpr-step cursor (fn-hrc-pgs c)))))
                 (:instance fn-his-relocation-placement-shape
                            (cursor (mv-nth 1 (fn-hpr-grow-image cursor (fn-hrc-pgs c))))))
           :in-theory (e/d (fn-his-row-relocate-step fn-hrc-wfp fn-hpr-final-placement)
                          (fn-hpr-step fn-hpr-grow-image fn-hpr-cursorp
                           fn-his-relocation-placement-shape fn-hrc-fields fn-hrc-updaters)))))

(local
 (defthm fn-his-relocate-leaf-potential-kept
   (implies (fn-hpr-cursorp cursor)
            (let ((reply (if grow (fn-hpr-grow-image cursor pgs-mem)
                           (fn-hpr-step cursor pgs-mem))))
              (equal (fn-hpr-target (mv-nth 1 reply) (mv-nth 2 reply))
                     (fn-hpr-target cursor pgs-mem))))
   :hints (("Goal" :do-not-induct t
            :cases ((equal (car cursor) :grow-image))
            :use ((:instance fn-hpr-tick-preserves-target))
            :in-theory (e/d (fn-hpr-tick fn-hpr-step fn-hpr-grow-image)
                            (fn-hpr-target fn-hpr-remaining fn-hpr-cursorp
                             fn-hpr-phase fn-hpr-tick-preserves-target
                             fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark
                             fn-hp-x-ready pgs-x-grow-image adt-cap
                             adt-placement-ok fn-hp-hdr-m fn-hp-u64-listp))))))

(local
 (defthm fn-his-relocate-leaf-placement-kept
   (implies (fn-hpr-cursorp cursor)
            (let ((reply (if grow (fn-hpr-grow-image cursor pgs-mem)
                           (fn-hpr-step cursor pgs-mem))))
              (equal (fn-hpr-final-placement (mv-nth 1 reply))
                     (fn-hpr-final-placement cursor))))
   :hints (("Goal" :do-not-induct t
            :cases ((equal (car cursor) :grow-image))
            :use ((:instance fn-hpr-tick-keeps-placement))
            :in-theory (e/d (fn-hpr-tick fn-hpr-step fn-hpr-grow-image)
                            (fn-hpr-final-placement fn-hpr-cursorp
                             fn-hpr-phase fn-hpr-tick-keeps-placement
                             fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark
                             fn-hp-x-ready pgs-x-grow-image adt-cap
                             adt-placement-ok fn-hp-hdr-m fn-hp-u64-listp))))))

(defun-nx fn-his-row-relocation-target (cursor c)
  (let ((placement (fn-hpr-final-placement cursor)))
    (update-fn-hrc-npages (cadr placement)
      (update-fn-hrc-starts (car placement)
        (update-fn-hrc-pgs (fn-hpr-target cursor (fn-hrc-pgs c)) c)))))

(local
 (defthm fn-his-relocate-leaf-done-phase
   (implies (and (fn-hpr-cursorp cursor)
                 (equal (mv-nth 0 (if grow (fn-hpr-grow-image cursor pgs-mem)
                                   (fn-hpr-step cursor pgs-mem))) :done))
            (equal (car (mv-nth 1 (if grow (fn-hpr-grow-image cursor pgs-mem)
                                   (fn-hpr-step cursor pgs-mem)))) :done))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hpr-tick-done-phase))
            :in-theory (e/d (fn-hpr-tick fn-hpr-step fn-hpr-grow-image fn-hp-x-ready)
                            (fn-hpr-cursorp fn-hpr-phase fn-hpr-tick-done-phase
                             fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark
                             pgs-x-grow-image adt-cap adt-placement-ok
                             fn-hp-hdr-m fn-hp-u64-listp))))))
(local
 (defthm fn-his-relocate-leaf-done-target
   (implies (and (fn-hpr-cursorp cursor)
                 (equal (mv-nth 0 (if grow (fn-hpr-grow-image cursor pgs-mem)
                                   (fn-hpr-step cursor pgs-mem))) :done))
            (equal (mv-nth 2 (if grow (fn-hpr-grow-image cursor pgs-mem)
                               (fn-hpr-step cursor pgs-mem)))
                   (fn-hpr-target cursor pgs-mem)))
   :hints (("Goal" :use ((:instance fn-his-relocate-leaf-potential-kept)
                         (:instance fn-his-relocate-leaf-done-phase))
            :in-theory (disable fn-hpr-grow-image fn-hpr-step fn-hpr-target
                                fn-hpr-cursorp fn-his-relocate-leaf-potential-kept
                                fn-his-relocate-leaf-done-phase)))))

(defthm fn-his-row-relocate-step-keeps-completion
  (implies (and (fn-hrecs$cp c) (fn-hpr-cursorp cursor))
           (let* ((reply (fn-his-row-relocate-step grow cursor c))
                  (next (mv-nth 2 reply)))
             (if (equal (mv-nth 1 reply) '(:append))
                 (equal next (fn-his-row-relocation-target cursor c))
               (equal (fn-his-row-relocation-target (cadr (mv-nth 1 reply)) next)
                      (fn-his-row-relocation-target cursor c)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-his-relocate-leaf-potential-kept (grow t) (pgs-mem (fn-hrc-pgs c)))
                 (:instance fn-his-relocate-leaf-potential-kept (grow nil) (pgs-mem (fn-hrc-pgs c)))
                 (:instance fn-his-relocate-leaf-placement-kept (grow t) (pgs-mem (fn-hrc-pgs c)))
                 (:instance fn-his-relocate-leaf-placement-kept (grow nil) (pgs-mem (fn-hrc-pgs c)))
                 (:instance fn-his-relocate-leaf-done-target (grow t) (pgs-mem (fn-hrc-pgs c)))
                 (:instance fn-his-relocate-leaf-done-target (grow nil) (pgs-mem (fn-hrc-pgs c))))
           :in-theory (e/d (fn-his-row-relocate-step fn-his-row-relocation-target
                            update-fn-hrc-pgs fn-hrc-pgs)
                          (fn-hpr-step fn-hpr-grow-image fn-hpr-target
                           fn-hpr-final-placement fn-hpr-cursorp
                           fn-hrecs$cp)))))
