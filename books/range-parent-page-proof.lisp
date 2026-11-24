; Growing the tree takes two driver calls: extend the height, then open
; the new parent. The next call sees the same pending rows and child page.
(in-package "ACL2")
(include-book "runs-parent-height-proof")
(include-book "range-page-reservation-proof")

(defun-nx fn2-range-page-configuration-p (b w)
  (and (fn2-run-buildsp b) (fn2-run-builds-wfp b) (< 0 (fn2-run-builds-rows b))
       (fn2-run-writersp w) (fn2-run-writers-wfp w)
       (equal (fn2-run-builds-limit 0 b) 2048) (equal (fn2-run-builds-okind 0 b) 9)
       (equal (fn2-run-builds-oslot 0 b) 0) (equal (fn2-run-builds-ogen 0 b) 1)))

(local
 (defthm fn2-range-new-parent-ready-to-open
   (implies (and (fn2-run-sealed-top-ready-p level b w rs f fc ctx) (fn2-range-page-configuration-p b w))
            (fn2-range-ready-page-level-p (1+ level) (fn2-run-builds-set-height 0 (+ 2 level) b) w))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-sealed-top-ready-p fn2-range-page-configuration-p fn2-range-ready-page-level-p
                           fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-schema fn2-run-builds-fields
                           fn2-run-builds-limit fn2-run-builds-okind fn2-run-builds-oslot fn2-run-builds-ogen
                           fn2-run-builds-rows nth-update-nth)
                         (fn2-run-builds-set-height fn2-run-buildsp fn2-run-builds-wfp fn2-run-writersp fn2-run-writers-wfp
                          fn2-run-writers-phase fn2-run-writers-rows fn2-run-writerp fn2-fields-rows fn2-fc-rows fn2-fc-context-rows
                          fn2-run-builds-crow fn2-run-builds-hbase nth update-nth))))))

(local
 (defthm fn2-run-driver-opens-requested-page
   (fn2-range-with-reserved-page
    (implies (and (equal (fn2-run-build-work 0 4096 b w rs f p fc ctx b3 ds)
                         (list :need-page level b w rs f p fc ctx b3 ds))
                  (equal (car reserve) :ok) (equal (car page) :ok) (equal (mv-nth 1 page) b))
             (equal (fn2-run-run-onestep layout entries src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds)
                    (list nil :more entries at (+ 1 unit) pages b curs paths cache opened rs f pool fc ctx b3 ds))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (union-theories (theory 'minimal-theory)
                            '(fn2-run-run-onestep eq eql car-cons cdr-cons mv-nth (:e equal) (:e zp) (:e binary-+) (:e mv-nth)))))))

(defmacro fn2-range-with-new-parent (body)
  `(let ((b (fn2-run-builds-set-height 0 (+ 2 level) builds)) (level (1+ level)))
      (fn2-range-with-reserved-page ,body)))

(defthmd fn2-range-driver-opens-new-parent
  (implies (and (fn2-run-sealed-top-ready-p level builds w rs f fc ctx) (fn2-range-page-configuration-p builds w)
                (posp n) (<= n 327) (fn2-range-pool-available-p n p) (unsigned-byte-p 60 unit))
           (fn2-range-with-new-parent
            (and (equal (fn2-run-run-onestep layout entries src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds)
                        (list nil :more entries at (1+ unit) pages b curs paths cache opened rs f pool fc ctx b3 ds))
                 (equal slot (- 327 n)) (equal gen 1)
                 (fn2-run-empty-open-writer-p level 3 level slot gen 9 0 1 opened)
                 (equal (fn2-run-writers-fields level opened) (* level *fn2-run-writer-fields*))
                 (equal (fn2-run-writers-limit level opened) 2048)
                 (equal (fn2-pool-base slot pool) (* slot 65536))
                 (equal (fn2-layout-range-code slot gen *fn2-run-entries-base* *fn2-run-page-size* t 9 0 1 pool) :ok)
                 (fn2-range-pool-available-p (1- n) pool))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-grown-parent-requests-its-page (writers w) (restarts rs) (pool p))
                 (:instance fn2-range-reserving-opens-overview-page (level (1+ level))
                   (b (fn2-run-builds-set-height 0 (+ 2 level) builds)))
                 (:instance fn2-run-driver-opens-requested-page (level (1+ level))
                   (b (fn2-run-builds-set-height 0 (+ 2 level) builds)))
                 (:instance fn2-range-new-parent-ready-to-open (b builds)))
           :in-theory (theory 'minimal-theory))))

(defmacro fn2-range-parent-loop (fuel unit b w p)
  `(fn2-run-run-loop ,fuel layout entries src sg at ,unit pages ,b curs paths cache ,w rs f ,p fc ctx b3 ds))

(local
 (defthm fn2-run-one-call-from-remaining-fuel
   (implies (natp fuel) (and (not (zp (1+ fuel))) (equal (1- (1+ fuel)) fuel)))))

(local
 (defthm fn2-run-continue-with-same-input
   (implies (and (natp fuel)
                 (equal (fn2-run-run-onestep layout entries src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds)
                        (list done code entries at next-unit pages next-b curs paths cache next-w rs f next-p fc ctx b3 ds)))
            (equal (fn2-range-parent-loop (1+ fuel) unit b w p)
                   (if done (list code pages next-b curs paths cache next-w rs f next-p fc ctx b3 ds)
                     (fn2-range-parent-loop fuel next-unit next-b next-w next-p))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-range-parent-loop (1+ fuel) unit b w p))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-run-one-call-from-remaining-fuel mv-nth car-cons cdr-cons
                           (:e mv-nth) (:e binary-+) (:e zp) (:e equal)))))))

(defthmd fn2-range-builder-returns-sole-sealed-root
  (implies (and (natp fuel) (fn2-run-sealed-top-ready-p level builds w rs f fc ctx)
                (fn2-run-top-is-root-p level builds w))
           (equal (fn2-range-parent-loop (1+ fuel) unit builds w p)
                  (list :root pages (fn2-run-builds-set-phase 0 *fn2-run-build-phase-done* builds)
                        curs paths cache w rs f p fc ctx b3 ds)))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-driver-finishes-root-or-grows-parent (writers w) (restarts rs) (pool p) (off at))
                 (:instance fn2-run-continue-with-same-input (b builds) (done t) (code :root) (next-unit unit)
                            (next-b (fn2-run-builds-set-phase 0 *fn2-run-build-phase-done* builds)) (next-w w) (next-p p)))
           :in-theory (theory 'minimal-theory))))

(local
 (defthm fn2-run-two-calls-from-remaining-fuel
   (implies (natp fuel) (and (natp (1+ fuel)) (equal (1+ (1+ fuel)) (+ 2 fuel))))))

(defthmd fn2-range-builder-continues-with-new-parent
  (implies (and (natp fuel) (fn2-run-sealed-top-ready-p level builds w rs f fc ctx) (fn2-range-page-configuration-p builds w)
                (not (fn2-run-top-is-root-p level builds w)) (posp n) (<= n 327) (fn2-range-pool-available-p n p)
                (unsigned-byte-p 60 unit))
           (equal (fn2-range-parent-loop (+ 2 fuel) unit builds w p)
                  (fn2-range-with-new-parent (fn2-range-parent-loop fuel (1+ unit) b opened pool))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-driver-finishes-root-or-grows-parent (writers w) (restarts rs) (pool p) (off at))
                 fn2-range-driver-opens-new-parent
                 (:instance fn2-run-continue-with-same-input (fuel (1+ fuel)) (b builds) (done nil) (code :more)
                            (next-unit unit) (next-b (fn2-run-builds-set-height 0 (+ 2 level) builds)) (next-w w) (next-p p))
                 (:instance fn2-run-continue-with-same-input (done nil) (code :more) (next-unit (1+ unit))
                            (b (fn2-run-builds-set-height 0 (+ 2 level) builds))
                            (next-b (fn2-run-builds-set-height 0 (+ 2 level) builds))
                            (next-w (fn2-range-with-new-parent opened)) (next-p (fn2-range-with-new-parent pool))))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-run-two-calls-from-remaining-fuel (:e equal))))))
