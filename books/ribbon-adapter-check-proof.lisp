(in-package "ACL2")
(include-book "ribbon-mutation-state")

; Connect the public constructor to the driver, checker and probes.
(local
 (defthm fn2-ribbon-setup-fold
   (equal (fn2-rba-setup n (create-fn2-ribbon-builds) (create-fn2-ribbon-band) (create-fn2-run-writers) (create-fn2-run-restarts) (create-fn2-fields) (create-fn2-pool) (create-fn2-fc) (create-fn2-fc-context) (create-fn2-b3) (create-fn2-digests))
          (fn2-ribbon-fresh-state n))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-fresh-state) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-image-run-result
   (equal (fn2-ribbon-image keys drop queries mutate)
          (mv-nth 0 (fn2-rba-run keys drop queries mutate (create-fn2-ribbon-builds)
                       (create-fn2-ribbon-band)
                       (create-fn2-run-writers)
                       (create-fn2-run-restarts)
                       (create-fn2-fields)
                       (create-fn2-pool)
                       (create-fn2-fc)
                       (create-fn2-fc-context)
                       (create-fn2-b3)
                       (create-fn2-digests))))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-image mv-nth-of-cons (:e zp) (:e binary-+) car-cons cdr-cons)
                                             (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-prelude-initial-columns
   (and (equal (mv-nth 3 (fn2-ribbon-fresh-state n)) (fn2-run-writers-init 1 (create-fn2-run-writers)))
        (equal (mv-nth 6 (fn2-ribbon-fresh-state n)) (fn2-pool-init '((3 . 65536)) 1 100 (create-fn2-pool))))
   :hints (("Goal" :use fn2-ribbon-fresh-state-shape :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-ribbon-real-open-success
   (equal (mv-nth 0 (fn2-ribbon-opened-writer)) :ok)
   :hints (("Goal" :use fn2-ribbon-initial-page-and-key-arenas :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-ribbon-initial-success-codes
   (let ((n (len keys)))
     (implies (and (fn2-ribbon-keysp keys) (posp n) (<= n 256))
              (and (equal (mv-nth 0 (fn2-ribbon-started-build n)) :ok)
                   (equal (mv-nth 0 (fn2-ribbon-ready-state n)) :ready)
                   (equal (mv-nth 6 (fn2-ribbon-ready-state n)) (mv-nth 2 (fn2-ribbon-opened-writer)))
                   (equal (mv-nth 0 (fn2-ribbon-added-state keys)) :ok)
                   (equal (mv-nth 0 (fn2-ribbon-finish 0 (mv-nth 1 (fn2-ribbon-added-state keys)))) :ok))))
   :hints (("Goal" :use ((:instance fn2-ribbon-fresh-build-clears (n (len keys)))
                          (:instance fn2-ribbon-drive-clears-fresh-band (n (len keys)))
                          fn2-ribbon-fresh-adds-solve-key-equations fn2-ribbon-fresh-finish-enters-emitter)
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-ribbon-started-build-fold
   (equal (let ((st (fn2-ribbon-fresh-state n)))
     (fn2-ribbon-start 0 0 0 136 0 n (mv-nth 1 st) (mv-nth 2 st) (mv-nth 1 (fn2-ribbon-opened-writer))))
          (fn2-ribbon-started-build n))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-started-build) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-ready-state-fold
   (equal (fn2-ribbon-call-with-state fn2-rba-drive (100000) (fn2-ribbon-fresh-state n)
     (1 (mv-nth 1 (fn2-ribbon-started-build n))) (3 (mv-nth 1 (fn2-ribbon-opened-writer)))
     (6 (mv-nth 2 (fn2-ribbon-opened-writer))))
          (fn2-ribbon-ready-state n))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-ready-state) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-added-state-fold
   (equal (let ((reserve (fn2-ribbon-key-reservation)))
     (fn2-ribbon-call-with-state fn2-rba-adds (keys (mv-nth 1 reserve) (mv-nth 2 reserve) 0)
           (fn2-ribbon-ready-state (len keys)) (6 (mv-nth 3 reserve))))
          (fn2-ribbon-added-state keys))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-added-state) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-final-drive-fold
   (equal (let* ((added (fn2-ribbon-added-state keys)) (finish (fn2-ribbon-finish 0 (mv-nth 1 added))))
     (fn2-ribbon-call-with-state fn2-rba-drive (100000) added (1 (mv-nth 1 finish))))
          (fn2-ribbon-final-drive keys))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-final-drive) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-final-check-fold
   (equal (fn2-ribbon-call-with-state fn2-rba-check ((mv-nth 1 (fn2-ribbon-first-reservation)) (mv-nth 2 (fn2-ribbon-first-reservation))) (fn2-ribbon-final-drive keys))
          (fn2-ribbon-final-check keys))
   :hints (("Goal" :use fn2-ribbon-initial-page-and-key-arenas :in-theory (union-theories '(fn2-ribbon-final-check) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-final-answers-fold
   (equal (let* ((checked (fn2-ribbon-final-check keys))
          (q (fn2-pool-reserve 0 9 0 1 (mv-nth 6 checked))))
     (mv-nth 0 (fn2-ribbon-call-with-state fn2-rba-probes
                   (queries (mv-nth 1 q) (mv-nth 2 q) 0 (mv-nth 1 (fn2-ribbon-first-reservation)) (mv-nth 2 (fn2-ribbon-first-reservation))) checked (6 (mv-nth 3 q)))))
          (fn2-ribbon-final-answers keys queries))
   :hints (("Goal" :use fn2-ribbon-initial-page-and-key-arenas :in-theory (union-theories '(fn2-ribbon-final-answers) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-car-as-status
   (equal (car x) (mv-nth 0 x))
   :hints (("Goal" :in-theory (enable mv-nth)))))

(local
 (defthm fn2-ribbon-first-start-result
   (implies (and (posp n) (<= n 256)) (equal (car (fn2-ribbon-started-build n)) :ok))
   :hints (("Goal" :use fn2-ribbon-fresh-build-clears
            :in-theory (union-theories '(fn2-ribbon-car-as-status) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-adapter-success-status
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
            (and (equal (car (fn2-ribbon-ready-state (len keys))) :ready)
                 (equal (car (fn2-ribbon-added-state keys)) :ok)
                 (equal (car (fn2-ribbon-finish 0 (mv-nth 1 (fn2-ribbon-added-state keys)))) :ok)))
   :hints (("Goal" :use fn2-ribbon-initial-success-codes
            :in-theory (union-theories '(fn2-ribbon-car-as-status) (theory 'minimal-theory))))))

(defthm fn2-ribbon-image-reaches-final-drive
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
            (equal (fn2-ribbon-image keys nil queries nil)
                   (list (mv-nth 0 (fn2-ribbon-final-drive keys)) (mv-nth 0 (fn2-ribbon-final-check keys))
                         (fn2-ribbon-final-answers keys queries))))
   :hints (("Goal" :do-not '(preprocess) :in-theory (union-theories
                      '(fn2-ribbon-image-run-result fn2-rba-run fn2-rba-check-and-probe fn2-ribbon-drop fn2-ribbon-setup-fold
                        fn2-ribbon-prelude-initial-columns fn2-ribbon-real-open-success
                        fn2-ribbon-initial-success-codes fn2-ribbon-started-build-fold fn2-ribbon-ready-state-fold
                        fn2-ribbon-added-state-fold fn2-ribbon-final-drive-fold fn2-ribbon-final-check-fold fn2-ribbon-final-answers-fold
                        fn2-ribbon-adapter-success-status fn2-ribbon-first-start-result (:t fn2-ribbon-ready-state) (:t fn2-ribbon-added-state) (:t fn2-ribbon-finish) (:t fn2-ribbon-final-drive) (:t fn2-ribbon-final-check) (:t fn2-ribbon-started-build) mv-nth-of-cons car-cons cdr-cons (:e natp) (:e equal) (:e not) (:e consp) (:e zp) (:e binary-+))
                      (theory 'minimal-theory))))
   :rule-classes nil)

(local
 (defmacro fn2-ribbon-reserved-slot ()
   '(mv-nth 1 (fn2-ribbon-first-reservation))))

(local
 (defmacro fn2-ribbon-reserved-generation ()
   '(mv-nth 2 (fn2-ribbon-first-reservation))))

(local
 (defthm fn2-ribbon-flipped-pool-at-reservation
   (let* ((slot (fn2-ribbon-reserved-slot)) (gen (fn2-ribbon-reserved-generation))
          (byte (mv-nth 1 (fn2-pool-read slot gen off 9 0 1 pool))))
     (equal (mv-nth 1 (fn2-pool-write slot gen off (logxor (nfix x) (nfix byte)) 9 0 1 pool))
            (fn2-ribbon-flipped-pool off x pool)))
   :hints (("Goal" :use fn2-ribbon-initial-page-and-key-arenas
            :in-theory (union-theories '(fn2-ribbon-flipped-pool) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-read-page-at-reservation
   (equal (fn2-run-read-bytes 65536 (fn2-ribbon-reserved-slot) (fn2-ribbon-reserved-generation)
                              0 9 0 1 pool)
          (fn2-ribbon-read-page pool))
   :hints (("Goal" :use fn2-ribbon-initial-page-and-key-arenas :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-ribbon-recheck-at-reservation
   (let ((st (fn2-ribbon-final-check keys)))
     (equal (fn2-ribbon-call-with-state fn2-rba-check
              ((fn2-ribbon-reserved-slot) (fn2-ribbon-reserved-generation)) st
              (6 (fn2-ribbon-flipped-pool off x (mv-nth 6 st))))
            (fn2-ribbon-rechecked-state keys off x)))
   :hints (("Goal" :use fn2-ribbon-initial-page-and-key-arenas
            :in-theory (union-theories '(fn2-ribbon-rechecked-state) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-check-and-probe-after-write
   (let ((st (fn2-ribbon-final-drive keys)))
     (equal (cadr (mv-nth 0 (fn2-ribbon-call-with-state fn2-rba-check-and-probe
                ((fn2-ribbon-reserved-slot) (fn2-ribbon-reserved-generation) sealed nil (cons off x)) st)))
            (mv-nth 0 (fn2-ribbon-rechecked-state keys off x))))
   :hints (("Goal" :in-theory (union-theories
                 '(fn2-rba-check-and-probe fn2-ribbon-final-check-fold fn2-ribbon-flipped-pool-at-reservation
                   fn2-ribbon-recheck-at-reservation mv-nth-of-cons car-cons cdr-cons (:e consp)
                   (:e zp) (:e equal) (:e binary-+) (:t fn2-ribbon-rechecked-state))
                 (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))))

(defthm fn2-ribbon-mutated-image-rechecks-page
  (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
           (equal (cadr (fn2-ribbon-image keys nil nil (cons off x)))
                  (mv-nth 0 (fn2-ribbon-rechecked-state keys off x))))
  :hints (("Goal" :do-not '(preprocess) :in-theory (union-theories
                      '(fn2-ribbon-image-run-result fn2-rba-run
                        fn2-ribbon-check-and-probe-after-write
                        fn2-ribbon-read-page-at-reservation (:t fn2-rba-check) (:t fn2-ribbon-rechecked-state) fn2-ribbon-drop fn2-ribbon-setup-fold
                        fn2-ribbon-prelude-initial-columns fn2-ribbon-real-open-success
                        fn2-ribbon-initial-success-codes fn2-ribbon-started-build-fold fn2-ribbon-ready-state-fold
                        fn2-ribbon-added-state-fold fn2-ribbon-final-drive-fold fn2-ribbon-final-check-fold fn2-ribbon-final-answers-fold
                        fn2-ribbon-adapter-success-status fn2-ribbon-first-start-result (:t fn2-ribbon-ready-state) (:t fn2-ribbon-added-state) (:t fn2-ribbon-finish) (:t fn2-rba-check-and-probe) (:t fn2-ribbon-final-drive) (:t fn2-ribbon-final-check) (:t fn2-ribbon-started-build) mv-nth-of-cons car-cons cdr-cons (:e natp) (:e equal) (:e not) (:e consp) (:e zp) (:e binary-+))
                      (theory 'minimal-theory)))
          ("Subgoal 2'" :use ((:instance fn2-ribbon-check-and-probe-after-write (sealed (car (fn2-ribbon-final-drive keys)))))
           :in-theory (union-theories '((:t fn2-ribbon-rechecked-state) (:t fn2-rba-check-and-probe)
                                        (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons)
                                      (theory 'minimal-theory))))
   :rule-classes nil)

(defthm fn2-ribbon-mutation-observes-checks
  (let* ((before (mv-nth 6 (fn2-ribbon-final-drive keys)))
         (checked (mv-nth 6 (fn2-ribbon-final-check keys)))
         (after (fn2-ribbon-flipped-pool off x checked)))
    (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
             (equal (fn2-ribbon-mutation-premise keys off x)
                    (fn2-ribbon-page-integrity-premise
                     (fn2-ribbon-read-page before) (fn2-ribbon-read-page after)))))
  :hints (("Goal" :do-not '(preprocess) :in-theory (union-theories
                      '(fn2-rba-mutation-pages fn2-ribbon-mutation-premise
                        fn2-ribbon-recheck-at-reservation fn2-ribbon-flipped-pool-at-reservation
                        fn2-ribbon-read-page-at-reservation (:t fn2-rba-check) (:t fn2-ribbon-rechecked-state) fn2-ribbon-drop fn2-ribbon-setup-fold
                        fn2-ribbon-prelude-initial-columns fn2-ribbon-real-open-success
                        fn2-ribbon-initial-success-codes fn2-ribbon-started-build-fold fn2-ribbon-ready-state-fold
                        fn2-ribbon-added-state-fold fn2-ribbon-final-drive-fold fn2-ribbon-final-check-fold fn2-ribbon-final-answers-fold
                        fn2-ribbon-adapter-success-status fn2-ribbon-first-start-result (:t fn2-ribbon-ready-state) (:t fn2-ribbon-added-state) (:t fn2-ribbon-finish) (:t fn2-ribbon-final-drive) (:t fn2-ribbon-final-check) (:t fn2-ribbon-started-build) mv-nth-of-cons car-cons cdr-cons (:e natp) (:e equal) (:e not) (:e consp) (:e zp) (:e binary-+))
                      (theory 'minimal-theory))))
   :rule-classes nil)
