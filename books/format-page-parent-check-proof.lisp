; At acceptance every result byte agrees with the parent-held digest.
(in-package "ACL2")
(include-book "format-page-hash-drive-proof")
(local (include-book "format-binds-trailer-proof"))
(local (in-theory (current-theory 'fc-u32-reconstruct)))

(defun-nx fn2-page-parent-byte (k ctx ds)
  (fn2-fc-word-byte (fn2-fc-context-hash-word 0 (floor k 4) ctx ds) (mod k 4)))

(defun-nx fn2-page-parent-matchp (k ctx ds)
  (equal (fn2-fc-digest-byte 0 k nil ds) (fn2-page-parent-byte k ctx ds)))

(defun-nx fn2-page-parent-progressp (k fc ctx ds)
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-digest*)
           (let ((pos (fn2-fc-pos 0 fc)))
             (and (natp pos) (or (<= pos k) (fn2-page-parent-matchp k ctx ds))))))

(defmacro fn2-page-parent-effect (call fi di)
  `(let ((r ,call))
     (implies (and (natp k) (< k 32) (fn2-page-parent-progressp k fc ctx ds))
              (and (implies (member-eq (car r) '(:more :yield))
                            (fn2-page-parent-progressp k (mv-nth ,fi r) ctx (mv-nth ,di r)))
                   (implies (equal (car r) :ok) (fn2-page-parent-matchp k ctx (mv-nth ,di r)))))))

(defthm fn2-page-byte-checks-parent
  (fn2-page-parent-effect (fn2-page-check-call fn2-fc-byte) 1 4)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-fc-byte fn2-page-parent-progressp fn2-page-parent-matchp
                            fn2-page-parent-byte fn2-fc-digest-byte fc-pending-after-increment
                            fc-phase-pos-updates fc-mv-zero fc-mv-cons)
                           (mv-nth fn2-fc-phase fn2-fc-pos fn2-fc-set-phase fn2-fc-set-pos
                            fn2-fc-word-byte fn2-digest-word fn2-fc-context-hash-word
                            fn2-fc-prefix-byte fn2-b3-byte fn2-fc-check-byte fn2-b3-finalize fn2-b3-read floor mod)))))

(defthmd fn2-page-outside-digest
  (implies (not (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-digest*))
           (fn2-page-parent-progressp k fc ctx ds))
  :hints (("Goal" :in-theory (enable fn2-page-parent-progressp))))

(defthm fn2-page-advance-checks-parent
  (fn2-page-parent-effect (fn2-page-check-call fn2-fc-advance fuel) 2 5)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :cases ((equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*))
           :use (fn2-page-span-frames fn2-page-byte-checks-parent
                 (:instance fn2-page-byte-checks-parent (fc (mv-nth 2 (fn2-page-hash-span-call)))
                            (b3 (mv-nth 3 (fn2-page-hash-span-call))) (ds (mv-nth 4 (fn2-page-hash-span-call)))))
           :in-theory (e/d (fn2-fc-advance fn2-page-outside-digest fc-mv-zero fc-mv-cons)
                           (fn2-page-span-frames fn2-fc-phase fn2-fc-byte fn2-fc-page-span fn2-page-parent-progressp
                            fn2-page-parent-matchp mv-nth)))))

(defthm fn2-page-run-checks-parent
  (fn2-page-parent-effect (fn2-page-check-call fn2-fc-run-bytes fuel) 1 4)
  :rule-classes nil
  :hints (("Goal" :induct (fn2-page-check-call fn2-fc-run-bytes fuel)
           :expand (fn2-page-check-call fn2-fc-run-bytes fuel)
           :in-theory (e/d ((:induction fn2-fc-run-bytes) fc-mv-zero fc-mv-cons)
                           (fn2-fc-advance fn2-page-parent-progressp fn2-page-parent-matchp mv-nth)))
          ("Subgoal *1/3" :use fn2-page-advance-checks-parent)
          ("Subgoal *1/2" :use fn2-page-advance-checks-parent)))

(local
 (defthm fn2-page-decoding-parent-progress
   (let ((r (fn2-fc-decoded 0 :page 0 65536 0 next fc ctx b3 f pool ds)))
     (and (not (equal (car r) :ok))
          (implies (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)
                        (member-eq (car r) '(:more :yield)))
                   (fn2-page-parent-progressp k (mv-nth 1 r) ctx ds))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-decoded fn2-page-outside-digest fc-phase-pos-updates)
                                   (fn2-fc-phase fn2-fc-identity fn2-fields-value fn2-fc-set-phase
                                    fn2-page-parent-progressp mv-nth))))))

(defthm fn2-page-checks-parent-on-step
  (fn2-page-parent-effect (fn2-page-driver-call fn2-fc-step) 1 5)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-page-run-checks-parent (fuel 4096))
                 (:instance fn2-page-decoding-parent-progress
                            (next (mv-nth 1 (fn2-fc-decode-step :page 0 0 1 0 65536 9 0 1 4096 f pool)))
                            (f (mv-nth 2 (fn2-fc-decode-step :page 0 0 1 0 65536 9 0 1 4096 f pool)))))
           :in-theory (e/d (fn2-fc-step fc-phase-pos-updates fn2-page-outside-digest fc-mv-zero fc-mv-cons)
                           (fn2-page-decoding-parent-progress fn2-fc-phase fn2-b3-init fn2-fc-set-phase
                            fn2-fc-decoded fn2-fc-decode-step fn2-fc-run-bytes fn2-layout-range-code
                            fn2-page-parent-progressp fn2-page-parent-matchp mv-nth)))))

(defthm fn2-page-format-checks-parent
  (fn2-page-parent-effect (fn2-page-driver-call fn2-format-run) 1 5)
  :rule-classes nil
  :hints (("Goal" :use fn2-page-checks-parent-on-step
           :in-theory (e/d (fn2-format-run fn2-fc-reset fn2-page-outside-digest fc-phase-pos-updates
                            fc-mv-zero fc-mv-cons)
                           (fn2-fc-phase fn2-fc-step fn2-page-parent-progressp fn2-page-parent-matchp mv-nth)))))

(defthm fn2-page-drive-checks-every-parent-byte
  (let ((r (fn2-page-driver-call fn2-format-drive)))
    (implies (and (natp k) (< k 32) (fn2-page-parent-progressp k fc ctx ds) (eq (car r) :ok))
             (fn2-page-parent-matchp k ctx (mv-nth 5 r))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-page-driver-call fn2-format-drive)
           :expand (fn2-page-driver-call fn2-format-drive)
           :in-theory (e/d ((:induction fn2-format-drive) fc-mv-zero fc-mv-cons)
                           (fn2-format-run fn2-page-parent-progressp fn2-page-parent-matchp mv-nth)))
          ("Subgoal *1/3" :use fn2-page-format-checks-parent)
          ("Subgoal *1/2" :use fn2-page-format-checks-parent)))
