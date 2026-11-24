; The checker returns the digest of the domain-prefixed physical page.
(in-package "ACL2")
(include-book "format-page-hash-run-proof")
(local (include-book "format-binds-seal-proof"))
(local (in-theory (current-theory 'fc-u32-reconstruct)))

(defun-nx fn2-page-hash-answer (bytes)
  (fn2-b3-output-words (fn-b3-node *fn-b3-iv* (fn2-fc-covered :page bytes nil) 0 0) t))

(defthmd fn2-page-covered-shape
  (implies (fn-b3-octet-listp bytes)
           (and (fn-b3-octet-listp (fn2-fc-covered :page bytes nil))
                (equal (len (fn2-fc-covered :page bytes nil)) (+ 20 (len bytes)))))
  :hints (("Goal" :in-theory (enable fn2-page-covered-bytes fn-b3-octet-listp fn2-fc-domain))))

(defthmd fn2-page-hash-answer-octets
  (implies (fn-b3-octet-listp bytes)
           (equal (fn-b3-words-octets (fn2-page-hash-answer bytes))
                  (fn-blake3 (fn2-fc-covered :page bytes nil))))
  :hints (("Goal" :in-theory (enable fn2-page-hash-answer fc-blake3-is-answer-octets
                                    fn2-page-covered-shape fn-b3-fix-octets))))

(defthmd fn2-page-decoded-starts-hashing
  (let ((r (fn2-fc-decoded 0 :page 0 65536 0 next fc ctx b3 f pool ds)))
    (implies (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)
                  (fn2-page-hash-statep bytes ans fc ds b3))
             (and (not (eq (car r) :ok))
                  (implies (member-eq (car r) '(:more :yield))
                           (fn2-page-hash-statep bytes ans (mv-nth 1 r) ds b3)))))
  :hints (("Goal" :in-theory (e/d (fn2-fc-decoded fn2-page-hash-statep fn2-page-covered-bytes
                                   fc-phase-pos-updates fc-identity-never-more fc-decoded-never-yields)
                                  (fn2-fc-identity fn2-fc-pos fn2-fc-phase fn2-fields-value
                                   fn2-fc-set-pos fn2-fc-set-phase fn2-fc-set-zero fn2-fc-set-geom
                                   fn2-fc-set-previous-seal-offset fn2-fc-set-pad fn2-fc-set-pad-end
                                   fc-g fn2-fc-string-bytes mv-nth)))))

(defmacro fn2-page-driver-call (op)
  (case op
    (fn2-format-run '(fn2-format-run :page nil 0 0 1 0 65536 0 9 0 1 4096 fc ctx b3 f pool ds))
    (fn2-format-drive '(fn2-format-drive fuel 0 :page nil 0 1 0 65536 0 9 0 1 4096 fc ctx b3 f pool ds))
    (otherwise '(fn2-fc-step 0 :page nil 0 1 0 65536 0 9 0 1 4096 fc ctx b3 f pool ds))))

(defthmd fn2-page-started-hash-state
  (equal (fn2-page-hash-statep bytes ans (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc) ds b3)
         (fc-g (fn2-fc-covered :page bytes nil) ans ds b3))
  :hints (("Goal" :in-theory (enable fn2-page-hash-statep fc-phase-pos-updates))))

(defthmd fn2-page-reset-hash-state
  (fn2-page-hash-statep bytes ans (fn2-fc-reset 0 fc) ds b3)
  :hints (("Goal" :in-theory (enable fn2-page-hash-statep fn2-fc-reset fc-phase-pos-updates))))

(defthm fn2-page-step-hashes-input
  (let ((ans (fn2-page-hash-answer bytes)))
    (fn2-page-hash-effect (fn2-page-driver-call fn2-fc-step) 1 2 5))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-page-hash-run (fuel 4096) (ans (fn2-page-hash-answer bytes)))
                 (:instance fn2-page-decoded-starts-hashing (ans (fn2-page-hash-answer bytes))
                            (next (mv-nth 1 (fn2-fc-decode-step :page 0 0 1 0 65536 9 0 1 4096 f pool)))
                            (f (mv-nth 2 (fn2-fc-decode-step :page 0 0 1 0 65536 9 0 1 4096 f pool))))
                 (:instance fc-g-init (xs (fn2-fc-covered :page bytes nil)))
                 fn2-page-covered-shape)
           :in-theory (e/d (fn2-fc-step fn2-page-started-hash-state fn2-page-hash-answer fc-mv-zero fc-mv-cons fc-b3-init-key fc-phase-pos-updates)
                           (fn2-fc-phase fn2-fc-pos fn2-b3-init fn2-fc-run-bytes
                            fn2-layout-range-code fn2-fc-decode-step fn2-fc-decoded fn2-page-hash-statep
                            fn2-fc-covered fn2-b3-output-words fn-b3-node fn-b3-octet-listp
                            fn2-hash-page-windowp fn2-b3-covers mv-nth)))))

(defthm fn2-page-format-hashes-input
  (let ((ans (fn2-page-hash-answer bytes)))
    (fn2-page-hash-effect (fn2-page-driver-call fn2-format-run) 1 2 5))
  :rule-classes nil
  :hints (("Goal" :use fn2-page-step-hashes-input
           :in-theory (e/d (fn2-format-run fn2-page-reset-hash-state fc-mv-zero fc-mv-cons)
                           (fn2-fc-step fn2-page-hash-statep fn2-page-hash-answer
                            fn2-fc-reset fn2-b3-covers fn2-hash-page-windowp mv-nth)))))

(defthm fn2-page-drive-hashes-checked-input
  (let ((r (fn2-page-driver-call fn2-format-drive)))
    (implies (and (fn2-page-hash-statep bytes (fn2-page-hash-answer bytes) fc ds b3)
                  (fn2-hash-page-windowp pool) (fn-b3-octet-listp bytes)
                  (equal (len bytes) 65536) (fn2-b3-covers bytes 0 pool) (eq (car r) :ok))
             (equal (fn-b3-words-octets (fn2-digest-list 125 (mv-nth 5 r)))
                    (fn-blake3 (fn2-fc-covered :page bytes nil)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-page-driver-call fn2-format-drive)
           :expand (fn2-page-driver-call fn2-format-drive)
           :in-theory (e/d ((:induction fn2-format-drive) fc-format-keeps-pool fn2-page-hash-answer-octets
                            fc-mv-zero fc-mv-cons)
                           (fn2-format-run fn2-page-hash-answer fn2-page-hash-statep fn-blake3
                            fn-b3-words-octets fn2-fc-covered fn2-b3-covers fn2-hash-page-windowp mv-nth)))
          ("Subgoal *1/3" :use fn2-page-format-hashes-input)
          ("Subgoal *1/2" :use fn2-page-format-hashes-input)))
