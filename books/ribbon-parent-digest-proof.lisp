; Checking a physical page leaves the digest supplied by its parent in place.
(in-package "ACL2")
(local (include-book "ribbon-false-neg-hash-proof"))
(include-book "format-page-parent-check-proof")
(local (in-theory (current-theory 'fc-u32-reconstruct)))

(defmacro fn2-ribbon-parent-frame (name call index enabled &key induct)
  `(defthmd ,name
     (equal (fn2-digest-list 136 (mv-nth ,index ,call)) (fn2-digest-list 136 ds))
     :hints (("Goal" ,@(and induct (list :induct call :expand call))
              :in-theory (union-theories
                          (set-difference-theories (theory 'minimal-theory) '(mv-nth))
                          '(,@enabled fc-mv-zero fc-mv-cons car-cons cdr-cons
                            (:e mv-nth) (:e fn2-digest-slot) (:e binary-+) (:e <)
                            (:e equal) (:e member-equal) (:e eq) (:e eql) (:e zp) (:e not)))))))

(local
 (defthm fn2-page-byte-parent-row
   (equal (fn2-digest-list 136 (car (fn2-b3-byte 0 byte fn2-digests fn2-b3)))
          (fn2-digest-list 136 fn2-digests))
   :hints (("Goal" :use fn2-ribbon-byte-preserves-parent-digest
            :in-theory (union-theories (theory 'minimal-theory) '(fc-mv-zero))))))

(local
 (defthm fn2-page-init-parent-row
   (equal (fn2-digest-list 136 (car (fn2-b3-init 0 0 1 fn2-digests fn2-b3)))
          (fn2-digest-list 136 fn2-digests))
   :hints (("Goal" :use fn2-ribbon-init-preserves-parent-digest
            :in-theory (union-theories (theory 'minimal-theory) '(fc-mv-zero))))))

(fn2-ribbon-parent-frame fn2-page-byte-retains-parent
  (fn2-page-check-call fn2-fc-byte) 4
  (fn2-fc-byte fn2-page-byte-parent-row fn2-ribbon-finalize-preserves-parent-digest))

(fn2-ribbon-parent-frame fn2-page-span-retains-parent
  (fn2-page-hash-span-call) 4
  (fn2-fc-page-span fn2-ribbon-page-update-preserves-parent-digest))

(fn2-ribbon-parent-frame fn2-page-advance-retains-parent
  (fn2-page-check-call fn2-fc-advance fuel) 5
  (fn2-fc-advance fn2-page-byte-retains-parent fn2-page-span-retains-parent))

(fn2-ribbon-parent-frame fn2-page-run-retains-parent
  (fn2-page-check-call fn2-fc-run-bytes fuel) 4
  ((:induction fn2-fc-run-bytes) fn2-page-advance-retains-parent) :induct t)

(fn2-ribbon-parent-frame fn2-page-step-retains-parent
  (fn2-page-driver-call fn2-fc-step) 5
  (fn2-fc-step fn2-page-run-retains-parent fn2-page-init-parent-row))

(fn2-ribbon-parent-frame fn2-page-format-retains-parent
  (fn2-page-driver-call fn2-format-run) 5
  (fn2-format-run fn2-page-step-retains-parent))

(fn2-ribbon-parent-frame fn2-page-drive-retains-parent
  (fn2-page-driver-call fn2-format-drive) 5
  ((:induction fn2-format-drive) fn2-page-format-retains-parent) :induct t)
