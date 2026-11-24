; Appending a reference changes the parent writer only. Committing a
; promotion consumes its sealed child on success and keeps it on overflow.
(in-package "ACL2")
(include-book "runs-served")

(local
 (defthm fn2-run-noting-restart-keeps-ordinal
   (let ((after (mv-nth 1 (fn2-run-note-restart w writers restarts))))
     (and (equal (fn2-run-writers-ordinal j after) (fn2-run-writers-ordinal j writers))
          (equal (fn2-run-writers-rows after) (fn2-run-writers-rows writers))))
   :hints (("Goal" :in-theory (e/d (fn2-run-note-restart fn2-run-writers-ordinal fn2-run-writers-rows
                                    fn2-run-writers-set-restarts update-fn2-run-writers-restarts$ai nth-update-nth)
                              (fn2-run-writers-entries fn2-run-writers-restarts fn2-run-restarts-rows
                               fn2-run-writers-cursor fn2-run-restarts-set-offset mod nth update-nth))))))

(local
 (defthm fn2-run-commit-keeps-ordinal
   (let ((after (mv-nth 1 (fn2-run-add-commit w code end writers))))
     (and (equal (fn2-run-writers-ordinal j after) (fn2-run-writers-ordinal j writers))
          (equal (fn2-run-writers-rows after) (fn2-run-writers-rows writers))))
   :hints (("Goal" :in-theory (e/d (fn2-run-add-commit fn2-run-writers-ordinal fn2-run-writers-rows
                                    fn2-run-writers-set-prev fn2-run-writers-set-entries fn2-run-writers-set-cursor
                                    fn2-run-writers-set-phase update-fn2-run-writers-prev$ai
                                    update-fn2-run-writers-entries$ai update-fn2-run-writers-cursor$ai
                                    update-fn2-run-writers-phase$ai nth-update-nth)
                             (fn2-run-writers-entries nth update-nth unsigned-byte-p))))))

(defthmd fn2-run-parent-append-keeps-writer-ordinals
  (let ((after (mv-nth 1 (fn2-run-add w sid base writers restarts f pool))))
    (and (equal (fn2-run-writers-ordinal j after) (fn2-run-writers-ordinal j writers))
         (equal (fn2-run-writers-rows after) (fn2-run-writers-rows writers))))
  :hints (("Goal" :in-theory (e/d (fn2-run-add fn2-run-add-write)
                               (fn2-run-add-ready fn2-run-add-check fn2-run-writers-fields fn2-fields-rows
                                fn2-run-writers-ordinal fn2-run-writers-rows fn2-run-layout-encode fn2-run-layout-decode
                                fn2-run-note-restart fn2-run-add-commit fn2-run-writers-okind fn2-run-writers-oslot
                                fn2-run-writers-ogen fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-cursor
                                fn2-run-writers-level nfix)))))

(defthmd fn2-run-promotion-releases-appended-child
  (let* ((parent (1+ level)) (ordinal (1+ (fn2-run-writers-ordinal level writers)))
         (commit (fn2-run-promote-commit level :ok writers)) (after (mv-nth 1 commit)))
    (implies (and (natp level) (< parent (fn2-run-writers-rows writers)) (unsigned-byte-p 60 ordinal))
             (and (equal (car commit) :ok) (equal (fn2-run-writers-phase level after) *fn2-run-writer-phase-idle*)
                  (equal (fn2-run-writers-ordinal level after) ordinal)
                  (equal (fn2-run-writers-phase parent after) (fn2-run-writers-phase parent writers))
                  (equal (fn2-run-writers-entries parent after) (fn2-run-writers-entries parent writers))
                  (equal (fn2-run-writers-cursor parent after) (fn2-run-writers-cursor parent writers))
                  (equal (fn2-run-writers-restarts parent after) (fn2-run-writers-restarts parent writers)))))
  :hints (("Goal" :in-theory (e/d (fn2-run-promote-commit fn2-run-writers-phase fn2-run-writers-ordinal fn2-run-writers-entries
                                    fn2-run-writers-cursor fn2-run-writers-restarts fn2-run-writers-set-phase
                                    fn2-run-writers-set-ordinal update-fn2-run-writers-phase$ai update-fn2-run-writers-ordinal$ai
                                    nth-update-nth)
                            (fn2-run-writers-rows nth update-nth unsigned-byte-p)))))

(defthmd fn2-run-promotion-keeps-child-on-full-parent
  (let* ((parent (1+ level)) (commit (fn2-run-promote-commit level :full writers)) (after (mv-nth 1 commit)))
    (implies (and (natp level) (< parent (fn2-run-writers-rows writers))
                  (posp (fn2-run-writers-entries parent writers)) (equal (fn2-run-writers-phase parent writers) *fn2-run-writer-phase-open*))
             (and (equal (car commit) :more)
                  (equal (fn2-run-writers-phase parent after) *fn2-run-writer-phase-closing*) (equal (fn2-run-writers-pos parent after) 0)
                  (equal (fn2-run-writers-entries parent after) (fn2-run-writers-entries parent writers))
                  (equal (fn2-run-writers-phase level after) (fn2-run-writers-phase level writers))
                  (equal (fn2-run-writers-ordinal level after) (fn2-run-writers-ordinal level writers))
                  (equal (fn2-run-writers-slot level after) (fn2-run-writers-slot level writers))
                  (equal (fn2-run-writers-gen level after) (fn2-run-writers-gen level writers)))))
  :hints (("Goal" :in-theory (e/d (fn2-run-promote-commit fn2-run-close-full fn2-run-close fn2-run-writers-phase
                                    fn2-run-writers-pos fn2-run-writers-entries fn2-run-writers-ordinal fn2-run-writers-slot fn2-run-writers-gen
                                    fn2-run-writers-set-phase fn2-run-writers-set-pos update-fn2-run-writers-pos$ai
                                    update-fn2-run-writers-phase$ai nth-update-nth)
                              (fn2-run-writers-rows nth update-nth unsigned-byte-p)))))
