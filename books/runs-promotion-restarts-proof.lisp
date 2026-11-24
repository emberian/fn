; On a successful promotion the only restart-table write is the parent's
; note at its old cursor. All earlier offsets remain in order.
(in-package "ACL2")
(include-book "runs-builder-page-contents-proof")

(local
 (defthm fn2-run-successful-add-keeps-noted-offsets
   (let ((add (fn2-run-add w sid base writers restarts f pool)))
     (implies (equal (car add) :ok)
              (equal (mv-nth 2 add) (mv-nth 2 (fn2-run-note-restart w writers restarts)))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-run-add fn2-run-add-write eq eql mv-nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e mv-nth)))))))

(local
 (defthm fn2-run-promotion-check-never-reports-append
   (not (equal (car (fn2-run-promote-check b l builds writers)) :ok))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                           '(fn2-run-promote-check car-cons (:e equal)))))))

(local
 (defthm fn2-run-promotion-commit-requires-append
   (implies (equal (car (fn2-run-promote-commit w code writers)) :ok)
            (equal code :ok))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                           '(fn2-run-promote-commit fn2-run-close-full eq eql car-cons cdr-cons (:e equal)))))))

(defthmd fn2-run-promoted-restarts-are-noted-by-parent
  (let ((promote (fn2-run-build-promote b l builds writers restarts f pool ds))
        (w (1+ (+ (nfix (fn2-run-builds-wbase b builds)) (nfix l)))))
    (implies (equal (car promote) :ok)
             (equal (mv-nth 3 promote) (mv-nth 2 (fn2-run-note-restart w writers restarts)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-run-build-promote fn2-run-promotion-check-never-reports-append
                       fn2-run-promotion-commit-requires-append fn2-run-successful-add-keeps-noted-offsets
                       eq eql mv-nth car-cons cdr-cons commutativity-of-+ (:e equal) (:e zp) (:e binary-+) (:e mv-nth))))))

(defthmd fn2-run-promoted-parent-keeps-restart-list
  (let* ((w (1+ level)) (nr (fn2-run-writers-restarts w writers)) (idx (fn2-run-writers-entries w writers))
         (at (* w *fn2-run-restart-capacity*)) (restartp (equal (mod idx *fn2-run-restart-interval*) 0))
         (newnr (if restartp (1+ nr) nr)) (promote (fn2-run-build-promote 0 level builds writers restarts f pool ds)))
    (implies (and (natp level) (equal (fn2-run-builds-wbase 0 builds) 0) (natp nr) (< nr *fn2-run-restart-capacity*)
                  (< (+ at nr) (fn2-run-restarts-rows restarts)) (equal (car promote) :ok))
             (equal (fn2-run-saved-offsets newnr at (mv-nth 3 promote))
                    (append (fn2-run-saved-offsets nr at restarts)
                            (if restartp (list (fn2-run-writers-cursor w writers)) nil)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-promoted-restarts-are-noted-by-parent (b 0) (l level))
                 (:instance fn2-run-note-extends-restart-list (w (1+ level))))
           :in-theory (disable fn2-run-build-promote fn2-run-builds-wbase fn2-run-saved-offsets fn2-run-note-restart
                     fn2-run-writers-cursor fn2-run-writers-restarts fn2-run-writers-entries fn2-run-restarts-rows mod binary-append))))
