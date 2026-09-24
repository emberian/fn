(in-package "ACL2")
(include-book "../../books/checkpoint-pack-retire")
(include-book "std/testing/must-fail" :dir :system)

; Three generations, with 1 selected.  Retiring old 0 never changes selected
; 1 or a newer unselected candidate 2, regardless of whether the unlink is
; observed after a process death.
(assert-event (equal (fn-cprt-retire-plan '(0 1 2) 1) '(0)))
(assert-event (equal (fn-cprt-retire-program '(0 1 2) 1)
                     '((:unlink :packs 0)
                       (:cut "pack-retire-unlink")
                       (:fsync-dir :packs)
                       (:cut "pack-retire-directory"))))
; The native caller returns before a directory barrier when the plan is empty.
(assert-event (equal (fn-cprt-retire-plan '(1 2) 1) nil))
(assert-event (equal (fn-cprt-retire-program '(1 2) 1) nil))
(assert-event (equal (fn-cprt-crash-survivors '(0 1 2) '(0) nil)
                     '(1 2)))
(assert-event (equal (fn-cprt-crash-survivors '(0 1 2) '(0) '(0))
                     '(0 1 2)))
(assert-event
 (and (< (len (fn-cprt-crash-survivors '(0 1 2) '(0 1) nil))
         (len '(0 1 2)))
      (equal (fn-cprt-crash-survivors '(0 1 2) '(0 1) nil) '(2))))
; No slot is freed if the named generation was absent, never attempted, or
; survived an interrupted directory publication.
(assert-event
 (and (equal (len (fn-cprt-crash-survivors '(0 1) '(2) nil)) 2)
      (equal (len (fn-cprt-crash-survivors '(0 1) nil nil)) 2)
      (equal (len (fn-cprt-crash-survivors '(0 1) '(0) '(0))) 2)))
(local
 (must-fail
  (defthm fn-cprt-slot-without-generation-membership
    (implies (and (member-equal generation issued)
                  (not (member-equal generation retained)))
             (< (len (fn-cprt-crash-survivors generations issued retained))
                (len generations))))))
(local
 (must-fail
  (defthm fn-cprt-slot-without-issued-attempt
    (implies (and (member-equal generation generations)
                  (not (member-equal generation retained)))
             (< (len (fn-cprt-crash-survivors generations issued retained))
                (len generations))))))
(local
 (must-fail
  (defthm fn-cprt-slot-without-unretained-image
    (implies (and (member-equal generation generations)
                  (member-equal generation issued))
             (< (len (fn-cprt-crash-survivors generations issued retained))
                (len generations))))))
(assert-event (equal (fn-cprt-next-generation '(1 2)) 3))
(assert-event (equal (fn-cprt-publication-initial '(1 2) 3 t t)
                     (list :ok 3 (fn-jpub-initial t))))
(assert-event (equal (fn-cprt-publication-initial '(1 2) 2 t t)
                     '(:error :generation)))
(assert-event (equal (fn-cprt-publication-initial '(1 2) 3 nil t)
                     '(:error :authority)))
(assert-event (equal (fn-cprt-publication-initial '(1 2) 3 t nil)
                     '(:error :occupied)))
(assert-event (equal (fn-cprt-publication-initial '(2 1) 3 t t)
                     '(:error :namespace)))
(assert-event (equal (fn-cprt-publication-initial '(4095) 4096 t t)
                     '(:error :exhausted)))
(assert-event (equal (fn-cprt-next-generation nil) 0))
(assert-event (equal (fn-cprt-next-generation '(0 2 2)) :invalid))
(assert-event (equal (fn-cprt-retire-plan '(0 2) 1) :invalid))
(assert-event (equal (fn-cprt-retire-plan '(1 0) 1) :invalid))

; The selected-generation membership and issued-prefix premises both carry
; the result: without membership 1 is absent, and without the prefix rule a
; hostile caller could issue deletion of the selected generation itself.
(assert-event
 (and (fn-cprt-prefixp nil (fn-cprt-retire-plan '(0 2) 1))
      (not (member-equal 1 (fn-cprt-crash-survivors '(0 2) nil nil)))))
(assert-event
 (and (member-equal 1 '(0 1 2))
      (not (fn-cprt-prefixp '(1) (fn-cprt-retire-plan '(0 1 2) 1)))
      (not (member-equal 1
                         (fn-cprt-crash-survivors '(0 1 2) '(1) nil)))))
(local
 (must-fail
  (defthm fn-cprt-selected-survives-without-membership
    (let ((plan (fn-cprt-retire-plan generations selected)))
      (implies (fn-cprt-prefixp issued plan)
               (member-equal selected
                             (fn-cprt-crash-survivors generations issued retained)))))))
(local
 (must-fail
  (defthm fn-cprt-selected-survives-without-issued-prefix
    (implies (member-equal selected generations)
             (member-equal selected
                           (fn-cprt-crash-survivors generations issued retained))))))

; The selected pack remains present at the closing directory fence; a later
; publication advances above the retained maximum instead of reusing a
; physically retired generation name.
(assert-event
 (and (member-equal 1 (fn-cprt-crash-survivors '(0 1 2) '(0) nil))
      (equal (fn-cprt-next-generation '(1 2)) 3)))

; The allocator theorem needs a well-formed increasing namespace, a selected
; member, and remaining finite generation capacity.  Each omitted premise has
; a concrete counterexample (the malformed case yields :invalid).
(assert-event
 (and (member-equal 2 '(2 1))
      (equal (fn-cprt-next-generation '(2 1)) :invalid)))
(assert-event
 (and (fn-cprt-generationsp '(0 1))
      (not (< 3 (fn-cprt-next-generation '(0 1))))))
(assert-event
 (and (fn-cprt-generationsp '(4095))
      (equal (fn-cprt-next-generation '(4095)) :exhausted)))
(local
 (must-fail
  (defthm fn-cprt-next-without-valid-namespace
    (implies (and (member-equal selected generations)
                  (not (equal (fn-cprt-next-generation generations) :exhausted)))
             (< selected (fn-cprt-next-generation generations))))))
(local
 (must-fail
  (defthm fn-cprt-next-without-selected-member
    (implies (and (fn-cprt-generationsp generations)
                  (not (equal (fn-cprt-next-generation generations) :exhausted)))
             (< selected (fn-cprt-next-generation generations))))))
(local
 (must-fail
  (defthm fn-cprt-next-without-capacity
    (implies (and (fn-cprt-generationsp generations)
                  (member-equal selected generations))
             (< selected (fn-cprt-next-generation generations))))))
