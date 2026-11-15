; Source-only proof leaves; ACL2 admission is unexecuted.
; The actual hash arm cannot report scanner EOF. Therefore :done retains
; the exact MK/B3/digest carriers, rather than assuming a disjoint write model.
(in-package "ACL2")
(include-book "../books/event-frontier")
(include-book "merkle-scanner-result-proof")
(defthm fn2-event-member-hash-step-never-scanner-done
 (not (equal (mv-nth 0 (fn2-event-member-hash-step row leaf fn2-journal-members
                       fn2-mk fn2-b3 fn2-digests fn2-pool)) :done))
 :hints (("Goal" :in-theory (enable fn2-event-member-hash-step))))
(defthm fn2-event-members-done-frames-hash-carriers
 (implies
  (equal (mv-nth 0 (fn2-event-members-step base row leaf fn2-journal-members
                    fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)) :done)
  (and
   (equal (mv-nth 2 (fn2-event-members-step base row leaf fn2-journal-members
                     fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-mk)
   (equal (mv-nth 3 (fn2-event-members-step base row leaf fn2-journal-members
                     fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-b3)
   (equal (mv-nth 5 (fn2-event-members-step base row leaf fn2-journal-members
                     fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-digests)))
 :hints (("Goal" :in-theory (enable fn2-event-members-step))))
