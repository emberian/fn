; Proof/caller phase carry, never executed by a served scalar step.
(in-package "ACL2")
(include-book "index-range-held-row-controller")
; Proof/caller carry only. The scalar callback never evaluates this predicate.
(defun fn-ibr-held-executing-phase-p (control)
 (declare (xargs :guard t))
 (let ((cell (fn-spp-at 4 (fn-spp-at 8 control))))
  (or (not (equal (fn-spp-at 3 control) :held))
      (equal (fn-hmid-at 4 cell) :msgid)
      (and (equal (fn-hmid-at 4 cell) :row)
           (member-eq (fn-hmid-at 2 (fn-hmid-at 5 cell)) '(:parse :emit))))))
(defthm fn-ibr-selected-held-install-establishes-executing-phase
 (fn-ibr-held-executing-phase-p
   (mv-nth 1 (fn-ibr-selected-held-row-install control held fn-arena)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-ibr-held-executing-phase-p fn-ibr-selected-held-row-install
        fn-ibr-restate fn-ibr-make fn-ibr-work fn-spp-at fn-hmid-at
        fn-ag-car fn-ag-cdr fn-osh-begin fn-osh-make)
       (fn-ibr-held-visible-p fn-gns-number-result fn-gns-number-begin
        fn-obc-next-range fn-hmid-begin fn-spp-origin fn-ipub-count fn-ipub-view)))))


(encapsulate ()
 (local (defthm fn-ibr-phase-hmid-at-is-nth
  (equal (fn-hmid-at i x) (nth (nfix i) x))
  :hints (("Goal" :in-theory (enable fn-hmid-at fn-ag-car fn-ag-cdr nth)))))
 (local (defthm fn-ibr-phase-spp-at-is-nth
  (equal (fn-spp-at i x) (nth (nfix i) x))
  :hints (("Goal" :in-theory (enable fn-spp-at fn-ag-car fn-ag-cdr nth)))))
(defthm fn-ibr-held-one-establishes-executing-phase
 (implies (fn-ibr-held-current-ready-p control fn-arena)
  (let ((r (fn-ibr-held-one control fn-arena)))
   (implies (eq (mv-nth 1 r) :held)
            (fn-ibr-held-executing-phase-p (mv-nth 2 r)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-osh-one-preserves-held-row-carry
         (cell (fn-spp-at 4 (fn-spp-at 8 control)))))
  :in-theory
   (e/d (fn-ibr-held-executing-phase-p fn-ibr-held-current-ready-p
         fn-ibr-held-one fn-ibr-restate fn-ibr-make fn-ibr-work
         fn-ag-car fn-ag-cdr
         fn-osh-ready-p fn-ohr-carried-p)
        (fn-spp-at fn-hmid-at fn-osh-one fn-osh-selected-source-p fn-hmid-ready-p fn-hnov-p
         fn-lpc-ready-p fn-lpc-cursor-bounds-p fn-npw-piecesp
         fn-gns-number-begin fn-gns-group-selected-result fn-ipub-count)))))

)
