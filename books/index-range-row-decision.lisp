; Internal SAME-controller visible-number decision; no NOV/payload renderer.
; Actual captured row/source publication authority remains separate.
(in-package "ACL2")
(include-book "index-range-held-row-controller")
(defun fn-ibr-decision-next-number (control)
 (declare (xargs :guard (true-listp (fn-spp-at 1 (fn-spp-at 8 control)))))
 (let* ((work (fn-spp-at 8 control)) (range (fn-spp-at 1 work))
        (publication (fn-spp-at 2 work)) (group (fn-spp-at 6 control))
        (next (fn-obc-next-range range (fn-spp-at 5 range))))
  (fn-ibr-restate control :number group
   (fn-gns-number-begin (fn-spp-at 1 next)
    (fn-spp-at 1 (fn-gns-group-selected-result group)) (fn-ipub-count publication))
   (fn-ibr-work next publication nil nil))))
(defun fn-ibr-row-decision-begin (control held fn-arena)
 (declare (ignorable fn-arena)
  (xargs :stobjs fn-arena
   :guard (fn-ibr-held-install-ready-p control held fn-arena)))
 (let* ((work (fn-spp-at 8 control)) (range (fn-spp-at 1 work))
        (publication (fn-spp-at 2 work))
        (ordinal (fn-spp-at 1 (fn-gns-number-result (fn-spp-at 7 control)))))
  (if (not (fn-ibr-held-visible-p ordinal (fn-ipub-count publication)
                                  (fn-ipub-view publication) held))
      (mv :skip (fn-ibr-decision-next-number control))
   (mv :decision
    (fn-ibr-restate control :decision (fn-spp-at 6 control) (fn-spp-at 7 control)
     (fn-ibr-work range publication (fn-spp-at 3 work)
      (fn-osh-begin range (fn-spp-origin (fn-spp-at 4 control)) held)))))))
(defun fn-ibr-row-decision-ready-p (control)
 (declare (xargs :guard t))
 (let* ((work (fn-spp-at 8 control)) (cell (fn-spp-at 4 work))
        (held (fn-hmid-at 3 cell)) (cursor (fn-hmid-at 5 cell))
        (publication (fn-spp-at 2 work))
        (ordinal (fn-spp-at 1 (fn-gns-number-result (fn-spp-at 7 control)))))
  (and (true-listp control)
       (true-listp (fn-spp-at 1 work)) (eq (fn-spp-at 3 control) :decision)
       (true-listp cell) (equal (len cell) 6)
       (eq (fn-hmid-at 0 cell) :selected-held-row)
       (eq (fn-hmid-at 4 cell) :msgid)
       (equal (fn-hmid-at 1 cell) (fn-spp-at 1 work))
       (natp ordinal) (natp (fn-ipub-count publication))
       (natp (fn-ipub-view publication))
       (fn-held-withdrawnp (fn-held-withdrawn held))
       (fn-ibr-held-visible-p ordinal (fn-ipub-count publication)
                                 (fn-ipub-view publication) held)
       (fn-hmid-ready-p cursor)
       (equal (fn-hmid-at 1 cursor)
              (if (stringp (fn-record-msgid held)) (fn-record-msgid held) "")))))
(defun fn-ibr-row-decision-one (control)
 (declare (xargs :guard (fn-ibr-row-decision-ready-p control)))
 (let* ((work (fn-spp-at 8 control)) (cell (fn-spp-at 4 work))
        (cursor (fn-hmid-one (fn-hmid-at 5 cell)))
        (word (fn-hmid-status cursor)))
  (if (eq word :yield)
   (mv :yield nil
    (fn-ibr-restate control :decision (fn-spp-at 6 control) (fn-spp-at 7 control)
     (fn-ibr-work (fn-spp-at 1 work) (fn-spp-at 2 work) (fn-spp-at 3 work)
      (fn-osh-make (fn-hmid-at 1 cell) (fn-hmid-at 2 cell) (fn-hmid-at 3 cell)
                   :msgid cursor))))
   (mv (if (eq word :valid) :visible :skip)
       (if (eq word :valid) (fn-spp-at 1 (fn-spp-at 1 work)) nil)
       (fn-ibr-decision-next-number control)))))


(defthm fn-ibr-row-decision-retains-original-plan-and-source
 (let ((next (mv-nth 2 (fn-ibr-row-decision-one control))))
  (and (equal (fn-spp-at 1 next) (fn-spp-at 1 control))
       (equal (fn-spp-at 2 next) (fn-spp-at 2 control))
       (equal (fn-spp-at 4 next) (fn-spp-at 4 control))
       (equal (fn-spp-at 5 next) (fn-spp-at 5 control))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ibr-row-decision-one fn-ibr-decision-next-number
                    fn-ibr-restate fn-ibr-make fn-spp-at fn-ag-car fn-ag-cdr)
                   (fn-hmid-one fn-hmid-status fn-osh-make fn-ibr-work
                    fn-gns-group-selected-result
                    fn-gns-number-begin fn-obc-next-range)))))

(local
 (defthm fn-ibr-decision-hmid-one-text-by-definition
  (equal (fn-hmid-at 1 (fn-hmid-one cursor)) (fn-hmid-at 1 cursor))
  :hints (("Goal" :in-theory (enable fn-hmid-one fn-hmid-at fn-ag-car fn-ag-cdr)))))
(local
 (defthm fn-ibr-decision-msgid-nonstring-by-definition
  (implies (not (stringp text)) (not (fn-scat-msgid-idp text)))
  :hints (("Goal" :in-theory (enable fn-scat-msgid-idp)))))
(defthm fn-ibr-row-decision-completed-is-original-msgid-predicate
 (implies
  (and (fn-ibr-row-decision-ready-p control)
       (not (eq (fn-hmid-status
                  (fn-hmid-one (fn-hmid-at 5 (fn-spp-at 4 (fn-spp-at 8 control)))))
                :yield)))
  (equal (equal (mv-nth 0 (fn-ibr-row-decision-one control)) :visible)
         (fn-scat-msgid-idp
           (fn-record-msgid (fn-hmid-at 3 (fn-spp-at 4 (fn-spp-at 8 control)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ibr-decision-msgid-nonstring-by-definition
          (text (fn-record-msgid (fn-hmid-at 3 (fn-spp-at 4 (fn-spp-at 8 control))))))
        (:instance fn-hmid-one-preserves-original-predicate-carry
          (cursor (fn-hmid-at 5 (fn-spp-at 4 (fn-spp-at 8 control)))))
        (:instance fn-hmid-completed-status-is-original-predicate
          (cursor (fn-hmid-one
                    (fn-hmid-at 5 (fn-spp-at 4 (fn-spp-at 8 control)))))))
  :in-theory (e/d (fn-ibr-row-decision-one fn-ibr-row-decision-ready-p
                    fn-hmid-status)
                   (fn-hmid-one fn-hmid-ready-p fn-hmid-cursorp fn-hmid-suffix-ok
                    fn-scat-msgid-idp fn-gns-number-result
                    fn-ibr-held-visible-p fn-held-withdrawnp
                    fn-ibr-decision-next-number fn-ibr-restate fn-ibr-work fn-osh-make
                    fn-hmid-at fn-record-msgid)))))


(local
 (defthm fn-ibr-decision-carry-hmid-one-text-by-definition
  (equal (fn-hmid-at 1 (fn-hmid-one cursor)) (fn-hmid-at 1 cursor))
  :hints (("Goal" :in-theory (e/d (fn-hmid-one fn-hmid-at fn-ag-car fn-ag-cdr)
                                (fn-hmid-char-ok))))))
(defthm fn-ibr-row-decision-begin-establishes-carried-predicate
 (implies (fn-ibr-held-install-ready-p control held fn-arena)
  (let ((answer (fn-ibr-row-decision-begin control held fn-arena)))
   (implies (eq (mv-nth 0 answer) :decision)
            (fn-ibr-row-decision-ready-p (mv-nth 1 answer)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hmid-begin-establishes-original-predicate-carry
                    (text (fn-record-msgid held))))
  :in-theory
   (e/d (fn-ibr-row-decision-begin fn-ibr-row-decision-ready-p
          fn-ibr-held-install-ready-p fn-ibr-restate fn-ibr-make fn-ibr-work
          fn-osh-begin fn-osh-make fn-hmid-begin fn-spp-at fn-hmid-at
          fn-ag-car fn-ag-cdr)
        (fn-hmid-ready-p fn-ibr-held-visible-p fn-gns-number-result
         fn-ibr-decision-next-number fn-spp-origin fn-ipub-count fn-ipub-view
         fn-held-withdrawnp fn-held-withdrawn fn-record-msgid)))))
(defthm fn-ibr-row-decision-yield-preserves-carried-predicate
 (implies (fn-ibr-row-decision-ready-p control)
  (let ((answer (fn-ibr-row-decision-one control)))
   (implies (eq (mv-nth 0 answer) :yield)
            (fn-ibr-row-decision-ready-p (mv-nth 2 answer)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hmid-one-preserves-original-predicate-carry
           (cursor (fn-hmid-at 5 (fn-spp-at 4 (fn-spp-at 8 control))))))
  :in-theory
   (e/d (fn-ibr-row-decision-one fn-ibr-row-decision-ready-p
          fn-ibr-restate fn-ibr-make fn-ibr-work fn-osh-make
          fn-spp-at fn-hmid-at fn-ag-car fn-ag-cdr)
        (fn-hmid-ready-p fn-hmid-one fn-hmid-status fn-ibr-held-visible-p
         fn-gns-number-result fn-ibr-decision-next-number
         fn-ipub-count fn-ipub-view fn-held-withdrawnp fn-held-withdrawn
         fn-record-msgid)))))
