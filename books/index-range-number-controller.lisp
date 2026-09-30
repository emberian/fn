; Internal registered range transitions; no host source/row/root setter.
; Publication and controller pointers come from the same admitted slot.
(in-package "ACL2")
(include-book "index-range-controller")
(include-book "index-publication-shape")
(include-book "group-number-source-assignment")
(include-book "over-row-state")

; (:range-work advanced-range SAME-publication ordinal-walk row-state).
(defun fn-ibr-work (range publication ordinal row)
  (declare (xargs :guard t))
  (list :range-work range publication ordinal row))

(defun fn-ibr-restate (control phase group number work)
  (declare (xargs :guard t))
  (fn-ibr-make (fn-spp-at 1 control) (fn-spp-at 2 control) phase
               (fn-spp-at 4 control) (fn-spp-at 5 control) group number work))

; Invoked only inside the actual authenticated registered terminal action.
; PIN is the core-retained publication-pin, not a supplied publication tuple.
(defun fn-ibr-number-source-begin (control)
  (declare (xargs :guard t))
  (let* ((plan (fn-spp-at 4 control))
         (effect (fn-ag-car (fn-spp-rest plan)))
         (range (fn-spp-at 1 effect))
         (pin (fn-spp-at 5 control))
         (publication (fn-spp-at 2 pin)))
    (if (not (and (equal (fn-spp-at 0 control) :fn-ibr)
                  (equal (fn-spp-at 3 control) :position)
                  (equal (fn-spp-status plan) :cursor)
                  (equal (fn-spp-at 0 pin) :publication-pin)
                  (stringp (fn-spp-at 0 range))
                  (natp (fn-ipub-count publication))
                  (equal (fn-spp-at 2 control)
                         (fn-ipub-generation publication))
                  (equal (fn-spp-at 3 range) (fn-ipub-view publication))))
        (mv :source-mismatch control)
      (mv :group
          (fn-ibr-restate control :group
            (fn-gns-group-begin (fn-spp-at 0 range)
                                 (fn-ipub-number-root publication))
            nil (fn-ibr-work range publication nil nil))))))

(defun fn-ibr-group-one (control)
  (declare (xargs :guard
                  (fn-gns-group-cursorp (fn-spp-at 6 control))))
  (let* ((group (fn-gns-group-step (fn-spp-at 6 control)))
         (result (fn-gns-group-selected-result group))
         (work (fn-spp-at 8 control))
         (range (fn-spp-at 1 work))
         (publication (fn-spp-at 2 work)))
    (if (equal (fn-spp-at 0 result) :number-root)
        (fn-ibr-restate control :number group
          (fn-gns-number-begin (fn-spp-at 1 range)
                               (fn-spp-at 1 result) (fn-ipub-count publication))
          work)
      (fn-ibr-restate control :group group (fn-spp-at 7 control) work))))

; One number-bit action. A hole advances the local number while retaining
; the same selected group root, publication and actual owed flag.
(defun fn-ibr-number-one (control)
  (declare (xargs :guard
                  (and (fn-gns-number-cursorp (fn-spp-at 7 control))
                       (true-listp (fn-spp-at 1 (fn-spp-at 8 control))))))
  (let* ((number (fn-gns-number-step (fn-spp-at 7 control)))
         (raw-result (fn-gns-number-result number))
         (group (fn-spp-at 6 control))
         (work (fn-spp-at 8 control))
         (range (fn-spp-at 1 work))
         (publication (fn-spp-at 2 work))
         (result (if (or (not (posp (fn-spp-at 1 range)))
                         (< *fn-nntp-max-article-number* (nfix (fn-spp-at 1 range))))
                     '(:missing) raw-result)))
    (cond
     ((< (nfix (fn-spp-at 2 range)) (nfix (fn-spp-at 1 range)))
      (fn-ibr-restate control :terminal group number work))
     ((equal (fn-spp-at 0 result) :ordinal)
      (fn-ibr-restate control :row group number work))
     ((equal (fn-spp-at 0 result) :missing)
      (let ((next (fn-obc-next-range range (fn-spp-at 5 range))))
        (fn-ibr-restate control :number group
          (fn-gns-number-begin (fn-spp-at 1 next)
            (fn-spp-at 1 (fn-gns-group-selected-result group))
            (fn-ipub-count publication))
          (fn-ibr-work next publication nil nil))))
     (t (fn-ibr-restate control :number group number work)))))

(defthm fn-ibr-group-one-retains-original-plan-and-source
  (let ((next (fn-ibr-group-one control)))
    (and (equal (fn-spp-at 1 next) (fn-spp-at 1 control))
         (equal (fn-spp-at 2 next) (fn-spp-at 2 control))
         (equal (fn-spp-at 4 next) (fn-spp-at 4 control))
         (equal (fn-spp-at 5 next) (fn-spp-at 5 control))
         (equal (fn-spp-at 8 next) (fn-spp-at 8 control))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-ibr-group-one fn-ibr-restate fn-ibr-make
                 fn-spp-at fn-ag-car fn-ag-cdr)
                (fn-gns-group-step fn-gns-group-selected-result
                 fn-gns-number-begin fn-ipub-count)))))

(defthm fn-ibr-number-one-retains-publication-plan-and-owed
  (let* ((next (fn-ibr-number-one control))
         (old-work (fn-spp-at 8 control)) (new-work (fn-spp-at 8 next)))
    (and (equal (fn-spp-at 1 next) (fn-spp-at 1 control))
         (equal (fn-spp-at 2 next) (fn-spp-at 2 control))
         (equal (fn-spp-at 4 next) (fn-spp-at 4 control))
         (equal (fn-spp-at 5 next) (fn-spp-at 5 control))
         (equal (fn-spp-at 6 next) (fn-spp-at 6 control))
         (equal (fn-spp-at 2 new-work) (fn-spp-at 2 old-work))
         (equal (fn-spp-at 5 (fn-spp-at 1 new-work))
                (fn-spp-at 5 (fn-spp-at 1 old-work)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-ibr-number-one fn-ibr-restate fn-ibr-make fn-ibr-work
                 fn-obc-next-range fn-ovw-cursor fn-spp-at fn-ag-car fn-ag-cdr)
                (fn-gns-number-step fn-gns-number-result
                 fn-gns-group-selected-result fn-gns-number-begin fn-ipub-count)))))

; Guard/proof carry only. Registered transitions establish it once and keep
; it; the selected compiled callback must not execute this recognizer.
(defun fn-ibr-number-ready-p (control)
  (declare (xargs :guard t))
  (let* ((work (fn-spp-at 8 control))
         (range (fn-spp-at 1 work)) (publication (fn-spp-at 2 work))
         (number (fn-spp-at 7 control)))
    (and (fn-gns-number-cursorp number) (true-listp range)
         (natp (fn-ipub-count publication))
         (implies (posp (fn-spp-at 1 range))
                  (equal (fn-gns-at 3 number) (fn-ipub-count publication))))))

(defthm fn-ibr-number-one-preserves-captured-count-carry
  (implies (fn-ibr-number-ready-p control)
           (fn-ibr-number-ready-p (fn-ibr-number-one control)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-gns-number-step-cursorp
                            (c (fn-spp-at 7 control))))
           :in-theory
           (e/d (fn-ibr-number-ready-p fn-ibr-number-one fn-ibr-work
                 fn-ibr-restate fn-ibr-make fn-obc-next-range fn-ovw-cursor
                 fn-spp-at fn-gns-at fn-ag-car fn-ag-cdr
                 fn-gns-number-step fn-gns-number-begin fn-gns-number-cursorp)
                (fn-gns-number-result fn-gns-group-selected-result fn-ipub-count)))))
