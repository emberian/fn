; Historical held15 MODEL: registered captured-source issuance is not asserted.
(in-package "ACL2")
(include-book "../../books/index-range-row-decision")
(defun-nx ibrdt-begin (msgid withdrawn view)
 (let* ((arena '((65)))
        (publication (fn-ipub-make 7 nil nil 1 19 view nil 0 11 nil 0 12 nil 13 nil nil 4 1))
        (range (list "g" 1 3 view nil t))
        (plan (fn-spp-begin nil '(:source 17) '(:resource 18)))
        (number (fn-gns-number-step (fn-gns-number-begin 1 (cons '(:ordinal 0) nil) 1)))
        (control (fn-ibr-make 17 7 :row plan
          (list :publication-pin '(:generation 7) publication)
          (fn-gns-group-begin "g" nil) number (fn-ibr-work range publication nil nil)))
        (held (fn-held-make 0 1 0 msgid 0 '("g") "o" "s" "e" 1 5
          (fn-hf-make 3 nil 0 nil)
          (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) '(("g" . 1)) withdrawn)))
  (list control held arena (mv-list 2 (fn-ibr-row-decision-begin control held arena)))))
(defun-nx ibrdt-advance (n control)
 (declare (xargs :measure (nfix n)))
 (if (zp n) control
  (ibrdt-advance (1- n) (mv-nth 2 (fn-ibr-row-decision-one control)))))
(defthm ibrdt-completed-valid-model-positive
 (let* ((setup (ibrdt-begin "<e@x>" nil 7))
        (initial (nth 1 (nth 3 setup))) (control (mv-nth 2 (fn-ibr-row-decision-one (mv-nth 2 (fn-ibr-row-decision-one (mv-nth 2 (fn-ibr-row-decision-one (mv-nth 2 (fn-ibr-row-decision-one initial)))))))))
        (answer (fn-ibr-row-decision-one control)))
  (and (fn-ibr-held-install-ready-p (nth 0 setup) (nth 1 setup) (nth 2 setup))
       (equal (nth 0 (nth 3 setup)) :decision)
       (fn-ibr-row-decision-ready-p initial) (fn-ibr-row-decision-ready-p control)
       (not (eq (fn-hmid-status (fn-hmid-one
                   (fn-hmid-at 5 (fn-spp-at 4 (fn-spp-at 8 control))))) :yield))
       (equal (mv-nth 0 answer) :visible) (equal (mv-nth 1 answer) 1)
       (fn-scat-msgid-idp (fn-record-msgid (nth 1 setup)))
       (equal (fn-spp-at 4 (mv-nth 2 answer)) (fn-spp-at 4 control))
       (equal (fn-spp-at 5 (mv-nth 2 answer)) (fn-spp-at 5 control))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable ibrdt-advance))))
(defthm ibrdt-completed-invalid-model-positive
 (let* ((setup (ibrdt-begin "<e x>" nil 7))
        (control (mv-nth 2 (fn-ibr-row-decision-one (mv-nth 2 (fn-ibr-row-decision-one (mv-nth 2 (fn-ibr-row-decision-one (mv-nth 2 (fn-ibr-row-decision-one (nth 1 (nth 3 setup)))))))))))
        (answer (fn-ibr-row-decision-one control)))
  (and (fn-ibr-row-decision-ready-p control)
       (not (eq (fn-hmid-status (fn-hmid-one
                   (fn-hmid-at 5 (fn-spp-at 4 (fn-spp-at 8 control))))) :yield))
       (equal (mv-nth 0 answer) :skip) (null (mv-nth 1 answer))
       (not (fn-scat-msgid-idp (fn-record-msgid (nth 1 setup))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable ibrdt-advance))))
(defthm ibrdt-without-completion-model-premise-removal
 (let* ((setup (ibrdt-begin "<e@x>" nil 7)) (control (nth 1 (nth 3 setup)))
        (answer (fn-ibr-row-decision-one control)))
  (and (fn-ibr-row-decision-ready-p control)
       (eq (fn-hmid-status (fn-hmid-one
                   (fn-hmid-at 5 (fn-spp-at 4 (fn-spp-at 8 control))))) :yield)
       (fn-scat-msgid-idp (fn-record-msgid (nth 1 setup)))
       (not (equal (equal (mv-nth 0 answer) :visible)
                   (fn-scat-msgid-idp (fn-record-msgid (nth 1 setup)))))
       (equal (mv-nth 0 answer) :yield)
       (fn-ibr-row-decision-ready-p (mv-nth 2 answer))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable ibrdt-advance))))
; Corrupted-state MUTATION: forged completed-valid bit contradicts original.
(defthm ibrdt-without-carried-predicate-mutation
 (let* ((setup (ibrdt-begin "<e x>" nil 7)) (old (nth 1 (nth 3 setup)))
        (work (fn-spp-at 8 old)) (cell (fn-spp-at 4 work))
        (control (fn-ibr-restate old :decision (fn-spp-at 6 old) (fn-spp-at 7 old)
          (fn-ibr-work (fn-spp-at 1 work) (fn-spp-at 2 work) (fn-spp-at 3 work)
             (fn-osh-make (fn-hmid-at 1 cell) (fn-hmid-at 2 cell) (fn-hmid-at 3 cell)
                          :msgid '(:held-msgid "<e x>" 5 5 t)))))
        (answer (fn-ibr-row-decision-one control)))
  (and (not (fn-ibr-row-decision-ready-p control))
       (not (eq (fn-hmid-status (fn-hmid-one
                   (fn-hmid-at 5 (fn-spp-at 4 (fn-spp-at 8 control))))) :yield))
       (not (fn-scat-msgid-idp (fn-record-msgid (nth 1 setup))))
       (equal (mv-nth 0 answer) :visible)
       (not (equal (equal (mv-nth 0 answer) :visible)
                   (fn-scat-msgid-idp (fn-record-msgid (nth 1 setup)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable ibrdt-advance))))
(defthm ibrdt-withdrawn-captured-model-skip
 (let* ((setup (ibrdt-begin "<e@x>" '(5 . 0) 7))
        (answer (nth 3 setup)))
  (and (fn-ibr-held-install-ready-p (nth 0 setup) (nth 1 setup) (nth 2 setup))
       (equal (nth 0 answer) :skip)
       (equal (fn-spp-at 4 (nth 1 answer)) (fn-spp-at 4 (nth 0 setup)))
       (equal (fn-spp-at 5 (nth 1 answer)) (fn-spp-at 5 (nth 0 setup)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable ibrdt-advance))))
