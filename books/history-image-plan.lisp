; Length planning for the canonical history image. The host carries PLAN;
; the generated quantum owns iteration and refusal, with no encoded rows.
(in-package "ACL2")
(include-book "history-image-build-rows")
(include-book "store-tree-length")
(include-book "def-loop-run")

(defun fn-hp-x-rowlen (ev)
  (declare (xargs :guard t))
  (if (not (fn-sccb-treep ev))
      (mv (list :refused :event) 0 0)
    (let ((tl (fn-scc-program-len ev 0)))
      (if (not (unsigned-byte-p 64 tl))
          (mv (list :refused :event) 0 0)
        (mv nil tl (+ tl (fn-hp-pad8-count tl)))))))

(defthm fn-hp-x-rowlen-spec
 (equal (fn-hp-x-rowlen ev)
        (if (fn-hp-evp ev)
            (list nil (len (fn-scc-encode ev)) (len (fn-hp-pad8 (fn-scc-encode ev))))
          (list '(:refused :event) 0 0)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-scc-program-len-is-encode-len (x ev) (acc 0)))
          :in-theory (e/d (fn-hp-x-rowlen fn-hp-evp fn-hp-len-pad8)
                          (fn-scc-program-len fn-scc-encode fn-scc-encode-is-program
                           fn-scc-program fn-sccb-treep fn-hp-pad8-count fn-hp-pad8 fn-hp-pe-is-pad8)))))

(defthm fn-hp-x-rowlen-plen-natural
 (natp (mv-nth 2 (fn-hp-x-rowlen ev)))
 :rule-classes :type-prescription
 :hints (("Goal" :use fn-hp-x-rowlen-spec
          :in-theory (disable fn-hp-x-rowlen fn-hp-evp fn-hp-pad8 fn-hp-len-pad8
                              fn-scc-encode fn-scc-encode-is-program))))

(defun fn-his-planp (plan)
  (declare (xargs :guard t))
  (and (true-listp plan) (equal (len plan) 2)
       (natp (car plan)) (nat-listp (cadr plan)) (equal (len (cadr plan)) 5)))

(defun fn-his-plan-row (ev plan)
  (declare (xargs :guard (fn-his-planp plan)
                  :guard-hints (("Goal" :in-theory (disable fn-hp-x-rowlen)))))
  (mv-let (v tl plen) (fn-hp-x-rowlen ev)
    (declare (ignore tl))
    (if v (mv v plan)
      (mv nil (list (+ 1 (nfix (car plan)))
                    (fn-hp-x-add (cadr plan) (list 8 8 8 8 plen)))))))

(defthm fn-his-plan-row-preserves-planp
 (implies (fn-his-planp plan) (fn-his-planp (mv-nth 1 (fn-his-plan-row ev plan))))
 :hints (("Goal" :in-theory (e/d (fn-his-planp fn-his-plan-row fn-hp-x-add) (fn-hp-x-rowlen)))))

(defthm fn-his-plan-row-status
 (and (not (equal (car (fn-his-plan-row ev plan)) :done))
      (not (equal (car (fn-his-plan-row ev plan)) :more)))
 :hints (("Goal" :in-theory (e/d (fn-his-plan-row fn-hp-x-rowlen)
                                (fn-scc-program-len fn-sccb-treep fn-hp-pad8-count)))))

(local (in-theory (disable fn-his-planp fn-his-plan-row fn-hp-x-rowlen)))

(def-loop/run fn-his-plan (evs plan) :acc plan :quantum *fn-his-build-yield-rows*
 :guard (fn-his-planp plan) :row (fn-his-plan-row (car evs) plan)
 :guard-hints (("Goal" :in-theory (disable fn-his-plan-row fn-his-planp fn-hp-x-rowlen)))
 :row-theory (fn-hp-x-rowlen)
 :end-status (if (null evs) nil '(:refused :event)))

(defthm fn-his-plan-drive-is-plan-all
  (equal (fn-his-plan-drive (+ 1 (len evs)) evs plan) (fn-his-plan-all evs plan))
  :hints (("Goal" :use fn-his-plan-drive-is-all
           :in-theory (disable fn-his-plan-drive fn-his-plan-all)))
  :rule-classes nil)

(defthm fn-his-plan-all-preserves-planp
 (implies (fn-his-planp plan) (fn-his-planp (mv-nth 1 (fn-his-plan-all evs plan))))
 :hints (("Goal" :induct (fn-his-plan-all evs plan)
          :in-theory (disable fn-his-planp fn-his-plan-row))))

(defthm fn-his-plan-drive-preserves-planp
 (implies (fn-his-planp plan)
          (fn-his-planp (mv-nth 1 (fn-his-plan-drive (+ 1 (len evs)) evs plan))))
 :hints (("Goal" :use fn-his-plan-drive-is-plan-all
          :in-theory (disable fn-his-plan-drive fn-his-plan-all fn-his-planp))))
