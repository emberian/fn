; Paid positioning of a full render plan. PRF-1066 integration component.
; The reversed prefix is borrowed effect data, retained once while the active
; suffix advances. Its reconstruction is logical vocabulary only. Each ONE
; skips at most one effect; no served scan or prefix rebuild is hidden here.
(in-package "ACL2")
(include-book "served-plan-shape")

; (:position-plan current skipped-reverse remaining origin resource).
(defun fn-spp-holderp (p)
 (declare (xargs :guard t))
 (and (consp p) (eq (car p) :position-plan)))

(defun fn-spp-at (k x)
 (declare (xargs :guard (natp k) :measure (nfix k)))
 (if (zp k) (fn-ag-car x) (fn-spp-at (1- k) (fn-ag-cdr x))))

(defun fn-spp-cur (p)
 (declare (xargs :guard t)) (fn-spp-at 1 p))
(defun fn-spp-prefix (p)
 (declare (xargs :guard t)) (fn-spp-at 2 p))
(defun fn-spp-rest (p)
 (declare (xargs :guard t)) (fn-spp-at 3 p))
(defun fn-spp-origin (p)
 (declare (xargs :guard t)) (fn-spp-at 4 p))
(defun fn-spp-resource (p)
 (declare (xargs :guard t)) (fn-spp-at 5 p))

(defun fn-spp-make (cur prefix rest origin resource)
 (declare (xargs :guard t))
 (list :position-plan cur prefix rest origin resource))

(defun fn-spp-begin (p origin resource)
 (declare (xargs :guard t))
 (if (fn-spp-holderp p) p
  (fn-spp-make (fn-splan-cur p) nil (fn-splan-rest p) origin resource)))

; Status is a fixed set of outer-spine/head observations, not a traversal.
(defun fn-spp-status (p)
 (declare (xargs :guard t))
 (cond ((not (fn-spp-holderp p)) :malformed)
       ((consp (fn-spp-cur p)) :reply)
       ((not (consp (fn-spp-rest p))) :done)
       ((fn-splan-cursor-effectp (fn-ag-car (fn-spp-rest p))) :cursor)
       ((consp (fn-srb-effect-octets (fn-ag-car (fn-spp-rest p)))) :reply)
       (t :position)))

(defun fn-spp-one (p)
 (declare (xargs :guard t))
 (if (eq (fn-spp-status p) :position)
  (fn-spp-make (fn-spp-cur p)
               (cons (fn-ag-car (fn-spp-rest p)) (fn-spp-prefix p))
               (fn-ag-cdr (fn-spp-rest p)) (fn-spp-origin p) (fn-spp-resource p))
  p))

; WORK counts exactly the skipped effects. Exhaustion yields the full holder.
(defun fn-spp-tick (p fuel)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel) :verify-guards nil))
 (let ((status (fn-spp-status p)))
  (cond ((not (eq status :position)) (mv status p 0))
        ((zp fuel) (mv :yield p 0))
        (t (mv-let (status next work) (fn-spp-tick (fn-spp-one p) (1- fuel))
             (mv status next (+ 1 work)))))))

(defthm fn-spp-tick-work-natural
 (natp (mv-nth 2 (fn-spp-tick p fuel)))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-spp-tick p fuel)
          :in-theory (e/d (fn-spp-tick) (fn-spp-one fn-spp-status)))))

(verify-guards fn-spp-tick
 :hints (("Goal" :in-theory (disable fn-spp-one fn-spp-status))))

; Constant-work active-plan projection and save. Prefix, origin and resource
; remain in the SAME returned holder when the active cursor/renderer changes.
(defun fn-spp-active-plan (p)
 (declare (xargs :guard t))
 (cons (fn-spp-cur p) (fn-spp-rest p)))

(defun fn-spp-save-active (p active)
 (declare (xargs :guard t))
 (fn-spp-make (fn-splan-cur active) (fn-spp-prefix p) (fn-splan-rest active)
              (fn-spp-origin p) (fn-spp-resource p)))

(defun fn-spp-window-size (p)
 (declare (xargs :guard t))
 (if (consp (fn-spp-cur p)) (len (fn-spp-cur p))
  (len (fn-srb-effect-octets (fn-ag-car (fn-spp-rest p))))))

; Representation boundary: full effect trace, including every ignored prefix
; effect. Reconstructing it is never part of a served quantum or host guard.
(defun-nx fn-spp-plan (p)
 (declare (xargs :guard t :verify-guards nil))
 (cons (fn-spp-cur p) (revappend (fn-spp-prefix p) (fn-spp-rest p))))

(defthm fn-spp-begin-denotes-original-plan
 (implies (and (consp p) (not (fn-spp-holderp p)))
          (equal (fn-spp-plan (fn-spp-begin p origin resource)) p))
 :hints (("Goal" :in-theory
  (enable fn-spp-plan fn-spp-begin fn-spp-make fn-spp-cur fn-spp-prefix
          fn-spp-rest fn-splan-cur fn-splan-rest fn-spp-at fn-ag-car fn-ag-cdr))))

(defthm fn-spp-one-preserves-complete-plan
 (equal (fn-spp-plan (fn-spp-one p)) (fn-spp-plan p))
 :hints (("Goal" :in-theory
  (enable fn-spp-one fn-spp-status fn-spp-plan fn-spp-make fn-spp-cur
          fn-spp-prefix fn-spp-rest fn-spp-origin fn-spp-resource revappend fn-spp-at fn-ag-car fn-ag-cdr))))

(defthm fn-spp-one-preserves-origin-and-resource
 (and (equal (fn-spp-origin (fn-spp-one p)) (fn-spp-origin p))
      (equal (fn-spp-resource (fn-spp-one p)) (fn-spp-resource p)))
 :hints (("Goal" :in-theory
  (enable fn-spp-one fn-spp-make fn-spp-origin fn-spp-resource fn-spp-at fn-ag-car fn-ag-cdr))))

(defthm fn-spp-tick-preserves-complete-plan-and-ownership
 (let ((next (mv-nth 1 (fn-spp-tick p fuel))))
  (and (equal (fn-spp-plan next) (fn-spp-plan p))
       (equal (fn-spp-origin next) (fn-spp-origin p))
       (equal (fn-spp-resource next) (fn-spp-resource p))))
 :hints (("Goal" :induct (fn-spp-tick p fuel)
          :in-theory (e/d (fn-spp-tick) (fn-spp-one fn-spp-plan
                                        fn-spp-origin fn-spp-resource fn-spp-at fn-ag-car fn-ag-cdr)))))

(defthm fn-spp-tick-at-most-fuel
 (and (natp (mv-nth 2 (fn-spp-tick p fuel)))
      (<= (mv-nth 2 (fn-spp-tick p fuel)) (nfix fuel)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-spp-tick p fuel)
          :in-theory (e/d (fn-spp-tick) (fn-spp-one fn-spp-status)))))

(defthm fn-spp-save-retains-prefix-and-ownership
 (and (equal (fn-spp-prefix (fn-spp-save-active p active)) (fn-spp-prefix p))
      (equal (fn-spp-origin (fn-spp-save-active p active)) (fn-spp-origin p))
      (equal (fn-spp-resource (fn-spp-save-active p active)) (fn-spp-resource p)))
 :hints (("Goal" :in-theory
  (enable fn-spp-save-active fn-spp-make fn-spp-prefix fn-spp-origin fn-spp-resource fn-spp-at fn-ag-car fn-ag-cdr))))

(defthm fn-spp-one-skips-exactly-one-effect
 (equal (len (fn-spp-rest (fn-spp-one p)))
        (if (eq (fn-spp-status p) :position)
            (1- (len (fn-spp-rest p)))
          (len (fn-spp-rest p))))
 :hints (("Goal" :in-theory
  (enable fn-spp-one fn-spp-status fn-spp-make fn-spp-rest fn-spp-at
          fn-ag-car fn-ag-cdr))))

(defthm fn-spp-tick-pays-every-skipped-effect
 (let ((next (mv-nth 1 (fn-spp-tick p fuel)))
       (work (mv-nth 2 (fn-spp-tick p fuel))))
  (equal (+ work (len (fn-spp-rest next))) (len (fn-spp-rest p))))
 :hints (("Goal" :induct (fn-spp-tick p fuel)
          :in-theory (e/d (fn-spp-tick)
                          (fn-spp-one fn-spp-status fn-spp-rest)))))

(defthm fn-spp-tick-makes-positive-positioning-progress
 (implies (and (posp fuel) (eq (fn-spp-status p) :position))
          (< 0 (mv-nth 2 (fn-spp-tick p fuel))))
 :hints (("Goal" :expand ((fn-spp-tick p fuel))
          :in-theory (disable fn-spp-one fn-spp-status fn-spp-tick))))

; Analysis-only inventory of explicit source constructor sites: each skipped
; effect allocates six holder slots and one prefix cell, and each tick call
; returns three MV slots. Compiler/runtime correspondence is a separate join.
(defun fn-spp-tick-conses (p fuel)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (not (eq (fn-spp-status p) :position)) (zp fuel)) 3
  (+ 10 (fn-spp-tick-conses (fn-spp-one p) (1- fuel)))))

(defthm fn-spp-tick-conses-track-actual-work
 (equal (fn-spp-tick-conses p fuel)
        (+ 3 (* 10 (mv-nth 2 (fn-spp-tick p fuel)))))
 :hints (("Goal" :induct (fn-spp-tick p fuel)
          :in-theory (e/d (fn-spp-tick fn-spp-tick-conses)
                          (fn-spp-one fn-spp-status)))))

(defthm fn-spp-tick-source-conses-at-most-funded-fuel
 (<= (fn-spp-tick-conses p fuel) (+ 3 (* 10 (nfix fuel))))
 :rule-classes nil
 :hints (("Goal" :use fn-spp-tick-at-most-fuel
          :in-theory (disable fn-spp-tick fn-spp-tick-conses))))
