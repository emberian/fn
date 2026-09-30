; Actual original render-buffer bridge for the positioned full plan.
; Semantic positioning is separate from this broader served implementation.
(in-package "ACL2")
(include-book "served-plan-position")
(include-book "served-plan-window")

(defun fn-spp-window (p w fn-octets)
 (declare (xargs :stobjs fn-octets
                 :guard (and (natp w) (eq (fn-spp-status p) :reply)
                             (<= w (fn-spp-window-size p)))))
 (mv-let (status active fn-octets)
   (fn-splan-window (fn-spp-active-plan p) w fn-octets)
  (mv status (fn-spp-save-active p active) fn-octets)))

(defthm fn-spp-window-refines-original-buffer-window
 (let* ((original (fn-splan-window (fn-spp-active-plan p) w fn-octets))
        (actual (fn-spp-window p w fn-octets))
        (next (mv-nth 1 actual)))
  (and (equal (mv-nth 0 actual) (mv-nth 0 original))
       (equal (mv-nth 2 actual) (mv-nth 2 original))
       (equal (fn-spp-active-plan next) (mv-nth 1 original))
       (equal (fn-spp-prefix next) (fn-spp-prefix p))
       (equal (fn-spp-origin next) (fn-spp-origin p))
       (equal (fn-spp-resource next) (fn-spp-resource p))))
 :hints (("Goal" :in-theory
  (e/d (fn-spp-window fn-spp-save-active fn-spp-active-plan fn-spp-make
         fn-spp-cur fn-spp-rest fn-spp-prefix fn-spp-origin fn-spp-resource
         fn-spp-at fn-ag-car fn-ag-cdr fn-splan-cur fn-splan-rest)
       (fn-splan-window)))))

(local
 (defthm fn-spp-window-fill-keeps-unvisited-tail
  (implies (and (natp k) (<= k (len cur)))
   (equal (fn-splan-rest (mv-nth 1 (fn-splan-fill cur rest k fn-octets))) rest))
  :hints (("Goal" :induct (fn-splan-fill cur rest k fn-octets)
            :in-theory (enable fn-splan-rest)))))

(local
 (defthm fn-spp-window-fill-selects-head-by-definition
  (implies (and (not (consp cur)) (consp rest) (posp k)
                (not (fn-splan-cursor-effectp (car rest))))
   (equal (fn-splan-fill cur rest k fn-octets)
          (fn-splan-fill (fn-srb-effect-octets (car rest)) (cdr rest) k fn-octets)))
  :hints (("Goal" :expand ((fn-splan-fill cur rest k fn-octets))
            :in-theory (disable fn-splan-fill)))))

(local (defthm fn-spp-window-consp-car-implies-consp
 (implies (consp (car x)) (consp x))
 :hints (("Goal" :cases ((consp x))))))

(defthm fn-spp-window-keeps-complete-unvisited-tail
 (implies (and (posp w) (<= w (fn-spp-window-size p)))
  (equal (fn-spp-rest (mv-nth 1 (fn-spp-window p w fn-octets)))
         (if (consp (fn-spp-cur p)) (fn-spp-rest p)
           (fn-ag-cdr (fn-spp-rest p)))))
 :hints (("Goal" :cases ((consp (fn-spp-cur p)))
           :in-theory
   (e/d (fn-spp-window fn-splan-window fn-spp-active-plan fn-spp-save-active
          fn-spp-status fn-spp-window-size fn-spp-holderp fn-spp-make
          fn-spp-cur fn-spp-rest fn-spp-at fn-ag-car fn-ag-cdr
          fn-srb-effect-octets fn-splan-cursor-effectp)
        (fn-splan-fill fn-splan-rest)))))
