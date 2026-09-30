; Paid head-only reply rendering. Window is the operator-granted capacity;
; the logical reference alone computes a reply length. No ignored tail scan.
(in-package "ACL2")
(include-book "served-plan-position")
(include-book "served-plan-window")

(defun fn-spp-head-window (p w fn-octets)
 (declare (xargs :stobjs fn-octets
                 :guard (and (natp w) (eq (fn-spp-status p) :reply))))
 (let ((fn-octets (fn-octets-clear fn-octets)))
  (if (zp w) (mv :ok p fn-octets)
   (let* ((currentp (consp (fn-spp-cur p)))
          (cur (if currentp (fn-spp-cur p)
                 (fn-srb-effect-octets (fn-ag-car (fn-spp-rest p)))))
          (tail (if currentp (fn-spp-rest p) (fn-ag-cdr (fn-spp-rest p)))))
    (mv-let (status segment fn-octets) (fn-splan-fill cur nil w fn-octets)
     (mv status (fn-spp-save-active p (cons (fn-splan-cur segment) tail)) fn-octets))))))

(local
 (defthm fn-spp-head-fill-zero
  (equal (fn-splan-fill cur tail 0 fn-octets) (list :ok (cons cur tail) fn-octets))
  :hints (("Goal" :in-theory (enable fn-splan-fill)))))

(local
 (defun fn-spp-head-induct (cur w fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil :measure (nfix w)))
  (if (and (consp cur) (posp w) (fn-cbor-octetp (car cur)))
   (let ((fn-octets (fn-octets-append-octet (car cur) fn-octets)))
    (fn-spp-head-induct (cdr cur) (1- w) fn-octets))
   fn-octets)))

(local
 (defthm fn-spp-head-fill-is-old-bounded-fill
  (implies (and (true-listp cur) (natp w))
   (let* ((actual (fn-splan-fill cur nil w fn-octets))
          (old (fn-splan-fill cur tail (min w (len cur)) fn-octets)))
    (and (equal (mv-nth 0 actual) (mv-nth 0 old))
         (equal (mv-nth 2 actual) (mv-nth 2 old))
         (equal (fn-splan-cur (mv-nth 1 actual)) (fn-splan-cur (mv-nth 1 old)))
         (equal (fn-splan-rest (mv-nth 1 old)) tail))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-spp-head-induct cur w fn-octets)
   :in-theory (e/d (fn-splan-fill fn-splan-cur fn-splan-rest)
     (fn-octets-append-octet fn-cbor-octetp))))))

(local
 (defthm fn-spp-head-nonempty-length
  (implies (consp x) (< 0 (len x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable len)))))

(defthm fn-spp-head-window-refines-actual-old-buffer-window
 (let* ((cur (if (consp (fn-spp-cur p)) (fn-spp-cur p)
                (fn-srb-effect-octets (fn-ag-car (fn-spp-rest p)))))
        (actual (fn-spp-head-window p w fn-octets))
        (old (fn-splan-window (fn-spp-active-plan p) (min w (len cur)) fn-octets))
        (next (mv-nth 1 actual)))
  (implies (and (natp w) (eq (fn-spp-status p) :reply) (true-listp cur))
   (and (equal (mv-nth 0 actual) (mv-nth 0 old))
        (equal (mv-nth 2 actual) (mv-nth 2 old))
        (equal (fn-spp-active-plan next) (mv-nth 1 old))
        (equal (fn-spp-prefix next) (fn-spp-prefix p))
        (equal (fn-spp-origin next) (fn-spp-origin p))
        (equal (fn-spp-resource next) (fn-spp-resource p)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-spp-head-fill-is-old-bounded-fill
          (cur (fn-spp-cur p)) (tail (fn-spp-rest p))
          (fn-octets (fn-octets-clear fn-octets)))
        (:instance fn-spp-head-fill-is-old-bounded-fill
          (cur (fn-srb-effect-octets (fn-ag-car (fn-spp-rest p))))
          (tail (fn-ag-cdr (fn-spp-rest p)))
          (fn-octets (fn-octets-clear fn-octets))))
  :in-theory
   (e/d (fn-spp-head-window fn-splan-window fn-spp-status fn-splan-fill fn-spp-active-plan fn-spp-save-active
         fn-spp-make fn-spp-cur fn-spp-rest fn-spp-prefix fn-spp-origin fn-spp-resource
         fn-spp-at fn-ag-car fn-ag-cdr fn-splan-cur fn-splan-rest fn-octets-clear)
        (fn-srb-effect-octets)))))
