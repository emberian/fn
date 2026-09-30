; Exact original render-buffer implementation moved verbatim.
(in-package "ACL2")
(include-book "served-plan-shape")
(include-book "octets-stobj")

(defun fn-splan-fill (cur rest k fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (natp k)
                  :measure (+ (acl2-count cur) (acl2-count rest))))
  (cond ((zp k) (mv :ok (cons cur rest) fn-octets))
        ((consp cur)
         (if (fn-cbor-octetp (car cur))
             (let ((fn-octets (fn-octets-append-octet (car cur) fn-octets)))
               (fn-splan-fill (cdr cur) rest (- k 1) fn-octets))
           (mv :malformed (cons cur rest) fn-octets)))
        ((consp rest)
         (if (fn-splan-cursor-effectp (car rest))
             (mv :cursor (cons cur rest) fn-octets)
           (fn-splan-fill (fn-srb-effect-octets (car rest)) (cdr rest) k fn-octets)))
        (t (mv :ok (cons nil nil) fn-octets))))

; The host-called subject: clear the buffer, then one window.
(defun fn-splan-window (p w fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp w)))
  (let ((fn-octets (fn-octets-clear fn-octets)))
    (fn-splan-fill (fn-splan-cur p) (fn-splan-rest p) w fn-octets)))

(defthm fn-splan-fill-returns-plan
 (consp (mv-nth 1 (fn-splan-fill cur rest k fn-octets)))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-splan-fill cur rest k fn-octets))))

(defthm fn-splan-window-returns-plan
 (consp (mv-nth 1 (fn-splan-window p w fn-octets)))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (e/d (fn-splan-window) (fn-splan-fill)))))
