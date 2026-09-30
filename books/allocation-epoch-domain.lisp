; Checked immediate-domain arithmetic for the internal allocation epoch.
; DOMAIN is derived by the selected runtime/profile installation, not an
; arbitrary storage ceiling. These helpers establish no installation authority.
(in-package "ACL2")

(defun fn-aed-add-roomp (used debit domain)
 (declare (xargs :guard t))
 (and (natp used) (natp debit) (natp domain)
      (<= debit domain) (<= used (- domain debit))))

(defun fn-aed-add (used debit domain)
 (declare (xargs :guard t))
 (if (fn-aed-add-roomp used debit domain)
     (mv :fits (+ used debit))
   (mv :unavailable used)))

; Leave the installed cleanup/collector/control reserve outside ordinary
; admission. Subtractions precede addition, so even a refused operation never
; creates an oversized sum in the selected immediate representation.
(defun fn-aed-ordinary-roomp (occupied prepaid reserve budget domain)
 (declare (xargs :guard t))
 (and (natp occupied) (natp prepaid) (natp reserve)
      (natp budget) (natp domain) (<= budget domain)
      (<= reserve budget)
      (<= prepaid (- budget reserve))
      (<= occupied (- (- budget reserve) prepaid))))

(defun fn-aed-ordinary-prepay (occupied prepaid debit reserve budget domain)
 (declare (xargs :guard t))
 (if (and (fn-aed-add-roomp prepaid debit domain)
          (fn-aed-ordinary-roomp occupied (+ prepaid debit) reserve budget domain))
     (mv :prepaid (+ prepaid debit))
   (mv :unavailable prepaid)))

(defthm fn-aed-add-fits-immediate-domain
 (implies (eq (mv-nth 0 (fn-aed-add used debit domain)) :fits)
          (and (natp (mv-nth 1 (fn-aed-add used debit domain)))
               (<= (mv-nth 1 (fn-aed-add used debit domain)) domain)
               (equal (mv-nth 1 (fn-aed-add used debit domain)) (+ used debit))))
 :rule-classes nil)

(defthm fn-aed-prepay-keeps-headroom
 (implies (eq (mv-nth 0 (fn-aed-ordinary-prepay occupied prepaid debit reserve budget domain))
              :prepaid)
          (let ((next (mv-nth 1 (fn-aed-ordinary-prepay occupied prepaid debit reserve budget domain))))
           (and (natp next) (<= next domain)
                (<= (+ occupied next reserve) budget)
                (equal next (+ prepaid debit)))))
 :rule-classes nil)

(defthm fn-aed-refused-prepay-keeps-charge
 (implies (not (eq (mv-nth 0 (fn-aed-ordinary-prepay occupied prepaid debit reserve budget domain))
                   :prepaid))
          (equal (mv-nth 1 (fn-aed-ordinary-prepay occupied prepaid debit reserve budget domain)) prepaid))
 :rule-classes nil)
