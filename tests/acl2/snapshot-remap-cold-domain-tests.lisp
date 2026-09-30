(in-package "ACL2")
(include-book "../../books/snapshot-remap-cold-domain")
(defun rccdt-spine (n)
 (declare (xargs :guard (natp n)))
 (if (zp n) (fn-hdc-atom nil)
  (fn-hdc-pair (fn-hdc-atom 0) (rccdt-spine (1- n)))))
(defconst *rccdt-held* (rccdt-spine 16))
(defconst *rccdt-composite*
 (fn-hdc-pair (fn-hdc-atom :hstxa)
  (fn-hdc-pair (fn-hdc-atom nil)
   (fn-hdc-pair *rccdt-held* (fn-hdc-atom nil)))))
(defthm rccdt-actual-held-complete-positive
 (and (fn-odm-prefixp 5 *rccdt-held*)
      (fn-hrcur-cold-domainp *rccdt-held* nil)
      (fn-hrcur-cold-domainp (fn-hdc-atom 7) nil)
      (fn-hrcur-cold-domainp (fn-odm-held *rccdt-held* 7) nil))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hrcur-cold-domainp fn-hrcur-dos-domainp
  fn-hdc-abstract fn-hrcur-field fn-hrcur-widthp fn-hrsc-domainp fn-scc-atomp
  fn-scc-nat-encodablep))))
(defthm rccdt-actual-composite-complete-positive
 (and (fn-odm-prefixp 3 *rccdt-composite*)
      (fn-odm-prefixp 5 (fn-odm-at 2 *rccdt-composite*))
      (fn-hrcur-cold-domainp *rccdt-composite* nil)
      (fn-hrcur-cold-domainp (fn-hdc-atom 7) nil)
      (fn-hrcur-cold-domainp (fn-odm-composite *rccdt-composite* 7) nil))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hrcur-cold-domainp fn-hrcur-dos-domainp
  fn-hdc-abstract fn-hrcur-field fn-hrcur-widthp fn-hrsc-domainp fn-scc-atomp
  fn-scc-nat-encodablep))))
; Structural representation witnesses, not authenticated-provider witnesses.
(defthm rccdt-prefix-removal
 (and (natp 4) (not (fn-odm-prefixp 5 (fn-hdc-atom 0)))
      (fn-hrcur-cold-domainp (fn-hdc-atom 0) nil)
      (fn-hrcur-cold-domainp (fn-hdc-atom 7) nil)
      (not (fn-hrcur-cold-domainp (fn-odm-put 4 (fn-hdc-atom 7) (fn-hdc-atom 0)) nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hrcur-cold-domainp fn-hrcur-dos-domainp
  fn-hdc-abstract fn-hrcur-field fn-hrcur-widthp fn-hrsc-domainp fn-scc-atomp
  fn-scc-nat-encodablep fn-odm-put))))
(defthm rccdt-natural-index-removal
 (and (not (natp -1)) (fn-odm-prefixp 0 (fn-hdc-atom 0))
      (fn-hrcur-cold-domainp (fn-hdc-atom 0) nil)
      (fn-hrcur-cold-domainp (fn-hdc-atom 7) nil)
      (not (fn-hrcur-cold-domainp (fn-odm-put -1 (fn-hdc-atom 7) (fn-hdc-atom 0)) nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hrcur-cold-domainp fn-hrcur-dos-domainp
  fn-hdc-abstract fn-hrcur-field fn-hrcur-widthp fn-hrsc-domainp fn-scc-atomp
  fn-scc-nat-encodablep fn-odm-put))))
(defthm rccdt-value-domain-removal-corrupted-representation
 (and (natp 4) (fn-odm-prefixp 5 *rccdt-held*)
      (fn-hrcur-cold-domainp *rccdt-held* nil)
      (not (fn-hrcur-cold-domainp (fn-hdc-atom '(1)) nil))
      (not (fn-hrcur-cold-domainp (fn-odm-put 4 (fn-hdc-atom '(1)) *rccdt-held*) nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hrcur-cold-domainp fn-hrcur-dos-domainp
  fn-hdc-abstract fn-hrcur-field fn-hrcur-widthp fn-hrsc-domainp fn-scc-atomp
  fn-scc-nat-encodablep fn-odm-put))))
(defconst *rccdt-bad-source*
 (fn-hdc-pair (fn-hdc-atom '(1)) (rccdt-spine 15)))
(defthm rccdt-source-domain-removal-corrupted-representation
 (and (natp 4) (fn-odm-prefixp 5 *rccdt-bad-source*)
      (not (fn-hrcur-cold-domainp *rccdt-bad-source* nil))
      (fn-hrcur-cold-domainp (fn-hdc-atom 7) nil)
      (not (fn-hrcur-cold-domainp (fn-odm-put 4 (fn-hdc-atom 7) *rccdt-bad-source*) nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hrcur-cold-domainp fn-hrcur-dos-domainp
  fn-hdc-abstract fn-hrcur-field fn-hrcur-widthp fn-hrsc-domainp fn-scc-atomp
  fn-scc-nat-encodablep fn-odm-put))))
