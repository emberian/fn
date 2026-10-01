(in-package "ACL2")
(include-book "../../books/admission-semantic-census-prefix")
(defconst *rccap-test-source* '(7 (11 1) 0 0))
(defconst *rccap-test-remapper* (fn-osm-begin *rccap-test-source*))
(defconst *rccap-test-census* (fn-hct-begin 1 '(11 1) :lease))
(defconst *rccap-test-waiting*
 (mv-let (word next) (fn-osm-offer *rccap-test-remapper* *rccap-test-source* '(:resident nil)) (declare (ignore word)) next))
(defconst *rccap-test-offered*
 (mv-let (word next) (fn-hct-offer *rccap-test-census* 0 '(:resident nil)) (declare (ignore word)) next))
(defun rccap-test-run (fuel c)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (zp fuel) (mv :exhausted c c)
  (mv-let (word ignored next) (fn-hct-tick c)
   (declare (ignore ignored))
   (if (eq word :continue) (rccap-test-run (1- fuel) next)
    (mv word c next)))))
(defconst *rccap-test-before* (mv-let (word before next) (rccap-test-run 40 *rccap-test-offered*) (declare (ignore word next)) before))
; Literal complete positive antecedent and result for the actual ACK boundary.
(thm
 (let* ((c *rccap-test-before*) (r *rccap-test-waiting*)
        (completed (mv-nth 2 (fn-hct-tick c)))
        (next (mv-nth 1 (fn-osm-census-ack r completed))))
  (and (fn-rccap-waiting-original-prefixp r c nil nil nil nil)
       (eq (mv-nth 0 (fn-hct-tick c)) :row-done)
       (fn-rccap-idle-original-prefixp next completed '(nil))
       (equal next '(:idle (7 (11 1) 0 1) 0 nil))
       (equal (fn-omk-at 3 completed) (fn-hp-pes-len '(nil)))))
 :hints (("Goal" :in-theory (enable fn-rccap-waiting-original-prefixp
  fn-rccap-idle-original-prefixp fn-rccap-remapped-prefix fn-rcca-waiting-rowp
  fn-rcca-idle-prefixp fn-rcct-current-row-invariantp fn-hsrcc-invariantp
  fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-coldp
  fn-hrcur-census-invariantp fn-hrcur-census-total fn-hrcur-byte-invariantp
  fn-hrcur-byte-rest fn-hct-shapep))))
; Positive terminal target witness: original list, actual transformed list,
; ordinal and HCT completion are checked together.
(thm
 (let* ((target '(nil)) (c *rccap-test-before*)
        (completed (mv-nth 2 (fn-hct-tick c)))
        (next (mv-nth 1 (fn-osm-census-ack *rccap-test-waiting* completed))))
  (and (true-listp target) (equal 1 (len target))
       (fn-rccap-idle-original-prefixp next completed (take 1 target))
       (eq (fn-omk-at 0 completed) :prepared)
       (equal (fn-omk-at 2 completed) (len target))
       (equal (fn-omk-at 3 (fn-omk-at 1 next)) (len target))
       (equal (fn-omk-at 3 completed)
              (fn-hp-pes-len (mv-nth 0 (fn-rccap-remapped-prefix target 0))))))
 :hints (("Goal" :in-theory (enable fn-rccap-idle-original-prefixp
  fn-rccap-remapped-prefix fn-rcca-idle-prefixp fn-hct-shapep))))
