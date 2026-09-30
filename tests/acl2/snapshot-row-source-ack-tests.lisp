; Structural actual pending/census/ACK execution, not typed Store/auth lineage.
(in-package "ACL2")
(include-book "../../books/snapshot-recovery-census-refinement")
(defconst *rccat-source* '(7 (11 1) 0 0))
(defconst *rccat-original* '(:resident nil))
(defconst *rccat-waiting*
 (mv-let (word next) (fn-osm-offer (fn-osm-begin *rccat-source*) *rccat-source* *rccat-original*) (declare (ignore word)) next))
(defconst *rccat-census*
 (mv-let (word next) (fn-hct-offer (fn-hct-begin 1 '(11 1) :lease) 0
                         (fn-omk-at 1 (fn-omk-at 3 *rccat-waiting*))) (declare (ignore word)) next))
(defun rccat-run (fuel c)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (zp fuel) (mv :exhausted c c)
  (mv-let (word ignored next) (fn-hct-tick c)
   (declare (ignore ignored))
   (if (eq word :continue) (rccat-run (1- fuel) next)
    (mv word c next)))))
(defconst *rccat-before* (mv-let (word before next) (rccat-run 40 *rccat-census*) (declare (ignore word next)) before))
(assert-event
 (mv-let (word before completed) (rccat-run 40 *rccat-census*)
  (declare (ignore before))
  (mv-let (ack next) (fn-osm-census-ack *rccat-waiting* completed)
   (and (eq word :row-done) (eq ack :acknowledged)
        (equal next '(:idle (7 (11 1) 0 1) 0 nil))
        (equal (fn-omk-at 2 completed) 1)
        (equal (fn-omk-at 3 completed) (fn-hp-pes-len '(nil)))
        (equal (fn-omk-at 4 completed) nil)
        (equal (fn-omk-at 5 completed) '(11 1))
        (equal (fn-omk-at 6 completed) :lease)))))
(thm
 (and (fn-rcca-waiting-rowp *rccat-waiting* *rccat-before* nil nil nil)
      (equal (mv-nth 0 (fn-hct-tick *rccat-before*)) :row-done))
 :hints (("Goal" :in-theory
  (enable fn-rcca-waiting-rowp fn-rcct-current-row-invariantp
          fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest
          fn-hsrcb-coldp fn-hrcur-census-invariantp fn-hrcur-census-total
          fn-hrcur-byte-invariantp fn-hrcur-byte-rest))))

(thm
 (fn-rcca-idle-prefixp (fn-osm-begin *rccat-source*)
                       (fn-hct-begin 1 '(11 1) :lease) nil)
 :hints (("Goal" :in-theory (enable fn-rcca-idle-prefixp fn-hct-shapep))))
(defun rccat-source-run (fuel c)
 (declare (xargs :guard (and (natp fuel) (fn-osrc-guardp c))
                 :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :exhausted c)
  (let* ((r (fn-osrc-tick c nil)) (word (car r)))
   (cond ((eq word :yield) (rccat-source-run (1- fuel) (fn-osrc-at 1 r)))
         ((eq word :row) (rccat-source-run (1- fuel) (fn-osrc-at 4 r)))
         (t (mv word c))))))
(defconst *rccat-field* (fn-sl-of '(nil)))
(defconst *rccat-drained*
 (mv-let (word c) (rccat-source-run 20
                   (fn-osrc-begin *rccat-field* (fn-sl-count *rccat-field*) 7 '(11 1)))
  (declare (ignore word)) c))
(defconst *rccat-completed*
 (mv-let (word before next) (rccat-run 40 *rccat-census*)
  (declare (ignore word before)) next))
(defconst *rccat-acked*
 (mv-let (word next) (fn-osm-census-ack *rccat-waiting* *rccat-completed*)
  (declare (ignore word)) next))
(defconst *rccat-descriptor*
 (list :recovery-census '(:recovery-source 11 7 4) 7 2 :structural-store
       *rccat-field* 1 7 nil))
(defconst *rccat-collector*
 (fn-rcc-state :census *rccat-descriptor* *rccat-acked* *rccat-completed*
               :original-context :original-fields nil :lease))
(assert-event
 (mv-let (word measured next) (fn-rcc-readout *rccat-collector* *rccat-drained*
                                            *rccat-acked* *rccat-completed*)
  (and (eq word :measured)
       (equal measured
        (list :measured '(:recovery-source 11 7 4) 1 (fn-hp-pes-len '(nil))
              :original-context :original-fields nil))
       (equal (fn-omk-at 0 next) :measured))))
(thm
 (and (fn-rcca-idle-prefixp *rccat-acked* *rccat-completed* '(nil))
      (equal (mv-nth 0 (fn-rcc-readout *rccat-collector* *rccat-drained*
                                      *rccat-acked* *rccat-completed*)) :measured))
 :hints (("Goal" :in-theory (enable fn-rcca-idle-prefixp fn-hct-shapep))))
