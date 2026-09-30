(in-package "ACL2")
(include-book "../../books/snapshot-row-source-tagged-refinement")
(defun rcctt-spine (n)
 (declare (xargs :guard (natp n)))
 (if (zp n) (fn-hdc-atom nil)
  (fn-hdc-pair (fn-hdc-atom 0) (rcctt-spine (1- n)))))
(defconst *rcctt-node* (rcctt-spine 16))
(defconst *rcctt-original* (list :decoded *rcctt-node*))
(defconst *rcctt-mapped* (mv-let (mapped ignored) (fn-osm-row-source *rcctt-original* 7) (declare (ignore ignored)) mapped))
(defconst *rcctt-offered*
 (mv-let (ignored next) (fn-hct-offer (fn-hct-begin 1 '(:capture 1) :lease) 0 *rcctt-mapped*) (declare (ignore ignored)) next))
; Structural decoded representation fixture: not actual authenticated parser,
; typed Store capture, profile authority, or runtime allocation evidence.
(defconst *rcctt-expected-row* '(0 0 0 0 7 0 0 0 0 0 0 0 0 0 0 0))
(defthm rcctt-structural-source-complete-positive
 (and (fn-rccs-decoded-row-lineagep *rcctt-original* 7 nil)
      (fn-scc-octet-listp nil)
      (equal (fn-hdc-abstract (fn-omk-at 1 *rcctt-mapped*) nil) *rcctt-expected-row*)
      (< (len (fn-scc-encode *rcctt-expected-row*)) *fn-hrcur-u64-bound*)
      (fn-rcct-current-row-invariantp *rcctt-offered* nil *rcctt-expected-row* nil))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-rccs-decoded-row-lineagep
  fn-rcct-current-row-invariantp fn-hsrcc-invariantp fn-hsrcc-total
  fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-coldp fn-hrcur-cold-invariantp
  fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-rest
  fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest fn-hdc-abstract
  fn-hrcur-cold-domainp fn-hrcur-dos-domainp fn-hrcur-field fn-hrcur-widthp
  fn-hrsc-domainp fn-scc-atomp fn-scc-nat-encodablep))))
(defun rcctt-run (fuel c)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (zp fuel) (mv :exhausted c)
  (mv-let (word ignored next) (fn-hct-tick c)
   (declare (ignore ignored))
   (if (eq word :continue) (rcctt-run (1- fuel) next)
    (mv word next)))))
(assert-event
 (mv-let (word next) (rcctt-run 200 *rcctt-offered*)
  (let ((row *rcctt-expected-row*))
   (and (eq word :row-done) (equal (fn-hrcur-field 2 next) 1)
        (equal (fn-hrcur-field 3 next) (fn-hp-pes-len (list row)))
        (equal (fn-hrcur-field 4 next) nil)
        (equal (fn-hrcur-field 5 next) '(:capture 1))
        (equal (fn-hrcur-field 6 next) :lease)))))
