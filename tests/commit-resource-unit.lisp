; The commit kind's derived contracts (MACHINE-FORM: the arms are in the
; arm language, so each arm's next phases are derived from its :next steps,
; never stated by hand): every arm moves only along *fn2-commit-transitions*
; from its own phase, every handler only to a phase some live phase may
; reach. Scenario microsteps separately check exact source/destination edges.
(in-package "ACL2")
(include-book "../sim/commit-resources")
(fn2-book-layer :b)
(make-event (value `(defconst *fn2-cru-contracts*
 ',(cdr (assoc-eq 'fn2-commit (table-alist 'fn2-machine-arm-contracts (w state)))))))
(defun fn2-cru-arm-next (tag entries)
 (declare (xargs :verify-guards nil))
 (cond ((atom entries) nil)
       ((eq (caar entries) tag) (fn2-arm-get :next (cddar entries)))
       (t (fn2-cru-arm-next tag (cdr entries)))))
(defun fn2-cru-observer-allowed (states)
 (declare (xargs :verify-guards nil))
 (if (atom states) (strip-cars *fn2-commit-transitions*)
  (intersection-eq (cons (car states) (cdr (assoc-eq (car states) *fn2-commit-transitions*)))
                   (fn2-cru-observer-allowed (cdr states)))))
(defun fn2-cru-audit-arms (entries)
 (declare (xargs :verify-guards nil))
 (if (atom entries) t
  (and (subsetp-eq (fn2-arm-get :next (cddar entries))
                   (cons (caar entries) (cdr (assoc-eq (caar entries) *fn2-commit-transitions*))))
       (fn2-cru-audit-arms (cdr entries)))))
(defun fn2-cru-audit-observers (entries)
 (declare (xargs :verify-guards nil))
 (if (atom entries) t
  (and (subsetp-eq (remove-eq :stay (fn2-arm-get :next (cddar entries)))
                   (fn2-cru-observer-allowed (remove-eq :free (strip-cars *fn2-commit-transitions*))))
       (fn2-cru-audit-observers (cdr entries)))))
(defconst *fn2-cru-arms* (fn2-arm-get :continuations *fn2-cru-contracts*))
(defconst *fn2-cru-observers* (fn2-arm-get :observes *fn2-cru-contracts*))
(assert-event (and (equal (strip-cars *fn2-cru-arms*) (strip-cars *fn2-commit-transitions*))
                   (fn2-cru-audit-arms *fn2-cru-arms*)
                   (equal (strip-cars *fn2-cru-observers*) '(:write-result :fence-result))
                   (fn2-cru-audit-observers *fn2-cru-observers*)))
;; teeth: the derived edges are the ones the pipeline takes
(assert-event
 (and (member-eq :seal (fn2-cru-arm-next :collect *fn2-cru-arms*))
      (member-eq :draining (fn2-cru-arm-next :notify *fn2-cru-arms*))
      (member-eq :free (fn2-cru-arm-next :draining *fn2-cru-arms*))
      (member-eq :uncertain (fn2-cru-arm-next :write-result *fn2-cru-observers*))))
;; the control: a :notify arm that could free its row is refused
(assert-event (not (fn2-cru-audit-arms
 (put-assoc-eq :notify (list* 'fn2-commit-run-notify '(:next (:free))) *fn2-cru-arms*))))
; Independent prefix inventory check over the ACTUAL generated P/V word.
; Reusable holdings return to zero; immutable-root holdings remain declared.
(defun fn2-cru-potential-delta (values)
 (if (atom (cdr values)) 0
  (+ (- (ifix (cadr values)) (ifix (car values))) (fn2-cru-potential-delta (cdr values)))))
(defthm fn2-cru-potential-telescopes
 (equal (fn2-cru-potential-delta values)
  (if (consp values) (- (ifix (car (last values))) (ifix (car values))) 0)))
(defthm fn2-cru-every-cycle-conservative
 (implies (equal (car (last values)) (car values))
          (equal (fn2-cru-potential-delta values) 0)))
(defun fn2-cru-cycle (name word retained)
 (declare (xargs :verify-guards nil))
 (let ((caps (pairlis$ *fn2-commit-resource-order* (make-list (len *fn2-commit-resource-order*) :initial-element 1))))
  (mv-let (ok intervals) (fn2-pv-word word caps 0 1 nil retained)
   (declare (ignore intervals))
   (list (if (and ok (fn2-pv-capsp retained) (fn2-pv-retention-valid retained caps)) :ok :refused) name))))
(defun fn2-cru-drop-release (word resource)
 (declare (xargs :verify-guards nil))
 (if (atom word) nil
  (if (equal (car word) (list :v resource)) (cdr word)
    (cons (car word) (fn2-cru-drop-release (cdr word) resource)))))
(assert-event (equal (fn2-cru-cycle :baseline (fn2-cr-commit-word 0) *fn2-commit-resource-retained*) '(:ok :baseline)))
(assert-event (equal (fn2-cru-cycle :preflush-fua (fn2-cr-commit-word 1) *fn2-commit-resource-retained*) '(:ok :preflush-fua)))
(assert-event (equal (fn2-cru-cycle :baseline-missing-vpool
 (fn2-cru-drop-release (fn2-cr-commit-word 0) :pool) *fn2-commit-resource-retained*) '(:refused :baseline-missing-vpool)))
(assert-event (and (= (len *fn2-commit-seal-stages*) 19)
 (= *fn2-commit-seal-stage-records* 10) (= *fn2-commit-seal-stage-save-seal* 17)
 (= *fn2-commit-seal-stage-hash-seal-frame* 18) (= *fn2-commit-unit-bytes* 4096)
 (= *fn2-commit-write-resources* 3) (= *fn2-commit-pools* 4) (= *fn2-commit-extent-bytes* 12288)
 (= *fn2-commit-frame-trailer* 4063) (= *fn2-commit-frame-digest* 4064)))
(make-event (value `(assert-event
 (and (= ,(fn2-machine-property 'fn2-commit :capacity (w state)) 2)
      (equal ',(fn2-decl-get :init (fn2-decl-row '(:core-child fn2-core-commit-io) (w state)))
             '(fn2-commit-io-init 6 fn2-commit-io))
      (< (+ (* 1 *fn2-commit-write-resources*) (- *fn2-commit-write-resources* 1)) 6)))))

