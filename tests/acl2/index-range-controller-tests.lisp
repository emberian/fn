(in-package "ACL2")
(include-book "../../books/index-range-controller")

(defconst *ibr-test-effects*
 '((:log accepted) (:retain source) (:over-cursor ("fn.test" 1 8 7 nil t)) (:close)))
(defconst *ibr-test-control*
 (fn-ibr-begin '(:index-query 3 0 0 7) 7 *ibr-test-effects* :actual-pin :grant :origin))

(defun-nx ibr-test-installed-conclusion (control holder)
 (declare (xargs :verify-guards nil))
 (let* ((next (mv-nth 1 (fn-ibr-render-install control holder)))
        (plan (fn-spp-at 4 control)))
  (and (equal (fn-rh-plan next) plan)
       (equal (fn-rh-pin next) (fn-spp-at 5 control))
       (equal (fn-rh-query next) (fn-spp-at 1 control))
       (equal (fn-rh-resource next) (fn-spp-resource plan))
       (equal (fn-rh-origin next) (fn-spp-origin plan)))))

; This internal constructor fixture is conditional source evidence, not
; ingress/publication/query admission or native authorization evidence.
(defthm ibr-test-actual-producer-position-holder-positive
 (let* ((control (fn-ibr-position-one (fn-ibr-position-one *ibr-test-control*)))
        (holder (create-fn-render-holder))
        (next (mv-nth 1 (fn-ibr-render-install control holder))))
  (and (equal (fn-spp-at 0 control) :fn-ibr)
       (equal (fn-spp-at 3 control) :position) (not (fn-rh-live holder))
       (ibr-test-installed-conclusion control holder)
       (equal (fn-rh-status next) :cursor)
       (equal (fn-rh-trace next) (fn-splan-of-effects *ibr-test-effects*))
       (equal (fn-rh-query next) '(:index-query 3 0 0 7))
       (equal (fn-spp-at 2 control) 7)
       (equal (fn-rh-pin next) :actual-pin)))
 :rule-classes nil)

(defthm ibr-test-without-range-header-corrupted-state
 (let ((control (cons :wrong (cdr *ibr-test-control*)))
       (holder (create-fn-render-holder)))
  (and (not (equal (fn-spp-at 0 control) :fn-ibr))
       (equal (fn-spp-at 3 control) :position) (not (fn-rh-live holder))
       (not (ibr-test-installed-conclusion control holder))))
 :rule-classes nil)

(defthm ibr-test-without-position-phase-corrupted-state
 (let ((control (update-nth 3 :wrong *ibr-test-control*))
       (holder (create-fn-render-holder)))
  (and (equal (fn-spp-at 0 control) :fn-ibr)
       (not (equal (fn-spp-at 3 control) :position)) (not (fn-rh-live holder))
       (not (ibr-test-installed-conclusion control holder))))
 :rule-classes nil)

(defthm ibr-test-without-vacancy-corrupted-state
 (let ((control *ibr-test-control*)
       (holder (mv-nth 1 (fn-rh-producer-install
                         '((:reply (65))) :other-pin :other-query :other-grant :other-origin
                         (create-fn-render-holder)))))
  (and (equal (fn-spp-at 0 control) :fn-ibr)
       (equal (fn-spp-at 3 control) :position) (fn-rh-live holder)
       (not (ibr-test-installed-conclusion control holder))))
 :rule-classes nil)
