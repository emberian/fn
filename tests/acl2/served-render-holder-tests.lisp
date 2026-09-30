(in-package "ACL2")
(include-book "../../books/served-render-holder")

(defconst *rh-test-effects*
 '((:log accepted) (:retain source) (:reply (49 50 51))
   (:over-cursor ("fn.test" 1 100000 7 nil t)) (:close)))

(defun-nx rh-test-installed-conclusion (effects pin query resource origin holder)
 (declare (xargs :verify-guards nil))
 (let ((next (mv-nth 1 (fn-rh-producer-install
                        effects pin query resource origin holder))))
  (and (equal (fn-rh-trace next) (fn-splan-of-effects effects))
       (equal (fn-rh-pin next) pin) (equal (fn-rh-query next) query)
       (equal (fn-rh-resource next) resource) (equal (fn-rh-origin next) origin))))

(defthm rh-test-internal-producer-positive
 (let ((holder (create-fn-render-holder)))
  (and (not (fn-rh-live holder))
       (rh-test-installed-conclusion *rh-test-effects* :pin :query :grant :origin holder)))
 :rule-classes nil)

; Omit ONLY vacancy. A live holder must retain its original source/trace;
; replacing it would erase an outstanding response's resource authority.
(defthm rh-test-without-vacancy-corrupted-state
 (let ((holder (mv-nth 1 (fn-rh-producer-install
                         '((:reply (65))) :old-pin :old-query :old-grant :old-origin
                         (create-fn-render-holder)))))
  (and (fn-rh-live holder)
       (not (rh-test-installed-conclusion *rh-test-effects* :pin :query :grant :origin holder))
       (equal (mv-nth 0 (fn-rh-producer-install
                        *rh-test-effects* :pin :query :grant :origin holder)) :busy)))
 :rule-classes nil)

(defthm rh-test-actual-position-full-trace-positive
 (let* ((holder (mv-nth 1 (fn-rh-producer-install
                          *rh-test-effects* :pin :query :grant :origin
                          (create-fn-render-holder))))
        (first (mv-nth 1 (fn-rh-position-one holder)))
        (next (mv-nth 1 (fn-rh-position-one first))))
  (and (equal (fn-rh-status holder) :position)
       (equal (fn-rh-status first) :position)
       (equal (fn-rh-status next) :reply)
       (equal (fn-rh-trace next) (fn-rh-trace holder))
       (equal (fn-rh-pin next) :pin) (equal (fn-rh-query next) :query)
       (equal (fn-rh-resource next) :grant) (equal (fn-rh-origin next) :origin)
       (equal (fn-spp-prefix (fn-rh-plan next))
              '((:retain source) (:log accepted)))))
 :rule-classes nil)

(defthm rh-test-head-output-and-retained-cursor-positive
 (let* ((holder (mv-nth 1 (fn-rh-producer-install
                          '((:reply (49 50 51)) (:over-cursor :retained) (:close))
                          :pin :query :grant :origin (create-fn-render-holder))))
        (actual (fn-rh-head-window 2 nil holder))
        (next (mv-nth 2 actual)))
  (and (equal (fn-rh-status holder) :reply)
       (equal (mv-nth 0 actual) :ok) (equal (mv-nth 1 actual) '(49 50))
       (equal (fn-spp-cur (fn-rh-plan next)) '(51))
       (equal (fn-spp-rest (fn-rh-plan next)) '((:over-cursor :retained) (:close)))
       (equal (fn-rh-pin next) :pin) (equal (fn-rh-query next) :query)
       (equal (fn-rh-resource next) :grant) (equal (fn-rh-origin next) :origin)))
 :rule-classes nil)

(defthm rh-test-without-reply-status-corrupted-state
 (let* ((holder (create-fn-render-holder))
        (actual (fn-rh-head-window 1 nil holder))
        (reference (fn-spp-head-window (fn-rh-plan holder) 1 nil)))
  (and (not (equal (fn-rh-status holder) :reply))
       (not (equal (mv-nth 0 actual) (mv-nth 0 reference)))))
 :rule-classes nil)
