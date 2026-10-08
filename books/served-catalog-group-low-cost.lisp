; The cost of GROUP's low at the top view (lane s-group-low, 2026-10-08).
;
; The executable of fn-scat-group-low reads the catalog's maintained raw low
; at the top view: fn-scat-top-viewp (a count compare and the horizon cell)
; and fn-scat-group-low-top (one probe).  Neither has a size term: the cost
; is a constant whatever the group's withdrawn or reclaimed prefix is.  Below
; the top view the probe pass answers, at the cost of the leading non-kept
; numbers; fn-scat-group-low's own twin is not stated here because it holds
; that pass.
(in-package "ACL2")
(include-book "def-cost")
(include-book "served-catalog")

(def-cost fn-scat-group-low-top :visits 1)
(def-cost fn-scat-top-viewp :visits 2)

; KEYSTONE.  The top view's arm of GROUP's low costs at most three visits
; (the top-view test's two, the probe's one), with no size term: nothing
; here depends on the group's withdrawn or reclaimed prefix.
(defthm fn-scat-group-low-top-arm-visits
  (implies (and (fn-cat-p fn-cat) (natp v))
           (<= (+ (fn-scat-top-viewp-route-visits v fn-cat)
                  (fn-scat-group-low-top-route-visits group fn-cat))
               3))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-scat-top-viewp-visits-bound (fn-cat-v fn-cat))
                        (:instance fn-scat-group-low-top-visits-bound (fn-cat-v fn-cat)))
           :in-theory (disable fn-scat-top-viewp-route-visits fn-scat-group-low-top-route-visits))))

(def-cost-check fn-scat-group-low-top)
(def-cost-check fn-scat-top-viewp)
