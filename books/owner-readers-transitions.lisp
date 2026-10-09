; Exact capture/cache compositions; no new selection policy.
(in-package "ACL2")
(include-book "owner-readers-state")
(include-book "owner-reader-view")
(defun fn-ordr-capture (r event current)
  (declare (xargs :guard t))
  (fn-ordr-put :views (fn-ocv-capture (fn-ordr-views r) event current) r))
(defun fn-ordr-cache-install (r cache)
  (declare (xargs :guard t))
  (fn-ordr-put :cache cache r))
(defthm fn-ordr-capture-composition-by-definition
  (equal (fn-ordr-capture r event current)
         (list (fn-ocv-capture (fn-ordr-views r) event current) (fn-ordr-cache r)))
  :hints (("Goal" :in-theory (e/d (fn-ordr-make) (fn-ocv-capture))))
  :rule-classes nil)
(defthm fn-ordr-cache-install-composition-by-definition
  (equal (fn-ordr-cache-install r cache) (list (fn-ordr-views r) cache))
  :hints (("Goal" :in-theory (enable fn-ordr-make)))
  :rule-classes nil)
(defthm fn-ordr-capture-frames-cache
  (equal (fn-ordr-cache (fn-ordr-capture r event current)) (fn-ordr-cache r)))
(defthm fn-ordr-cache-install-frames-views
  (equal (fn-ordr-views (fn-ordr-cache-install r cache)) (fn-ordr-views r)))
(defthm fn-ordr-capture-preserves-shape
  (fn-ordr-shapep (fn-ordr-capture r event current)))
(defthm fn-ordr-cache-install-preserves-shape
  (fn-ordr-shapep (fn-ordr-cache-install r cache)))
(in-theory (disable fn-ordr-capture fn-ordr-cache-install fn-ordr-index-kind))
