; Concrete private per-response positioning holder. PRF-1066 component.
; Only the registered producer may call the internal constructor. This book
; does not authorize a host-supplied plan, publication, query or resource.
(in-package "ACL2")
(include-book "served-plan-head-window")

(defstobj fn-render-holder
 (fn-rh-live :type t :initially nil)
 (fn-rh-plan :type t :initially nil)
 (fn-rh-pin :type t :initially nil)
 (fn-rh-query :type t :initially nil)
 (fn-rh-resource :type t :initially nil)
 (fn-rh-origin :type t :initially nil)
 :inline t)

; Internal producer endpoint, deliberately absent from the host callback
; roster. Matching registered publication/query/grant is the producer's
; establishment obligation, not a :ready argument supplied by the host.
(defun fn-rh-producer-install-positioned (positioned pin query resource origin fn-render-holder)
 (declare (xargs :stobjs fn-render-holder :guard t))
 (if (fn-rh-live fn-render-holder)
  (mv :busy fn-render-holder)
  (let* ((fn-render-holder
           (update-fn-rh-plan
             positioned fn-render-holder))
         (fn-render-holder (update-fn-rh-pin pin fn-render-holder))
         (fn-render-holder (update-fn-rh-query query fn-render-holder))
         (fn-render-holder (update-fn-rh-resource resource fn-render-holder))
         (fn-render-holder (update-fn-rh-origin origin fn-render-holder))
         (fn-render-holder (update-fn-rh-live t fn-render-holder)))
   (mv :installed fn-render-holder))))

(defun fn-rh-producer-install (effects pin query resource origin fn-render-holder)
 (declare (xargs :stobjs fn-render-holder :guard t))
 (if (fn-rh-live fn-render-holder) (mv :busy fn-render-holder)
  (fn-rh-producer-install-positioned
   (fn-spp-begin (fn-splan-of-effects effects) origin resource)
   pin query resource origin fn-render-holder)))

(defun fn-rh-status (fn-render-holder)
 (declare (xargs :stobjs fn-render-holder :guard t))
 (if (fn-rh-live fn-render-holder)
     (fn-spp-status (fn-rh-plan fn-render-holder)) :unavailable))

; Exactly one positioning action; no recursive search for the next effect.
(defun fn-rh-position-one (fn-render-holder)
 (declare (xargs :stobjs fn-render-holder :guard t))
 (if (not (fn-rh-live fn-render-holder))
  (mv :unavailable fn-render-holder)
  (let ((fn-render-holder
         (update-fn-rh-plan (fn-spp-one (fn-rh-plan fn-render-holder))
                            fn-render-holder)))
   (mv (fn-rh-status fn-render-holder) fn-render-holder))))

; W is the admitted quantum/capacity. Source ownership is retained even on
; non-reply or zero-capacity calls; release requires the separate actual
; completion/cancel/join producer, which is not implemented by this book.
(defun fn-rh-head-window (w fn-octets fn-render-holder)
 (declare (xargs :stobjs (fn-octets fn-render-holder) :guard (natp w)))
 (if (not (eq (fn-rh-status fn-render-holder) :reply))
  (mv :not-reply fn-octets fn-render-holder)
  (mv-let (status plan fn-octets)
    (fn-spp-head-window (fn-rh-plan fn-render-holder) w fn-octets)
   (let ((fn-render-holder (update-fn-rh-plan plan fn-render-holder)))
    (mv status fn-octets fn-render-holder)))))

; Logical boundary only: reconstructing the skipped prefix is never a hot
; getter or callback, and the host never receives the stored plan.
(defun-nx fn-rh-trace (fn-render-holder)
 (declare (xargs :stobjs fn-render-holder :guard t :verify-guards nil))
 (fn-spp-plan (fn-rh-plan fn-render-holder)))

(local
 (defthm fn-rh-nth-update
  (implies (and (natp i) (natp j))
   (equal (nth i (update-nth j value xs))
          (if (equal i j) value (nth i xs))))
  :hints (("Goal" :induct (update-nth j value xs)))))

(defthm fn-rh-installed-positioned-plan-is-same-registered-plan
 (implies (not (fn-rh-live fn-render-holder))
  (let ((next (mv-nth 1 (fn-rh-producer-install-positioned
                        positioned pin query resource origin fn-render-holder))))
   (and (equal (fn-rh-plan next) positioned)
        (equal (fn-rh-pin next) pin)
        (equal (fn-rh-query next) query)
        (equal (fn-rh-resource next) resource)
        (equal (fn-rh-origin next) origin))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rh-producer-install-positioned) (nth update-nth nth-add1)))))

(defthm fn-rh-installed-plan-is-exact-producer-effect-trace
 (implies (not (fn-rh-live fn-render-holder))
  (let ((next (mv-nth 1 (fn-rh-producer-install
                        effects pin query resource origin fn-render-holder))))
   (and (equal (fn-rh-trace next) (fn-splan-of-effects effects))
        (equal (fn-rh-pin next) pin)
        (equal (fn-rh-query next) query)
        (equal (fn-rh-resource next) resource)
        (equal (fn-rh-origin next) origin))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-rh-producer-install fn-rh-producer-install-positioned fn-rh-trace
                            fn-splan-of-effects)
                           (nth update-nth nth-add1)))))

(defthm fn-rh-position-preserves-complete-trace-and-ownership
 (let ((next (mv-nth 1 (fn-rh-position-one fn-render-holder))))
  (and (equal (fn-rh-trace next) (fn-rh-trace fn-render-holder))
       (equal (fn-rh-pin next) (fn-rh-pin fn-render-holder))
       (equal (fn-rh-query next) (fn-rh-query fn-render-holder))
       (equal (fn-rh-resource next) (fn-rh-resource fn-render-holder))
       (equal (fn-rh-origin next) (fn-rh-origin fn-render-holder))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-rh-position-one fn-rh-trace)
                               (nth update-nth nth-add1)))))

(defthm fn-rh-head-window-is-stored-plan-window-with-retained-ownership
 (implies (eq (fn-rh-status fn-render-holder) :reply)
  (let* ((old-plan (fn-rh-plan fn-render-holder))
         (actual (fn-rh-head-window w fn-octets fn-render-holder))
         (reference (fn-spp-head-window old-plan w fn-octets))
         (next (mv-nth 2 actual)))
   (and (equal (mv-nth 0 actual) (mv-nth 0 reference))
        (equal (mv-nth 1 actual) (mv-nth 2 reference))
        (equal (fn-rh-plan next) (mv-nth 1 reference))
        (equal (fn-rh-live next) (fn-rh-live fn-render-holder))
        (equal (fn-rh-pin next) (fn-rh-pin fn-render-holder))
        (equal (fn-rh-query next) (fn-rh-query fn-render-holder))
        (equal (fn-rh-resource next) (fn-rh-resource fn-render-holder))
        (equal (fn-rh-origin next) (fn-rh-origin fn-render-holder)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-rh-head-window fn-rh-status)
                               (fn-spp-head-window nth update-nth nth-add1)))))
