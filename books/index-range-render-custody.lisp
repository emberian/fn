; Actual internal RH custody boundary. Registered context provenance and
; producer/capture/terminal/runtime activation remain separate obligations.
(in-package "ACL2")
(include-book "index-range-controller")
(include-book "receiver-render-custody")

(defun fn-ibr-registered-render-custody-install
 (control query custody fn-render-holder)
 (declare (xargs :stobjs fn-render-holder :guard t))
 (cond
  ((fn-rh-live fn-render-holder) (mv :busy custody fn-render-holder))
  ((not (and (equal (fn-spp-at 0 control) :fn-ibr)
              (equal (fn-spp-at 3 control) :position)
              (equal (fn-spp-at 1 query) (fn-spp-at 1 control))
              (equal (fn-spp-at 4 query) (fn-spp-at 2 control))))
   (mv :unavailable custody fn-render-holder))
  (t
   (let ((plan (fn-spp-at 4 control)))
    (mv-let (word candidate)
     (fn-ric-custody-render-acquire custody t plan (fn-spp-at 5 control)
                  query (fn-spp-resource plan) (fn-spp-origin plan))
     (if (not (eq word :render-acquired))
         (mv word custody fn-render-holder)
       (mv-let (installed fn-render-holder)
        (fn-ibr-registered-render-install control query fn-render-holder)
        ; Never rollback or grant terminal credit on an escape. The actual
        ; registered caller persists candidate only after installed, otherwise
        ; retains source/grant and freezes with this recovery evidence.
        (mv (if (eq installed :installed) :installed :recovery-required)
             candidate fn-render-holder))))))))

(local
 (defthm fn-ibr-custody-nth-update
  (implies (and (natp i) (natp j))
   (equal (nth i (update-nth j value xs))
          (if (equal i j) value (nth i xs))))
  :hints (("Goal" :induct (update-nth j value xs)))))

(defthm fn-ibr-render-custody-root-is-actual-installed-holder
 (let* ((result (fn-ibr-registered-render-custody-install
                   control query custody fn-render-holder))
        (row (mv-nth 1 result)) (next (mv-nth 2 result)))
  (implies (eq (mv-nth 0 result) :installed)
   (equal (fn-omk-at 8 row)
          (list :receiver-render-root (fn-rh-live next) (fn-rh-plan next)
                 (fn-rh-pin next) (fn-rh-query next) (fn-rh-resource next)
                 (fn-rh-origin next)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (e/d (fn-ibr-registered-render-custody-install
        fn-ibr-registered-render-install fn-rh-producer-install-positioned
        fn-ric-custody-render-acquire fn-omk-at)
       (fn-ibp-query-tokenp fn-omk-widthp fn-spp-resource fn-spp-origin fn-spp-at
        nth update-nth nth-add1)))))
