; Internal producer-owned range control header, shared provider slot ABI.
; No host callback takes this list and no source authority is manufactured.
(in-package "ACL2")
(include-book "served-render-holder")

; (:fn-ibr ticket capture-generation phase plan pin group number ordinal).
; The last three cursors are installed only from the retained publication
; and maintained number root by the later admitted source transition.
(defun fn-ibr-make (ticket generation phase plan pin group number ordinal)
 (declare (xargs :guard t))
 (list :fn-ibr ticket generation phase plan pin group number ordinal))

(defun fn-ibr-begin (ticket generation effects pin resource origin)
 (declare (xargs :guard t))
 (fn-ibr-make ticket generation :position
  (fn-spp-begin (fn-splan-of-effects effects) origin resource) pin nil nil nil))

(defun fn-ibr-position-one (control)
 (declare (xargs :guard t))
 (if (and (equal (fn-spp-at 0 control) :fn-ibr)
          (equal (fn-spp-at 3 control) :position))
  (fn-ibr-make (fn-spp-at 1 control) (fn-spp-at 2 control) :position
   (fn-spp-one (fn-spp-at 4 control)) (fn-spp-at 5 control)
   (fn-spp-at 6 control) (fn-spp-at 7 control) (fn-spp-at 8 control))
  control))

(defun fn-ibr-position-status (control)
 (declare (xargs :guard t))
 (if (and (equal (fn-spp-at 0 control) :fn-ibr)
          (equal (fn-spp-at 3 control) :position))
     (fn-spp-status (fn-spp-at 4 control)) :unavailable))

; Called ONLY after the shared request producer admits the registered
; control/source/grant. This internal bridge borrows the same positioned
; plan; it neither rebuilds the effects nor manufactures a second budget.
(defun fn-ibr-render-install (control fn-render-holder)
 (declare (xargs :stobjs fn-render-holder :guard t))
 (if (and (equal (fn-spp-at 0 control) :fn-ibr)
          (equal (fn-spp-at 3 control) :position))
  (let ((plan (fn-spp-at 4 control)))
   (fn-rh-producer-install-positioned
     plan (fn-spp-at 5 control) (fn-spp-at 1 control)
     (fn-spp-resource plan) (fn-spp-origin plan) fn-render-holder))
  (mv :unavailable fn-render-holder)))

(defthm fn-ibr-begin-keeps-actual-effect-trace-and-header
 (let ((control (fn-ibr-begin ticket generation effects pin resource origin)))
  (and (equal (fn-spp-at 0 control) :fn-ibr)
       (equal (fn-spp-at 1 control) ticket)
       (equal (fn-spp-at 2 control) generation)
       (equal (fn-spp-at 5 control) pin)
       (equal (fn-spp-plan (fn-spp-at 4 control)) (fn-splan-of-effects effects))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-ibr-begin fn-ibr-make
                                   fn-spp-at fn-ag-car fn-ag-cdr fn-splan-of-effects))))

(defthm fn-ibr-position-keeps-actual-effect-trace-and-source-coordinates
 (let ((next (fn-ibr-position-one control)))
  (and (equal (fn-spp-plan (fn-spp-at 4 next))
              (fn-spp-plan (fn-spp-at 4 control)))
       (equal (fn-spp-at 1 next) (fn-spp-at 1 control))
       (equal (fn-spp-at 2 next) (fn-spp-at 2 control))
       (equal (fn-spp-at 5 next) (fn-spp-at 5 control))
       (equal (fn-spp-at 6 next) (fn-spp-at 6 control))
       (equal (fn-spp-at 7 next) (fn-spp-at 7 control))
       (equal (fn-spp-at 8 next) (fn-spp-at 8 control))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-ibr-position-one fn-ibr-make
                                    fn-spp-at fn-ag-car fn-ag-cdr)
                                   (fn-spp-one fn-spp-plan)))))

(defthm fn-ibr-render-installs-same-registered-control-plan
 (implies (and (equal (fn-spp-at 0 control) :fn-ibr)
               (equal (fn-spp-at 3 control) :position)
               (not (fn-rh-live fn-render-holder)))
  (let* ((next (mv-nth 1 (fn-ibr-render-install control fn-render-holder)))
         (plan (fn-spp-at 4 control)))
   (and (equal (fn-rh-plan next) plan)
        (equal (fn-rh-pin next) (fn-spp-at 5 control))
        (equal (fn-rh-query next) (fn-spp-at 1 control))
        (equal (fn-rh-resource next) (fn-spp-resource plan))
        (equal (fn-rh-origin next) (fn-spp-origin plan)))))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-rh-installed-positioned-plan-is-same-registered-plan
    (positioned (fn-spp-at 4 control)) (pin (fn-spp-at 5 control))
    (query (fn-spp-at 1 control)) (resource (fn-spp-resource (fn-spp-at 4 control)))
    (origin (fn-spp-origin (fn-spp-at 4 control)))))
  :in-theory (e/d (fn-ibr-render-install) (fn-rh-producer-install-positioned)))))
