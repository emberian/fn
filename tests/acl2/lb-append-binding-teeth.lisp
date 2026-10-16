; Append binding, including an earlier empty target segment and a wrong-payload fault.
(in-package "ACL2")
(include-book "lb-reclaim-binding-teeth")
(defun fn-lbwa-append-log ()
 (declare (xargs :guard t :verify-guards nil))
 (cons '(1 nil nil)
  (fn-lb-log-model-append (fn-lbw-second-held) *fn-lbw-payload-b* 2
   (fn-lb-log-model-append (fn-lbr13-held) *fn-lbr13-payload* 2 nil))))
(defteeth fn-lb-arena-is-log-of-append
 :claim (((binding (fn-lb-arena-is-log fn-arena rows log)))
  (fn-lb-arena-is-log fn-arena rows
   (fn-lb-log-model-append row (fn-nntp-payload-bytes (fn-record-payload row) fn-arena) target log)))
 :subject fn-lb-log-model-append
 :witness ((arena-mode :good) (rows (fn-lbw-two-rows)) (log (fn-lbwa-append-log))
           (row (fn-lbr13-held)) (target 1))
 :stobjs ((fn-arena (fn-lbwr-reclaim-arena arena-mode fn-arena)))
 :breaks ((binding ((arena-mode :bad-retained))))
 :mutations ((wrong-payload
              (:conclusion (fn-lb-arena-is-log fn-arena rows
                 (fn-lb-log-model-append row *fn-lbw-payload-b* target log)))
              ((arena-mode :good) (rows (fn-lbw-two-rows)) (log (fn-lbwa-append-log))
               (row (fn-lbr13-held)) (target 1))
              :fault "append receives another row's payload before the retained copy")))
