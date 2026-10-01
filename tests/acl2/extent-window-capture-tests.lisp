(in-package "ACL2")
(include-book "../../books/extent-window-capture")
(include-book "extent-window-plan-tests")
(include-book "extent-window-buffer-tests")

(defun ewct-capture ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (answer fn-octets)
      (with-local-stobj fn-ew-buffer
        (mv-let (answer fn-ew-buffer fn-octets)
          (let* ((fn-octets (fn-octets-from-list
                             (append (make-list 60 :initial-element 200) '(0 1 2 3)) fn-octets))
                 (fn-ew-buffer (fn-ewb-capture *ewpt-begin* fn-octets fn-ew-buffer))
                 (fn-octets (fn-octets-from-list '(4 5 6 7 8 9) fn-octets))
                 (fn-ew-buffer (fn-ewb-capture *ewpt-last* fn-octets fn-ew-buffer)))
            (mv (list (fn-ew-bytesi 0 fn-ew-buffer) (fn-ew-bytesi 1 fn-ew-buffer)
                      (fn-ew-bytesi 2 fn-ew-buffer) (fn-ew-bytesi 3 fn-ew-buffer)
                      (fn-ew-bytesi 4 fn-ew-buffer) (fn-ew-bytesi 5 fn-ew-buffer)
                      (fn-ew-bytesi 6 fn-ew-buffer) (fn-ew-bytesi 7 fn-ew-buffer)
                      (fn-ew-bytesi 8 fn-ew-buffer) (fn-ew-bytesi 9 fn-ew-buffer)
                      (fn-ew-bytesi 10 fn-ew-buffer)) fn-ew-buffer fn-octets))
          (mv answer fn-octets)))
      answer)))

; Actual concrete capture across a block boundary, only private output.
(assert-event
 (and (equal (ewct-capture) '(0 1 2 3 4 5 6 7 8 9 0))
      (not (fn-ewp-publication *ewpt-last*))
      (not (fn-ewp-publication *ewpt-trailer-state*))
      (not (fn-ewp-publication *ewpt-digest*))))
