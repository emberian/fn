(in-package "ACL2")
(include-book "../../books/consumer-remote-wire-charge")
(include-book "consumer-remote-scope-tests")

(defun fn-crwt-witness (fuel answer key g)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (not (member-eq (fn-cp-nth 0 answer) '(:yield :ready))) nil
  (let ((s (fn-cp-nth 1 answer)))
   (and (fn-crw-wirep s)
        (if (or (zp fuel) (eq (car answer) :ready)) t
          (let ((next (fn-crs-tick s key g)))
           (and (member-eq (car next) '(:yield :ready))
                (fn-crw-wirep (fn-cp-nth 1 next))
                (fn-crwt-witness (1- fuel) next key g))))))))
;@positive fn-crs-begin-establishes-exact-wire-charge
;@positive fn-crs-tick-preserves-exact-wire-charge
(assert-event
 (let* ((i (fn-crst-ingress)) (key (fn-crs-key i 7))
        (start (fn-crs-begin i 7 (fn-crst-config nil nil) '((97) (98))))
        (ready (fn-crst-run 80 start key 3)))
  (and (eq (car i) :authenticated) (fn-crw-wirep (fn-cp-nth 1 start))
       (fn-crwt-witness 80 start key 3) (eq (car ready) :ready)
       (equal (fn-cp-nth 17 (fn-cp-nth 1 ready)) 6))))
;@hypothesis-removal fn-crs-begin-establishes-exact-wire-charge authenticated-ingress
(assert-event
 (and (not (eq (car '(:refused :authentication)) :authenticated))
      (not (fn-crw-wirep (fn-cp-nth 1 (fn-crs-begin '(:refused :authentication) 7 nil nil))))))
;@hypothesis-removal fn-crs-tick-preserves-exact-wire-charge maintained-charge
; Corrupted carried scalar, explicitly separate from an external request.
(assert-event
 (let* ((i (fn-crst-ingress)) (key (fn-crs-key i 7))
        (s (update-nth 17 1 (fn-cp-nth 1 (fn-crs-begin i 7 (fn-crst-config nil nil) '((97))))))
        (next (fn-crs-tick s key 3)))
  (and (not (fn-crw-wirep s)) (member-eq (car next) '(:yield :ready))
       (not (fn-crw-wirep (fn-cp-nth 1 next))))))
;@hypothesis-removal fn-crs-tick-preserves-exact-wire-charge non-refused-result
(assert-event
 (let* ((i (fn-crst-ingress))
        (s (fn-cp-nth 1 (fn-crs-begin i 7 (fn-crst-config nil nil) '((97)))))
        (next (fn-crs-tick s '(changed) 3)))
  (and (fn-crw-wirep s) (not (member-eq (car next) '(:yield :ready)))
       (not (fn-crw-wirep (fn-cp-nth 1 next))))))
