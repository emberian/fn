(in-package "ACL2")
(include-book "../../books/assumptions-selected-runtime-native-constructors")
; MODEL request/coordinate teeth, separate from actual raw constructor fixture.
(encapsulate ()
 (local (assert-event
  (let ((s (car (fn-srnc-unit-row :connection-turn-binding))) (r *fn-srnc-runtime*))
   (and (fn-srnc-unit-coordinate-p :connection-turn-binding s r)
        (equal (fn-srnc-unit-request :connection-turn-binding) 64)
        (equal (fn-srnc-unit-status :connection-turn-binding s r) :native-owned-row)
        (equal (fn-srnc-bound-installation-with-turns-owned-census 1 1 1) 1024)))))
 (local (assert-event
  (let ((r *fn-srnc-runtime*))
   (and (fn-srnc-runtime-p r)
        (not (equal :wrong (car (fn-srnc-unit-row :connection-turn-binding))))
        (not (fn-srnc-unit-coordinate-p :connection-turn-binding :wrong r))
        (equal (fn-srnc-unit-status :connection-turn-binding :wrong r) :unavailable)))))
 (local (assert-event
  (let ((s (car (fn-srnc-unit-row :connection-turn-binding))))
   (and (equal s (car (fn-srnc-unit-row :connection-turn-binding)))
        (not (fn-srnc-runtime-p :wrong))
        (not (fn-srnc-unit-coordinate-p :connection-turn-binding s :wrong))
        (equal (fn-srnc-unit-status :connection-turn-binding s :wrong) :unavailable)))))
 (local (assert-event
  (equal (fn-srnc-bound-installation-with-turns-owned-census 1 1 2) 1088))))
