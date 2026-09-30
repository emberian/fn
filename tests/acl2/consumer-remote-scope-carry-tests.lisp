(in-package "ACL2")
(include-book "../../books/consumer-remote-scope-carry-model")

; Fixture only: authenticated ingress is the preceding producer's output.
(defun fn-crsct-ingress ()
 (declare (xargs :guard t))
 (list :authenticated (list :remote-consumer :register '(97) '(99) '(105) '((97) (98)) nil 0)
       '(97) '(1 2) '(3) 4 5))

(defun fn-crsct-start ()
 (declare (xargs :guard t))
 (fn-crs-begin (fn-crsct-ingress) 7
  (fn-inj-make-config-full t nil '((97) (98)) 4096 (list nil nil nil nil) nil) '((97) (98))))

(defun fn-crsct-witness (fuel answer key)
 (declare (xargs :guard (natp fuel) :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 answer) :yield))) answer
  (let* ((s (fn-cp-nth 1 answer)) (next (fn-crs-tick s key 2)))
   (if (and (fn-crsc-invariant s)
             (member-eq (fn-cp-nth 0 next) '(:yield :ready))
             (fn-crsc-invariant (fn-cp-nth 1 next)))
       (fn-crsct-witness (1- fuel) next key) '(:broken)))))

;@positive fn-crs-begin-establishes-complete-query-annotation
;@positive fn-crs-tick-preserves-complete-query-annotation
;@positive fn-crs-finish-carries-exact-complete-query-annotation
(assert-event
 (let* ((i (fn-crsct-ingress)) (key (fn-crs-key i 7)) (start (fn-crsct-start))
        (end (fn-crsct-witness 80 start key)) (s (fn-cp-nth 1 end)) (out (fn-crs-finish s key)))
  (and (eq (fn-cp-nth 0 i) :authenticated) (fn-crsc-invariant (fn-cp-nth 1 start))
       (eq (fn-cp-nth 0 end) :ready) (fn-crsc-invariant s)
       (equal (fn-cp-nth 1 s) key) (eq (fn-cp-nth 3 s) :ready)
       (eq (fn-cp-nth 0 out) :definition) (equal (fn-cp-nth 1 out) '((97) (98)))
       (equal (fn-cp-nth 2 out) (fn-caam-list-annotation (fn-cp-nth 1 out)))
       (equal (fn-caac-list-carry (fn-cp-nth 2 out)) (fn-scs-summary (fn-cp-nth 1 out))))))

;@hypothesis-removal fn-crs-begin-establishes-complete-query-annotation authenticated
(assert-event
 (let ((i '(:refused :authentication)))
  (and (not (eq (fn-cp-nth 0 i) :authenticated))
       (not (fn-crsc-invariant (fn-cp-nth 1 (fn-crs-begin i 7 nil nil)))))))

;@hypothesis-removal fn-crs-tick-preserves-complete-query-annotation carried-invariant
; Corrupted-state witness: exact key and accepted result retained.
(assert-event
 (let* ((s (fn-crs-state '(1) '(97) :reverse nil nil nil nil nil nil nil nil 1
                         '((97)) nil nil nil 3)) (out (fn-crs-tick s '(1) 2)))
  (and (not (fn-crsc-invariant s)) (member-eq (fn-cp-nth 0 out) '(:yield :ready))
       (not (fn-crsc-invariant (fn-cp-nth 1 out))))))

;@hypothesis-removal fn-crs-tick-preserves-complete-query-annotation accepted-result
(assert-event
 (let* ((s (fn-cp-nth 1 (fn-crsct-start))) (out (fn-crs-tick s '(changed) 2)))
  (and (fn-crsc-invariant s) (not (member-eq (fn-cp-nth 0 out) '(:yield :ready)))
       (not (fn-crsc-invariant (fn-cp-nth 1 out))))))

;@hypothesis-removal fn-crs-finish-carries-exact-complete-query-annotation carried-invariant
; Corrupted-state witness: key and ready retained, wrong full annotation.
(assert-event
 (let* ((s (fn-crs-state '(1) '(97) :ready nil nil nil nil nil nil nil nil 1 nil nil '((97)) nil 3))
        (out (fn-crs-finish s '(1))))
  (and (not (fn-crsc-invariant s)) (equal (fn-cp-nth 1 s) '(1)) (eq (fn-cp-nth 3 s) :ready)
       (not (equal (fn-cp-nth 2 out) (fn-caam-list-annotation (fn-cp-nth 1 out)))))))

;@hypothesis-removal fn-crs-finish-carries-exact-complete-query-annotation current-key
(assert-event
 (let* ((key (fn-crs-key (fn-crsct-ingress) 7)) (s (fn-cp-nth 1 (fn-crsct-witness 80 (fn-crsct-start) key)))
        (out (fn-crs-finish s '(changed))))
  (and (fn-crsc-invariant s) (not (equal (fn-cp-nth 1 s) '(changed))) (eq (fn-cp-nth 3 s) :ready)
       (not (eq (fn-cp-nth 0 out) :definition)))))

;@hypothesis-removal fn-crs-finish-carries-exact-complete-query-annotation ready
(assert-event
 (let* ((s (fn-cp-nth 1 (fn-crsct-start))) (key (fn-cp-nth 1 s)) (out (fn-crs-finish s key)))
  (and (fn-crsc-invariant s) (equal (fn-cp-nth 1 s) key) (not (eq (fn-cp-nth 3 s) :ready))
       (not (eq (fn-cp-nth 0 out) :definition)))))
