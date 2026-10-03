(in-package "ACL2")
(include-book "../../books/page-read-startup")

(defconst *prst-plan* (fn-prstartup-plan 536870912 67108864 268435456 "/tmp/store" 4 1048576 4194304 8 256))
(assert-event (and (fn-prstartup-planp *prst-plan*)
  (equal (fn-prstartup-file-capacity *prst-plan*) 256)
  (equal (fn-prstartup-cache-capacity *prst-plan*) 256)
  (equal (fn-prstartup-decoded-workers *prst-plan*) 4)
  (<= (fn-prstartup-required-heap 256 4 "/tmp/store") 268435456)))
(assert-event (equal (fn-prstartup-status (fn-prstartup-plan 1024 0 0 "/tmp/store" 4 1048576 4194304 8 256)) :refused))
(assert-event (equal (fn-prstartup-status (fn-prstartup-plan 536870912 67108864 268435456 "/tmp/store" 4 1048576 4194304 8 8)) :refused))
(assert-event (not (fn-prstartup-planp (update-nth 2 '(0 0 0 0 0) *prst-plan*))))
(assert-event (equal (fn-prstartup-decoded-workers (update-nth 2 '(0 0 0 0 0) *prst-plan*)) 0))
(assert-event (and (equal (fn-prstartup-status '(garbage)) :fault)
                  (equal (fn-prstartup-install-status :invalid-default-pool-plan) :fault)
                  (equal (fn-prstartup-install-status :invalid-resource-profile) :fault)
                  (equal (fn-prstartup-install-status :already-installed) :refused)))

; Literal positive and antecedent-removal teeth for the actual admitted plan.
(assert-event
 (and (equal (fn-prstartup-nth 0 *prst-plan*) :admitted)
      (natp (fn-prstartup-file-capacity *prst-plan*))
      (<= (max 8 (+ 1 (nfix 8))) (fn-prstartup-file-capacity *prst-plan*))
      (<= (fn-prstartup-file-capacity *prst-plan*) 256)
      (<= (fn-prstartup-required-heap (fn-prstartup-file-capacity *prst-plan*) 4 "/tmp/store")
          (nfix (- 536870912 (max 67108864 268435456))))))
(assert-event
 (let ((plan (fn-prstartup-plan 1024 0 0 "/tmp/store" 4 1048576 4194304 8 256)))
  (and (not (equal (fn-prstartup-nth 0 plan) :admitted))
       (not (<= (fn-prstartup-required-heap (fn-prstartup-file-capacity plan) 4 "/tmp/store")
                1024)))))

; A launcher that reserved only the protected figure has no default backing.
; The exact DEFAULT contribution makes the minimum selected pool affordable.
(defconst *prst-launch-base* '(:heap 256 "custom" 8192 1024 20))
(defconst *prst-launch*
 (fn-prstartup-extend-operation-reservation *prst-launch-base* :run nil "/tmp/store" 4 8
                                           '(83886080 . 67108864) '(8589934592)))
(assert-event
 (and (equal (fn-prstartup-nth 0 *prst-launch*) :heap)
      (equal (fn-prstartup-nth 1 *prst-launch*) 257)
      (equal (fn-prstartup-nth 4 *prst-launch*) 1024)
      (equal (fn-prstartup-nth 5 *prst-launch*) 20)
      (<= (fn-heap-reservation-octets (fn-prstartup-nth 1 *prst-launch*)
             '(83886080 . 67108864) (fn-prstartup-nth 4 *prst-launch*) (fn-prstartup-nth 5 *prst-launch*))
          (fn-heap-machine-octets '(8589934592)))
      (equal (fn-prstartup-status
              (fn-prstartup-plan 268435456 67108864 268435456 "/tmp/store" 4 1048576 4194304 8 256)) :refused)
      (fn-prstartup-planp
       (fn-prstartup-plan (* 1048576 (fn-prstartup-nth 1 *prst-launch*)) 67108864 268435456
                           "/tmp/store" 4 1048576 4194304 8 256))))
(assert-event
 (and (equal (fn-prstartup-extend-operation-reservation *prst-launch-base* :status nil "/tmp/store" 4 8
                                                       '(83886080 . 67108864) '(8589934592)) *prst-launch-base*)
      (equal (fn-prstartup-extend-operation-reservation *prst-launch-base* :run '(complete) "/tmp/store" 4 8
                                                       '(83886080 . 67108864) '(8589934592)) *prst-launch-base*)))
; Literal removal of each machine-fit hypothesis; the other is retained.
(assert-event
 (let* ((cold '(complete))
        (d (fn-prstartup-extend-default-reservation *prst-launch-base* cold "/tmp/store" 4 8 100 nil)))
  (and cold (equal (fn-prstartup-nth 0 d) :heap)
       (not (<= (fn-heap-reservation-octets (fn-prstartup-nth 1 d) 100
                  (fn-prstartup-nth 4 d) (fn-prstartup-nth 5 d)) (fn-heap-machine-octets nil))))))
(assert-event
 (let* ((cold nil)
        (d (fn-prstartup-extend-default-reservation *prst-launch-base* cold "/tmp/store" 4 8 100 nil)))
  (and (not cold) (not (equal (fn-prstartup-nth 0 d) :heap))
       (not (<= (fn-heap-reservation-octets (fn-prstartup-nth 1 d) 100
                  (fn-prstartup-nth 4 d) (fn-prstartup-nth 5 d)) (fn-heap-machine-octets nil))))))
