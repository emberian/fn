; Dependency/registration gate only. The actual initialized whole-trace
; witness is the selected native control-death campaign, still pending.
(in-package "ACL2")
(include-book "../sim/native-device-envelope")
(include-book "native-device-bindings-unit")

; The actual consumer calls this ordered join before reading the logical loan.
; Whole initialized replay remains the separate native campaign obligation.
(assert-event
 (let* ((a *fn2-nde-write-take*)
        (b (update-nth 1 5 a))
        (records '((:submit 1 (17 5 7 :write 100 3 (8 9 10) 0 1 1))
                   (:submit 2 (17 4 7 :write 100 3 (8 9 10) 0 1 1)))))
  (and (fn2-nde-submit-join-p b records '(1 2) (list a) :fdatasync)
       (not (fn2-nde-submit-join-p a records '(1 2) (list b) :fdatasync)))))
(assert-event
 (and (fn2-nde-submit-join-p *fn2-nde-write-take* nil nil nil :fdatasync)
      (fn2-nde-submit-join-p *fn2-nde-write-take* nil nil '((:ack 1)) :fdatasync)
      (not (fn2-nde-submit-join-p *fn2-nde-write-take* nil '(1) nil :fdatasync))
      (not (fn2-nde-submit-join-p *fn2-nde-write-take* nil nil '((:ack 1) (:turn 0)) :fdatasync))))

; Physical return order is independent of submit identity coverage. Refuse a
; later completion first; leaving an unposted suffix is a valid terminal cut.
(assert-event
 (let* ((records '((:submit 1 (17 4 7 :write 100 3 (8 9 10) 0 1 1))
                   (:submit 2 (17 5 7 :write 100 3 (8 9 10) 0 1 1))
                   (:begin 1) (:return 1 3 0 nil)
                   (:begin 2) (:return 2 3 0 nil)))
        (unposted (fn2-nde-returned-jobs records records))
        (a (list :post 0 4 7 *fn2-event-write-result* *fn2-outcome-done*
                 *fn2-reason-none* 3 0 0 0 '(0 0 0 0 0) nil))
        (b (update-nth 2 5 a)))
  (and (equal (strip-cars unposted) '(1 2))
       (fn2-nde-post-join-p a records unposted)
       (not (fn2-nde-post-join-p b records unposted))
       (fn2-nde-post-join-p b records (cdr unposted))
       (not (fn2-nde-post-join-p a records nil)))))

; Workers race between return and release, so unordered jobs (two Reads, a
; Read and a Fence) may post in either return order; ordered ones may not.
(defun fn2-nde-test-posts-loop (records slots unposted)
 (declare (xargs :verify-guards nil))
 (or (atom slots)
     (let ((e (update-nth 2 (car slots) *fn2-nde-write-post*)))
      (and (fn2-nde-post-join-p e records unposted)
           (fn2-nde-test-posts-loop records (cdr slots)
            (remove1-assoc-equal (nth 1 (fn2-nde-job (car slots) 7 records)) unposted))))))
(defun fn2-nde-test-posts-p (records slots)
 (declare (xargs :verify-guards nil))
 (let ((unposted (fn2-nde-returned-jobs records records)))
  (fn2-nde-test-posts-loop records slots unposted)))
(defun fn2-nde-test-pair (a b)
 (list (list :submit 1 a) (list :submit 2 b) '(:begin 1)
       (list :return 1 (if (eq (nth 3 a) :fence) 0 2) 0 (if (eq (nth 3 a) :read) '(8 9) nil))
       '(:begin 2)
       (list :return 2 (if (eq (nth 3 b) :fence) 0 2) 0 (if (eq (nth 3 b) :read) '(8 9) nil))))
(assert-event
 (let ((w4 '(17 4 7 :write 100 3 (8 9 10) 0 1 1)) (r5 '(17 5 7 :read 100 3 nil 0 1 1))
       (r6 '(17 6 7 :read 100 3 nil 0 1 1)) (f8 '(17 8 7 :fence 0 0 nil 0 1 1))
       (f9 '(17 9 7 :fence 0 0 nil 0 1 1)))
  (and (fn2-nde-test-posts-p (fn2-nde-test-pair r5 r6) '(5 6))
       (fn2-nde-test-posts-p (fn2-nde-test-pair r5 r6) '(6 5))
       (fn2-nde-test-posts-p (fn2-nde-test-pair r5 f8) '(8 5))
       (fn2-nde-test-posts-p (fn2-nde-test-pair f8 r6) '(6 8))
       ; Teeth: the later of an ordered pair cannot post first.
       (fn2-nde-test-posts-p (fn2-nde-test-pair w4 r6) '(4 6))
       (not (fn2-nde-test-posts-p (fn2-nde-test-pair w4 r6) '(6 4)))
       (fn2-nde-test-posts-p (fn2-nde-test-pair r5 w4) '(5 4))
       (not (fn2-nde-test-posts-p (fn2-nde-test-pair r5 w4) '(4 5)))
       (fn2-nde-test-posts-p (fn2-nde-test-pair f8 f9) '(8 9))
       (not (fn2-nde-test-posts-p (fn2-nde-test-pair f8 f9) '(9 8)))
       (not (fn2-nde-test-posts-p (fn2-nde-test-pair f8 w4) '(4 8)))
       ; Nor post twice, nor post an unreturned job.
       (not (fn2-nde-test-posts-p (fn2-nde-test-pair r5 r6) '(5 5)))
       (not (fn2-nde-test-posts-p (butlast (fn2-nde-test-pair r5 r6) 1) '(6))))))

; Use the real constructor widths (especially Post's cell before slot/gen).
; Shape rejection precedes all replay positional access and state mutation.
(assert-event
 (and (fn2-nde-control-shape-p *fn2-nde-write-take*)
      (fn2-nde-control-shape-p *fn2-nde-write-post*)
      (fn2-nde-control-shape-p '(:clock 1 2 1))
      (fn2-nde-control-shape-p '(:ack 1))
      (not (fn2-nde-control-shape-p (take 10 *fn2-nde-write-post*)))
      (not (fn2-nde-control-shape-p (append *fn2-nde-write-post* '(extra))))
      (not (fn2-nde-control-shape-p (append *fn2-nde-write-post* 'dotted)))
      (not (fn2-nde-control-shape-p '(:clock 1 2)))
      (not (fn2-nde-control-shape-p '(:ack 1 extra)))
      (not (fn2-nde-control-shape-p '(:unknown 1)))))
