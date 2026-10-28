(in-package "ACL2")
(include-book "../books/format-check")
(defun fn2-fc-test-values (layout seed)
 (declare (xargs :verify-guards nil))
 (if (atom layout) nil
  (cons (let ((k (cadar layout)))
          (cond ((eq k :digest) (cons 1 (make-list 32 :initial-element 0)))
                ((and (consp k) (eq (car k) :enum)) 0) ((eq (caar layout) 'history) 1)
                ((eq (caar layout) 'incarnation) 2)
                ((eq (caar layout) 'extent) 7)
                ((eq (caar layout) 'extent-writer-epoch) 8)
                ((eq (caar layout) 'extent-allocation) 9)
                ((eq (caar layout) 'commit) 4)
                ((eq (caar layout) 'previous-commit) 6)
                (t seed)))
        (fn2-fc-test-values (cdr layout) seed))))
(defconst *fn2-fc-test-context*
 (append '(17 9 1 2 3 4 0 4096) (make-list 16 :initial-element 0) '(8 6) (make-list 8 :initial-element 0) '(7)))
(defun fn2-fc-test-frame (seed)
 (declare (xargs :verify-guards nil))
 (let ((header (fn2-layout-octets *fn2-format-frame-header*
                (list *fn2-format-frame-magic* 0 1 2 3 4 7 8 9 0 0 3))))
  (append header (list seed 72 19) (make-list (- 4060 (len header)) :initial-element 0)
          '(1) (make-list 32 :initial-element 0))))
(defconst *fn2-fc-test-frame* (cadr (fn2-fc-image :frame (fn2-fc-test-frame 3) *fn2-fc-test-context* t 4096)))
(assert-event (fn2-fc-acceptedp :frame *fn2-fc-test-frame* *fn2-fc-test-context*))
(assert-event
 (let* ((a *fn2-fc-test-context*) (b (update-fn2-fc-expected-location 18 a)) (bytes *fn2-fc-test-frame*))
  (and (fn2-fc-expectedp a) (fn2-fc-expectedp b) (fn2-fc-acceptedp :frame bytes a)
       (not (equal (fn2-fc-frame-identity a) (fn2-fc-frame-identity b)))
       (fn2-fc-collision-free-pairp (fn2-fc-covered :frame bytes a) (fn2-fc-covered :frame bytes b))
       (not (fn2-fc-acceptedp :frame bytes b)))))
(assert-event
 (let ((a *fn2-fc-test-context*) (bytes *fn2-fc-test-frame*))
  (and (fn2-fc-expectedp a) (fn2-fc-acceptedp :frame bytes a)
       (equal (fn2-fc-frame-identity a) (fn2-fc-frame-identity a))
       (fn2-fc-collision-free-pairp (fn2-fc-covered :frame bytes a) (fn2-fc-covered :frame bytes a))
       (not (not (fn2-fc-acceptedp :frame bytes a))))))
(defun fn2-fc-test-page (seed)
 (declare (xargs :verify-guards nil))
 (let ((header (fn2-layout-octets *fn2-format-page-header*
                (list *fn2-format-page-magic* 1 0 1 2 17 3 9 32 3))))
  (append header (make-list (- 32 (len header)) :initial-element 0)
          (list seed 72 19) (make-list 93 :initial-element 0))))
(defun fn2-fc-test-page-context (bytes)
 (declare (xargs :verify-guards nil))
 (append '(17 9 1 2 3 4 0 128)
  (fn-b3-words 8 (fn-blake3 (fn2-fc-covered :page bytes nil))) (make-list 8 :initial-element 0) '(8 6) (make-list 8 :initial-element 0) '(7)))
(defconst *fn2-fc-test-page* (fn2-fc-test-page 3))
(defconst *fn2-fc-test-page-context* (fn2-fc-test-page-context *fn2-fc-test-page*))
(assert-event
 (let* ((bytes *fn2-fc-test-page*) (a *fn2-fc-test-page-context*) (b (update-fn2-fc-expected-page-kind 1 a)))
  (and (fn2-fc-expectedp a) (fn2-fc-expectedp b) (fn2-fc-acceptedp :page bytes a)
       (not (equal (fn2-fc-parent-identity a) (fn2-fc-parent-identity b)))
       (not (fn2-fc-acceptedp :page bytes b)))))
(assert-event
 (let ((bytes *fn2-fc-test-page*) (a *fn2-fc-test-page-context*))
  (and (fn2-fc-expectedp a) (fn2-fc-acceptedp :page bytes a) (equal (fn2-fc-parent-identity a) (fn2-fc-parent-identity a))
       (not (not (fn2-fc-acceptedp :page bytes a))))))
(defun fn2-fc-test-anchor (seed)
 (declare (xargs :verify-guards nil))
 (fn2-layout-octets *fn2-format-anchor*
  (update-nth *fn2-format-anchor-field-slot* 1 (update-nth *fn2-format-anchor-field-history* 1 (update-nth *fn2-format-anchor-field-incarnation* 2 (fn2-fc-test-values *fn2-format-anchor* seed))))))
(defconst *fn2-fc-test-anchor-context* (update-fn2-fc-expected-location 1 *fn2-fc-test-context*))
(defconst *fn2-fc-test-anchor* (cadr (fn2-fc-image :anchor (fn2-fc-test-anchor 16384) *fn2-fc-test-anchor-context* t 7)))
(assert-event (fn2-fc-acceptedp :anchor *fn2-fc-test-anchor* *fn2-fc-test-anchor-context*))
(defun fn2-fc-test-seal (seed)
 (declare (xargs :verify-guards nil))
 (cadr (fn2-fc-image :seal (fn2-layout-octets *fn2-format-sealed-batch*
                       (fn2-fc-test-values *fn2-format-sealed-batch* seed)) *fn2-fc-test-context* t 7)))
(defconst *fn2-fc-test-seal* (fn2-fc-test-seal 3))
; Whole seal-commits antecedent AND every conclusion, on the actual checker.
(assert-event
 (let* ((a *fn2-fc-test-seal*) (b a) (ca *fn2-fc-test-context*) (cb ca))
  (and (fn2-fc-expectedp ca) (fn2-fc-expectedp cb)
       (fn2-fc-acceptedp :seal a ca) (fn2-fc-acceptedp :seal b cb)
       (equal (nthcdr (- (len a) 32) a) (nthcdr (- (len b) 32) b))
       (fn2-fc-collision-free-pairp (fn2-fc-covered :seal a ca) (fn2-fc-covered :seal b cb))
       (equal (fn2-fc-seal-identity ca) (fn2-fc-seal-identity cb))
       (equal (fn2-fc-seal-predecessor ca) (fn2-fc-seal-predecessor cb))
       (equal (fn2-fc-covered :seal a ca) (fn2-fc-covered :seal b cb)))))
; Removing equal hashes permits two accepted, distinct covered batch contents.
(assert-event
 (let ((a *fn2-fc-test-seal*) (b (fn2-fc-test-seal 4)) (c *fn2-fc-test-context*))
  (and (fn2-fc-expectedp c)
       (fn2-fc-acceptedp :seal a c) (fn2-fc-acceptedp :seal b c)
       (fn2-fc-collision-free-pairp (fn2-fc-covered :seal a c) (fn2-fc-covered :seal b c))
       (not (equal (nthcdr (- (len a) 32) a) (nthcdr (- (len b) 32) b)))
       (not (equal (fn2-fc-covered :seal a c) (fn2-fc-covered :seal b c))))))
; Changed expected history/incarnation/extent/allocation and predecessors refuse.
(assert-event
 (not (fn2-fc-acceptedp :seal *fn2-fc-test-seal*
        (update-fn2-fc-expected-history 2 *fn2-fc-test-context*))))
(assert-event
 (not (fn2-fc-acceptedp :seal *fn2-fc-test-seal*
        (update-fn2-fc-expected-incarnation 3 *fn2-fc-test-context*))))
(assert-event
 (not (fn2-fc-acceptedp :seal *fn2-fc-test-seal*
        (update-fn2-fc-expected-extent 8 *fn2-fc-test-context*))))
(assert-event
 (not (fn2-fc-acceptedp :seal *fn2-fc-test-seal*
        (update-fn2-fc-expected-extent-writer-epoch 9 *fn2-fc-test-context*))))
(assert-event
 (not (fn2-fc-acceptedp :seal *fn2-fc-test-seal*
        (update-fn2-fc-expected-allocation 10 *fn2-fc-test-context*))))
(assert-event
 (not (fn2-fc-acceptedp :seal *fn2-fc-test-seal*
        (update-fn2-fc-expected-previous-commit 7 *fn2-fc-test-context*))))
(assert-event
 (not (fn2-fc-acceptedp :seal *fn2-fc-test-seal*
        (update-fn2-fc-expected-previous-seal-0 1 *fn2-fc-test-context*))))
(assert-event (equal (car (fn2-fc-image :frame *fn2-fc-test-frame* *fn2-fc-test-context* nil 1)) :ok))
(assert-event (equal (car (fn2-fc-image :frame *fn2-fc-test-frame* *fn2-fc-test-context* nil 7)) :ok))
; Independent list BLAKE3 oracle controls the hashing subject, including zeroing.
(assert-event
 (and (equal (nthcdr 4064 *fn2-fc-test-frame*)
             (fn-blake3 (fn2-fc-covered :frame *fn2-fc-test-frame* *fn2-fc-test-context*)))
      (equal (nthcdr (- (len *fn2-fc-test-anchor*) 32) *fn2-fc-test-anchor*)
             (fn-blake3 (fn2-fc-covered :anchor *fn2-fc-test-anchor* *fn2-fc-test-context*)))
      (equal (nthcdr (- (len *fn2-fc-test-seal*) 32) *fn2-fc-test-seal*)
             (fn-blake3 (fn2-fc-covered :seal *fn2-fc-test-seal* *fn2-fc-test-context*)))))
