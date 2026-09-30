(in-package "ACL2")
(include-book "../../books/consumer-account-config-commit")
(local (include-book "consumer-account-candidate-tests"))
(local (include-book "consumer-account-config-preparation-tests"))

; Test-only annotation/caller. Actual runtime consumes carried parsed roots.
(defun fn-acjt-fields (fields)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp fields) (cons (fn-scs-summary (car fields)) (fn-acjt-fields (cdr fields))) nil))
(defconst *acjt-initial* (fn-cp-initial (make-list 32 :initial-element 11)
                                      (make-list 32 :initial-element 12) 0))
(defconst *acjt-metadata*
 (list :account-carries (fn-acjt-fields *acjt-initial*) nil nil nil))
(defun fn-acjt-stage (snapshot op)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((cp (fn-cp-nth 0 snapshot)) (metadata (fn-cp-nth 1 snapshot))
        (b (fn-cp-nth 2 snapshot)) (seq (fn-cp-nth 3 cp))
        (cursor (fn-cp-nth 11 b))
        (one (fn-acj-stage cp metadata b *bcpt-base*
                          (list :consumer-authority seq (1+ (nfix seq)) 0 op) seq
                          (fn-scs-summary (if (consp cursor) (car cursor) nil)))))
  (if (eq (fn-cp-nth 0 one) :ok)
      (list (fn-cp-nth 1 one) (fn-cp-nth 4 one) (fn-cp-nth 6 one)) one)))
(defun fn-acjt-prepare (snapshot fuel)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (let* ((cp (fn-cp-nth 0 snapshot)) (a (fn-cp-nth 6 cp))
        (p (fn-cp-nth 5 a)) (b (fn-cp-nth 2 snapshot)))
  (cond ((and (eq (fn-cp-nth 1 (fn-cp-nth 5 p)) :ready)
              (eq (fn-cp-nth 4 b) :ready)) snapshot)
        ((zp fuel) '(:refused :test-fuel))
        (t (fn-acjt-prepare
            (fn-acjt-stage snapshot (list :authority-prepare '(65) (fn-cp-nth 1 a)))
            (1- fuel))))))
(defconst *acjt-begin*
 (fn-acjt-stage (list *acjt-initial* *acjt-metadata* nil) '(:authority-begin (65) 0 1 7)))
(defconst *acjt-row*
 (fn-acjt-stage *acjt-begin* (fn-cad-row-operation '(65) 0 *cadt-b* 2)))
(defconst *acjt-bound*
 (fn-acjt-stage *acjt-row* (fn-cab-operation '(65) 0 '(98) 0 2 *bcpt-new*)))
(defconst *acjt-sealed*
 (let ((p (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 0 *acjt-bound*)))))
  (fn-acjt-stage *acjt-bound* (list :authority-seal '(65) 0 (fn-cp-nth 3 p) (fn-cp-nth 7 p)))))
(defconst *acjt-prepared* (fn-acjt-prepare *acjt-sealed* 60))
(defconst *acjt-marker*
 (let* ((cp (fn-cp-nth 0 *acjt-prepared*)) (p (fn-cp-nth 5 (fn-cp-nth 6 cp))))
  (fn-cacm-marker '(65) 7 0 0 (fn-cp-nth 3 cp) (fn-cp-nth 3 p) (fn-cp-nth 7 p))))
(defconst *acjt-record*
 (fn-cfg-record-make 8 (1+ (fn-cp-nth 3 (fn-cp-nth 0 *acjt-prepared*))) 8
                     *acjt-marker* (fn-clock-observation 1 0 0 nil)))
(defconst *acjt-final*
 (fn-acj-commit (fn-cp-nth 0 *acjt-prepared*) (fn-cp-nth 1 *acjt-prepared*)
                (fn-cp-nth 2 *acjt-prepared*) *acjt-record* 0
                (fn-cp-nth 3 (fn-cp-nth 0 *acjt-prepared*))))
;@positive-witness fn-acj-success-preserves-actual-e-frontier
(assert-event
 (and (equal (fn-cp-nth 0 *acjt-final*) :ok)
      (equal (fn-cp-nth 3 (fn-cp-nth 1 *acjt-final*))
             (fn-cp-nth 3 (fn-cp-nth 0 *acjt-prepared*)))))
;@hyp-removal-witness fn-acj-success-preserves-actual-e-frontier omitted=successful
(assert-event
 (let* ((cp (fn-cp-nth 0 *acjt-prepared*))
        (bad (update-nth 3 (update-nth 2 6 *acjt-marker*) *acjt-record*))
        (one (fn-acj-commit cp (fn-cp-nth 1 *acjt-prepared*)
                           (fn-cp-nth 2 *acjt-prepared*) bad 0 (fn-cp-nth 3 cp))))
  (and (not (equal (fn-cp-nth 0 one) :ok))
       (not (equal (fn-cp-nth 3 (fn-cp-nth 1 one)) (fn-cp-nth 3 cp))))))
;@mutation-witness actual-typed-c-publishes-account-config-once
(assert-event
 (let* ((cp (fn-cp-nth 1 *acjt-final*)) (root (fn-cp-nth 2 *acjt-final*))
        (cfg (fn-cp-nth 6 *acjt-final*))
        (binding (fn-cai-get-octets '(98) (fn-caa-root-index root))))
  (and (equal (fn-cp-nth 1 (fn-cp-nth 6 cp)) 1)
       (null (fn-cp-nth 5 (fn-cp-nth 6 cp)))
       (equal (fn-cp-nth 3 root) (list *cadt-b*))
       (equal (fn-cp-nth 2 binding) *cadt-b*)
       (equal (fn-cfg-generation cfg) 8)
       (equal (fn-cfg-accounts (fn-cfg-value cfg))
              (append (list (fn-bcp-binding-row '(97) *bcpt-old*) *bcpt-redeemed*
                            (fn-bcp-binding-row '(99) *bcpt-old*)
                            (fn-bcp-binding-row '(100) *bcpt-old*))
                      (list (fn-bcp-binding-row '(98) *bcpt-new*))))
       (equal (fn-cp-nth 3 *acjt-final*) (fn-cp-nth 3 cp)))))
;@mutation-witness actual-stage-binding-missing-and-old-e-fence-refuse
(assert-event
 (let* ((cp (fn-cp-nth 0 *acjt-row*)) (metadata (fn-cp-nth 1 *acjt-row*))
        (b (fn-cp-nth 2 *acjt-row*)) (seq (fn-cp-nth 3 cp))
        (p (fn-cp-nth 5 (fn-cp-nth 6 cp)))
        (event (list :consumer-authority seq (1+ seq) 0
                     (list :authority-seal '(65) 0 (fn-cp-nth 3 p) (fn-cp-nth 7 p)))))
  (and (equal (fn-acj-stage cp metadata b *bcpt-base* event seq nil)
              '(:refused :binding-stage-missing))
       (equal (fn-acj-stage cp metadata b *bcpt-base*
                           (update-nth 4 (list :authority-fence '(65) 0 (fn-cp-nth 3 p) (fn-cp-nth 7 p)) event)
                           seq nil)
              '(:refused :typed-config-commit-required)))))
