(in-package "ACL2")
(include-book "../../books/consumer-remote-report-scope")

; Pure semantic fixtures, never a forged configured-source/custody issuer.
(defconst *crrs-i* '(:authenticated (:remote-consumer :poll (97)) (112) (65) (78) 3 7))
(defun fn-crrs-test-config (table closed)
 (declare (xargs :guard t))
 (fn-inj-make-config-full t nil '((97) (98) (113)) 4096 (list nil nil nil table) closed))
(defun fn-crrs-test-article ()
 (declare (xargs :guard t))
 (list 0 0 0 "<a>" 1 '("a" "b" "q") nil nil nil 0 nil nil nil
       '(("a" . 1) ("b" . 2) ("q" . 3))))
(defun fn-crrs-test-run (fuel result key)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 result) :yield))) result
  (fn-crrs-test-run (- fuel 1) (fn-crrs-tick (fn-cp-nth 1 result) key 1) key)))

(assert-event
 (let* ((cfg (fn-crrs-test-config '(("a" "a" "*" 3) ("a" "*" "*" 3)) nil))
        (key (fn-crs-key *crrs-i* 9))
        (start (fn-crrs-begin *crrs-i* 9 cfg (fn-crrs-test-article)))
        (partial (fn-crrs-test-run 1 start key))
        (answer (fn-crrs-test-run 160 partial key)))
  (and (eq (car partial) :yield)
       (equal answer (list :report-input (fn-crrs-test-article) '("a") '(("a" . 1)))))))

(assert-event
 (let* ((key (fn-crs-key *crrs-i* 9))
        (hidden '((:moderated (97) (113) ((97))) (:moderated (98) (113) ((98)))))
        (cfg (fn-crrs-test-config nil hidden))
        (answer (fn-crrs-test-run 160 (fn-crrs-begin *crrs-i* 9 cfg (fn-crrs-test-article)) key)))
  (and (fn-mod-queue-hiddenp '(113) hidden '(97))
       (equal answer (list :report-input (fn-crrs-test-article) '("a" "b") '(("a" . 1) ("b" . 2)))))))

(assert-event
 (let* ((key (fn-crs-key *crrs-i* 9))
        (cfg (fn-crrs-test-config '(("a" "x" "*" 3)) nil))
        (start (fn-crrs-begin *crrs-i* 9 cfg (fn-crrs-test-article))))
  (and (equal (fn-crrs-test-run 160 start key) '(:excluded :remote-report-read-scope))
       (equal (fn-crrs-tick (cadr start) (fn-crs-key *crrs-i* 10) 1)
              '(:refused :remote-report-source-changed)))))

; Current-view rows preserve their distinct representation while cutting BOTH
; group and numbering metadata. They cannot become an original signed event.
(assert-event
 (let* ((cfg (fn-crrs-test-config '(("a" "a" "*" 3)) nil))
        (article (fn-make-article "<a>" 1 '("a" "b") '(("a" . 1) ("b" . 2)) t nil))
        (answer (fn-crrs-test-run 160 (fn-crrs-begin-view *crrs-i* 9 cfg article)
                                   (fn-crs-key *crrs-i* 9))))
  (equal answer (list :report-input (list :current-article article) '("a") '(("a" . 1))))))
