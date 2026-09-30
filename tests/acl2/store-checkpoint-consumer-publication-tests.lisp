(in-package "ACL2")
(include-book "../../books/store-checkpoint-consumer-publication")

; Protocol/format fixtures only. No CP, policy or parsed-source authority
; is inferred from these constructed fixed values.
(defconst *fn-cpub-initial*
 '(:consumer-state (1) (2) 5 1 nil (:authority 0 1 nil nil nil)))
(defconst *fn-cpub-pending*
 '(:consumer-state (1) (2) 6 1 nil (:authority 0 1 nil nil (:prep))))
(defconst *fn-cpub-adopted*
 '(:consumer-state (1) (2) 7 1 nil (:authority 1 2 (:ns) (:rows) nil)))
(defconst *fn-cpub-later*
 '(:consumer-state (1) (2) 9 1 nil (:authority 1 2 (:ns) (:rows) nil)))
(defconst *fn-cpub-root* '(:account-root 7 (:index) (:credentials)))

(assert-event
 (and (equal (fn-cpub-readout '(:ok nil)) '(:ok nil nil nil))
      (equal (fn-cpub-readout (list :ok *fn-cpub-initial*))
             (list :ok *fn-cpub-initial* nil nil))
      (equal (fn-cpub-readout (list :ok *fn-cpub-pending*))
             '(:refused :consumer-publication-missing))
      (equal (fn-cpub-readout (list :ok *fn-cpub-adopted*))
             '(:refused :consumer-publication-missing))))

(defconst *fn-cpub-namespace*
 '(1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1))
(defconst *fn-cpub-captured-cp*
 (list :consumer-state '(1) '(2) 9 1 nil
       (list :authority 1 2 *fn-cpub-namespace* '(:rows) nil)))
(defconst *fn-cpub-sidecar*
 (list :ready 3 *fn-cpub-namespace* 1 7 *fn-cpub-root*))
(assert-event
 (and (equal (fn-cpub-capture *fn-cpub-captured-cp* *fn-cpub-sidecar* 3 9)
             (list :ok *fn-cpub-captured-cp* *fn-cpub-root* 7))
      (equal (fn-cpub-capture *fn-cpub-pending* nil 3 6)
             (list :ok *fn-cpub-pending* nil nil))
      (equal (fn-cpub-capture *fn-cpub-captured-cp* *fn-cpub-sidecar* 4 9)
             '(:refused :consumer-publication-coordinate))
      (equal (fn-cpub-capture *fn-cpub-captured-cp* *fn-cpub-sidecar* 3 6)
             '(:refused :consumer-publication-coordinate))
      (equal (fn-cpub-capture *fn-cpub-captured-cp* nil 3 9)
             '(:refused :consumer-publication-missing))))

; Labelled malformed namespace mutation: identical cons-valued elements
; must refuse without a deep equality walk through either element.
(assert-event
 (let* ((bad (cons '(:nested) (cdr *fn-cpub-namespace*)))
        (cp (list :consumer-state '(1) '(2) 9 1 nil
                  (list :authority 1 2 bad '(:rows) nil)))
        (sidecar (list :ready 3 bad 1 7 *fn-cpub-root*)))
  (and (not (fn-cpub-namespace-match bad bad 40))
       (equal (fn-cpub-capture cp sidecar 3 9)
              '(:refused :consumer-publication-coordinate)))))

(assert-event
 (and (equal (fn-cpub-readout (fn-cpub-make *fn-cpub-pending* nil nil))
             (fn-cpub-make *fn-cpub-pending* nil nil))
      (equal (fn-cpub-readout (fn-cpub-make *fn-cpub-adopted* nil nil))
             '(:refused :consumer-publication-fields))
      (equal (fn-cpub-readout (list :ok *fn-cpub-adopted* *fn-cpub-root* 7))
             (list :ok *fn-cpub-adopted* *fn-cpub-root* 7))))

(assert-event
 (and (equal (fn-cpub-retain-produced
              (list :ok *fn-cpub-initial*)
              (list :ok *fn-cpub-adopted* *fn-cpub-root* 7 :metadata :carry))
             (list :ok *fn-cpub-adopted* *fn-cpub-root* 7))
      (equal (fn-cpub-retain-produced
              (list :ok *fn-cpub-adopted* *fn-cpub-root* 7)
              (list :ok *fn-cpub-later* nil nil :metadata :carry))
             (list :ok *fn-cpub-later* *fn-cpub-root* 7))))

; Labelled malformed protocol/field mutations, not source lineage teeth.
(assert-event
 (and (equal (fn-cpub-readout
              (list :ok *fn-cpub-adopted* '(:account-root 8 nil nil) 7))
             '(:refused :consumer-publication-fields))
      (equal (fn-cpub-readout (list :ok nil *fn-cpub-root* 7))
             '(:refused :consumer-publication-fields))
      (equal (fn-cpub-readout (list :ok *fn-cpub-adopted* *fn-cpub-root* nil))
             '(:refused :consumer-publication-fields))
      (equal (fn-cpub-readout (list :ok *fn-cpub-initial* nil))
             '(:refused :consumer-publication-width))))

