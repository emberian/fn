(in-package "ACL2")
(include-book "../../books/checkpoint-compaction")

(defconst *cc-a0*
  (fn-record-make 0 0 0 "<compact@example.invalid>" '(65 13 10)
                  '("fn.letters") "archive-0" "subject-0" "evidence-0" 3))
(defconst *cc-e1*
  (fn-store-retention-event-make :undertake 1 1 1
                                 "forward-1" "subject-1" "evidence-1" 2))
(defconst *cc-e2*
  (fn-store-retention-event-make :release 2 2 2
                                 "forward-1" "subject-1" "receipt-1" 0))
(defconst *cc-b0* (fn-store-event-encode *cc-a0*))
(defconst *cc-b1* (fn-store-event-encode *cc-e1*))
(defconst *cc-b2* (fn-store-event-encode *cc-e2*))
(defconst *cc-i3*
  (fn-stxe-make 3 3 3 "<compact@example.invalid>" :unverified
                '(117 110 118 101 114 105 102 105 101 100) 7 '(116 101 115 116)))
(defconst *cc-k4*
  (fn-stxk-make 4 4 4 7 '(116 101 115 116) '(1 2 3 4)))
(defconst *cc-b3* (fn-store-event-encode *cc-i3*))
(defconst *cc-b4* (fn-store-event-encode *cc-k4*))

(assert-event
 (equal (fn-cc-expand (fn-cc-make 2 2 (list *cc-b0* *cc-b1*))
                      (list *cc-b2*) 4)
        (list :ok (list *cc-b0* *cc-b1* *cc-b2*) 4)))
(assert-event
 (equal (fn-cc-expand
         (fn-cc-make 4 4 (list *cc-b0* *cc-b1* *cc-b2* *cc-b3*))
         (list *cc-b4*) 6)
        (list :ok (list *cc-b0* *cc-b1* *cc-b2* *cc-b3* *cc-b4*) 6)))
(assert-event
 (fn-cc-observation-agrees
  (list (list 1 *cc-b1*) (list 2 *cc-b2*) (list 3 *cc-b3*) (list 4 *cc-b4*))
  (list *cc-b0* *cc-b1* *cc-b2* *cc-b3*) 4))
(assert-event
 (not (fn-cc-observation-agrees
       (list (list 1 *cc-b0*) (list 4 *cc-b4*))
       (list *cc-b0* *cc-b1* *cc-b2* *cc-b3*) 4)))
(assert-event
 (equal (fn-cc-decode-exact
         (fn-cc-encode (fn-cc-make 2 2 (list *cc-b0* *cc-b1*))))
        (list :ok (fn-cc-make 2 2 (list *cc-b0* *cc-b1*)))))
(assert-event
 (equal (fn-cc-decode-exact
         (append (fn-cc-encode (fn-cc-make 2 2 (list *cc-b0* *cc-b1*))) '(0)))
        '(:error :summary)))
(assert-event
 (member-equal *cc-b0*
               (fn-cc-events
                (fn-cc-nth 1 (fn-cc-capture (list *cc-b0* *cc-b1*) 2)))))
(assert-event
 (equal (fn-cc-expand (fn-cc-make 2 2 (list *cc-b0* *cc-b1*))
                      (list *cc-b1*) 6)
        '(:error :suffix)))
(assert-event
 (equal (fn-cc-expand (fn-cc-make 2 2 (list *cc-b0* *cc-b1*))
                      (list *cc-b2*) 1)
        '(:error :frontier)))
(assert-event
 (equal (fn-cc-expand (fn-cc-make 2 2 (list *cc-b0* '(999)))
                      (list *cc-b2*) 6)
        '(:error :summary)))
