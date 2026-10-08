; Article witnesses for the paged model's held fold.  No snapshot exclusion:
; enroll, article, rotate, article are the actual replay-worker fixture.
(in-package "ACL2")
(include-book "../../books/paged-checkpoint-held")
(include-book "../../books/owner-checkpoint-open")
(include-book "statement-recover-stream-tests")
(include-book "must-fail-checked")

; Use a topic in the supported default profile, so the owner open succeeds.
(defconst *pckh-a*
  (list *ssrt-enroll*
        (fn-record-make 1 1 1 "<before@example>" '(65 13 10) '("fn.test")
                        "o1" "s1" "e1" 1 841000000)))
(defconst *pckh-b*
  (list *ssrt-rotate*
        (fn-record-make 3 3 3 "<after@example>" '(66 13 10) '("fn.test")
                        "o2" "s2" "e2" 1 841000001)))

(defconst *pckh-wire* (append *pckh-a* *pckh-b*))
(make-event `(defconst *pckh-held* ',(fn-pck-held *pckh-wire*)))
(make-event `(defconst *pckh-worker*
               ',(fn-ssr-rows (car (ssrt-run *pckh-a* *pckh-b* nil)))))
(defconst *pckh-configs* (list *fn-cfg-default-record*))

; Complete antecedent (T) and conclusion of the replay correspondence.
(assert-event
 (and (not (equal *pckh-held* :bad))
      (equal *pckh-held* *pckh-worker*)
      (equal (len *pckh-held*) 4)
      (fn-sco-store-eventsp *pckh-held*)
      (equal (fn-record-payload (nth 1 *pckh-held*)) 0)
      (equal (fn-record-payload (nth 3 *pckh-held*)) 1)
      (not (equal (fn-ock-recover-full *pckh-configs* 4 *pckh-held* 4) :fault))))

; The append lemma's full antecedent and result: handle and context continue.
(assert-event
 (let* ((p (fn-pck-held *pckh-a*))
        (d (fn-scka-intern-at *pckh-b*
             (fn-replay-identity-loop p (fn-stxk-initial-context 0))
             (len (fn-scka-payloads *pckh-a*)))))
   (and (true-listp *pckh-a*) (not (equal p :bad))
        (not (equal d :bad)) (equal *pckh-held* (append p d)))))

; A wire article is not a store event: the former model's equality was fault
; on both sides.  This mutation must fail a successful recovery assertion.
(must-fail-checked
 (assert-event
  (not (equal (fn-ock-recover-full *pckh-configs* 4 *pckh-wire* 4) :fault))))

; Resetting context or handle at the suffix is wrong on this same log.
(must-fail-checked
 (assert-event
  (equal *pckh-held* (car (ssrt-raw-run *pckh-wire*)))))
(must-fail-checked
 (assert-event
  (equal *pckh-held* (append (fn-pck-held *pckh-a*) (fn-pck-held *pckh-b*)))))
