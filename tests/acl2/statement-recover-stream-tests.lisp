; Literal resident chunk-composition antecedent/conclusion and its necessary
; list hypothesis. Real journal grammar, local arena, frozen generation rows.
(in-package "ACL2")
(include-book "../../books/statement-recover-stream")
(include-book "../../books/codec-attach")
(include-book "../../books/crypto-attach")
(defconst *ssrt-principal* (make-list 32 :initial-element 7))
(defconst *ssrt-keys1*
 (list (cons :ed25519 (make-list 32 :initial-element 11))
       (cons :ml-dsa-65 (make-list 1952 :initial-element 13))))
(defconst *ssrt-keys2*
 (list (cons :ed25519 (make-list 32 :initial-element 12))
       (cons :ml-dsa-65 (make-list 1952 :initial-element 14))))
(make-event `(defconst *ssrt-enroll*
 ',(fn-hl-enroll-event 0 0 0 1 *ssrt-principal* *ssrt-keys1* nil)))
(defconst *ssrt-article1*
 (fn-record-make 1 1 1 "<before@example>" '(65 13 10) '("example")
                 "o1" "s1" "e1" 1 841000000))
(make-event `(defconst *ssrt-rotate*
 ',(fn-hl-enroll-event 2 2 2 2 *ssrt-principal* *ssrt-keys2* (list *ssrt-enroll*))))
(defconst *ssrt-article2*
 (fn-record-make 3 3 3 "<after@example>" '(66 13 10) '("example")
                 "o2" "s2" "e2" 1 841000001))
(defconst *ssrt-a* (list *ssrt-enroll* *ssrt-article1*))
(defconst *ssrt-b* (list *ssrt-rotate* *ssrt-article2*))
(defun ssrt-arena-list (i fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil
                 :measure (nfix (- (fn-arena-count fn-arena) (nfix i)))))
 (if (and (natp i) (< i (fn-arena-count fn-arena)))
  (cons (fn-arena-payload i fn-arena) (ssrt-arena-list (1+ i) fn-arena)) nil))
(defun ssrt-run-in (a b splitp fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((seed (fn-ssr-seed (fn-stxk-initial-context 0))))
  (mv-let (acc fn-arena)
   (if splitp
    (mv-let (middle fn-arena)
     (fn-ssr-intern-step seed a nil nil :resident nil fn-arena)
     (fn-ssr-intern-step middle b nil nil :resident nil fn-arena))
    (fn-ssr-intern-step seed (append a b) nil nil :resident nil fn-arena))
   (mv (list acc (ssrt-arena-list 0 fn-arena)) fn-arena))))
(defun ssrt-run (a b splitp)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (out fn-arena) (ssrt-run-in a b splitp fn-arena) out)))
(assert-event
 (and (true-listp *ssrt-a*)
      (equal (ssrt-run *ssrt-a* *ssrt-b* nil)
             (ssrt-run *ssrt-a* *ssrt-b* t))
      (not (eq (car (ssrt-run *ssrt-a* *ssrt-b* t)) :bad))
      (equal (cadr (ssrt-run *ssrt-a* *ssrt-b* t)) '((65 13 10) (66 13 10)))))
; Affirmative hypothesis removal: append drops the dotted terminal, whereas
; the first worker refuses it. The complete tuple/arena conclusion differs.
(assert-event
 (with-guard-checking :none
 (let ((a (cons *ssrt-enroll* (cons *ssrt-article1* 7))))
  (and (not (true-listp a))
       (not (equal (ssrt-run a *ssrt-b* nil) (ssrt-run a *ssrt-b* t)))
       (eq (car (ssrt-run a *ssrt-b* t)) :bad)
       (not (eq (car (ssrt-run a *ssrt-b* nil)) :bad))))))
; fn-ssr-recovery-rows-are-the-raw-rows-without-snapshots (lane proofs2,
; 2026-10-04).  Premise inhabitation: two articles from sequence 0 carry no
; keyring snapshot, the statement worker accepts them from the host's seed,
; and its rows and arena are the raw worker's.  Hypothesis necessity: the
; enroll and rotate events above ARE keyring snapshots (fn-stxk-p), and over
; that history the two workers' rows differ.
(defun ssrt-raw-run (ws)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (out fn-arena)
   (mv-let (acc fn-arena) (fn-srs-intern-step nil ws fn-arena)
    (mv (list (fn-srs-rows acc) (ssrt-arena-list 0 fn-arena)) fn-arena))
   out)))
(defconst *ssrt-plain*
 (list (fn-record-make 0 0 0 "<zero@example>" '(65 13 10) '("example")
                       "o0" "s0" "e0" 1 841000000)
       (fn-record-make 1 1 1 "<one@example>" '(66 13 10) '("example")
                       "o1" "s1" "e1" 1 841000001)))
(assert-event
 (and (fn-ssr-no-snapshot-p *ssrt-plain*)
      (not (eq (car (ssrt-run *ssrt-plain* nil nil)) :bad))
      (equal (fn-ssr-rows (car (ssrt-run *ssrt-plain* nil nil)))
             (car (ssrt-raw-run *ssrt-plain*)))
      (equal (cadr (ssrt-run *ssrt-plain* nil nil)) (cadr (ssrt-raw-run *ssrt-plain*)))
      (equal (cadr (ssrt-raw-run *ssrt-plain*)) '((65 13 10) (66 13 10)))))
(assert-event
 (let ((ws (append *ssrt-a* *ssrt-b*)))
  (and (not (fn-ssr-no-snapshot-p ws))
       (not (eq (car (ssrt-run *ssrt-a* *ssrt-b* nil)) :bad))
       (not (equal (fn-ssr-rows (car (ssrt-run *ssrt-a* *ssrt-b* nil)))
                   (car (ssrt-raw-run ws)))))))
