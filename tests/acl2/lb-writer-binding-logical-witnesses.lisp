; Whole logical antecedent/conclusion witnesses over the actual sealed arena and writers.
(in-package "ACL2")
(include-book "lb-writer-binding-fixtures")

(defthm fn-lbw-good-arena-is-two-real-seals
 (equal (fn-lbw-arena-good (create-fn-arena))
        (list *fn-lbr13-payload* *fn-lbw-payload-b*))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbw-arena-good fn-arena-clear-is-nil fn-arena-seal-list-is-append
   fn-arena-p (:executable-counterpart fn-arena$ap) create-fn-arena)))))

(defthm fn-lbw-logical-two-row-binding
 (let ((arena (fn-lbw-arena-good (create-fn-arena)))
       (rows (fn-lbw-two-rows)) (log (fn-lbw-two-log)))
  (and (fn-arena-p arena) (fn-cat$ap rows)
       (equal (fn-arena-count arena) 2)
       (fn-scol-handles-below rows (fn-arena-count arena))
       (fn-lb-log-handles-below log (fn-arena-count arena))
       (fn-lb-arena-is-log arena rows log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbw-good-arena-is-two-real-seals fn-arena-p fn-arena-count-is-len
   fn-lb-arena-is-log fn-nntp-payload-bytes fn-arena-payload-is-nth
   (:executable-counterpart fn-arena$ap)
   (:executable-counterpart fn-lbw-two-rows) (:executable-counterpart fn-lbw-two-log)
   (:executable-counterpart fn-cat$ap) (:executable-counterpart fn-scol-handles-below)
   (:executable-counterpart fn-lb-log-handles-below)
   (:executable-counterpart fn-lb-log-payload) (:executable-counterpart fn-record-payload))))))

(defthm fn-lbw-append-whole-positive
 (and (and (fn-cat$ap (fn-lbw-two-rows)) (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-lbw-two-rows) (fn-lbw-two-log))) (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-lbw-two-rows) (fn-lb-log-model-append (fn-lbr13-held) (fn-nntp-payload-bytes 0 (fn-lbw-arena-good (create-fn-arena))) 2 (fn-lbw-two-log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbw-logical-two-row-binding)
       (:instance fn-lb-arena-is-log-of-append (fn-arena (fn-lbw-arena-good (create-fn-arena))) (rows (fn-lbw-two-rows)) (log (fn-lbw-two-log)) (row (fn-lbr13-held)) (target 2)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbw-good-arena-is-two-real-seals (:executable-counterpart fn-cat$ap) (:executable-counterpart fn-lbw-two-rows) (:executable-counterpart fn-lbw-two-log) (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbw-incoming-held) (:executable-counterpart fn-record-payload) (:executable-counterpart fn-lb-log-model-row-entry))))))

(defthm fn-lbw-withdraw-whole-positive
 (and (and (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-lbw-two-rows) (fn-lbw-two-log)) (natp 0)) (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-cat-withdraw 0 1 (fn-lbw-two-rows)) (fn-lbw-two-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbw-logical-two-row-binding)
       (:instance fn-lb-arena-is-log-of-withdraw (fn-arena (fn-lbw-arena-good (create-fn-arena))) (rows (fn-lbw-two-rows)) (log (fn-lbw-two-log)) (target 0) (by 1)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbw-good-arena-is-two-real-seals (:executable-counterpart fn-cat$ap) (:executable-counterpart fn-lbw-two-rows) (:executable-counterpart fn-lbw-two-log) (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbw-incoming-held) (:executable-counterpart fn-record-payload) (:executable-counterpart fn-lb-log-model-row-entry))))))

(defthm fn-lbw-redecide-whole-positive
 (and (and (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-lbw-two-rows) (fn-lbw-two-log)) (natp 0) (< 0 (len (fn-lbw-two-rows)))) (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-cat-redecide 0 nil (fn-lbw-two-rows)) (fn-lbw-two-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbw-logical-two-row-binding)
       (:instance fn-lb-arena-is-log-of-redecide (fn-arena (fn-lbw-arena-good (create-fn-arena))) (rows (fn-lbw-two-rows)) (log (fn-lbw-two-log)) (seq 0) (context nil)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbw-good-arena-is-two-real-seals (:executable-counterpart fn-cat$ap) (:executable-counterpart fn-lbw-two-rows) (:executable-counterpart fn-lbw-two-log) (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbw-incoming-held) (:executable-counterpart fn-record-payload) (:executable-counterpart fn-lb-log-model-row-entry))))))

(defthm fn-lbw-commit-whole-positive
 (and (and (fn-arena-p (fn-lbw-arena-good (create-fn-arena))) (fn-cat$ap (fn-lbw-two-rows)) (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-lbw-two-rows) (fn-lbw-two-log)) (fn-scol-handles-below (fn-lbw-two-rows) (fn-arena-count (fn-lbw-arena-good (create-fn-arena)))) (equal (fn-record-payload (fn-lbw-incoming-held)) (fn-arena-count (fn-lbw-arena-good (create-fn-arena)))) (not (fn-lb-log-model-row-entry (fn-lbw-incoming-held) (fn-lbw-two-log)))) (fn-lb-arena-is-log (fn-arena-seal-list *fn-lbw-payload-b* (fn-lbw-arena-good (create-fn-arena))) (fn-cat-commit (fn-lbw-incoming-held) (fn-lbw-two-rows)) (fn-lb-log-model-append (fn-cat-assign (fn-lbw-incoming-held) (fn-lbw-two-rows)) *fn-lbw-payload-b* 2 (fn-lbw-two-log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbw-logical-two-row-binding)
       (:instance fn-lb-arena-is-log-of-commit (fn-arena (fn-lbw-arena-good (create-fn-arena))) (rows (fn-lbw-two-rows)) (log (fn-lbw-two-log)) (h (fn-lbw-incoming-held)) (payload *fn-lbw-payload-b*) (target 2)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbw-good-arena-is-two-real-seals (:executable-counterpart fn-cat$ap) (:executable-counterpart fn-lbw-two-rows) (:executable-counterpart fn-lbw-two-log) (:executable-counterpart fn-lbr13-held) (:executable-counterpart fn-lbw-incoming-held) (:executable-counterpart fn-record-payload) (:executable-counterpart fn-lb-log-model-row-entry))))))

(defthm fn-lbw-withdraw-natural-target-removal
 (let* ((fn-arena (create-fn-arena)) (rows nil)
        (log '((1 nil ((0 0 0 0 0 nil (9) nil nil))))) (target -1) (by 0))
  (and (fn-lb-arena-is-log fn-arena rows log)
       (not (natp target))
       (not (fn-lb-arena-is-log fn-arena (fn-cat-withdraw target by rows) log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-arena-is-log fn-cat-withdraw fn-cat$a-withdraw fn-cat-mark-withdrawn
 fn-nntp-payload-bytes
 (:executable-counterpart fn-held-with-withdrawn)
 (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-payload)
 (:executable-counterpart fn-held-withdrawn))))))
