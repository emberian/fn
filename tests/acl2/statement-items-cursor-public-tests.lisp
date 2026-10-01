(in-package "ACL2")
(include-book "../../books/statement-items-cursor-public")
(include-book "../../books/statement-attach")
; Full public bounded result, including terminal phase.
(assert-event
 (let* ((xs '(66 9 10 1)) (c (fn-sic-begin 2 xs 4 2))
        (d (fn-sic-run (fn-sic-completion-cost c) c)))
  (and (natp 2) (natp 4) (natp 2)
       (equal (fn-sic-at 0 d) :done)
       (equal (fn-sic-result-abstract d) '(:ok ((:bytes 9 10) (:uint . 1))))
       (equal (fn-sic-result-abstract d) (fn-stmt-decode-items-bounded 2 xs 4 2)))))
; Canonicality is the public constraint at the original wrapper budgets.
(assert-event
 (let* ((xs '(66 9 10 1)) (c (fn-sic-begin-legacy 2 xs))
        (d (fn-sic-run (fn-sic-completion-cost c) c)))
  (and (natp 2) (fn-stmt-okp (fn-sic-result-abstract d))
       (equal (fn-sic-result-abstract d) (fn-stmt-decode-items 2 xs))
       (equal (fn-stmt-encode-items (fn-stmt-value (fn-sic-result-abstract d))) xs))))
; Full public errors preserve nonminimal, truncation and fuel decisions.
(assert-event
 (let* ((xs '(24 1)) (c (fn-sic-begin-legacy 1 xs))
        (d (fn-sic-run (fn-sic-completion-cost c) c)))
  (and (equal (fn-sic-result-abstract d) (fn-stmt-decode-items 1 xs))
       (equal (fn-sic-result-abstract d) '(:error :noncanonical)))))
(assert-event
 (let* ((xs '(66 9)) (c (fn-sic-begin-legacy 1 xs))
        (d (fn-sic-run (fn-sic-completion-cost c) c)))
  (and (equal (fn-sic-result-abstract d) (fn-stmt-decode-items 1 xs))
       (equal (fn-sic-result-abstract d) '(:error :truncated)))))
(assert-event
 (let* ((xs '(1)) (c (fn-sic-begin-legacy 0 xs))
        (d (fn-sic-run (fn-sic-completion-cost c) c)))
  (and (equal (fn-sic-result-abstract d) (fn-stmt-decode-items 0 xs))
       (equal (fn-sic-result-abstract d) '(:error :too-many-items)))))
; Outer limit takes precedence over malformed source bytes.
(assert-event
 (let* ((xs '(999 1)) (c (fn-sic-begin 1 xs 1 1))
        (d (fn-sic-run (fn-sic-completion-cost c) c)))
  (and (equal (fn-sic-result-abstract d) (fn-stmt-decode-items-bounded 1 xs 1 1))
       (equal (fn-sic-result-abstract d) '(:error :limit)))))
 ; Accepted hypothesis removal is a logical literal: refusal values are outside
; the encoder's executable guard, so it must not be executed as host evidence.
(defthm fn-sic-public-canonical-accepted-hypothesis-removal
 (let* ((xs '(24 1)) (c (fn-sic-begin-legacy 1 xs))
        (d (fn-sic-run (fn-sic-completion-cost c) c)))
  (and (natp 1) (not (fn-stmt-okp (fn-sic-result-abstract d)))
       (not (equal (fn-stmt-encode-items (fn-stmt-value (fn-sic-result-abstract d))) xs))))
 :hints (("Goal" :in-theory (disable fn-stmt-encode-items-of-cons))))
