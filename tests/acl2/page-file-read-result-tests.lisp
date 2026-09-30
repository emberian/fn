(in-package "ACL2")
(include-book "../../books/page-file-lease")
(include-book "../../books/page-discovery-ledger")

(defconst *prfr-start* (mv-nth 1 (mv-list 2
  (fn-prl-make-baseline '(10000000 0 4 2 32) '(1000 0 0 0 0)))))
(defconst *prfr-registered* (mv-nth 1 (mv-list 2
  (fn-prl-register *prfr-start* 11 '(64 0 1 0 0)))))
(defconst *prfr-root-answer* (mv-list 3
  (fn-prf-acquire *prfr-registered* 11 '(256 0 1 0 1))))
(defconst *prfr-root* (nth 1 *prfr-root-answer*))
(defconst *prfr-request* (list :read-page (nth 1 *prfr-root*) 7 2 :table 1 16384 16384 0))
(defconst *prfr-read* (mv-list 3
  (fn-prd-admit (nth 2 *prfr-root-answer*) 11 16448 16384 '(65536 0 0 1 1))))
(defconst *prfr-token* (nth 1 *prfr-read*))
(defconst *prfr-held* (nth 2 *prfr-read*))
(defconst *prfr-complete* (mv-list 4
  (fn-prf-read-result *prfr-held* *prfr-root* *prfr-request* 64 *prfr-token* 16384 :ok)))
; REACHABLE POSITIVE: complete literal antecedent/conclusion of the authority
; definition boundary. Supplied model demand is not native allocation adequacy.
(assert-event (and (equal (nth 0 *prfr-read*) :admitted)
  (equal (nth 3 *prfr-complete*) :read-ok)
  (equal (nth 0 *prfr-complete*) :read-result)
  (equal (nth 1 *prfr-complete*) (fn-prl-nth 1 *prfr-token*))
  (equal (nth 2 *prfr-complete*) 16384)
  (equal (fn-prl-nth 1 (cdr (fn-prl-binding *prfr-token* (fn-prl-nth 3 *prfr-held*)))) :discovery)
  (equal (fn-prf-ticket *prfr-held* *prfr-root*) 0)
  (equal (fn-prl-close-preview *prfr-held* 11) :read-file-held)))
; Observed short/error results retain the exact ID, without success status.
(assert-event (equal (mv-list 4 (fn-prf-read-result *prfr-held* *prfr-root*
  *prfr-request* 64 *prfr-token* 512 :ok))
  (list :read-result (fn-prl-nth 1 *prfr-token*) 512 :short-read)))
(assert-event (equal (mv-list 4 (fn-prf-read-result *prfr-held* *prfr-root*
  *prfr-request* 64 *prfr-token* -1 :ok))
  (list :read-result (fn-prl-nth 1 *prfr-token*) 0 :io-error)))
; MUTATIONS: wrong physical placement or vanished exact ownership is stale.
(assert-event (equal (mv-list 4 (fn-prf-read-result *prfr-held* *prfr-root*
  *prfr-request* 65 *prfr-token* 16384 :ok)) '(:stale-read nil 0 :stale)))
(assert-event (let ((released (mv-list 2 (fn-prd-release *prfr-held* *prfr-token*))))
  (and (equal (nth 0 released) :released)
       (equal (mv-list 4 (fn-prf-read-result (nth 1 released) *prfr-root*
          *prfr-request* 64 *prfr-token* 16384 :ok)) '(:stale-read nil 0 :stale))
       (equal (mv-list 2 (fn-prd-release (nth 1 released) *prfr-token*))
              (list :stale (nth 1 released))))))
