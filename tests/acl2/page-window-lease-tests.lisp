(in-package "ACL2")
(include-book "../../books/page-window-lease")
(defconst *prw-budget* '(10000 0 2 1 20))
(defconst *prw-baseline* '(1000 0 0 0 0))
(defconst *prw-start* (mv-nth 1 (mv-list 2 (fn-prl-make-baseline *prw-budget* *prw-baseline*))))
(defconst *prw-registered* (mv-nth 1 (mv-list 2 (fn-prl-register *prw-start* 11 '(64 0 1 0 0)))))
(defconst *prw-descriptor* '(11 100 1000000000 200 900000000 16384 77))
(defconst *prw-admitted* (mv-list 3 (fn-prw-admit *prw-registered* *prw-descriptor* '(256 0 0 1 1))))
(defconst *prw-token* (nth 1 *prw-admitted*))
(defconst *prw-held* (nth 2 *prw-admitted*))
; KEYSTONE fn-prw-admit-preserves-pool-funding.
; REACHABLE POSITIVE: full antecedent and conclusion; huge ELEN is metadata,
; not the supplied demand. Actual demand adequacy is a separate model.
(assert-event (and (equal (nth 0 *prw-admitted*) :admitted)
  (fn-prs-fundedp *prw-budget* *prw-baseline* '(0 0 0 0 0) (fn-prl-nth 1 *prw-held*))))
; KEYSTONE fn-prw-admitted-window-holds-file.
; REACHABLE POSITIVE: full antecedent and conclusion.
(assert-event (and (equal (nth 0 *prw-admitted*) :admitted)
  (equal (fn-prl-close-preview *prw-held* (fn-prl-nth 0 *prw-descriptor*)) :read-file-held)))
; KEYSTONE fn-prw-admit-preserves-pool-funding.
; HYPOTHESIS-REMOVAL: corrupted unfunded ledger, no retained hypotheses.
(assert-event (let* ((bad (fn-prl-make nil))
    (r (mv-list 3 (fn-prw-admit bad *prw-descriptor* '(256 0 0 1 1)))))
  (and (not (equal (nth 0 r) :admitted))
       (not (fn-prs-fundedp nil (fn-prl-baseline bad) '(0 0 0 0 0) (fn-prl-nth 1 (nth 2 r)))))))
; KEYSTONE fn-prw-admitted-window-holds-file.
; HYPOTHESIS-REMOVAL: malformed worker demand, no retained hypotheses.
(assert-event (let ((r (mv-list 3 (fn-prw-admit *prw-registered* *prw-descriptor* '(256 0 0 0 1)))))
  (and (not (equal (nth 0 r) :admitted))
       (not (equal (fn-prl-close-preview (nth 2 r) (fn-prl-nth 0 *prw-descriptor*)) :read-file-held)))))
; Cancellation/timeout cannot manufacture a physical return or release.
(assert-event (equal (mv-list 2 (fn-prw-release *prw-held* *prw-token*)) (list :stale *prw-held*)))
; MUTATION: another requested offset cannot settle the original job.
(assert-event (and
  (equal (mv-list 2 (fn-prw-return *prw-held* (update-nth 7 0 *prw-token*))) (list :stale *prw-held*))
  (equal (mv-list 2 (fn-prl-settle *prw-held* *prw-token* t)) (list :stale *prw-held*))))
(defconst *prw-returned* (mv-list 2 (fn-prw-return *prw-held* *prw-token*)))
; Return retains every credit and the physical file through output borrowing.
(assert-event (and (equal (nth 0 *prw-returned*) :returned)
  (equal (fn-prl-nth 1 (nth 1 *prw-returned*)) (fn-prl-nth 1 *prw-held*))
  (equal (fn-prl-close-preview (nth 1 *prw-returned*) 11) :read-file-held)
  (equal (nth 0 (mv-list 3 (fn-prw-admit (nth 1 *prw-returned*) *prw-descriptor* '(256 0 0 1 1)))) :read-resources-unavailable)))
(defconst *prw-released* (mv-list 2 (fn-prw-release (nth 1 *prw-returned*) *prw-token*)))
(assert-event (and (equal (nth 0 *prw-released*) :released)
  (equal (fn-prl-close-preview (nth 1 *prw-released*) 11) :closable)
  (equal (fn-prl-baseline (nth 1 *prw-released*)) *prw-baseline*)
  (equal (mv-list 2 (fn-prw-release (nth 1 *prw-released*) *prw-token*)) (list :stale (nth 1 *prw-released*)))))
(defconst *prw-second* (mv-list 3 (fn-prw-admit (nth 1 *prw-released*) *prw-descriptor* '(256 0 0 1 1))))
(assert-event (and (equal (nth 0 *prw-second*) :admitted)
  (not (equal (nth 1 *prw-second*) *prw-token*))
  (equal (mv-list 2 (fn-prw-return (nth 2 *prw-second*) *prw-token*)) (list :stale (nth 2 *prw-second*)))))
