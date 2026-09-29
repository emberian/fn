; Committed prefix interpretation, including every nonarticle journal slot.
(in-package "ACL2")
(include-book "../../books/consumer-store-projection")
(include-book "must-fail-checked")
(include-book "held-rows-tests")

(defconst *cppt-boot* (fn-cpe-make 0 0 0 '(:bootstrap (1) (2))))
(defconst *cppt-reg* (fn-cpe-make 1 1 1 '(:register (3) (4) (5) 1 1 1)))
(defconst *cppt-article-wire*
  (fn-record-make 2 2 2 "<cppt@example.invalid>" '(9) '("g")
                  "archive-cppt" "subject-cppt" "post-cppt" 1 0))
(defconst *cppt-cursor* (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 2))
(defconst *cppt-ack* (fn-cpe-make 3 3 3 (list :ack *cppt-cursor*)))
(defconst *cppt-history-wire*
  (list *cppt-boot* *cppt-reg* *cppt-article-wire* *cppt-ack*))
; by specification: the flip -- the store's journal slots are retained rows
; (books/held-record.lisp; a wire record is no longer fn-store-event-p): the
; open interns the decoded history in order on a fresh arena (store-intern
; fn-intern-events, keyring nil at generation 0).  The consumer events pass
; through; the article is the row at handle 0, whose bytes are its octets.
(defconst *cppt-history* (fn-hrt-rows *cppt-history-wire* nil 0))
(defconst *cppt-article* (nth 2 *cppt-history*))
(assert-event (and (equal (nth 0 *cppt-history*) *cppt-boot*)
                   (equal (nth 1 *cppt-history*) *cppt-reg*)
                   (equal (nth 3 *cppt-history*) *cppt-ack*)
                   (fn-held-p *cppt-article*)
                   (equal (fn-record-payload *cppt-article*) 0)
                   (equal (fn-hrt-bytes *cppt-history-wire* 0) '(9))))
(defconst *cppt-replayed* (fn-cpe-projection-replay nil *cppt-history* 0))
(assert-event (equal (car *cppt-replayed*) :ok))
(assert-event (fn-cp-statep (cadr *cppt-replayed*)))
(assert-event (equal (nth 3 (cadr *cppt-replayed*)) 4))
(assert-event (equal (nth 7 (fn-cp-find '(3) (nth 5 (cadr *cppt-replayed*)))) 2))
(assert-event (equal (fn-cpe-projection-replay nil *cppt-history* 0)
                     *cppt-replayed*))
(assert-event (equal (fn-cpe-projection-step (cadr *cppt-replayed*) *cppt-boot* 4)
                     '(:refused :sequence)))
(assert-event (equal (fn-cpe-projection-step
                      (cadr (fn-cpe-projection-replay nil (list *cppt-boot*) 0))
                      (fn-cpe-make 1 1 1 '(:bootstrap (1) (2))) 1)
                     '(:refused :duplicate-bootstrap)))
(assert-event (equal (fn-cpe-projection-step nil *cppt-reg* 1)
                     '(:refused :unbootstrapped)))
(assert-event (equal (fn-cpe-projection-step
                      (cadr *cppt-replayed*)
                      (fn-cpe-make 4 4 4 '(:rollover (2))) 4)
                     '(:refused :same-incarnation)))
(defconst *cppt-rolled*
  (fn-cpe-projection-step (cadr *cppt-replayed*)
                           (fn-cpe-make 4 4 4 '(:rollover (8))) 4))
(assert-event (and (equal (car *cppt-rolled*) :ok)
                   (equal (nth 2 (cadr *cppt-rolled*)) '(8))
                   (null (nth 5 (cadr *cppt-rolled*)))))
(assert-event (equal (fn-cpe-projection-step
                      (cadr *cppt-rolled*)
                      (fn-cpe-make 5 5 5 (list :ack *cppt-cursor*)) 5)
                     '(:refused :operation)))
(must-fail-checked (defthm cppt-ack-needs-current-scope
             (equal (car (fn-cpe-projection-step s event expected)) :ok)))
