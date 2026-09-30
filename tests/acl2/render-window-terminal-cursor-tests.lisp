; Internal logical storage fixtures, not actual epilogue or funded admission.
(in-package "ACL2")
(include-book "../../books/render-window-terminal-cursor")

(defconst *prwt-test-token* '(:window 17 3 0 200 0 100 5 55))
(defconst *prwt-test-query* '(:index-query 29 1 0 1))
(defconst *prwt-test-root*
  (list :render-window *prwt-test-token* :source :recipient
        *prwt-test-query* :origin 4))
(defconst *prwt-test-row* (list *prwt-test-token* '(10 0 0 1 0) :window :returned))
(defconst *prwt-test-other* '((:window 18 3 0 200 0 100 5 55) (20 0 0 1 0) :window :running))
(defconst *prwt-test-rows* (list *prwt-test-other* *prwt-test-row*))

(assert-event
 (let ((initial (fn-prwt-start *prwt-test-root* 7 *prwt-test-rows*)))
  (mv-let (cursor left) (fn-prwt-run initial 1)
   (and (equal cursor (fn-prwt-one initial))
        (equal left 0)
        (eq (fn-prl-nth 8 cursor) :scan)
        (equal (fn-prl-nth 1 cursor) *prwt-test-token*)
        (not (fn-prl-nth 10 cursor))
        (not (fn-prl-nth 11 cursor))
        (equal (fn-prl-nth 2 cursor) 7)
        (equal (fn-prl-nth 3 cursor) *prwt-test-rows*)
        (equal (fn-prl-nth 9 cursor) *prwt-test-root*)
        (equal (fn-prl-nth 5 cursor) (list *prwt-test-other*))))))

(assert-event
 (let ((initial (fn-prwt-start *prwt-test-root* 7 *prwt-test-rows*)))
  (mv-let (cursor left) (fn-prwt-run initial 8)
   (and (equal left 3)
        (eq (fn-prl-nth 8 cursor) :commit-ready)
        (equal (fn-prl-nth 1 cursor) *prwt-test-token*)
        (equal (fn-prl-nth 2 cursor) 7)
        (not (fn-prl-nth 10 cursor))
        (not (fn-prl-nth 11 cursor))
        (equal (fn-prl-nth 6 cursor) (list *prwt-test-other*))
        (equal (fn-prl-nth 7 cursor) *prwt-test-row*)
        (equal (fn-prl-nth 3 cursor) *prwt-test-rows*)
        (equal (fn-prl-nth 9 cursor) *prwt-test-root*)
        (mv-let (again remaining) (fn-prwt-run cursor 8)
          (and (equal again cursor) (equal remaining 8)))))))
