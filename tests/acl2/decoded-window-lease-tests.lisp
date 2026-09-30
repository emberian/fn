(in-package "ACL2")
(include-book "../../books/decoded-window-lease")
(defconst *pwz-budget* '(10000 0 2 1 20))
(defconst *pwz-start* (mv-nth 1 (mv-list 2 (fn-prl-make-baseline *pwz-budget* '(1000 0 0 0 0)))))
(defconst *pwz-registered* (mv-nth 1 (mv-list 2 (fn-prl-register *pwz-start* 7 '(64 0 1 0 0)))))
(defconst *pwz-descriptor* '(7 100 320 120 40 200 99 250 0))
(defconst *pwz-admitted* (mv-list 3 (fn-pwz-admit *pwz-registered* *pwz-descriptor* '(256 0 0 1 1))))
; KEYSTONE fn-pwz-admit-preserves-pool-funding. REACHABLE POSITIVE.
; Supplied demand is a kernel witness, not selected-runtime adequacy.
(assert-event (and (equal (nth 0 *pwz-admitted*) :admitted)
 (fn-pwz-tokenp (nth 1 *pwz-admitted*))
 (fn-prs-fundedp *pwz-budget* '(1000 0 0 0 0) '(0 0 0 0 0)
                 (fn-prl-nth 1 (nth 2 *pwz-admitted*)))))
; KEYSTONE fn-pwz-admitted-window-holds-file. REACHABLE POSITIVE.
(assert-event (and (equal (nth 0 *pwz-admitted*) :admitted)
 (equal (fn-prl-close-preview (nth 2 *pwz-admitted*) 7) :read-file-held)))
; HYPOTHESIS-REMOVAL / CORRUPTED STATE: funding, no retained hypotheses.
(assert-event (let* ((bad (fn-prl-make nil))
 (r (mv-list 3 (fn-pwz-admit bad *pwz-descriptor* '(256 0 0 1 1)))))
 (and (not (equal (nth 0 r) :admitted))
 (not (fn-prs-fundedp nil (fn-prl-baseline bad) '(0 0 0 0 0)
                       (fn-prl-nth 1 (nth 2 r)))))))
; HYPOTHESIS-REMOVAL: file hold, no retained hypotheses. Unregistered file.
(assert-event (let ((r (mv-list 3 (fn-pwz-admit *pwz-start* *pwz-descriptor* '(256 0 0 1 1)))))
 (and (not (equal (nth 0 r) :admitted))
      (not (equal (fn-prl-close-preview (nth 2 r) 7) :read-file-held)))))
; MUTATION: unknown dictionary and decoded offset beyond N refuse unchanged.
(assert-event (and
 (equal (mv-list 3 (fn-pwz-admit *pwz-registered* (update-nth 8 123 *pwz-descriptor*) '(256 0 0 1 1)))
        (list :invalid-decoded-window-demand nil *pwz-registered*))
 (equal (mv-list 3 (fn-pwz-admit *pwz-registered* (update-nth 5 251 *pwz-descriptor*) '(256 0 0 1 1)))
        (list :invalid-decoded-window-demand nil *pwz-registered*))))
