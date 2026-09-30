(in-package "ACL2")
(include-book "page-window-lease-tests")
(include-book "../../books/page-window-executor")
(defconst *pwx-idle* (fn-pxe-new 0))
(defconst *pwx-acquired* (mv-list 3 (fn-pwx-acquire *prw-held* *pwx-idle* *prw-token*)))
(defconst *pwx-worker* (nth 1 *pwx-acquired*))
(defconst *pwx-held* (nth 2 *pwx-acquired*))
(defconst *pwx-returned* (mv-list 3 (fn-pwx-return *pwx-held* *pwx-worker* *prw-token*)))
(defconst *pwx-worker-returned* (nth 1 *pwx-returned*))
(defconst *pwx-held-returned* (nth 2 *pwx-returned*))
(defconst *pwx-released* (mv-list 3 (fn-pwx-release *pwx-held-returned* *pwx-worker-returned* *prw-token*)))
; KEYSTONE fn-pwx-return-keeps-all-charges. REACHABLE POSITIVE.
(assert-event (and (equal (nth 0 *pwx-acquired*) :assigned)
  (equal (nth 0 *pwx-returned*) :returned)
  (equal (fn-prl-nth 1 *pwx-held-returned*) (fn-prl-nth 1 *pwx-held*))
  (equal (fn-prl-close-preview *pwx-held-returned* 11) :read-file-held)))
; KEYSTONE fn-pwx-release-requires-exact-returned-window-and-slot.
; REACHABLE POSITIVE: full antecedent and every conjunct of the conclusion.
(assert-event (and (equal (nth 0 *pwx-released*) :released)
  (fn-pwx-boundp *pwx-held-returned* *pwx-worker-returned* *prw-token* :returned)
  (equal (nth 0 (mv-list 2 (fn-prw-release *pwx-held-returned* *prw-token*))) :released)
  (equal (nth 1 *pwx-released*) (list (fn-prl-nth 0 *pwx-worker-returned*)
                                   (fn-prl-nth 1 *pwx-worker-returned*) :idle nil))
  (equal (nth 2 *pwx-released*) (nth 1 (mv-list 2 (fn-prw-release *pwx-held-returned* *prw-token*))))))
; KEYSTONE fn-pwx-release-requires-exact-returned-window-and-slot.
; HYPOTHESIS-REMOVAL: no retained hypotheses; running is not returned.
(assert-event (let ((r (mv-list 3 (fn-pwx-release *pwx-held* *pwx-worker* *prw-token*))))
  (and (not (equal (nth 0 r) :released))
       (not (fn-pwx-boundp *pwx-held* *pwx-worker* *prw-token* :returned)))))
; KEYSTONE fn-pwx-other-request-cannot-return-or-release.
; REACHABLE POSITIVE: mutated payload offset retains legacy projection.
(assert-event (let ((token (update-nth 7 0 *prw-token*)))
  (and (not (equal (fn-prl-nth 3 *pwx-worker*) token))
       (equal (mv-list 3 (fn-pwx-return *pwx-held* *pwx-worker* token))
              (list :stale-job *pwx-worker* *pwx-held*))
       (equal (mv-list 3 (fn-pwx-release *pwx-held* *pwx-worker* token))
              (list :stale-job *pwx-worker* *pwx-held*)))))
; KEYSTONE fn-pwx-other-request-cannot-return-or-release.
; HYPOTHESIS-REMOVAL: no retained hypotheses; exact request does return.
(assert-event (and (equal (fn-prl-nth 3 *pwx-worker*) *prw-token*)
  (not (equal *pwx-returned* (list :stale-job *pwx-worker* *pwx-held*)))))
; KEYSTONE fn-pwx-acquire-preserves-all-charges. REACHABLE POSITIVE.
(assert-event (and (equal (nth 0 *pwx-acquired*) :assigned)
  (equal (fn-prl-nth 1 *pwx-held*) (fn-prl-nth 1 *prw-held*))))
; MUTATION: slot zero is a real owner; another idle worker cannot steal it.
(assert-event (equal (mv-list 3 (fn-pwx-acquire *pwx-held* (fn-pxe-new 1) *prw-token*))
                    (list :stale-job (fn-pxe-new 1) *pwx-held*)))
; MUTATION: returning/releasing the right request through the wrong slot fails.
(assert-event (and
  (equal (mv-list 3 (fn-pwx-return *pwx-held* (update-nth 0 1 *pwx-worker*) *prw-token*))
         (list :stale-job (update-nth 0 1 *pwx-worker*) *pwx-held*))
  (equal (mv-list 3 (fn-pwx-release *pwx-held-returned* (update-nth 0 1 *pwx-worker-returned*) *prw-token*))
         (list :stale-job (update-nth 0 1 *pwx-worker-returned*) *pwx-held-returned*))))
; Worker1 remains unavailable through output borrow, even after actual return.
(assert-event (equal (nth 0 (mv-list 3 (fn-prw-admit *pwx-held-returned* *prw-descriptor* '(256 0 0 1 1))))
                    :read-resources-unavailable))
; Final cleanup makes the slot reusable by the ordinary executor, exactly once.
(assert-event (and (fn-pxe-rowp (nth 1 *pwx-released*))
  (equal (fn-prl-close-preview (nth 2 *pwx-released*) 11) :closable)
  (equal (mv-list 3 (fn-pwx-release (nth 2 *pwx-released*) (nth 1 *pwx-released*) *prw-token*))
         (list :stale-job (nth 1 *pwx-released*) (nth 2 *pwx-released*)))))
