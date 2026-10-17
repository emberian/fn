; Critical restricted-dispatch witnesses.  The archive is produced by three
; acceptance prepare/complete transitions, then a real served open selects it.
(in-package "ACL2")
(include-book "../../books/defkeystone")
(defconst *s11av-archive*
 (fn-accept-complete
  (fn-accept-prepare
   (fn-accept-complete
    (fn-accept-prepare
     (fn-accept-complete
      (fn-accept-prepare (fn-initial-state '("fn.test" "fn.other"))
                         1 "<a@x>" 0 '("fn.test") 5) 0 1 :durable)
     2 "<b@x>" 1 '("fn.test" "fn.other") 5) 1 2 :durable)
   3 "<c@x>" 2 '("fn.test") 5) 2 3 :durable))
(assert-event (and (fn-nntp-projectionp *s11av-archive*)
                   (equal (len (fn-state-articles *s11av-archive*)) 3)))

(defun s11av-load-cat (rows fn-cat)
 (declare (xargs :stobjs fn-cat :verify-guards nil))
 (if (consp rows) (let ((fn-cat (fn-cat-commit (car rows) fn-cat))) (s11av-load-cat (cdr rows) fn-cat)) fn-cat))
(defun s11av-dispatch-drop-effects (conn event live lver arts cache fn-arena fn-cat) (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat) :verify-guards nil)) (let* ((v (fn-scr-view-of (fn-served-pinned-version (fn-served-conn-pinned conn)) fn-cat)) (r (fn-av-scr-auth-step (fn-served-conn-session conn) live lver arts cache (fn-served-conn-archive conn) (fn-served-conn-pinned-index conn) (fn-served-conn-verdicts conn) (fn-served-conn-config conn) (fn-served-conn-observation conn) (fn-served-conn-injection conn) event v fn-arena fn-cat)) (effects nil) (submission (fn-post-result-submission r)) (wire (fn-served-conn-wire conn)) (wire2 (if (fn-post-offeredp effects) (fn-wire-result-state (fn-wire-begin-article-with-line-limit wire (fn-wire-article-line-limit wire))) wire))) (fn-served-make-result (fn-served-make-conn-live wire2 (fn-post-result-session r) (fn-served-conn-archive conn) (fn-served-conn-config conn) (fn-served-conn-observation conn) (fn-served-conn-injection conn) (fn-served-conn-verdicts conn) (fn-served-conn-group-index conn) (fn-served-conn-control conn) (fn-served-conn-pinned conn) (fn-served-conn-live conn)) (mbe :logic (append effects (if submission (list (fn-served-submit-effect submission (fn-served-login (fn-served-conn-session conn)) (fn-served-account (fn-served-conn-session conn)))) nil)) :exec (fn-ag-append effects (if submission (list (fn-served-submit-effect submission (fn-served-login (fn-served-conn-session conn)) (fn-served-account (fn-served-conn-session conn)))) nil))))))

(defteeth-check (fn-av-scr-auth-delegate-restricted-is-reference fn-av-scr-dispatch-core-restricted-is-reference))
