; Teeth for the actual configuration capture boundary; renderer bytes/steps
; are exercised separately by native_article_stream_source.lisp.
(in-package "ACL2")
(include-book "../../books/article-stream-server")

(defconst *asrv-login*
  (fn-auth-make-session nil nil (fn-nntp-string-octets "alice")
                        '(:principal) nil nil nil nil 0))
(defconst *asrv-archive*
  (fn-make-state '("fn.mod" "fn.queue")
                 '(("fn.mod" . 1) ("fn.queue" . 1)) nil 0 nil nil))
(defconst *asrv-server* (fn-nntp-string-octets "node:119.example"))
(defconst *asrv-config*
  (fn-inj-make-config-full
   t (fn-nntp-string-octets "node.example")
   (list (fn-nntp-string-octets "fn.mod") (fn-nntp-string-octets "fn.queue"))
   1048576 (list nil nil *asrv-server*)
   (list (list :moderated (fn-nntp-string-octets "fn.mod")
               (fn-nntp-string-octets "fn.queue")
               (list (fn-nntp-string-octets "alice"))))))

; Reachable moderator changes the status projection, but not the listing.
(assert-event
 (and (fn-auth-session-shapep *asrv-login*)
      (fn-inj-config-shapep *asrv-config*)
      (fn-xref-serverp *asrv-server*)
      (not (equal (fn-auth-moderation-config *asrv-login* *asrv-config*) *asrv-config*))
      (equal (fn-asto-server-candidate *asrv-config*) *asrv-server*)
      (equal (fn-nntp-xref-server
              (fn-post-command-env
               (fn-auth-view-config *asrv-login*
                 (fn-auth-moderation-config *asrv-login* *asrv-config*) *asrv-archive*)
               nil nil (list :command (fn-nntp-string-octets "ARTICLE 1"))))
             (if (fn-xref-serverp (fn-asto-server-candidate *asrv-config*))
                 (fn-asto-server-candidate *asrv-config*) nil))))

; Mutation: substituting another listing's server refutes the conclusion.
(assert-event
 (let* ((other (fn-inj-make-config-listed nil nil nil 0 '(nil nil (88))))
        (wrong (fn-asto-server-candidate other)))
   (and (fn-xref-serverp wrong)
        (not (equal wrong (fn-nntp-xref-server
                          (fn-post-command-env *asrv-config* nil nil
                           (list :command (fn-nntp-string-octets "HEAD 1")))))))))

; Corrupted/improper server candidate is retained for incremental rejection;
; the old reference omits Xref, without normalizing it into a valid identity.
(assert-event
 (let ((bad (fn-inj-make-config-listed t nil nil 1 '(nil nil (65 . 66)))))
   (and (equal (fn-asto-server-candidate bad) '(65 . 66))
        (not (fn-xref-serverp (fn-asto-server-candidate bad)))
        (equal (fn-nntp-xref-server
                (fn-post-command-env bad nil nil
                 (list :command (fn-nntp-string-octets "ARTICLE 1")))) nil))))
