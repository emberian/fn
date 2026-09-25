; Teeth for books/source-projection-bridge.lisp.  A concrete agent and two
; sources, one without and one with a reserved (FN-Statement) field; the
; stored record is this agent's block with neither field generated, then
; the source, as fn-inj-decide writes it for a source with a Message-ID and
; a Date.
(in-package "ACL2")
(include-book "../../books/source-projection-bridge")
(include-book "std/testing/must-fail" :dir :system)

(defun spjt-codes (cs)
  (if (consp cs) (cons (char-code (car cs)) (spjt-codes (cdr cs))) nil))
(defun spjt-oct (s) (spjt-codes (coerce s 'list)))

(defconst *spjt-agent* (spjt-oct "news.example"))
(defconst *spjt-msgid* (spjt-oct "<a@b.example>"))
(defconst *spjt-date* (spjt-oct "Thu, 24 Sep 2026 00:00:00 +0000"))
(defun spjt-crlf (s) (append (spjt-oct s) '(13 10)))
(defconst *spjt-native*
  (append (spjt-crlf "From: a@b.example") (spjt-crlf "Subject: s")
          (spjt-crlf "Date: Thu, 24 Sep 2026 00:00:00 +0000")
          (spjt-crlf "Message-ID: <a@b.example>") (spjt-crlf "Newsgroups: fn.test")
          '(13 10) (spjt-crlf "body")))
(defconst *spjt-carrier*
  (append (spjt-crlf "From: a@b.example") (spjt-crlf "FN-Statement: xyz")
          (spjt-crlf "Subject: s")
          (spjt-crlf "Date: Thu, 24 Sep 2026 00:00:00 +0000")
          (spjt-crlf "Message-ID: <a@b.example>") (spjt-crlf "Newsgroups: fn.test")
          '(13 10) (spjt-crlf "body")))
(defun spjt-stored (agent gid gdate src)
  (append (fn-inj-prefix *spjt-date* *spjt-msgid* agent gid gdate) src))
(defun spjt-proj (octets)
  (fn-hc-authored-source (fn-article-result-article (fn-article-parse octets))))
(defun spjt-ok (octets) (fn-article-result-okp (fn-article-parse octets)))

; Witnesses: every hypothesis holds, both sources satisfy the carrier's
; source profile, and the projections agree.
(assert-event
 (and (fn-spj-line-freep *spjt-agent*)
      (spjt-ok *spjt-native*) (spjt-ok (spjt-stored *spjt-agent* nil nil *spjt-native*))
      (spjt-ok *spjt-carrier*) (spjt-ok (spjt-stored *spjt-agent* nil nil *spjt-carrier*))
      (fn-hc-required-sourcep (fn-article-result-article (fn-article-parse *spjt-native*)))
      (fn-hc-required-sourcep (fn-article-result-article (fn-article-parse *spjt-carrier*)))
      (equal (spjt-proj (spjt-stored *spjt-agent* nil nil *spjt-native*))
             (spjt-proj *spjt-native*))
      (equal (spjt-proj (spjt-stored *spjt-agent* nil nil *spjt-carrier*))
             (spjt-proj *spjt-carrier*))))

; The injection inverse returns each source, and the two subjects agree on
; the native source and differ on the carrier source by exactly its
; reserved line.
(assert-event
 (let ((s1 (spjt-stored *spjt-agent* nil nil *spjt-native*))
       (s2 (spjt-stored *spjt-agent* nil nil *spjt-carrier*)))
   (and (equal (fn-inj-source-of s1 *spjt-agent* *spjt-msgid*) (cons t *spjt-native*))
        (equal (fn-inj-source-of s2 *spjt-agent* *spjt-msgid*) (cons t *spjt-carrier*))
        (equal (spjt-proj s1) *spjt-native*)
        (equal (spjt-proj s2) *spjt-native*)
        (not (equal (spjt-proj s2) *spjt-carrier*)))))

; Drop "no generated field": a generated Message-ID line is not reserved.
(assert-event
 (and (spjt-ok (spjt-stored *spjt-agent* t nil *spjt-native*))
      (not (fn-hc-reserved-namep (spjt-oct "message-id")))))
(must-fail
 (assert-event (equal (spjt-proj (spjt-stored *spjt-agent* t nil *spjt-native*))
                      (spjt-proj *spjt-native*))))

; Drop the line-free agent: a line break in the agent splits the Path line
; and the second half is a field the projection keeps.
(defconst *spjt-bad-agent* (append (spjt-oct "x") '(13 10) (spjt-oct "X-Y: z")))
(assert-event
 (and (not (fn-spj-line-freep *spjt-bad-agent*))
      (spjt-ok (spjt-stored *spjt-bad-agent* nil nil *spjt-native*))))
(must-fail
 (assert-event (equal (spjt-proj (spjt-stored *spjt-bad-agent* nil nil *spjt-native*))
                      (spjt-proj *spjt-native*))))

; Drop the source's own parse: a leading continuation line fails alone and
; folds into Injection-Info behind the block.
(defconst *spjt-folded* (append (spjt-crlf " tail") *spjt-native*))
(assert-event
 (and (not (spjt-ok *spjt-folded*))
      (spjt-ok (spjt-stored *spjt-agent* nil nil *spjt-folded*))))
(must-fail
 (assert-event (equal (spjt-proj (spjt-stored *spjt-agent* nil nil *spjt-folded*))
                      (spjt-proj *spjt-folded*))))
