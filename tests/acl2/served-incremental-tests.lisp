; served-incremental-tests.lisp -- witnesses and teeth for the reader arms
; books/served-catalog.lisp moved off the list model (lane
; served-incremental-1, audit-incremental-2026-10-02 R1, R2, R4): LIST /
; LIST ACTIVE (fn-nntp-list-active-cat), NEXT / LAST
; (fn-nntp-next-or-last-cat, fn-scat-next-number, fn-scat-previous-number),
; the current article (fn-nntp-current-retrieval-cat) and OVER with no
; argument or a Message-ID (fn-nntp-over-current-served-cat,
; fn-nntp-over-msgid-served-cat).
;
; The fixture is three committed articles (fn.test 1, 2, 3; fn.other 1) and
; a fourth withdrawn by a later cancel is not needed: the view is a count.
; Every witness is ground and proved by evaluation.  A REACHABLE witness
; asserts each theorem's whole antecedent and its conclusion; a
; HYPOTHESIS-REMOVAL witness checks every retained hypothesis, the failure
; of the omitted one and the failure of the conclusion, and is followed by
; the must-fail of the theorem without it.  CORRUPTED-STATE witnesses are
; labelled.
(in-package "ACL2")
(include-book "../../books/served-catalog")
(include-book "must-fail-checked")

(defconst *sit-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *sit-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))
(defconst *sit-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *sit-w0* (fn-record-make 0 1 1 "<a@x>" *sit-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *sit-w1* (fn-record-make 1 2 2 "<b@x>" *sit-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *sit-w2* (fn-record-make 2 3 3 "<c@x>" *sit-p2* '("fn.test") "o" "s" "e" 1 5))

(defun sit-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defconst *sit-a* (list *sit-p0* *sit-p1* *sit-p2*))
(defconst *sit-r0* (fn-cat-assign (sit-held *sit-w0* 0 nil) nil))
(defconst *sit-r1* (fn-cat-assign (sit-held *sit-w1* 1 nil) (list *sit-r0*)))
(defconst *sit-r2* (fn-cat-assign (sit-held *sit-w2* 2 nil) (list *sit-r0* *sit-r1*)))
(defconst *sit-c* (list *sit-r0* *sit-r1* *sit-r2*))

(defmacro sit-state (v)
  `(fn-make-state '("fn.test" "fn.other") (list (cons "fn.test" 4) (cons "fn.other" 2))
                  (fn-cat-view-articles ,v *sit-a* *sit-c*) 1 nil nil))

;; The archive with no articles: the view hypothesis fails for it.
(defconst *sit-state0*
  (fn-make-state '("fn.test" "fn.other") (list (cons "fn.test" 4) (cons "fn.other" 2))
                 nil 1 nil nil))

(defmacro sit-at (n) `(fn-nntp-set-cursor (fn-nntp-open-session (sit-state 3)) "fn.test" ,n))
(defconst *sit-server* (fn-nntp-string-octets "news.example.org"))
(defconst *sit-env-closed*
  (fn-nntp-env-with-closed nil nil nil (list (fn-nntp-string-octets "fn.other"))))

;;; fn-scat-next-number-is-next-number, fn-scat-previous-number-is-last-number.

;; REACHABLE: fresh, a group, natural current and view; at view 3 the
;; neighbours of 1 are 2 (next) and none (previous); of 3, none and 2; at
;; view 2 (row 2 not yet visible) the next of 2 is none.
(defthm sit-neighbours
  (and (fn-cnx-freshp *sit-c*) (natp 1) (natp 3) (natp 2)
       (equal (fn-scat-next-number "fn.test" 1 3 *sit-c*) 2)
       (equal (fn-scat-next-number "fn.test" 1 3 *sit-c*)
              (fn-nntp-group-next-number "fn.test" 1 (fn-cat-view-articles 3 *sit-a* *sit-c*)))
       (equal (fn-scat-previous-number "fn.test" 1 3 *sit-c*) 0)
       (equal (fn-scat-previous-number "fn.test" 1 3 *sit-c*)
              (fn-nntp-group-last-number "fn.test" 1 (fn-cat-view-articles 3 *sit-a* *sit-c*)))
       (equal (fn-scat-next-number "fn.test" 3 3 *sit-c*) 0)
       (equal (fn-scat-previous-number "fn.test" 3 3 *sit-c*) 2)
       (equal (fn-scat-previous-number "fn.test" 3 3 *sit-c*)
              (fn-nntp-group-last-number "fn.test" 3 (fn-cat-view-articles 3 *sit-a* *sit-c*)))
       (equal (fn-scat-next-number "fn.test" 2 2 *sit-c*) 0)
       (equal (fn-scat-next-number "fn.test" 2 2 *sit-c*)
              (fn-nntp-group-next-number "fn.test" 2 (fn-cat-view-articles 2 *sit-a* *sit-c*)))
       (equal (fn-scat-next-number "fn.test" 2 3 *sit-c*) 3))
  :rule-classes nil)

;; HYPOTHESIS REMOVAL (natp current): current 1/2; the probe starts at no
;; natural and answers 0, the list model's least number above 1/2 is 1.
(defthm sit-next-number-current-hypotheses
  (and (fn-cnx-freshp *sit-c*) (stringp "fn.test") (natp 3)
       (not (natp 1/2))
       (not (equal (fn-scat-next-number "fn.test" 1/2 3 *sit-c*)
                   (fn-nntp-group-next-number "fn.test" 1/2
                                              (fn-cat-view-articles 3 *sit-a* *sit-c*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm sit-next-number-without-natural-current
   (equal (fn-scat-next-number "fn.test" 1/2 3 *sit-c*)
          (fn-nntp-group-next-number "fn.test" 1/2 (fn-cat-view-articles 3 *sit-a* *sit-c*)))
   :rule-classes nil))

;; HYPOTHESIS REMOVAL (fn-cnx-freshp), CORRUPTED STATE: fn.test 1 bound by
;; row 0, whose Message-ID is not renderable, and again by row 2.  The
;; number table names the first binder (row 0), which is not served, so
;; the probe's next number above 0 is 2; the list model's walk finds row 2
;; at 1.
(defconst *sit-c-bad*
  (list (sit-held (fn-record-make 0 1 1 "bad" *sit-p0* '("fn.test") "o" "s" "e" 1 5)
                  0 '(("fn.test" . 1)))
        *sit-r1*
        (sit-held *sit-w2* 2 '(("fn.test" . 1)))))

(defthm sit-next-number-fresh-hypotheses
  (and (not (fn-cnx-freshp *sit-c-bad*))
       (stringp "fn.test") (natp 0) (natp 3)
       (equal (fn-scat-next-number "fn.test" 0 3 *sit-c-bad*) 2)
       (equal (fn-nntp-group-next-number "fn.test" 0
                                         (fn-cat-view-articles 3 *sit-a* *sit-c-bad*))
              1))
  :rule-classes nil)

(must-fail-checked
 (defthm sit-next-number-without-freshness
   (equal (fn-scat-next-number "fn.test" 0 3 *sit-c-bad*)
          (fn-nntp-group-next-number "fn.test" 0 (fn-cat-view-articles 3 *sit-a* *sit-c-bad*)))
   :rule-classes nil))

;;; fn-nntp-next-or-last-cat-is-next-or-last.

;; REACHABLE: fresh and the archive the view's articles; NEXT from 1 moves
;; to 2 (223), LAST from 1 answers 422, LAST from 3 moves to 2.
(defthm sit-next-or-last
  (and (fn-cnx-freshp *sit-c*)
       (equal (fn-state-articles (sit-state 3)) (fn-cat-view-articles 3 *sit-a* *sit-c*))
       (equal (fn-nntp-next-or-last-cat (sit-at 1) (sit-state 3) :next 3 *sit-a* *sit-c*)
              (fn-nntp-next-or-last (sit-at 1) (sit-state 3) :next *sit-a*))
       (equal (fn-nntp-session-current
               (fn-nntp-result-session
                (fn-nntp-next-or-last-cat (sit-at 1) (sit-state 3) :next 3 *sit-a* *sit-c*)))
              2)
       (equal (fn-nntp-next-or-last-cat (sit-at 1) (sit-state 3) :last 3 *sit-a* *sit-c*)
              (fn-nntp-next-or-last (sit-at 1) (sit-state 3) :last *sit-a*))
       (equal (fn-nntp-next-or-last-cat (sit-at 1) (sit-state 3) :last 3 *sit-a* *sit-c*)
              (fn-nntp-single (sit-at 1) (fn-proto-text "LAST" :no-previous)))
       (equal (fn-nntp-next-or-last-cat (sit-at 3) (sit-state 3) :last 3 *sit-a* *sit-c*)
              (fn-nntp-next-or-last (sit-at 3) (sit-state 3) :last *sit-a*))
       (equal (fn-nntp-session-current
               (fn-nntp-result-session
                (fn-nntp-next-or-last-cat (sit-at 3) (sit-state 3) :last 3 *sit-a* *sit-c*)))
              2))
  :rule-classes nil)

;; HYPOTHESIS REMOVAL (archive = the view's articles): the empty archive;
;; the catalog arm moves to 2, the list model answers 421.
(defthm sit-next-or-last-view-hypotheses
  (and (fn-cnx-freshp *sit-c*)
       (not (equal (fn-state-articles *sit-state0*) (fn-cat-view-articles 3 *sit-a* *sit-c*)))
       (not (equal (fn-nntp-next-or-last-cat (sit-at 1) *sit-state0* :next 3 *sit-a* *sit-c*)
                   (fn-nntp-next-or-last (sit-at 1) *sit-state0* :next *sit-a*))))
  :rule-classes nil)

(must-fail-checked
 (defthm sit-next-or-last-without-view
   (equal (fn-nntp-next-or-last-cat (sit-at 1) *sit-state0* :next 3 *sit-a* *sit-c*)
          (fn-nntp-next-or-last (sit-at 1) *sit-state0* :next *sit-a*))
   :rule-classes nil))

;;; fn-nntp-current-retrieval-cat-is-current-retrieval.

;; REACHABLE: the current article 2 of fn.test, BODY and STAT; the archive
;; arm answers the same; it is found (not 420).
(defthm sit-current-retrieval
  (and (fn-cnx-freshp *sit-c*)
       (equal (fn-state-articles (sit-state 3)) (fn-cat-view-articles 3 *sit-a* *sit-c*))
       (equal (fn-nntp-current-retrieval-cat (sit-at 2) :body 3 *sit-a* *sit-c*)
              (fn-nntp-current-retrieval (sit-at 2) (sit-state 3) :body *sit-a*))
       (equal (fn-nntp-current-retrieval-cat (sit-at 2) :stat 3 *sit-a* *sit-c*)
              (fn-nntp-current-retrieval (sit-at 2) (sit-state 3) :stat *sit-a*))
       (not (equal (fn-nntp-current-retrieval-cat (sit-at 2) :stat 3 *sit-a* *sit-c*)
                   (fn-nntp-single (sit-at 2) (fn-proto-text * :no-current)))))
  :rule-classes nil)

(defthm sit-current-retrieval-view-hypotheses
  (and (fn-cnx-freshp *sit-c*)
       (not (equal (fn-state-articles *sit-state0*) (fn-cat-view-articles 3 *sit-a* *sit-c*)))
       (not (equal (fn-nntp-current-retrieval-cat (sit-at 2) :stat 3 *sit-a* *sit-c*)
                   (fn-nntp-current-retrieval (sit-at 2) *sit-state0* :stat *sit-a*))))
  :rule-classes nil)

(must-fail-checked
 (defthm sit-current-retrieval-without-view
   (equal (fn-nntp-current-retrieval-cat (sit-at 2) :stat 3 *sit-a* *sit-c*)
          (fn-nntp-current-retrieval (sit-at 2) *sit-state0* :stat *sit-a*))
   :rule-classes nil))

;;; fn-nntp-over-current-served-cat-is-col, fn-nntp-over-msgid-served-cat-is-col.

(defthm sit-over-current-and-msgid
  (and (fn-cnx-freshp *sit-c*)
       (equal (fn-state-articles (sit-state 3)) (fn-cat-view-articles 3 *sit-a* *sit-c*))
       (equal (fn-nntp-over-current-served-cat (sit-at 2) *sit-server* 3 *sit-a* *sit-c*)
              (fn-nntp-over-current-served-col (sit-at 2) (sit-state 3) *sit-server* *sit-a* *sit-c*))
       (not (equal (fn-nntp-over-current-served-cat (sit-at 2) *sit-server* 3 *sit-a* *sit-c*)
                   (fn-nntp-single (sit-at 2) "420 no current article")))
       (equal (fn-nntp-over-msgid-served-cat (sit-at 2) (fn-nntp-string-octets "<c@x>")
                                             *sit-server* 3 *sit-a* *sit-c*)
              (fn-nntp-over-msgid-served-col (sit-at 2) (sit-state 3) (fn-nntp-string-octets "<c@x>")
                                             *sit-server* *sit-a* *sit-c*))
       (not (equal (fn-nntp-over-msgid-served-cat (sit-at 2) (fn-nntp-string-octets "<c@x>")
                                                  *sit-server* 3 *sit-a* *sit-c*)
                   (fn-nntp-single (sit-at 2) "430 no article with that message-id"))))
  :rule-classes nil)

(defthm sit-over-current-view-hypotheses
  (and (fn-cnx-freshp *sit-c*)
       (not (equal (fn-state-articles *sit-state0*) (fn-cat-view-articles 3 *sit-a* *sit-c*)))
       (not (equal (fn-nntp-over-current-served-cat (sit-at 2) *sit-server* 3 *sit-a* *sit-c*)
                   (fn-nntp-over-current-served-col (sit-at 2) *sit-state0* *sit-server*
                                                    *sit-a* *sit-c*)))
       (not (equal (fn-nntp-over-msgid-served-cat (sit-at 2) (fn-nntp-string-octets "<c@x>")
                                                  *sit-server* 3 *sit-a* *sit-c*)
                   (fn-nntp-over-msgid-served-col (sit-at 2) *sit-state0* (fn-nntp-string-octets "<c@x>")
                                                  *sit-server* *sit-a* *sit-c*))))
  :rule-classes nil)

(must-fail-checked
 (defthm sit-over-msgid-without-view
   (equal (fn-nntp-over-msgid-served-cat (sit-at 2) (fn-nntp-string-octets "<c@x>")
                                         *sit-server* 3 *sit-a* *sit-c*)
          (fn-nntp-over-msgid-served-col (sit-at 2) *sit-state0* (fn-nntp-string-octets "<c@x>")
                                         *sit-server* *sit-a* *sit-c*))
   :rule-classes nil))

;;; fn-nntp-list-active-cat-is-list-command.

(defconst *sit-args-active* (list (fn-nntp-string-octets "ACTIVE")))
(defconst *sit-args-active-wild* (list (fn-nntp-string-octets "ACTIVE")
                                       (fn-nntp-string-octets "fn.t*")))
(defconst *sit-args-newsgroups* (list (fn-nntp-string-octets "NEWSGROUPS")))

;; REACHABLE: every antecedent (the LIST form, fresh, a state, the view),
;; LIST, LIST ACTIVE and LIST ACTIVE fn.t*, with and without a closed
;; group; the lines carry fn.test 3 1 and fn.other 1 1.
(defthm sit-list-active
  (and (fn-scat-list-active-formp nil)
       (fn-scat-list-active-formp *sit-args-active*)
       (fn-scat-list-active-formp *sit-args-active-wild*)
       (fn-cnx-freshp *sit-c*) (fn-statep (sit-state 3))
       (equal (fn-state-articles (sit-state 3)) (fn-cat-view-articles 3 *sit-a* *sit-c*))
       (equal (fn-nntp-list-active-cat (fn-nntp-open-session (sit-state 3)) (sit-state 3)
                                       (fn-nntp-env-closed nil) nil 3 *sit-c*)
              (fn-nntp-list-command (fn-nntp-open-session (sit-state 3)) (sit-state 3) nil nil))
       (equal (fn-scat-active-lines (sit-state 3) '("fn.test" "fn.other") nil nil 3 *sit-c*)
              (list (fn-nntp-string-octets "fn.test 3 1 y")
                    (fn-nntp-string-octets "fn.other 1 1 y")))
       (equal (fn-nntp-list-active-cat (fn-nntp-open-session (sit-state 3)) (sit-state 3)
                                       (fn-nntp-env-closed *sit-env-closed*) *sit-args-active* 3 *sit-c*)
              (fn-nntp-list-command (fn-nntp-open-session (sit-state 3)) (sit-state 3)
                                    *sit-env-closed* *sit-args-active*))
       (equal (fn-scat-active-lines (sit-state 3) '("fn.test" "fn.other")
                                    (fn-nntp-env-closed *sit-env-closed*) t 3 *sit-c*)
              (list (fn-nntp-string-octets "fn.test 3 1 y")
                    (fn-nntp-string-octets "fn.other 1 1 n")))
       (equal (fn-nntp-list-active-cat (fn-nntp-open-session (sit-state 3)) (sit-state 3)
                                       (fn-nntp-env-closed nil) *sit-args-active-wild* 3 *sit-c*)
              (fn-nntp-list-command (fn-nntp-open-session (sit-state 3)) (sit-state 3)
                                    nil *sit-args-active-wild*)))
  :rule-classes nil)

;; HYPOTHESIS REMOVAL (the LIST form): LIST NEWSGROUPS; the arm answers
;; the active list, LIST NEWSGROUPS the descriptions.
(defthm sit-list-active-form-hypotheses
  (and (fn-cnx-freshp *sit-c*) (fn-statep (sit-state 3))
       (equal (fn-state-articles (sit-state 3)) (fn-cat-view-articles 3 *sit-a* *sit-c*))
       (not (fn-scat-list-active-formp *sit-args-newsgroups*))
       (not (equal (fn-nntp-list-active-cat (fn-nntp-open-session (sit-state 3)) (sit-state 3)
                                            (fn-nntp-env-closed nil) *sit-args-newsgroups* 3 *sit-c*)
                   (fn-nntp-list-command (fn-nntp-open-session (sit-state 3)) (sit-state 3)
                                         nil *sit-args-newsgroups*))))
  :rule-classes nil)

(must-fail-checked
 (defthm sit-list-active-without-form
   (equal (fn-nntp-list-active-cat (fn-nntp-open-session (sit-state 3)) (sit-state 3)
                                   (fn-nntp-env-closed nil) *sit-args-newsgroups* 3 *sit-c*)
          (fn-nntp-list-command (fn-nntp-open-session (sit-state 3)) (sit-state 3)
                                nil *sit-args-newsgroups*))
   :rule-classes nil))

;; HYPOTHESIS REMOVAL (archive = the view's articles): the empty archive;
;; the catalog line says fn.test 3 1, the list model the watermark 4 3...
(defthm sit-list-active-view-hypotheses
  (and (fn-scat-list-active-formp nil) (fn-cnx-freshp *sit-c*) (fn-statep *sit-state0*)
       (not (equal (fn-state-articles *sit-state0*) (fn-cat-view-articles 3 *sit-a* *sit-c*)))
       (not (equal (fn-nntp-list-active-cat (fn-nntp-open-session *sit-state0*) *sit-state0*
                                            (fn-nntp-env-closed nil) nil 3 *sit-c*)
                   (fn-nntp-list-command (fn-nntp-open-session *sit-state0*) *sit-state0* nil nil))))
  :rule-classes nil)

(must-fail-checked
 (defthm sit-list-active-without-view
   (equal (fn-nntp-list-active-cat (fn-nntp-open-session *sit-state0*) *sit-state0*
                                   (fn-nntp-env-closed nil) nil 3 *sit-c*)
          (fn-nntp-list-command (fn-nntp-open-session *sit-state0*) *sit-state0* nil nil))
   :rule-classes nil))

;;; Codex r51 F3: the edge cases, every arm at once.  A catalog whose row 1
;;; (<b@x>, fn.test 2 and fn.other 1) is withdrawn at version 2, and a state
;;; with a third, never-posted group.

(defconst *sit-cw* (fn-cat-mark-withdrawn 1 2 2 *sit-c*))
(defmacro sit-wstate (v)
  `(fn-make-state '("fn.test" "fn.other" "fn.empty")
                  (list (cons "fn.test" 4) (cons "fn.other" 2) (cons "fn.empty" 1))
                  (fn-cat-view-articles ,v *sit-a* *sit-cw*) 1 nil nil))
(defmacro sit-wat (n) `(fn-nntp-set-cursor (fn-nntp-open-session (sit-wstate 3)) "fn.test" ,n))

;; REACHABLE (every keystone's antecedent holds: fresh, a state, the view):
;; LIST shows the EMPTY group as 0 1 (RFC 3977 6.1.1.2's preferred empty
;; form) and the ALL-WITHDRAWN group fn.other as 1 2; NEXT from 1 skips the
;; withdrawn 2 to 3 and LAST from 3 to 1; the WITHDRAWN CURRENT article 2
;; answers 420 to STAT and to OVER; OVER <msgid> of the withdrawn <b@x> and
;; of the ABSENT <zz@x> answer 430.  Each equal to the list model.
(defthm sit-edges
  (and (fn-cnx-freshp *sit-cw*) (fn-statep (sit-wstate 3))
       (fn-scat-list-active-formp nil)
       (equal (fn-state-articles (sit-wstate 3)) (fn-cat-view-articles 3 *sit-a* *sit-cw*))
       (equal (len (fn-cat-view-articles 3 *sit-a* *sit-cw*)) 2)
       (equal (fn-scat-active-lines (sit-wstate 3) '("fn.test" "fn.other" "fn.empty") nil nil 3 *sit-cw*)
              (list (fn-nntp-string-octets "fn.test 3 1 y") (fn-nntp-string-octets "fn.other 1 2 y")
                    (fn-nntp-string-octets "fn.empty 0 1 y")))
       (equal (fn-nntp-list-active-cat (fn-nntp-open-session (sit-wstate 3)) (sit-wstate 3)
                                       (fn-nntp-env-closed nil) nil 3 *sit-cw*)
              (fn-nntp-list-command (fn-nntp-open-session (sit-wstate 3)) (sit-wstate 3) nil nil))
       (equal (fn-nntp-next-or-last-cat (sit-wat 1) (sit-wstate 3) :next 3 *sit-a* *sit-cw*)
              (fn-nntp-next-or-last (sit-wat 1) (sit-wstate 3) :next *sit-a*))
       (equal (fn-nntp-session-current
               (fn-nntp-result-session (fn-nntp-next-or-last-cat (sit-wat 1) (sit-wstate 3) :next 3 *sit-a* *sit-cw*)))
              3)
       (equal (fn-nntp-next-or-last-cat (sit-wat 3) (sit-wstate 3) :last 3 *sit-a* *sit-cw*)
              (fn-nntp-next-or-last (sit-wat 3) (sit-wstate 3) :last *sit-a*))
       (equal (fn-nntp-session-current
               (fn-nntp-result-session (fn-nntp-next-or-last-cat (sit-wat 3) (sit-wstate 3) :last 3 *sit-a* *sit-cw*)))
              1)
       (equal (fn-nntp-current-retrieval-cat (sit-wat 2) :stat 3 *sit-a* *sit-cw*)
              (fn-nntp-current-retrieval (sit-wat 2) (sit-wstate 3) :stat *sit-a*))
       (equal (fn-nntp-current-retrieval-cat (sit-wat 2) :stat 3 *sit-a* *sit-cw*)
              (fn-nntp-single (sit-wat 2) (fn-proto-text * :no-current)))
       (equal (fn-nntp-over-current-served-cat (sit-wat 2) *sit-server* 3 *sit-a* *sit-cw*)
              (fn-nntp-over-current-served-col (sit-wat 2) (sit-wstate 3) *sit-server* *sit-a* *sit-cw*))
       (equal (fn-nntp-over-current-served-cat (sit-wat 2) *sit-server* 3 *sit-a* *sit-cw*)
              (fn-nntp-single (sit-wat 2) "420 no current article"))
       (equal (fn-nntp-over-msgid-served-cat (sit-wat 1) (fn-nntp-string-octets "<b@x>") *sit-server* 3 *sit-a* *sit-cw*)
              (fn-nntp-over-msgid-served-col (sit-wat 1) (sit-wstate 3) (fn-nntp-string-octets "<b@x>")
                                             *sit-server* *sit-a* *sit-cw*))
       (equal (fn-nntp-over-msgid-served-cat (sit-wat 1) (fn-nntp-string-octets "<b@x>") *sit-server* 3 *sit-a* *sit-cw*)
              (fn-nntp-single (sit-wat 1) "430 no article with that message-id"))
       (equal (fn-nntp-over-msgid-served-cat (sit-wat 1) (fn-nntp-string-octets "<zz@x>") *sit-server* 3 *sit-a* *sit-cw*)
              (fn-nntp-over-msgid-served-col (sit-wat 1) (sit-wstate 3) (fn-nntp-string-octets "<zz@x>")
                                             *sit-server* *sit-a* *sit-cw*))
       (equal (fn-nntp-over-msgid-served-cat (sit-wat 1) (fn-nntp-string-octets "<zz@x>") *sit-server* 3 *sit-a* *sit-cw*)
              (fn-nntp-single (sit-wat 1) "430 no article with that message-id")))
  :rule-classes nil)

;; HYPOTHESIS REMOVAL (fn-cnx-freshp), CORRUPTED STATE (*sit-c-bad* above:
;; fn.test 1 bound by the unrenderable row 0 and by row 2), for LAST, the
;; current article and OVER with no argument.  The view equation holds; the
;; number table names row 0, the list model's walk row 2, and the replies
;; differ.
(defmacro sit-bstate (v)
  `(fn-make-state '("fn.test" "fn.other") (list (cons "fn.test" 4) (cons "fn.other" 2))
                  (fn-cat-view-articles ,v *sit-a* *sit-c-bad*) 1 nil nil))
(defmacro sit-bat (n) `(fn-nntp-set-cursor (fn-nntp-open-session (sit-bstate 3)) "fn.test" ,n))

(defthm sit-fresh-hypotheses
  (and (not (fn-cnx-freshp *sit-c-bad*))
       (equal (fn-state-articles (sit-bstate 3)) (fn-cat-view-articles 3 *sit-a* *sit-c-bad*))
       (not (equal (fn-nntp-current-retrieval-cat (sit-bat 1) :stat 3 *sit-a* *sit-c-bad*)
                   (fn-nntp-current-retrieval (sit-bat 1) (sit-bstate 3) :stat *sit-a*)))
       (not (equal (fn-nntp-next-or-last-cat (sit-bat 2) (sit-bstate 3) :last 3 *sit-a* *sit-c-bad*)
                   (fn-nntp-next-or-last (sit-bat 2) (sit-bstate 3) :last *sit-a*)))
       (not (equal (fn-nntp-over-current-served-cat (sit-bat 1) *sit-server* 3 *sit-a* *sit-c-bad*)
                   (fn-nntp-over-current-served-col (sit-bat 1) (sit-bstate 3) *sit-server* *sit-a* *sit-c-bad*))))
  :rule-classes nil)
