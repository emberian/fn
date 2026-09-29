; Teeth for PKT-443: a view whose every article is withdrawn (two signed
; cancels by one author naming each other) has no buckets, and the pinned
; index still carries its control pin, so a read by Message-ID answers
; `430 withdrawn' (books/served.lisp fn-served-conn-pinned-index;
; books/owner-control-read.lisp fn-octl-pinned-index-of-served-conn and
; fn-own-read-of-a-withdrawn-article-answers-430-withdrawn).  The subject is
; fn-octl-reply, the pinned dispatcher's reply over the served connection
; fn-own-read builds (fn-own-read-archive-command-is-the-pinned-dispatcher).
(in-package "ACL2")
(include-book "control-served-tests")
(include-book "../../books/owner-control-read")
(include-book "must-fail-checked")

(defconst *sev-c1* (csv-cancel "<mutual-1@example.invalid>" "<mutual-2@example.invalid>"))
(defconst *sev-c2* (csv-cancel "<mutual-2@example.invalid>" "<mutual-1@example.invalid>"))
(defconst *sev-verdicts*
  (list (cons "<mutual-1@example.invalid>" *csv-p-verified*)
        (cons "<mutual-2@example.invalid>" *csv-p-verified*)))
(defconst *sev-raw* (list *sev-c2* *sev-c1*))
(defconst *sev-hist*
  (list (csv-row 0 "<mutual-1@example.invalid>" (fn-article-payload *sev-c1*) '("control.cancel"))
        (csv-row 1 "<mutual-2@example.invalid>" (fn-article-payload *sev-c2*) '("control.cancel"))))
(defconst *sev-ws* (fn-ctl-articles-withdrawals *sev-raw* *sev-verdicts* *sev-hist* nil))
(defconst *sev-vis* (fn-ctl-visible-articles *sev-raw* *sev-ws* *sev-verdicts*))
(defconst *sev-w* (fn-ctl-withdrawn-articles *sev-raw* *sev-ws* *sev-verdicts*))

; The view: nothing visible, both cancels withdrawn, and so no buckets.
(assert-event
 (and (equal *sev-vis* nil)
      (equal *sev-w* *sev-raw*)
      (equal (fn-gidx-build *sev-vis*) nil)))

(defconst *sev-archive*
  (fn-make-state (list "control.cancel") (list (cons "control.cancel" 3))
                 *sev-vis* 3 nil nil))
(defconst *sev-control* (fn-ctl-pin *sev-w* *sev-ws*))
(defun sev-conn (archive group-index control)
  (fn-served-make-conn-group-indexed
   (fn-wire-initial-state 512 1000) (fn-auth-open-session archive nil nil nil nil nil) archive nil nil nil
   *sev-verdicts* (fn-midx-build (fn-state-articles archive)) group-index control))
(defconst *sev-conn* (sev-conn *sev-archive* nil *sev-control*))
(defun sev-line (text) (fn-nntp-string-octets text))

(include-book "arena-lift")
(defconst *sr-arena* nil)
(bpr-lift fn-octl-reply 2)
(defun sev-reply (conn text)
  (declare (xargs :verify-guards nil))
  (coerce (fn-nntp-octets-chars
           (fn-served-reply-octets
            (fn-nntp-result-effects
             (in-arena-fn-octl-reply *sr-arena* conn (sev-line text)))))
          'string))

; fn-octl-pinned-index-of-served-conn, the new disjunct.  Witness: the empty
; view's served connection has no buckets and a control pin, and its pinned
; index is a pin carrying that control pin and the connection's trie.
(assert-event
 (let ((index (fn-served-conn-pinned-index *sev-conn*)))
   (and (null (fn-served-conn-group-index *sev-conn*))
        (fn-served-conn-control *sev-conn*)
        (not (consp (fn-state-articles (fn-served-conn-archive *sev-conn*))))
        (fn-gidx-pinp index)
        (equal (fn-gidx-pin-control index) *sev-control*)
        (equal (fn-gidx-pin-trie index) (fn-served-conn-index *sev-conn*))
        (equal (fn-gidx-pin-buckets index) nil))))
; Hypothesis removed (the view holds an article): a connection with no
; buckets over a non-empty archive keeps the bare trie, whose control is nil
; -- the retained hypothesis (a control pin) holds, the omitted one fails and
; so does the conclusion.  (No owner connection is in this state: the
; owner's buckets are fn-gidx-build of its visible list.)
(defconst *sev-full-archive*
  (fn-make-state (list "fn.mod.a") (list (cons "fn.mod.a" 3)) (list *csv-o*) 3 nil nil))
(defconst *sev-full-conn* (sev-conn *sev-full-archive* nil *sev-control*))
(assert-event
 (let ((index (fn-served-conn-pinned-index *sev-full-conn*)))
   (and (fn-served-conn-control *sev-full-conn*)
        (null (fn-served-conn-group-index *sev-full-conn*))
        (consp (fn-state-articles (fn-served-conn-archive *sev-full-conn*)))
        (not (fn-gidx-pinp index))
        (not (equal (fn-gidx-pin-control index) *sev-control*)))))

; fn-own-read-of-a-withdrawn-article-answers-430-withdrawn, over the reply
; the host-called read returns (fn-octl-reply of the served connection):
; both cancels answer `430 withdrawn' by Message-ID, ARTICLE and STAT.
(assert-event
 (and (member-equal *sev-c1* *sev-raw*)
      (not (member-equal *sev-c1* *sev-vis*))
      (not (consp (fn-find-article "<mutual-1@example.invalid>" *sev-vis*)))
      (equal (sev-reply *sev-conn* "ARTICLE <mutual-1@example.invalid>")
             (coerce (list #\4 #\3 #\0 #\Space #\w #\i #\t #\h #\d #\r #\a #\w #\n
                           (code-char 13) (code-char 10)) 'string))
      (equal (sev-reply *sev-conn* "STAT <mutual-2@example.invalid>")
             (sev-reply *sev-conn* "ARTICLE <mutual-1@example.invalid>"))))
; Hypothesis removed (the control pin): the same empty view served without
; one answers the message-id as never seen -- the answer before PKT-443.
(assert-event
 (not (equal (sev-reply (sev-conn *sev-archive* nil nil) "ARTICLE <mutual-1@example.invalid>")
             (sev-reply *sev-conn* "ARTICLE <mutual-1@example.invalid>"))))
; Hypothesis removed (the article is withdrawn): a message-id the view never
; held answers 430 no article, not withdrawn.
(assert-event
 (not (equal (sev-reply *sev-conn* "ARTICLE <never@example.invalid>")
             (sev-reply *sev-conn* "ARTICLE <mutual-1@example.invalid>"))))

; GROUP and LISTGROUP over the empty view's nil buckets answer exactly as
; the bare trie does (fn-gidx-listgroup-command-of-build): the pin changes
; no selection answer.
(assert-event
 (and (equal (sev-reply *sev-conn* "GROUP control.cancel")
             (sev-reply (sev-conn *sev-archive* nil nil) "GROUP control.cancel"))
      (equal (sev-reply *sev-conn* "LISTGROUP control.cancel")
             (sev-reply (sev-conn *sev-archive* nil nil) "LISTGROUP control.cancel"))))
