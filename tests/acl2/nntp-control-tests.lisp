; Teeth for books/nntp-control.lisp (control-c3e): the three withdrawal arms
; of the pinned dispatcher, on control-served-tests' view: P's T
; (fn.mod.a 1) withdrawn by P's cancel C, O (fn.mod.a 2) served, Q's cancel
; D of a U that never arrived.  Each keystone has a witness through
; `fn-nntp-archive-command-pinned' itself and one must-fail per substantive
; hypothesis (the pin's W, the arm's decision, the archive's miss, the trie
; correspondence, the keyword, the argument shape).
(in-package "ACL2")
(include-book "control-served-tests")
(include-book "../../books/nntp-control")
(include-book "std/testing/must-fail" :dir :system)

(defun nct-tok (text) (fn-nntp-string-octets text))
(defconst *nct-archive*
  (fn-make-state (list "fn.mod.a" "control.cancel")
                 (list (cons "fn.mod.a" 3) (cons "control.cancel" 3))
                 *csv-vis* 5 nil nil))
(defconst *nct-session*
  (fn-nntp-set-cursor (fn-nntp-open-session *nct-archive*) "fn.mod.a" nil))
(defun nct-index (w)
  (fn-gidx-pin-with-control (fn-midx-build *csv-vis*) (fn-gidx-build *csv-vis*)
                            (fn-ctl-pin w *csv-ws*)))
(defconst *nct-index* (nct-index *csv-w*))
(defun nct-toks (args)
  (if (consp args) (cons (nct-tok (car args)) (nct-toks (cdr args))) nil))
(defun nct-run (session archive index keyword args)
  (fn-nntp-archive-command-pinned session archive index *csv-verdicts* nil
                                  (nct-tok keyword) (nct-toks args)))
(defconst *nct-423* (fn-nntp-single *nct-session* "423 withdrawn"))
(defconst *nct-430* (fn-nntp-single *nct-session* "430 withdrawn"))

; The pin's W is the view's withdrawn list, and the archive serves the view.
(assert-event (equal *csv-w* (fn-ctl-withdrawn-articles *csv-raw* *csv-ws* *csv-verdicts*)))
(assert-event (equal (fn-state-articles *nct-archive*) *csv-vis*))

; ---------------------------------------------------------------------------
; 423: fn-nntp-423-withdrawn-is-a-withdrawn-holder and
; fn-nntp-withdrawn-holder-answers-423-withdrawn.  Witness: ARTICLE 1 and
; STAT 1 answer 423 withdrawn; ARTICLE 2 (O, served) does not.
(assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index* "ARTICLE" '("1")) *nct-423*))
(assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index* "STAT" '("1")) *nct-423*))
(assert-event (fn-nntp-number-withdrawn-p *nct-session* *nct-archive* *nct-index* (nct-tok "1")))
(assert-event (not (equal (nct-run *nct-session* *nct-archive* *nct-index* "ARTICLE" '("2"))
                          *nct-423*)))
; Sound, hypothesis 1 removed (the pin's W is RAW's withdrawn list): a stale
; W holding A (fn.misc 1) under group fn.misc answers 423 withdrawn for an
; article outside RAW.
(must-fail
 (assert-event
  (let* ((s (fn-nntp-set-cursor *nct-session* "fn.misc" nil))
         (idx (nct-index (list *csv-a*)))
         (y (fn-ctl-number-withdrawn "fn.misc" 1 (list *csv-a*))))
    (implies (fn-nntp-number-withdrawn-p s *nct-archive* idx (nct-tok "1"))
             (member-equal y *csv-raw*)))))
; Sound, hypothesis 2 removed (the arm fired): number 7 names no holder.
(must-fail
 (assert-event
  (member-equal (fn-ctl-number-withdrawn "fn.mod.a" 7 *csv-w*) *csv-raw*)))
; Complete, per hypothesis, each with every other hypothesis kept:
; the pin's W (nil instead of RAW's): plain 423.
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* (nct-index nil)
                                         "ARTICLE" '("1")) *nct-423*)))
; the keyword (GROUP is not a retrieval).
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                                         "GROUP" '("1")) *nct-423*)))
; one argument (two).
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                                         "ARTICLE" '("1" "1")) *nct-423*)))
; a number token (a Message-ID token is taken by the Message-ID arms).
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                                         "ARTICLE" '("<t@example.invalid>")) *nct-423*)))
; a selected group (none selected).
(must-fail (assert-event (equal (nct-run (fn-nntp-open-session *nct-archive*) *nct-archive*
                                         *nct-index* "ARTICLE" '("1"))
                                (fn-nntp-single (fn-nntp-open-session *nct-archive*)
                                                "423 withdrawn"))))
; x in RAW, not served, holding the number: 3 is held by nothing.
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                                         "ARTICLE" '("3")) *nct-423*)))
; the archive misses the number: an archive that still serves T answers T.
(must-fail (assert-event
            (equal (nct-run *nct-session*
                            (fn-ctl-visible-state-of *nct-archive* *csv-raw*)
                            *nct-index* "ARTICLE" '("1"))
                   *nct-423*)))

; ---------------------------------------------------------------------------
; 430: fn-nntp-430-withdrawn-is-a-withdrawn-article and
; fn-nntp-withdrawn-article-answers-430-withdrawn.
(assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                              "ARTICLE" '("<t@example.invalid>")) *nct-430*))
(assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                              "HEAD" '("<t@example.invalid>")) *nct-430*))
(assert-event (not (equal (nct-run *nct-session* *nct-archive* *nct-index*
                                   "ARTICLE" '("<o@example.invalid>")) *nct-430*)))
; Sound, hypothesis 1 removed (W is RAW's): a stale W holding A.
(must-fail
 (assert-event
  (let ((idx (nct-index (list *csv-a*))))
    (implies (fn-nntp-msgid-withdrawn-p idx (nct-tok "<a@example.invalid>"))
             (member-equal (fn-ctl-msgid-withdrawn "<a@example.invalid>" (list *csv-a*))
                           *csv-raw*)))))
; Sound, hypothesis 2 removed (the trie is the archive's): a trie of the raw
; list misses nothing, so the arm cannot fire on T; with an empty trie and
; an archive that serves T, the arm fires and T is served.
(must-fail
 (assert-event
  (let* ((arch (fn-ctl-visible-state-of *nct-archive* *csv-raw*))
         (idx (fn-gidx-pin-with-control nil nil (fn-ctl-pin *csv-w* *csv-ws*))))
    (implies (fn-nntp-msgid-withdrawn-p idx (nct-tok "<t@example.invalid>"))
             (not (consp (fn-find-article "<t@example.invalid>"
                                          (fn-state-articles arch))))))))
; Sound, hypothesis 3 removed (the arm fired): O is not withdrawn.
(must-fail
 (assert-event
  (member-equal (fn-ctl-msgid-withdrawn "<o@example.invalid>" *csv-w*) *csv-raw*)))
; Complete, per hypothesis: W nil; keyword; two arguments; the archive
; serves T (trie of the raw list).
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* (nct-index nil)
                                         "ARTICLE" '("<t@example.invalid>")) *nct-430*)))
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                                         "GROUP" '("<t@example.invalid>")) *nct-430*)))
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                                         "ARTICLE" '("<t@example.invalid>" "1")) *nct-430*)))
(must-fail (assert-event
            (equal (nct-run *nct-session* (fn-ctl-visible-state-of *nct-archive* *csv-raw*)
                            (fn-gidx-pin-with-control (fn-midx-build *csv-raw*)
                                                      (fn-gidx-build *csv-raw*)
                                                      (fn-ctl-pin *csv-w* *csv-ws*))
                            "ARTICLE" '("<t@example.invalid>"))
                   *nct-430*)))

; ---------------------------------------------------------------------------
; HDR :fn-control: fn-nntp-hdr-fn-control-is-the-status.  C's line is its
; executed author withdrawal of T; D's is owed; T itself (withdrawn) names
; no target; an unknown Message-ID is 430.
(defun nct-hdr-line (text)
  (fn-nntp-multi *nct-session* (fn-nntp-hdr-initial nil)
                 (list (fn-nntp-hdr-line (fn-nntp-decimal-field 0)
                                         (fn-nntp-string-octets text)))))
(assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                              "HDR" '(":fn-control" "<c@example.invalid>"))
                     (nct-hdr-line "executed withdrawal <t@example.invalid> author")))
(assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                              "HDR" '(":fn-control" "<d@example.invalid>"))
                     (nct-hdr-line "owed")))
(assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                              "HDR" '(":fn-control" "<t@example.invalid>"))
                     (nct-hdr-line "none")))
(assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                              "HDR" '(":fn-control" "<zz@example.invalid>"))
                     (fn-nntp-single *nct-session* "430 no article with that message-id")))
; Hypothesis removed (the trie is the served list's): an empty trie misses C
; and answers 430.
(must-fail (assert-event
            (equal (nct-run *nct-session* *nct-archive*
                            (fn-gidx-pin-with-control nil nil (fn-ctl-pin *csv-w* *csv-ws*))
                            "HDR" '(":fn-control" "<c@example.invalid>"))
                   (nct-hdr-line "executed withdrawal <t@example.invalid> author"))))
; The keyword and the field name (HDR :fn-verified answers the verdict).
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                                         "HDR" '(":fn-verified" "<c@example.invalid>"))
                                (nct-hdr-line "executed withdrawal <t@example.invalid> author"))))
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                                         "OVER" '(":fn-control" "<c@example.invalid>"))
                                (nct-hdr-line "executed withdrawal <t@example.invalid> author"))))
; A Message-ID token (a range is refused 501).
(must-fail (assert-event (equal (nct-run *nct-session* *nct-archive* *nct-index*
                                         "HDR" '(":fn-control" "1-2"))
                                (nct-hdr-line "executed withdrawal <t@example.invalid> author"))))

; fn-nntp-hdr-fn-control-executed-means-withdrawn: C's executed status names
; T, which RAW holds and the view does not serve.  Hypothesis removed (the
; status is executed): D's owed status names U, which RAW does not hold.
(assert-event
 (let ((c (fn-ctl-find-held "<c@example.invalid>" *csv-vis* *csv-w*)))
   (and (equal c *csv-c*)
        (equal (car (fn-ctl-control-status c *csv-vis* *csv-w* *csv-ws* *csv-verdicts*))
               :executed)
        (member-equal (fn-ctl-find-held "<t@example.invalid>" *csv-vis* *csv-w*) *csv-raw*))))
(must-fail
 (assert-event
  (member-equal (fn-ctl-find-held "<u@example.invalid>" *csv-vis* *csv-w*) *csv-raw*)))
