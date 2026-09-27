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
(include-book "must-fail-checked")

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
(defun nct-run (session archive index keyword args fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-nntp-archive-command-pinned session archive index *csv-verdicts* nil
                                  (nct-tok keyword) (nct-toks args) fn-arena))
(defconst *nct-423* (fn-nntp-single *nct-session* "423 withdrawn"))
(defconst *nct-430* (fn-nntp-single *nct-session* "430 withdrawn"))

; The pin's W is the view's withdrawn list, and the archive serves the view.
(assert-event (equal *csv-w* (fn-ctl-withdrawn-articles *csv-raw* *csv-ws* *csv-verdicts*)))
(assert-event (equal (fn-state-articles *nct-archive*) *csv-vis*))

; ---------------------------------------------------------------------------
; 423: fn-nntp-423-withdrawn-is-a-withdrawn-holder and
; fn-nntp-withdrawn-holder-answers-423-withdrawn.  Witness: ARTICLE 1 and
; STAT 1 answer 423 withdrawn; ARTICLE 2 (O, served) does not.
(include-book "arena-lift")
;; The arena: empty; control-served-tests' articles carry their octets (or
;; nil), never a handle, so no read goes through it.
(defconst *sr-arena* nil)
(bpr-lift nct-run 5)
(assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "ARTICLE" '("1")) *nct-423*))
(assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "STAT" '("1")) *nct-423*))
(assert-event (fn-nntp-number-withdrawn-p *nct-session* *nct-archive* *nct-index* (nct-tok "1")))
(assert-event (not (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "ARTICLE" '("2"))
                          *nct-423*)))
; Sound, hypothesis 1 removed (the pin's W is RAW's withdrawn list): a stale
; W holding A (fn.misc 1) under group fn.misc answers 423 withdrawn for an
; article outside RAW.
(must-fail-checked
 (assert-event
  (let* ((s (fn-nntp-set-cursor *nct-session* "fn.misc" nil))
         (idx (nct-index (list *csv-a*)))
         (y (fn-ctl-number-withdrawn "fn.misc" 1 (list *csv-a*))))
    (implies (fn-nntp-number-withdrawn-p s *nct-archive* idx (nct-tok "1"))
             (member-equal y *csv-raw*)))))
; Sound, hypothesis 2 removed (the arm fired): number 7 names no holder.
(must-fail-checked
 (assert-event
  (member-equal (fn-ctl-number-withdrawn "fn.mod.a" 7 *csv-w*) *csv-raw*)))
; Complete, per hypothesis, each with every other hypothesis kept:
; the pin's W (nil instead of RAW's): plain 423.
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* (nct-index nil) "ARTICLE" '("1")) *nct-423*)))
; the keyword (GROUP is not a retrieval).
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "GROUP" '("1")) *nct-423*)))
; one argument (two).
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "ARTICLE" '("1" "1")) *nct-423*)))
; a number token (a Message-ID token is taken by the Message-ID arms).
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "ARTICLE" '("<t@example.invalid>")) *nct-423*)))
; a selected group (none selected).
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* (fn-nntp-open-session *nct-archive*) *nct-archive* *nct-index* "ARTICLE" '("1"))
                                (fn-nntp-single (fn-nntp-open-session *nct-archive*)
                                                "423 withdrawn"))))
; x in RAW, not served, holding the number: 3 is held by nothing.
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "ARTICLE" '("3")) *nct-423*)))
; the archive misses the number: an archive that still serves T answers T.
(must-fail-checked (assert-event
            (equal (in-arena-nct-run *sr-arena* *nct-session* (fn-ctl-visible-state-of *nct-archive* *csv-raw*) *nct-index* "ARTICLE" '("1"))
                   *nct-423*)))

; ---------------------------------------------------------------------------
; 430: fn-nntp-430-withdrawn-is-a-withdrawn-article and
; fn-nntp-withdrawn-article-answers-430-withdrawn.
(assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "ARTICLE" '("<t@example.invalid>")) *nct-430*))
(assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "HEAD" '("<t@example.invalid>")) *nct-430*))
(assert-event (not (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "ARTICLE" '("<o@example.invalid>")) *nct-430*)))
; Sound, hypothesis 1 removed (W is RAW's): a stale W holding A.
(must-fail-checked
 (assert-event
  (let ((idx (nct-index (list *csv-a*))))
    (implies (fn-nntp-msgid-withdrawn-p idx (nct-tok "<a@example.invalid>"))
             (member-equal (fn-ctl-msgid-withdrawn "<a@example.invalid>" (list *csv-a*))
                           *csv-raw*)))))
; Sound, hypothesis 2 removed (the trie is the archive's): a trie of the raw
; list misses nothing, so the arm cannot fire on T; with an empty trie and
; an archive that serves T, the arm fires and T is served.
(must-fail-checked
 (assert-event
  (let* ((arch (fn-ctl-visible-state-of *nct-archive* *csv-raw*))
         (idx (fn-gidx-pin-with-control nil nil (fn-ctl-pin *csv-w* *csv-ws*))))
    (implies (fn-nntp-msgid-withdrawn-p idx (nct-tok "<t@example.invalid>"))
             (not (consp (fn-find-article "<t@example.invalid>"
                                          (fn-state-articles arch))))))))
; Sound, hypothesis 3 removed (the arm fired): O is not withdrawn.
(must-fail-checked
 (assert-event
  (member-equal (fn-ctl-msgid-withdrawn "<o@example.invalid>" *csv-w*) *csv-raw*)))
; Complete, per hypothesis: W nil; keyword; two arguments; the archive
; serves T (trie of the raw list).
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* (nct-index nil) "ARTICLE" '("<t@example.invalid>")) *nct-430*)))
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "GROUP" '("<t@example.invalid>")) *nct-430*)))
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "ARTICLE" '("<t@example.invalid>" "1")) *nct-430*)))
(must-fail-checked (assert-event
            (equal (in-arena-nct-run *sr-arena* *nct-session* (fn-ctl-visible-state-of *nct-archive* *csv-raw*) (fn-gidx-pin-with-control (fn-midx-build *csv-raw*)
                                                      (fn-gidx-build *csv-raw*)
                                                      (fn-ctl-pin *csv-w* *csv-ws*)) "ARTICLE" '("<t@example.invalid>"))
                   *nct-430*)))

; ---------------------------------------------------------------------------
; HDR :fn-control: fn-nntp-hdr-fn-control-is-the-status.  C's line is its
; executed author withdrawal of T; D's is owed; T itself (withdrawn) names
; no target; an unknown Message-ID is 430.
(defun nct-hdr-line (text)
  (fn-nntp-multi *nct-session* (fn-nntp-hdr-initial nil)
                 (list (fn-nntp-hdr-line (fn-nntp-decimal-field 0)
                                         (fn-nntp-string-octets text)))))
(assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "HDR" '(":fn-control" "<c@example.invalid>"))
                     (nct-hdr-line "executed withdrawal <t@example.invalid> author")))
(assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "HDR" '(":fn-control" "<d@example.invalid>"))
                     (nct-hdr-line "owed")))
(assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "HDR" '(":fn-control" "<t@example.invalid>"))
                     (nct-hdr-line "none")))
(assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "HDR" '(":fn-control" "<zz@example.invalid>"))
                     (fn-nntp-single *nct-session* "430 no article with that message-id")))
; Hypothesis removed (the trie is the served list's): an empty trie misses C
; and answers 430.
(must-fail-checked (assert-event
            (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* (fn-gidx-pin-with-control nil nil (fn-ctl-pin *csv-w* *csv-ws*)) "HDR" '(":fn-control" "<c@example.invalid>"))
                   (nct-hdr-line "executed withdrawal <t@example.invalid> author"))))
; The keyword and the field name (HDR :fn-verified answers the verdict).
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "HDR" '(":fn-verified" "<c@example.invalid>"))
                                (nct-hdr-line "executed withdrawal <t@example.invalid> author"))))
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "OVER" '(":fn-control" "<c@example.invalid>"))
                                (nct-hdr-line "executed withdrawal <t@example.invalid> author"))))
; A Message-ID token (a range is refused 501).
(must-fail-checked (assert-event (equal (in-arena-nct-run *sr-arena* *nct-session* *nct-archive* *nct-index* "HDR" '(":fn-control" "1-2"))
                                (nct-hdr-line "executed withdrawal <t@example.invalid> author"))))

; fn-nntp-hdr-fn-control-executed-means-withdrawn: C's executed status names
; T, which RAW holds and the view does not serve.  Hypothesis removed (the
; status is executed): D's owed status names U, which RAW does not hold.
(assert-event
 (let ((c (fn-ctl-find-held "<c@example.invalid>" *csv-vis* *csv-w*)))
   (and (equal c *csv-c*)
        (equal (car (fn-ctl-control-status c (fn-article-payload c) *csv-vis* *csv-w* *csv-ws* *csv-verdicts*))
               :executed)
        (member-equal (fn-ctl-find-held "<t@example.invalid>" *csv-vis* *csv-w*) *csv-raw*))))
(must-fail-checked
 (assert-event
  (member-equal (fn-ctl-find-held "<u@example.invalid>" *csv-vis* *csv-w*) *csv-raw*)))

; ---------------------------------------------------------------------------
; Over a FLIPPED archive (lane matrix-reds): the archive articles C and D
; carry arena handles 0 and 1, as every stored article has since the records
; flip; the arena holds their octets.  The witnesses above serve wire-form
; articles (octet payloads, which fn-nntp-payload-bytes passes through), so
; they never met a handle: on dev before this lane the served reply parsed
; the handle, found no target, and answered `none' for C
; (tests.test_native_control_filing, `0 none').
(defun nct-flip (a h)
  (fn-make-article (fn-article-msgid a) h (fn-article-groups a)
                   (fn-article-memberships a) (fn-article-pin a) (fn-article-stamp a)))
(defconst *nct-f-c* (nct-flip *csv-c* 0))
(defconst *nct-f-d* (nct-flip *csv-d* 1))
(defconst *nct-f-arena* (list (fn-article-payload *csv-c*) (fn-article-payload *csv-d*)))
(defconst *nct-f-raw* (list *nct-f-d* *nct-f-c* *csv-t* *csv-o*))
(defconst *nct-f-vis* (fn-ctl-visible-articles *nct-f-raw* *csv-ws* *csv-verdicts*))
(defconst *nct-f-w* (fn-ctl-withdrawn-articles *nct-f-raw* *csv-ws* *csv-verdicts*))
(defconst *nct-f-archive*
  (fn-make-state (list "fn.mod.a" "control.cancel")
                 (list (cons "fn.mod.a" 3) (cons "control.cancel" 3))
                 *nct-f-vis* 5 nil nil))
(defconst *nct-f-index*
  (fn-gidx-pin-with-control (fn-midx-build *nct-f-vis*) (fn-gidx-build *nct-f-vis*)
                            (fn-ctl-pin *nct-f-w* *csv-ws*)))
(defconst *nct-f-session*
  (fn-nntp-set-cursor (fn-nntp-open-session *nct-f-archive*) "fn.mod.a" nil))
(defun nct-f-hdr-line (text)
  (fn-nntp-multi *nct-f-session* (fn-nntp-hdr-initial nil)
                 (list (fn-nntp-hdr-line (fn-nntp-decimal-field 0)
                                         (fn-nntp-string-octets text)))))
; The flipped view withdraws T and serves the handle-carrying C and D.
(assert-event
 (and (natp (fn-article-payload (fn-ctl-find-held "<c@example.invalid>" *nct-f-vis* *nct-f-w*)))
      (equal *nct-f-w* (list *csv-t*))
      (equal *nct-f-vis* (list *nct-f-d* *nct-f-c* *csv-o*))))
; fn-nntp-hdr-fn-control-is-the-status over the flipped archive: C's line is
; its executed author withdrawal of T, D's is owed.
(assert-event (equal (in-arena-nct-run *nct-f-arena* *nct-f-session* *nct-f-archive* *nct-f-index* "HDR" '(":fn-control" "<c@example.invalid>"))
                     (nct-f-hdr-line "executed withdrawal <t@example.invalid> author")))
(assert-event (equal (in-arena-nct-run *nct-f-arena* *nct-f-session* *nct-f-archive* *nct-f-index* "HDR" '(":fn-control" "<d@example.invalid>"))
                     (nct-f-hdr-line "owed")))
; The arena is what the reply reads: without C's bytes under its handle (an
; empty arena), the handle names nothing and the line is `none', the answer
; dev served before this lane.
(assert-event (equal (in-arena-nct-run nil *nct-f-session* *nct-f-archive* *nct-f-index* "HDR" '(":fn-control" "<c@example.invalid>"))
                     (nct-f-hdr-line "none")))
(must-fail-checked (assert-event (equal (in-arena-nct-run nil *nct-f-session* *nct-f-archive* *nct-f-index* "HDR" '(":fn-control" "<c@example.invalid>"))
                                (nct-f-hdr-line "executed withdrawal <t@example.invalid> author"))))

; fn-nntp-hdr-fn-control-status-is-the-model-status: the status of the
; flipped C from the bytes its handle names is the pre-flip kernel's status
; of C's octet model, which is C itself before the flip.  The theorem has no
; hypothesis (a former (consp c) was removed after the weakened statement
; proved).  The mutation: the kernel over the handle itself (the pre-lane
; read) does not give the model's status.
(defun nct-f-status (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (list (fn-ctl-control-status *nct-f-c* (fn-nntp-article-bytes *nct-f-c* fn-arena)
                               *nct-f-vis* *nct-f-w* *csv-ws* *csv-verdicts*)
        (fn-nntp-article-alpha *nct-f-c* fn-arena)))
(bpr-lift nct-f-status 0)
(assert-event
 (let* ((r (in-arena-nct-f-status *nct-f-arena*))
        (model (cadr r)))
   (and (equal (car r) (list :executed :author))
        (equal model *csv-c*)
        (equal (car r)
               (fn-ctl-control-status model (fn-article-payload model)
                                      *nct-f-vis* *nct-f-w* *csv-ws* *csv-verdicts*)))))
(must-fail-checked
 (assert-event
  (equal (fn-ctl-control-status *nct-f-c* (fn-article-payload *nct-f-c*)
                                *nct-f-vis* *nct-f-w* *csv-ws* *csv-verdicts*)
         (list :executed :author))))
