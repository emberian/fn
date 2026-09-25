; Teeth for books/control-served.lisp (brief control-c3d step 1): for each
; keystone a reachable non-degenerate witness and, per hypothesis, a case
; where the conclusion fails without it.
(in-package "ACL2")
(include-book "../../books/control-served")
(include-book "../../books/control-visible")
(include-book "std/testing/must-fail" :dir :system)

(defun csv-line (text)
  (append (fn-record-string-octets text) '(13 10)))
(defun csv-octets (lines)
  (if (consp lines)
      (append (csv-line (car lines)) (csv-octets (cdr lines)))
    (append '(13 10) (csv-line "body"))))
(defconst *csv-p* (make-list 32 :initial-element 17))
(defconst *csv-p-verified* (fn-stx-make-verdict :verified *csv-p* 1))
(defconst *csv-q* (make-list 32 :initial-element 34))
(defconst *csv-q-verified* (fn-stx-make-verdict :verified *csv-q* 1))

; P's target T (fn.mod.a 1), P's cancel C (control.cancel 1) of T, an
; ordinary O (fn.mod.a 2), and Q's cancel D (control.cancel 2) of a target
; U that never arrives.
(defconst *csv-t*
  (fn-make-article "<t@example.invalid>" nil (list "fn.mod.a")
                   (list (cons "fn.mod.a" 1)) t nil))
(defconst *csv-o*
  (fn-make-article "<o@example.invalid>" nil (list "fn.mod.a")
                   (list (cons "fn.mod.a" 2)) t nil))
(defun csv-cancel (msgid target)
  (fn-make-article msgid
                   (csv-octets (list "From: p@example.invalid"
                                     "Newsgroups: control.cancel"
                                     (concatenate 'string "Message-ID: " msgid)
                                     "Subject: cmsg cancel"
                                     (concatenate 'string "Control: cancel " target)))
                   (list "control.cancel") nil t nil))
(defconst *csv-c* (csv-cancel "<c@example.invalid>" "<t@example.invalid>"))
(defconst *csv-d* (csv-cancel "<d@example.invalid>" "<u@example.invalid>"))
(defconst *csv-verdicts*
  (list (cons "<t@example.invalid>" *csv-p-verified*)
        (cons "<c@example.invalid>" *csv-p-verified*)
        (cons "<d@example.invalid>" *csv-q-verified*)))
(defconst *csv-raw* (list *csv-d* *csv-c* *csv-t* *csv-o*))
(defconst *csv-ws* (fn-ctl-articles-withdrawals *csv-raw* *csv-verdicts* nil nil))
(defconst *csv-vis* (fn-ctl-visible-articles *csv-raw* *csv-ws* *csv-verdicts*))
(defconst *csv-w* (fn-ctl-withdrawn-articles *csv-raw* *csv-ws* *csv-verdicts*))

(assert-event
 (and (equal (len *csv-ws*) 2)
      (equal *csv-vis* (list *csv-d* *csv-c* *csv-o*))
      (equal *csv-w* (list *csv-t*))))

; fn-ctl-withdrawn-is-the-complement.  Witness: T in W and not served; O
; served and not in W.  Hypothesis removed (x in the raw list): an article A
; outside it is in neither list.
(assert-event
 (and (member-equal *csv-t* *csv-w*) (not (member-equal *csv-t* *csv-vis*))
      (member-equal *csv-o* *csv-vis*) (not (member-equal *csv-o* *csv-w*))))
(defconst *csv-a*
  (fn-make-article "<a@example.invalid>" nil (list "fn.misc")
                   (list (cons "fn.misc" 1)) t nil))
(must-fail
 (assert-event
  (iff (member-equal *csv-a* *csv-w*) (not (member-equal *csv-a* *csv-vis*)))))

; fn-ctl-refresh-withdrawn-is-withdrawn.  Witness: the old view (T O) had
; W nil; C arrives and withdraws T; the refresh's W is (T).
(assert-event
 (let* ((old (list *csv-t* *csv-o*))
        (new (cons *csv-c* old))
        (ws (fn-ctl-articles-withdrawals new *csv-verdicts* nil nil))
        (vis (fn-ctl-visible-articles new ws *csv-verdicts*)))
   (and (equal (fn-ctl-subseq-diff old old) nil)
        (equal (fn-ctl-refresh-withdrawn new old vis old nil) (list *csv-t*))
        (equal (fn-ctl-refresh-withdrawn new old vis old nil)
               (fn-ctl-withdrawn-articles new ws *csv-verdicts*)))))
; Hypothesis 1 removed (the carried W was the merge): a stale W (O) is kept
; by an ordinary visible arrival.
(must-fail
 (assert-event
  (let* ((old (list *csv-t* *csv-o*))
         (new (cons *csv-a* old))
         (ws (fn-ctl-articles-withdrawals new *csv-verdicts* nil nil))
         (vis (fn-ctl-visible-articles new ws *csv-verdicts*)))
    (equal (fn-ctl-refresh-withdrawn new old vis old (list *csv-o*))
           (fn-ctl-withdrawn-articles new ws *csv-verdicts*)))))
; Hypothesis 2 removed (the visible list is the view's): the unfiltered list.
(must-fail
 (assert-event
  (let* ((old (list *csv-t* *csv-o*))
         (new (cons *csv-c* old))
         (ws (fn-ctl-articles-withdrawals new *csv-verdicts* nil nil)))
    (equal (fn-ctl-refresh-withdrawn new old new old nil)
           (fn-ctl-withdrawn-articles new ws *csv-verdicts*)))))
; control-c3e: the merge copies the withdrawn tail as a true list, so the
; former third hypothesis (RAW a true list) is gone: a raw list ending in 5
; now agrees too.
(assert-event
 (let* ((raw (cons *csv-c* (cons *csv-t* 5)))
        (ws (fn-ctl-articles-withdrawals raw *csv-verdicts* nil nil))
        (vis (fn-ctl-visible-articles raw ws *csv-verdicts*)))
   (and (equal (fn-ctl-refresh-withdrawn raw nil vis nil nil) (list *csv-t*))
        (equal (fn-ctl-refresh-withdrawn raw nil vis nil nil)
               (fn-ctl-withdrawn-articles raw ws *csv-verdicts*)))))

; fn-ctl-number-withdrawn-is-a-withdrawn-holder (423 withdrawn).  Witness:
; fn.mod.a 1 finds T, held in raw, not served.  Hypothesis removed (the
; lookup found something): fn.mod.a 7 finds nothing, and nil is not in raw.
(assert-event
 (equal (fn-ctl-number-withdrawn "fn.mod.a" 1 *csv-w*) *csv-t*))
(must-fail
 (assert-event
  (let ((y (fn-ctl-number-withdrawn "fn.mod.a" 7 *csv-w*)))
    (and (member-equal y *csv-raw*) (not (member-equal y *csv-vis*))))))
; The converse (supporting), fn-ctl-withdrawn-holder-is-found-by-number:
; T at fn.mod.a 1 is found; O's number 2 (served) and A's fn.misc 1 (not
; in raw) are not.
(assert-event (consp (fn-ctl-number-withdrawn "fn.mod.a" 1 *csv-w*)))
(must-fail (assert-event (consp (fn-ctl-number-withdrawn "fn.mod.a" 2 *csv-w*))))
(must-fail (assert-event (consp (fn-ctl-number-withdrawn "fn.misc" 1 *csv-w*))))

; fn-ctl-msgid-withdrawn-is-a-withdrawn-article (430 withdrawn).
(assert-event
 (equal (fn-ctl-msgid-withdrawn "<t@example.invalid>" *csv-w*) *csv-t*))
(must-fail
 (assert-event
  (let ((y (fn-ctl-msgid-withdrawn "<o@example.invalid>" *csv-w*)))
    (and (member-equal y *csv-raw*) (not (member-equal y *csv-vis*))))))

; fn-ctl-executed-status-means-withdrawn and fn-ctl-owed-status-means-not-held.
; C is executed by the author basis; D is owed (U never arrived); O names
; no target; the item texts.
(assert-event
 (and (equal (fn-ctl-control-status *csv-c* *csv-vis* *csv-w* *csv-ws* *csv-verdicts*)
             (list :executed :author))
      (equal (fn-ctl-control-status *csv-d* *csv-vis* *csv-w* *csv-ws* *csv-verdicts*)
             (list :owed))
      (equal (fn-ctl-control-status *csv-o* *csv-vis* *csv-w* *csv-ws* *csv-verdicts*)
             (list :none))
      (equal (fn-ctl-control-item (list :executed :author) "<t@example.invalid>")
             "executed withdrawal <t@example.invalid> author")
      (equal (fn-ctl-control-item (list :owed) "<u@example.invalid>") "owed")))
; Executed, hypothesis 2 removed (C in the raw list): a view (T O) that does
; not hold C still finds C's record in WS, so C's status reads executed, but
; the view serves T: the not-served conclusion fails.
(assert-event
 (let* ((raw (list *csv-t* *csv-o*))
        (vis (fn-ctl-visible-articles raw *csv-ws* *csv-verdicts*))
        (w (fn-ctl-withdrawn-articles raw *csv-ws* *csv-verdicts*)))
   (equal (car (fn-ctl-control-status *csv-c* vis w *csv-ws* *csv-verdicts*))
          :executed)))
(must-fail
 (assert-event
  (let* ((raw (list *csv-t* *csv-o*))
         (vis (fn-ctl-visible-articles raw *csv-ws* *csv-verdicts*))
         (w (fn-ctl-withdrawn-articles raw *csv-ws* *csv-verdicts*)))
    (not (member-equal (fn-ctl-find-held "<t@example.invalid>" vis w) vis)))))
; Executed, hypothesis 1 removed (the status is executed): O's held target
; is nil, not a member of raw.
(must-fail
 (assert-event
  (member-equal (fn-ctl-find-held (fn-ctl-target-octets (fn-article-payload *csv-o*))
                                  *csv-vis* *csv-w*)
                *csv-raw*)))
; Owed, hypothesis 1 removed (the status is owed): C's target T is held.
(must-fail
 (assert-event
  (not (equal (fn-article-msgid *csv-t*)
              (fn-ctl-target-octets (fn-article-payload *csv-c*))))))
; Owed, hypothesis 2 removed (x in the raw list): U arriving elsewhere
; carries D's target.
(defconst *csv-u*
  (fn-make-article "<u@example.invalid>" nil (list "fn.mod.a")
                   (list (cons "fn.mod.a" 3)) t nil))
(assert-event (not (member-equal *csv-u* *csv-raw*)))
(must-fail
 (assert-event
  (not (equal (fn-article-msgid *csv-u*)
              (fn-ctl-target-octets (fn-article-payload *csv-d*))))))
