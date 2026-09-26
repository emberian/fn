; Teeth for books/nntp-search-scope.lisp (reader-daily, PRF-122): the
; reader's search scope on the served reader step.  Each keystone has a
; reachable witness and, per hypothesis, a case where every retained
; hypothesis holds, the removed one fails, and the conclusion fails.
;
; Two fixtures.  *ss-archive* is a real accepted archive (fn-accept-prepare
; and fn-accept-complete): fn.letters 1 "search alpha", fn.letters 2
; "Re: search alpha" referencing 1, fn.other 1 "search elsewhere".  The
; withdrawal fixture is control-served-tests' view: T (fn.mod.a 1)
; withdrawn by its author's cancel, O (fn.mod.a 2) served.
(in-package "ACL2")
(include-book "control-served-tests")
(include-book "../../books/nntp-search-scope")
(include-book "std/testing/must-fail" :dir :system)

(defun ss-payload (msgid subject refs)
  (append (fn-nntp-string-octets (concatenate 'string "Message-ID: " msgid)) '(13 10)
          (fn-nntp-string-octets (concatenate 'string "Subject: " subject)) '(13 10)
          (if refs
              (append (fn-nntp-string-octets (concatenate 'string "References: " refs))
                      '(13 10))
            nil)
          '(13 10)
          (fn-nntp-string-octets "Hi") '(13 10)))
(defun ss-add (st seq msgid subject refs groups)
  (fn-accept-complete
   (fn-accept-prepare st 1 msgid (ss-payload msgid subject refs) groups
                      841000000)
   (- seq 1) 1 :durable))
(defconst *ss-archive*
  (ss-add (ss-add (ss-add (fn-initial-state '("fn.letters" "fn.other"))
                          1 "<a@x.invalid>" "search alpha" nil '("fn.letters"))
                  2 "<b@x.invalid>" "Re: search alpha" "<a@x.invalid>" '("fn.letters"))
          3 "<c@x.invalid>" "search elsewhere" nil '("fn.other")))
(defconst *ss-env*
  (fn-nntp-env (fn-clock-observation 1000 843136496000 1000 t) nil nil))
(defconst *ss-session* (fn-nntp-make-session t "fn.letters" nil t))
(defun ss-tok (text) (fn-nntp-string-octets text))
(defmacro ss-step (session text)
  `(fn-nntp-step-pinned ,session *ss-archive* nil nil *ss-env*
                        (list :command (ss-tok ,text))))
(assert-event (fn-nntp-projectionp *ss-archive*))
(defun ss-parsed (text)
  (declare (xargs :verify-guards nil))
  (fn-wildmat-result-value (fn-wildmat-parse-text (ss-tok text))))
(defun ss-hits (field pattern group low high articles)
  (declare (xargs :verify-guards nil))
  (fn-nss-hits (ss-tok field) (ss-parsed pattern) group
               (fn-nntp-group-range-numbers group low high articles)
               articles))
(defun ss-lines (texts)
  (if (consp texts)
      (append (fn-nntp-string-octets (car texts)) '(13 10) (ss-lines (cdr texts)))
    nil))
(defun ss-block (initial lines)
  (list (list :reply (append (fn-nntp-string-octets initial) '(13 10)
                             (ss-lines lines) '(46 13 10)))))

; -----------------------------------------------------------------------------
; fn-nss-hits-are-the-scope (no hypothesis; both directions).
(defconst *ss-articles* (fn-state-articles *ss-archive*))
; In scope, served and matching: 1 and 2 are hits, in number order.
(assert-event (equal (ss-hits "Subject" "*alpha*" "fn.letters" 1 9 *ss-articles*)
                     '(1 2)))
(assert-event (let ((a (fn-nntp-available-article "fn.letters" 1 *ss-articles*)))
                (and (consp a)
                     (fn-nntp-hdr-okp (fn-nntp-hdr-content (ss-tok "Subject") a))
                     (fn-nntp-xpat-matchesp
                      (ss-parsed "*alpha*")
                      (fn-nntp-hdr-octets (fn-nntp-hdr-content (ss-tok "Subject") a))))))
; Outside the stated range: 1 matches and is served, but the range is 2-9.
(assert-event (equal (ss-hits "Subject" "*alpha*" "fn.letters" 2 9 *ss-articles*)
                     '(2)))
; Served in another group only: "search elsewhere" is fn.other 1, and
; fn.letters has nothing at 3; the group is the scope.
(assert-event (equal (ss-hits "Subject" "*elsewhere*" "fn.letters" 1 9 *ss-articles*)
                     nil))
(assert-event (equal (ss-hits "Subject" "*elsewhere*" "fn.other" 1 9 *ss-articles*)
                     '(1)))
; Not matching: the node's matcher is case-sensitive.
(assert-event (equal (ss-hits "Subject" "*Alpha*" "fn.letters" 1 9 *ss-articles*)
                     nil))
; The thread query the reader sends: which articles in the scope carry
; <a@x.invalid> in References.
(assert-event (equal (ss-hits "References" "*<a@x.invalid>*" "fn.letters" 1 9
                              *ss-articles*)
                     '(2)))

; -----------------------------------------------------------------------------
; fn-nss-withdrawn-number-is-never-a-hit.
(defconst *ss-w-archive*
  (fn-make-state (list "fn.mod.a" "control.cancel")
                 (list (cons "fn.mod.a" 3) (cons "control.cancel" 3))
                 *csv-vis* 5 nil nil))
(defconst *ss-w-session*
  (fn-nntp-set-cursor (fn-nntp-open-session *ss-w-archive*) "fn.mod.a" nil))
(defconst *ss-w-index*
  (fn-gidx-pin-with-control (fn-midx-build *csv-vis*) (fn-gidx-build *csv-vis*)
                            (fn-ctl-pin *csv-w* *csv-ws*)))
; Witness: the step's 423 arm fires for 1 (T, withdrawn), and 1 is not a hit
; of the pattern that selects everything; O at 2 is.
(assert-event (fn-nntp-number-withdrawn-p *ss-w-session* *ss-w-archive* *ss-w-index*
                                          (ss-tok "1")))
(assert-event (equal (ss-hits ":bytes" "*" "fn.mod.a" 1 3
                              (fn-state-articles *ss-w-archive*))
                     '(2)))
; Hypothesis removed: over the raw list, T is held at 1, the arm does not
; fire, and 1 is a hit.
(defconst *ss-raw-archive*
  (fn-make-state (list "fn.mod.a" "control.cancel")
                 (list (cons "fn.mod.a" 3) (cons "control.cancel" 3))
                 *csv-raw* 5 nil nil))
(assert-event (not (fn-nntp-number-withdrawn-p *ss-w-session* *ss-raw-archive*
                                               *ss-w-index* (ss-tok "1"))))
(assert-event (member-equal 1 (ss-hits ":bytes" "*" "fn.mod.a" 1 3
                                       (fn-state-articles *ss-raw-archive*))))

; -----------------------------------------------------------------------------
; fn-nntp-step-pinned-xpat-range-is-the-scope: the ten hypotheses as a
; list, the conclusion, the witness, and one counterexample per hypothesis.
(defun ss-hyps (session line)
  (declare (xargs :verify-guards nil))
  (let* ((toks (fn-nntp-tokenize line))
         (args (cdr toks)))
    (list (and (fn-nntp-sessionp session) t)
          (equal (fn-nntp-session-openp session) t)
          (and (fn-nntp-session-projected session) t)
          (and (fn-nntp-command-inputp line) t)
          (and (fn-nntp-command-arguments-at-mostp toks) t)
          (and (fn-nntp-keywordp (car toks) "XPAT") t)
          (and (fn-nntp-hdr-fieldp (car args)) t)
          (and (fn-nntp-range-okp (fn-nntp-parse-range (car (cdr args)))) t)
          (and (fn-wildmat-result-okp
                (fn-wildmat-parse-text (fn-nntp-xpat-join (cdr (cdr args)))))
               t)
          (and (fn-nntp-session-group session) t))))
(defun ss-conclusion (session line)
  (declare (xargs :verify-guards nil))
  (let* ((args (cdr (fn-nntp-tokenize line)))
         (field (car args))
         (range (fn-nntp-parse-range (car (cdr args))))
         (parsed (fn-wildmat-parse-text (fn-nntp-xpat-join (cdr (cdr args)))))
         (group (fn-nntp-session-group session))
         (articles (fn-state-articles *ss-archive*)))
    (equal (fn-nntp-step-pinned session *ss-archive* nil nil *ss-env*
                                (list :command line))
           (fn-nntp-multi
            session (fn-nntp-hdr-initial t)
            (fn-nntp-hdr-lines-for-numbers
             field group
             (fn-nss-hits field (fn-wildmat-result-value parsed) group
                          (fn-nntp-group-range-numbers
                           group (fn-nntp-range-low range)
                           (fn-nntp-range-high range) articles)
                          articles)
             articles)))))
(defun ss-all-but (i n)
  (if (zp n) nil
    (cons (not (equal i 0)) (ss-all-but (1- i) (1- n)))))
(defmacro ss-without (i session text)
  `(and (equal (ss-hyps ,session ,text) (ss-all-but ,i 10))
        (not (ss-conclusion ,session ,text))))
(defconst *ss-line* (ss-tok "XPAT Subject 1-9 *alpha*"))
; Witness: every hypothesis, the conclusion, and the block the node sends.
(assert-event (equal (ss-hyps *ss-session* *ss-line*) (ss-all-but -1 10)))
(assert-event (ss-conclusion *ss-session* *ss-line*))
(assert-event (equal (fn-nntp-result-effects (ss-step *ss-session* "XPAT Subject 1-9 *alpha*"))
                     (ss-block "221 header follows"
                               (list "1 search alpha" "2 Re: search alpha"))))
(defun ss-spaces (n) (if (zp n) nil (cons 32 (ss-spaces (1- n)))))
; 0 fn-nntp-sessionp: a five-element record whose slots read the same.
(assert-event (ss-without 0 (list t "fn.letters" nil t :extra) *ss-line*))
; 1 open.
(assert-event (ss-without 1 (fn-nntp-make-session nil "fn.letters" nil t) *ss-line*))
; 2 projected: the step's 503.
(assert-event (ss-without 2 (fn-nntp-make-session t "fn.letters" nil nil) *ss-line*))
; 3 command input: the same tokens past the 510-octet preflight.
(assert-event (ss-without 3 *ss-session*
                          (append (ss-tok "XPAT Subject 1-9") (ss-spaces 600)
                                  (ss-tok "*alpha*"))))
; 4 each argument at most 497 octets: a 498-octet field name on a 509-octet
; line (the preflight holds; the step's 501).
(defun ss-as (n) (if (zp n) nil (cons 97 (ss-as (1- n)))))
(assert-event (ss-without 4 *ss-session*
                          (append (ss-tok "XPAT ") (ss-as 498) (ss-tok " 1-9 *"))))
; 5 the XPAT keyword: HDR's 225 block is not XPAT's 221.
(assert-event (ss-without 5 *ss-session* (ss-tok "HDR Subject 1-9 *alpha*")))
; 6 the field: a name with a colon.
(assert-event (ss-without 6 *ss-session* (ss-tok "XPAT Sub:ject 1-9 *alpha*")))
; 7 a range: the Message-ID form answers that article's line.
(assert-event (ss-without 7 *ss-session*
                          (ss-tok "XPAT Subject <b@x.invalid> *alpha*")))
; 8 a pattern that parses: none at all (the empty join does not parse).  The
; range holds no article, so the right side never runs the matcher on the
; failed parse; the step's 501 is not the empty 221 block.
(assert-event (ss-without 8 *ss-session* (ss-tok "XPAT Subject 5-9")))
; 9 a selected group: 412.
(assert-event (ss-without 9 (fn-nntp-make-session t nil nil t) *ss-line*))
