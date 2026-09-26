; Teeth for books/control-evidence.lisp (PKT-209, PRF-185): the rendered
; words of `control log' and `control evidence' over a real signed cancel
; (a cancel of P's, P holding cancel over fn.mod.* at generation 1), the
; keystone's reachable witness and a must-fail without its hypothesis, the
; decision-line lemma's witness and a must-fail without its hypothesis, the
; grammar, and the FNLS kind-3 request.
(in-package "ACL2")
(include-book "../../books/control-evidence")
(include-book "std/testing/must-fail" :dir :system)

(defun cet-string (octets) (fn-record-octets-string octets))
(defconst *cet-lf* (coerce (list (code-char 10)) 'string))
(defconst *cet-p* (make-list 32 :initial-element 17))
(defconst *cet-p-hex* (fn-record-octets-string (fn-stx-hex-octets *cet-p*)))
(defconst *cet-p-verified* (fn-stx-make-verdict :verified *cet-p* 1))
(defun cet-line (s) (append (fn-record-string-octets s) '(13 10)))
(defun cet-octets (lines)
  (if (consp lines)
      (append (cet-line (car lines)) (cet-octets (cdr lines)))
    (append '(13 10) (cet-line "body"))))
(defconst *cet-c2*
  (fn-make-article "<c2@example.invalid>"
                   (cet-octets (list "From: p@example.invalid"
                                     "Date: Wed, 23 Sep 2026 12:00:00 +0000"
                                     "Newsgroups: control.cancel"
                                     "Message-ID: <c2@example.invalid>"
                                     "Subject: cmsg cancel <t@example.invalid>"
                                     "Control: cancel <t@example.invalid>"))
                   (list "control.cancel") nil t nil))
(defconst *cet-t* (fn-make-article "<t@example.invalid>" nil (list "fn.mod.a") nil t nil))
(defconst *cet-raw* (list *cet-c2* *cet-t*))
(defconst *cet-v* (list (cons "<c2@example.invalid>" *cet-p-verified*)))
(defun cet-rec (seq txid msgid groups)
  (fn-record-make seq txid 1 msgid '(65) groups "a" "s" "e" 2 :legacy))
(defconst *cet-records* (list (cet-rec 0 4 "<t@example.invalid>" '("fn.mod.a"))
                              (cet-rec 1 5 "<c2@example.invalid>" '("control.cancel"))))
(defconst *cet-configs*
  (list (fn-cfg-record-make 0 1 1 (list (fn-cfg-grant-control "fn.mod.*" *cet-p-hex* "cancel")) nil)))
(defconst *cet-ws* (fn-ctl-articles-withdrawals *cet-raw* *cet-v* *cet-records* *cet-configs*))
(defconst *cet-p-words* "1111111111111111111111111111111111111111111111111111111111111111")
(defconst *cet-record-words*
  (concatenate 'string " target=<t@example.invalid> cause=<c2@example.invalid> principal="
               *cet-p-words* " scope=fn.mod.* generation=1"))
(defun cet-report (kind ws verdicts)
  (cet-string (fn-cev-report kind ws *cet-raw* verdicts *cet-records* *cet-configs*)))

; The words.  The log: one record, decided under generation 1.
(assert-event
 (equal (cet-report :control-log *cet-ws* *cet-v*)
        (concatenate 'string "withdrawals=1" *cet-lf* "withdrawal" *cet-record-words* *cet-lf*)))
; The cancel's evidence: stored at txid 5, verified, its record.
(assert-event
 (equal (cet-report '(:control-evidence . "<c2@example.invalid>") *cet-ws* *cet-v*)
        (concatenate 'string
                     "evidence message-id=<c2@example.invalid> stored=yes txid=5 verdict=verified" *cet-lf*
                     "decision=withdrawal" *cet-record-words* *cet-lf*)))
; The target's evidence: it names no target itself; the record naming it
; withdraws it on the authority basis (its group fn.mod.a is in the scope).
(assert-event
 (equal (cet-report '(:control-evidence . "<t@example.invalid>") *cet-ws* *cet-v*)
        (concatenate 'string
                     "evidence message-id=<t@example.invalid> stored=yes txid=4 verdict=unsigned" *cet-lf*
                     "decision=none" *cet-lf*
                     "withdrawn-by" *cet-record-words* " effect=authority" *cet-lf*)))
; An unsigned cancel: the decline and its reason.
(assert-event
 (equal (cet-report '(:control-evidence . "<c2@example.invalid>") nil nil)
        (concatenate 'string
                     "evidence message-id=<c2@example.invalid> stored=yes txid=5 verdict=unsigned" *cet-lf*
                     "decision=declined reason=unsigned" *cet-lf*)))
; A Message-ID the owner does not hold.
(assert-event
 (equal (cet-report '(:control-evidence . "<z@example.invalid>") *cet-ws* *cet-v*)
        (concatenate 'string "evidence message-id=<z@example.invalid> stored=no" *cet-lf*)))

; KEYSTONE fn-cev-evidence-decision-is-in-the-log.  Reachable witness: the
; hypothesis (WS is the journal of RAW) holds, the cancel is stored, its
; decision is a withdrawal record and a member of WS: both sides true.
(defun cet-plan (verdicts)
  (fn-cev-plan (fn-cev-find-article "<c2@example.invalid>" *cet-raw*)
               verdicts *cet-records* *cet-configs*))
(assert-event
 (and (equal *cet-ws* (fn-ctl-articles-withdrawals *cet-raw* *cet-v* *cet-records* *cet-configs*))
      (fn-cev-find-article "<c2@example.invalid>" *cet-raw*)
      (fn-ctl-withdrawalp (cet-plan *cet-v*))
      (member-equal (cet-plan *cet-v*) *cet-ws*)))
; The false side too: an unsigned cancel declines, and its journal holds nothing.
(assert-event
 (let ((ws (fn-ctl-articles-withdrawals *cet-raw* nil *cet-records* *cet-configs*)))
   (and (not (fn-ctl-withdrawalp (cet-plan nil)))
        (not (member-equal (cet-plan nil) ws)))))
; Without the hypothesis (records other than the journal: none carried) the
; conclusion fails: the decision is a withdrawal the records do not hold.
(assert-event (not (equal nil *cet-ws*)))
(must-fail
 (assert-event
  (iff (member-equal (cet-plan *cet-v*) nil)
       (fn-ctl-withdrawalp (cet-plan *cet-v*)))))

; fn-cev-decision-line-is-a-log-line.  Witness: the decision's words are
; "decision=" and the log's one line.
(assert-event
 (and (fn-ctl-withdrawalp (cet-plan *cet-v*))
      (equal (fn-cev-decision-line (cet-plan *cet-v*))
             (append (fn-nls-text "decision=") (fn-cev-log-line (cet-plan *cet-v*))))
      (member-equal (fn-cev-log-line (cet-plan *cet-v*)) (fn-cev-log-lines *cet-ws*))))
; Without the withdrawal-record hypothesis (a decline) the words are not a log line.
(assert-event (not (fn-ctl-withdrawalp (cet-plan nil))))
(must-fail
 (assert-event
  (equal (fn-cev-decision-line (cet-plan nil))
         (append (fn-nls-text "decision=") (fn-cev-log-line (cet-plan nil))))))
; Without the relation hypothesis the line is in no log of the carried records.
(must-fail
 (assert-event
  (member-equal (fn-cev-log-line (cet-plan *cet-v*)) (fn-cev-log-lines nil))))

; The grammar.
(assert-event (equal (fn-cevg-parse '("log")) '(:kind :control-log)))
(assert-event (equal (fn-cevg-parse '("evidence" "<a@b>"))
                     '(:kind (:control-evidence . "<a@b>"))))
(assert-event (equal (fn-cevg-parse '("evidence" "a@b")) '(:usage :message-id)))
(assert-event (equal (fn-cevg-parse '("evidence" "<a b>")) '(:usage :message-id)))
(assert-event (equal (fn-cevg-parse '("evidence")) '(:usage :message-id)))
(assert-event (equal (fn-cevg-parse '("log" "x")) '(:usage :unexpected-arguments)))
(assert-event (null (fn-cevg-parse '("list"))))
(assert-event (null (fn-cevg-parse '("grant" "ab" "cancel" "fn.*"))))

; The request: both kinds round-trip through FNLS frame kind 3, the plain
; kind-1 decoder (an owner before this) refuses it as a frame it does not
; know, and the either-kind decoder still reads a kind-1 status request.
(assert-event
 (equal (fn-cev-any-request-decode (fn-cev-any-request-encode :control-log 0))
        '(:live-status :control-log 0)))
(assert-event
 (equal (fn-cev-any-request-decode
         (fn-cev-any-request-encode '(:control-evidence . "<c2@example.invalid>") 131072))
        '(:live-status (:control-evidence . "<c2@example.invalid>") 131072)))
(assert-event
 (equal (fn-nls-request-decode (fn-cev-request-encode :control-log 0))
        '(:refused :frame)))
(assert-event
 (equal (fn-cev-any-request-decode (fn-cev-any-request-encode :obligations 7))
        '(:live-status :obligations 7)))
(assert-event (equal (fn-cev-request-encode '(:control-evidence . "nope") 0) :bad))
