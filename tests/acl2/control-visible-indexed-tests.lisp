; Teeth for books/control-visible-indexed.lisp: the cancel refresh's row
; lookup through the Store's Message-ID index.
;
; KEYSTONE fn-ctl-row-event-ix-is-row-event (and its refresh restatement
; fn-ctl-refresh-withdrawals-ix-is-refresh-withdrawals): under (H1) the
; index corresponds to the history and (H2) the rows agree, the index
; lookup is the walk.  The positive witness is a Store history (every
; record a Store event with its position as its sequence,
; fn-sf-record-listp, from which H2 follows by fn-ctl-rows-okp-of-sf-record-
; listp) with a plain held row, a composite row and a duplicate Message-ID
; (the oldest wins), and asserts the index branch is the one taken.  One
; must-fail per hypothesis.
(in-package "ACL2")
(include-book "../../books/control-visible-indexed")
(include-book "../../books/catalog-record")   ; fn-held-facts-of: the rows' facts
(include-book "must-fail-checked")

; lane history-columns-3: the readers take the history stobj fn-hist.
(defun fn-ctl-refresh-withdrawals-ix-hx (new old ws verdicts records hist configs)
  ; fn-ctl-refresh-withdrawals-ix over a history stobj loaded with HIST (R holds when HIST is the history it reads).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist)))
        (mv (fn-ctl-refresh-withdrawals-ix new old ws verdicts records fn-hist configs) fn-hist))
      ans)))
(defun fn-ctl-row-event-ix-hx (m records hist)
  ; fn-ctl-row-event-ix over a history stobj loaded with HIST (R holds when HIST is the history it reads).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist)))
        (mv (fn-ctl-row-event-ix m records fn-hist) fn-hist))
      ans)))

(defconst *cvit-p* (make-list 32 :initial-element 17))
(defconst *cvit-p-verified* (fn-stx-make-verdict :verified *cvit-p* 1))
(defun cvit-line (text)
  (append (fn-record-string-octets text) '(13 10)))
(defun cvit-octets (lines)
  (if (consp lines)
      (append (cvit-line (car lines)) (cvit-octets (cdr lines)))
    (append '(13 10) (cvit-line "body"))))
(defconst *cvit-t-bytes*
  (cvit-octets (list "From: p@example.invalid" "Newsgroups: fn.mod.a"
                     "Message-ID: <t@example.invalid>" "Subject: t")))
(defconst *cvit-o-bytes*
  (cvit-octets (list "From: o@example.invalid" "Newsgroups: fn.mod.a"
                     "Message-ID: <t@example.invalid>" "Subject: again")))
(defconst *cvit-c2-bytes*
  (cvit-octets (list "From: p@example.invalid"
                     "Date: Wed, 23 Sep 2026 12:00:00 +0000"
                     "Newsgroups: control.cancel"
                     "Message-ID: <c2@example.invalid>"
                     "Subject: cmsg cancel <t@example.invalid>"
                     "Control: cancel <t@example.invalid>")))

; A held row of BYTES at sequence SEQ and txid TXID (= its generation, as a
; Store record's is); its handle is SEQ.
(defun cvit-rec (seq txid msgid groups bytes)
  (fn-held-make seq txid txid msgid seq groups "a" "s" "e" 2 :legacy
                (fn-held-facts-of bytes)
                (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) nil nil))

(defconst *cvit-rt* (cvit-rec 0 4 "<t@example.invalid>" '("fn.mod.a") *cvit-t-bytes*))
; The signed cancel, retained as a composite row: the wire composite (its
; own coordinates: sequence 1, txid 5) beside the interned article.
(defconst *cvit-rc2* (cvit-rec 1 5 "<c2@example.invalid>" '("control.cancel")
                               *cvit-c2-bytes*))
(defconst *cvit-ec2*
  (fn-hstxa-make (fn-stxa-make 1 5 5 0 '(1) '(1) '(1) '(1)) *cvit-rc2*))
; A later row reusing T's Message-ID (the duplicate gate reads the node's
; articles; a row outlives its article's expiry).
(defconst *cvit-rt2* (cvit-rec 2 6 "<t@example.invalid>" '("fn.mod.a") *cvit-o-bytes*))
(defconst *cvit-hist* (list *cvit-rt* *cvit-ec2* *cvit-rt2*))
(defconst *cvit-ix* *cvit-hist*)

; The history is a Store history; the rows agree (H2); the index is the
; history's (H1).
(assert-event
 (and (fn-sf-record-listp *cvit-hist* 0 0 10)
      (fn-hstxa-p *cvit-ec2*)
      (fn-ctl-rows-okp *cvit-hist*)
      (equal *cvit-ix* *cvit-hist*)))

(defun cvit-index-branch (m ix)
  (nth (fn-record-sequence (car (fn-cei-article-records-for m ix))) ix))

; KEYSTONE fn-ctl-row-event-ix-is-row-event, positive witness: equal to the
; walk for the plain row's Message-ID (the OLDEST of its two rows), the
; composite's and an absent one; the index branch is the one taken.
(assert-event
 (and (equal (fn-ctl-row-event-ix-hx "<t@example.invalid>" *cvit-hist* *cvit-ix*)
             (fn-ctl-row-event "<t@example.invalid>" *cvit-hist*))
      (equal (fn-ctl-row-event-ix-hx "<t@example.invalid>" *cvit-hist* *cvit-ix*) *cvit-rt*)
      (equal (cvit-index-branch "<t@example.invalid>" *cvit-ix*) *cvit-rt*)
      (equal (len (fn-cei-article-records-for "<t@example.invalid>" *cvit-ix*)) 2)
      (equal (fn-ctl-row-event-ix-hx "<c2@example.invalid>" *cvit-hist* *cvit-ix*)
             (fn-ctl-row-event "<c2@example.invalid>" *cvit-hist*))
      (equal (fn-ctl-row-event-ix-hx "<c2@example.invalid>" *cvit-hist* *cvit-ix*) *cvit-ec2*)
      (equal (cvit-index-branch "<c2@example.invalid>" *cvit-ix*) *cvit-ec2*)
      (equal (fn-ctl-row-event-ix-hx "<x@example.invalid>" *cvit-hist* *cvit-ix*) nil)
      (equal (fn-ctl-row-event "<x@example.invalid>" *cvit-hist*) nil)))

; KEYSTONE fn-ctl-refresh-withdrawals-ix-is-refresh-withdrawals, positive
; witness: C2 arrives over (T); the record it decides (from the composite's
; row, under the config at the composite's txid) withdraws T.
(defun cvit-art (msgid groups)
  (fn-make-article msgid nil groups nil t nil))
(defconst *cvit-t* (cvit-art "<t@example.invalid>" (list "fn.mod.a")))
(defconst *cvit-c2* (cvit-art "<c2@example.invalid>" (list "control.cancel")))
(defconst *cvit-v1* (list (cons "<c2@example.invalid>" *cvit-p-verified*)
                          (cons "<t@example.invalid>" *cvit-p-verified*)))
(assert-event
 (let ((ix (fn-ctl-refresh-withdrawals-ix-hx (list *cvit-c2* *cvit-t*) (list *cvit-t*) nil
                                          *cvit-v1* *cvit-hist* *cvit-ix* nil))
       (ref (fn-ctl-refresh-withdrawals (list *cvit-c2* *cvit-t*) (list *cvit-t*) nil
                                        *cvit-v1* *cvit-hist* nil)))
   (and (equal ix ref)
        (equal (len ix) 1)
        (equal (fn-ctl-w-target (car ix)) "<t@example.invalid>"))))

; Teeth, H1 (the index is the history's): an index of another history,
; whose one row for T sits at sequence 0, answers that row; the walk
; answers T's own.  H2 holds.
(defconst *cvit-other-rt* (cvit-rec 0 6 "<t@example.invalid>" '("fn.mod.a") *cvit-o-bytes*))
(defconst *cvit-bad-ix* (list *cvit-other-rt*))
(assert-event
 (and (fn-ctl-rows-okp *cvit-hist*)
      (not (equal *cvit-bad-ix* *cvit-hist*))
      (equal (cvit-index-branch "<t@example.invalid>" *cvit-bad-ix*) *cvit-other-rt*)))
(must-fail-checked
 (assert-event
  (equal (fn-ctl-row-event-ix-hx "<t@example.invalid>" *cvit-hist* *cvit-bad-ix*)
         (fn-ctl-row-event "<t@example.invalid>" *cvit-hist*))))

; Teeth, H2 (the rows agree): a history whose first event has a row's head
; and shape and carries T's Message-ID but is no held row (its payload
; position is no handle), so the index skips it and the walk does not.  H1
; holds.
(defconst *cvit-fake*
  (list 0 3 3 "<t@example.invalid>" :no-handle '("fn.mod.a") "a" "s" "e" 2 :legacy
        nil nil nil nil))
(defconst *cvit-rt1* (cvit-rec 1 4 "<t@example.invalid>" '("fn.mod.a") *cvit-t-bytes*))
(defconst *cvit-fake-hist* (list *cvit-fake* *cvit-rt1*))
(defconst *cvit-fake-ix* *cvit-fake-hist*)
(assert-event
 (and (equal *cvit-fake-ix* *cvit-fake-hist*)
      (not (fn-ctl-rows-okp *cvit-fake-hist*))
      (not (fn-held-p *cvit-fake*))
      (equal (fn-ctl-event-row *cvit-fake*) *cvit-fake*)
      (equal (fn-ctl-row-event "<t@example.invalid>" *cvit-fake-hist*) *cvit-fake*)))
(must-fail-checked
 (assert-event
  (equal (fn-ctl-row-event-ix-hx "<t@example.invalid>" *cvit-fake-hist* *cvit-fake-ix*)
         (fn-ctl-row-event "<t@example.invalid>" *cvit-fake-hist*))))

; The dispatch fix (books/control-visible.lisp fn-ctl-event-row): a
; standalone verdict event (fn-stxe-p: a natural head, T's Message-ID at a
; row's Message-ID position) before T's row is a Store event and no row;
; the walk skips it, as the index does.  Before the fix the walk answered
; the verdict event, whose facts are nil: a cancel so preceded withdrew
; nothing.
(defconst *cvit-stxe*
  (fn-stxe-make 0 3 3 "<t@example.invalid>" :verified *cvit-p* 1 '(1)))
(defconst *cvit-stxe-hist* (list *cvit-stxe* *cvit-rt1*))
(assert-event
 (and (fn-stxe-p *cvit-stxe*)
      (fn-sf-record-listp *cvit-stxe-hist* 0 0 10)
      (fn-ctl-rows-okp *cvit-stxe-hist*)
      (null (fn-ctl-event-row *cvit-stxe*))
      (equal (fn-ctl-row-event "<t@example.invalid>" *cvit-stxe-hist*) *cvit-rt1*)
      (equal (fn-ctl-row-event-ix-hx "<t@example.invalid>" *cvit-stxe-hist*
                                  *cvit-stxe-hist*)
             *cvit-rt1*)))
