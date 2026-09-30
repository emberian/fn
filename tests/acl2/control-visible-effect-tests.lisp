; Literal producer teeth. Fixtures mirror the existing indexed cancel data;
; this book exercises the actual FILES/history producer, not event-kind tags.
(in-package "ACL2")
(include-book "../../books/control-visible-effect")
(include-book "../../books/catalog-record")

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
  (fn-held-make seq txid txid msgid seq groups "a" "s" "e" 2 0
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

(defun cvit-art (msgid groups)
  (fn-make-article msgid nil groups nil t nil))
(defconst *cvit-t* (cvit-art "<t@example.invalid>" (list "fn.mod.a")))
(defconst *cvit-c2* (cvit-art "<c2@example.invalid>" (list "control.cancel")))
(defconst *cvit-v1* (list (cons "<c2@example.invalid>" *cvit-p-verified*)
                          (cons "<t@example.invalid>" *cvit-p-verified*)))

(defun cve-withdrawals (new old ws verdicts hist)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let* ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist))
            (files (fn-sf-make :idle 10 nil hist nil nil nil nil)))
        (mv (mv-list 2 (fn-ctl-refresh-withdrawals-effect-fx
                        new old ws verdicts files fn-hist nil)) fn-hist))
      ans)))
(defun cve-original (new old ws verdicts hist)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let* ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist))
            (files (fn-sf-make :idle 10 nil hist nil nil nil nil)))
        (mv (fn-ctl-refresh-withdrawals-fx new old ws verdicts files fn-hist nil)
            fn-hist))
      ans)))

(defun cve-visible (new old old-visible ws old-verdicts verdicts effect)
  (declare (xargs :guard t))
  (mv-list 2 (fn-ctl-refresh-visible-effect
              new old old-visible ws old-verdicts verdicts effect)))

; Reachable producer arm: a plain held article and no accepted verdict.
(assert-event
 (let* ((new (list *cvit-t*))
        (one (cve-withdrawals new nil nil nil (list *cvit-rt*))))
   (and (fn-held-p *cvit-rt*) (fn-ctl-rows-okp (list *cvit-rt*))
        (equal (car one) (cve-original new nil nil nil (list *cvit-rt*)))
        (eq (cadr one) :preserved)
        (fn-ctl-verdicts-grow-by-p nil nil *cvit-t*)
        (eq (cadr (cve-visible
                       new nil nil (car one) nil nil (cadr one))) :preserved))))

; Verified ordinary append keeps the same existing article verdict prefix.
(assert-event
 (let* ((new (list *cvit-t*))
        (verdicts (list (cons "<t@example.invalid>" *cvit-p-verified*)))
        (one (cve-withdrawals new nil nil verdicts (list *cvit-rt*))))
   (and (eq (fn-stx-verdict-token *cvit-p-verified*) :verified)
        (fn-ctl-verdicts-grow-by-p verdicts nil *cvit-t*)
        (eq (cadr one) :preserved)
        (equal (car one) (cve-original new nil nil verdicts (list *cvit-rt*)))
        (equal (car (cve-visible
                          new nil nil (car one) nil verdicts (cadr one)))
               (fn-ctl-refresh-visible new nil nil (car one) nil verdicts))
        (eq (cadr (cve-visible
                       new nil nil (car one) nil verdicts (cadr one))) :preserved))))

; The accepted author cancel produces a typed withdrawal plan and fences.
(assert-event
 (let* ((new (list *cvit-c2* *cvit-t*)) (old (list *cvit-t*))
        (one (cve-withdrawals new old nil *cvit-v1* *cvit-hist*)))
   (and (fn-hstxa-p *cvit-ec2*) (fn-ctl-rows-okp *cvit-hist*)
        (fn-ctl-withdrawalp (car (car one)))
        (equal (fn-ctl-w-target (car (car one))) "<t@example.invalid>")
        (eq (cadr one) :changed)
        (equal (car one) (cve-original new old nil *cvit-v1* *cvit-hist*))
        (eq (cadr (cve-visible
                       new old (list *cvit-t*) (car one) nil *cvit-v1*
                       (cadr one))) :changed))))

; Pending-target resolution must fence even when the old visible list is nil.
(defconst *cve-pending*
  (list (fn-ctl-withdrawal-make "<t@example.invalid>" "<early@example.invalid>"
                              "author" :author 1)))
(assert-event
 (let* ((new (list *cvit-t*))
        (one (cve-withdrawals new nil *cve-pending* nil (list *cvit-rt*))))
   (and (fn-ctl-withdrawalp (car *cve-pending*))
        (fn-ctl-targets-p *cve-pending* "<t@example.invalid>")
        (equal (car one) (cve-original new nil *cve-pending* nil (list *cvit-rt*)))
        (eq (cadr one) :changed)
        (eq (cadr (cve-visible
                       new nil nil (car one) nil nil (cadr one))) :changed))))

; A verdict update to an older article is a semantic fence, even with raw
; articles literally unchanged and no new withdrawal plan.
(assert-event
 (let* ((raw (list *cvit-t*))
        (old-verdicts nil)
        (verdicts (list (cons "<t@example.invalid>" *cvit-p-verified*)))
        (one (cve-withdrawals raw raw nil verdicts (list *cvit-rt*))))
   (and (eq (cadr one) :preserved) (not (equal verdicts old-verdicts))
        (eq (cadr (cve-visible
                       raw raw nil (car one) old-verdicts verdicts (cadr one)))
            :changed))))

; Hypothesis removal for the preserved-append theorem: retain append/growth,
; but drop preserved withdrawal effect using the actual cancellation above.
(assert-event
 (let* ((new (list *cvit-c2* *cvit-t*)) (old (list *cvit-t*))
        (old-v (cdr *cvit-v1*))
        (one (cve-withdrawals new old nil *cvit-v1* *cvit-hist*)))
   (and (consp new) (equal (cdr new) old)
        (fn-ctl-verdicts-grow-by-p *cvit-v1* old-v (car new))
        (not (eq (cadr one) :preserved))
        (not (eq (cadr (cve-visible
                            new old (list *cvit-t*) (car one) old-v *cvit-v1*
                            (cadr one))) :preserved)))))

; Hypothesis removal: append/growth are true, effect is preserved, but
; a verdict for an older article (not the arriving one) fails growth.
(assert-event
 (let* ((new (list *cvit-t* *cvit-c2*)) (old (list *cvit-c2*))
        (verdicts (list (cons "<c2@example.invalid>" *cvit-p-verified*)))
        (one (cve-withdrawals new old nil verdicts (list *cvit-rt*))))
   (and (consp new) (equal (cdr new) old) (eq (cadr one) :preserved)
        (not (fn-ctl-verdicts-grow-by-p verdicts nil (car new)))
        (not (eq (cadr (cve-visible new old nil (car one) nil verdicts
                                    (cadr one))) :preserved)))))

; Hypothesis removal: retained CONSP/growth/preserved effect but not append.
(assert-event
 (let ((new (list *cvit-t*)) (old (list *cvit-c2*)))
   (and (consp new) (not (equal (cdr new) old))
        (fn-ctl-verdicts-grow-by-p nil nil (car new))
        (not (eq (cadr (cve-visible new old nil nil nil nil :preserved))
                 :preserved)))))

; Corrupted-state removal of CONSP; the other three conditions remain true.
(assert-event
 (and (not (consp 17)) (equal (fn-ag-cdr 17) nil)
      (fn-ctl-verdicts-grow-by-p nil nil (fn-ag-car 17))
      (not (eq (cadr (cve-visible 17 nil nil nil nil nil :preserved)) :preserved))))

(defun cve-candidate-row (m hist candidate)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let* ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist))
             (files (fn-sf-make :idle 10 nil hist nil nil nil nil)))
        (mv (fn-ctl-row-event-candidate-fx m files fn-hist candidate) fn-hist))
      ans)))

; Historical target survives a same-Message-ID candidate; absent target
; selects only matching candidate, not an arbitrary row.
(assert-event
 (and (fn-held-p *cvit-rt*) (fn-held-p *cvit-rt2*)
      (fn-ctl-rows-okp (list *cvit-rt*))
      (equal (cve-candidate-row "<t@example.invalid>" (list *cvit-rt*) *cvit-rt2*)
             *cvit-rt*)
      (equal (cve-candidate-row "<t@example.invalid>" nil *cvit-rt2*) *cvit-rt2*)
      (null (cve-candidate-row "<other@example.invalid>" nil *cvit-rt2*))
      (equal (cve-candidate-row "<t@example.invalid>" (list *cvit-rt*) *cvit-rt2*)
             (fn-ctl-row-event "<t@example.invalid>" (list *cvit-rt* *cvit-rt2*)))))

(defun cve-candidate-index (m records hist candidate)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let* ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist))
             (files (fn-sf-make :idle 10 nil records nil nil nil nil)))
        (mv (fn-ctl-row-event-candidate-fx m files fn-hist candidate) fn-hist))
      ans)))
(defconst *cve-other-rt*
  (cvit-rec 0 6 "<t@example.invalid>" '("fn.mod.a") *cvit-o-bytes*))
; H1 removal for post-install selection: rows agree, history index differs.
(assert-event
 (and (fn-ctl-rows-okp (list *cvit-rt*))
      (not (equal (list *cve-other-rt*) (list *cvit-rt*)))
      (equal (cve-candidate-index "<t@example.invalid>" (list *cvit-rt*)
                                  (list *cve-other-rt*) *cvit-rt2*) *cve-other-rt*)
      (not (equal (cve-candidate-index "<t@example.invalid>" (list *cvit-rt*)
                                        (list *cve-other-rt*) *cvit-rt2*)
                  (fn-ctl-row-event "<t@example.invalid>"
                                    (list *cvit-rt* *cvit-rt2*))))))

(defconst *cve-fake*
  (list 0 3 3 "<t@example.invalid>" :no-handle '("fn.mod.a") "a" "s" "e" 2 0
        nil nil nil nil))
; Corrupted-state H2 removal: the index is exactly these rows, but a fake
; row passes only the event-row shape and is skipped by the held-row index.
(assert-event
 (and (equal (list *cve-fake*) (list *cve-fake*))
      (not (fn-ctl-rows-okp (list *cve-fake*))) (not (fn-held-p *cve-fake*))
      (equal (cve-candidate-index "<t@example.invalid>" (list *cve-fake*)
                                  (list *cve-fake*) *cvit-rt2*) *cvit-rt2*)
      (not (equal (cve-candidate-index "<t@example.invalid>" (list *cve-fake*)
                                        (list *cve-fake*) *cvit-rt2*)
                  (fn-ctl-row-event "<t@example.invalid>"
                                    (list *cve-fake* *cvit-rt2*))))))
