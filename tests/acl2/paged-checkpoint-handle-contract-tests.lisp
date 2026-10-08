; Ground refutation of literal handle independence (S ruling 4).
; Both captures successfully admit the article; no refusal hides its handle.
(in-package "ACL2")
(include-book "../../books/store-finalize-incremental")
(include-book "must-fail-checked")
(defconst *sfi-t-stamp* *fn-cfg-default-stamp*)
(defconst *sfi-t-undertake*
  (fn-store-retention-event-make :undertake 0 0 0
                                 "forward-sfi" "subject" "evidence" 10))
(defconst *sfi-t-release*
  (fn-store-retention-event-make :release 1 1 1
                                 "forward-sfi" "subject" "evidence" 0))
(defconst *sfi-t-decrease*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *sfi-t-stamp*))
(defconst *sfi-t-increase*
  (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 20)) *sfi-t-stamp*))
(defun sfi-t-article (sequence txid msgid obligation)
  (fn-held-plain (fn-record-make sequence txid txid msgid '(65) '("fn.test")
                                 obligation "subject" "evidence" 2 841000000)
                 sequence))
(defconst *sfi-t-article* (sfi-t-article 2 7 "<sfi@example.invalid>" "archive-sfi"))
(defconst *sfi-t-article-2*
  (sfi-t-article 3 8 "<sfi-2@example.invalid>" "archive-sfi-2"))

(defconst *sfi-t-configs*
  (list *fn-cfg-default-record* *sfi-t-decrease* *sfi-t-increase*))
(defconst *sfi-t-prefix* (list *sfi-t-undertake* *sfi-t-release* *sfi-t-article*))
(defconst *sfi-t-base* (fn-sco-capture *sfi-t-configs* *sfi-t-prefix*))
(defconst *sfi-t-f0* 8)
(defconst *sfi-t-f1* 9)
(defconst *sfi-t-q* (list *sfi-t-article-2*))
(defconst *sfi-t-next* (fn-sf-next-lower (fn-sco-records *sfi-t-base*) 0))


(defconst *pck-handle-five*
 (fn-sco-capture *sfi-t-configs*
  (list *sfi-t-undertake* *sfi-t-release* (update-nth 4 5 *sfi-t-article*))))
(assert-event
 (and (fn-held-p *sfi-t-article*)
      (fn-held-p (update-nth 4 5 *sfi-t-article*))
      (fn-sco-pausedp (fn-sco-cpr *sfi-t-base*))
      (fn-sco-pausedp (fn-sco-cpr *pck-handle-five*))
      (equal (fn-sn-open-kind (fn-sco-finalize *sfi-t-base* *sfi-t-configs* 8)) :ok)
      (equal (fn-sn-open-kind (fn-sco-finalize *pck-handle-five* *sfi-t-configs* 8)) :ok)
      (not (equal (fn-sco-cpr *sfi-t-base*) (fn-sco-cpr *pck-handle-five*)))))

(must-fail-checked
 (defthm pck-handles-do-not-change-the-cpr-root
   (equal (fn-sco-cpr *sfi-t-base*) (fn-sco-cpr *pck-handle-five*))))
