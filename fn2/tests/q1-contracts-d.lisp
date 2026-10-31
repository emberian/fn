; Q1's honest classification for layer D's transaction (build/coordinator/fn2/lanes/a-dm4-q1-classification.md
; section 3): the independent contract of fn2-txn. Nothing on the checking side calls a transaction,
; upload or identity handler. Three oracles:
; - WIRE's two-phase POST read over the client's octets and the served wire;
; - H's model's outcome for the article block, with the model's store seeded with the same articles
;   (tests/model/nntp_model.py through tests/upload-model-export.py, pinned in
;   evidence/upload-model.lisp as *fn2-txn-model-cases*);
; - C's IDENTITY checker (sim/check-identity.lisp): the seeded facts are recorded offers, and the
;   served transaction's answer, read from its reply, is a query judged against the checker's own
;   Binding (the first content recorded for a Message-ID is its accepted content).
; Premise B-S2-ADMISSION-INTERIM (named in *fn2-q1t-premises*): until B lands the transaction
; member, the batch admission answers :not-served, so an article the model admits is answered with
; the interim "441 posting failed" and nothing is recorded; its identity answer is :stored, judged
; as a query. When B-S2 lands, the admitted article is answered 240 by the model's pattern and the
; query becomes an offer recorded with outcome :ok; this row then changes with it.
(in-package "ACL2")
(include-book "q1-contracts")
(include-book "txn-unit")
(include-book "../sim/check-identity")

(defconst *fn2-q1t-premises* '(:b-s2-admission-interim))
; CASE is (name block data judgement mid seeds identity), as the model export writes it.
(defun fn2-q1t-seeds (seeds)
  ; the identity facts to seed: (mid-octets content-identity), the content B's BLAKE3 of the source
  (declare (xargs :verify-guards nil))
  (if (atom seeds) nil
    (cons (list (car (car seeds)) (fn-blake3 (cadr (car seeds)))) (fn2-q1t-seeds (cdr seeds)))))
(defun fn2-q1t-seeded-events (seeds)
  (declare (xargs :verify-guards nil))
  (if (atom seeds) nil
    (cons (list :offer (car (car seeds)) (fn-blake3 (cadr (car seeds))) :stored :ok)
          (fn2-q1t-seeded-events (cdr seeds)))))
; The identity answer a reply states (reading the reply text only); nil when it states none.
(defun fn2-q1t-answer (line)
  (declare (xargs :verify-guards nil))
  (cond ((equal line *fn2-q1c-upload-interim*) :stored)
        ((fn2-q1c-contains-p (fn2-cw-chars (coerce "already stored here" 'list)) line) :duplicate)
        ((fn2-q1c-contains-p (fn2-cw-chars (coerce "a different article with this Message-ID" 'list)) line) :conflict)
        (t nil)))
(defun fn2-q1t-ok (case sizes)
  (declare (xargs :verify-guards nil))
  (b* ((data (nth 2 case)) (judgement (nth 3 case)) (mid (nth 4 case)) (seeds (nth 5 case))
       (client (fn2-q1c-upload-client (nth 1 case)))
       (r (fn2-tu-run *fn2-tu-profile* (fn2-q1t-seeds seeds) (list (list client sizes))))
       (wire (car (car (nth 2 r)))) (closed (cadr (car (nth 2 r))))
       (reply (fn2-q1c-line 2 wire)))
    (and (equal (nth 0 r) :ok) (equal (nth 1 r) :quiet) (equal (nth 3 r) 0)
         (fn2-wire-pass-p client wire closed)
         (equal (fn2-wire-code (fn2-q1c-line 1 wire)) 340)
         (fn2-q1c-model-reply-p judgement reply)
         (or (not (nth 6 case))
             (equal (car (fn2-check-identity
                          (append (fn2-q1t-seeded-events seeds) (list (list :query mid (fn-blake3 data) (fn2-q1t-answer reply))))
                          *fn2-identity-contents-max*))
                    :ok)))))
(defthm-owed fn2-txn-answers-by-identity (case sizes)
  (implies (and (member-equal case *fn2-txn-model-cases*) (nat-listp sizes)
                (member-eq :b-s2-admission-interim *fn2-q1t-premises*))
           (fn2-q1t-ok case sizes))
  :schema :invariant :claim :semantic
  :teeth (fn2-txn-answers-positive fn2-txn-answers-negative)
  :doc "For H's model's POST fixtures over a seeded store, in any chunks: the served POST through the upload and the transaction passes WIRE's two-phase read; its reply is the model's outcome, where an admitted article gets the interim 441 under premise B-S2-ADMISSION-INTERIM; and where the outcome is the identity decision, C's IDENTITY checker accepts the reply's answer against its own Binding of the seeded facts.")
(defun fn2-q1t-all (cases k)
  (declare (xargs :verify-guards nil))
  (or (atom cases)
      (and (or (fn2-q1t-ok (car cases)
                           (and k (fn2-q1c-upload-chunks (len (fn2-q1c-upload-client (nth 1 (car cases)))) k)))
               (cw "TXN CONTRACT ~x0 chunks ~x1 FAIL~%" (car (car cases)) k))
           (fn2-q1t-all (cdr cases) k))))
; Positive: every case whole and in 7-octet chunks.
(defun fn2-txn-answers-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-q1t-all *fn2-txn-model-cases* nil) (fn2-q1t-all *fn2-txn-model-cases* 7)))
(defun fn2-q1t-case (name) (declare (xargs :verify-guards nil)) (assoc-equal name *fn2-txn-model-cases*))
; Negative: outside the fixtures the conclusion is false: the conflict case with its seed removed
; (the served answer is then :stored, and the model admits it, but the case still names the
; conflict reason), and the duplicate case with another content seeded (IDENTITY expects :conflict
; where the served duplicate answers, and the model's reason differs too).
(defun fn2-txn-answers-negative ()
  (declare (xargs :verify-guards nil))
  (let ((conflict (fn2-q1t-case "conflict")) (dup (fn2-q1t-case "duplicate")))
    (and (not (fn2-q1t-ok (update-nth 5 nil conflict) nil))
         (not (fn2-q1t-ok (update-nth 5 (nth 5 conflict) dup) nil))
         ; IDENTITY alone refuses a second content answered as stored
         (not (equal (car (fn2-check-identity (append (fn2-q1t-seeded-events (nth 5 conflict))
                                                      (list (list :query (nth 4 conflict) (fn-blake3 (nth 2 conflict)) :stored)))
                                              *fn2-identity-contents-max*))
                     :ok)))))

(fn2-assert-owed-teeth fn2-txn-answers-by-identity)
(value-triple (cw "Q1 CONTRACTS D: txn teeth PASS~%"))
