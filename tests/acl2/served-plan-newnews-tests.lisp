(in-package "ACL2")
(include-book "../../books/served-plan-cursor")
(include-book "newnews-metadata-cursor-tests")

(defconst *spn-cur*
  (fn-cur-make (fn-cur-context *nnmt-cur*) (fn-cur-progress *nnmt-cur*)
               (fn-nntp-crlf (fn-nntp-string-octets (fn-proto-text "NEWNEWS" :listed))) nil))
(defconst *spn-effects* (list (fn-nnw-meta-effect *spn-cur*)))

; The actual host-called plan subject, two scheduling budgets, complete
; antecedent and conclusion: initial expansion, sparse scan and final suffix.
(defthm spn-newnews-actual-plan-drains-exactly
  (let* ((plan (fn-splan-of-effects *spn-effects*))
         (small (fn-splan-cw-drain plan 1 1 200 nil nil))
         (large (fn-splan-cw-drain plan 256 256 100 nil nil)))
    (and (fn-splan-fresh-effectsp *spn-effects*)
         (fn-splan-cw-okp plan)
         (equal (mv-nth 0 small) :ok)
         (equal (mv-nth 0 large) :ok)
         (fn-splan-donep (mv-nth 2 small))
         (fn-splan-donep (mv-nth 2 large))
         (equal (mv-nth 1 small) (mv-nth 1 large))
         (equal (mv-nth 1 small) (fn-nnw-meta-remaining *spn-cur* nil nil))
         (equal (mv-nth 1 small)
                (fn-served-reply-octets (fn-ovw-expand *spn-effects* nil nil))))))

(defconst *spn-configured-groups*
  '("fn.g0" "fn.g1" "fn.g2" "fn.g3" "fn.g4" "fn.g5"
    "fn.g6" "fn.g7" "fn.g8" "fn.g9" "fn.test"))
(defconst *spn-archive*
  (fn-make-state *spn-configured-groups* nil (list *nnmt-b* *nnmt-a*) 0 nil nil))
(defconst *spn-args*
  (list (fn-nntp-string-octets "fn.test") (fn-nntp-string-octets "20000101")
        (fn-nntp-string-octets "000000")))
(defmacro spn-result ()
  '(fn-nntp-newnews-response-stream nil *spn-archive* nil *spn-args* nil nil))

; The producer the generated command arm calls, rather than a hand-built
; cursor. Eleven configured groups and a sparse first candidate force the
; selector to survive repeated quanta before matching the final group.
(defthm spn-configured-factory-and-actual-plan-drain
  (let* ((result (spn-result))
         (effects (cdr result))
         (cur (cadr (car effects)))
         (progress (fn-cur-progress cur))
         (plan (fn-splan-of-effects effects))
         (small (fn-splan-cw-drain plan 1 1 500 nil nil))
         (large (fn-splan-cw-drain plan 256 256 300 nil nil)))
    (and (equal (car result) nil)
         (fn-nnw-meta-effectp (car effects))
         (fn-nnw-configured-cursorp progress)
         (equal (fn-nnw-groups progress)
                (fn-nnw-group-source (fn-wildmat-result-value
                                      (fn-wildmat-parse (fn-nntp-string-octets "fn.test")))
                                     *spn-configured-groups*))
         (equal (fn-nnw-tail progress) (fn-state-articles *spn-archive*))
         (equal (fn-cur-context cur) (list *spn-archive* nil *spn-args*))
         (fn-splan-fresh-effectsp effects)
         (fn-splan-cw-okp plan)
         (equal (mv-nth 0 small) :ok)
         (equal (mv-nth 0 large) :ok)
         (fn-splan-donep (mv-nth 2 small))
         (fn-splan-donep (mv-nth 2 large))
         (equal (mv-nth 1 small) (mv-nth 1 large))
         (equal (mv-nth 1 small)
                (fn-served-reply-octets
                 (cdr (fn-nntp-newnews-response-cat nil *spn-archive* nil *spn-args* nil nil))))
         (equal (mv-nth 1 small)
                (append (fn-nntp-crlf
                         (fn-nntp-string-octets (fn-proto-text "NEWNEWS" :listed)))
                        (fn-nntp-string-octets "<a@x>") '(13 10 46 13 10))))))
