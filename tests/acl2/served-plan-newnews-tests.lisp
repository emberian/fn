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
