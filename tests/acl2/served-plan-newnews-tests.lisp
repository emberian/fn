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
         (small (fn-splan-cw-drain plan 1 1 1 1 200 nil nil))
         (large (fn-splan-cw-drain plan 256 256 256 256 100 nil nil)))
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
         (small (fn-splan-cw-drain plan 1 1 1 1 3000 nil nil))
         (large (fn-splan-cw-drain plan 256 256 256 256 3000 nil nil)))
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

; The quantum per kind (lane spans-newnews).  W' = 1 fits an OVER quantum to
; one NOV line; a NEWNEWS quantum keeps V visits and B octets.  The split
; quantum writes the same reply, and drains in a fraction of the rounds the
; uniform W' = 1 quantum takes (teeth: at 40 rounds the uniform quantum, the
; regression's shape, is not done, the split one is).
(defthm spn-split-quantum-drains-the-same-reply-sooner
  (let* ((plan (fn-splan-of-effects (cdr (spn-result))))
         (uniform (fn-splan-cw-drain plan 256 1 1 1 3000 nil nil))
         (split (fn-splan-cw-drain plan 256 1 256 4096 3000 nil nil))
         (uniform-40 (fn-splan-cw-drain plan 256 1 1 1 40 nil nil))
         (split-40 (fn-splan-cw-drain plan 256 1 256 4096 40 nil nil)))
    (and (equal (mv-nth 0 split) :ok)
         (fn-splan-donep (mv-nth 2 split))
         (equal (mv-nth 1 split) (mv-nth 1 uniform))
         (fn-splan-donep (mv-nth 2 split-40))
         (not (fn-splan-donep (mv-nth 2 uniform-40))))))

; K-NQ-YIELD's witness: the configured cursor past its status line, at V = 3
; and B = 100, yields after exactly three control visits; teeth: at B = 0 it
; yields having visited nothing.
(defthm spn-batch-yield-spends-the-visits-witness
  (let* ((cur (cadr (car (cdr (spn-result)))))
         (bare (fn-cur-make (fn-cur-context cur) (fn-cur-progress cur) nil nil))
         (r (mv-list 4 (fn-nnw-stream-batch bare 3 100 nil nil)))
         (z (mv-list 4 (fn-nnw-stream-batch bare 3 0 nil nil))))
    (and (equal (nth 3 r) :yield)
         (equal (nth 2 r) 3)
         (equal (nth 0 r) nil)
         (equal (nth 3 z) :yield)
         (equal (nth 2 z) 0))))
