(in-package "ACL2")
(include-book "../../books/page-discovery-ledger")
(include-book "std/testing/assert-bang" :dir :system)
(defconst *prd-budget* '(10000 0 2 1 10))
(defconst *prd-baseline* '(3000 0 0 0 0))
(defconst *prd-start* (mv-nth 1 (mv-list 2 (fn-prl-make-baseline *prd-budget* *prd-baseline*))))
(defconst *prd-registered* (mv-nth 1 (mv-list 2 (fn-prl-register *prd-start* 11 '(8 0 1 0 0)))))
(defconst *prd-read* (mv-list 3 (fn-prd-admit *prd-registered* 11 200 64 '(4000 0 0 1 1))))
(defconst *prd-token* (mv-nth 1 *prd-read*))
(defconst *prd-issued* (mv-nth 2 *prd-read*))
; Complete positive at the actual typed unverified-read boundary.
(assert!
 (and (equal (mv-nth 0 *prd-read*) :admitted)
      (equal *prd-token* '(:discovery 0 11 200 64))
      (fn-prs-fundedp *prd-budget* *prd-baseline* '(0 0 0 0 0) (fn-prl-nth 1 *prd-issued*))
      (equal (fn-prl-close-preview *prd-issued* 11) :read-file-held)))
; Hypothesis removal: unregistered malformed-budget state is refused and
; does not satisfy the conclusion. It is explicitly a corrupted-state case.
(assert!
 (let* ((bad (fn-prl-make nil))
        (r (mv-list 3 (fn-prd-admit bad 11 200 64 '(4000 0 0 1 1)))))
   (and (not (equal (mv-nth 0 r) :admitted))
        (not (fn-prs-fundedp nil (fn-prl-baseline bad) '(0 0 0 0 0)
                            (fn-prl-nth 1 (mv-nth 2 r)))))))
; Worker slot remains occupied even though synchronous native I/O returned.
(assert! (equal (mv-list 3 (fn-prd-admit *prd-issued* 11 200 64 '(4000 0 0 1 1)))
                (list :read-resources-unavailable nil *prd-issued*)))
; Discovery can never settle into the verified cache through ordinary settle.
(assert! (equal (mv-list 2 (fn-prl-settle *prd-issued* *prd-token* t))
                (list :stale *prd-issued*)))
(defconst *prd-released* (mv-list 2 (fn-prd-release *prd-issued* *prd-token*)))
(assert! (and (equal (mv-nth 0 *prd-released*) :released)
              (equal (fn-prl-nth 1 (mv-nth 1 *prd-released*)) '(8 0 1 0 1))
              (equal (fn-prl-baseline (mv-nth 1 *prd-released*)) *prd-baseline*)
              (equal (mv-list 2 (fn-prd-release (mv-nth 1 *prd-released*) *prd-token*))
                     (list :stale (mv-nth 1 *prd-released*)))))
(assert! (equal (mv-list 2 (fn-prd-release *prd-issued* '(:discovery 0 11 201 64)))
                (list :stale *prd-issued*)))
