; Internal post-scan PRL admission; not a public runtime/constructor issuer.
(in-package "ACL2")
(include-book "decoded-worker-binding-scan")
(include-book "decoded-window-lease")

; Caller carry must establish CURRENT binding revision/root still equals the
; captured scan and this found row is the actual first incarnation binding.
; The body performs no binding lookup or graph-root equality. It reads current
; scalar ledger coordinates, preserving intervening counter-only updates.
(defun fn-dwb-admit-resolved (ledger descriptor demand scan)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (and (eq (fn-dwb-word scan) :binding-resolved)
               (equal (fn-prl-nth 1 scan) (fn-pwz-nth 0 descriptor))))
  (mv :stale-decoded-binding nil ledger)
  (let* ((budget (fn-prl-nth 0 ledger)) (charged (fn-prl-nth 1 ledger))
         (next (fn-prl-nth 2 ledger)))
   (mv-let (word next1 charged1)
    (if (and (fn-pwz-descriptorp descriptor)
             (fn-prs-vectorp demand) (equal (fn-prl-nth 3 demand) 1)
             (equal (fn-prl-nth 4 demand) 1))
     (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                   charged next (fn-prl-nth 4 budget) demand)
     (mv :invalid-decoded-window-demand next charged))
    (if (not (equal word :admitted)) (mv word nil ledger)
     (let ((token (cons :decoded-window (cons next descriptor))))
      (mv :admitted token
          (fn-prl-build budget charged1 next1
           (cons (cons token (list demand :window :running)) (fn-prl-nth 3 ledger))
           (fn-prl-nth 4 ledger)))))))))

; Complete MV equality, scoped to the retained actual binding premise.
; This algebra seam neither publishes the ledger nor authorizes constructors.
(defthm fn-dwb-admit-resolved-matches-original
 (implies
  (and (eq (fn-dwb-word scan) :binding-resolved)
       (equal (fn-prl-nth 1 scan) (fn-pwz-nth 0 descriptor))
       (equal (fn-prl-nth 5 scan)
              (fn-prl-binding (list :incarnation (fn-pwz-nth 0 descriptor))
                              (fn-prl-nth 3 ledger))))
  (equal (fn-dwb-admit-resolved ledger descriptor demand scan)
         (fn-pwz-admit ledger descriptor demand)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-dwb-admit-resolved fn-dwb-word fn-pwz-admit))))
