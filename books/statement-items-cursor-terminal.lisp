; Any actually scheduled terminal parse is the same paid completion.
(in-package "ACL2")
(include-book "statement-items-cursor-refinement")
(local (defthm fn-sic-run-of-done
 (implies (equal (fn-sic-at 0 c) :done) (equal (fn-sic-run q c) c))
 :hints (("Goal" :induct (fn-sic-run q c)
 :in-theory (e/d (fn-sic-run) (fn-sic-step fn-sic-at))))))
(local (defthm fn-sic-two-terminal-runs-agree
 (implies (and (natp q) (natp p)
  (equal (fn-sic-at 0 (fn-sic-run q c)) :done)
  (equal (fn-sic-at 0 (fn-sic-run p c)) :done))
  (equal (fn-sic-run q c) (fn-sic-run p c)))
 :hints (("Goal" :use ((:instance fn-sic-run-is-resumable (a q) (b p))
 (:instance fn-sic-run-is-resumable (a p) (b q))
 (:instance fn-sic-run-of-done (q p) (c (fn-sic-run q c)))
 (:instance fn-sic-run-of-done (q q) (c (fn-sic-run p c))))
 :in-theory (disable fn-sic-run fn-sic-at fn-sic-step fn-sic-run-is-resumable fn-sic-run-of-done)))))
(defthm fn-sic-terminal-begin-is-paid-completion
 (implies (and (natp q) (natp fuel) (natp outer-budget) (natp item-budget)
  (equal (fn-sic-at 0 (fn-sic-run q (fn-sic-begin fuel octets outer-budget item-budget))) :done))
  (equal (fn-sic-run q (fn-sic-begin fuel octets outer-budget item-budget))
   (fn-sic-run (fn-sic-completion-cost (fn-sic-begin fuel octets outer-budget item-budget))
    (fn-sic-begin fuel octets outer-budget item-budget))))
 :hints (("Goal" :use ((:instance fn-sic-two-terminal-runs-agree
 (c (fn-sic-begin fuel octets outer-budget item-budget))
 (p (fn-sic-completion-cost (fn-sic-begin fuel octets outer-budget item-budget))))
 (:instance fn-sic-paid-begin-completion-is-exact-old-result))
 :in-theory (disable fn-sic-at fn-sic-run fn-sic-step fn-sic-begin fn-sic-completion-cost
 fn-sic-complete fn-sic-paid-begin-completion-is-exact-old-result fn-sic-two-terminal-runs-agree))))
