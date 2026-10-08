; The old metadata admission premise already establishes the shared held fold.
; The root/open model switch is separate; this test does not claim it is wired.
(in-package "ACL2")
(include-book "../../books/paged-checkpoint")
(include-book "paged-checkpoint-held-tests")

(defun pckhb-f (configs recs)
  (declare (xargs :guard t) (ignore configs recs)) nil)
(defattach (fn-pck-f pckhb-f))

(assert-event
 (and (true-listp *pckh-wire*)
      (fn-pck-context-agreep (fn-pck-seed) (fn-pck-seed)) (natp 0)
      (fn-pck-context-agreep
       (fn-pck-st-of (fn-pck-seed) *pckh-wire*)
       (fn-scka-fold-at (fn-pck-seed) *pckh-wire* 0))
      (fn-pck-recordsp *pckh-configs* *pckh-wire*)
      (not (equal (fn-pck-held *pckh-wire*) :bad))
      (not (equal (fn-ock-recover-full *pckh-configs* 4 *pckh-held* 4) :fault))))

; The metadata loop stops at an atom; the shared replay rejects a dotted tail.
; This is why the bridge needs the proper-list fact recordsp already supplies.
(must-fail-checked
 (assert-event
  (fn-pck-context-agreep
   (fn-pck-st-of (fn-pck-seed) (append *pckh-wire* 7))
   (fn-scka-fold-at (fn-pck-seed) (append *pckh-wire* 7) 0))))

(must-fail-checked
 (assert-event
  (fn-pck-context-agreep
   (fn-pck-st-of (fn-ssr-seed (fn-stxk-initial-context 1)) *pckh-wire*)
   (fn-scka-fold-at (fn-pck-seed) *pckh-wire* 0))))
