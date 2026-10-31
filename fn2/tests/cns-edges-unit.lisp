; D8's subscription edges (books/cns-edges.lisp): link within a stream's
; probe window, refusal when it is full, a publish marking exactly the edges
; whose first position it reaches, the pending stack popped once per edge, an
; unlink before the pop waking nothing, two streams sharing a window kept
; apart.
(in-package "ACL2")
(include-book "../books/cns-edges")

(defun fn2-cet-link-many (stream n waiter fn2-cns-edges)
  (declare (xargs :stobjs fn2-cns-edges :guard (and (fn2-cns-edges-wfp fn2-cns-edges) (natp n)) :verify-guards nil))
  (if (zp n) (mv nil fn2-cns-edges)
    (mv-let (code e fn2-cns-edges) (fn2-cns-edge-link stream waiter 1 0 fn2-cns-edges)
      (declare (ignore e))
      (mv-let (rest fn2-cns-edges) (fn2-cet-link-many stream (- n 1) (+ 1 waiter) fn2-cns-edges)
        (mv (cons code rest) fn2-cns-edges)))))
(defun fn2-cet-pop-all (n fn2-cns-edges)
  (declare (xargs :stobjs fn2-cns-edges :guard (and (fn2-cns-edges-wfp fn2-cns-edges) (natp n)) :verify-guards nil))
  (if (or (zp n) (not (fn2-cns-ready-p fn2-cns-edges))) (mv nil fn2-cns-edges)
    (mv-let (w fn2-cns-edges) (fn2-cns-pop fn2-cns-edges)
      (mv-let (rest fn2-cns-edges) (fn2-cet-pop-all (- n 1) fn2-cns-edges)
        (mv (cons w rest) fn2-cns-edges)))))

(defun fn2-cet-run ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-cns-edges
    (mv-let (result fn2-cns-edges)
      (b* ((fn2-cns-edges (fn2-cns-edges-init 16 fn2-cns-edges))
           (fn2-cns-edges (update-fn2-cns-pending-head *fn2-cns-none* fn2-cns-edges))
           ;; stream 5: waiters 10 and 11 from position 3; stream 21 (same window mod 16): waiter 12 from 1
           ((mv c1 e1 fn2-cns-edges) (fn2-cns-edge-link 5 10 1 3 fn2-cns-edges))
           ((mv c2 & fn2-cns-edges) (fn2-cns-edge-link 5 11 1 3 fn2-cns-edges))
           ((mv c3 & fn2-cns-edges) (fn2-cns-edge-link 21 12 1 1 fn2-cns-edges))
           ;; a publish below the edges' first position wakes nothing
           (fn2-cns-edges (fn2-cns-wake-stream 5 2 fn2-cns-edges))
           (quiet (not (fn2-cns-ready-p fn2-cns-edges)))
           ;; at 3 both stream-5 edges are pending, once each (a second publish does not push twice)
           (fn2-cns-edges (fn2-cns-wake-stream 5 3 fn2-cns-edges))
           (fn2-cns-edges (fn2-cns-wake-stream 5 4 fn2-cns-edges))
           ;; waiter 10 gives up before the pop: its pop wakes nothing
           (fn2-cns-edges (fn2-cns-edge-unlink e1 fn2-cns-edges))
           ((mv woken fn2-cns-edges) (fn2-cet-pop-all 8 fn2-cns-edges))
           ;; stream 21 is woken alone
           (fn2-cns-edges (fn2-cns-wake-stream 21 1 fn2-cns-edges))
           ((mv woken21 fn2-cns-edges) (fn2-cet-pop-all 8 fn2-cns-edges))
           ;; stream 7's window is slots 7..14; free slots outside it are never used for it
           ((mv codes fn2-cns-edges) (fn2-cet-link-many 7 9 100 fn2-cns-edges))
           (used (fn2-cns-used-count fn2-cns-edges)))
        (mv (list :linked (list c1 c2 c3) :quiet quiet :woken woken :woken21 woken21 :codes codes :used used)
            fn2-cns-edges))
      result)))

(assert-event
 (let ((r (fn2-cet-run)))
   (and (equal (cadr (member-eq :linked r)) '(:ok :ok :ok))
        (cadr (member-eq :quiet r))
        ;; the stack pops 11 first (pushed last); 10's edge was unlinked: none
        (equal (cadr (member-eq :woken r)) (list 11 *fn2-cns-none*))
        (equal (cadr (member-eq :woken21 r)) '(12))
        ;; streams 5 and 21 took slots 5, 6 and 7 (21 probed past 5's two), so stream 7's
        ;; window (slots 7..14) has 7 free: the 8th and 9th edges are refused
        (equal (cadr (member-eq :codes r)) '(:ok :ok :ok :ok :ok :ok :ok :exhausted :exhausted))
        (equal (cadr (member-eq :used r)) (+ 2 7)))))
(value-triple (cw "CNS EDGES UNIT: probe-window link and refusal, wake by first position, one push per edge, unlink before pop, shared window PASS~%"))
