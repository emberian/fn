; D8's subscription edges (books/cns-edges.lisp), after D's review: a link
; refused :behind when a publish touched the bucket since the read (K4b); a
; publish waking every edge of its bucket once, colliding streams included
; (harmless); an unlink moving the cursor past its edge; a pending bucket
; below the top whose edges all leave taking itself off the stack, so the
; source stays live; allocation from the free list and fresh rows, refused
; only when every row is in use.
(in-package "ACL2")
(include-book "../books/cns-edges")

(defun fn2-cet-take-all (n fn2-cns-edges)
  (declare (xargs :stobjs fn2-cns-edges :guard (and (fn2-cns-edges-wfp fn2-cns-edges) (natp n)) :verify-guards nil))
  (if (or (zp n) (not (fn2-cns-ready-p fn2-cns-edges))) (mv nil fn2-cns-edges)
    (mv-let (w fn2-cns-edges) (fn2-cns-take-next fn2-cns-edges)
      (mv-let (rest fn2-cns-edges) (fn2-cet-take-all (- n 1) fn2-cns-edges)
        (mv (cons w rest) fn2-cns-edges)))))
(defun fn2-cet-link-many (stream n waiter fn2-cns-edges)
  (declare (xargs :stobjs fn2-cns-edges :guard (and (fn2-cns-edges-wfp fn2-cns-edges) (natp n)) :verify-guards nil))
  (if (zp n) (mv nil nil fn2-cns-edges)
    (mv-let (code e fn2-cns-edges) (fn2-cns-edge-link stream waiter 1 1 fn2-cns-edges)
      (mv-let (codes es fn2-cns-edges) (fn2-cet-link-many stream (- n 1) (+ 1 waiter) fn2-cns-edges)
        (mv (cons code codes) (cons e es) fn2-cns-edges)))))

(defun fn2-cet-run ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-cns-edges
    (mv-let (result fn2-cns-edges)
      (b* ((fn2-cns-edges (fn2-cns-edges-init 16 fn2-cns-edges))
           ;; stream 5: waiters 10 and 11 from 3; stream 21 shares bucket 5: waiter 12 from 1
           ((mv c1 e10 fn2-cns-edges) (fn2-cns-edge-link 5 10 1 3 fn2-cns-edges))
           ((mv c2 & fn2-cns-edges) (fn2-cns-edge-link 5 11 1 3 fn2-cns-edges))
           ((mv c3 & fn2-cns-edges) (fn2-cns-edge-link 21 12 1 1 fn2-cns-edges))
           (quiet (not (fn2-cns-ready-p fn2-cns-edges)))
           ;; a publish of 3 on stream 5; a second publish while the bucket is pending adds nothing
           (fn2-cns-edges (fn2-cns-wake-stream 5 3 fn2-cns-edges))
           (fn2-cns-edges (fn2-cns-wake-stream 5 4 fn2-cns-edges))
           ;; waiter 10 leaves before its turn: the cursor moves past its edge
           (fn2-cns-edges (fn2-cns-edge-unlink e10 fn2-cns-edges))
           ((mv woken fn2-cns-edges) (fn2-cet-take-all 8 fn2-cns-edges))
           ;; the link race: the waiter read through 3 (from 4 would be right; from 3 is behind
           ;; the bucket's last publish of 4) and through 4
           ((mv behind & fn2-cns-edges) (fn2-cns-edge-link 5 13 1 4 fn2-cns-edges))
           ((mv c4 & fn2-cns-edges) (fn2-cns-edge-link 5 13 1 5 fn2-cns-edges))
           ;; bucket 6 pending under bucket 5; its only edge leaves: it leaves the stack
           ((mv c5 e20 fn2-cns-edges) (fn2-cns-edge-link 6 20 1 1 fn2-cns-edges))
           (fn2-cns-edges (fn2-cns-wake-stream 6 1 fn2-cns-edges))
           (fn2-cns-edges (fn2-cns-wake-stream 5 5 fn2-cns-edges))
           (fn2-cns-edges (fn2-cns-edge-unlink e20 fn2-cns-edges))
           ((mv woken2 fn2-cns-edges) (fn2-cet-take-all 8 fn2-cns-edges))
           (used (fn2-cns-used-count fn2-cns-edges)))
        (mv (list :linked (list c1 c2 c3 c4 c5) :quiet quiet :woken woken :behind behind :woken2 woken2 :used used)
            fn2-cns-edges))
      result)))
(defun fn2-cet-full ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-cns-edges
    (mv-let (result fn2-cns-edges)
      (b* ((fn2-cns-edges (fn2-cns-edges-init 4 fn2-cns-edges))
           ;; four edges on one stream fill every row; a fifth is refused; a release is reused
           ((mv codes es fn2-cns-edges) (fn2-cet-link-many 7 5 100 fn2-cns-edges))
           (fn2-cns-edges (fn2-cns-edge-unlink (cadr es) fn2-cns-edges))
           ((mv again e fn2-cns-edges) (fn2-cns-edge-link 3 200 1 1 fn2-cns-edges)))
        (mv (list :codes codes :again again :reused (equal e (cadr es))) fn2-cns-edges))
      result)))

(assert-event
 (let ((r (fn2-cet-run)))
   (and (equal (cadr (member-eq :linked r)) '(:ok :ok :ok :ok :ok))
        (cadr (member-eq :quiet r))
        ;; bucket 5's chain in link order, 10 gone: 11, then 12 (stream 21, a harmless wake)
        (equal (cadr (member-eq :woken r)) '(11 12))
        (equal (cadr (member-eq :behind r)) :behind)
        ;; bucket 6 left the stack with its edge; bucket 5 wakes 11, 12 and the new 13
        (equal (cadr (member-eq :woken2 r)) '(11 12 13))
        (equal (cadr (member-eq :used r)) 3))))
(assert-event
 (let ((r (fn2-cet-full)))
   (and (equal (cadr (member-eq :codes r)) '(:ok :ok :ok :ok :exhausted))
        (equal (cadr (member-eq :again r)) :ok)
        (cadr (member-eq :reused r)))))
(value-triple (cw "CNS EDGES UNIT: link behind a publish, bucket wake with collisions, unlink past the cursor, an emptied pending bucket off the stack, allocation to every row PASS~%"))
