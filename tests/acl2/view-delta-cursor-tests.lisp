; UNHOOKED cert-roots (2026-10-02): out of the Makefile certify roots -- its closure reaches books/view-delta-cursor-refinement, a Codex-era book that never certified (fn-mxc-put-is-put-chars-of-nthcdr fails). The code stays; it certifies again with that book.
(in-package "ACL2")
(include-book "../../books/view-delta-cursor-refinement")

(defun vcut-drive (c fuel)
 (declare (xargs :guard (natp fuel)))
 (mv-let (next used) (fn-vcu-drive c fuel) (declare (ignore used)) next))

(defun vcut-run (c quantum turns)
 (declare (xargs :mode :program))
 (if (or (zp turns) (eq (fn-vcu-at 0 c) :done)) c
  (mv-let (next used) (fn-vcu-drive c quantum)
   (if (and (natp used) (< 0 used) (<= used quantum))
    (vcut-run next quantum (1- turns))
    '(:harness-error)))))

(defconst *vcut-old*
 (fn-vdc-bump "ab" 11 (fn-vdc-bump "ab" 7
  (fn-vdc-bump "ac" 9 (fn-vdc-bump "z" 13 (fn-vdc-bump "" 5 nil))))))

; Literal complete positive witness for the completed-result keystone.
(assert-event
 (let* ((start (fn-vcu-begin "ab" 7 t *vcut-old*))
        (end (vcut-drive start 200)))
  (and (eq (fn-vcu-at 0 end) :done)
       (equal (fn-vcu-result end) (list :done (fn-vdc-unbump "ab" 7 *vcut-old*)))
       (equal (fn-vdc-get "ab" (cadr (fn-vcu-result end))) '(1 . 11))
       (equal (fn-vdc-get "ac" (cadr (fn-vcu-result end))) '(1 . 9)))))

; Hypothesis removal: a yielded cursor is not a completed aggregate result.
(assert-event
 (let* ((start (fn-vcu-begin "ab" 7 t *vcut-old*))
        (end (vcut-drive start 1)))
  (and (not (eq (fn-vcu-at 0 end) :done))
       (not (equal (fn-vcu-result end)
                   (list :done (fn-vdc-unbump "ab" 7 *vcut-old*)))))))

; Full positive statements for step/drive denotation preservation and work.
(assert-event
 (let ((start (fn-vcu-begin "ac" 21 nil *vcut-old*)))
  (mv-let (next used) (fn-vcu-drive start 3)
   (and (equal used 3) (<= used (nfix 3))
        (equal (fn-vcu-meaning (fn-vcu-step start)) (fn-vcu-meaning start))
        (equal (fn-vcu-meaning next) (fn-vcu-meaning start))))))

(assert-event
 (let* ((start (fn-vcu-begin "ac" 21 nil *vcut-old*))
        (fuel (fn-vcu-work-left start)) (end (vcut-drive start fuel)))
  (and (fn-vcu-livep start) (<= (fn-vcu-work-left start) (nfix fuel))
       (not (eq (fn-vcu-at 0 start) :done))
       (fn-vcu-livep (fn-vcu-step start))
       (< (fn-vcu-work-left (fn-vcu-step start)) (fn-vcu-work-left start))
       (eq (fn-vcu-at 0 end) :done))))

; Remove the sufficient-fuel premise while retaining liveness: no completion.
(assert-event
 (let ((start (fn-vcu-begin "ac" 21 nil *vcut-old*)))
  (and (fn-vcu-livep start) (not (<= (fn-vcu-work-left start) (nfix 0)))
       (not (eq (fn-vcu-at 0 (vcut-drive start 0)) :done)))))
; Remove liveness while retaining sufficient fuel: invalid phase cannot advance.
(assert-event
 (let ((bad '(:invalid)))
  (and (not (fn-vcu-livep bad)) (<= (fn-vcu-work-left bad) (nfix 10))
       (not (eq (fn-vcu-at 0 (vcut-drive bad 10)) :done)))))
; Each strict-progress hypothesis is necessary independently.
(assert-event
 (let ((bad '(:invalid)) (done (fn-vcu-begin 99 1 nil nil)))
  (and (not (fn-vcu-livep bad)) (not (eq (fn-vcu-at 0 bad) :done))
       (not (< (fn-vcu-work-left (fn-vcu-step bad)) (fn-vcu-work-left bad)))
       (fn-vcu-livep done) (eq (fn-vcu-at 0 done) :done)
       (not (< (fn-vcu-work-left (fn-vcu-step done)) (fn-vcu-work-left done))))))

(assert-event
 (let* ((end (vcut-run (fn-vcu-begin "ab" 7 t *vcut-old*) 1 1000))
        (view (cadr (fn-vcu-result end)))
        (end2 (vcut-run (fn-vcu-begin "ab" 11 t view) 3 1000))
        (view2 (cadr (fn-vcu-result end2))))
  (and (equal (fn-vcu-result end) (list :done (fn-vdc-unbump "ab" 7 *vcut-old*)))
       (equal (fn-vcu-result end2) (list :done (fn-vdc-unbump "ab" 11 view)))
       (equal (fn-vdc-get "ab" view2) '(0 . 0))
       (equal (fn-vdc-get "ab" *vcut-old*) '(2 . 18))
       (equal (fn-vcu-step end) end)
       (mv-let (again used) (fn-vcu-drive end 4)
        (and (equal again end) (equal used 0))))))

(defun vcut-case (key weight release trie)
 (declare (xargs :mode :program))
 (equal (fn-vcu-result (vcut-run (fn-vcu-begin key weight release trie) 1 2000))
        (list :done (if release (fn-vdc-unbump key weight trie)
                                (fn-vdc-bump key weight trie)))))
(assert-event
 (and (vcut-case "" 4 nil *vcut-old*)
      (vcut-case "missing" 7 nil *vcut-old*)
      (vcut-case "absent" 7 t *vcut-old*)
      (vcut-case "ab" 999 t *vcut-old*)
      (vcut-case "ac" 999 t *vcut-old*)
      (vcut-case 99 4 nil *vcut-old*)
      (vcut-case (coerce (make-list 256 :initial-element #\a) 'string) 9 nil *vcut-old*)
      ; Corrupted representation fixture, not a reachable-state witness.
      (vcut-case "ab" 4 nil '(17 (#\a . invalid) (#\z . other)))
      (vcut-case "" 4 t '((:fn-midx-value . broken)))))
