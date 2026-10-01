; Actual registered source fixtures only; no installed native admission.
(in-package "ACL2")
(include-book "decoded-worker-controller-trajectory-tests")
(include-book "../../books/decoded-worker-controller-canonical")

(defun-nx fn-dwcct-retained-hypotheses (token s)
 (let* ((c (nth 2 s)) (z (fn-pww-controller c)))
  (and (fn-pwz-tokenp token)
       (eq (fn-pww-phase c) :running) (eq (fn-pww-borrow-phase c) :owned)
       (null (fn-pww-pending-action c)) (true-listp z) (true-listp (nth 1 z))
       (equal (car (fn-ewz-next-action z (nth 4 s))) :codec)
       (natp (nth 6 z)) (natp (nth 7 z)) (<= (nth 6 z) (nth 7 z))
       (<= (- (nth 7 z) (nth 6 z)) 64) (<= (nth 7 z) (fn-octets-len (nth 3 s))))))
(defun-nx fn-dwcct-full-effects (token s)
 (let* ((z (fn-pww-controller (nth 2 s)))
        (r (fn-dwc-one token (nth 2 s) (nth 3 s) (nth 4 s) (nth 5 s) (nth 6 s) (nth 7 s) (nth 8 s) (nth 9 s)))
        (next (fn-pww-controller (nth 2 r))) (compressed (nth 12 (nth 1 z)))
        (credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin (nth 5 s))) (nth 5 s)))
        (ref (fn-zin-feed (fn-pzw-quantum 1024 (nth 5 z)) credited (nth 6 z) (nth 7 z)
                (fn-pzw-room (min (nfix (nth 2 z)) (fn-pzw-stored-allowance compressed)) (fn-zin-tout credited))
                (nth 3 s) (nth 6 s) (nth 7 s) nil)))
  (equal (list (nth 8 next) (nth 6 next)
               (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin (nth 5 r))) (nth 5 r))
               (nth 6 r) (nth 7 r) (nth 8 r))
         (list (nth 0 ref) (nth 2 ref) (nth 3 ref) (nth 4 ref) (nth 5 ref) (nth 6 ref)))))
(local
 (defthm fn-dwcct-full-effects-positive
  (let ((s (fn-dwctt-codec-current)) (token (fn-dwctt-token)))
   (and (fn-dwcct-retained-hypotheses token s)
        (equal token (fn-pww-token (nth 2 s)))
        (fn-dwcct-full-effects token s)))
  :rule-classes nil))
(local
 (defthm fn-dwcct-current-token-removal
  (let* ((s (fn-dwctt-codec-current)) (token (update-nth 1 24 (fn-dwctt-token))))
   (and (fn-dwcct-retained-hypotheses token s)
        (not (equal token (fn-pww-token (nth 2 s))))
        (not (fn-dwcct-full-effects token s))))
  :rule-classes nil))
(local
 (defthm fn-dwcct-noncodec-window-positive
  (let* ((s (fn-dwctt-codec-one))
         (action (fn-ewz-next-action (fn-pww-controller (nth 2 s)) (nth 4 s)))
         (r (fn-dwc-one (fn-dwctt-token) (nth 2 s) (nth 3 s) (nth 4 s) (nth 5 s) (nth 6 s) (nth 7 s) (nth 8 s) (nth 9 s))))
   (and (not (equal (car action) :codec))
        (equal (nth 9 r) (nth 9 s))
        (equal (take 2 (nth 0 (nth 9 r))) '(66 67))))
  :rule-classes nil))

(defun-nx fn-dwcct-trailer-issued ()
 (let* ((s (fn-dwctt-codec-one))
        (h1 (fn-dwc-one (fn-dwctt-token) (nth 2 s) (nth 3 s) (nth 4 s) (nth 5 s) (nth 6 s) (nth 7 s) (nth 8 s) (nth 9 s)))
        (h2 (fn-dwc-one (fn-dwctt-token) (nth 2 h1) (nth 3 h1) (nth 4 h1) (nth 5 h1) (nth 6 h1) (nth 7 h1) (nth 8 h1) (nth 9 h1))))
  (fn-dwc-one (fn-dwctt-token) (nth 2 h2) (nth 3 h2) (nth 4 h2) (nth 5 h2) (nth 6 h2) (nth 7 h2) (nth 8 h2) (nth 9 h2))))
(local
 (defthm fn-dwcct-current-trailer-read-window-positive
  (let* ((s (fn-dwcct-trailer-issued))
         (c (nth 2 s)) (z (fn-pww-controller c))
         (trailer (fn-blake3 (fn-dwctt-message)))
         (r (fn-dwc-read-observation (fn-dwctt-token) (fn-pww-action-revision c) :ok
                                    c trailer (nth 4 s) (nth 9 s))))
   (and (equal (car s) :read) (equal (car (fn-pww-pending-action c)) :read)
        (eq (fn-pww-phase c) :running) (eq (fn-pww-borrow-phase c) :owned)
        (equal (fn-pww-token c) (fn-dwctt-token)) (natp (fn-pww-action-revision c))
        (equal (nth 5 (nth 1 z)) 0)
        (equal (nth 4 r) (nth 9 s)) (equal (take 2 (nth 0 (nth 4 r))) '(66 67))
        (fn-ewz-publication (fn-pww-controller (nth 1 r)))))
  :rule-classes nil))
(local
 (defthm fn-dwcct-codec-action-window-removal
  (let* ((s (fn-dwctt-codec-current))
         (action (fn-ewz-next-action (fn-pww-controller (nth 2 s)) (nth 4 s)))
         (r (fn-dwctt-codec-one)))
   (and (equal (car action) :codec)
        (not (equal (nth 9 r) (nth 9 s)))))
  :rule-classes nil))
; Corrupted logical raw request: the typed plan invariant is deliberately
; broken. This is not a valid native admitted job or an activation fixture.
(local
 (defthm fn-dwcct-zero-raw-window-removal
  (let* ((s (fn-dwctt-issued-read)) (c (nth 2 s))
         (z (fn-pww-controller c))
         (z (update-nth 1 (update-nth 4 0 (update-nth 5 1 (nth 1 z))) z))
         (c (update-fn-pww-controller z c))
         (h (update-pgs-dc-capture (fn-ews-capture (nth 1 z)) (nth 4 s)))
         (r (fn-dwc-read-observation (fn-dwctt-token) (fn-pww-action-revision c) :ok
                                     c (fn-dwctt-message) h (nth 9 s))))
   (and (not (equal (nth 5 (nth 1 z)) 0))
        (fn-pwz-tokenp (fn-dwctt-token)) (equal (fn-dwctt-token) (fn-pww-token c))
        (eq (fn-pww-phase c) :running) (eq (fn-pww-borrow-phase c) :owned)
        (natp (fn-pww-action-revision c))
        (consp (fn-pww-pending-action c)) (true-listp (fn-pww-pending-action c))
        (equal (car (fn-pww-pending-action c)) :read)
        (true-listp z) (true-listp (nth 1 z))
        (equal (cadr (fn-pww-pending-action c)) (fn-ewz-effect z h))
        (not (equal (nth 4 r) (nth 9 s)))))
  :rule-classes nil))
