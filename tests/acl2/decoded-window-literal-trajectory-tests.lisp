(in-package "ACL2")
(include-book "../../books/decoded-window-literal-trajectory")

; Test-only observer stops before the actual ready literal scheduling branch.
(defun pwzlt-reach-ready (fuel ip fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel)
          (and (equal (fn-zin-mode fn-zin-st) 8) (fn-zin-freshp fn-zin-st)
               (fn-zin-lit-ready-p fn-zin-st fn-zin-tab)))
      (mv ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (mv-let (status b ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (fn-zin-loop-ahead 1 ip (fn-octets-len fn-octets) 64 fn-zin-st fn-octets
                   fn-zin-win fn-zin-tab fn-zin-out)
      (declare (ignore status b))
      (pwzlt-reach-ready (1- fuel) ip fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))

(local
 (defthm pwzlt-actual-ready-literal-step-reachable
   (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
          (reach (pwzlt-reach-ready 32 0 (car init) '(115 116 28 177 0 0)
                                    (mv-nth 1 init) (mv-nth 2 init) (mv-nth 3 init)))
          (s (mv-nth 1 reach)) (w (mv-nth 2 reach))
          (tab (mv-nth 3 reach)) (out (mv-nth 4 reach)))
     (and (posp 64) (equal (fn-zin-mode s) 8) (fn-zin-freshp s)
          (fn-zin-lit-ready-p s tab)
          (equal (fn-zin-step 64 s w tab out)
                 (fn-pwz-action-sequence (car (fn-zin-lits 64 s w tab out)) s w tab out))))
   :rule-classes nil))

; Corrupted-state/request witnesses remove one exact step-join hypothesis.
(defconst *pwzlt-model-win* (make-list 65536 :initial-element 0))
(defconst *pwzlt-model-tab* (update-nth 672 65 (update-nth 642 1 (update-nth 1447 2 (update-nth 1446 65 (make-list 3494 :initial-element 0))))))
(defconst *pwzlt-model-st* (list '(8 0 16 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0)))

(local
 (defthm pwzlt-step-room-removal
   (let ((s *pwzlt-model-st*) (w *pwzlt-model-win*) (tab *pwzlt-model-tab*) (room 0))
     (and (not (posp room)) (equal (fn-zin-mode s) 8)
          (fn-zin-freshp s) (fn-zin-lit-ready-p s tab)
          (not (equal (fn-zin-step room s w tab nil)
                      (fn-pwz-action-sequence (car (fn-zin-lits room s w tab nil)) s w tab nil)))))
   :rule-classes nil))

(local
 (defthm pwzlt-step-mode-removal
   (let ((s (fn-zin-set 0 0 *pwzlt-model-st*)) (w *pwzlt-model-win*)
         (tab *pwzlt-model-tab*) (room 64))
     (and (posp room) (not (equal (fn-zin-mode s) 8))
          (fn-zin-freshp s) (fn-zin-lit-ready-p s tab)
          (not (equal (fn-zin-step room s w tab nil)
                      (fn-pwz-action-sequence (car (fn-zin-lits room s w tab nil)) s w tab nil)))))
   :rule-classes nil))

(local
 (defthm pwzlt-step-fresh-removal
   (let ((s (fn-zin-set 11 0 *pwzlt-model-st*)) (w *pwzlt-model-win*)
         (tab *pwzlt-model-tab*) (room 64))
     (and (posp room) (equal (fn-zin-mode s) 8)
          (not (fn-zin-freshp s)) (fn-zin-lit-ready-p s tab)
          (not (equal (fn-zin-step room s w tab nil)
                      (fn-pwz-action-sequence (car (fn-zin-lits room s w tab nil)) s w tab nil)))))
   :rule-classes nil))

(local
 (defthm pwzlt-step-ready-bomb-removal
   (let ((s (fn-zin-set 6 65536 *pwzlt-model-st*)) (w *pwzlt-model-win*)
         (tab *pwzlt-model-tab*) (room 64))
     (and (posp room) (equal (fn-zin-mode s) 8)
          (fn-zin-freshp s) (not (fn-zin-lit-ready-p s tab))
          (equal (fn-zin-tout s) (fn-zin-bomb-limit s))
          (not (equal (fn-zin-step room s w tab nil)
                      (fn-pwz-action-sequence (car (fn-zin-lits room s w tab nil)) s w tab nil)))))
   :rule-classes nil))

; Reach the scalar STEP branch through its actual basic scheduling caller.
; Five nine-bit fixed literals align the following eight-bit literal.
(defun pwzlt-reach-basic-ready (fuel ip fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel)
          (and (equal (fn-zin-mode fn-zin-st) 8) (fn-zin-freshp fn-zin-st)
               (fn-zin-lit-ready-p fn-zin-st fn-zin-tab)))
      (mv ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (mv-let (status b ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (fn-zin-loop 1 ip (fn-octets-len fn-octets) 64 fn-zin-st fn-octets
                   fn-zin-win fn-zin-tab fn-zin-out)
      (declare (ignore status b))
      (pwzlt-reach-basic-ready (1- fuel) ip fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))

(local
 (defthm pwzlt-actual-basic-literal-step-reachable
   (let* ((init (fn-pzw-initialize nil (create-fn-zin-st) nil nil nil))
          (reach (pwzlt-reach-basic-ready 32 0 (car init) '(59 113 226 196 137 19 142 0)
                                    (mv-nth 1 init) (mv-nth 2 init) (mv-nth 3 init)))
          (s (mv-nth 1 reach)) (w (mv-nth 2 reach))
          (tab (mv-nth 3 reach)) (out (mv-nth 4 reach)))
     (and (posp 64) (equal (fn-zin-mode s) 8) (fn-zin-freshp s)
          (fn-zin-lit-ready-p s tab)
          (equal (fn-zin-step 64 s w tab out)
                 (fn-pwz-action-sequence (car (fn-zin-lits 64 s w tab out)) s w tab out))))
   :rule-classes nil))
