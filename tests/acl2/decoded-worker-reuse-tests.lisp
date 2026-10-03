; PRF-1298: actual acquisition/return/retirement/reassignment, no invented
; completion token. Corrupted carry mutations are labelled separately.
(in-package "ACL2")
(include-book "../../books/decoded-worker-job")

(defun-nx fn-dwrt-running ()
  (let* ((ledger (mv-nth 1 (fn-prl-register
                           (fn-prl-make '(200000 0 2 1 20)) 7 '(64 0 1 0 0))))
         (admitted (fn-pwz-admit ledger '(7 100 320 120 40 200 99 250 0)
                                 '(86928 0 0 1 1)))
         (token (nth 1 admitted))
         (acquired (fn-pwx-acquire (nth 2 admitted) (fn-pxe-new 0) token))
         (carry (mv-nth 1 (fn-dwa-assign (nth 2 acquired) (nth 1 acquired)
                                        token token 47 (create-fn-pww-carry)))))
    (list (nth 2 acquired) (nth 1 acquired) token carry)))
(defun-nx fn-dwrt-returned (cancelp)
  (let* ((r (fn-dwrt-running))
         (cancel (if cancelp (fn-pwx-cancel (nth 0 r) (nth 1 r) (nth 2 r))
                   (list :unchanged (nth 1 r) (nth 0 r))))
         (returned (fn-pwx-return (nth 2 cancel) (nth 1 cancel) (nth 2 r))))
    (list (nth 2 returned) (nth 1 returned) (nth 2 r) (nth 3 r))))
(defun-nx fn-dwrt-retired (cancelp)
  (let ((r (fn-dwrt-returned cancelp)))
    (fn-dwa-retire (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r))))

(defthm fn-dwrt-returned-positive
 (let* ((r (fn-dwrt-returned nil)) (retired (fn-dwrt-retired nil)))
  (and (fn-pwx-boundp (nth 0 r) (nth 1 r) (nth 2 r) :returned)
       (equal (car retired) :reusable)
       (equal (cadr retired) (create-fn-pww-carry))
       (equal (fn-dwa-retire (nth 0 r) (nth 1 r) (nth 2 r) (cadr retired))
              (list :decoded-retirement-unavailable (cadr retired)))))
 :rule-classes nil)
(defthm fn-dwrt-cancelled-positive
 (let ((r (fn-dwrt-returned t)))
  (and (fn-pwx-boundp (nth 0 r) (nth 1 r) (nth 2 r) :cancelled-returned)
       (equal (car (fn-dwrt-retired t)) :reusable)))
 :rule-classes nil)
; Physical running state does not authorize recycling.
(defthm fn-dwrt-running-refusal
 (let ((r (fn-dwrt-running)))
  (and (fn-pwx-boundp (nth 0 r) (nth 1 r) (nth 2 r) :running)
       (equal (fn-dwa-retire (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r))
              (list :decoded-retirement-unavailable (nth 3 r)))))
 :rule-classes nil)
; MUTATION: pending read, torn intermediate phase, and wrong token all refuse.
(defthm fn-dwrt-corrupted-carry-refusal
 (let* ((r (fn-dwrt-returned nil)) (c (nth 3 r)))
  (and
   (equal (car (fn-dwa-retire (nth 0 r) (nth 1 r) (nth 2 r)
                 (update-fn-pww-pending-action '(:read) c))) :decoded-retirement-unavailable)
   (equal (car (fn-dwa-retire (nth 0 r) (nth 1 r) (nth 2 r)
                 (update-fn-pww-phase :codec-acting c))) :decoded-retirement-unavailable)
   (equal (car (fn-dwa-retire (nth 0 r) (nth 1 r) nil c)) :decoded-retirement-unavailable)))
 :rule-classes nil)
; Release the previous token, acquire its successor, and assign the SAME carry.
(defthm fn-dwrt-reassignment
 (let* ((r (fn-dwrt-returned nil))
        (carry (cadr (fn-dwrt-retired nil)))
        (release (fn-pwx-release (nth 0 r) (nth 1 r) (nth 2 r)))
        (admit (fn-pwz-admit (nth 2 release) '(7 100 320 120 40 200 99 250 0)
                             '(86928 0 0 1 1)))
        (token (nth 1 admit))
        (acquire (fn-pwx-acquire (nth 2 admit) (nth 1 release) token))
        (assign (fn-dwa-assign (nth 2 acquire) (nth 1 acquire) token token 48 carry)))
   (and (equal (car release) :released)
        (equal (car acquire) :assigned)
        (not (equal token (nth 2 r)))
        (equal (car assign) :decoded-assigned)
        (equal (fn-pww-token (cadr assign)) token)
        (equal (fn-pww-source-incarnation (cadr assign)) 48)
        (null (fn-pww-controller (cadr assign)))))
 :rule-classes nil)
