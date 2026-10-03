; LIST status lookup retains the group string and configured octet tails.
; One accepted call enters one entry or compares one character. No group-sized
; string/octet conversion or full entry equality is performed in execution.
(in-package "ACL2")
(include-book "nntp-responses")
(include-book "def-cursor")

(local (in-theory (disable (tau-system))))

; Fields: remaining entries, group string, moderated receipt, phase,
; candidate tail, string offset, plain/closed entry flag, terminal status.
(defun fn-lss-make (tail group moderated phase candidate offset closedp status)
  (declare (xargs :guard t))
  (list tail group moderated phase candidate offset closedp status))

(defun fn-lss-start (group closed)
  (declare (xargs :guard t))
  (fn-lss-make closed group nil :entry nil 0 nil nil))

(local
 (defthm fn-lss-indexed-character
   (implies (and (stringp text) (natp k) (< k (length text)))
            (characterp (char text k)))
   :hints (("Goal" :use ((:instance character-listp-coerce (str text)))
            :in-theory (e/d (char length character-listp)
                            (character-listp-coerce))))))

(defun fn-lss-one (cur)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((tail (fn-cur-at 0 cur))
         (group (fn-cur-at 1 cur))
         (moderated (fn-cur-at 2 cur))
         (phase (fn-cur-at 3 cur))
         (candidate (fn-cur-at 4 cur))
         (offset (nfix (fn-cur-at 5 cur)))
         (closedp (fn-cur-at 6 cur)))
    (cond
     ((eq phase :done) cur)
     ((eq phase :entry)
      (if (consp tail)
          (let* ((entry (car tail))
                 (modp (fn-nntp-moderated-entryp entry)))
            (fn-lss-make (cdr tail) group moderated :match
                         (if modp (fn-cur-at 1 entry) entry) 0 (not modp) nil))
        (fn-lss-make nil group moderated :done nil 0 nil (if moderated "m" "y"))))
     ((eq phase :match)
      (if (and (stringp group) (< offset (length group)))
          (if (and (consp candidate)
                   (equal (char-code (char group offset)) (car candidate)))
              (fn-lss-make tail group moderated :match (cdr candidate)
                           (1+ offset) closedp nil)
            (fn-lss-make tail group moderated :entry nil 0 nil nil))
        (if (not candidate)
            (if closedp
                (fn-lss-make tail group moderated :done nil 0 nil "n")
              (fn-lss-make tail group t :entry nil 0 nil nil))
          (fn-lss-make tail group moderated :entry nil 0 nil nil))))
     (t (fn-lss-make nil group nil :done nil 0 nil "y")))))

(verify-guards fn-lss-one
  :hints (("Goal" :in-theory
           (union-theories '(nfix natp length fn-lss-indexed-character
                             (:type-prescription len))
                           (theory 'minimal-theory)))))

(defun fn-lss-donep (cur)
  (declare (xargs :guard t))
  (eq (fn-cur-at 3 cur) :done))

(defun fn-lss-status (cur)
  (declare (xargs :guard t))
  (fn-cur-at 7 cur))

(defthm fn-lss-one-fixed-envelope
  (implies (not (fn-lss-donep cur)) (equal (len (fn-lss-one cur)) 8))
  :hints (("Goal" :in-theory
           (union-theories '(fn-lss-one fn-lss-make fn-lss-donep
                             len car-cons cdr-cons zp)
                           (theory 'minimal-theory)))))

(defthm fn-lss-done-is-unchanged
  (implies (fn-lss-donep cur) (equal (fn-lss-one cur) cur))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-lss-donep fn-lss-one) (theory 'minimal-theory)))))

(in-theory (disable fn-lss-make fn-lss-start fn-lss-one fn-lss-donep fn-lss-status))
