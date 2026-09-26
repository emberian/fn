; Witnesses and teeth for books/byte-store-marker-candidates: the three
; cheaper marker programs and what refuses each.  The byte witnesses run on
; the K5 fixture's second publication at its completing pair (as
; byte-store-k0-marker-tests does): two records durable, the kernel
; :completing sequence 1, the marker frame the host writes for sequence 1.
(in-package "ACL2")
(include-book "../../books/byte-store-marker-candidates")
(include-book "byte-store-k0-marker-tests")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Candidate 1, the unfenced stage.  A crash after the root barrier: the
; entry landed (the barrier drained it), the content is a pending write of an
; unfenced inode, and the model lets that unit land as any octets.

(defun bsmc-unfenced-run (bs ks stage octets)
  (fn-bs-run bs ks (fn-bs-marker-unfenced-program stage octets) nil *bsk5-groups* *bsk5-capacity*))
; Choices: every pending operation lands, and the one write of INO lands as
; the garble G, one selector per write unit (the fixture's unit is 4 octets,
; so the frame spans eleven); the i-th selector carries G from its i-th
; unit, since fn-bs-tear-write slices each selector's octets from their
; start.
(defun bsmc-garble-selectors (n start g unit)
  (if (zp n) nil
    (cons (cons :garble (nthcdr start g))
          (bsmc-garble-selectors (1- n) (+ start unit) g unit))))
(defun bsmc-garble-choices (ops ino g unit)
  (if (atom ops) nil
    (cons (cond ((and (equal (car (car ops)) :write) (equal (nth 1 (car ops)) ino))
                 (bsmc-garble-selectors
                  (fn-bs-unit-count (nth 2 (car ops)) (len (nth 3 (car ops))) unit)
                  0 g unit))
                ((equal (car (car ops)) :write)
                 (fn-bs-all-new (fn-bs-unit-count (nth 2 (car ops)) (len (nth 3 (car ops))) unit)))
                (t :apply))
          (bsmc-garble-choices (cdr ops) ino g unit))))
(defun bsmc-garbled-obs (b ino g)
  (fn-bs-hm-observation (fn-bs-crash b (bsmc-garble-choices (fn-bs-pending b) ino g (fn-bs-unit b)))))
; A garble that spells a valid marker of count 23 (the same frame length as
; count 2: both counts are one CBOR octet), and one that spells nothing.
(defconst *bsmc-junk* (make-list 64 :initial-element 255))

(assert-event
 (let* ((bs (car (bskm-pair))) (ks (cdr (bskm-pair)))
        (new (fn-hm-after-commit 1))
        (run (bsmc-unfenced-run bs ks ".stage-marker-u" new))
        (b (car (nth 7 run)))                 ; after the root barrier
        (ino (fn-bs-durable-entry b :root *fn-bs-history-marker-name*))
        (spelled (fn-hm-after-commit 22)))
   (and (fn-bs-store-relation bs ks)
        (fn-bs-marker-inputp bs ".stage-marker-u")
        (equal (len run) 8)
        (equal (fn-bs-hm-observation bs) '(:absent))
        (fn-bs-inop ino)
        (not (fn-bs-fencedp b ino))          ; the content was never fenced
        (equal (len spelled) (len new))
        (< 1 (fn-bs-unit-count 0 (len new) (fn-bs-unit b)))   ; several units
        ; the choices are admissible
        (fn-bs-crash-choicesp (bsmc-garble-choices (fn-bs-pending b) ino spelled (fn-bs-unit b))
                              (fn-bs-pending b) (fn-bs-unit b))
        (fn-bs-crash-choicesp (bsmc-garble-choices (fn-bs-pending b) ino *bsmc-junk* (fn-bs-unit b))
                              (fn-bs-pending b) (fn-bs-unit b))
        ; the crash image's marker is neither the old one nor the new one
        (equal (bsmc-garbled-obs b ino spelled) (list :present spelled))
        (not (member-equal (bsmc-garbled-obs b ino spelled)
                           (list (fn-bs-hm-observation bs) (list :present new))))
        ; and the open of a store that lost nothing (two records) refuses,
        ; either by the count the garble spells or as damage
        (equal (fn-hm-open-verdict (bsmc-garbled-obs b ino spelled) 2)
               '(:refused :history-short-of-marker 23))
        (equal (fn-hm-open-verdict (bsmc-garbled-obs b ino *bsmc-junk*) 2)
               '(:refused :marker-damaged))
        (not (fn-hm-admittedp (cons 2 (bsmc-garbled-obs b ino spelled))))
        ; the served program's image at the same cut is the new marker
        (equal (bskm-obs (bskm-good) 9 nil) (list :present new)))))

; -----------------------------------------------------------------------------
; Candidate 2, one overwrite in place, from the served program's durable
; state (count 2 present and fenced).  A crash at marker-written: the
; overwrite is a pending write of a fenced inode, and its unit may land as
; any octets.

(defun bsmc-in-place-run (bs ks octets)
  (fn-bs-run bs ks (fn-bs-marker-in-place-program octets) nil *bsk5-groups* *bsk5-capacity*))

(assert-event
 (let* ((bs (car (nth 9 (bskm-good)))) (ks (cdr (nth 9 (bskm-good))))
        (old (fn-hm-after-commit 1)) (new (fn-hm-after-commit 2))
        (run (bsmc-in-place-run bs ks new))
        (b (car (nth 1 run)))                 ; marker-written
        (ino (fn-bs-durable-entry bs :root *fn-bs-history-marker-name*))
        (spelled (fn-hm-after-commit 22)))
   (and (equal (fn-bs-hm-observation bs) (list :present old))
        (fn-bs-fencedp bs ino)
        (equal (len run) 4)
        (mv-let (r b1 k1)
          (fn-bs-step bs ks (car (fn-bs-marker-in-place-program new)) :ok
                      *bsk5-groups* *bsk5-capacity*)
          (declare (ignore b1 k1))
          (equal r :ok))                     ; the overwrite is accepted
        (not (fn-bs-fencedp b ino))          ; the overwrite is pending
        (equal (len spelled) (len new))
        (fn-bs-crash-choicesp (bsmc-garble-choices (fn-bs-pending b) ino spelled (fn-bs-unit b))
                              (fn-bs-pending b) (fn-bs-unit b))
        (equal (bsmc-garbled-obs b ino spelled) (list :present spelled))
        (equal (fn-hm-open-verdict (bsmc-garbled-obs b ino spelled) 2)
               '(:refused :history-short-of-marker 23))
        (equal (fn-hm-open-verdict (bsmc-garbled-obs b ino *bsmc-junk*) 2)
               '(:refused :marker-damaged))
        ; after its one fence the image is the new marker: the barrier is
        ; not the problem, the window before it is
        (equal (fn-bs-hm-observation (fn-bs-crash (car (nth 3 run)) nil)) (list :present new)))))

; -----------------------------------------------------------------------------
; Candidate 3, the deferred marker.  A reachable state: a fresh unmarked
; store, its first open (the catch-up writes count 0 and the process is
; live), one acknowledged commit, then the deferred commit.

; The development preset (format 8, `unmarked'), as store-history-required-tests.
; The states that hold a marker frame are zero-ary functions, not constants:
; a defconst is evaluated without the SHA-256 attachment.
(defconst *bsmc-unmarked* *fn-bs-profile-development*)
(assert-event (not (fn-bs-profile-marker-requiredp *bsmc-unmarked*)))
(defconst *bsmc-st0* (fn-hmr-state 0 '(:absent) 0 *bsmc-unmarked* nil))
(defun bsmc-live ()
  (fn-hmr-run '((:open :marker-durable nil) (:commit :marker-durable nil)) *bsmc-st0*))
(assert-event (and (fn-hmr-invp *bsmc-st0*) (fn-hmr-invp (bsmc-live))
                   (equal (fn-hmr-count (bsmc-live)) 1) (nth 4 (bsmc-live))
                   (equal (nfix (nth 2 (bsmc-live))) 1)
                   (equal (fn-hmr-marker-count (nth 1 (bsmc-live))) 1)))
(defun bsmc-deferred () (fn-hmr-deferred-commit (bsmc-live)))

; The positive witness of the three theorems: every hypothesis, every
; conclusion.  Record 1 is answered (A = 2) over a marker that counts 1; the
; open at one record admits; the catch-up writes nothing.
(assert-event
 (let ((live (bsmc-live)) (end (bsmc-deferred)))
   (and (fn-hmr-invp live) (nth 4 live)
        (not (fn-hmr-invp end))
        (equal (fn-hmr-count end) 2)
        (equal (nfix (nth 2 end)) 2)
        (equal (fn-hmr-marker-count (nth 1 end)) 1)
        (< 1 (nfix (nth 2 end)))
        (equal (fn-hmr-open-verdict (nth 3 end) (nth 1 end) 1) '(:admitted :marked 1))
        (equal (fn-hmr-catch-up (nth 3 end) (nth 1 end) 1) nil)
        ; the served step at the same point keeps the invariant and refuses
        ; the same open
        (let ((served (fn-hmr-step '(:commit :marker-durable nil) live)))
          (and (fn-hmr-invp served)
               (equal (fn-hmr-open-verdict (nth 3 served) (nth 1 served) 1)
                      '(:refused :history-short-of-marker 2)))))))

; Teeth.  Each hypothesis removed with every other retained and the
; conclusion, evaluated, false.
;   live: a state that is not live does not answer; the step is the identity
;   and the invariant holds (leaves-the-invariant), K is not below A
;   (admits-a-lost-answered-record), and a marker behind the history is
;   caught up (is-not-caught-up).
(defun bsmc-rest ()
  (fn-hmr-run '((:open :marker-durable nil) (:commit :marker-durable nil)
                (:commit :marker-created nil))
              *bsmc-st0*))
(assert-event (and (fn-hmr-invp (bsmc-rest)) (not (nth 4 (bsmc-rest)))
                   (equal (fn-hmr-count (bsmc-rest)) 2)
                   (equal (fn-hmr-marker-count (nth 1 (bsmc-rest))) 1)
                   (equal (fn-hmr-deferred-commit (bsmc-rest)) (bsmc-rest))))
(must-fail (assert-event (not (fn-hmr-invp (fn-hmr-deferred-commit (bsmc-rest))))))
(must-fail (assert-event (< (fn-hmr-count (bsmc-rest))
                            (nfix (nth 2 (fn-hmr-deferred-commit (bsmc-rest)))))))
(must-fail (assert-event (equal (fn-hmr-catch-up (nth 3 (fn-hmr-deferred-commit (bsmc-rest)))
                                                 (nth 1 (fn-hmr-deferred-commit (bsmc-rest)))
                                                 (fn-hmr-count (bsmc-rest)))
                                nil)))
;   the invariant (corrupted-state witnesses): a live process over a marker
;   ABOVE the history (M = D + 1, the open refuses it) makes the deferred
;   step land exactly on the invariant, and K is below A but the open at K
;   refuses; a live process over a marker BEHIND the history (an open that
;   skipped the catch-up) is caught up.
(defun bsmc-above ()
  (fn-hmr-state 1 (list :present (fn-hm-after-commit 1)) 1 *bsmc-unmarked* t))
(assert-event (and (not (fn-hmr-invp (bsmc-above))) (nth 4 (bsmc-above))))
(must-fail (assert-event (not (fn-hmr-invp (fn-hmr-deferred-commit (bsmc-above))))))
(must-fail (assert-event (equal (fn-hmr-open-verdict (nth 3 (fn-hmr-deferred-commit (bsmc-above)))
                                                     (nth 1 (fn-hmr-deferred-commit (bsmc-above)))
                                                     1)
                                '(:admitted :marked 1))))
(defun bsmc-behind ()
  (fn-hmr-state 2 (list :present (fn-hm-after-commit 0)) 1 *bsmc-unmarked* t))
(assert-event (and (not (fn-hmr-invp (bsmc-behind))) (nth 4 (bsmc-behind))))
(must-fail (assert-event (equal (fn-hmr-catch-up (nth 3 (fn-hmr-deferred-commit (bsmc-behind)))
                                                 (nth 1 (fn-hmr-deferred-commit (bsmc-behind)))
                                                 (fn-hmr-count (bsmc-behind)))
                                nil)))
