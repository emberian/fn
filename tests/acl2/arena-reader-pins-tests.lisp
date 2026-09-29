; Teeth for books/arena-reader-pins.lisp (PRF-941, lane composed-owner-5):
; KEYSTONE fn-arpn-release-postdates-every-live-pin on the host's call,
; fn-arpn-step (host/native/io.lisp fnn-arena-pins-step), over a reached
; state.

(in-package "ACL2")
(include-book "../../books/arena-reader-pins")
(include-book "must-fail-checked")

;; The host's events in order: (list FINAL-STATE ANSWERS).
(defun arpnt-run (st evs)
  (declare (xargs :guard (fn-arpn-okp st)
                  :verify-guards nil))
  (if (atom evs)
      (list st nil)
    (mv-let (st2 ans) (fn-arpn-step st (car evs))
      (let ((rest (arpnt-run st2 (cdr evs))))
        (list (first rest) (cons ans (second rest)))))))

;; One step as a list (ST' ANSWER), for the evaluated checks.
(defun arpnt-step (st ev)
  (declare (xargs :guard (fn-arpn-okp st)))
  (mv-list 2 (fn-arpn-step st ev)))

; Reader A pins generation 0; the reseat of handle 11 is retired (stamp 0);
; reader B pins generation 1; the reseat of handle 12 is retired (stamp 1);
; A ends.  B is still running.
(defconst *arpnt-events*
  '((:pin) (:retire (11)) (:pin) (:retire (12)) (:unpin 0)))

(defconst *arpnt-st* (first (arpnt-run (fn-arpn-initial) *arpnt-events*)))

(assert-event (equal (second (arpnt-run (fn-arpn-initial) *arpnt-events*))
                     '(0 0 1 1 :ok)))
(assert-event (equal *arpnt-st* '(2 ((1 . 1)) ((1 12) (0 11)))))
(assert-event (fn-arpn-okp *arpnt-st*))

; The release: handle 11's retirement (stamp 0) goes, although reader B
; runs -- B pinned after it; handle 12's (stamp 1) waits for B.  (The
; single count this generalizes released neither.)
(assert-event
 (equal (arpnt-step *arpnt-st* '(:release))
        '((2 ((1 . 1)) ((1 12))) ((0 11)))))
(assert-event (equal (second (arpnt-step *arpnt-st* '(:clear 0))) t))
(assert-event (equal (second (arpnt-step *arpnt-st* '(:clear 1))) nil))
(assert-event (equal (second (arpnt-step *arpnt-st* '(:clear-except 1 1))) t))
(assert-event (equal (second (arpnt-step *arpnt-st* '(:count))) 1))
(assert-event (equal (second (arpnt-step *arpnt-st* '(:unpin 0))) :refused))

; B ends: handle 12's retirement goes too.
(assert-event
 (equal (second (arpnt-step (first (arpnt-step *arpnt-st* '(:unpin 1)))
                             '(:release)))
        '((1 12) (0 11))))

; REACHABLE POSITIVE WITNESS: the complete antecedent and the conclusion of
; the keystone, e = (0 11), h = 1 (reader B).
(defthm arpnt-release-positive
  (let ((r (fn-arpn-step *arpnt-st* '(:release))))
    (and (fn-arpn-okp *arpnt-st*)
         (member-equal '(0 11) (mv-nth 1 r))
         (< 0 (fn-arpn-pins-of 1 (second (mv-nth 0 r))))
         (member-equal '(0 11) (third *arpnt-st*))
         (< (car '(0 11)) 1)))
  :rule-classes nil)

; HYPOTHESIS-REMOVAL WITNESS, fn-arpn-okp omitted (CORRUPTED STATE): a pin
; table out of order ((5 . 1) before (1 . 1)).  The :release compares the
; stamp 3 with the first row only and answers (3 21); a reader is live at 1,
; below the stamp: the okp fails and so does the conclusion.
(defconst *arpnt-bad* '(5 ((5 . 1) (1 . 1)) ((3 21))))

(defthm arpnt-without-okp-corrupted-state
  (let ((r (fn-arpn-step *arpnt-bad* '(:release))))
    (and (not (fn-arpn-okp *arpnt-bad*))
         (member-equal '(3 21) (mv-nth 1 r))
         (< 0 (fn-arpn-pins-of 1 (second (mv-nth 0 r))))
         (member-equal '(3 21) (third *arpnt-bad*))
         (not (< (car '(3 21)) 1))))
  :rule-classes nil)

(local
 (must-fail-checked
  (with-prover-step-limit 50000
    (defthm arpnt-keystone-without-okp
      (implies (and (member-equal e (mv-nth 1 (fn-arpn-step st '(:release))))
                    (< 0 (fn-arpn-pins-of h (second (mv-nth 0 (fn-arpn-step st '(:release)))))))
               (and (member-equal e (third st))
                    (< (car e) h)))))))

; Without the released membership: (1 12) is pending, not released; reader B
; at 1 is live; the stamp 1 is not below it.
(defthm arpnt-without-released
  (let ((r (fn-arpn-step *arpnt-st* '(:release))))
    (and (fn-arpn-okp *arpnt-st*)
         (not (member-equal '(1 12) (mv-nth 1 r)))
         (< 0 (fn-arpn-pins-of 1 (second (mv-nth 0 r))))
         (not (< (car '(1 12)) 1))))
  :rule-classes nil)

(local
 (must-fail-checked
  (with-prover-step-limit 50000
    (defthm arpnt-keystone-without-released
      (implies (and (fn-arpn-okp st)
                    (< 0 (fn-arpn-pins-of h (second (mv-nth 0 (fn-arpn-step st '(:release)))))))
               (and (member-equal e (third st))
                    (< (car e) h)))))))

; Without the live pin: nobody is pinned at 0 (reader A ended); the released
; (0 11) is not below 0.
(defthm arpnt-without-live-pin
  (let ((r (fn-arpn-step *arpnt-st* '(:release))))
    (and (fn-arpn-okp *arpnt-st*)
         (member-equal '(0 11) (mv-nth 1 r))
         (not (< 0 (fn-arpn-pins-of 0 (second (mv-nth 0 r)))))
         (not (< (car '(0 11)) 0))))
  :rule-classes nil)

(local
 (must-fail-checked
  (with-prover-step-limit 50000
    (defthm arpnt-keystone-without-live-pin
      (implies (and (fn-arpn-okp st)
                    (member-equal e (mv-nth 1 (fn-arpn-step st '(:release)))))
               (and (member-equal e (third st))
                    (< (car e) h)))))))

; MUTATION: a release that answered every pending retirement (the old
; readers ignored) is not what the step does: (1 12) waits for reader B.
(local
 (must-fail-checked
  (with-prover-step-limit 50000
    (defthm arpnt-mutation-release-everything
      (implies (and (fn-arpn-okp st)
                    (member-equal e (third st)))
               (member-equal e (mv-nth 1 (fn-arpn-step st '(:release)))))))))
