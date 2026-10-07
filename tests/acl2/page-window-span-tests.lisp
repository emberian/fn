(in-package "ACL2")
(include-book "../../books/page-window-span")
(include-book "page-window-read-tests")

; The span borrow's teeth, over the same actual authenticated stream the
; scalar borrow's witnesses use (pwrtest-ready: message 1 2 3 and its digest).

(defun-nx pwspan-ctx ()
  (let* ((r (pwrtest-ready)) (token (nth 0 r)) (returned (nth 2 r))
         (run (nth 3 r)) (s (nth 1 run)) (buffer (nth 3 run)))
    (list token (nth 2 returned) (nth 1 returned) s buffer)))

; REACHABLE POSITIVE: the span [1,3) answers, and each of its octets is the
; scalar borrow of its own coordinate (keystone fn-pwr-span-is-the-borrowed-bytes).
(defun-nx pwspan-positive ()
  (let* ((c (pwspan-ctx)) (token (nth 0 c)) (ledger (nth 1 c)) (worker (nth 2 c))
         (s (nth 3 c)) (buffer (nth 4 c))
         (r (fn-pwr-span ledger worker token s 1 3 buffer (create-fn-ew-span))))
    (and (equal (nth 0 r) :span)
         (equal (nth 0 (nth 1 r)) (list* 2 3 (nthcdr 2 (nth 0 (nth 1 r)))))
         (equal (fn-pwr-byte ledger worker token s 1 buffer) (list :byte (nth 0 (nth 0 (nth 1 r)))))
         (< 2 (nth 5 s)))))
(defthm pwspan-positive-witness (pwspan-positive) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-span fn-pwr-span-copy fn-pwr-byte
                                     fn-pwr-plan-matches-token))))

; REMOVAL, one per hypothesis of the keystone.  Each removes exactly one and the
; span refuses by name, leaves the buffer as it was, and the scalar refuses too.
(defun-nx pwspan-refuses (ledger worker token s i j buffer)
  (let ((r (fn-pwr-span ledger worker token s i j buffer (create-fn-ew-span))))
    (and (equal (nth 0 r) :unavailable)
         (equal (nth 1 r) (create-fn-ew-span))
         (or (not (equal (nth 0 (fn-pwr-byte ledger worker token s i buffer)) :byte))
             (not (equal (nth 0 (fn-pwr-byte ledger worker token s (- j 1) buffer)) :byte))))))

; ledger: the job is acquired, not returned.
(defun-nx pwspan-removal-boundp ()
  (let* ((r (pwrtest-ready)) (token (nth 0 r)) (acquire (nth 1 r)) (run (nth 3 r)))
    (pwspan-refuses (nth 2 acquire) (nth 1 acquire) token (nth 1 run) 1 3 (nth 3 run))))
; plan: not this token's.
(defun-nx pwspan-removal-plan ()
  (let ((c (pwspan-ctx)))
    (pwspan-refuses (nth 1 c) (nth 2 c) (nth 0 c) (update-nth 8 'other (nth 3 c)) 1 3 (nth 4 c))))
; publication: the plan has not published.
(defun-nx pwspan-removal-publication ()
  (let ((c (pwspan-ctx)))
    (pwspan-refuses (nth 1 c) (nth 2 c) (nth 0 c) (update-nth 0 :scan (nth 3 c)) 1 3 (nth 4 c))))
; bound: the span runs past the window.
(defun-nx pwspan-removal-bound ()
  (let ((c (pwspan-ctx)))
    (pwspan-refuses (nth 1 c) (nth 2 c) (nth 0 c) (nth 3 c) 1 (+ 1 (nth 5 (nth 3 c))) (nth 4 c))))

(defthm pwspan-removal-boundp-witness (pwspan-removal-boundp) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-span fn-pwr-byte fn-pwr-plan-matches-token))))
(defthm pwspan-removal-plan-witness (pwspan-removal-plan) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-span fn-pwr-byte fn-pwr-plan-matches-token))))
(defthm pwspan-removal-publication-witness (pwspan-removal-publication) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-span fn-pwr-byte fn-pwr-plan-matches-token fn-ewp-publication))))
(defthm pwspan-removal-bound-witness (pwspan-removal-bound) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-span fn-pwr-byte fn-pwr-plan-matches-token))))

; Payload coordinates: the original descriptor must match (a different poff refuses),
; and the first covered octet is the scalar's (payload 1 -> window 0 here).
(defun-nx pwspan-at-witness ()
  (let* ((digest (fn-blake3 '(1 2 3)))
         (r (pwrtest-request 1 (fn-bch-pack digest) (append '(1 2 3) digest)))
         (token (nth 0 r)) (returned (nth 2 r)) (run (nth 3 r))
         (s (nth 1 run)) (buffer (nth 3 run))
         (ledger (nth 2 returned)) (worker (nth 1 returned))
         (ok (fn-pwr-span-at ledger worker token s 11 100 3 100 3 (fn-bch-pack digest) 1 3
                             buffer (create-fn-ew-span)))
         (bad (fn-pwr-span-at ledger worker token s 11 100 3 101 2 (fn-bch-pack digest) 1 3
                              buffer (create-fn-ew-span)))
         (early (fn-pwr-span-at ledger worker token s 11 100 3 100 3 (fn-bch-pack digest) 0 2
                                buffer (create-fn-ew-span))))
    (and (equal (nth 0 ok) :span)
         (equal (nth 0 (fn-pwr-byte-at ledger worker token s 11 100 3 100 3 (fn-bch-pack digest) 1 buffer))
                :byte)
         (equal (nth 0 bad) :unavailable)
         (equal (nth 0 early) :unavailable))))
(defthm pwspan-at-witness-holds (pwspan-at-witness) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-span-at fn-pwr-span fn-pwr-span-copy fn-pwr-byte-at
                                     fn-pwr-byte fn-pwr-outcome fn-pwr-plan-matches-token))))

; Teeth of fn-pwr-byte-at-below-the-window-is-the-outcome (row 21).  A window
; starting at payload coordinate 2: coordinates 0 and 1 are refused with ONE
; word (:unavailable, the job being :ready); the coordinate AT the start is a
; byte, so the independence of the word from the coordinate needs `i < start`;
; and against the same token and a ledger that has the job running (not
; returned) the word below the window is the outcome, :stale-job, not
; :unavailable, so the conclusion's `if` is not decorative.
(defun-nx pwspan-below-witness ()
  (let* ((digest (fn-blake3 '(1 2 3)))
         (r (pwrtest-request 2 (fn-bch-pack digest) (append '(1 2 3) digest)))
         (token (nth 0 r)) (acquire (nth 1 r)) (returned (nth 2 r)) (run (nth 3 r))
         (s (nth 1 run)) (buffer (nth 3 run))
         (ledger (nth 2 returned)) (worker (nth 1 returned))
         (w0 (nth 0 (fn-pwr-byte-at ledger worker token s 11 100 3 100 3 (fn-bch-pack digest) 0 buffer)))
         (w1 (nth 0 (fn-pwr-byte-at ledger worker token s 11 100 3 100 3 (fn-bch-pack digest) 1 buffer)))
         (w2 (nth 0 (fn-pwr-byte-at ledger worker token s 11 100 3 100 3 (fn-bch-pack digest) 2 buffer)))
         (running (nth 0 (fn-pwr-byte-at (nth 2 acquire) (nth 1 acquire) token s
                                         11 100 3 100 3 (fn-bch-pack digest) 0 buffer))))
    (and (equal w0 :unavailable) (equal w1 :unavailable)
         (equal w2 :byte)
         (equal running :stale-job))))
(defthm pwspan-below-witness-holds (pwspan-below-witness) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-byte-at fn-pwr-byte fn-pwr-outcome
                                     fn-pwr-plan-matches-token))))
