(in-package "ACL2")
(include-book "../../books/decoded-window-read")
(include-book "../../books/decoded-window-lease")

; Source witness uses the exact buffer carried through this actual driver.
; It does not quantify over arbitrary native buffers or prove root/view binding.
(defun pwzrt-observe (ledger worker token z fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer :verify-guards nil))
  (let* ((returned (mv-list 3 (fn-pwx-return ledger worker token)))
         (w (nth 1 returned)) (l (nth 2 returned))
         (cancelled (mv-list 3 (fn-pwx-cancel l w token)))
         (released (mv-list 3 (fn-pwx-release l w token))))
    (list
      (fn-pwx-boundp ledger worker token :running)
      (fn-pwz-plan-matches-token z token)
      (fn-ewz-publication z)
      (fn-pwz-outcome ledger worker token z)
      (car returned)
      (equal (fn-prl-nth 1 l) (fn-prl-nth 1 ledger))
      (fn-pwz-outcome l w token z)
      (mv-list 2 (fn-pwz-byte-at l w token z 7 100 9 102 6
                               (fn-pwz-nth 8 token) 251 0 250 fn-ew-buffer))
      (mv-list 2 (fn-pwz-byte-at l (update-nth 1 (+ 1 (fn-prl-nth 1 w)) w)
                               token z 7 100 9 102 6 (fn-pwz-nth 8 token)
                               251 0 250 fn-ew-buffer))
      (mv-list 2 (fn-pwz-byte-at l w (update-nth 9 252 token) z
                               7 100 9 102 6 (fn-pwz-nth 8 token)
                               251 0 250 fn-ew-buffer))
      (mv-list 2 (fn-pwz-byte-at l w token z 7 100 9 102 6
                               (+ 1 (fn-pwz-nth 8 token)) 251 0 250 fn-ew-buffer))
      (mv-list 2 (fn-pwz-byte-at l w token z 7 100 9 102 6
                               (fn-pwz-nth 8 token) 251 1 250 fn-ew-buffer))
      (mv-list 2 (fn-pwz-byte-at (nth 2 cancelled) (nth 1 cancelled) token z
                               7 100 9 102 6 (fn-pwz-nth 8 token)
                               251 0 250 fn-ew-buffer))
      (car released)
      (mv-list 2 (fn-pwz-byte-at (nth 2 released) (nth 1 released) token z
                               7 100 9 102 6 (fn-pwz-nth 8 token)
                               251 0 250 fn-ew-buffer)))))

(defun pwzrt-run (fuel archive ledger worker token z reads codec-ticks pgs-digest-state fn-octets fn-ew-buffer
                      fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :verify-guards nil :measure (nfix fuel)
                  :stobjs (pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  (let ((action (fn-ewz-next-action z pgs-digest-state)))
    (cond ((zp fuel)
           (mv (list :fuel z reads codec-ticks) pgs-digest-state fn-octets fn-ew-buffer
               fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
          ((member-eq (car action) '(:ready :refused))
           (mv (list action reads codec-ticks (fn-zin-tout fn-zin-st)
                     (if (eq (car action) :ready)
                         (pwzrt-observe ledger worker token z fn-ew-buffer) nil))
               pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
          ((eq (car action) :codec)
           (mv-let (status z fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
             (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
             (declare (ignore status))
             (pwzrt-run (1- fuel) archive ledger worker token z reads (1+ codec-ticks)
                       pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
          ((eq (car action) :read)
           (let* ((effect (cadr action))
                  (bytes (fn-b3-firstn (nth 5 effect)
                             (fn-b3-nthcdrx (- (nth 4 effect) 100) archive)))
                  (fn-octets (fn-octets-from-list bytes fn-octets)))
             (mv-let (status z pgs-digest-state fn-ew-buffer)
               (fn-ewz-read effect :ok z fn-octets pgs-digest-state fn-ew-buffer)
               (declare (ignore status))
               (pwzrt-run (1- fuel) archive ledger worker token z (+ reads (len bytes)) codec-ticks
                         pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
          (t
           (mv-let (status z pgs-digest-state)
             (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)
             (declare (ignore status))
             (pwzrt-run (1- fuel) archive ledger worker token z reads codec-ticks
                       pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))))

(defun pwzrt-example (archive token ledger worker)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-digest-state
    (mv-let (answer pgs-digest-state)
    (with-local-stobj fn-octets
      (mv-let (answer fn-octets pgs-digest-state)
      (with-local-stobj fn-ew-buffer
        (mv-let (answer fn-ew-buffer fn-octets pgs-digest-state)
        (with-local-stobj fn-zin-st
          (mv-let (answer fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)
          (with-local-stobj fn-zin-win
            (mv-let (answer fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)
            (with-local-stobj fn-zin-tab
              (mv-let (answer fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)
              (with-local-stobj fn-zin-out
                (mv-let (answer fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)
                  (mv-let (z pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                    (fn-pwz-begin token 301 pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                    (mv-let (answer pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                      (pwzrt-run 100000 archive ledger worker token z 0 0 pgs-digest-state fn-octets fn-ew-buffer
                                fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                      (mv answer fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
                (mv answer fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
              (mv answer fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
            (mv answer fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
          (mv answer fn-ew-buffer fn-octets pgs-digest-state)))
        (mv answer fn-octets pgs-digest-state)))
      (mv answer pgs-digest-state)))
    answer)))
; Actual supplied-demand issuer -> shared acquire -> typed initialization ->
; authenticated bounded decoding -> actual-return observation -> scalar borrow.
; Demand is a kernel witness, not selected-runtime codec adequacy.
(assert-event
 (let* ((c '(115 116 28 177 0 0)) (msg (append '(9 8) c '(7)))
        (digest (fn-blake3 msg)) (trailer (fn-bch-pack digest))
        (whole (fn-pzd-decode nil c 251))
        (baseline (mv-nth 1 (mv-list 2 (fn-prl-make-baseline '(10000 0 2 1 20) '(1000 0 0 0 0)))))
        (registered (mv-nth 1 (mv-list 2 (fn-prl-register baseline 7 '(64 0 1 0 0)))))
        (admitted (mv-list 3 (fn-pwz-admit registered (list 7 100 9 102 6 0 trailer 251 0) '(256 0 0 1 1))))
        (token (nth 1 admitted))
        (acquired (mv-list 3 (fn-pwx-acquire (nth 2 admitted) (fn-pxe-new 0) token)))
        (answer (pwzrt-example (append msg digest) token (nth 2 acquired) (nth 1 acquired)))
        (observed (nth 4 answer)))
   (and (equal (car admitted) :admitted) (fn-pwz-tokenp token)
        (equal (car acquired) :assigned)
        (equal (car (car answer)) :ready) (< 1 (nth 2 answer))
        (equal (nth 3 answer) 251)
        (equal (car whole) :ok) (equal (len (cadr whole)) 251)
        (equal (nth 7 observed) (list :byte (nth 250 (cadr whole))))
        (equal observed
          (list t t (list (fn-pwz-nth 1 token) 301 token :decoded 0 251)
                :stale-job :returned t :ready '(:byte 65)
                '(:stale-job nil) '(:stale-job nil) '(:unavailable nil)
                '(:unavailable nil) '(:cancelled nil) :released '(:stale-job nil))))))
