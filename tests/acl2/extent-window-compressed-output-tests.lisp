(in-package "ACL2")
(include-book "../../books/extent-window-compressed-output")
(include-book "extent-window-compressed-input-tests")
(include-book "extent-window-compressed-refinement-tests")

; Actual private pools, no huge logical ground-state term.
(defun ewzot-transition-checks (operation corrupt bad-coordinate)
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
 (let* ((c (if (eq operation :hash) nil '(1 3 0 252 255 65 66 67)))
             (prefix '(9 8 7)) (protected (append prefix c))
             (archive (append protected (fn-blake3 protected)))
             (poff (if bad-coordinate 201/2 103)))
 (mv-let (z pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
   (fn-ewz-begin 7 100 (len protected) poff (len c) (if (eq operation :hash) 0 3) 0
                 23 47 59 (fn-bch-pack (fn-blake3 protected)) nil
                 pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (if (eq operation :begin)
   (mv (list (natp poff) (fn-ewz-output-invariantp z fn-zin-st)
             (equal (nth 0 z) :scan)) fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)
   (mv-let (z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
     (cond ((eq operation :codec)
            (ewzt-to-codec 10 archive z pgs-digest-state fn-octets fn-ew-buffer
                           fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
           ((eq operation :hash)
            (mv-let (z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (ewzit-to-read 10 archive z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (mv-let (answer pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
              (ewzt-run 1 archive z 0 0 pgs-digest-state fn-octets fn-ew-buffer
                        fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
              (mv (nth 1 answer) pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
           (t (mv-let (z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                (ewzit-to-read 10 archive z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                (let ((fn-octets (fn-octets-from-list protected fn-octets)))
                (mv z pgs-digest-state fn-octets fn-ew-buffer
                    fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))))
     (let* ((fn-zin-st (if corrupt (fn-zin-set 6 (+ 1 (len c)) fn-zin-st) fn-zin-st))
            (before (fn-ewz-output-invariantp z fn-zin-st)))
       (cond
        ((eq operation :codec)
         (mv-let (decision next fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
           (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
           (declare (ignore decision))
           (mv (list before (fn-ewz-output-invariantp next fn-zin-st)
                     (equal (nth 0 z) :codec) (equal (nth 0 next) :decoded)
                     (<= (fn-zin-tout fn-zin-st) (nfix (nth 2 next)))) fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
        ((member-eq operation '(:hash :hash-scan))
         (mv-let (decision next pgs-digest-state)
           (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)
           (declare (ignore decision))
           (mv (list before (fn-ewz-output-invariantp next fn-zin-st)
                     (equal (nth 0 z) (if (eq operation :hash) :drain :scan))
                     (equal (nth 0 next) (if (eq operation :hash) :decoded :scan))) fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
        (t (mv-let (status next pgs-digest-state fn-ew-buffer)
             (fn-ewz-read (fn-ewz-effect z pgs-digest-state) :ok z fn-octets pgs-digest-state fn-ew-buffer)
             (declare (ignore status))
             (mv (list before (natp (nth 2 (nth 1 z))) (natp (nth 7 (nth 1 z)))
                       (natp (nth 11 (nth 1 z))) (natp (nth 12 (nth 1 z)))
                       (fn-ewz-output-invariantp next fn-zin-st)
                       (equal (nth 0 next) :codec)) fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))))))))
 (mv answer fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-octets pgs-digest-state)))
 (mv answer pgs-digest-state)))
 answer)))

 ; Literal positive witnesses affirm the entire hypotheses/conclusion,
; and an actual nonempty codec/read or final-drain transition.
(defthm ewzot-begin-output-positive
 (equal (ewzot-transition-checks :begin nil nil) '(t t t)) :rule-classes nil)
(defthm ewzot-codec-output-positive
 (equal (ewzot-transition-checks :codec nil nil) '(t t t t t)) :rule-classes nil)
(defthm ewzot-read-output-positive
 (equal (ewzot-transition-checks :read nil nil) '(t t t t t t t)) :rule-classes nil)
(defthm ewzot-hash-output-positive
 (equal (ewzot-transition-checks :hash nil nil) '(t t t t)) :rule-classes nil)
; Corrupted-state removal witnesses. READ and scan-phase HASH retain an
; oversized private count if its sole carry hypothesis is omitted.
(defthm ewzot-read-without-output-carry-corrupted-state
 (equal (ewzot-transition-checks :read t nil) '(nil t t t t nil t)) :rule-classes nil)
(defthm ewzot-hash-without-output-carry-corrupted-state
 (equal (ewzot-transition-checks :hash-scan t nil) '(nil nil t t)) :rule-classes nil)
