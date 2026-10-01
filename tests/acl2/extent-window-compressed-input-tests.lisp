(in-package "ACL2")
(include-book "../../books/extent-window-compressed-input")
(include-book "extent-window-compressed-refinement-tests")

; Advance only through actual dispatch actions until a core read is owed.
(defun ewzit-to-read (fuel archive z pgs-digest-state fn-octets fn-ew-buffer
                         fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
 (declare (xargs :verify-guards nil :measure (nfix fuel)
                 :stobjs (pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
 (if (or (zp fuel) (equal (car (fn-ewz-next-action z pgs-digest-state)) :read))
  (mv z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (mv-let (answer pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
   (ewzt-run 1 archive z 0 0 pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
   (ewzit-to-read (1- fuel) archive (nth 1 answer) pgs-digest-state fn-octets fn-ew-buffer
                  fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))

; Actual private pools, no huge logical ground-state term.
(defun ewzit-transition-checks (operation corrupt bad-coordinate)
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
   (mv (list (natp poff) (fn-ewz-input-invariantp z fn-zin-st)
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
     (let* ((fn-zin-st (if corrupt (fn-zin-set 7 (+ 1 (len c)) fn-zin-st) fn-zin-st))
            (before (fn-ewz-input-invariantp z fn-zin-st)))
       (cond
        ((eq operation :codec)
         (mv-let (decision next fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
           (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
           (declare (ignore decision))
           (mv (list before (fn-ewz-input-invariantp next fn-zin-st)
                     (equal (nth 0 z) :codec) (equal (nth 0 next) :decoded)
                     (<= (fn-zin-tin fn-zin-st) (nfix (nth 12 (nth 1 next))))) fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
        ((eq operation :hash)
         (mv-let (decision next pgs-digest-state)
           (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)
           (declare (ignore decision))
           (mv (list before (fn-ewz-input-invariantp next fn-zin-st)
                     (equal (nth 0 z) :drain) (equal (nth 0 next) :decoded)) fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
        (t (mv-let (status next pgs-digest-state fn-ew-buffer)
             (fn-ewz-read (fn-ewz-effect z pgs-digest-state) :ok z fn-octets pgs-digest-state fn-ew-buffer)
             (declare (ignore status))
             (mv (list before (natp (nth 2 (nth 1 z))) (natp (nth 7 (nth 1 z)))
                       (natp (nth 11 (nth 1 z))) (natp (nth 12 (nth 1 z)))
                       (fn-ewz-input-invariantp next fn-zin-st)
                       (equal (nth 0 next) :codec)) fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))))))))
 (mv answer fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-octets pgs-digest-state)))
 (mv answer pgs-digest-state)))
 answer)))

; Each reachable positive evaluates every literal theorem hypothesis and
; its complete conclusion; mode/terminal checks affirm a real transition.
(defthm ewzit-begin-input-positive
 (equal (ewzit-transition-checks :begin nil nil) '(t t t)) :rule-classes nil)
(defthm ewzit-codec-input-positive
 (equal (ewzit-transition-checks :codec nil nil) '(t t t t t)) :rule-classes nil)
(defthm ewzit-read-input-positive
 (equal (ewzit-transition-checks :read nil nil) '(t t t t t t t)) :rule-classes nil)
(defthm ewzit-hash-input-positive
 (equal (ewzit-transition-checks :hash nil nil) '(t t t t)) :rule-classes nil)

; BEGIN removal: nonnatural POFF is the sole omitted hypothesis. The
; guarded production call cannot create it; this is a malformed-coordinate
; logical-domain witness, distinct from a served successful admission.
(defthm ewzit-begin-without-natural-payload-coordinate
 (equal (ewzit-transition-checks :begin nil t) '(nil nil t)) :rule-classes nil)

; Corrupted-state hypothesis-removal witnesses: only carried input evidence
; fails; the extra READ coordinate checks affirm the captured request shape.
(defthm ewzit-codec-without-input-carry-corrupted-state
 (equal (ewzit-transition-checks :codec t nil) '(nil nil t t nil)) :rule-classes nil)
(defthm ewzit-read-without-input-carry-corrupted-state
 (equal (ewzit-transition-checks :read t nil) '(nil t t t t nil t)) :rule-classes nil)
(defthm ewzit-hash-without-input-carry-corrupted-state
 (equal (ewzit-transition-checks :hash t nil) '(nil nil t nil)) :rule-classes nil)
