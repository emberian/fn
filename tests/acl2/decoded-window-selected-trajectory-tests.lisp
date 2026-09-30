; Actual BEGIN/read/hash/codec dispatcher setup, with no installed native source holder.
(in-package "ACL2")
(include-book "../../books/decoded-window-selected-trajectory")
(include-book "extent-window-compressed-refinement-tests")
(defun fn-pws-selected-tick-checks (second j corrupt-cell bad-prefix)
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
 (let* ((wire (fn-pzd-stored (make-list 65 :initial-element 65)))
        (archive (append wire (fn-blake3 wire))))
 (mv-let (z pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (fn-ewz-begin 7 100 (len wire) 100 (len wire) 65 57 23 47 59
                (fn-bch-pack (fn-blake3 wire)) nil
                pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (mv-let (z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
   (ewzt-to-codec 100 archive z pgs-digest-state fn-octets fn-ew-buffer
                  fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
   (mv-let (z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (if second
     (mv-let (decision z fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
      (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
      (declare (ignore decision))
      (ewzt-to-codec 100 archive z pgs-digest-state fn-octets fn-ew-buffer
                     fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
     (mv z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
    (let* ((prefix (if second (make-list (if bad-prefix 60 59) :initial-element 65) nil))
           (fn-ew-buffer (if corrupt-cell (update-fn-ew-bytesi 0 99 fn-ew-buffer) fn-ew-buffer))
           (domain (and (equal (nth 0 z) :codec)
                        (natp (nth 6 z)) (natp (nth 7 z)) (<= (nth 6 z) (nth 7 z))
                        (<= (- (nth 7 z) (nth 6 z)) 64)
                        (<= (nth 7 z) (fn-octets-len fn-octets))
                        (natp (nth 3 z)) (natp (nth 4 z)) (<= (nth 4 z) 16384)
                        (natp j) (equal (fn-zin-win-len fn-zin-win) 65536)
                        (equal (fn-zin-tab-len fn-zin-tab) 3494)))
           (position (equal (fn-zin-tout fn-zin-st) (len prefix)))
           (carry (implies (and (< j (nth 4 z)) (< (+ (nth 3 z) j) (len prefix)))
                           (equal (fn-ew-bytesi j fn-ew-buffer) (nth (+ (nth 3 z) j) prefix)))))
     (mv-let (decision next fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
      (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
      (let* ((model (append prefix (fn-zin-out-list fn-zin-out)))
             (conclusion (and (equal (fn-zin-tout fn-zin-st) (len model))
                             (implies (and (< j (nth 4 z)) (< (+ (nth 3 z) j) (len model)))
                                      (equal (fn-ew-bytesi j fn-ew-buffer)
                                             (nth (+ (nth 3 z) j) model))))))
       (mv (list domain position carry conclusion decision (nth 0 next)
                 (fn-zin-tout fn-zin-st) (fn-ew-bytesi j fn-ew-buffer))
           fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state))))))))
 (mv answer fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-ew-buffer fn-octets pgs-digest-state)))
 (mv answer fn-octets pgs-digest-state)))
 (mv answer pgs-digest-state)))
 answer)))

(local (defthm fn-pws-first-new-cell
 (equal (fn-pws-selected-tick-checks nil 0 nil nil) '(t t t t :input :scan 59 65))
 :rule-classes nil))

(local (defthm fn-pws-second-carried-cell
 (equal (fn-pws-selected-tick-checks t 0 nil nil) '(t t t t :decoded :decoded 65 65))
 :rule-classes nil))

(local (defthm fn-pws-second-new-cell
 (equal (fn-pws-selected-tick-checks t 7 nil nil) '(t t t t :decoded :decoded 65 65))
 :rule-classes nil))

(local (defthm fn-pws-prior-cell-carry-removal-corrupted-state
 (equal (fn-pws-selected-tick-checks t 0 t nil) '(t t nil nil :decoded :decoded 65 99))
 :rule-classes nil))

(local (defthm fn-pws-prefix-position-removal-corrupted-model
 (equal (fn-pws-selected-tick-checks t 7 nil t) '(t nil t nil :decoded :decoded 65 65))
 :rule-classes nil))
