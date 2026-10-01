(in-package "ACL2")
(include-book "../../books/extent-window-compressed-refinement")
(include-book "extent-window-compressed-tests")

; Step the actual dispatcher to its first retained codec input.
(defun ewzt-to-codec (fuel archive z pgs-digest-state fn-octets fn-ew-buffer
                          fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :verify-guards nil :measure (nfix fuel)
                  :stobjs (pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  (if (or (zp fuel) (equal (nth 0 z) :codec))
      (mv z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (mv-let (answer pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (ewzt-run 1 archive z 0 0 pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (ewzt-to-codec (1- fuel) archive (nth 1 answer) pgs-digest-state fn-octets fn-ew-buffer
                     fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))

; Actual local buffers avoid materializing the 65KiB logical decoder pool
; in a ground proof term. Each result lists the complete literal checks.
(defun ewzt-copy-decoded-checks (j prepare)
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
                  (let* ((c '(1 3 0 252 255 65 66 67)) (digest (fn-blake3 c))
                         (fn-octets (fn-octets-from-list c fn-octets)))
                    (mv-let (z pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                      (fn-ewz-begin 7 100 8 100 8 3 0 23 47 59 (fn-bch-pack digest) nil
                                    pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                      (mv-let (z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                        (if prepare
                            (ewzt-to-codec 10 (append c digest) z pgs-digest-state fn-octets fn-ew-buffer
                                           fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                          (mv z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                        (let ((before (fn-zin-tout fn-zin-st))
                              (old-cell (fn-ew-bytesi (nfix j) fn-ew-buffer)))
                          (mv-let (decision next fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
                            (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
                            (declare (ignore decision))
                            (mv-let (src count dst)
                              (fn-pzw-select before (fn-zin-out-len fn-zin-out) (nth 3 z) (nth 4 z))
                              (mv
                               (list
                                ; Complete retained copy hypotheses, in literal order.
                                (natp j) (equal (nth 0 z) :codec)
                                (natp (nth 6 z)) (natp (nth 7 z)) (<= (nth 6 z) (nth 7 z))
                                (<= (- (nth 7 z) (nth 6 z)) 64)
                                (<= (nth 7 z) (fn-octets-len fn-octets))
                                ; Complete exact-cell conclusion, including unchanged case.
                                (equal (fn-ew-bytesi (nfix j) fn-ew-buffer)
                                       (if (and (<= dst j) (< j (+ dst count)))
                                           (fn-octets-get (+ src (- j dst)) fn-zin-out) old-cell))
                                ; Literal decoded antecedent and complete conclusion.
                                (equal (nth 0 next) :decoded)
                                (and (equal (nth 0 z) :codec)
                                     (equal (fn-zin-tout fn-zin-st) (nth 2 z))
                                     (fn-pzw-stored-admissiblep (nth 12 (nth 1 z)) (nth 2 z))
                                     (fn-ewz-compressed-completep (nth 1 z))
                                     (or (and (equal (nth 12 (nth 1 z)) 0) (equal (nth 2 z) 0)
                                              (equal (fn-zin-tin fn-zin-st) 0))
                                         (fn-zin-stored-terminalp (nth 8 next) fn-zin-st)))
                                ; Nonempty observed output prevents a vacuous copied branch.
                                (equal (fn-ew-bytesi 0 fn-ew-buffer) 65))
                               fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))))))
                (mv answer fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
              (mv answer fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
            (mv answer fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
          (mv answer fn-ew-buffer fn-octets pgs-digest-state)))
        (mv answer fn-octets pgs-digest-state)))
      (mv answer pgs-digest-state)))
    answer)))

; Reachable positive: all seven copy hypotheses, the entire cell conclusion,
; decoded antecedent and all five decoded conclusions, and nonempty output.
(defthm ewzt-copy-and-decoded-positive
  (equal (ewzt-copy-decoded-checks 0 t) '(t t t t t t t t t t t))
  :rule-classes nil)

; Remove only NATP J. Every retained hypothesis is affirmatively true;
; the complete cell conclusion fails at logical NTH's negative-index alias.
(defthm ewzt-copy-without-natural-cell
  (equal (ewzt-copy-decoded-checks -1 t) '(nil t t t t t t nil t t t))
  :rule-classes nil)

; Remove the decoded antecedent on a reachable initial :scan state; no
; retained hypothesis exists. The complete decoded conclusion fails.
(defthm ewzt-decoded-without-decoded-result
  (let ((r (ewzt-copy-decoded-checks 0 nil)))
    (and (not (nth 8 r)) (not (nth 9 r))))
  :rule-classes nil)

(defun ewzt-to-trailer (fuel archive z pgs-digest-state fn-octets fn-ew-buffer
                            fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :verify-guards nil :measure (nfix fuel)
                  :stobjs (pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  (if (or (zp fuel) (and (equal (nth 0 z) :decoded)
                         (equal (nth 6 (fn-ewz-effect z pgs-digest-state)) :trailer)))
      (mv z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (mv-let (answer pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (ewzt-run 1 archive z 0 0 pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (ewzt-to-trailer (1- fuel) archive (nth 1 answer) pgs-digest-state fn-octets fn-ew-buffer
                       fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))

(defun ewzt-integrity-conclusion (z effect io-status pgs-digest-state fn-octets)
  (declare (xargs :verify-guards nil :stobjs (pgs-digest-state fn-octets)))
  (let ((plan (nth 1 z)))
    (and (equal (nth 0 z) :decoded) (equal (nth 0 plan) :trailer)
         (equal (pgs-dc-mode pgs-digest-state) :done)
         (equal (nth 7 plan) (nth 3 plan))
         (equal effect (fn-ews-effect plan pgs-digest-state))
         (equal io-status :ok) (equal (fn-octets-len fn-octets) 32)
         (equal (fn-bch-pack (fn-ews-read-trailer 32 0 fn-octets)) (nth 6 plan))
         (equal (pgs-dcb-result-octets pgs-digest-state) (fn-ews-read-trailer 32 0 fn-octets)))))

(defun ewzt-publication-checks (removal)
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
                  (let* ((c '(1 3 0 252 255 65 66 67)) (digest (fn-blake3 c)))
                    (mv-let (z pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                      (fn-ewz-begin 7 100 8 100 8 3 0 23 47 59 (fn-bch-pack digest) nil
                                    pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                      (mv-let (z pgs-digest-state fn-octets fn-ew-buffer fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                        (ewzt-to-trailer 100 (append c digest) z pgs-digest-state fn-octets fn-ew-buffer
                                         fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                        (let* ((effect (fn-ewz-effect z pgs-digest-state))
                               (fn-octets (fn-octets-from-list digest fn-octets))
                               (no-prior (not (fn-ewz-publication z)))
                               (conclusion (ewzt-integrity-conclusion z effect :ok pgs-digest-state fn-octets)))
                          (mv-let (status next pgs-digest-state fn-ew-buffer)
                            (fn-ewz-read effect :ok z fn-octets pgs-digest-state fn-ew-buffer)
                            (declare (ignore status))
                            (if (not removal)
                                (mv (list no-prior (if (fn-ewz-publication next) t nil) conclusion
                                          (equal (fn-ew-bytesi 0 fn-ew-buffer) 65))
                                    fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)
                              (let ((no-prior (not (fn-ewz-publication next)))
                                    (conclusion (ewzt-integrity-conclusion next nil :ok pgs-digest-state fn-octets)))
                                (mv-let (status after pgs-digest-state fn-ew-buffer)
                                  (fn-ewz-read nil :ok next fn-octets pgs-digest-state fn-ew-buffer)
                                  (declare (ignore status))
                                  (mv (list no-prior (if (fn-ewz-publication after) t nil) conclusion
                                            (equal (fn-ew-bytesi 0 fn-ew-buffer) 65))
                                      fn-zin-out fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))))))))
                (mv answer fn-zin-tab fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
              (mv answer fn-zin-win fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
            (mv answer fn-zin-st fn-ew-buffer fn-octets pgs-digest-state)))
          (mv answer fn-ew-buffer fn-octets pgs-digest-state)))
        (mv answer fn-octets pgs-digest-state)))
      (mv answer pgs-digest-state)))
    answer)))

; Full antecedent, full integrity conclusion, and a nonempty decoded result.
(defthm ewzt-publication-integrity-positive
  (equal (ewzt-publication-checks nil) '(t t t t))
  :rule-classes nil)

; Remove only no-prior-publication. The retained next-publication hypothesis
; holds after an actual stale read; the entire new-integrity conclusion fails.
(defthm ewzt-publication-without-no-prior-publication
  (equal (ewzt-publication-checks t) '(nil t nil t))
  :rule-classes nil)
