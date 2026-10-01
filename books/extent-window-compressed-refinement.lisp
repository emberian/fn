(in-package "ACL2")
(include-book "extent-window-compressed")
(include-book "extent-window-stream-refinement")
(local
 (in-theory (disable fn-pzw-stored-chunk fn-pzw-chunk fn-pzw-select
                     fn-pzw-stored-decision fn-pzw-decision fn-pzw-budget-left
                     fn-pzw-stored-chunk-is-resumable-run fn-zin-feed-unfolds
                     fn-ewz-state fn-ewz-compressed-completep fn-ewz-decision-mode)))


; Exact copy boundary over the scratch produced by the actual stored codec.
; The theorem describes every cell, including cells outside the selection.
(defthm fn-ewz-codec-tick-exact-window-output-and-effects
  (implies
   (and (natp j) (equal (nth 0 z) :codec)
        (natp (nth 6 z)) (natp (nth 7 z)) (<= (nth 6 z) (nth 7 z))
        (<= (- (nth 7 z) (nth 6 z)) 64)
        (<= (nth 7 z) (fn-octets-len fn-octets)))
   (let* ((r (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                  (nth 12 (nth 1 z)) (nth 2 z)
                                  fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
          (scratch (mv-nth 6 r))
          (span (fn-pzw-select (fn-zin-tout fn-zin-st) (fn-zin-out-len scratch)
                               (nth 3 z) (nth 4 z))))
     (equal
      (nth j (nth 0 (mv-nth 6 (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))))
      (if (and (<= (mv-nth 2 span) j) (< j (+ (mv-nth 2 span) (mv-nth 1 span))))
          (nth (+ (car span) (- j (mv-nth 2 span))) scratch)
        (nth j (nth 0 fn-ew-buffer))))))
  :hints (("Goal" :do-not-induct t
           :use (:instance fn-ewb-copy-exact-output-and-effects
                   (src (car (fn-pzw-select (fn-zin-tout fn-zin-st)
                                (fn-zin-out-len (mv-nth 6 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                               (nth 12 (nth 1 z)) (nth 2 z) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                                (nth 3 z) (nth 4 z))))
                   (count (mv-nth 1 (fn-pzw-select (fn-zin-tout fn-zin-st)
                                (fn-zin-out-len (mv-nth 6 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                               (nth 12 (nth 1 z)) (nth 2 z) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                                (nth 3 z) (nth 4 z))))
                   (dst (mv-nth 2 (fn-pzw-select (fn-zin-tout fn-zin-st)
                                (fn-zin-out-len (mv-nth 6 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                               (nth 12 (nth 1 z)) (nth 2 z) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                                (nth 3 z) (nth 4 z))))
                   (fn-octets (mv-nth 6 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                               (nth 12 (nth 1 z)) (nth 2 z) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
           :in-theory (enable fn-ewz-codec-tick)))
  :rule-classes nil)

(defthm fn-ewz-codec-decoded-has-exact-length-and-terminal
  (let ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
    (implies (equal (nth 0 (mv-nth 1 r)) :decoded)
             (and (equal (nth 0 z) :codec)
                  (equal (fn-zin-tout (mv-nth 2 r)) (nth 2 z))
                  (fn-pzw-stored-admissiblep (nth 12 (nth 1 z)) (nth 2 z))
                  (fn-ewz-compressed-completep (nth 1 z))
                  (or (and (equal (nth 12 (nth 1 z)) 0) (equal (nth 2 z) 0)
                           (equal (fn-zin-tin (mv-nth 2 r)) 0))
                      (fn-zin-stored-terminalp (nth 8 (mv-nth 1 r)) (mv-nth 2 r))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ewz-codec-tick fn-ewz-state fn-ewz-decision-mode)
           :use (:instance fn-pzw-stored-decoded-is-complete
                   (status (car (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                  (nth 12 (nth 1 z)) (nth 2 z)
                                  fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                   (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))
                   (remaining (fn-pzw-budget-left 1024 (nth 5 z)
                                (mv-nth 1 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                            (nth 12 (nth 1 z)) (nth 2 z)
                                            fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
                   (complete (and (equal (mv-nth 2 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                                   (nth 12 (nth 1 z)) (nth 2 z)
                                                   fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
                                         (nth 7 z))
                                  (fn-ewz-compressed-completep (nth 1 z))))
                   (fn-zin-st (mv-nth 3 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                           (nth 12 (nth 1 z)) (nth 2 z)
                                           fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))))
  :rule-classes nil)

(defthm fn-ewz-read-zero-window-preserves-private-buffer
  (implies (equal (nth 5 (nth 1 z)) 0)
           (equal (mv-nth 3 (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer))
                  fn-ew-buffer))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-ewz-read)
           :use (:instance fn-ews-zero-window-preserves-private-buffer (s (nth 1 z)))))
  :rule-classes nil)

; A newly published decoded window on the READ entry can only follow the
; actual raw controller's full scan/trailer digest gate. A filled window or
; raw :verified state by itself does not satisfy compressed publication.
(defthm fn-ewz-read-publication-requires-core-integrity
  (implies
   (and (not (fn-ewz-publication z))
        (fn-ewz-publication
         (mv-nth 1 (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer))))
   (let ((plan (nth 1 z)))
     (and (equal (nth 0 z) :decoded)
          (equal (nth 0 plan) :trailer)
          (equal (pgs-dc-mode pgs-digest-state) :done)
          (equal (nth 7 plan) (nth 3 plan))
          (equal effect (fn-ews-effect plan pgs-digest-state))
          (equal io-status :ok) (equal (fn-octets-len fn-octets) 32)
          (equal (fn-bch-pack (fn-ews-read-trailer 32 0 fn-octets)) (nth 6 plan))
          (equal (pgs-dcb-result-octets pgs-digest-state)
                 (fn-ews-read-trailer 32 0 fn-octets)))))
  :hints (("Goal" :do-not-induct t
           :use (:instance fn-ews-read-publication-requires-core-integrity (s (nth 1 z)))
           :in-theory (e/d (fn-ewz-read fn-ewz-state fn-ewz-publication)
                            (nth fn-ewz-effect fn-ewp-payload-span))))
  :rule-classes nil)

; Carried codec evidence: no whole-state revalidation on a served entry.
(defun fn-ewz-decoded-invariantp (z fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (implies (equal (nth 0 z) :decoded)
           (and (equal (fn-zin-tout fn-zin-st) (nth 2 z))
                (fn-pzw-stored-admissiblep (nth 12 (nth 1 z)) (nth 2 z))
                (fn-ewz-compressed-completep (nth 1 z))
                (or (and (equal (nth 12 (nth 1 z)) 0) (equal (nth 2 z) 0)
                         (equal (fn-zin-tin fn-zin-st) 0))
                    (fn-zin-stored-terminalp (nth 8 z) fn-zin-st)))))
(in-theory (disable fn-ewz-decoded-invariantp))

(defthm fn-ewz-codec-tick-establishes-decoded-invariant
  (let ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
    (fn-ewz-decoded-invariantp (mv-nth 1 r) (mv-nth 2 r)))
  :hints (("Goal" :do-not-induct t
           :use fn-ewz-codec-decoded-has-exact-length-and-terminal
           :in-theory (enable fn-ewz-decoded-invariantp fn-ewz-codec-tick fn-ewz-state))))

(defthm fn-ewz-begin-establishes-decoded-invariant
  (let ((r (fn-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict
                        pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (fn-ewz-decoded-invariantp (car r) (mv-nth 2 r)))
  :hints (("Goal" :in-theory (enable fn-ewz-begin fn-ewz-state fn-ewz-decoded-invariantp))))

(local
 (defthm ewzr-completep-preserved
 (implies (and (natp (nth 7 s)) (fn-ewz-compressed-completep s))
  (fn-ewz-compressed-completep
   (mv-nth 1 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer))))
 :hints (("Goal" :do-not-induct t
  :use (fn-ews-read-preserves-captured-request fn-ews-read-never-decreases-scan-position fn-ews-read-preserves-natural-scan-position)
  :in-theory (e/d (fn-ewz-compressed-completep fn-ews-capture) (fn-ews-read-preserves-captured-request fn-ews-read-never-decreases-scan-position fn-ews-read-preserves-natural-scan-position))))))

(local
 (defthm ewzr-read-preserves-decoded-invariant-under-natural-position
  (implies (and (natp (nth 7 (nth 1 z))) (fn-ewz-decoded-invariantp z fn-zin-st))
           (fn-ewz-decoded-invariantp
            (mv-nth 1 (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer)) fn-zin-st))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ews-read-preserves-captured-request (s (nth 1 z)))
                 (:instance ewzr-completep-preserved (s (nth 1 z))))
           :in-theory (e/d (fn-ewz-read fn-ewz-state fn-ewz-decoded-invariantp fn-ews-capture)
                            (fn-ews-read-preserves-captured-request fn-pzw-stored-admissiblep
                             fn-zin-stored-terminalp fn-ewz-effect fn-ewp-payload-span))))))

(local
 (defthm ewzr-effect-natural-position-by-definition
 (implies (fn-ewz-effect z pgs-digest-state) (natp (nth 7 (nth 1 z))))
 :hints (("Goal" :in-theory (enable fn-ewz-effect fn-ews-effect fn-ews-boundp)))))

(defthm fn-ewz-read-preserves-decoded-invariant
 (implies (fn-ewz-decoded-invariantp z fn-zin-st)
  (fn-ewz-decoded-invariantp
   (mv-nth 1 (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer)) fn-zin-st))
 :hints (("Goal" :do-not-induct t
  :cases ((fn-ewz-effect z pgs-digest-state))
  :use (ewzr-read-preserves-decoded-invariant-under-natural-position ewzr-effect-natural-position-by-definition)
  :in-theory (e/d (fn-ewz-read) (fn-ewz-effect fn-ewz-decoded-invariantp nth fn-ewp-payload-span
                    ewzr-read-preserves-decoded-invariant-under-natural-position ewzr-effect-natural-position-by-definition)))))

(local
 (defthm ewzr-tick-completep-preserved
 (equal (fn-ewz-compressed-completep (mv-nth 1 (fn-ews-tick s pgs-digest-state)))
        (fn-ewz-compressed-completep s))
 :hints (("Goal" :do-not-induct t
  :use fn-ews-tick-preserves-captured-request-and-position
  :in-theory (e/d (fn-ewz-compressed-completep fn-ews-capture)
                  (fn-ews-tick-preserves-captured-request-and-position))))))

(defthm fn-ewz-hash-tick-preserves-decoded-invariant
  (implies (fn-ewz-decoded-invariantp z fn-zin-st)
           (fn-ewz-decoded-invariantp
            (mv-nth 1 (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)) fn-zin-st))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ews-tick-preserves-captured-request-and-position (s (nth 1 z)))
                 (:instance fn-pzw-stored-decoded-is-complete
                   (status (nth 8 z)) (compressed (nth 12 (nth 1 z)))
                   (expected (nth 2 z)) (remaining (nth 5 z)) (complete t)))
           :in-theory (e/d (fn-ewz-hash-tick fn-ewz-state fn-ewz-decoded-invariantp
                             fn-ewz-decision-mode fn-ews-capture)
                            (fn-ewz-compressed-completep nth update-nth fn-ews-tick-preserves-captured-request-and-position fn-pzw-stored-admissiblep
                             fn-zin-stored-terminalp fn-ewz-effect fn-ewp-payload-span)))))
