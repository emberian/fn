; Active decoded-output carry for the actual streaming compressed controller.
(in-package "ACL2")
(include-book "payload-window")
(include-book "extent-window-compressed-input")

(defun fn-ewz-output-invariantp (z fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (implies (member-eq (nth 0 z) '(:scan :codec :drain :decoded))
           (and (fn-pzw-stored-admissiblep (nth 12 (nth 1 z)) (nth 2 z))
                (<= (fn-zin-tout fn-zin-st)
                    (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 (nth 1 z))))))))
(in-theory (disable fn-ewz-output-invariantp))

(local
 (defthm ewzo-active-decision-bounds-output
  (implies (member-eq (fn-pzw-stored-decision status compressed expected remaining complete fn-zin-st)
                     '(:input :resume :drain :decoded))
           (and (fn-pzw-stored-admissiblep compressed expected)
                (<= (fn-zin-tout fn-zin-st)
                    (min (nfix expected) (fn-pzw-stored-allowance compressed)))))
  :hints (("Goal" :in-theory (enable fn-pzw-stored-decision fn-pzw-decision
                                    fn-pzw-stored-admissiblep min)))))

(defthm fn-ewz-codec-tick-establishes-output-invariant
 (let ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
  (fn-ewz-output-invariantp (mv-nth 1 r) (mv-nth 2 r)))
 :hints (("Goal" :do-not-induct t
  :use (:instance ewzo-active-decision-bounds-output
    (status (car (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                 (nth 12 (nth 1 z)) (nth 2 z) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))
    (remaining (fn-pzw-budget-left 1024 (nth 5 z)
      (mv-nth 1 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                 (nth 12 (nth 1 z)) (nth 2 z) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
    (complete (and (equal (mv-nth 2 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                 (nth 12 (nth 1 z)) (nth 2 z) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (nth 7 z))
                   (fn-ewz-compressed-completep (nth 1 z))))
    (fn-zin-st (mv-nth 3 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                 (nth 12 (nth 1 z)) (nth 2 z) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :in-theory (e/d (fn-ewz-codec-tick fn-ewz-state fn-ewz-decision-mode fn-ewz-output-invariantp)
                  (fn-pzw-stored-chunk fn-pzw-select fn-ewb-copy fn-pzw-budget-left
                   fn-pzw-stored-decision fn-ewz-compressed-completep nth
                   ewzo-active-decision-bounds-output fn-pzw-stored-chunk-is-resumable-run)))))

(local
 (defthm ewzo-reset-loop-below
   (implies (and (natp i) (natp j) (< j i))
            (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) (fn-zin-fld j fn-zin-st)))
   :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
                  :in-theory (enable fn-zin-reset-loop)))))
(local
 (defthm ewzo-reset-loop-fields
   (implies (and (natp i) (natp j) (<= i j) (< j 18))
            (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) 0))
   :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
                  :in-theory (enable fn-zin-reset-loop)))))

(defthm fn-ewz-begin-establishes-output-invariant
 (let ((r (fn-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict
                       pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  (fn-ewz-output-invariantp (car r) (mv-nth 2 r)))
 :hints (("Goal" :do-not-induct t
  :in-theory (enable fn-ewz-begin fn-ewz-state fn-ewz-output-invariantp
                     fn-ews-begin fn-ewp-begin fn-ewp-state fn-pzw-initialize
                     fn-zin-reset fn-zin-reset-loop min))))

(defthm fn-ewz-read-preserves-output-invariant
 (implies (fn-ewz-output-invariantp z fn-zin-st)
  (fn-ewz-output-invariantp
   (mv-nth 1 (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer)) fn-zin-st))
 :hints (("Goal" :do-not-induct t
  :use (:instance fn-ews-read-preserves-captured-request (s (nth 1 z)))
  :in-theory (e/d (fn-ewz-read fn-ewz-state fn-ewz-output-invariantp fn-ews-capture)
                  (fn-ews-read fn-ewz-effect fn-ewp-payload-span fn-pzw-stored-admissiblep
                   fn-pzw-stored-allowance nth fn-ews-read-preserves-captured-request)))))

(defthm fn-ewz-hash-tick-preserves-output-invariant
 (implies (fn-ewz-output-invariantp z fn-zin-st)
  (fn-ewz-output-invariantp
   (mv-nth 1 (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)) fn-zin-st))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ews-tick-preserves-captured-request-and-position (s (nth 1 z)))
        (:instance ewzo-active-decision-bounds-output
         (status (nth 8 z)) (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))
         (remaining (nth 5 z)) (complete t)))
  :in-theory (e/d (fn-ewz-hash-tick fn-ewz-output-invariantp fn-ewz-decision-mode fn-ews-capture)
                  (fn-ews-tick fn-ewz-compressed-completep fn-pzw-stored-decision
                   fn-pzw-stored-admissiblep fn-pzw-stored-allowance nth update-nth
                   ewzo-active-decision-bounds-output fn-ews-tick-preserves-captured-request-and-position)))))
