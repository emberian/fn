; Actual compressed controller authentication carry; source-only component.
; The captured-source read equality remains an explicit I/O binding obligation.
(in-package "ACL2")
(include-book "decoded-window-selected-trajectory")
(include-book "extent-window-stream-semantics")
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-pwdg-actual-raw-read-retains-total
  (equal (nth 3 (mv-nth 1 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer)))
         (nth 3 s))
  :hints (("Goal" :do-not-induct t
           :use fn-ews-read-preserves-captured-request
           :in-theory (e/d (fn-ews-capture) (fn-ews-read fn-ews-read-preserves-captured-request))))))
(local
 (defthm fn-pwdg-actual-raw-tick-retains-total
  (equal (nth 3 (mv-nth 1 (fn-ews-tick s pgs-digest-state))) (nth 3 s))
  :hints (("Goal" :do-not-induct t
           :use fn-ews-tick-preserves-captured-request-and-position
           :in-theory (e/d (fn-ews-capture) (fn-ews-tick fn-ews-tick-preserves-captured-request-and-position))))))

(defthm fn-pwdg-actual-compressed-begin-establishes-digest-trajectory
 (implies (and (natp limit) (<= limit 63)
               (fn-b3-octet-listp msg) (equal (len msg) elen)
               (<= (pgs-dcb-word-count elen) (* 128 (expt 2 limit))))
  (pgs-dcs-invariantp limit elen msg
   (mv-nth 1 (fn-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict
                          pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
 :hints (("Goal" :do-not-induct t
          :use (:instance fn-ews-begin-establishes-digest-trajectory
                  (plen compressed) (offset compressed))
          :in-theory (e/d (fn-ewz-begin)
                          (fn-ews-begin fn-pzw-initialize pgs-dcs-invariantp
                           fn-ews-begin-establishes-digest-trajectory))))
 :rule-classes nil)

(defthm fn-pwdg-actual-compressed-read-preserves-digest-trajectory
 (implies (and (pgs-dcs-invariantp limit (nth 3 (nth 1 z)) msg pgs-digest-state)
               (implies (equal (nth 0 (nth 1 z)) :scan)
                        (equal fn-octets (fn-shr-win (nth 7 (nth 1 z)) (fn-ewp-demand (nth 1 z)) msg))))
  (let ((r (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer)))
   (pgs-dcs-invariantp limit (nth 3 (nth 1 (mv-nth 1 r))) msg (mv-nth 2 r))))
 :hints (("Goal" :do-not-induct t
          :use (:instance fn-ews-read-preserves-digest-trajectory (s (nth 1 z)))
          :in-theory (e/d (fn-ewz-read fn-ewz-state)
                          (fn-ews-read pgs-dcs-invariantp fn-ewz-effect fn-ewp-payload-span
                           fn-ews-read-preserves-digest-trajectory))))
 :rule-classes nil)

(defthm fn-pwdg-actual-compressed-hash-preserves-digest-trajectory
 (implies (pgs-dcs-invariantp limit (nth 3 (nth 1 z)) msg pgs-digest-state)
  (let ((r (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)))
   (pgs-dcs-invariantp limit (nth 3 (nth 1 (mv-nth 1 r))) msg (mv-nth 2 r))))
 :hints (("Goal" :do-not-induct t
          :use (:instance fn-ews-tick-preserves-digest-trajectory (s (nth 1 z)))
          :in-theory (e/d (fn-ewz-hash-tick)
                          (fn-ews-tick pgs-dcs-invariantp fn-ewz-compressed-completep
                           fn-pzw-stored-decision fn-ewz-decision-mode
                           fn-ews-tick-preserves-digest-trajectory))))
 :rule-classes nil)

(defthm fn-pwdg-actual-compressed-publication-authenticates-captured-source
 (implies
  (and (pgs-dcs-invariantp limit (nth 3 (nth 1 z)) msg pgs-digest-state)
       (not (fn-ewz-publication z))
       (fn-ewz-publication
        (mv-nth 1 (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer))))
  (and (equal (fn-ews-read-trailer 32 0 fn-octets) (fn-blake3 msg))
       (equal (nth 6 (nth 1 z)) (fn-bch-pack (fn-blake3 msg)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-ewz-read-publication-requires-core-integrity
                (:instance pgs-dcs-done-result-is-blake3 (byte-total (nth 3 (nth 1 z)))))
          :in-theory (disable fn-ewz-read fn-ewz-publication pgs-dcs-invariantp
                              pgs-dcb-result-octets fn-blake3 fn-ews-read-trailer fn-bch-pack)))
 :rule-classes nil)
