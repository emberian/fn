; Actual captured-source authentication composition. Proof vocabulary only.
(in-package "ACL2")
(include-book "extent-window-source-words")
(include-book "extent-window-stream-refinement")
(include-book "pagestore-digest-cursor-semantics")
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm ewss-source-octets-true-listp
  (implies (fn-b3-octet-listp msg) (true-listp msg))
  :hints (("Goal" :in-theory (enable fn-b3-octet-listp)))))

(local
 (defthm ewss-octets-nthcdr
  (implies (fn-b3-octet-listp msg) (fn-b3-octet-listp (nthcdr n msg)))
  :hints (("Goal" :induct (nthcdr n msg)
                  :in-theory (enable nthcdr fn-b3-octet-listp)))))

(local
 (defthm ewss-octets-take
  (implies (and (fn-b3-octet-listp xs) (natp n) (<= n (len xs)))
           (fn-b3-octet-listp (take n xs)))
  :hints (("Goal" :induct (take n xs)
                  :in-theory (enable take fn-b3-octet-listp)))))

(local
 (defthm ewss-window-is-octets
  (implies (and (fn-b3-octet-listp msg) (natp start) (natp count)
                (<= (+ start count) (len msg)))
           (fn-b3-octet-listp (fn-shr-win start count msg)))
  :hints (("Goal" :in-theory (enable fn-shr-win)))))

(local
 (defthm ewss-min-after-position
  (implies (and (natp a) (natp b) (natp c) (<= a b) (<= a c))
           (equal (nfix (- (min b c) a)) (min (- c a) (- b a))))
  :hints (("Goal" :in-theory (enable min nfix)))))

(local
 (defthm ewss-nfix-natural
  (implies (natp n) (equal (nfix n) n))
  :hints (("Goal" :in-theory (enable nfix)))))
(local
 (defthm ewss-min-bounds
  (and (<= (min a b) a) (<= (min a b) b))
  :hints (("Goal" :in-theory (enable min)))
  :rule-classes :linear))
(local
 (defthm ewss-natural-min
  (implies (and (natp a) (natp b)) (natp (min a b)))
  :hints (("Goal" :in-theory (enable min)))))

(local
 (defthm ewss-scaled-span-natural
  (implies (and (natp p) (natp e) (<= p e)) (natp (* 8 (- e p))))
  :rule-classes nil))

(local
 (defthm ewss-canonical-under-scan
 (implies (and (pgs-dcs-invariantp limit (nth 3 s) msg pgs-digest-state)
               (fn-ews-effect s pgs-digest-state)
               (equal (nth 0 s) :scan)
               (equal fn-octets (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg)))
          (pgs-dcs-blockp
           (fn-b3x-words 16 0 (fn-ewp-demand s) nil 0 0 fn-octets) msg pgs-digest-state))
 :hints (("Goal" :do-not-induct t
  :use ((:instance ewss-scaled-span-natural (p (pgs-dc-pos pgs-digest-state)) (e (pgs-dc-end pgs-digest-state)))
        (:instance ewss-min-after-position
          (a (* 8 (pgs-dc-pos pgs-digest-state))) (b (nth 3 s))
          (c (* 8 (pgs-dc-end pgs-digest-state))))
        (:instance pgs-dcs-domain-current-unfolds (byte-total (nth 3 s)))
        (:instance ewss-window-is-octets (start (nth 7 s)) (count (fn-ewp-demand s)))
        (:instance fn-ews-concrete-block-is-source-words
          (source-block (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg)) (count (fn-ewp-demand s)))
        (:instance fn-ews-window-words-are-span-words
          (k 16) (start (* 8 (pgs-dc-pos pgs-digest-state)))
          (count (* 8 (- (pgs-dc-end pgs-digest-state) (pgs-dc-pos pgs-digest-state))))))
  :in-theory (e/d (pgs-dcs-blockp pgs-dcs-invariantp fn-ews-effect fn-ews-boundp
                  pgs-dcb-read-demand pgs-dcb-next-byte-offset pgs-dcr-span)
                 (fn-shr-win fn-b3x-words fn-b3-words fn-b3-firstn fn-b3-nthcdrx
                  pgs-dbd-domainp pgs-dcs-counterp pgs-dcs-phasep pgs-dcr-denote fn-b3-node
                  nth pgs-dbd-domain-implies-byte-step-guard pgs-dbd-domain-scalars nfix min member-equal posp pgs-dc-pos pgs-dc-end pgs-dc-start pgs-dc-mode pgs-dc-power pgs-dc-depth pgs-dc-total pgs-dc-cv pgs-dc-counter pgs-dc-capture pgs-dc-lease fn-shr-win-is-slice fn-ews-window-words-are-span-words))))))

(defthm fn-ews-actual-read-block-is-canonical-source
 (implies (and (pgs-dcs-invariantp limit (nth 3 s) msg pgs-digest-state)
               (fn-ews-effect s pgs-digest-state)
               (equal fn-octets (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg)))
          (pgs-dcs-blockp
           (fn-b3x-words 16 0 (fn-ewp-demand s) nil 0 0 fn-octets) msg pgs-digest-state))
 :hints (("Goal" :cases ((equal (nth 0 s) :scan))
  :use ewss-canonical-under-scan
  :in-theory (e/d (fn-ews-effect pgs-dcs-blockp pgs-dc-needs-block)
                  (fn-ews-boundp fn-ewp-effect pgs-dcs-invariantp fn-b3x-words fn-b3-words
                   pgs-dcr-span nth ewss-canonical-under-scan)))))

(defthm fn-ews-begin-establishes-digest-trajectory
 (implies (and (natp limit) (<= limit 63)
               (fn-b3-octet-listp msg) (equal (len msg) elen)
               (<= (pgs-dcb-word-count elen) (* 128 (expt 2 limit))))
          (pgs-dcs-invariantp limit elen msg
           (mv-nth 1 (fn-ews-begin file eoff elen poff plen offset ticket incarnation lease expected pgs-digest-state))))
 :hints (("Goal" :do-not-induct t
  :use (:instance pgs-dcs-begin-establishes-invariant
         (byte-total elen) (sel 0) (base 0) (lease lease)
         (capture (fn-ews-capture (fn-ewp-begin file eoff elen poff plen offset ticket incarnation lease expected))))
  :in-theory (e/d (fn-ews-begin) (pgs-dcb-begin pgs-dcs-invariantp pgs-dcs-begin-establishes-invariant)))))

(defthm fn-ews-read-preserves-digest-trajectory
 (implies (and (pgs-dcs-invariantp limit (nth 3 s) msg pgs-digest-state)
               (implies (equal (nth 0 s) :scan)
                        (equal fn-octets (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg))))
          (pgs-dcs-invariantp limit (nth 3 s) msg
           (mv-nth 2 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer))))
 :hints (("Goal" :do-not-induct t
  :use (fn-ews-actual-read-block-is-canonical-source
        (:instance pgs-dcs-byte-step-preserves-invariant
         (byte-total (nth 3 s))
         (block (fn-b3x-words 16 0 (fn-ewp-demand s) nil 0 0 fn-octets))))
  :in-theory (e/d (fn-ews-read) (pgs-dcs-invariantp pgs-dcs-blockp pgs-dcb-step
                  fn-ews-effect fn-ewp-demand fn-b3x-words fn-ewb-capture
                  fn-ewp-complete-read fn-ewp-with-phase-pos fn-ewp-finish
                  fn-ews-read-trailer pgs-dcb-result-octets fn-shr-win nth
                  fn-ews-actual-read-block-is-canonical-source pgs-dcs-byte-step-preserves-invariant)))))

(defthm fn-ews-tick-preserves-digest-trajectory
 (implies (pgs-dcs-invariantp limit (nth 3 s) msg pgs-digest-state)
          (pgs-dcs-invariantp limit (nth 3 s) msg
           (mv-nth 2 (fn-ews-tick s pgs-digest-state))))
 :hints (("Goal" :do-not-induct t
  :use (:instance pgs-dcs-byte-step-preserves-invariant (byte-total (nth 3 s)) (block nil))
  :in-theory (e/d (fn-ews-tick pgs-dcs-blockp) (pgs-dcs-invariantp pgs-dcb-step
                  fn-ews-effect fn-ews-boundp fn-ewp-with-phase-pos
                  fn-b3-words pgs-dcr-span nth pgs-dcs-byte-step-preserves-invariant)))))

(defthm fn-ews-read-new-publication-authenticates-captured-source
 (implies (and (pgs-dcs-invariantp limit (nth 3 s) msg pgs-digest-state)
               (not (fn-ewp-publication s))
               (fn-ewp-publication (mv-nth 1 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer))))
          (and (equal (fn-ews-read-trailer 32 0 fn-octets) (fn-blake3 msg))
               (equal (nth 6 s) (fn-bch-pack (fn-blake3 msg)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-ews-read-publication-requires-core-integrity
        (:instance pgs-dcs-done-result-is-blake3 (byte-total (nth 3 s))))
  :in-theory (disable fn-ews-read fn-ewp-publication pgs-dcs-invariantp pgs-dcb-result-octets
                      fn-blake3 fn-ews-read-trailer fn-bch-pack))))

