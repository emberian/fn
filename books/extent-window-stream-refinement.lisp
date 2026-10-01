; Representation equations for the actual window stream input and output.
(in-package "ACL2")
(include-book "extent-window-stream")
(include-book "extent-window-refinement")

(local
 (defthm ewsr-octets-true-listp
   (implies (fn-b3-octet-listp xs) (true-listp xs))
   :hints (("Goal" :in-theory (enable fn-b3-octet-listp)))))
(local
 (defthm ewsr-firstn-length
   (implies (true-listp xs)
            (equal (fn-b3-firstn (len xs) xs) xs))
   :hints (("Goal" :in-theory (enable fn-b3-firstn)))))

; Actual buffer word assembly denotes exactly the bounded source block,
; with zero padding. This is not an assertion about a host-created word list.
(defthm fn-ews-concrete-block-is-source-words
  (implies (and (fn-b3-octet-listp source-block)
                (equal fn-octets source-block)
                (equal count (len source-block)))
           (equal (fn-b3x-words 16 0 count nil 0 0 fn-octets)
                  (fn-b3-words 16 source-block)))
  :hints (("Goal"
           :use ((:instance fn-b3x-words-is-words (k 16) (p 0) (e count)
                            (prefix nil) (lp 0) (a 0)))
           :in-theory (e/d (fn-b3x-msg0 fn-b3-nthcdrx)
                            (fn-b3x-words fn-b3-words fn-b3-firstn fn-b3-fix-octets))))
  :rule-classes nil)

; Every copied or retained byte in the actual host-called read output stays
; faithful. The original whole source is a proof parameter, never allocated
; by READ; the physical captured-source boundary supplies its bounded slice.
(defthm fn-ews-read-extends-faithful-window
  (implies
    (and (natp j) (natp (nth 4 s)) (natp (nth 5 s)) (natp (nth 7 s))
         (equal (nth 0 s) :scan) (< j (nth 5 s))
         (< (+ (nth 4 s) j) (+ (nth 7 s) (fn-ewp-demand s)))
         (fn-ews-effect s pgs-digest-state)
         (equal effect (fn-ews-effect s pgs-digest-state))
         (equal io-status :ok)
         (equal (fn-octets-len fn-octets) (fn-ewp-demand s))
         (equal fn-octets (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg))
         (implies (< (+ (nth 4 s) j) (nth 7 s))
                  (equal (nth j (nth 0 fn-ew-buffer)) (nth (+ (nth 4 s) j) msg))))
    (equal (nth j (nth 0 (mv-nth 3 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer))))
           (nth (+ (nth 4 s) j) msg)))
  :hints (("Goal" :use fn-ewb-capture-extends-faithful-window
                   :in-theory (enable fn-ews-read)))
  :rule-classes nil)

; The compressed controller shares the private decoded window with a raw
; hash subplan whose WN is zero. Even its scan reads cannot overwrite it.
(defthm fn-ews-zero-window-preserves-private-buffer
  (implies (equal (nth 5 s) 0)
           (equal (mv-nth 3 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer))
                  fn-ew-buffer))
  :hints (("Goal" :in-theory (enable fn-ews-read fn-ewb-capture fn-ewp-window-span fn-ewb-copy)))
  :rule-classes nil)

(defthm fn-ews-read-preserves-captured-request
  (equal (fn-ews-capture
          (mv-nth 1 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer)))
         (fn-ews-capture s))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ews-read fn-ews-capture fn-ewp-complete-read
                              fn-ewp-finish fn-ewp-with-phase-pos fn-ewp-state))))

(defthm fn-ews-read-never-decreases-scan-position
  (implies (natp (nth 7 s))
           (<= (nth 7 s)
               (nth 7 (mv-nth 1 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ews-read fn-ewp-complete-read
                              fn-ewp-finish fn-ewp-with-phase-pos fn-ewp-state))))

(defthm fn-ews-read-preserves-natural-scan-position
  (implies (natp (nth 7 s))
           (natp (nth 7 (mv-nth 1 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ews-read fn-ewp-complete-read
                              fn-ewp-finish fn-ewp-with-phase-pos fn-ewp-state))))

(defthm fn-ews-tick-preserves-captured-request-and-position
  (let ((next (mv-nth 1 (fn-ews-tick s pgs-digest-state))))
    (and (equal (fn-ews-capture next) (fn-ews-capture s))
         (equal (nth 7 next) (nth 7 s))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ews-tick fn-ews-capture fn-ewp-with-phase-pos fn-ewp-state))))
