; CURRENT registered codec turn to the actual basic loop's complete effects.
; Proof-only reference; no installed native issuer or allowance is introduced.
(in-package "ACL2")
(include-book "decoded-worker-controller-trajectory")
(include-book "decoded-window-stored-trajectory")

(local
 (defthm fn-dwcc-codec-action-implies-codec-mode-by-definition
  (implies (equal (car (fn-ewz-next-action z pgs-digest-state)) :codec)
           (equal (nth 0 z) :codec))
  :hints (("Goal" :in-theory (e/d (fn-ewz-next-action) (fn-ewz-publication fn-ewz-effect))))))

; CREDIT is the proved reference recredit used by the existing actual FEED
; refinement. It is a logical observation, never a native budget substitution.
(defthm fn-dwcc-actual-codec-one-basic-loop-effects
 (let ((z (fn-pww-controller fn-pww-carry)))
  (implies
   (and (fn-pwz-tokenp token) (equal token (fn-pww-token fn-pww-carry))
        (eq (fn-pww-phase fn-pww-carry) :running)
        (eq (fn-pww-borrow-phase fn-pww-carry) :owned)
        (null (fn-pww-pending-action fn-pww-carry))
        (true-listp z) (true-listp (nth 1 z))
        (equal (car (fn-ewz-next-action z pgs-digest-state)) :codec)
        (natp (nth 6 z)) (natp (nth 7 z)) (<= (nth 6 z) (nth 7 z))
        (<= (- (nth 7 z) (nth 6 z)) 64)
        (<= (nth 7 z) (fn-octets-len fn-octets)))
   (let* ((r (fn-dwc-one token fn-pww-carry fn-octets pgs-digest-state
                        fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))
          (next (fn-pww-controller (mv-nth 2 r)))
          (compressed (nth 12 (nth 1 z)))
          (credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
          (ref (fn-zin-feed (fn-pzw-quantum 1024 (nth 5 z)) credited (nth 6 z) (nth 7 z)
                  (fn-pzw-room (min (nfix (nth 2 z)) (fn-pzw-stored-allowance compressed))
                               (fn-zin-tout credited))
                  fn-octets fn-zin-win fn-zin-tab nil)))
    (equal (list (nth 8 next) (nth 6 next)
                 (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin (mv-nth 5 r))) (mv-nth 5 r))
                 (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))
           (list (car ref) (mv-nth 2 ref) (mv-nth 3 ref)
                 (mv-nth 4 ref) (mv-nth 5 ref) (mv-nth 6 ref))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-dwcc-codec-action-implies-codec-mode-by-definition
          (z (fn-pww-controller fn-pww-carry)))
        (:instance fn-pwzc-actual-stored-chunk-recredited-full-tuple
          (requested 1024) (remaining (nth 5 (fn-pww-controller fn-pww-carry)))
          (start (nth 6 (fn-pww-controller fn-pww-carry)))
          (end (nth 7 (fn-pww-controller fn-pww-carry)))
          (compressed (nth 12 (nth 1 (fn-pww-controller fn-pww-carry))))
          (expected (nth 2 (fn-pww-controller fn-pww-carry)))))
  :in-theory (e/d (fn-dwc-one fn-ewz-codec-tick fn-ewz-state)
   (fn-pwz-tokenp fn-ewz-next-action fn-ewz-hash-tick fn-zin-feed
    fn-pzw-stored-chunk fn-pzw-select fn-ewb-copy fn-pzw-budget-left
    fn-pzw-stored-decision fn-pzw-quantum fn-pzw-room fn-pzw-stored-allowance
    fn-pzw-stored-chunk-is-resumable-run fn-zin-loop fn-zin-run min nfix)))))

; Subsequent hash/drain/publication turns cannot overwrite selected output.
(defthm fn-dwcc-actual-noncodec-one-retains-selected-window
 (implies (not (equal (car (fn-ewz-next-action (fn-pww-controller fn-pww-carry) pgs-digest-state)) :codec))
  (equal (mv-nth 9 (fn-dwc-one token fn-pww-carry fn-octets pgs-digest-state
                             fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))
         fn-ew-buffer))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-dwc-one) (fn-ewz-next-action fn-ewz-codec-tick fn-ewz-hash-tick fn-pwz-tokenp)))))

; The actual typed compressed plan's raw window request is zero. Trailer
; I/O can update the input/digest but preserves the selected decoded window.
(defthm fn-dwcc-actual-current-read-retains-selected-window
 (implies (equal (nth 5 (nth 1 (fn-pww-controller fn-pww-carry))) 0)
  (equal (mv-nth 4 (fn-dwc-read-observation token revision io-status fn-pww-carry
                         fn-octets pgs-digest-state fn-ew-buffer)) fn-ew-buffer))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (:instance fn-ewz-read-zero-window-preserves-private-buffer
    (z (fn-pww-controller fn-pww-carry))
    (effect (cadr (fn-pww-pending-action fn-pww-carry))))
  :in-theory (e/d (fn-dwc-read-observation) (fn-ewz-read fn-pwz-tokenp)))))
