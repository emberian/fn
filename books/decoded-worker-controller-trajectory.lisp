; Proof candidate for the actual registered decoded controller, not another
; hosted decoder. Requires physical owner's frozen controller closure.
(in-package "ACL2")
(include-book "decoded-worker-controller")
(include-book "decoded-window-digest-trajectory")
(include-book "decoded-window-budget-trajectory")

(local
 (defthm fn-dwct-codec-retains-raw-plan
  (equal (nth 1 (mv-nth 1 (fn-ewz-codec-tick z fn-octets fn-zin-st
                   fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
         (nth 1 z))
  :hints (("Goal" :do-not-induct t
   :in-theory (e/d (fn-ewz-codec-tick fn-ewz-state)
    (fn-pzw-stored-chunk fn-pzw-select fn-ewb-copy fn-pzw-budget-left
     fn-pzw-stored-decision fn-ewz-compressed-completep fn-ewz-decision-mode))))))

; Even a stale/refused/no-I/O turn retains the actual captured-source digest.
; CODEC does not touch its digest child; TICK uses the actual EWZ hash step.
; READ issuance cannot overwrite input or authenticate a native supplied tuple.
(defthm fn-dwct-actual-one-preserves-captured-source-digest
 (implies
  (pgs-dcs-invariantp limit
    (nth 3 (nth 1 (fn-pww-controller fn-pww-carry))) msg pgs-digest-state)
  (let ((r (fn-dwc-one token fn-pww-carry fn-octets pgs-digest-state
                       fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
   (pgs-dcs-invariantp limit
    (nth 3 (nth 1 (fn-pww-controller (mv-nth 2 r)))) msg (mv-nth 4 r))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pwdg-actual-compressed-hash-preserves-digest-trajectory
         (z (fn-pww-controller fn-pww-carry)))
        (:instance fn-dwct-codec-retains-raw-plan
         (z (fn-pww-controller fn-pww-carry))))
  :in-theory
  (e/d (fn-dwc-one)
       (pgs-dcs-invariantp fn-ewz-next-action fn-ewz-hash-tick fn-ewz-codec-tick
        fn-pzw-stored-chunk fn-pzw-select fn-ewb-copy fn-pzw-budget-left
        fn-pzw-stored-decision fn-ewz-compressed-completep fn-ewz-decision-mode)))))

(local
 (defthm fn-dwct-codec-action-implies-codec-mode-by-definition
  (implies (equal (car (fn-ewz-next-action z pgs-digest-state)) :codec)
           (equal (nth 0 z) :codec))
  :hints (("Goal" :in-theory (e/d (fn-ewz-next-action)
             (fn-ewz-publication fn-ewz-effect))))))

; The registered actual turn carries one selected cell and its full produced
; position. Authorization is the CURRENT carry; PREFIX is prior semantic
; output, not an assumed decoder answer. No native buffer identity follows.
(defthm fn-dwct-actual-codec-one-carries-selected-prefix
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
        (<= (nth 7 z) (fn-octets-len fn-octets))
        (natp (nth 3 z)) (natp (nth 4 z)) (<= (nth 4 z) 16384)
        (natp j) (equal (fn-zin-tout fn-zin-st) (len prefix))
        (equal (len fn-zin-win) *fn-zin-win-octets*)
        (equal (len fn-zin-tab) *fn-zin-tab-octets*)
        (implies (and (< j (nth 4 z)) (< (+ (nth 3 z) j) (len prefix)))
                 (equal (nth j (nth 0 fn-ew-buffer))
                        (nth (+ (nth 3 z) j) prefix))))
   (let* ((scratch (mv-nth 6 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                       (nth 12 (nth 1 z)) (nth 2 z)
                       fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          (model (append prefix scratch))
          (r (fn-dwc-one token fn-pww-carry fn-octets pgs-digest-state
                        fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
    (and (equal (fn-zin-tout (mv-nth 5 r)) (len model))
         (implies (and (< j (nth 4 z)) (< (+ (nth 3 z) j) (len model)))
                  (equal (nth j (nth 0 (mv-nth 9 r)))
                         (nth (+ (nth 3 z) j) model)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pws-actual-codec-tick-carries-selected-prefix
         (z (fn-pww-controller fn-pww-carry)))
        (:instance fn-dwct-codec-action-implies-codec-mode-by-definition
         (z (fn-pww-controller fn-pww-carry))))
  :in-theory (e/d (fn-dwc-one)
                 (fn-ewz-next-action fn-ewz-codec-tick fn-ewz-hash-tick
                  fn-pzw-stored-chunk fn-pwz-tokenp
                  fn-pzw-stored-chunk-is-resumable-run fn-zin-feed-unfolds
                  fn-zin-loop fn-zin-run fn-zin-loop-counts fn-pzw-quantum
                  fn-pzw-room fn-pzw-stored-allowance fn-pzw-budget-left
                  fn-pzw-stored-decision fn-pzw-select fn-ewb-copy
                  fn-dwct-codec-action-implies-codec-mode-by-definition nfix min)))))

; This is the logical charged STEP-budget carry, not a native allocation or
; workspace allowance. Refused codec status remains a distinct exclusion.
(defthm fn-dwct-actual-one-preserves-charged-budget-carry
 (let* ((z (fn-pww-controller fn-pww-carry))
        (r (fn-dwc-one token fn-pww-carry fn-octets pgs-digest-state
                      fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))
        (next (fn-pww-controller (mv-nth 2 r))))
  (implies
   (and (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st)
        (not (consp (nth 8 next))))
   (fn-pwz-budget-carryp (nth 12 (nth 1 next)) (nth 2 next) (nth 5 next) (mv-nth 5 r))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pwz-actual-codec-carries-budget
          (z (fn-pww-controller fn-pww-carry)))
        (:instance fn-pwz-actual-compressed-hash-tick-preserves-budget-carry
          (z (fn-pww-controller fn-pww-carry))))
  :in-theory (e/d (fn-dwc-one)
                 (fn-pwz-budget-carryp fn-ewz-next-action fn-ewz-codec-tick
                  fn-ewz-hash-tick fn-pwz-tokenp
                  fn-pwz-actual-compressed-hash-tick-preserves-budget-carry)))))

; Actual CURRENT receipt completion preserves faithful source hashing. The
; supplied octets must be the captured issued source slice on raw scan; that
; equality is the explicit physical I/O obligation, not a native assumption.
(defthm fn-dwct-actual-read-observation-preserves-captured-source-digest
 (let ((z (fn-pww-controller fn-pww-carry)))
  (implies
   (and (pgs-dcs-invariantp limit (nth 3 (nth 1 z)) msg pgs-digest-state)
        (implies (equal (nth 0 (nth 1 z)) :scan)
                 (equal fn-octets (fn-shr-win (nth 7 (nth 1 z)) (fn-ewp-demand (nth 1 z)) msg))))
   (let ((r (fn-dwc-read-observation token revision io-status fn-pww-carry
                                   fn-octets pgs-digest-state fn-ew-buffer)))
    (pgs-dcs-invariantp limit
     (nth 3 (nth 1 (fn-pww-controller (mv-nth 1 r)))) msg (mv-nth 3 r)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (:instance fn-pwdg-actual-compressed-read-preserves-digest-trajectory
         (z (fn-pww-controller fn-pww-carry))
         (effect (cadr (fn-pww-pending-action fn-pww-carry))))
  :in-theory (e/d (fn-dwc-read-observation)
                 (pgs-dcs-invariantp fn-ewz-read fn-shr-win fn-ewp-demand fn-pwz-tokenp)))))
