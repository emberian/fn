; Packet 1 (profile monotonicity, Fable mandate §5.5 and §12): evaluated
; counterexamples.  Two findings, each at a profile the relation admits:
;   (1) the history gate charges an article at the fixed pre-reservation
;       figure 65 538 (`*fn-store-article-publication-figure*'), not at the
;       record the profile admits, so the gates can admit an article whose
;       committed total then exceeds H, and every later open refuses the store
;       (`fn-profile-replay-within-boundp', host/native/io.lisp
;       `fnn-durable-records');
;   (2) the truthful figure, the article record of (A, G), makes the history
;       gate depend on A and G, so raising A without H is an upgrade
;       (`fn-profile-upgradep') after which a verdict the old profile gave is
;       refused: `fn-profile-upgrade-keeps-verdict' does not hold of it.
(in-package "ACL2")
(include-book "../../books/store-profile-upgrade")
(include-book "../../books/codec-attach")

; A valid profile: T 4, H 250 000, R 196 608 (the minimum every kind needs),
; A 32 768, G 500.  Its article record ceiling is 164 351, within R.
(defconst *pmt-old*
  (fn-bs-profile-set-fields *fn-bs-profile-defaults*
                            '((2 . 4) (3 . 250000) (4 . 196608) (5 . 32768)
                              (6 . 500) (8 . 4))))
(assert-event (fn-bs-profile-validp *pmt-old*))
(assert-event (equal (fn-record-encoded-octets-ceiling 32768 500) 164351))

; An article at A in 400 groups of 255-octet names.
(defun pmt-name (i)
  (coerce (append (explode-atom (+ 100 i) 10)
                  (make-list 252 :initial-element #\a))
          'string))
(defun pmt-names (i n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil (cons (pmt-name i) (pmt-names (1+ i) (1- n)))))
(defconst *pmt-record*
  (fn-record-make 1 1 1 "<pmt@example.invalid>"
                  (make-list 32768 :initial-element 65)
                  (pmt-names 0 400) "archive-a" "content-a" "release-a" 9
                  841000000))
(defconst *pmt-len* (len (fn-record-encode-impl *pmt-record*)))
(assert-event (equal (len (fn-record-encode *pmt-record*)) *pmt-len*))
(assert-event (fn-record-p *pmt-record*))
(assert-event (not (fn-record-widep *pmt-record*)))
(assert-event (< 65538 *pmt-len*))

; (1) One article committed (1 000 octets); the owner's verdict for the next
; one charges the figure: 1 000 + 65 538 <= H, :admissible.  The article
; (A payload, 400 <= G groups) passes the publish gate's count-and-record
; check.  Committed, the total exceeds H, and the open refuses the store.
(defconst *pmt-used-octets* (- 250000 65538))
(assert-event (equal (fn-sbud-verdict-at *pmt-old* :article 1 *pmt-used-octets*)
                     :admissible))
(assert-event (<= (len (fn-record-payload *pmt-record*))
                  (fn-bs-profile-max-article-octets *pmt-old*)))
(assert-event (<= (len (fn-record-groups *pmt-record*))
                  (fn-bs-profile-max-groups-per-article *pmt-old*)))
(assert-event (fn-bs-publication-admissiblep *pmt-old* 1 *pmt-len*))
(assert-event (not (fn-profile-replay-within-boundp
                    *pmt-old* (+ *pmt-used-octets* *pmt-len*))))

; (2) The derived figure: the history gate at the article record of (A, G).
(defun pmt-derived-verdict-at (profile used bytes-used)
  (if (and (fn-sbud-admitp (fn-sbud-budget profile :article) used)
           (fn-bs-history-admissiblep
            profile bytes-used
            (fn-record-encoded-octets-ceiling
             (fn-bs-profile-max-article-octets profile)
             (fn-bs-profile-max-groups-per-article profile))))
      :admissible
    :unaffordable))
; It is truthful: at the bytes where it admits, the worst article fits H.
(assert-event (equal (pmt-derived-verdict-at *pmt-old* 1 (- 250000 164351))
                     :admissible))
(assert-event (fn-profile-replay-within-boundp
               *pmt-old* (+ (- 250000 164351) *pmt-len*)))
; NEW raises A to 60 000 and nothing else: a valid profile and an upgrade by
; `fn-profile-upgradep' (no field smaller).  Its article ceiling is 191 583.
(defconst *pmt-new* (fn-bs-profile-set-fields *pmt-old* '((5 . 60000))))
(assert-event (fn-bs-profile-validp *pmt-new*))
(assert-event (fn-profile-upgradep *pmt-old* *pmt-new*))
(assert-event (equal (fn-record-encoded-octets-ceiling 60000 500) 191583))
; The counterexample: the old profile admits, the upgraded one refuses.
(assert-event (equal (pmt-derived-verdict-at *pmt-old* 1 (- 250000 164351))
                     :admissible))
(assert-event (equal (pmt-derived-verdict-at *pmt-new* 1 (- 250000 164351))
                     :unaffordable))
; The fixed figure keeps the verdict (`fn-profile-upgrade-keeps-verdict'),
; at the price of (1).
(assert-event (equal (fn-sbud-verdict-at *pmt-new* :article 1
                                         (- 250000 164351))
                     :admissible))

; The two promises, separately.  Reopen: `fn-profile-upgradep' keeps the
; replay bound and the per-file read bound (H and R never shrink), so every
; existing store still opens under NEW.  Future admissibility: the derived
; verdict is kept when H grows by at least the figure's growth; with H
; raised by 27 232 (191 583 - 164 351) the same state is admitted again.
(defconst *pmt-new-h* (fn-bs-profile-set-fields *pmt-new* '((3 . 277232))))
(assert-event (fn-profile-upgradep *pmt-old* *pmt-new-h*))
(assert-event (equal (pmt-derived-verdict-at *pmt-new-h* 1 (- 250000 164351))
                     :admissible))
