; Teeth for books/byte-store-profile-v1 (packet P6): a format-8 profile saved
; by the image before P6 is admitted, unchanged, by this one.
(in-package "ACL2")
(include-book "../../books/byte-store-profile-v1")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; The scale and development profiles as the image before P6 saved them: the
; format-7 translations, R = 17 138 486 (the article record of A = 32 768 and
; G = 65 535 at the 1 083-octet overhead), the namespace counts 2^20 and the
; history requirement `unmarked'.  Written out, not computed, so a change to
; the presets does not move the witness with them.
(defconst *bspv1-saved-scale*
  (list *fn-bs-meta-format-8* *fn-bs-meta-frontier-format*
        4096 805306368 17138486 32768 65535 256 4096
        1048576 1048576 1048576 1048576 1048576 0))
(defconst *bspv1-saved-development*
  (list *fn-bs-meta-format-8* *fn-bs-meta-frontier-format*
        128 25165824 17138486 32768 65535 256 128
        1048576 1048576 1048576 1048576 1048576 0))

; Non-degenerate witness: the old relation admits both; this image admits
; them, runs the store under them unchanged, and reads their saved frames
; back to them (the open path, `fn-bs-config-decode').  The presets this
; image writes are the same values.
(assert-event (not (fn-bs-profile-v1-invalid-reason *bspv1-saved-scale*)))
(assert-event (not (fn-bs-profile-v1-invalid-reason *bspv1-saved-development*)))
(assert-event (fn-bs-profile-admittedp *bspv1-saved-scale*))
(assert-event (fn-bs-profile-admittedp *bspv1-saved-development*))
(assert-event (equal (fn-bs-profile-of *bspv1-saved-scale*) *bspv1-saved-scale*))
(assert-event (equal (fn-bs-config-decode (fn-bs-config-encode *bspv1-saved-scale*))
                     *bspv1-saved-scale*))
(assert-event (equal (fn-bs-config-decode
                      (fn-bs-config-encode *bspv1-saved-development*))
                     *bspv1-saved-development*))
(assert-event (equal *fn-bs-profile-scale* *bspv1-saved-scale*))
(assert-event (equal *fn-bs-profile-development* *bspv1-saved-development*))
; R is tight there: the article record of (A, G) is exactly R.
(assert-event (equal (fn-record-encoded-octets-ceiling 32768 65535) 17138486))
; The live node's format-7 store translates to the same R.
(assert-event (equal (fn-bs-profile-record-ceiling
                      *fn-bs-meta-format-7-scale-values*) 17138486))

; What the fix repairs: at the wide overhead (every uint head at 9 octets,
; P6's first cut) the article record of (A, G) is 17 138 514, 28 octets past
; the saved R, so a relation reading that ceiling refused both profiles.
(assert-event (equal (fn-record-wide-encoded-octets-ceiling 32768 65535)
                     17138514))
(assert-event (< 17138486 (fn-record-wide-encoded-octets-ceiling 32768 65535)))

; The hypothesis: one octet below R the old relation refuses the profile by
; name, and so does this image; the conclusion fails at that value, so it is
; not a fact about every value.
(defconst *bspv1-short-scale*
  (fn-bs-profile-set-fields *bspv1-saved-scale* '((4 . 17138485))))
(assert-event (equal (fn-bs-profile-v1-invalid-reason *bspv1-short-scale*)
                     :max-record-octets-below-the-article-record))
(assert-event (not (fn-bs-profile-admittedp *bspv1-short-scale*)))
(must-fail
 (thm (implies (equal values *bspv1-short-scale*)
               (fn-bs-profile-admittedp values))))

; PKT-467's hypothesis on the two theorems: a profile the old relation admits
; with R one octet past the poll reply's report ceiling (H raised with it).
; The old relation admits it; this image refuses it by the new name, so the
; conclusion of fn-bs-profile-v1-valid-stays-valid fails without the
; hypothesis, and fn-bs-profile-v1-valid-above-the-poll-reply-is-refused-by-name
; holds of it.  The saved presets satisfy the hypothesis (R 17 138 486).
(defconst *bspv1-poll-window*
  (fn-bs-profile-set-fields *bspv1-saved-scale*
                            '((4 . 4294966941) (3 . 4294966941))))
(assert-event (not (fn-bs-profile-v1-invalid-reason *bspv1-poll-window*)))
(assert-event (< *fn-stxa-max-octets* (fn-bs-pf 4 *bspv1-poll-window*)))
(assert-event (equal (fn-bs-profile-invalid-reason *bspv1-poll-window*)
                     :max-record-octets-above-the-poll-reply))
(assert-event (not (fn-bs-profile-admittedp *bspv1-poll-window*)))
(assert-event (<= (fn-bs-pf 4 *bspv1-saved-scale*) *fn-stxa-max-octets*))
(assert-event (<= (fn-bs-pf 4 *bspv1-saved-development*) *fn-stxa-max-octets*))
(must-fail
 (thm (implies (equal values *bspv1-poll-window*)
               (fn-bs-profile-admittedp values))))
; At the ceiling itself the old relation's profile stays admitted.
(defconst *bspv1-poll-top*
  (fn-bs-profile-set-fields *bspv1-saved-scale*
                            '((4 . 4294966940) (3 . 4294966940))))
(assert-event (not (fn-bs-profile-v1-invalid-reason *bspv1-poll-top*)))
(assert-event (fn-bs-profile-admittedp *bspv1-poll-top*))
