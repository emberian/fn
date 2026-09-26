;; Teeth for books/store-profile-open (PKT-471): the open of a saved profile
;; in the poll reply's window is a named refusal, and the one repair.
(in-package "ACL2")
(include-book "../../books/store-profile-open")
(include-book "../../books/native-operator")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; The witness store's profile, BY HAND: the scale preset's fields with R at
; the codec's u32 (4 294 967 295, the old relation's ceiling) and H raised
; with it.  Written out, not computed from a preset.
(defconst *spot-window*
  (list *fn-bs-meta-format-8* *fn-bs-meta-frontier-format*
        4096 4294967295 4294967295 32768 65535 256 4096
        1048576 1048576 1048576 1048576 1048576 0))

; Its config.json, octet for octet: the FNSM frame the format-8 encoder wrote
; under the relation before PKT-467 (magic, version 1, kind 1, the u32
; payload length 148, the two texts, thirteen u64 fields, the SHA-256
; trailer).  tests/test_native_control_reply_fit.py writes the same octets.
(defconst *spot-window-octets*
  '(
    70 78 83 77 1 1 0 0 0 148 0 10 102 110 45 115
    116 111 114 101 45 56 0 30 102 110 45 115 116 111 114 101
    45 97 108 108 111 99 97 116 105 111 110 45 102 114 111 110
    116 105 101 114 45 50 0 0 0 0 0 0 16 0 0 0
    0 0 255 255 255 255 0 0 0 0 255 255 255 255 0 0
    0 0 0 0 128 0 0 0 0 0 0 0 255 255 0 0
    0 0 0 0 1 0 0 0 0 0 0 0 16 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 0 0 0 48 240
    243 102 208 195 151 137 84 88 154 142 3 226 22 4 80 206
    44 194 4 53 39 56 56 72 73 34 203 142 157 18))

(assert-event (equal (len *spot-window-octets*) 190))
(assert-event (equal (fn-spo-saved-frame *spot-window*) *spot-window-octets*))

; -----------------------------------------------------------------------------
; The open (fn-spo-open-of-a-saved-format-8-profile-opens-or-refuses-by-name)

; Reachable witness, the complete antecedent: the old relation admitted the
; profile; its R is above the ceiling; the current relation refuses it by
; the window's name; the open refuses by that name.
(assert-event (fn-bs-profile-v2-validp *spot-window*))
(assert-event (< *fn-stxa-max-octets* (fn-bs-pf 4 *spot-window*)))
(assert-event (equal (fn-bs-profile-invalid-reason *spot-window*)
                     :max-record-octets-above-the-poll-reply))
(assert-event (equal (fn-spo-config-open *spot-window-octets*)
                     '(:refused :max-record-octets-above-the-poll-reply)))
; What the open answered before (the generic fault): the decoder refuses it.
(assert-event (null (fn-bs-config-decode *spot-window-octets*)))
; The line every open path prints names the repair and the width.
(assert-event (equal (fn-spo-refusal-text (fn-spo-config-open *spot-window-octets*))
                     "profile record bound exceeds the poll reply width: run store upgrade-profile --max-record-octets 4294966940"))
(assert-event (search "4294966940" (fn-spo-refusal-text
                                     '(:refused :max-record-octets-above-the-poll-reply))))
(assert-event (equal *fn-stxa-max-octets* 4294966940))

; The other half: at the ceiling the saved profile opens, as itself.
(defconst *spot-ceiling* (fn-bs-profile-put 4 4294966940 *spot-window*))
(assert-event (fn-bs-profile-v2-validp *spot-ceiling*))
(assert-event (equal (fn-spo-config-open (fn-spo-saved-frame *spot-ceiling*))
                     (list :opened *spot-ceiling*)))
; The presets and the defaults open as themselves (the refinement: the old
; open's answer).
(assert-event (equal (fn-spo-config-open (fn-bs-config-encode *fn-bs-profile-scale*))
                     (list :opened *fn-bs-profile-scale*)))
(assert-event (equal (fn-spo-config-open (fn-bs-config-encode *fn-bs-profile-defaults*))
                     (list :opened *fn-bs-profile-defaults*)))
(assert-event (equal (fn-spo-config-open (fn-bs-initial-config-octets))
                     (list :opened *fn-bs-profile-development*)))
; A format-7 frame opens as its tuple, as before (the refinement theorem
; fn-spo-config-open-refuses-only-what-the-old-open-rejected; the store runs
; under its translation).
(defun spot-format-7-frame (values)
  (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                 *fn-bs-meta-config-kind*
                 (fn-frame-fields-octets *fn-bs-meta-format-7-spec* values)))
(assert-event (equal (fn-spo-config-open
                      (spot-format-7-frame *fn-bs-meta-format-7-scale-values*))
                     (list :opened *fn-bs-meta-format-7-scale-values*)))

; Hypothesis removed (fn-bs-profile-v2-validp): R in the window but H one
; octet below it.  Retained hypothesis holds (R above the ceiling); the
; omitted one fails (the old relation refused it); the conclusion fails: the
; open answers the fault, not the name.
(defconst *spot-short-history*
  (fn-bs-profile-put 3 4294967294 *spot-window*))
(assert-event (< *fn-stxa-max-octets* (fn-bs-pf 4 *spot-short-history*)))
(assert-event (equal (fn-bs-profile-v2-invalid-reason *spot-short-history*)
                     :max-history-octets-below-max-record-octets))
(assert-event (equal (fn-spo-config-open (fn-spo-saved-frame *spot-short-history*))
                     '(:rejected)))
(must-fail
 (thm (implies (equal values *spot-short-history*)
               (equal (fn-spo-config-open (fn-spo-saved-frame values))
                      (if (<= (fn-bs-pf 4 values) *fn-stxa-max-octets*)
                          (list :opened values)
                        (list :refused :max-record-octets-above-the-poll-reply))))))

; CORRUPTED-state witness (not a saved profile): the window frame with one
; payload octet changed fails its trailer, and the open answers :rejected
; (the host's fault, as before), not the name.
(defconst *spot-corrupted*
  (update-nth 60 (logxor 1 (nth 60 *spot-window-octets*)) *spot-window-octets*))
(assert-event (not (equal *spot-corrupted* *spot-window-octets*)))
(assert-event (equal (fn-spo-config-open *spot-corrupted*) '(:rejected)))

; -----------------------------------------------------------------------------
; The repair (fn-spo-repair-admits-exactly-the-lowering-to-the-width)

; `store upgrade-profile --max-record-octets 4294966940' parses to the
; repair request (books/native-operator.lisp fn-nop-parse-store).
(assert-event (equal (car (fn-nop-parse-profile-flags
                           '("--max-record-octets" "4294966940") :current nil nil))
                     *fn-spo-repair-request*))

; Reachable witness: the window frame and that request: the verdict writes a
; frame, the next open opens it as the saved profile with R lowered, H and
; every other field kept.
; (A defconst cannot evaluate the attached digest, so each check calls it.)
(assert-event (equal (car (fn-spo-repair-verdict *spot-window-octets*
                                                 *fn-spo-repair-request*))
                     :repair))
(assert-event (equal (fn-spo-config-open
                      (cadr (fn-spo-repair-verdict *spot-window-octets*
                                                   *fn-spo-repair-request*)))
                     (list :opened (fn-spo-repaired *spot-window*))))
(assert-event (equal (fn-spo-repaired *spot-window*) *spot-ceiling*))
(assert-event (equal (fn-bs-pf 3 (fn-spo-repaired *spot-window*)) 4294967295))
(assert-event (fn-bs-profile-validp (fn-spo-repaired *spot-window*)))

; Every other target over the window store is refused by name, writing
; nothing: one octet lower, the old R, a preset, and a second field.
(assert-event (equal (fn-spo-repair-verdict *spot-window-octets*
                                            '(:current ((4 . 4294966939))))
                     '(:refused :repair-lowers-max-record-octets-to-the-poll-reply-only)))
(assert-event (equal (car (fn-spo-repair-verdict *spot-window-octets* :scale)) :refused))
(assert-event (equal (car (fn-spo-repair-verdict
                           *spot-window-octets*
                           '(:current ((4 . 4294966940) (2 . 8192)))))
                     :refused))
; A store that opens is not repaired (the upgrade verdict is its verb).
(assert-event (equal (fn-spo-repair-verdict (fn-bs-config-encode *fn-bs-profile-scale*)
                                            *fn-spo-repair-request*)
                     '(:refused :not-above-the-poll-reply)))
(assert-event (equal (fn-spo-repair-verdict (fn-spo-saved-frame *spot-ceiling*)
                                            *fn-spo-repair-request*)
                     '(:refused :not-above-the-poll-reply)))

; Hypothesis removed (fn-bs-profile-v2-validp): over the short-history frame
; R is above the ceiling and the target is the request, yet the verdict
; refuses: the keystone's equivalence fails without the hypothesis.
(assert-event (equal (car (fn-spo-repair-verdict (fn-spo-saved-frame *spot-short-history*)
                                                 *fn-spo-repair-request*))
                     :refused))
(must-fail
 (thm (implies (equal saved *spot-short-history*)
               (equal (equal (car (fn-spo-repair-verdict
                                   (fn-spo-saved-frame saved) *fn-spo-repair-request*))
                             :repair)
                      (and (< *fn-stxa-max-octets* (fn-bs-pf 4 saved))
                           (equal *fn-spo-repair-request* *fn-spo-repair-request*))))))

; The upgrade relation is unchanged: lowering R is still not an upgrade of
; an admitted profile (the exception lives only in the repair verdict).
(assert-event (equal (fn-profile-upgrade-verdict *fn-bs-profile-defaults*
                                                 '(:current ((4 . 17847355))))
                     '(:refused :not-an-upgrade "max-record-octets")))
; The upgrade verdict over the window profile refuses (it is not admitted).
(assert-event (equal (fn-profile-upgrade-verdict *spot-window* *fn-spo-repair-request*)
                     '(:refused :invalid-current-profile)))
