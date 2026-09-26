;; Teeth for books/store-profile-open (PKT-471, D34): the open of a saved
;; profile in the poll reply's window is a named refusal, and so is the open
;; of a profile frame of another format.
(in-package "ACL2")
(include-book "../../books/store-profile-open")
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
; The line every open path prints names the refusal and the way out.
(assert-event (equal (fn-spo-refusal-text (fn-spo-config-open *spot-window-octets*))
                     "open refused reason=max-record-octets-above-the-poll-reply: the profile record bound exceeds the poll reply width; reinstall from the release and import"))
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
; Another format (fn-spo-config-open-store-format-is-exactly-a-foreign-frame)

; A format-7 store's config.json, built here: the sealed FNSM config frame
; whose first text field is fn-store-experiment-7, then N=1048576, B=32768,
; H=25165824, T=128 and the frontier format (the development tuple the
; format-7 encoder wrote).  A function: a defconst cannot evaluate the
; attached digest.
(defconst *spot-fmt7-word*
  '(102 110 45 115 116 111 114 101 45 101 120 112 101 114 105 109 101 110 116 45 55))
(defun spot-codes (chars)
  (if (consp chars) (cons (char-code (car chars)) (spot-codes (cdr chars))) nil))
(assert-event (equal *spot-fmt7-word*
                     (spot-codes (coerce "fn-store-experiment-7" 'list))))
(defun spot-format-7-frame ()
  (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version* *fn-bs-meta-config-kind*
                 (fn-frame-fields-octets '(:text :nat :nat :nat :nat :text)
                                         (list *spot-fmt7-word* 1048576 32768
                                               25165824 128
                                               *fn-bs-meta-frontier-format*))))

; Reachable witness, the right side true: not in the window, not decoded,
; a foreign format word; the open refuses by the format's name, and the
; line says what to do.
(assert-event (null (fn-spo-saved-format-8 (spot-format-7-frame))))
(assert-event (null (fn-bs-config-decode (spot-format-7-frame))))
(assert-event (equal (fn-spo-saved-format-word (spot-format-7-frame)) *spot-fmt7-word*))
(assert-event (fn-spo-foreign-formatp (spot-format-7-frame)))
(assert-event (equal (fn-spo-config-open (spot-format-7-frame))
                     '(:refused :store-format)))
(assert-event (equal (fn-spo-refusal-text (fn-spo-config-open (spot-format-7-frame)))
                     "open refused reason=store-format: reinstall from the release and import"))

; Reachable witnesses, the right side false, one per conjunct.
; A valid frame decodes: it opens.
(assert-event (fn-bs-config-decode (fn-bs-config-encode *fn-bs-profile-scale*)))
(assert-event (not (fn-spo-foreign-formatp (fn-bs-config-encode *fn-bs-profile-scale*))))
; The window frame is in the window: the window's refusal, not the format's.
(assert-event (fn-spo-in-the-windowp (fn-spo-saved-format-8 *spot-window-octets*)))
(assert-event (not (equal (fn-spo-config-open *spot-window-octets*)
                          '(:refused :store-format))))
; A fn-store-8 frame the decoder refuses (H below R) is not foreign: the fault.
(assert-event (equal (fn-spo-saved-format-word (fn-spo-saved-frame *spot-short-history*))
                     *fn-bs-meta-format-8*))
(assert-event (not (fn-spo-foreign-formatp (fn-spo-saved-frame *spot-short-history*))))
; Octets that are no frame at all have no format word: the fault.
(defconst *spot-garbage* '(1 2 3 4 5 6 7 8 9 10))
(assert-event (null (fn-spo-saved-format-word *spot-garbage*)))
(assert-event (equal (fn-spo-config-open *spot-garbage*) '(:rejected)))
(assert-event (null (fn-spo-refusal-text (fn-spo-config-open *spot-garbage*))))
; A format-7 frame whose trailer is corrupted is not a sealed frame: the fault.
(assert-event
 (equal (fn-spo-config-open
         (let ((f (spot-format-7-frame)))
           (update-nth 20 (logxor 1 (nth 20 f)) f)))
        '(:rejected)))
