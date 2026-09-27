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
        1048576 1048576 1048576 1048576 1048576 0
        64 256 16384))

; Its config.json, octet for octet: the FNSM frame the format-8 encoder wrote
; under the relation before PKT-467 (magic, version 1, kind 1, the u32
; payload length 172, the two texts, sixteen u64 fields, the SHA-256
; trailer).  tests/test_native_control_reply_fit.py writes the same octets.
(defconst *spot-window-octets*
  '(
    70 78 83 77 1 1 0 0 0 172 0 10 102 110 45 115
    116 111 114 101 45 56 0 30 102 110 45 115 116 111 114 101
    45 97 108 108 111 99 97 116 105 111 110 45 102 114 111 110
    116 105 101 114 45 50 0 0 0 0 0 0 16 0 0 0
    0 0 255 255 255 255 0 0 0 0 255 255 255 255 0 0
    0 0 0 0 128 0 0 0 0 0 0 0 255 255 0 0
    0 0 0 0 1 0 0 0 0 0 0 0 16 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 0 0 0 0 0
    0 0 0 0 0 64 0 0 0 0 0 0 1 0 0 0
    0 0 0 0 64 0 121 139 102 61 92 206 2 20 187 88
    114 29 128 147 96 135 218 253 203 152 133 61 46 249 28 121
    15 221 14 210 22 11))

(assert-event (equal (len *spot-window-octets*) 214))
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
; Under the record log's word it opens as itself; under the per-file
; layout's (format 8, D34 after PKT-COL-1) it is refused by the format's name.
(defconst *spot-ceiling*
  (fn-bs-profile-put 4 4294966940 (cons *fn-bs-meta-format-9* (cdr *spot-window*))))
(assert-event (fn-bs-profile-v2-validp *spot-ceiling*))
(assert-event (equal (fn-spo-config-open (fn-spo-saved-frame *spot-ceiling*))
                     (list :opened *spot-ceiling*)))
(defconst *spot-ceiling-8* (fn-bs-profile-put 4 4294966940 *spot-window*))
(assert-event (fn-bs-profile-v2-validp *spot-ceiling-8*))
(assert-event (equal (fn-spo-config-open (fn-spo-saved-frame *spot-ceiling-8*))
                     '(:refused :store-format)))
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
                          (if (equal (car values) *fn-bs-meta-format-9*)
                              (list :opened values)
                            (list :refused :store-format))
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

; Its octets (129), written out: tests/older_release_store.py writes the same
; file as the config.json of a synthesized format-7 store.
(defconst *spot-format-7-octets*
  '(
    70 78 83 77 1 1 0 0 0 87 0 21 102 110 45 115
    116 111 114 101 45 101 120 112 101 114 105 109 101 110 116 45
    55 0 0 0 0 0 16 0 0 0 0 0 0 0 0 128
    0 0 0 0 0 1 128 0 0 0 0 0 0 0 0 0
    128 0 30 102 110 45 115 116 111 114 101 45 97 108 108 111
    99 97 116 105 111 110 45 102 114 111 110 116 105 101 114 45
    50 236 231 127 192 153 44 184 72 173 60 49 58 185 189 124
    69 192 134 19 202 227 175 86 144 55 35 230 236 93 118 46
    173))
(assert-event (equal (spot-format-7-frame) *spot-format-7-octets*))

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

; -----------------------------------------------------------------------------
; Format 9 (lane commit-onto-log): the preset profiles are format 9 and name
; the record log as their commit route; the same values in the per-file
; layout (format 8) are valid profiles too (the decoder reads them, for the
; import's migration) and name the files; a format-9 frame decodes, opens and
; is not foreign.
(defun spot-as-format-8 (values) (cons *fn-bs-meta-format-8* (cdr values)))
(assert-event (equal (car *fn-bs-profile-scale*) *fn-bs-meta-format-9*))
(assert-event (fn-bs-profile-validp *fn-bs-profile-scale*))
(assert-event (fn-bs-profile-logp *fn-bs-profile-scale*))
(assert-event (fn-bs-profile-validp (spot-as-format-8 *fn-bs-profile-scale*)))
(assert-event (not (fn-bs-profile-logp (spot-as-format-8 *fn-bs-profile-scale*))))
(assert-event (equal (fn-spo-config-open (fn-bs-config-encode *fn-bs-profile-scale*))
                     (list :opened *fn-bs-profile-scale*)))
(assert-event (not (fn-spo-foreign-formatp
                    (fn-bs-config-encode (spot-as-format-8 *fn-bs-profile-scale*)))))

; A format-8 store (fn-spo-open-of-a-format-8-profile-refuses-by-name, and
; the decoded-branch half of fn-spo-config-open-store-format-is-exactly-a-
; foreign-frame).  The config.json every format-8 store of the development
; preset carried (`init --profile development' before lane commit-onto-log:
; sha256 61802dbb..., tests/native_profile_fixture.py's old DEVELOPMENT_FRAME),
; octet for octet; tests/older_release_store.py writes the same file as a
; synthesized format-8 store's config.json.
(defconst *spot-format-8-octets*
  '(
    70 78 83 77 1 1 0 0 0 172 0 10 102 110 45 115
    116 111 114 101 45 56 0 30 102 110 45 115 116 111 114 101
    45 97 108 108 111 99 97 116 105 111 110 45 102 114 111 110
    116 105 101 114 45 50 0 0 0 0 0 0 0 128 0 0
    0 0 1 128 0 0 0 0 0 0 1 5 131 54 0 0
    0 0 0 0 128 0 0 0 0 0 0 0 255 255 0 0
    0 0 0 0 1 0 0 0 0 0 0 0 0 128 0 0
    0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 0 0 0 0 0
    0 0 0 0 0 64 0 0 0 0 0 0 1 0 0 0
    0 0 0 0 64 0 111 175 234 85 87 2 35 102 237 1
    113 126 80 157 84 219 244 161 139 149 192 230 72 133 110 142
    218 91 176 40 45 100))
(assert-event (equal (len *spot-format-8-octets*) 214))
(assert-event (equal (fn-bs-config-encode (spot-as-format-8 *fn-bs-profile-development*))
                     *spot-format-8-octets*))
; Reachable witness, the complete antecedent: a valid profile whose word is
; not fn-store-9; the conclusion: the open refuses it by the format's name,
; and the line names the way out.  The decoder still reads it (the import's
; migration reads the same values).
(assert-event (fn-bs-profile-validp (spot-as-format-8 *fn-bs-profile-development*)))
(assert-event (not (equal (car (spot-as-format-8 *fn-bs-profile-development*))
                          *fn-bs-meta-format-9*)))
(assert-event (equal (fn-spo-config-open *spot-format-8-octets*) '(:refused :store-format)))
(assert-event (equal (fn-bs-config-decode *spot-format-8-octets*)
                     (spot-as-format-8 *fn-bs-profile-development*)))
(assert-event (equal (fn-spo-refusal-text (fn-spo-config-open *spot-format-8-octets*))
                     "open refused reason=store-format: reinstall from the release and import"))
; Hypothesis removed (the word): the development preset itself (format 9) is
; valid and opens: the conclusion fails.
(assert-event (fn-bs-profile-validp *fn-bs-profile-development*))
(assert-event (equal (car *fn-bs-profile-development*) *fn-bs-meta-format-9*))
(assert-event (equal (fn-spo-config-open (fn-bs-config-encode *fn-bs-profile-development*))
                     (list :opened *fn-bs-profile-development*)))
(must-fail
 (with-prover-step-limit 20000 (thm (implies (and (equal values *fn-bs-profile-development*)
                    (fn-bs-profile-validp values))
               (equal (fn-spo-config-open (fn-bs-config-encode values))
                      (list :refused :store-format))))))
; Hypothesis removed (validity): the format-8 word over fields whose H is
; below R: the retained hypothesis holds, the profile is invalid, and the open
; answers the generic fault, not the format's name.
(defconst *spot-format-8-short*
  (fn-bs-profile-put 3 1 (spot-as-format-8 *fn-bs-profile-development*)))
(assert-event (not (equal (car *spot-format-8-short*) *fn-bs-meta-format-9*)))
(assert-event (not (fn-bs-profile-validp *spot-format-8-short*)))
(assert-event (equal (fn-spo-config-open (fn-spo-saved-frame *spot-format-8-short*))
                     '(:rejected)))
(must-fail
 (with-prover-step-limit 20000 (thm (implies (and (equal values *spot-format-8-short*)
                    (not (equal (car values) *fn-bs-meta-format-9*)))
               (equal (fn-spo-config-open (fn-spo-saved-frame values))
                      (list :refused :store-format))))))
; A value that is not a profile names no route.
(assert-event (not (fn-bs-profile-logp '(1 2 3))))
(assert-event (equal (cdr (assoc-equal "format" (fn-bs-profile-report *fn-bs-profile-scale*))) 9))
; Another layout (PKT-705: fn-spo-open-of-another-layout-refuses-by-name)

; The layouts, by hand: the one before batch AS (13 u64 fields) and this
; release's (16, the profile spec itself).
(assert-event (equal (fn-spo-layout-spec 13)
                     '(:text :text :nat :nat :nat :nat :nat :nat :nat :nat :nat
                       :nat :nat :nat :nat)))
(assert-event (equal (fn-spo-layout-spec 16) *fn-bs-meta-profile-spec*))
(assert-event (equal *fn-spo-release-layout-fields* 16))

; A store made before batch AS: hbox:/tank/fn/scratch/fixtures/n1k-2k/store/
; config.json, octet for octet (190 octets; the default profile, written by
; the throughput gate's developer image of dev 6407de336): the FNSM frame,
; payload length 148 = the two texts (44) and thirteen u64 fields (104).
(defconst *spot-pre-as-octets*
  '(70 78 83 77 1 1 0 0 0 148 0 10 102 110 45 115
    116 111 114 101 45 56 0 30 102 110 45 115 116 111 114 101
    45 97 108 108 111 99 97 116 105 111 110 45 102 114 111 110
    116 105 101 114 45 50 0 0 0 0 255 255 255 255 0 0
    1 0 0 0 0 0 0 0 0 0 4 0 0 0 0 0
    0 0 1 0 0 0 0 0 0 0 0 0 16 0 0 0
    0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 0 0 0 70 112
    111 138 38 173 76 99 249 65 234 23 184 118 203 76 223 145
    252 221 169 197 118 171 16 149 10 151 172 203 171 232))

; Its values, by hand (the u64 fields read off the octets above).
(defconst *spot-pre-as*
  (list *fn-bs-meta-format-8* *fn-bs-meta-frontier-format*
        4294967295 1099511627776 67108864 16777216 4096 256 65536
        1048576 1048576 1048576 1048576 1048576 0))

(assert-event (equal (len *spot-pre-as-octets*) 190))
(assert-event (equal (fn-spo-layout-frame 13 *spot-pre-as*) *spot-pre-as-octets*))

; Reachable witness, the complete antecedent and conclusion.
(assert-event (natp 13))
(assert-event (not (equal 13 *fn-spo-release-layout-fields*)))
(assert-event (fn-frame-values-okp (fn-spo-layout-spec 13) *spot-pre-as*))
(assert-event (equal (car *spot-pre-as*) *fn-bs-meta-format-8*))
(assert-event (<= (len (fn-frame-fields-octets (fn-spo-layout-spec 13) *spot-pre-as*))
                  *fn-bs-meta-max-config-payload*))
(assert-event (equal (fn-spo-layout-fields *spot-pre-as-octets*) 13))
(assert-event (equal (fn-spo-config-open *spot-pre-as-octets*)
                     '(:refused :profile-layout 13)))
; What the open answered before (the generic fault): the decoder refuses it,
; and it is no foreign format and not in the window.
(assert-event (null (fn-bs-config-decode *spot-pre-as-octets*)))
(assert-event (null (fn-spo-saved-format-8 *spot-pre-as-octets*)))
(assert-event (not (fn-spo-foreign-formatp *spot-pre-as-octets*)))
; The line every open path prints: the cause and the way out (D34).
(assert-event
 (equal (fn-spo-refusal-text (fn-spo-config-open *spot-pre-as-octets*))
        "open refused reason=older-release: store made by an older release (profile layout 13 fields, this release expects 16): export it with the release that made it, then import it here"))

; A layout wider than this release's is refused by the other name.
(defconst *spot-wider* (append *spot-pre-as* '(1 2 3 4)))
(assert-event (fn-frame-values-okp (fn-spo-layout-spec 17) *spot-wider*))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame 17 *spot-wider*))
                     '(:refused :profile-layout 17)))
(assert-event
 (equal (fn-spo-refusal-text (fn-spo-config-open (fn-spo-layout-frame 17 *spot-wider*)))
        "open refused reason=newer-release: store made by a newer release (profile layout 17 fields, this release expects 16): export it with the release that made it, then import it here"))

; Hypothesis removed: (not (equal n 16)).  This release's layout, the scale
; preset: every other hypothesis holds; the open opens it, not the refusal.
(assert-event (fn-frame-values-okp (fn-spo-layout-spec 16) *fn-bs-profile-scale*))
(assert-event (fn-bs-meta-formatp (car *fn-bs-profile-scale*)))
(assert-event (<= (len (fn-frame-fields-octets (fn-spo-layout-spec 16) *fn-bs-profile-scale*))
                  *fn-bs-meta-max-config-payload*))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame 16 *fn-bs-profile-scale*))
                     (list :opened *fn-bs-profile-scale*)))
(must-fail
 (thm (implies (and (equal n 16) (equal values *fn-bs-profile-scale*))
               (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                      (list :refused :profile-layout n)))))

; Hypothesis removed: (natp n).  n = -1 with no u64 field: the frame is the
; one of layout 0 (fn-spo-layout-frame reads (nfix n)); the refusal names 0,
; not -1.
(defconst *spot-no-fields* (list *fn-bs-meta-format-8* *fn-bs-meta-frontier-format*))
(assert-event (not (natp -1)))
(thm (fn-frame-values-okp (fn-spo-layout-spec -1) *spot-no-fields*))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame -1 *spot-no-fields*))
                     '(:refused :profile-layout 0)))
(must-fail
 (thm (implies (and (equal n -1) (equal values *spot-no-fields*))
               (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                      (list :refused :profile-layout n)))))

; Hypothesis removed: the values fit the layout.  The pre-AS values with an
; empty second text (frame text is nonempty): the sealed frame's head does
; not parse, so it has no layout, and the open answers the generic fault.
(defconst *spot-empty-text* (list* *fn-bs-meta-format-8* nil (cddr *spot-pre-as*)))
(assert-event (not (fn-frame-values-okp (fn-spo-layout-spec 13) *spot-empty-text*)))
(assert-event (equal (car *spot-empty-text*) *fn-bs-meta-format-8*))
; A frame of values outside the layout is outside the encoder's guard, so
; its octets are built from guarded pieces (the empty text is its u16 length
; 0 and no octet) and proved equal to the encoder's frame.
(defun spot-empty-text-payload ()
  (append (fn-frame-field-octets :text *fn-bs-meta-format-8*)
          '(0 0)
          (fn-frame-fields-octets (fn-spo-nat-specs 13) (cddr *spot-pre-as*))))
(defun spot-empty-text-frame ()
  (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version* *fn-bs-meta-config-kind*
                 (spot-empty-text-payload)))
(thm (equal (fn-spo-layout-frame 13 *spot-empty-text*) (spot-empty-text-frame))
     :hints (("Goal" :expand ((fn-spo-layout-frame 13 *spot-empty-text*))
              :in-theory (disable (:e fn-frame-seal) fn-frame-seal
                                  (:e fn-spo-layout-frame)))))
(assert-event (null (fn-spo-layout-fields (spot-empty-text-frame))))
(assert-event (equal (fn-spo-config-open (spot-empty-text-frame)) '(:rejected)))
(must-fail
 (thm (implies (and (equal n 13) (equal values *spot-empty-text*))
               (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                      (list :refused :profile-layout n)))))

; Hypothesis removed: the format word is a store format (fn-store-8 or, since
; lane commit-onto-log, fn-store-9).  The pre-AS values under the format-7
; word: another format, refused by that name instead.
(defconst *spot-other-word* (cons *spot-fmt7-word* (cdr *spot-pre-as*)))
(assert-event (fn-frame-values-okp (fn-spo-layout-spec 13) *spot-other-word*))
(assert-event (not (fn-bs-meta-formatp (car *spot-other-word*))))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame 13 *spot-other-word*))
                     '(:refused :store-format)))
(must-fail
 (thm (implies (and (equal n 13) (equal values *spot-other-word*))
               (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                      (list :refused :profile-layout n)))))

; Hypothesis removed: the payload fits a profile frame (600 octets).  Seventy
; zero fields: 44 + 560 = 604 octets; the frame does not open and the open
; answers the generic fault.
(defun spot-zeros (n) (if (zp n) nil (cons 0 (spot-zeros (1- n)))))
(defconst *spot-long* (list* *fn-bs-meta-format-8* *fn-bs-meta-frontier-format*
                             (spot-zeros 70)))
(assert-event (fn-frame-values-okp (fn-spo-layout-spec 70) *spot-long*))
(assert-event (equal (len (fn-frame-fields-octets (fn-spo-layout-spec 70) *spot-long*)) 604))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame 70 *spot-long*))
                     '(:rejected)))
(must-fail
 (thm (implies (and (equal n 70) (equal values *spot-long*))
               (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                      (list :refused :profile-layout n)))))

; The refinement (fn-spo-config-open-layout-refusal-is-never-a-decoded-frame):
; the witness above is refused and not decoded; a decoded frame is opened.
(assert-event (fn-bs-config-decode (fn-bs-config-encode *fn-bs-profile-scale*)))
(assert-event (not (equal (car (fn-spo-config-open (fn-bs-config-encode *fn-bs-profile-scale*)))
                          :refused)))

; The generic fault (fn-spo-config-open-rejected-has-this-layout-or-none-by-definition):
; octets that are no frame have no layout; this release's layout with H below
; R is this release's layout.
(assert-event (null (fn-spo-layout-fields *spot-garbage*)))
(assert-event (equal (fn-spo-layout-fields (fn-spo-saved-frame *spot-short-history*)) 16))
(assert-event (null (fn-spo-layout-fields *spot-corrupted*)))
