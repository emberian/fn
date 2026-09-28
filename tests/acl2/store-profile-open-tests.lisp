;; Teeth for books/store-profile-open (PKT-471, PKT-705, D34; format 10, lane
;; format-bump-10): the open of what `init' writes opens it; a format-9 store
;; is refused by name with the way out; another format is refused by name;
;; another layout of this format is refused by name; nothing decoded is
;; refused; the generic fault is left to this layout or none.
(in-package "ACL2")
(include-book "../../books/store-profile-open")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

; -----------------------------------------------------------------------------
; fn-spo-open-of-a-valid-profile-opens-it

; Reachable witnesses: the presets and the defaults, and the frame `init'
; writes, open as themselves.
(assert-event (fn-bs-profile-validp *fn-bs-profile-scale*))
(assert-event (equal (fn-spo-config-open (fn-bs-config-encode *fn-bs-profile-scale*))
                     (list :opened *fn-bs-profile-scale*)))
(assert-event (equal (fn-spo-config-open (fn-bs-config-encode *fn-bs-profile-defaults*))
                     (list :opened *fn-bs-profile-defaults*)))
(assert-event (equal (fn-spo-config-open (fn-bs-initial-config-octets))
                     (list :opened *fn-bs-profile-development*)))
; Hypothesis removed (validp): H one octet below R.  The encoder writes no
; frame, and the open of that answers the generic fault, not (:opened V).
(defconst *spot-short-history*
  (fn-bs-profile-put *fn-bs-pf-max-history-octets*
                     (1- (fn-bs-pf *fn-bs-pf-max-record-octets* *fn-bs-profile-scale*))
                     *fn-bs-profile-scale*))
(assert-event (equal (fn-bs-profile-invalid-reason *spot-short-history*)
                     :max-history-octets-below-max-record-octets))
(assert-event (null (fn-bs-config-encode *spot-short-history*)))
(assert-event (equal (fn-spo-config-open (fn-bs-config-encode *spot-short-history*))
                     '(:rejected)))
(must-fail-checked
 (thm (implies (equal values *spot-short-history*)
               (equal (fn-spo-config-open (fn-bs-config-encode values))
                      (list :opened values)))))

; -----------------------------------------------------------------------------
; fn-spo-open-of-a-format-9-frame-refuses-by-name

; A format-9 store's config.json, octet for octet: the scale preset of the
; release before format 10 (hbox /tank/fn/scratch/fixtures/chain-20000/store/
; config.json, 214 octets: FNSM, payload 172 = the word fn-store-9, the
; frontier word and sixteen u64 fields, the SHA-256 trailer): the scale
; preset with T raised to 1,048,576 and A lowered to 2,048.
(defconst *spot-format-9-octets*
  '(70 78 83 77 1 1 0 0 0 172 0 10 102 110 45 115 116 111 114 101 45 57
    0 30 102 110 45 115 116 111 114 101 45 97 108 108 111 99 97 116 105 111
    110 45 102 114 111 110 116 105 101 114 45 50 0 0 0 0 0 16 0 0 0 0 0 0
    48 0 0 0 0 0 0 0 1 5 131 54 0 0 0 0 0 0 8 0 0 0 0 0 0 0 255 255 0 0 0 0
    0 0 1 0 0 0 0 0 0 0 16 0 0 0 0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0 0 0 0 16
    0 0 0 0 0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 64
    0 0 0 0 0 0 1 0 0 0 0 0 0 0 64 0 175 29 24 208 73 68 104 101 148 236 215
    122 122 30 72 160 208 52 172 105 52 81 156 167 166 67 37 36 215 247 52 18))
; Its values, by hand, in format 9's layout.
(defconst *spot-scale-9*
  (list *fn-bs-meta-format-9* *fn-f9-frontier-word*
        1048576 805306368 17138486 2048 65535 256 4096
        1048576 1048576 1048576 1048576 1048576 0 64 256 16384))
(assert-event (equal (len *spot-format-9-octets*) 214))
(assert-event (equal (fn-f9-config-frame *spot-scale-9*) *spot-format-9-octets*))
; Reachable witness: the antecedent, then the conclusion and its line.
(assert-event (fn-spo-format-9p *spot-format-9-octets*))
(assert-event (equal (fn-spo-config-open *spot-format-9-octets*)
                     '(:refused :store-format-9)))
(assert-event
 (equal (fn-spo-refusal-text (fn-spo-config-open *spot-format-9-octets*))
        "open refused reason=store-format-9: a format-9 store (made by the release before format 10); export it with that release (store ROOT export DIR), then import it here (store NEWROOT import DIR); no store is upgraded in place (D34)"))
; The same fields translate to format 10 (the import's way).
(assert-event (equal (fn-f9-config-decode *spot-format-9-octets*)
                     (fn-f9-profile-of *spot-scale-9*)))
(assert-event (fn-bs-profile-validp (fn-f9-profile-of *spot-scale-9*)))
; Hypothesis removed (format-9p): the scale preset's format-10 frame.  Not a
; format-9 frame, and the open opens it rather than refusing.
(assert-event (not (fn-spo-format-9p (fn-bs-config-encode *fn-bs-profile-scale*))))
(assert-event (not (equal (fn-spo-config-open (fn-bs-config-encode *fn-bs-profile-scale*))
                          '(:refused :store-format-9))))
(must-fail-checked
 (thm (implies (equal octets (fn-bs-config-encode *fn-bs-profile-scale*))
               (equal (fn-spo-config-open octets)
                      (list :refused :store-format-9)))))
; CORRUPTED-state witness: one payload octet of the format-9 frame flipped.
; It fails its trailer, is no sealed frame, and the open answers the fault.
(defconst *spot-format-9-corrupted*
  (update-nth 60 (logxor 1 (nth 60 *spot-format-9-octets*)) *spot-format-9-octets*))
(assert-event (not (fn-spo-format-9p *spot-format-9-corrupted*)))
(assert-event (equal (fn-spo-config-open *spot-format-9-corrupted*) '(:rejected)))

; -----------------------------------------------------------------------------
; fn-spo-config-open-store-format-is-exactly-a-foreign-frame

; A format-7 store's config.json (the sealed FNSM frame of the format-7
; encoder; tests/older_release_store.py writes the same file).
(defconst *spot-fmt7-word*
  '(102 110 45 115 116 111 114 101 45 101 120 112 101 114 105 109 101 110 116 45 55))
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
; Right side true: a foreign word; the open refuses by the format's name.
(assert-event (fn-spo-foreign-formatp *spot-format-7-octets*))
(assert-event (equal (fn-spo-config-open *spot-format-7-octets*) '(:refused :store-format)))
(assert-event (equal (fn-spo-refusal-text (fn-spo-config-open *spot-format-7-octets*))
                     "open refused reason=store-format: reinstall from the release and import"))
; A format-8 store's config.json of the layout before batch AS (the word
; fn-store-8, the frontier word, thirteen u64 fields): foreign now too.
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
(assert-event (fn-spo-foreign-formatp *spot-pre-as-octets*))
(assert-event (equal (fn-spo-config-open *spot-pre-as-octets*) '(:refused :store-format)))
; Right side false, each way: a decoded frame, a format-9 frame, no frame.
(assert-event (not (fn-spo-foreign-formatp (fn-bs-config-encode *fn-bs-profile-scale*))))
(assert-event (not (fn-spo-foreign-formatp *spot-format-9-octets*)))
(assert-event (not (equal (fn-spo-config-open *spot-format-9-octets*) '(:refused :store-format))))
(defconst *spot-garbage* '(1 2 3 4 5 6 7 8 9 10))
(assert-event (not (fn-spo-foreign-formatp *spot-garbage*)))
(assert-event (equal (fn-spo-config-open *spot-garbage*) '(:rejected)))
(assert-event (null (fn-spo-refusal-text (fn-spo-config-open *spot-garbage*))))

; -----------------------------------------------------------------------------
; fn-spo-open-of-another-layout-refuses-by-name

; A format-10 frame of thirteen fields (an older release of this format).
(defconst *spot-13* (cons *fn-bs-meta-format-10* (take 13 (cdr *fn-bs-profile-scale*))))
(assert-event (natp 13))
(assert-event (not (equal 13 *fn-spo-release-layout-fields*)))
(assert-event (equal *fn-spo-release-layout-fields* 15))
(assert-event (fn-frame-values-okp (fn-spo-layout-spec 13) *spot-13*))
(assert-event (fn-bs-meta-formatp (car *spot-13*)))
(assert-event (<= (len (fn-frame-fields-octets (fn-spo-layout-spec 13) *spot-13*))
                  *fn-bs-meta-max-config-payload*))
(assert-event (equal (fn-spo-layout-fields (fn-spo-layout-frame 13 *spot-13*)) 13))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame 13 *spot-13*))
                     '(:refused :profile-layout 13)))
(assert-event
 (equal (fn-spo-refusal-text (fn-spo-config-open (fn-spo-layout-frame 13 *spot-13*)))
        "open refused reason=older-release: store made by an older release (profile layout 13 fields, this release expects 15): export it with the release that made it, then import it here"))
; A wider one is refused by the other name.
(defconst *spot-17* (append *fn-bs-profile-scale* '(1 2)))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame 17 *spot-17*))
                     '(:refused :profile-layout 17)))
(assert-event
 (equal (fn-spo-refusal-text (fn-spo-config-open (fn-spo-layout-frame 17 *spot-17*)))
        "open refused reason=newer-release: store made by a newer release (profile layout 17 fields, this release expects 15): export it with the release that made it, then import it here"))
; Hypothesis removed: (not (equal n 15)).  This release's layout opens.
(assert-event (fn-frame-values-okp (fn-spo-layout-spec 15) *fn-bs-profile-scale*))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame 15 *fn-bs-profile-scale*))
                     (list :opened *fn-bs-profile-scale*)))
(must-fail-checked
 (thm (implies (and (equal n 15) (equal values *fn-bs-profile-scale*))
               (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                      (list :refused :profile-layout n)))))
; Hypothesis removed: (natp n).  n = -1 is the frame of layout 0.
(defconst *spot-no-fields* (list *fn-bs-meta-format-10*))
(assert-event (not (natp -1)))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame -1 *spot-no-fields*))
                     '(:refused :profile-layout 0)))
(must-fail-checked
 (thm (implies (and (equal n -1) (equal values *spot-no-fields*))
               (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                      (list :refused :profile-layout n)))))
; Hypothesis removed: the word is this format's.  The thirteen fields under
; the format-7 word: refused by the format's name instead.
(defconst *spot-other-word* (cons *spot-fmt7-word* (cdr *spot-13*)))
(assert-event (fn-frame-values-okp (fn-spo-layout-spec 13) *spot-other-word*))
(assert-event (not (fn-bs-meta-formatp (car *spot-other-word*))))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame 13 *spot-other-word*))
                     '(:refused :store-format)))
(must-fail-checked
 (thm (implies (and (equal n 13) (equal values *spot-other-word*))
               (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                      (list :refused :profile-layout n)))))
; Hypothesis removed: the payload fits a profile frame.  Seventy-five zero
; fields: 13 + 600 octets; the frame does not open: the generic fault.
(defun spot-zeros (n) (if (zp n) nil (cons 0 (spot-zeros (1- n)))))
(defconst *spot-long* (cons *fn-bs-meta-format-10* (spot-zeros 75)))
(assert-event (fn-frame-values-okp (fn-spo-layout-spec 75) *spot-long*))
(assert-event (< *fn-bs-meta-max-config-payload*
                 (len (fn-frame-fields-octets (fn-spo-layout-spec 75) *spot-long*))))
(assert-event (equal (fn-spo-config-open (fn-spo-layout-frame 75 *spot-long*))
                     '(:rejected)))
(must-fail-checked
 (thm (implies (and (equal n 75) (equal values *spot-long*))
               (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                      (list :refused :profile-layout n)))))
; Hypothesis removed: the values fit the layout (a field that is no u64).
(defconst *spot-bad-field* (cons *fn-bs-meta-format-10* (list* -1 (cddr *spot-13*))))
(assert-event (not (fn-frame-values-okp (fn-spo-layout-spec 13) *spot-bad-field*)))

; -----------------------------------------------------------------------------
; fn-spo-config-open-refuses-no-decoded-frame

(assert-event (fn-bs-config-decode (fn-bs-config-encode *fn-bs-profile-scale*)))
(assert-event (equal (fn-spo-config-open (fn-bs-config-encode *fn-bs-profile-scale*))
                     (list :opened (fn-bs-config-decode
                                    (fn-bs-config-encode *fn-bs-profile-scale*)))))
; Hypothesis removed: the format-9 frame does not decode, and is refused.
(assert-event (null (fn-bs-config-decode *spot-format-9-octets*)))
(assert-event (not (equal (car (fn-spo-config-open *spot-format-9-octets*)) :opened)))

; -----------------------------------------------------------------------------
; fn-spo-config-open-rejected-has-this-layout-or-none-by-definition

; No frame: no layout.  This release's layout with H below R: this layout.
(defun spot-short-history-frame ()
  (fn-spo-layout-frame 15 *spot-short-history*))
(assert-event (null (fn-spo-layout-fields *spot-garbage*)))
(assert-event (equal (fn-spo-config-open (spot-short-history-frame)) '(:rejected)))
(assert-event (equal (fn-spo-layout-fields (spot-short-history-frame)) 15))
