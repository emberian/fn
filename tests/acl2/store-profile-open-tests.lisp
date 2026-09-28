;; Teeth for books/store-profile-open (PKT-471, D34: one store format): the
;; open of what `init' writes opens it; a sealed profile frame naming another
;; format word is refused by name ("not an fn store of this release:
;; redeploy fresh"); anything else is the generic fault.
(in-package "ACL2")
(include-book "../../books/store-profile-open")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

; A sealed profile frame of the u64 fields VALUES after the word WORD, under
; this build's digest: what a release whose format word is WORD writes.
(defun spot-nat-specs (n) (if (zp n) nil (cons :nat (spot-nat-specs (1- n)))))
(defun spot-frame (word fields)
  (declare (xargs :verify-guards nil))
  (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version* *fn-bs-meta-config-kind*
                 (fn-frame-fields-octets (cons :text (spot-nat-specs (len fields)))
                                         (cons word fields))))

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
; The frame spot-frame writes for this build's word and fields is init's.
(assert-event (equal (spot-frame *fn-bs-meta-format-10* (cdr *fn-bs-profile-scale*))
                     (fn-bs-config-encode *fn-bs-profile-scale*)))
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
; fn-spo-config-open-store-format-is-exactly-a-foreign-frame

; Right side true: this build's fields under another word (the dev-era
; fn-store-9, and a later fn-store-11): refused by name, with the line.
(defconst *spot-word-9* '(102 110 45 115 116 111 114 101 45 57))         ; fn-store-9
(defconst *spot-word-11* '(102 110 45 115 116 111 114 101 45 49 49))    ; fn-store-11
(defun spot-other-9 () (spot-frame *spot-word-9* (cdr *fn-bs-profile-scale*)))
(defun spot-other-11 () (spot-frame *spot-word-11* (cdr *fn-bs-profile-scale*)))
(assert-event (not (fn-bs-meta-formatp *spot-word-9*)))
(assert-event (fn-spo-foreign-formatp (spot-other-9)))
(assert-event (equal (fn-spo-config-open (spot-other-9)) '(:refused :store-format)))
(assert-event (fn-spo-foreign-formatp (spot-other-11)))
(assert-event (equal (fn-spo-config-open (spot-other-11)) '(:refused :store-format)))
(assert-event (equal (fn-spo-refusal-text (fn-spo-config-open (spot-other-11)))
                     "open refused reason=store-format: not an fn store of this release: redeploy fresh"))
; Another word and another layout (three fields): refused by the same name.
(defun spot-other-short () (spot-frame *spot-word-11* '(1 2 3)))
(assert-event (equal (fn-spo-config-open (spot-other-short)) '(:refused :store-format)))
; Its octets, pinned: tests/older_release_store.py writes exactly these as
; the config.json of a store of another release (the native refusal case).
(defconst *spot-other-short-octets*
  '(
    70 78 83 77 1 1 0 0 0 37 0 11 102 110 45 115
    116 111 114 101 45 49 49 0 0 0 0 0 0 0 1 0
    0 0 0 0 0 0 2 0 0 0 0 0 0 0 3 45
    225 223 249 8 199 206 214 99 193 26 231 104 203 173 29 80
    39 17 66 154 220 34 25 66 202 71 109 249 123 146 142))
(assert-event (equal (spot-other-short) *spot-other-short-octets*))
; Right side false, each way: a decoded frame (opened); this build's word
; over fields the relation refuses, or over another layout, and octets that
; are no sealed frame (the generic fault, no line).
(assert-event (not (fn-spo-foreign-formatp (fn-bs-config-encode *fn-bs-profile-scale*))))
(assert-event (not (equal (fn-spo-config-open (fn-bs-config-encode *fn-bs-profile-scale*))
                          '(:refused :store-format))))
(defun spot-bad-fields () (spot-frame *fn-bs-meta-format-10* (cdr *spot-short-history*)))
(assert-event (not (fn-spo-foreign-formatp (spot-bad-fields))))
(assert-event (equal (fn-spo-config-open (spot-bad-fields)) '(:rejected)))
(defun spot-this-short () (spot-frame *fn-bs-meta-format-10* '(1 2 3)))
(assert-event (not (fn-spo-foreign-formatp (spot-this-short))))
(assert-event (equal (fn-spo-config-open (spot-this-short)) '(:rejected)))
(defconst *spot-garbage* '(1 2 3 4 5 6 7 8 9 10))
(assert-event (not (fn-spo-foreign-formatp *spot-garbage*)))
(assert-event (equal (fn-spo-config-open *spot-garbage*) '(:rejected)))
(assert-event (null (fn-spo-refusal-text (fn-spo-config-open *spot-garbage*))))
; A foreign frame with one octet of its trailer flipped is damage, not a
; store of another release: the generic fault.
(defun spot-other-damaged ()
  (append (butlast (spot-other-11) 1)
          (list (logxor 1 (car (last (spot-other-11)))))))
(assert-event (not (fn-spo-foreign-formatp (spot-other-damaged))))
(assert-event (equal (fn-spo-config-open (spot-other-damaged)) '(:rejected)))
; The conclusion fails without the right side: a frame of this build's word.
(must-fail-checked
 (thm (implies (not (fn-spo-foreign-formatp octets))
               (equal (fn-spo-config-open octets) '(:refused :store-format)))))
