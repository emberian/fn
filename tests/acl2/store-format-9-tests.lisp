;; Teeth for books/store-format-9 (lane format-bump-10): the previous
;; format's reader.  Its frame opens under SHA-256 by name; its profile
;; translates to format 10 exactly when nothing the translation drops
;; carried a value; a frame of this format is never read as format 9.
(in-package "ACL2")
(include-book "../../books/store-format-9")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

; The scale preset in format 9's layout (the fixture chain-20000's
; config.json is this frame: tests/acl2/store-profile-open-tests.lisp).
(defconst *f9t-scale*
  (list *fn-bs-meta-format-9* *fn-f9-frontier-word*
        4096 805306368 17138486 32768 65535 256 4096
        1048576 1048576 1048576 1048576 1048576 0 64 256 16384))

; fn-f9-config-decode-of-a-format-9-frame: reachable witness.
(assert-event (null (fn-f9-profile-refusal *f9t-scale*)))
(assert-event (equal (fn-f9-profile-of *f9t-scale*) *fn-bs-profile-scale*))
(assert-event (fn-bs-profile-validp (fn-f9-profile-of *f9t-scale*)))
(assert-event (equal (fn-f9-config-decode (fn-f9-config-frame *f9t-scale*))
                     *fn-bs-profile-scale*))
(assert-event (equal (fn-f9-saved-format-word (fn-f9-config-frame *f9t-scale*))
                     *fn-bs-meta-format-9*))
; The translation drops exactly the two fields, and keeps the rest in order.
(assert-event (equal (len *f9t-scale*) 18))
(assert-event (equal (len (fn-f9-profile-of *f9t-scale*)) 16))
(assert-event (equal (cdr (fn-f9-profile-of *f9t-scale*))
                     (append (take 12 (nthcdr 2 *f9t-scale*))
                             (nthcdr 15 *f9t-scale*))))

; Hypothesis removed (no refusal), one refusal by name each.
(defconst *f9t-marked* (update-nth *fn-f9-history-marker* 1 *f9t-scale*))
(assert-event (equal (fn-f9-profile-refusal *f9t-marked*) :history-marker-required))
(assert-event (null (fn-f9-config-decode (fn-f9-config-frame *f9t-marked*))))
(defconst *f9t-other-frontier* (update-nth 1 *fn-bs-meta-format-9* *f9t-scale*))
(assert-event (equal (fn-f9-profile-refusal *f9t-other-frontier*) :frontier-format))
(defconst *f9t-word-10* (update-nth 0 *fn-bs-meta-format-10* *f9t-scale*))
(assert-event (equal (fn-f9-profile-refusal *f9t-word-10*) :store-format))
(defconst *f9t-short* (update-nth 3 196607 *f9t-scale*))
(assert-event (equal (fn-f9-profile-refusal *f9t-short*)
                     :max-history-octets-below-max-record-octets))
(assert-event (null (fn-f9-config-decode (fn-f9-config-frame *f9t-short*))))
(must-fail-checked
 (thm (implies (equal values9 *f9t-marked*)
               (equal (fn-f9-config-decode (fn-f9-config-frame values9))
                      (fn-f9-profile-of values9)))))

; fn-f9-format-9-frame-does-not-decode: a format-9 frame does not decode
; here; this format's frame is not read as format 9.
(assert-event (null (fn-bs-config-decode (fn-f9-config-frame *f9t-scale*))))
(assert-event (fn-bs-config-decode (fn-bs-config-encode *fn-bs-profile-scale*)))
(assert-event (not (equal (fn-f9-saved-format-word (fn-bs-config-encode *fn-bs-profile-scale*))
                          *fn-bs-meta-format-9*)))

; fn-f9-frame-open-of-seal: a CORRUPTED-state witness (one octet of the
; payload flipped) fails the SHA-256 trailer.
(defconst *f9t-frame* (fn-f9-config-frame *f9t-scale*))
(assert-event (fn-frame-result-okp (fn-f9-frame-open *f9t-frame* *fn-bs-meta-max-config-payload*)))
(assert-event (not (fn-frame-result-okp
                    (fn-f9-frame-open (update-nth 60 (logxor 1 (nth 60 *f9t-frame*)) *f9t-frame*)
                                      *fn-bs-meta-max-config-payload*))))
