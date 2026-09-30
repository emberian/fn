; The current frame algorithm is concrete BLAKE3, independently of the
; identity digest attachment. These are computation/representation tests,
; not witnesses of collision resistance.
(in-package "ACL2")
(include-book "../../books/frame-digest-buffer")

(defconst *fdct-abc*
  '(100 55 179 172 56 70 81 51 255 182 59 117 39 58 141 181
    72 197 88 70 93 121 219 3 253 53 156 108 213 189 157 133))
(defconst *fdct-empty*
  '(175 19 73 185 245 249 161 166 160 64 77 234 54 220 201 73
    155 203 37 201 173 193 18 183 204 154 147 202 228 31 50 98))

; Positive: the exact concrete frame subject evaluates in the proof logic.
; This equality could not follow from the earlier shape-only frame seam.
(defthm fdct-concrete-frame-abc
  (equal (fn-frame-digest '(97 98 99)) *fdct-abc*)
  :rule-classes nil)
(assert-event
 (and (equal (fn-frame-digest '(97 98 99)) *fdct-abc*)
      (equal (fn-frame-digest nil) *fdct-empty*)
      (fn-cbor-octet-listp (fn-frame-digest '(97 98 99)))
      (equal (len (fn-frame-digest '(97 98 99))) 32)))

(defun fdct-buffer-check ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (answer fn-octets)
      (let ((fn-octets (fn-octets-from-list '(120 98 99 121) fn-octets)))
        (mv (and (equal (fn-frame-digest-range '(97) 1 2 fn-octets) *fdct-abc*)
                 (equal (fn-frame-digest-buffer nil fn-octets)
                        (fn-frame-digest '(120 98 99 121)))) fn-octets))
      answer)))
(assert-event (fdct-buffer-check))

; Corrupted input changes this specific witness; no universal injectivity.
(assert-event
 (not (equal (fn-frame-digest '(97 98 100)) *fdct-abc*)))
