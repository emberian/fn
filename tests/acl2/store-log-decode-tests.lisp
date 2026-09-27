; Witnesses for books/store-log-decode (fn-lg-decode, the executable scan
; over the segment read as a string, equals the logical scan).  The keystone
; fn-lg-decode-is-the-scan has no hypothesis, so its teeth are reachable
; witnesses: a log with a torn tail and a zeroed extent, a log whose last
; padding runs past the end, an empty and a garbage segment.
(in-package "ACL2")
(include-book "../../books/store-log-decode")
(include-book "../../books/frame-trailer")

(defun sld-chars (codes)
  (declare (xargs :guard (fn-cbor-octet-listp codes)))
  (if (consp codes) (cons (code-char (car codes)) (sld-chars (cdr codes))) nil))
(defun sld-string (codes)
  (declare (xargs :guard (fn-cbor-octet-listp codes)))
  (coerce (sld-chars codes) 'string))
(defun sld-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))

; Decode and scan agree, and the decode reads what the witness names.
(defun sld-agree (codes unit expect-records expect-consumed)
  (declare (xargs :guard t :verify-guards nil))
  (let ((s (sld-string codes)) (g *fn-lg-genesis*))
    (mv-let (records consumed last) (fn-lg-decode s g unit 4096)
      (and (equal (fn-lgd-octets s) codes)
           (equal records (car (fn-lg-scan codes g unit 4096)))
           (equal consumed (cdr (fn-lg-scan codes g unit 4096)))
           (equal last (fn-lg-scan-last codes g unit 4096))
           (equal records expect-records)
           (equal consumed expect-consumed)))))

; Two records, a torn unit of garbage, two zero units: the frontier is the
; end of the second entry.
(assert-event
 (let ((log (fn-lg-log (list (sld-r 1) (sld-r 2)) *fn-lg-genesis* 4)))
   (sld-agree (append log '(9 9 9 9 0 0 0 0 0 0 0 0)) 4
              (list (sld-r 1) (sld-r 2)) (len log))))

; A 512-octet unit: the one entry's padding runs past the end of a segment
; cut short; the frontier is past the end (T3 needs whole units).
(assert-event
 (let* ((log (fn-lg-log (list (sld-r 5)) *fn-lg-genesis* 512))
        (short (fn-bs-take (- (len log) 100) log)))
   (and (< (len short) (len log))
        (sld-agree short 512 (list (sld-r 5)) (len log)))))

; Empty and garbage segments: the empty history at offset 0.
(assert-event (sld-agree nil 4 nil 0))
(assert-event (sld-agree '(70 78 76 71 1 1 0 0 0 99 1 2 3) 4 nil 0))
