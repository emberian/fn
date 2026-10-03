; Direct string-line rendering into the concrete octet buffer. Scalar loop
; registers replace per-character cursor and output lists. The returned cursor
; is allocated only once at the scheduling boundary.
(in-package "ACL2")
(include-book "string-line-cursor")
(include-book "octets-stobj")

(defun fn-slf-loop (text position phase bytes fn-octets)
  (declare (xargs :guard (natp bytes) :stobjs fn-octets
                  :measure (nfix bytes) :verify-guards nil))
  (if (zp bytes)
      (mv (fn-sl-make text position phase) fn-octets)
    (cond
     ((eq phase :stuff)
      (let ((fn-octets (fn-octets-append-octet 46 fn-octets)))
        (fn-slf-loop text position :text (1- bytes) fn-octets)))
     ((eq phase :text)
      (if (and (stringp text) (natp position) (< position (length text)))
          (let ((fn-octets (fn-octets-append-octet
                            (char-code (char text position)) fn-octets)))
            (fn-slf-loop text (1+ position)
                         (if (< (1+ position) (length text)) :text :cr)
                         (1- bytes) fn-octets))
        (let ((fn-octets (fn-octets-append-octet 13 fn-octets)))
          (fn-slf-loop text position :lf (1- bytes) fn-octets))))
     ((eq phase :cr)
      (let ((fn-octets (fn-octets-append-octet 13 fn-octets)))
        (fn-slf-loop text position :lf (1- bytes) fn-octets)))
     ((eq phase :lf)
      (let ((fn-octets (fn-octets-append-octet 10 fn-octets)))
        (mv nil fn-octets)))
     (t (mv nil fn-octets)))))

(verify-guards fn-slf-loop)

(defun fn-sl-fill (cur bytes fn-octets)
  (declare (xargs :guard (natp bytes) :stobjs fn-octets))
  (if (or (not cur) (zp bytes))
      (mv cur fn-octets)
    (fn-slf-loop (fn-cur-at 0 cur) (fn-cur-at 1 cur) (fn-cur-at 2 cur)
                 bytes fn-octets)))
