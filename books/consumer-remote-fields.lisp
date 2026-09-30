; Low remote field grammar/charge, independent of Store dispatch.
(in-package "ACL2")
(include-book "consumer-position")
(include-book "records-shape")

; This gate runs before a name's grammar, LEN, octet conversion or wildcard
; work. The representation width is the admitted group's codec width (256).
(defun fn-crs-namep (name)
 (declare (xargs :guard t))
 (and (consp name) (fn-cbor-at-mostp name *fn-record-max-group-name*)
      (fn-cbor-octet-listp name) (fn-record-group-name-octetsp name)))

(defun fn-crw-groups-charge (groups)
 (declare (xargs :guard t))
 (if (not (consp groups)) 0
  (+ 2 (len (car groups)) (fn-crw-groups-charge (cdr groups)))))

(in-theory (disable fn-crs-namep fn-crw-groups-charge))
