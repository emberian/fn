; Root3's canonical archive header, under its existing manifest-page envelope.
; Its manifest is an ordinary schema10 run of physically completed internal
; member runs. There is no alternate raw-journal fallback in this layout.
(in-package "ACL2")
(include-book "checkpoint-map-format")
(fn2-book-layer :b)
(deflayout fn2-event-archive-header
 (append
  '((kind (:enum checkpoint-event-archive-kind (:canonical-member-archive)))
    (version :u8) (checkpoint (:id checkpoint))
    (history (:id history)) (incarnation (:id incarnation))
    (cut-commit (:id commit)) (cut-event (:id event)) (cut-seal :digest)
    (first-event (:id event)) (last-event (:id event)) (member-runs :varint)
    (manifest-run (:id run)) (manifest-height :u8) (manifest-entries :varint))
  (fn2-format-prefix "MANIFEST-" *fn2-format-ref*)))
(defconst *fn2-event-archive-header-start* *fn2-checkpoint-map-body-start*)
(defconst *fn2-event-archive-header-limit*
 (+ *fn2-event-archive-header-start* *fn2-event-archive-header-max-size*))
(assert-event (<= *fn2-event-archive-header-limit* *fn2-format-page-size*))
