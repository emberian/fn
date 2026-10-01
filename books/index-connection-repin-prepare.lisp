; Prepare the offered publication BEFORE the actual source-changing command.
; NEW is an already admitted, registered holder for the SAME logical reader.
; No acceptance, construction grant or native Boolean is an input here.
(in-package "ACL2")
(include-book "index-connection-issuer")

(defun fn-icr-repin-prepare
 (id old-token new-token kind fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let* ((receipt (fn-ibp-connection-pending fn-index-backing))
        (phase (fn-omk-at 6 receipt)))
  (cond
   ((not (and (natp id) (fn-ich-tokenp old-token) (fn-ich-tokenp new-token)
              (not (equal old-token new-token))
              (member-eq kind '(:d :current))
              (fn-omk-widthp receipt 8)
              (eq (fn-omk-at 0 receipt) :connection-reservation)
              (equal (fn-omk-at 1 receipt) new-token)
              (equal (fn-omk-at 2 receipt) id)))
    (mv :stale nil fuel fn-index-backing))
   ((not (member-eq phase '(:registered :source-owned)))
    (mv :recovery-required nil fuel fn-index-backing))
   ; Old-holder lookup and two capture walks. This pays only registry work;
   ; the composed request funds parsing, RC construction and finish separately.
   ((< fuel (* 3 (+ 1 (fn-ibp-slot-depth fn-index-backing))))
    (mv :yield nil fuel fn-index-backing))
   (t
    (mv-let (found old-row left)
     (fn-ibp-connection-read old-token fuel fn-index-backing)
     (mv-let (source old-pin) (fn-ich-row-source id old-row)
      (declare (ignore old-pin))
      (cond
       ((not (and (eq found :present) (eq source :current)))
        (mv :stale nil left fn-index-backing))
       ((eq phase :source-owned)
        ; A prior capture does not authorize a later reader-view selection.
        ; Preserve its pin on mismatch so definite abort can release it once.
        (let ((pin (fn-omk-at 7 receipt))
              (selected (fn-icr-selected-generation kind fn-index-backing)))
         (cond
          ((not selected) (mv :unavailable nil left fn-index-backing))
          ((not (and (fn-omk-widthp pin 3)
                     (eq (fn-omk-at 0 pin) :publication-pin)
                     (equal (fn-omk-at 1 pin) selected)))
           (mv :stale-source nil left fn-index-backing))
          (t (mv :captured pin left fn-index-backing)))))
       (t (fn-icr-capture new-token kind (nfix left) fn-index-backing)))))))))
