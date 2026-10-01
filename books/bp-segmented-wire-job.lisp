; Actual retained TCPCL source -> bounded primary/canonical framing.
; Internal composite, uninstalled. No backing/policy/grant or CRC decision.
(in-package "ACL2")
(include-book "tcpcl-segment-source-cursor")
(include-book "bp-wire-primary-cursor")
(include-book "bp-wire-canonical-cursor")
(set-verify-guards-eagerness 0)
; job10:tag,phase,source,total,absoluteoffset,sourcecursor,bufferedbyte,
; framingcursor,payload-seen,reason. No whole bundle/block data is retained.
(defun fn-bpsw-begin (source reversed-segments count)
 (declare (xargs :guard t))
 (list :bp-segmented-wire :outer source count 0
       (fn-tsc-begin reversed-segments count) nil nil nil nil))
(defun fn-bpsw-next (j phase at sourcecursor buffered parser payload reason)
 (declare (xargs :guard t))
 (list :bp-segmented-wire phase (fn-bps-field 2 j) (fn-bps-field 3 j)
       at sourcecursor buffered parser payload reason))
(defun fn-bpsw-refuse (j reason)
 (declare (xargs :guard t))
 (fn-bpsw-next j :refused (fn-bps-field 4 j) (fn-bps-field 5 j)
  (fn-bps-field 6 j) (fn-bps-field 7 j) (fn-bps-field 8 j) reason))
(defun fn-bpsw-one (j)
 (declare (xargs :guard t))
 (let* ((phase (fn-bps-field 1 j)) (at (fn-bps-field 4 j))
        (sc (fn-bps-field 5 j)) (buffer (fn-bps-field 6 j))
        (parser (fn-bps-field 7 j)) (payload (fn-bps-field 8 j))
        (source (fn-bps-field 2 j)) (total (fn-bps-field 3 j)))
  (cond
   ((eq phase :refused) (mv :refused j nil))
   ((not (consp buffer))
    (mv-let (word byte next) (fn-tsc-one sc)
     (cond
      ((eq word :refused) (mv :refused (fn-bpsw-refuse j :source-refused) nil))
      ((eq word :source-complete)
       (if (and (eq phase :end) (equal at total)) (mv :source-complete j nil)
        (mv :refused (fn-bpsw-refuse j :truncated-wire) nil)))
      (t (mv :yield (fn-bpsw-next j phase at next
                     (if (eq word :source-byte) (list byte) nil) parser payload nil) nil)))))
   ((eq phase :end) (mv :refused (fn-bpsw-refuse j :trailing-wire) nil))
   ((eq phase :outer)
    (if (equal (car buffer) 159)
     (mv :yield (fn-bpsw-next j :primary (1+ at) sc nil
                 (fn-bpwp-start source total (1+ at)) nil nil) nil)
     (mv :refused (fn-bpsw-refuse j :bundle-array) nil)))
   ((eq phase :between)
    (cond
     ((equal (car buffer) 255)
      (if payload
       (mv :yield (fn-bpsw-next j :end (1+ at) sc nil nil payload nil) nil)
       (mv :refused (fn-bpsw-refuse j :missing-payload) nil)))
     (payload (mv :refused (fn-bpsw-refuse j :payload-not-last) nil))
     (t (mv :yield (fn-bpsw-next j :canonical at sc buffer
                     (fn-bpwc-start source total at) payload nil) nil))))
   ((or (eq phase :primary) (eq phase :canonical))
    (mv-let (word next event)
     (if (eq phase :primary) (fn-bpwp-feed parser (car buffer))
      (fn-bpwc-feed parser (car buffer)))
     (cond
      ((eq word :refused) (mv :refused (fn-bpsw-refuse j :block-framing) nil))
      ((eq word :complete)
       (let ((is-payload (and (eq phase :canonical) (equal (fn-bps-field 4 event) 1))))
        (if (and is-payload (not (equal (fn-bps-field 5 event) 1)))
         (mv :refused (fn-bpsw-refuse j :payload-number) nil)
         (mv :block-source (fn-bpsw-next j :between (1+ at) sc nil nil
                                     (or payload is-payload) nil) event))))
      (t (mv :yield (fn-bpsw-next j phase (1+ at) sc nil next payload nil) nil)))))
   (t (mv :refused (fn-bpsw-refuse j :job-phase) nil)))))
; Stops at each source block event: its receiver must register/retain that exact
; span before continuing. Event is structural metadata, never admission.
(defun fn-bpsw-turn (job quantum used)
 (declare (xargs :guard (and (natp quantum) (<= quantum 64) (natp used))
                 :measure (nfix quantum) :verify-guards nil))
 (if (zp quantum) (mv :yield job used nil)
  (mv-let (word next event) (fn-bpsw-one job)
   (if (eq word :yield) (fn-bpsw-turn next (1- quantum) (1+ used))
    (mv word next (1+ used) event)))))
