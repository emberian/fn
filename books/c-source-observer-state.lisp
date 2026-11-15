; Endpoint receipts for source observations. An actor can own multiple endpoints;
; READ and successor continuations must never collapse into one actor lease.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :c)

(defcolumns fn2-c-source-control
 ((phase (:enum fn2-c-source-writer-phase (:idle :pending :exclusive :uncertain)))
  (readers :u32) (next-receipt :u60)
  (writer-kind :u8) (writer-owner :u32) (writer-gen :u60)
  (writer-token :u60) (cut-commit :u60) (cut-event :u60)
  (wake-pending :bool)))

(defcolumns fn2-c-source-readers ((live :bool) (serial :u60)))

(defun fn2-c-source-reader-current-p (endpoint receipt fn2-c-source-readers)
 (declare (xargs :stobjs fn2-c-source-readers :guard (fn2-c-source-readers-wfp fn2-c-source-readers)))
 (and (natp endpoint) (< endpoint (fn2-c-source-readers-rows fn2-c-source-readers))
      (posp receipt) (unsigned-byte-p 60 receipt)
      (equal (fn2-c-source-readers-live endpoint fn2-c-source-readers) 1)
      (equal (fn2-c-source-readers-serial endpoint fn2-c-source-readers) receipt)))

(defun fn2-c-source-writer-receipt-p (kind owner gen token cutcommit cutevent fn2-c-source-control)
 (declare (xargs :stobjs fn2-c-source-control :guard (fn2-c-source-control-wfp fn2-c-source-control)))
 (and (< 0 (fn2-c-source-control-rows fn2-c-source-control))
      (unsigned-byte-p 8 kind) (unsigned-byte-p 32 owner)
      (unsigned-byte-p 60 gen) (posp gen) (unsigned-byte-p 60 token) (posp token)
      (unsigned-byte-p 60 cutcommit) (unsigned-byte-p 60 cutevent)
      (not (equal (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-idle*))
      (equal kind (fn2-c-source-control-writer-kind 0 fn2-c-source-control))
      (equal owner (fn2-c-source-control-writer-owner 0 fn2-c-source-control))
      (equal gen (fn2-c-source-control-writer-gen 0 fn2-c-source-control))
      (equal token (fn2-c-source-control-writer-token 0 fn2-c-source-control))
      (equal cutcommit (fn2-c-source-control-cut-commit 0 fn2-c-source-control))
      (equal cutevent (fn2-c-source-control-cut-event 0 fn2-c-source-control))))

(defun fn2-c-source-writer-exclusive-p (kind owner gen token cutcommit cutevent fn2-c-source-control)
 (declare (xargs :stobjs fn2-c-source-control :guard (fn2-c-source-control-wfp fn2-c-source-control)))
 (and (fn2-c-source-writer-receipt-p kind owner gen token cutcommit cutevent fn2-c-source-control)
      (equal (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-exclusive*)
      (equal (fn2-c-source-control-readers 0 fn2-c-source-control) 0)))
