(in-package "ACL2")
(include-book "../../books/tcpcl-frame-cursor")
; Unconditional quantum theorem positive literal; no removable hypotheses.
(assert-event
 (let ((plan (fn-tcf-span '(:data 70000 0 0) 90000)))
  (and (natp (fn-tcf-at 2 plan)) (<= (fn-tcf-at 2 plan) 4096)
       (<= (fn-tcf-at 2 plan) (nfix 90000))
       (equal plan '(:skip (:data 65904 0 0) 4096)))))
(assert-event (equal (fn-tcf-span '(:segment-ext 0 0 3) 0)
                      '(:skip (:probe 0 0 3) 0)))
; Actual codec composition fixture: consume exactly one frame before its
; coalesced suffix. This is a fixture, not universal cursor refinement.
(defun fn-test-tcf (cursor bytes prefix fuel)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) nil
  (let* ((plan (fn-tcf-span cursor (len bytes)))
         (action (fn-tcf-at 0 plan)) (next (fn-tcf-at 1 plan))
         (used (fn-tcf-at 2 plan)))
   (cond ((eq action :decode) (list prefix bytes))
    ((eq action :probe) (fn-test-tcf next bytes prefix (1- fuel)))
    ((and (eq action :byte) (equal used 1))
     (fn-test-tcf (fn-tcf-byte next (car bytes) 100000) (cdr bytes)
                   (append prefix (list (car bytes))) (1- fuel)))
    ((eq action :skip)
     (fn-test-tcf next (fn-tcl-drop used bytes)
                    (append prefix (fn-tcl-take used bytes)) (1- fuel)))
    (t nil)))))
(defun fn-test-tcf-message (m contact)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((wire (fn-tcl-encode m)) (bytes (append wire '(4 4)))
        (r (fn-test-tcf (fn-tcf-begin contact) bytes nil 300)))
  (and (equal r (list wire '(4 4)))
       (let ((parsed (if contact (fn-tcl-decode-contact (car r))
                     (fn-tcl-decode-message (car r) 100000))))
        (and (fn-tcl-parse-okp parsed) (equal (fn-tcl-parse-msg parsed) m)
             (not (fn-tcl-parse-rest parsed)))))))
(assert-event
 (and (fn-test-tcf-message (fn-tcl-make-contact 4 0) t)
      (fn-test-tcf-message (fn-tcl-make-keepalive) nil)
      (fn-test-tcf-message (fn-tcl-make-sess-term 1 0) nil)
      (fn-test-tcf-message (fn-tcl-make-msg-reject 0 1) nil)
      (fn-test-tcf-message (fn-tcl-make-xfer-ack 3 7 50000) nil)
      (fn-test-tcf-message (fn-tcl-make-xfer-refuse 1 7) nil)
      (fn-test-tcf-message (fn-tcl-make-sess-init 10 65536 1048576 '(100 116 110 58) nil) nil)
      (fn-test-tcf-message (fn-tcl-make-xfer-segment 3 7 nil '(1 2 3 4)) nil)
      (fn-test-tcf-message (fn-tcl-make-xfer-segment 0 7 nil '(1 2 3 4)) nil)))


(include-book "../../books/tcpcl-input-materialize")
(defun fn-test-tcim-window (fn-octets)
 (declare (xargs :stobjs fn-octets :verify-guards nil))
 (let* ((xs (append (make-list 4096 :initial-element 17) '(18 19 20)))
        (fn-octets (fn-octets-from-list xs fn-octets))
        (r (fn-tcim-turn 4099 '(21 22) fn-octets))
        (v (and (equal r (list (fn-tcim-start 4099)
                     (append (fn-oct-slice-list (fn-tcim-start 4099) 4099 fn-octets) '(21 22))))
                (equal (car r) 3) (equal (len (cadr r)) 4098)
                (equal (fn-tcim-turn (car r) (cadr r) fn-octets)
                       (list 0 (append xs '(21 22)))))))
  (mv v fn-octets)))
; Unconditional boundary positive, using the actual private concrete buffer
; operation over two windows. There is no removable boundary hypothesis.
(assert-event
 (with-local-stobj fn-octets
  (mv-let (v fn-octets) (fn-test-tcim-window fn-octets) v)))
; Scalar-quantum literal positive and sole hypothesis-removal witness.
(assert-event
 (let ((end 4099))
  (and (natp end) (natp (fn-tcim-start end)) (<= (fn-tcim-start end) end)
       (<= (- end (fn-tcim-start end)) 4096))))
(with-guard-checking :none
 (assert-event
  (let ((end -1))
   (and (not (natp end))
        (not (and (natp (fn-tcim-start end)) (<= (fn-tcim-start end) end)
                  (<= (- end (fn-tcim-start end)) 4096)))))))
