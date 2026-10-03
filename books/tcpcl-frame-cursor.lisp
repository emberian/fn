; Concrete input framing cursor, RFC9174 sections4.2,4.5,4.6,5.2.2.
; No body bytes are decoded here. Complete frames retain the existing codec's
; decisions; prefix probes preserve early extension-item refusal.
(in-package "ACL2")
(include-book "tcpcl-octets")
(set-verify-guards-eagerness 2)
(defun fn-tcf-at (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (fn-cbor-ag-car x) (fn-tcf-at (1- n) (fn-cbor-ag-cdr x))))
(defun fn-tcf-make (stage left value flags)
 (declare (xargs :guard t)) (list stage left value flags))
(defun fn-tcf-begin (contact)
 (declare (xargs :guard t)) (fn-tcf-make (if contact :contact :type) (if contact 6 1) 0 0))
(defun fn-tcf-skip-next (stage flags)
 (declare (xargs :guard t))
 (case stage
  (:init-fixed (fn-tcf-make :nid-length 2 0 flags))
  (:node (fn-tcf-make :init-ext-length 4 0 flags))
  (:id (fn-tcf-make (if (logbitp 1 (nfix flags)) :segment-ext-length :data-length)
                       (if (logbitp 1 (nfix flags)) 4 8) 0 flags))
  (:segment-ext (fn-tcf-make :probe 0 0 flags))
  (otherwise (fn-tcf-make :complete 0 0 flags))))
(defun fn-tcf-byte (cursor byte mru)
 (declare (xargs :guard t))
 (let* ((stage (fn-tcf-at 0 cursor)) (left (nfix (fn-tcf-at 1 cursor)))
        (value (+ (* 256 (nfix (fn-tcf-at 2 cursor))) (nfix byte)))
        (flags (fn-tcf-at 3 cursor)))
  (case stage
   (:type (case byte
    (1 (fn-tcf-make :flags 1 0 0))
    (2 (fn-tcf-make :fixed 17 0 0))
    (3 (fn-tcf-make :fixed 9 0 0))
    (4 (fn-tcf-make :complete 0 0 0))
    ((5 6) (fn-tcf-make :fixed 2 0 0))
    (7 (fn-tcf-make :init-fixed 18 0 0))
    (otherwise (fn-tcf-make :complete 0 0 0))))
   (:flags (fn-tcf-make :id 8 0 byte))
   ((:nid-length :init-ext-length :segment-ext-length :data-length)
    (if (< 1 left) (fn-tcf-make stage (1- left) value flags)
     (case stage
      (:nid-length (fn-tcf-make :node value 0 flags))
      (:init-ext-length
       (fn-tcf-make (if (< *fn-tcl-ext-cap* value) :complete :init-ext) value 0 flags))
      (:segment-ext-length
       (fn-tcf-make (if (< *fn-tcl-ext-cap* value) :complete :segment-ext) value 0 flags))
      (otherwise (fn-tcf-make (if (< (nfix mru) value) :complete :data) value 0 flags)))))
   (otherwise cursor))))
; One scalar skip consumes at most the physical read quantum. Zero-length
; ranges transition without consuming a byte, including empty extension lists.
(defun fn-tcf-span (cursor available)
 (declare (xargs :guard t))
 (let* ((stage (fn-tcf-at 0 cursor)) (left (nfix (fn-tcf-at 1 cursor)))
        (flags (fn-tcf-at 3 cursor))
        (used (min left (min (nfix available) 4096))))
  (cond
   ((eq stage :complete) (list :decode cursor 0))
   ((eq stage :probe) (list :probe (fn-tcf-make :data-length 8 0 flags) 0))
   ((member-eq stage '(:contact :fixed :init-fixed :node :id :init-ext :segment-ext :data))
    (list :skip (if (equal used left) (fn-tcf-skip-next stage flags)
                 (fn-tcf-make stage (- left used) 0 flags)) used))
   (t (list :byte cursor (if (zp (nfix available)) 0 1))))))
(defthm fn-tcf-span-physical-quantum
 (and (natp (fn-tcf-at 2 (fn-tcf-span cursor available)))
      (<= (fn-tcf-at 2 (fn-tcf-span cursor available)) 4096)
      (<= (fn-tcf-at 2 (fn-tcf-span cursor available)) (nfix available))))
(defun fn-tcf-contactp (phase)
 (declare (xargs :guard t)) (or (eq phase :tcp-connected) (eq phase :contact)))
