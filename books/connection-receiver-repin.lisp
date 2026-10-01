(in-package "ACL2")
(include-book "connection-receiver-source")
; INTERNAL: preserves the actual accepted origin's CID and RX identity. OLD
; remains retained by existing request/episode roots; this is a new descriptor.
(defun fn-crx-repin-origin (origin id old-holder new-holder)
 (declare (xargs :guard t))
 (if (and (fn-crx-originp origin)
          (equal id (fn-omk-at 1 origin))
          (equal old-holder (fn-omk-at 2 origin))
          (fn-ich-tokenp new-holder) (not (equal old-holder new-holder)))
     (list :connection-rx-origin id new-holder
           (fn-omk-at 3 origin) (fn-omk-at 4 origin)) nil))

; Publication is conditional on the actual core accepted repin disposition.
; Refusal/stale preserve the SAME issued receipt, including its old roots.
(defun fn-crx-repin-issued (issued id old-holder new-holder disposition)
 (declare (xargs :guard t))
 (let ((origin (fn-omk-at 1 issued)))
  (if (and (member-eq disposition '(:read-ready-repin-released :read-ready-repin-held))
           (fn-omk-widthp issued 3)
           (eq (fn-omk-at 0 issued) :connection-rx-turn))
      (let ((next (fn-crx-repin-origin origin id old-holder new-holder)))
       (if next (list :connection-rx-turn next (fn-omk-at 2 issued)) issued))
    issued)))
