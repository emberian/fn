; The BP stage is this job's private source incarnation. It is frozen after
; prefix writing; the digest reads bounded ranges from that same descriptor.
; The capture is a BP stage/token, never a Store or arena payload lease.
(in-package "ACL2")
(include-book "bp-node-checkpoint-job")
(include-book "pagestore-digest-byte-cursor")
(set-verify-guards-eagerness 0)

(defun fn-bpck-digest-start (job pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t))
  (if (not (and (equal (fn-bpn-nth 6 job) :digest-finish)
                (natp (fn-bpn-nth 8 job))
                (equal (fn-bpn-nth 10 job) (+ 14 (fn-bpn-nth 8 job)))
                (equal (fn-bpn-nth 11 job) :private)))
      (mv :refused pgs-digest-state)
    (let ((pgs-digest-state
           (pgs-dcb-begin 0 0 (+ 14 (fn-bpn-nth 8 job))
                          (list :bp-checkpoint-stage (fn-bpn-nth 1 job)
                                (fn-bpn-nth 3 job))
                          (fn-bpn-nth 1 job) pgs-digest-state)))
      (mv :started pgs-digest-state))))

; The native adapter reads only this action's range. All idle/tree turns
; advance without an I/O; the final32 octets are the exact-byte result.
(defun fn-bpck-digest-action (job pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t))
  (let ((total (+ 14 (nfix (fn-bpn-nth 8 job)))))
    (cond
     ((not (and (equal (pgs-dc-capture pgs-digest-state)
                        (list :bp-checkpoint-stage (fn-bpn-nth 1 job)
                              (fn-bpn-nth 3 job)))
                 (equal (pgs-dc-lease pgs-digest-state) (fn-bpn-nth 1 job))))
      '(:uncertain :capture))
     ((equal (pgs-dc-mode pgs-digest-state) :done)
      (list :trailer (pgs-dcb-result-octets pgs-digest-state)))
     ((posp (pgs-dcb-read-demand total pgs-digest-state))
      (list :read (pgs-dcb-next-byte-offset pgs-digest-state)
            (pgs-dcb-read-demand total pgs-digest-state)))
     (t '(:advance)))))

; Supplied bytes are one observed successful read of the named range. Short
; reads are uncertain; no padding can turn missing stage bytes into a digest.
(defun fn-bpck-digest-step (job octets pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t :verify-guards nil))
  (let* ((total (+ 14 (nfix (fn-bpn-nth 8 job))))
         (action (fn-bpck-digest-action job pgs-digest-state)))
    (cond
     ((equal (car action) :trailer) (mv :done pgs-digest-state))
     ((not (member-equal (car action) '(:read :advance)))
      (mv :uncertain pgs-digest-state))
     ((or (not (fn-bpck-small-octet-listp octets 64))
          (not (equal (len octets) (pgs-dcb-read-demand total pgs-digest-state)))
          (not (equal (pgs-dc-total pgs-digest-state) (pgs-dcb-word-count total)))
          (not (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state)))
          (not (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state)))
          (not (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state)))
          (not (<= (* 8 (pgs-dc-pos pgs-digest-state)) total)))
      (mv :uncertain pgs-digest-state))
     (t (pgs-dcb-step total (fn-b3-words 16 octets) pgs-digest-state)))))

(verify-guards fn-bpck-digest-start)
(verify-guards fn-bpck-digest-action)
(verify-guards fn-bpck-digest-step)

(in-theory (disable fn-bpck-digest-start fn-bpck-digest-action fn-bpck-digest-step))
