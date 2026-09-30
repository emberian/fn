; Registered prefix action semantics. This internal source composition is
; unhooked until actual stage/operation allowances are installed. It neither
; accepts native job snapshots nor treats requested I/O as an observation.
(in-package "ACL2")
(include-book "bp-checkpoint-source-incarnation")
(set-verify-guards-eagerness 2)

; Answer word/payload/effect. Revision is from the registered directory.
; Pending action retains the exact bounded bytes and old source offset.
(defun fn-bpck-prefix-prepare (payload revision)
 (declare (xargs :guard (natp revision)))
 (let* ((job (fn-bpck-control-job payload)) (io (fn-bpck-control-io payload))
        (kind (fn-bpck-io-action io job)))
  (cond
   ((fn-bpck-control-action payload) (list :busy payload nil))
   ((not (member-eq kind '(:open :emit :prefix-end)))
    (list :integrity-required payload nil))
   ((and (eq kind :prefix-end)
         (equal (fn-bpck-write-action job) :digest)
         (equal (fn-bpn-nth 11 job) :private))
    (list :prefix-frozen
     (fn-bpck-control-make job (fn-bpck-io-step io :prefix-end)
                          (fn-bpck-control-digest payload) nil) nil))
   ((or (and (eq kind :open) (equal (fn-bpn-nth 6 job) :emit)
             (equal (fn-bpn-nth 11 job) :none))
        (and (eq kind :emit) (equal (fn-bpn-nth 6 job) :emit)
             (equal (fn-bpn-nth 11 job) :private)))
    (let* ((answer (if (eq kind :emit) (fn-bpck-emit-step job) (list job nil)))
           (next (fn-bpn-nth 0 answer)) (bytes (fn-bpn-nth 1 answer))
           (action (list :bp-checkpoint-io-action (fn-bpn-nth 1 job)
                         (1+ revision) kind (fn-bpn-nth 10 job) bytes)))
     (list :action-prepared
       (fn-bpck-control-make next io (fn-bpck-control-digest payload) action)
       action)))
   (t (list :uncertain payload nil)))))

; This token/revision fence precedes every primitive-result update. Unknown
; outcomes fence/retain stage debt; they never restore the old encoder cursor.
(defun fn-bpck-prefix-observe (payload token revision observation)
 (declare (xargs :guard t))
 (let* ((action (fn-bpck-control-action payload))
        (job (fn-bpck-control-job payload)) (io (fn-bpck-control-io payload))
        (kind (fn-bpn-nth 3 action)))
  (if (not (and (equal (fn-bpn-nth 0 action) :bp-checkpoint-io-action)
                (fn-bpcc-job-tokenp token)
                (equal token (fn-bpn-nth 1 action))
                (equal token (fn-bpn-nth 1 job))
                (natp revision) (equal revision (fn-bpn-nth 2 action))
                (member-eq kind '(:open :emit))))
   (list :stale-checkpoint-observation payload)
   (let* ((ok (eq observation :ok))
          (next-job (cond ((not ok) (fn-bpck-stage-observation job :ambiguous))
                          ((eq kind :open) (fn-bpck-stage-observation job :created))
                          (t job)))
          (next-io (fn-bpck-io-step io (if ok :ok :error))))
    (list (if ok :observed :uncertain)
     (fn-bpck-control-make next-job next-io (fn-bpck-control-digest payload) nil))))))
