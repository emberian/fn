; Replay under the node's profile never truncates (PRF-131 part 2).
;
; Recovery replays the FNBS journal through fn-bpnf-family-replay-rows (the
; recovery event fn-bpnf-family-recover-auto-event, built for the host by
; fn-bpnr-recover-auto-event at host/native/bp-service.lisp fnn-bps-open),
; into a machine whose held rows and octets are the profile's
; (fn-bpnpf-valid-profile-opens).  A received row that is well formed but
; that the profile cannot hold -- the journal was written under a larger
; profile -- makes the whole replay answer the named verdict
; (:fault :held-beyond-profile): recovery fences with that reason, and no
; held list is ever returned without the row.
(in-package "ACL2")
(include-book "bp-fnbs-replay-append")
(include-book "bp-node-profile")

; A kind-5 row that replay admits at this point in every respect but the
; profile's bounds.
(defun fn-bpnpf-kind-five-row-fitsp (row held prior next-arrival)
  ; A statement predicate: the host never calls it.
  (declare (xargs :guard t :verify-guards nil))
  (let* ((record (fn-bpnf-family-replay-row-record row))
         (epoch (fn-bpn-nth 1 record))
         (op (fn-bpn-nth 2 record))
         (h (fn-bpn-nth 3 record)))
    (and record
         (equal (car row) (fn-bpnf-stored-record-name epoch op))
         (fn-bpnf-replay-pair-afterp epoch op prior)
         (equal (car record) :bpnf-stored)
         (equal (fn-bpn-nth 3 h) next-arrival)
         (equal (fn-bpnf-receive-decision held (fn-bpn-nth 4 h)
                                          (fn-bpnf-held-bundle h))
                :fresh))))

(defthm fn-bpnpf-row-past-the-profile-is-named
  (implies (and (fn-bpnpf-kind-five-row-fitsp row held prior next-arrival)
                (<= (fn-bpn-machine-state-max-jobs base) (len held)))
           (equal (fn-bpnf-family-replay-rows-aux
                   (cons row rest) base held handoffs prior next-arrival)
                  (list :fault :held-beyond-profile)))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-bpnf-family-replay-rows-aux
                     (cons row rest) base held handoffs prior next-arrival))
           :in-theory (disable fn-bpnf-family-replay-rows-aux
                               fn-bpnf-family-replay-row-record
                               fn-bpnf-stored-record-name
                               fn-bpnf-replay-pair-afterp
                               fn-bpnf-receive-decision
                               fn-bpnf-held-octets fn-bpnf-held-bundle
                               fn-bpn-machine-state-max-jobs
                               fn-bpn-machine-state-max-octets
                               fn-bpnr-family-replay-aux-cons))))

; Keystone: whatever prefix replayed to a held list the profile has filled,
; the next well-formed received row makes the whole replay the named
; verdict; the rest of the journal is never dropped into a :ready result.
(defthm fn-bpnpf-replay-past-the-profile-is-refused
  (let ((r (fn-bpnf-family-replay-rows-aux
            prefix base held handoffs prior next-arrival)))
    (implies (and (true-listp prefix)
                  (equal (car r) :ready)
                  (fn-bpnpf-kind-five-row-fitsp
                   row (fn-bpn-nth 1 r) (fn-bpn-nth 3 r) (fn-bpn-nth 4 r))
                  (<= (fn-bpn-machine-state-max-jobs base)
                      (len (fn-bpn-nth 1 r))))
             (equal (fn-bpnf-family-replay-rows-aux
                     (append prefix (cons row rest))
                     base held handoffs prior next-arrival)
                    (list :fault :held-beyond-profile))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-family-replay-aux-append
                  (suffix (cons row rest)))
                 (:instance fn-bpnpf-row-past-the-profile-is-named
                  (held (fn-bpn-nth 1 (fn-bpnf-family-replay-rows-aux
                                       prefix base held handoffs prior next-arrival)))
                  (handoffs (fn-bpn-nth 2 (fn-bpnf-family-replay-rows-aux
                                           prefix base held handoffs prior next-arrival)))
                  (prior (fn-bpn-nth 3 (fn-bpnf-family-replay-rows-aux
                                        prefix base held handoffs prior next-arrival)))
                  (next-arrival (fn-bpn-nth 4 (fn-bpnf-family-replay-rows-aux
                                               prefix base held handoffs prior next-arrival)))))
           :in-theory (disable fn-bpnf-family-replay-rows-aux
                               fn-bpnr-family-replay-aux-append
                               fn-bpnpf-row-past-the-profile-is-named
                               fn-bpnr-family-replay-aux-cons
                               fn-bpnpf-kind-five-row-fitsp))))

; The held image's bound is the profile's held octets (PRF-134, the codec
; half of P5): *fn-bpnf-max-held-image* is only the codec width.  A received
; row whose image the profile's held octets cannot take beside the rows
; already held is the same named verdict.
(defun fn-bpnpf-kind-five-row-image (row)
  ; A statement term: the image the row carries.
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-held-wire (fn-bpn-nth 3 (fn-bpnf-family-replay-row-record row))))

(defthm fn-bpnpf-row-past-the-octets-is-named
  (implies (and (fn-bpnpf-kind-five-row-fitsp row held prior next-arrival)
                (< (fn-bpn-machine-state-max-octets base)
                   (+ (fn-bpnf-held-octets held)
                      (len (fn-bpnpf-kind-five-row-image row)))))
           (equal (fn-bpnf-family-replay-rows-aux
                   (cons row rest) base held handoffs prior next-arrival)
                  (list :fault :held-beyond-profile)))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-bpnf-family-replay-rows-aux
                     (cons row rest) base held handoffs prior next-arrival))
           :in-theory (disable fn-bpnf-family-replay-rows-aux
                               fn-bpnf-family-replay-row-record
                               fn-bpnf-stored-record-name
                               fn-bpnf-replay-pair-afterp
                               fn-bpnf-receive-decision
                               fn-bpnf-held-octets fn-bpnf-held-bundle
                               fn-bpnf-held-wire
                               fn-bpn-machine-state-max-jobs
                               fn-bpn-machine-state-max-octets
                               fn-bpnr-family-replay-aux-cons))))

; Keystone: whatever prefix replayed, the next well-formed received row whose
; image does not fit the profile's held octets makes the whole replay the
; named verdict; the image is never dropped and the rest never truncated.
(defthm fn-bpnpf-replay-past-the-octets-is-refused
  (let ((r (fn-bpnf-family-replay-rows-aux
            prefix base held handoffs prior next-arrival)))
    (implies (and (true-listp prefix)
                  (equal (car r) :ready)
                  (fn-bpnpf-kind-five-row-fitsp
                   row (fn-bpn-nth 1 r) (fn-bpn-nth 3 r) (fn-bpn-nth 4 r))
                  (< (fn-bpn-machine-state-max-octets base)
                     (+ (fn-bpnf-held-octets (fn-bpn-nth 1 r))
                        (len (fn-bpnpf-kind-five-row-image row)))))
             (equal (fn-bpnf-family-replay-rows-aux
                     (append prefix (cons row rest))
                     base held handoffs prior next-arrival)
                    (list :fault :held-beyond-profile))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-family-replay-aux-append
                  (suffix (cons row rest)))
                 (:instance fn-bpnpf-row-past-the-octets-is-named
                  (held (fn-bpn-nth 1 (fn-bpnf-family-replay-rows-aux
                                       prefix base held handoffs prior next-arrival)))
                  (handoffs (fn-bpn-nth 2 (fn-bpnf-family-replay-rows-aux
                                           prefix base held handoffs prior next-arrival)))
                  (prior (fn-bpn-nth 3 (fn-bpnf-family-replay-rows-aux
                                        prefix base held handoffs prior next-arrival)))
                  (next-arrival (fn-bpn-nth 4 (fn-bpnf-family-replay-rows-aux
                                               prefix base held handoffs prior next-arrival)))))
           :in-theory (disable fn-bpnf-family-replay-rows-aux
                               fn-bpnr-family-replay-aux-append
                               fn-bpnpf-row-past-the-octets-is-named
                               fn-bpnr-family-replay-aux-cons
                               fn-bpnpf-kind-five-row-fitsp
                               fn-bpnpf-kind-five-row-image
                               fn-bpnf-held-octets))))

; The restart step fences with the replay's named verdict: a journal past its
; profile is refused at open with :held-beyond-profile, which the host prints
; (host/native/bp-service.lisp, the :restart-fault effect).
(defthm fn-bpnpf-restart-names-held-beyond-profile
  (equal (fn-bpnf-recover-fnbs-step st new-epoch base-records sequence-ready
                                    '(:fault :held-beyond-profile))
         (fn-bpnf-answer st '((:restart-fault :held-beyond-profile))))
  :hints (("Goal" :in-theory (disable fn-bpn-restart-step fn-bpnf-answer))))
