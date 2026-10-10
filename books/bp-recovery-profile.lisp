; PKT-311a: judge the actual recovered held data under the current ADU
; profile before installation, including rows restored from a checkpoint.
(in-package "ACL2")
(include-book "bp-node-profile-admission")
(include-book "bp-held-projection")

; This is an open-time pass, not a served-state invariant revalidation.
; The existing decoder has established held-row shape.  The ADU reading is
; the same ACL2 decision used by receive admission: fragment total length,
; otherwise payload length.
(defun fn-bprpf-held-adus-fitp (held limit)
  (declare (xargs :guard (natp limit)))
  (if (consp held)
      (and (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle (car held))) limit)
           (fn-bprpf-held-adus-fitp (cdr held) limit))
    (null held)))

(defthm fn-bprpf-held-adus-fitp-bounds-every-member
  (implies (and (fn-bprpf-held-adus-fitp held limit)
                (member-equal h held))
           (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h)) limit))
  :hints (("Goal" :induct (fn-bprpf-held-adus-fitp held limit)
           :in-theory (e/d (fn-bprpf-held-adus-fitp)
                           (fn-bpnpf-bundle-adu-length fn-bpnf-held-bundle))))
  :rule-classes nil)

; EVENT is the exact fn-bphp-recover-auto-event result.  A preexisting
; replay fault is preserved; no failed replay is changed into readiness.
(defun fn-bprpf-admit-recovery (event profile)
  (declare (xargs :guard t))
  (let ((replay (fn-bpn-nth 4 event)))
    (cond ((not (equal (fn-bpn-nth 0 replay) :ready)) event)
          ((not (fn-bpnpf-profilep profile))
           (update-nth 4 '(:fault :profile) (true-list-fix event)))
          ((not (fn-bprpf-held-adus-fitp (fn-bpn-nth 1 replay)
                                        (fn-bpnpf-adu-octets profile)))
           (update-nth 4 '(:fault :adu-beyond-profile) (true-list-fix event)))
          (t event))))

(defthm fn-bprpf-ready-recovery-bounds-every-held-adu
  (let ((replay (fn-bpn-nth 4 (fn-bprpf-admit-recovery event profile))))
    (implies (and (equal (fn-bpn-nth 0 replay) :ready)
                  (member-equal h (fn-bpn-nth 1 replay)))
             (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h))
                 (fn-bpnpf-adu-octets profile))))
  :hints (("Goal"
           :use ((:instance fn-bprpf-held-adus-fitp-bounds-every-member
                   (held (fn-bpn-nth 1 (fn-bpn-nth 4 event)))
                   (limit (fn-bpnpf-adu-octets profile))))
           :in-theory (e/d (fn-bprpf-admit-recovery fn-bpn-nth)
                           (fn-bprpf-held-adus-fitp fn-bpnpf-bundle-adu-length
                            fn-bpnf-held-bundle fn-bpnpf-profilep
                            fn-bpnpf-adu-octets))))
  :rule-classes nil)

; The host calls this on every bounded input frame before retaining the
; frame for replay.  In particular a later deletion cannot hide an ADU
; that would already have exceeded the profile during family replay.
(defun fn-bprpf-row-admit (octets profile)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :guard-hints
                  (("Goal" :in-theory
                    (disable fn-bpnf-stored-record-unframe
                             fn-bpnf-family-replay-unframe
                             fn-bpnpf-profilep fn-bpnpf-adu-octets
                             fn-bpnpf-bundle-octets fn-bpnpf-bundle-adu-length
                             fn-bpnf-held-bundle fn-bpnf-held-wire)))))
  (cond
   ((not (fn-bpnpf-profilep profile)) '(:fault :profile))
   (t
    (let* ((stored (fn-bpnf-stored-record-unframe octets))
           (h (fn-bpn-nth 3 stored)))
      (cond
       ((and stored
              (< (fn-bpnpf-adu-octets profile)
                 (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h))))
        '(:fault :adu-beyond-profile))
       ((and stored
              (< (fn-bpnpf-bundle-octets profile) (len (fn-bpnf-held-wire h))))
        '(:fault :bundle-beyond-profile))
       (t
        (let ((family (fn-bpnf-family-replay-unframe octets)))
          (if (and family
                    (< (fn-bpnpf-bundle-octets profile)
                       (len (fn-bpn-nth 5 family))))
              '(:fault :bundle-beyond-profile)
            '(:ready)))))))))

(defthm fn-bprpf-admitted-row-has-bounded-adu
  (implies (equal (fn-bprpf-row-admit octets profile) '(:ready))
           (<= (fn-bpnpf-bundle-adu-length
                (fn-bpnf-held-bundle
                 (fn-bpn-nth 3 (fn-bpnf-stored-record-unframe octets))))
               (fn-bpnpf-adu-octets profile)))
  :hints (("Goal" :cases ((fn-bpnf-stored-record-unframe octets))
           :in-theory (e/d (fn-bprpf-row-admit fn-bpn-nth fn-bpnf-held-bundle)
                                   (fn-bpnf-stored-record-unframe
                                    fn-bpnf-family-replay-unframe
                                    fn-bpnpf-profilep fn-bpnpf-adu-octets
                                    fn-bpnpf-bundle-octets))))
  :rule-classes nil)

;; The per-row recognizer of a selected checkpoint's held rows.  A checkpoint
;; file carries no authentication (its trailer is an unkeyed digest), so every
;; slot of every row is judged here against what the producers write there:
;;  5 submission: nil (no producer writes another value);
;;  6 lineage: nil, or (:reassembled CONSUMED) from fn-bpnf-family-apply
;;    (CONSUMED = fn-bpnf-family-consumed-ids: (principal id arrival) entries,
;;    at most the profile's rows);
;;  9 anchor: nil (old kind-5 row), or fn-bpnf-stored-anchorp (:wall /
;;    :observed-age; fn-bpnf-received-anchor, copied by the family row);
;; 10 dispatch: nil, (:dispatched :forward) (fn-bpnp-dispatched-held), or
;;    (:delivered STATUS DETAIL) (fn-bpah-delivered-held);
;; 11 next hop: nil, or the dispatch record's peer EID (fn-bpp-eidp);
;; 12 constraints: the three job states;
;; 13 attempt: nil, (:forwarding|:uncertain EPOCH OP PEER SESSION RETRIES)
;;    (fn-bpnp-attempted-held, fn-bpnp-forward-result-slot), or (:busy COUNT)
;;    (fn-bpnp-busy-slot);
;; 14 deleted: nil, or a fn-bpn-report-delete-recordp (the tombstone).
;; Where no recognizer existed (6, 10, 13) the three below are the smallest
;; that admit exactly those producer values.
(defun fn-bprpf-lineage-entryp (e)
  (declare (xargs :guard t))
  (and (true-listp e) (equal (len e) 3)
       (or (null (fn-bpn-nth 0 e)) (fn-bpn-machine-textp (fn-bpn-nth 0 e)))
       (true-listp (fn-bpn-nth 1 e)) (equal (len (fn-bpn-nth 1 e)) 6)
       (equal (car (fn-bpn-nth 1 e)) :fn-bp-bundle-id)
       (fn-bpp-eidp (fn-bpn-nth 1 (fn-bpn-nth 1 e)))
       (natp (fn-bpn-nth 2 e))))

(defun fn-bprpf-lineage-entriesp (es limit)
  (declare (xargs :guard (natp limit)))
  (if (consp es)
      (and (posp limit)
           (fn-bprpf-lineage-entryp (car es))
           (fn-bprpf-lineage-entriesp (cdr es) (1- limit)))
    (null es)))

(defun fn-bprpf-lineagep (x limit)
  (declare (xargs :guard (natp limit)))
  (or (null x)
      (and (true-listp x) (equal (len x) 2) (equal (car x) :reassembled)
           (fn-bprpf-lineage-entriesp (cadr x) limit))))

(defun fn-bprpf-dispatchp (x)
  (declare (xargs :guard t))
  (or (null x)
      (equal x '(:dispatched :forward))
      (and (true-listp x) (equal (len x) 3) (equal (car x) :delivered)
           (fn-bpah-disposition-code (fn-bpn-nth 1 x))
           (fn-cbor-octet-listp (fn-bpn-nth 2 x))
           (consp (fn-bpn-nth 2 x))
           (<= (len (fn-bpn-nth 2 x)) 256))))

(defun fn-bprpf-attemptp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (true-listp x) (equal (len x) 6)
           (member-equal (car x) '(:forwarding :uncertain))
           (fn-frame-natp (fn-bpn-nth 1 x))
           (fn-frame-natp (fn-bpn-nth 2 x))
           (fn-bpp-eidp (fn-bpn-nth 3 x))
           (fn-bpnp-session-idp (fn-bpn-nth 4 x))
           (natp (fn-bpn-nth 5 x)))
      (and (true-listp x) (equal (len x) 2) (equal (car x) :busy)
           (posp (fn-bpn-nth 1 x)) (fn-frame-natp (fn-bpn-nth 1 x)))))

(defun fn-bprpf-row-wfp (h profile)
  (declare (xargs :guard t))
  (and (fn-bpnpf-profilep profile)
       (fn-bpnf-heldp h)
       (fn-bpnf-frame-ingressp (fn-bpn-nth 4 h))
       (<= (len (fn-bpnf-held-wire h)) (fn-bpnpf-bundle-octets profile))
       (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h))
           (fn-bpnpf-adu-octets profile))
       (null (fn-bpn-nth 5 h))
       (fn-bprpf-lineagep (fn-bpn-nth 6 h) (nfix (fn-bpnpf-rows profile)))
       (or (null (fn-bpn-nth 9 h)) (fn-bpnf-stored-anchorp (fn-bpn-nth 9 h)))
       (fn-bprpf-dispatchp (fn-bpn-nth 10 h))
       (or (null (fn-bpn-nth 11 h)) (fn-bpp-eidp (fn-bpn-nth 11 h)))
       (member-equal (fn-bpn-nth 12 h)
                     '((:dispatch-pending) (:forward-pending) (:dispatch-done)))
       (fn-bprpf-attemptp (fn-bpn-nth 13 h))
       (or (null (fn-bpn-nth 14 h))
           (fn-bpn-report-delete-recordp (fn-bpn-nth 14 h)))))

(defun fn-bprpf-rows-wfp (held profile)
  (declare (xargs :guard t))
  (if (consp held)
      (and (fn-bprpf-row-wfp (car held) profile)
           (fn-bprpf-rows-wfp (cdr held) profile))
    (null held)))

; Read the checkpoint through the same selector the actual replay uses.
; No reassembly/fold can run before this decision.  Existing damaged-plan
; handling stays with the recovery interpreter.
(defun fn-bprpf-selection-admit (plan profile)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (fn-bpnpf-profilep profile)) '(:fault :profile))
        ((not (fn-bprpf-held-adus-fitp
                (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint plan))
                (fn-bpnpf-adu-octets profile)))
         '(:fault :adu-beyond-profile))
        ((not (fn-bprpf-rows-wfp
                (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint plan))
                profile))
         '(:fault :row-outside-the-profile))
        (t '(:ready))))

(verify-guards fn-bprpf-selection-admit
  :hints (("Goal" :in-theory (disable fn-bpnpf-profilep
                                      fn-bpnpf-adu-octets
                                      fn-bprpf-held-adus-fitp
                                      fn-bpnr-plan-checkpoint
                                      fn-bpnr-checkpoint-held))))

(defthm fn-bprpf-admitted-checkpoint-bounds-every-held-adu
  (implies
   (and (equal (fn-bprpf-selection-admit plan profile) '(:ready))
        (member-equal h (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint plan))))
   (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h))
       (fn-bpnpf-adu-octets profile)))
  :hints (("Goal"
           :use ((:instance fn-bprpf-held-adus-fitp-bounds-every-member
                   (held (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint plan)))
                   (limit (fn-bpnpf-adu-octets profile))))
           :in-theory (e/d (fn-bprpf-selection-admit)
                           (fn-bprpf-held-adus-fitp fn-bpnr-plan-checkpoint
                            fn-bpnr-checkpoint-held fn-bpnpf-bundle-adu-length
                            fn-bpnf-held-bundle fn-bpnpf-adu-octets))))
  :rule-classes nil)

;; KEYSTONE: a plan the admit answers :ready carries only well-formed rows.
(defthm fn-bprpf-rows-wfp-every-member
  (implies (and (fn-bprpf-rows-wfp held profile) (member-equal h held))
           (fn-bprpf-row-wfp h profile))
  :hints (("Goal" :induct (fn-bprpf-rows-wfp held profile)
           :in-theory (e/d (fn-bprpf-rows-wfp) (fn-bprpf-row-wfp)))))

(defthm fn-bprpf-admitted-checkpoint-rows-are-well-formed
  (implies (and (equal (fn-bprpf-selection-admit plan profile) '(:ready))
                (member-equal h (fn-bpnr-checkpoint-held
                                  (fn-bpnr-plan-checkpoint plan))))
           (fn-bprpf-row-wfp h profile))
  :hints (("Goal"
           :use ((:instance fn-bprpf-rows-wfp-every-member
                   (held (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint plan)))))
           :in-theory (e/d (fn-bprpf-selection-admit)
                           (fn-bprpf-rows-wfp-every-member fn-bprpf-rows-wfp
                            fn-bprpf-row-wfp fn-bprpf-held-adus-fitp
                            fn-bpnr-plan-checkpoint fn-bpnr-checkpoint-held))))
  :rule-classes nil)

(in-theory (disable fn-bprpf-held-adus-fitp fn-bprpf-admit-recovery))
