; Teeth for fn-bprpf-row-wfp and the selection admit's :row-outside-the-profile arm
; (books/bp-recovery-profile.lisp).  Every witness is derived from the real
; producers and codecs; no octet is pinned.
(in-package "ACL2")
(include-book "../../books/bp-recovery-profile")
(include-book "bp-recovery-profile-tests")
(include-book "must-fail-checked")

(defconst *bprw-profile* '(8 1048576 65538 1048576))

(defun bprw-all (rows profile)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (cons (fn-bprpf-row-wfp (car rows) profile) (bprw-all (cdr rows) profile))
    nil))
(defun bprw-all-tp (xs)
  (declare (xargs :guard t))
  (if (consp xs) (and (car xs) (bprw-all-tp (cdr xs))) t))

; ---------------------------------------------------------------------------
; 1. Every slot recognizer against the real producer of that slot.
; fn-bpnf-frame-held: a row at birth (the producer of kind-5 receptions), over the family fixture's bundle
(defconst *bprw-h0*
  (fn-bpnf-frame-held (fn-bpn-nth 4 (bprpft-held)) 0
                      (fn-bpnf-held-bundle (bprpft-held)) (fn-bpnf-held-wire (bprpft-held))))
(defconst *bprw-peer* (cons :dtn '(47 47 112 101 101 114 47)))
(defconst *bprw-session* (cons 2 7))
(defconst *bprw-id* (fn-bpp-primary-identity (fn-bpb-bundle-primary (fn-bpnf-held-bundle *bprw-h0*))))
; slots 10, 11, 12: fn-bpnp-dispatched-held
(defconst *bprw-dispatched* (fn-bpnp-dispatched-held *bprw-h0* *bprw-peer*))
; slot 13: fn-bpnp-attempted-held over a kind-8 record; then the kind-9 results
(defconst *bprw-attempt*
  (fn-bpnp-forward-attempt-record 5 1 (fn-bpn-nth 3 *bprw-h0*) *bprw-id* *bprw-peer* *bprw-session* nil))
(defconst *bprw-forwarding* (fn-bpnp-attempted-held *bprw-dispatched* *bprw-attempt*))
(defconst *bprw-uncertain* (fn-bpnp-forward-result-held *bprw-forwarding* :uncertain))
(defconst *bprw-sent* (fn-bpnp-forward-result-held *bprw-forwarding* :sent))
; slot 13 busy: fn-bpnp-deferred-held
(defconst *bprw-busy* (fn-bpnp-deferred-held *bprw-h0* 2))
; slot 10 delivered, slot 12 done: fn-bpah-delivered-held
(defconst *bprw-delivered*
  (fn-bpah-delivered-held *bprw-h0*
    (fn-bpah-delivery-record 5 1 (fn-bpn-nth 3 *bprw-h0*) *bprw-id* :request-accepted '(114 105 100))))
; slot 14: fn-bpn-report-tombstone-held (the replay of a kind-10 record)
(defconst *bprw-tombstone* (car (nth 1 (bpnfr-delete-answer))))
; slots 6, 9: the kind-18 family row (fn-bpnf-family-apply)
(defconst *bprw-reassembled* (car (nth 1 (bpnfr-replay-answer))))
; slot 9: fn-bpnf-received-anchor, both tags
(defconst *bprw-wall* (update-nth 9 (fn-bpnf-received-anchor (fn-bpnf-held-bundle *bprw-h0*) (fn-clock-observation 1000 0 0 nil)) *bprw-h0*))
(defconst *bprw-aged-bundle*
  (let ((b (fn-bpnf-held-bundle *bprw-h0*)))
    (fn-bpb-make-bundle (fn-bpb-bundle-primary b)
                        (cons (fn-bpb-bundle-age-block 9 0 0 500) (fn-bpb-bundle-blocks b))
                        (fn-bpb-bundle-payload b))))
(defconst *bprw-observed*
  (fn-bpnf-frame-held-with-anchor
   (fn-bpn-nth 4 *bprw-h0*) (fn-bpn-nth 3 *bprw-h0*) *bprw-aged-bundle*
   (fn-bpb-encode *bprw-aged-bundle*)
   (fn-bpnf-received-anchor *bprw-aged-bundle* (fn-clock-observation 1000 55 7 t))))

(defconst *bprw-honest*
  (list *bprw-h0* *bprw-dispatched* *bprw-forwarding* *bprw-uncertain* *bprw-sent*
        *bprw-busy* *bprw-delivered* *bprw-tombstone* *bprw-reassembled*
        *bprw-wall* *bprw-observed*))
(assert-event (equal (bprw-all *bprw-honest* *bprw-profile*) (make-list 11 :initial-element t)))
; the producers really did write the slots claimed (the witnesses are not vacuous)
(assert-event
 (and (equal (fn-bpn-nth 10 *bprw-dispatched*) '(:dispatched :forward))
      (equal (fn-bpn-nth 11 *bprw-dispatched*) *bprw-peer*)
      (equal (fn-bpn-nth 12 *bprw-dispatched*) '(:forward-pending))
      (equal (car (fn-bpn-nth 13 *bprw-forwarding*)) :forwarding)
      (equal (car (fn-bpn-nth 13 *bprw-uncertain*)) :uncertain)
      (null (fn-bpn-nth 13 *bprw-sent*))
      (equal (fn-bpn-nth 12 *bprw-sent*) '(:dispatch-done))
      (equal (fn-bpn-nth 13 *bprw-busy*) '(:busy 2))
      (equal (car (fn-bpn-nth 10 *bprw-delivered*)) :delivered)
      (equal (car (fn-bpn-nth 14 *bprw-tombstone*)) :bpnf-deleted)
      (equal (car (fn-bpn-nth 6 *bprw-reassembled*)) :reassembled)
      (equal (fn-bpn-nth 9 *bprw-wall*) '(:wall))
      (equal (car (fn-bpn-nth 9 *bprw-observed*)) :observed-age)))

; ---------------------------------------------------------------------------
; 2. (a) The ce3 row: a 65,536-octet principal in a selected-checkpoint row.
; heldp holds, the ADU fits, the old admit said :ready; the row recognizer refuses.
(defconst *bprw-local* (cons :dtn '(47 47 114 101 99 101 105 118 101 114 47)))
(defconst *bprw-sender* (cons :dtn '(47 47 115 101 110 100 101 114 47)))
(defconst *bprw-config* (fn-bpn-config *bprw-sender* 3600000 2 32 1048576))
(defconst *bprw-adu*
  (fn-bpa-encode (fn-bpa-make-request "w" "s" "dtn://sender/" "dtn://receiver/" "p" "i" "c" "t" '(88 13 10))))
(defconst *bprw-bundle*
  (fn-bpn-send-bundle *bprw-config* *bprw-local* *bprw-adu* 7 (fn-clock-observation 1000 0 0 nil)))
(defconst *bprw-big-ingress*
  (list :cl (cons 1 1) 1 *bprw-sender* (make-list 65536 :initial-element 97) 0))
(defconst *bprw-ce3*
  (fn-bpnf-held (fn-bpnf-ingress-principal *bprw-big-ingress*) (fn-bpb-bundle-id *bprw-bundle*) 0
                *bprw-big-ingress* nil nil *bprw-bundle* (fn-bpb-encode *bprw-bundle*)
                nil nil nil '(:dispatch-pending) nil nil 0))
(defconst *bprw-ce3-ck* (fn-bpnr-checkpoint 4 (list *bprw-ce3*) nil '(3 . 0) 1 0 nil 0))
(defconst *bprw-budget* (fn-bpnr-depth-budget 4))
(defconst *bprw-ce3-sel*
  (fn-bpnr-checkpoint-decode (fn-bpnr-checkpoint-octets *bprw-ce3-ck* *bprw-budget*) *bprw-budget*))
(defconst *bprw-ce3-plan* (list :selected *bprw-ce3-sel*))
(defconst *bprw-default* (fn-bpnpf-profile-default))
(assert-event
 (and (equal *bprw-ce3-sel* *bprw-ce3-ck*)                 ; the file round-trips: the checkpoint is selected
      (fn-bpnr-checkpointp *bprw-ce3-sel*)
      (fn-bpnf-heldp *bprw-ce3*)
      (not (fn-bpnf-frame-ingressp (fn-bpn-nth 4 *bprw-ce3*)))
      (fn-bprpf-held-adus-fitp (fn-bpnr-checkpoint-held *bprw-ce3-sel*)
                               (fn-bpnpf-adu-octets *bprw-default*))   ; the pre-fix admit's only row check passes
      (not (fn-bprpf-row-wfp *bprw-ce3* *bprw-default*))
      (equal (fn-bprpf-selection-admit *bprw-ce3-plan* *bprw-default*)
             '(:fault :row-outside-the-profile))))

; (b) The honest rotated checkpoint of rev2 witnesses.lsp: bundle -> held row -> kind-5 frame ->
; rows -> replay -> rotation checkpoint -> file -> decode (the selected checkpoint).
(defun bprw-octs (n) (declare (xargs :guard t :verify-guards nil))
  (if (zp n) nil (cons (+ 33 (mod n 90)) (bprw-octs (1- n)))))
(defun bprw-blocks (n k num) (declare (xargs :guard t :verify-guards nil))
  (if (zp n) nil
    (cons (fn-bpb-make-block 192 num 0 0 (bprw-octs k)) (bprw-blocks (1- n) k (1+ num)))))
(defun bprw-gen-bundle (nblocks k s p seq)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpb-make-bundle
   (fn-bpp-make-block 0 2 (list :ipn 2 7) (cons :dtn (append '(47 47 97 47) (bprw-octs s))) (list :dtn-none)
                      1000 seq 3600000 nil nil)
   (bprw-blocks nblocks k 2)
   (fn-bpb-payload-block 2 (bprw-octs p))))
(defun bprw-ingress (pl)
  (declare (xargs :guard t :verify-guards nil))
  (list :cl (cons 2 7) 3 (cons :dtn (append '(47 47) (bprw-octs pl) '(47))) '(112) 5))
(defun bprw-row (epoch i arrival nblocks k s p pl)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((b (bprw-gen-bundle nblocks k s p (+ 1000 i))) (w (fn-bpb-encode b))
         (h (fn-bpnf-frame-held (bprw-ingress pl) arrival b w))
         (rec (fn-bpnf-stored-record epoch i h)))
    (list (fn-bpnf-stored-record-name epoch i) (fn-bpnf-stored-record-frame rec))))
(defun bprw-rows (m epoch i arrival nblocks k s p pl)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp m) nil
    (cons (bprw-row epoch i arrival nblocks k s p pl)
          (bprw-rows (1- m) epoch (1+ i) (1+ arrival) nblocks k s p pl))))
(defconst *bprw-w-config* (fn-bpn-config (cons :dtn '(47 47 102 110 45 97 47)) 3600000 2 32 1048576))
(defconst *bprw-w-base* (fn-bpn-initial-machine-state *bprw-w-config* 64 16777216))
(defconst *bprw-w-budget* (fn-bpnr-depth-budget 64))
(defconst *bprw-w-rep* (fn-bpnf-family-replay-rows (bprw-rows 3 9 0 0 4 20 60 100 9) *bprw-w-base*))
(defconst *bprw-w-ck*
  (fn-bpnr-rotation-checkpoint (fn-bpnr-checkpoint-of-replay 1 *bprw-w-rep* 3 nil 0) 9))
(defconst *bprw-w-file* (fn-bpnr-checkpoint-octets *bprw-w-ck* *bprw-w-budget*))
(defconst *bprw-w-sel* (fn-bpnr-checkpoint-decode *bprw-w-file* *bprw-w-budget*))
(defconst *bprw-w-plan* (list :selected *bprw-w-sel*))
(assert-event
 (and (equal (car *bprw-w-rep*) :ready)
      (equal *bprw-w-sel* *bprw-w-ck*)
      (fn-bpnr-checkpointp *bprw-w-sel*)
      (equal (len (fn-bpnr-checkpoint-held *bprw-w-sel*)) 3)
      (equal (bprw-all (fn-bpnr-checkpoint-held *bprw-w-sel*) *bprw-default*) '(t t t))
      (fn-bprpf-rows-wfp (fn-bpnr-checkpoint-held *bprw-w-sel*) *bprw-default*)
      (equal (fn-bprpf-selection-admit *bprw-w-plan* *bprw-default*) '(:ready))))

; ---------------------------------------------------------------------------
; 3. One removal per conjunct.  BPRW-CONJUNCTS lists fn-bprpf-row-wfp's conjuncts in
; order; the fidelity assertions tie the list to the real recognizer on every witness.
(defun bprw-conjuncts (h profile)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-bpnpf-profilep profile)                                       ; 0
        (fn-bpnf-heldp h)                                                 ; 1
        (fn-bpnf-frame-ingressp (fn-bpn-nth 4 h))                         ; 2
        (<= (len (fn-bpnf-held-wire h)) (fn-bpnpf-bundle-octets profile)) ; 3
        (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h))
            (fn-bpnpf-adu-octets profile))                                ; 4
        (null (fn-bpn-nth 5 h))                                           ; 5 submission
        (fn-bprpf-lineagep (fn-bpn-nth 6 h) (nfix (fn-bpnpf-rows profile))) ; 6 lineage
        (or (null (fn-bpn-nth 9 h)) (fn-bpnf-stored-anchorp (fn-bpn-nth 9 h))) ; 7 anchor
        (fn-bprpf-dispatchp (fn-bpn-nth 10 h))                            ; 8 dispatch
        (or (null (fn-bpn-nth 11 h)) (fn-bpp-eidp (fn-bpn-nth 11 h)))     ; 9 next hop
        (if (member-equal (fn-bpn-nth 12 h)
                          '((:dispatch-pending) (:forward-pending) (:dispatch-done)))
            t nil)                                                        ; 10 constraints
        (fn-bprpf-attemptp (fn-bpn-nth 13 h))                             ; 11 attempt
        (or (null (fn-bpn-nth 14 h))
            (fn-bpn-report-delete-recordp (fn-bpn-nth 14 h)))))           ; 12 deleted

; every conjunct but the K-th holds
(defun bprw-only-false (xs k)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (if (equal k 0) (not (car xs)) (car xs))
           (bprw-only-false (cdr xs) (- (ifix k) 1)))
    t))

(defun bprw-tooth (k h profile)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-bprpf-row-wfp h profile)
              (if (bprw-all-tp (bprw-conjuncts h profile)) t nil))
       (bprw-only-false (bprw-conjuncts h profile) k)
       (not (fn-bprpf-row-wfp h profile))
       (<= (+ k 1) (len (bprw-conjuncts h profile)))
       (equal (len (bprw-conjuncts h profile)) 13)))

(defconst *bprw-small-bundle*     ; a valid profile whose bundle limit is one octet under h0's wire
  (list 8 1048576 65538 (1- (len (fn-bpnf-held-wire *bprw-h0*)))))

(assert-event (bprw-tooth 0 *bprw-h0* '(8 1048576 65538 2000000000)))                       ; profilep
(assert-event (bprw-tooth 1 (update-nth 2 '(0) *bprw-h0*) *bprw-profile*))               ; heldp (id <> bundle id)
(assert-event (bprw-tooth 2 *bprw-ce3* *bprw-default*))                                  ; frame-ingressp (ce3)
(assert-event (bprw-tooth 3 *bprw-h0* *bprw-small-bundle*))                              ; wire <= bundle limit
(assert-event (bprw-tooth 4 *bprw-h0* '(8 1048576 7 1048576)))                           ; ADU fit
(assert-event (bprw-tooth 5 (update-nth 5 '(:submitted) *bprw-h0*) *bprw-profile*))      ; submission
(assert-event (bprw-tooth 6 (update-nth 6 '(:reassembled ((nil (1) 0))) *bprw-h0*) *bprw-profile*)) ; lineage entry
(assert-event (bprw-tooth 7 (update-nth 9 '(:observed-age 1) *bprw-h0*) *bprw-profile*)) ; anchor
(assert-event (bprw-tooth 8 (update-nth 10 '(:delivered :bogus (1)) *bprw-h0*) *bprw-profile*)) ; dispatch
(assert-event (bprw-tooth 9 (update-nth 11 '(1 2 3) *bprw-h0*) *bprw-profile*))          ; next hop
(assert-event (bprw-tooth 10 (update-nth 12 '(:reassembly-consumed) *bprw-h0*) *bprw-profile*)) ; constraints
(assert-event (bprw-tooth 11 (update-nth 13 '(:forwarding 1 2) *bprw-h0*) *bprw-profile*)) ; attempt
(assert-event (bprw-tooth 12 (update-nth 14 '(:bpnf-deleted) *bprw-h0*) *bprw-profile*)) ; deleted
; lineage's count bound: the honest family row, under a profile with fewer rows than it consumed
(assert-event
 (and (< 1 (len (fn-bpn-nth 1 (fn-bpn-nth 6 *bprw-reassembled*))))
      (bprw-tooth 6 *bprw-reassembled* '(1 1048576 65538 1048576))))
