; Teeth for books/bp-checkpoint-size: the premise is inhabited and both
; keystone conclusions are true on an honest rotated checkpoint, every witness
; derived through the real producers (bundle -> held row -> kind-5 record frame
; -> replay -> rotation checkpoint -> published file -> the host's decode),
; nothing pinned.  The selection plan is the one the host asks at open.
(in-package "ACL2")
(include-book "../../books/bp-checkpoint-size")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defun bpcks-octs (n) (if (zp n) nil (cons (+ 33 (mod n 90)) (bpcks-octs (1- n)))))
(defun bpcks-blocks (n k num)
  (if (zp n) nil
    (cons (fn-bpb-make-block 192 num 0 0 (bpcks-octs k)) (bpcks-blocks (1- n) k (1+ num)))))
(defun bpcks-bundle (nblocks k s p seq)
  (fn-bpb-make-bundle
   (fn-bpp-make-block 0 2 (list :ipn 2 7) (cons :dtn (append '(47 47 97 47) (bpcks-octs s))) (list :dtn-none)
                      1000 seq 3600000 nil nil)
   (bpcks-blocks nblocks k 2)
   (fn-bpb-payload-block 2 (bpcks-octs p))))
(defun bpcks-ingress (pl) (list :cl (cons 2 7) 3 (cons :dtn (append '(47 47) (bpcks-octs pl) '(47))) '(112) 5))
(defun bpcks-row (epoch i arrival nblocks k s p pl)
  (let* ((b (bpcks-bundle nblocks k s p (+ 1000 i))) (w (fn-bpb-encode b))
         (h (fn-bpnf-frame-held (bpcks-ingress pl) arrival b w))
         (rec (fn-bpnf-stored-record epoch i h)))
    (list (fn-bpnf-stored-record-name epoch i) (fn-bpnf-stored-record-frame rec))))
(defun bpcks-rows (m epoch i arrival nblocks k s p pl)
  (if (zp m) nil (cons (bpcks-row epoch i arrival nblocks k s p pl)
                       (bpcks-rows (1- m) epoch (1+ i) (1+ arrival) nblocks k s p pl))))

; Constants computed through the codec seam are evaluated with attachments
; only inside make-event (:DOC ignored-attachment).
(make-event
 (let* ((config (fn-bpn-config (cons :dtn '(47 47 102 110 45 97 47)) 3600000 2 32 1048576))
        (base (fn-bpn-initial-machine-state config 64 16777216))
        (budget (fn-bpnr-depth-budget 64))
        (rows (bpcks-rows 3 9 0 0 4 20 60 100 9))
        (replay (fn-bpnf-family-replay-rows rows base))
        (ck (fn-bpnr-rotation-checkpoint (fn-bpnr-checkpoint-of-replay 1 replay 3 nil 0) 9))
        (file (fn-bpnr-checkpoint-octets ck budget)))
   `(progn (defconst *bpcks-budget* ,budget)
           (defconst *bpcks-file* ',file))))

(defconst *bpcks-plan* (fn-bpnr-selection-plan t *bpcks-file* *bpcks-budget*))
(defconst *bpcks-ck* (fn-bpnr-plan-checkpoint *bpcks-plan*))

; Premise inhabited: the plan selects a checkpoint, and it is one.
(assert-event (and *bpcks-file* (equal (car *bpcks-plan*) :selected)
                   *bpcks-ck* (fn-bpnr-checkpointp *bpcks-ck*)))

; KEYSTONE fn-bpck-selected-checkpoint-within-its-file, on the witness.
(assert-event (<= (fn-bpck-size *bpcks-ck*) (len *bpcks-file*)))

; KEYSTONE fn-bpck-selected-checkpoint-counts-within-its-file, on the witness.
(assert-event (<= (+ (len (fn-bpnr-checkpoint-held *bpcks-ck*))
                     (len (fn-bpnr-checkpoint-handoffs *bpcks-ck*))
                     (len (fn-bpnr-checkpoint-jobs *bpcks-ck*)))
                  (len *bpcks-file*)))

; The held rows are really there (the counts are not vacuously zero).
(assert-event (< 0 (len (fn-bpnr-checkpoint-held *bpcks-ck*))))

; Figures (printed by the certify run): size 4432, file octets 4478, held 3, handoffs 0, jobs 0.
(value-triple (cw "~%bpcks figures: size ~x0, file octets ~x1, held ~x2, handoffs ~x3, jobs ~x4~%"
                  (fn-bpck-size *bpcks-ck*) (len *bpcks-file*)
                  (len (fn-bpnr-checkpoint-held *bpcks-ck*))
                  (len (fn-bpnr-checkpoint-handoffs *bpcks-ck*))
                  (len (fn-bpnr-checkpoint-jobs *bpcks-ck*))))

; The premise has teeth: no file, or a damaged one, selects no checkpoint, so
; the keystones say nothing there.
(assert-event (null (fn-bpnr-plan-checkpoint (fn-bpnr-selection-plan nil *bpcks-file* *bpcks-budget*))))
(assert-event (null (fn-bpnr-plan-checkpoint
                     (fn-bpnr-selection-plan t (cdr *bpcks-file*) *bpcks-budget*))))
(assert-event (null (fn-bpnr-plan-checkpoint
                     (fn-bpnr-selection-plan t (append *bpcks-file* '(0)) *bpcks-budget*))))
