; Witnesses and teeth for lane k0-cuts: the root barrier from any related
; state (fn-bs-k0s-root-fence-preserves-relation, and its :ok arm in
; fn-bs-k0-step-inputp), the stage prefix derived by the keystone
; (fn-bs-k0p-stage-pairs-by-step), and the frontier and record corollaries
; it closes: created-and-written, staged-durable, record-linked and
; frontier-durable.  Witnesses are reachable: the K5 fixture's second
; allocation (bsk0-f-good) and second publication (bsk5-record-2-run).
(in-package "ACL2")
(include-book "../../books/byte-store-k0-step-bridge-frontier")
(include-book "byte-store-k0-tests")
(include-book "byte-store-k0-step-bridge-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bskc-f (k) (nth k (bsk0-f-good)))
(defun bskc-r (k) (nth k (bsk5-record-2-run)))
(defun bskc-fence-ok (bs ks) (fn-bs-store-relation (fn-bs-fence-dir bs :root) ks))

; ---------------------------------------------------------------------------
; The root barrier.  Witness: the frontier run's attempted pair 11 -- related,
; the frontier rename pending on :root, kernel :frontier-attempted.  The
; fence lemma's conclusion holds there, and so do the keystone's new :ok arm
; and its conclusion for the step the frontier program takes next.
(assert-event (fn-bs-store-relation (car (bskc-f 11)) (cdr (bskc-f 11))))
(assert-event (consp (fn-bs-ops-for-dir (fn-bs-pending (car (bskc-f 11))) :root)))
(assert-event (equal (fn-sf-phase (cdr (bskc-f 11))) :frontier-attempted))
(assert-event (not (fn-bs-replay-visiblep (cdr (bskc-f 11)))))
(assert-event (bskc-fence-ok (car (bskc-f 11)) (cdr (bskc-f 11))))
(assert-event (not (equal (fn-bs-fence-dir (car (bskc-f 11)) :root) (car (bskc-f 11)))))
(assert-event (bsks-ok (car (bskc-f 11)) (cdr (bskc-f 11)) '(:fsync-dir :root) :ok))
; The quiet-root arm: the record run's attempted pair 10 (a transaction link
; pending, nothing on :root); the fence is the identity there.
(assert-event (not (fn-bs-ops-for-dir (fn-bs-pending (car (bskc-r 10))) :root)))
(assert-event (bsks-ok (car (bskc-r 10)) (cdr (bskc-r 10)) '(:fsync-dir :root) :ok))
; Tooth: the relation.  The initial byte image under the same kernel.
(assert-event (not (fn-bs-store-relation (bsk5-initial) (cdr (bskc-f 11)))))
(must-fail (assert-event (bskc-fence-ok (bsk5-initial) (cdr (bskc-f 11)))))
; (not (fn-bs-replay-visiblep ks)) has no must-fail: it is the recovery-window
; guard every kind of fn-bs-k0-step-inputp carries, and the fence is not
; shown to need it.

; ---------------------------------------------------------------------------
; The stage prefix: create, write-all and fsync-file on a fresh staging name.
(defun bskc-stage-concl (bs ks stage octets)
  (and (fn-bs-store-relation (fn-bs-k0p-s1 bs stage) ks)
       (fn-bs-store-relation (fn-bs-k0p-s2 bs stage octets) ks)
       (fn-bs-store-relation (fn-bs-k0p-s3 bs stage octets) ks)))
(defun bskc-stage-hyps (bs ks stage octets)
  (and (fn-bs-store-relation bs ks)
       (not (fn-bs-replay-visiblep ks))
       (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
       (not (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
       (fn-bs-namep stage)
       (not (fn-bs-lookup bs :staging stage))
       (fn-cbor-octet-listp octets)))
(defun bskc-rb () (car (bsk0-r-start)))
(defun bskc-rk () (bsk0-r-prepared))
; Witness: the second publication's entry pair and its frame; the stage
; states are the record run's pairs 1, 3 and 5.
(assert-event (bskc-stage-hyps (bskc-rb) (bskc-rk) ".stage-k5-2" (bsk5-frame-2)))
(assert-event (bskc-stage-concl (bskc-rb) (bskc-rk) ".stage-k5-2" (bsk5-frame-2)))
(assert-event (equal (car (bskc-r 5)) (fn-bs-k0p-s3 (bskc-rb) ".stage-k5-2" (bsk5-frame-2))))
; Teeth.  The relation: the initial image under the prepared kernel.
(must-fail (assert-event (bskc-stage-concl (bsk5-initial) (bskc-rk) ".stage-k5-2" (bsk5-frame-2))))
; A name: stage 7 is not one, and the create's entry makes the state ill-formed.
(assert-event (not (fn-bs-namep 7)))
(must-fail (assert-event (bskc-stage-concl (bskc-rb) (bskc-rk) 7 (bsk5-frame-2))))
; The stage absent: occupied by inode 0, the write lands on that inode.
(defun bskc-occupied ()
  (let ((bs (bskc-rb)))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs)
                (put-assoc-equal :staging
                                 (cons (cons ".stage-k5-2" 0)
                                       (cdr (assoc-equal :staging (fn-bs-dirs bs))))
                                 (fn-bs-dirs bs))
                (fn-bs-pending bs) (fn-bs-next-ino bs))))
(assert-event (fn-bs-lookup (bskc-occupied) :staging ".stage-k5-2"))
(must-fail (assert-event (bskc-stage-concl (bskc-occupied) (bskc-rk) ".stage-k5-2" (bsk5-frame-2))))
; Typed octets.
(must-fail (assert-event (bskc-stage-concl (bskc-rb) (bskc-rk) ".stage-k5-2" '(300))))
; The quiet root and transaction directories and the recovery-window guard
; are the keystone's step-input guards (the file barrier's and every kind's);
; the conclusion is not shown to need them.  At the frontier run's replaced
; pair (a rename pending on :root) the conclusion holds anyway -- stated as a
; test, not a tooth.
(assert-event (consp (fn-bs-ops-for-dir (fn-bs-pending (car (bskc-f 9))) :root)))
(assert-event (bskc-stage-concl (car (bskc-f 9)) (cdr (bskc-f 9)) ".stage-k0-cuts" (bsk5-frame-2)))

; ---------------------------------------------------------------------------
; The corollaries.  Witness: every hypothesis holds, every claimed cut is
; related (the run reaches it).
(defun bskc-fb () (car (bsk0-f-start)))
(defun bskc-fk () (cdr (bsk0-f-start)))
(defun bskc-frontier-cuts (bs ks stage octets)
  (let ((run (bsk0-f-run bs ks stage octets)))
    (and (bsk0-related-at run 2) (bsk0-related-at run 4) (bsk0-related-at run 7)
         (bsk0-related-at run 13))))
(defun bskc-record-cuts (bs ks stage name frame)
  (let ((run (bsk0-r-run bs ks stage name frame)))
    (and (bsk0-related-at run 1) (bsk0-related-at run 3) (bsk0-related-at run 6)
         (bsk0-related-at run 8))))
(assert-event (and (fn-bs-store-relation (bskc-fb) (bskc-fk))
                   (fn-bs-frontier-inputp (bskc-fk) ".allocation-k0" (fn-bs-frontier-encode 2))
                   (not (fn-bs-lookup (bskc-fb) :staging ".allocation-k0"))))
(assert-event (bskc-frontier-cuts (bskc-fb) (bskc-fk) ".allocation-k0" (fn-bs-frontier-encode 2)))
(assert-event (and (fn-bs-store-relation (bskc-rb) (bskc-rk))
                   (fn-bs-record-inputp (bskc-rk) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))
                   (not (fn-bs-lookup (bskc-rb) :staging ".stage-k5-2"))))
(assert-event (bskc-record-cuts (bskc-rb) (bskc-rk) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2)))
; The link inputs at pair 6 hold on the witness, and the link lands.
(assert-event (bsks-ok (car (bskc-r 6)) (cdr (bskc-r 6))
                       (list :link :staging ".stage-k5-2" :transactions (fn-bs-txn-name 1)) :ok))
; Teeth, per hypothesis.  The relation: the initial byte image under the
; same kernels.
(must-fail (assert-event (bskc-frontier-cuts (bsk5-initial) (bskc-fk) ".allocation-k0" (fn-bs-frontier-encode 2))))
(must-fail (assert-event (bskc-record-cuts (bsk5-initial) (bskc-rk) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))))
; The input contract, by its octet type: untyped octets make the write's
; state ill-formed (and the frontier input and record input fail).
(assert-event (not (fn-bs-frontier-inputp (bskc-fk) ".allocation-k0" '(300))))
(must-fail (assert-event (bskc-frontier-cuts (bskc-fb) (bskc-fk) ".allocation-k0" '(300))))
(assert-event (not (fn-bs-record-inputp (bskc-rk) ".stage-k5-2" (fn-bs-txn-name 1) '(300))))
(must-fail (assert-event (bskc-record-cuts (bskc-rb) (bskc-rk) ".stage-k5-2" (fn-bs-txn-name 1) '(300))))
; The record input contract by its frame: the FIRST record's frame under the
; second name; the link lands on a target that does not read as the
; candidate, and the linked cut (pair 8) is not related.
(assert-event (not (fn-bs-record-inputp (bskc-rk) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame))))
(must-fail (assert-event (bsk0-related-at (bsk0-r-run (bskc-rb) (bskc-rk) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame)) 8)))
; The absent stage: O_EXCL fails and the run stops at its first syscall.
(must-fail (assert-event (bskc-frontier-cuts (bsk0-f-occupied) (bskc-fk) ".allocation-k0" (fn-bs-frontier-encode 2))))
(must-fail (assert-event (bskc-record-cuts (bskc-occupied) (bskc-rk) ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))))
