; Witnesses and teeth for lane k0-recovery: the recovery window as step kinds
; of the general K0 step (books/byte-store-k0-window.lisp,
; fn-bs-k0w-step-preserves-relation, and its disjunct of
; fn-bs-k0-step-inputp), the recovery program by the step
; (fn-bs-k0v-recover-program-by-step) and the in-process re-recovery at
; host/native/admin.lisp:107 (fn-bs-k0v-host-rerecovery-keeps-relation-at-every-cut),
; both in books/byte-store-k0-recover-program.lisp.
;
; Witnesses are reachable: a process that dies with the K5 fixture's second
; publication at its attempted pair 10 (the transaction link issued, not
; fenced) or its second allocation at its attempted pair 11 (the frontier
; rename issued, not fenced) leaves that pending entry in the page cache;
; the next process reads the live view and reopens at the kernel
; fn-cpo-open-observed installs, (fn-bs-recovered-kernel f r 0) over the
; scanned frontier and records.
(in-package "ACL2")
(include-book "../../books/byte-store-k0-recover-program")
(include-book "byte-store-k0-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bskv-configs* (list *fn-cfg-default-record*))
(defun bskv-f (k) (nth k (bsk0-f-good)))
(defun bskv-r (k) (nth k (bsk5-record-2-run)))
; The keystone's precondition and conclusion at one step.
(defun bskv-step-ok (bs ks step outcome)
  (and (fn-bs-k0-step-inputp bs ks step outcome)
       (mv-let (r bs1 ks1) (fn-bs-step bs ks step outcome *bsk5-groups* *bsk5-capacity*)
         (declare (ignore r))
         (and (fn-bs-k0-coveredp bs1 ks1)
              (or (equal ks1 ks) (equal (car step) :observe))))))
(defun bskv-k (bs n)
  (fn-bs-recovered-kernel (fn-bs-scan-frontier (fn-bs-scan-store bs))
                          (fn-bs-scan-records (fn-bs-scan-store bs)) n))
(defun bskv-run (bs ks) (fn-bs-run bs ks (fn-bs-recover-program) nil nil nil))
(defun bskv-prog-concl (bs ks)
  (let ((run (bskv-run bs ks)))
    (and (fn-bs-k0v-steps-coveredp (cons (cons bs ks) run) (fn-bs-recover-program))
         (fn-bs-run-relatedp run)
         (equal (len run) 17)
         (equal (car (nth 16 run)) (fn-bs-k0v-drained bs))
         (equal (fn-sf-phase (cdr (nth 16 run))) :ready))))
(defun bskv-link () (car (bskv-r 10)))
(defun bskv-rename () (car (bskv-f 11)))

; ---------------------------------------------------------------------------
; The window with a pending link.  Related to the reopened kernel, which
; holds the linked record the durable namespace does not yet name.
(assert-event (consp (fn-bs-ops-for-dir (fn-bs-pending (bskv-link)) :transactions)))
(assert-event (fn-bs-replay-visiblep (bskv-k (bskv-link) 0)))
(assert-event (fn-bs-store-relation (bskv-link) (bskv-k (bskv-link) 0)))
(assert-event (equal (len (fn-sf-records (bskv-k (bskv-link) 0)))
                     (1+ (len (fn-bs-durable-names (bskv-link) :transactions)))))
(assert-event (bskv-prog-concl (bskv-link) (bskv-k (bskv-link) 0)))
(assert-event (not (equal (fn-bs-k0v-drained (bskv-link)) (bskv-link))))
; The keystone's window arms at this pair.
(assert-event (bskv-step-ok (bskv-link) (bskv-k (bskv-link) 0) '(:fsync-dir :transactions) :ok))
(assert-event (bskv-step-ok (bskv-link) (bskv-k (bskv-link) 0) '(:observe (:recover)) :ok))
(assert-event (bskv-step-ok (bskv-link) (bskv-k (bskv-link) 0) (list :fsync-file :root *fn-bs-config-name*) '(:eio)))
(assert-event (bskv-step-ok (bskv-link) (bskv-k (bskv-link) 0) '(:fsync-dir :root) '(:eio)))
(assert-event (bskv-step-ok (bskv-link) (bskv-k (bskv-link) 3) '(:observe (:recovery-barrier :uncertain)) :ok))
; The window with a pending frontier rename: the durable frontier is the
; scanned one minus one, and the root barrier lands it.
(assert-event (consp (fn-bs-ops-for-dir (fn-bs-pending (bskv-rename)) :root)))
(assert-event (fn-bs-store-relation (bskv-rename) (bskv-k (bskv-rename) 0)))
(assert-event (equal (fn-bs-durable-frontier (bskv-rename))
                     (1- (fn-sf-frontier (bskv-k (bskv-rename) 0)))))
(assert-event (bskv-prog-concl (bskv-rename) (bskv-k (bskv-rename) 0)))
(assert-event (bskv-step-ok (bskv-rename) (bskv-k (bskv-rename) 3) '(:fsync-dir :root) :ok))

; Teeth for the window step precondition (fn-bs-k0w-step-inputp).
; (a) A directory barrier's error outcome with an authority entry pending:
; landing the link keeps the relation, dropping it does not, so the arm is
; restricted to :ok or a quiet directory.
(defun bskv-dir-eio (bs choice)
  (mv-nth 1 (fn-bs-fsync-dir bs :transactions (list :eio choice))))
(assert-event (not (fn-bs-k0-step-inputp (bskv-link) (bskv-k (bskv-link) 0)
                                         '(:fsync-dir :transactions) '(:eio :drop))))
(assert-event (fn-bs-store-relation (bskv-dir-eio (bskv-link) :apply) (bskv-k (bskv-link) 0)))
(must-fail (assert-event (fn-bs-store-relation (bskv-dir-eio (bskv-link) :drop) (bskv-k (bskv-link) 0))))
; (b) The quiet clause of an observation that leaves the window: the fifth
; barrier with the link still pending lands the kernel on :ready, whose
; relation reads the durable records, which lack the linked one.
(assert-event (not (fn-bs-k0-step-inputp (bskv-link) (bskv-k (bskv-link) 4)
                                         '(:observe (:recovery-barrier :ok)) :ok)))
(assert-event (fn-bs-store-relation (bskv-link) (bskv-k (bskv-link) 4)))
(must-fail (assert-event (fn-bs-store-relation (bskv-link) (bskv-k (bskv-link) 5))))
; (c) The relation: the initial byte image under the reopened kernel.
(must-fail (assert-event (bskv-prog-concl (bsk5-initial) (bskv-k (bskv-link) 0))))
; The fenced-target clause of :fsync-file has no must-fail here: the
; recovery program fsyncs only authority inodes, which the relation fences.

; ---------------------------------------------------------------------------
; The in-process re-recovery (admin.lisp:107).  Witness: the drained state
; the first recovery leaves, under its :ready kernel -- the pair an
; administrative process holds after opening the store.  It is not a crash
; image: a staging entry is still pending.
(defun bskv-open (configs bs)
  (fn-cpo-open-observed configs (fn-bs-scan-frontier (fn-bs-scan-store bs))
                        (fn-bs-scan-records (fn-bs-scan-store bs))))
(defun bskv-host (configs bs) (fn-sn-files (fn-sn-open-state (bskv-open configs bs))))
(defun bskv-rerecovery-concl (configs bs)
  (and (fn-bs-store-relation bs (bskv-host configs bs))
       (bskv-prog-concl bs (bskv-host configs bs))))
(defun bskv-admin () (fn-bs-k0v-drained (bskv-link)))
(defun bskv-admin-k () (bskv-k (bskv-link) 5))
(assert-event (fn-bs-store-relation (bskv-admin) (bskv-admin-k)))
(assert-event (not (fn-bs-replay-visiblep (bskv-admin-k))))
(assert-event (fn-bs-k0w-authority-quietp (bskv-admin)))
(assert-event (consp (fn-bs-pending (bskv-admin))))
(assert-event (fn-sn-open-okp (bskv-open *bskv-configs* (bskv-admin))))
(assert-event (bskv-rerecovery-concl *bskv-configs* (bskv-admin)))
(assert-event (equal (bskv-host *bskv-configs* (bskv-admin)) (bskv-k (bskv-admin) 0)))
; Teeth.  Open success: no configuration record, the open is refused.
(assert-event (not (fn-sn-open-okp (bskv-open nil (bskv-admin)))))
(must-fail (assert-event (bskv-rerecovery-concl nil (bskv-admin))))
; The relation: a pending write to the config inode with the octets it
; already holds.  The view, the scan and the open are unchanged; the config
; inode is no longer fenced, so no kernel is related to the state.
(defun bskv-unfenced ()
  (let* ((bs (bskv-admin))
         (ino (fn-bs-durable-entry bs :root *fn-bs-config-name*)))
    (mv-nth 1 (fn-bs-write bs ino 0 (fn-bs-durable-content bs ino) :ok))))
(assert-event (equal (fn-bs-scan-store (bskv-unfenced)) (fn-bs-scan-store (bskv-admin))))
(assert-event (fn-bs-k0w-authority-quietp (bskv-unfenced)))
(assert-event (fn-sn-open-okp (bskv-open *bskv-configs* (bskv-unfenced))))
(must-fail (assert-event (bskv-rerecovery-concl *bskv-configs* (bskv-unfenced))))
; The quiet hypothesis has no separating instance among these witnesses: the
; pending-link pair under its own publish-window kernel is related, and the
; re-recovery from it holds as well (it is the window witness above).  The
; hypothesis is what the host line provides, and it is sufficient, not
; shown necessary.
(assert-event (fn-bs-store-relation (bskv-link) (cdr (bskv-r 10))))
(assert-event (bskv-rerecovery-concl *bskv-configs* (bskv-link)))
