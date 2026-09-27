; Witnesses and teeth for books/store-log-open-barriers.lisp (lane
; log-recovery-2): the open's duplicate segment fence, and why one barrier is
; not enough.  The states are tests/acl2/store-log-kernel-tests.lisp's.
(in-package "ACL2")
(include-book "../../books/store-log-open-barriers")
(include-book "store-log-kernel-tests")
; The record codec seam's attachment: the log's txid reads the record through
; fn-record-decode-exact (books/store-log-txid.lisp).
(include-book "../../books/codec-attach")

(defun slob-step (bs ks)
  (declare (xargs :verify-guards nil))
  (mv-let (r bs1 ks1) (fn-lg-step bs ks '(:fence :segment :tail) :ok 0)
    (list r bs1 ks1)))

(defun slob-identityp (bs ks)
  (declare (xargs :verify-guards nil))
  (equal (slob-step bs ks) (list :ok bs ks)))

; fn-lgob-duplicate-segment-fence-is-identity, reachable witness: the
; recovered segment (P-LOG-RECOVER run: zeroed and fenced) with its kernel;
; every hypothesis holds and the second fence is the identity.
(assert-event
 (and (fn-bs-shapep (slk-bs0))
      (fn-lgk-relp (slk-bs0) (slk-ks0) 0 (slk-genesis) (slk-max))
      (not (consp (fn-lgk-inflight (slk-ks0))))
      (slob-identityp (slk-bs0) (slk-ks0))))

; Hypothesis removed (fn-bs-shapep): a store with a seventh field, related and
; idle; the fence rebuilds a six-field store, not the one given.
(assert-event
 (let ((bs (append (slk-bs0) '(extra))))
   (and (not (fn-bs-shapep bs))
        (fn-lgk-relp bs (slk-ks0) 0 (slk-genesis) (slk-max))
        (not (consp (fn-lgk-inflight (slk-ks0))))
        (not (slob-identityp bs (slk-ks0))))))

; Hypothesis removed (R): a store with a pending write of its segment the
; kernel does not hold (not related); the fence lands it.
(assert-event
 (let ((bs (slk-write (slk-bs0) 0 0 '(1 1 1 1))))
   (and (fn-bs-shapep bs)
        (not (fn-lgk-relp bs (slk-ks0) 0 (slk-genesis) (slk-max)))
        (not (consp (fn-lgk-inflight (slk-ks0))))
        (not (slob-identityp bs (slk-ks0))))))

; Hypothesis removed (nothing in flight): the appended batch, related with its
; kernel in flight; the fence lands the batch's write.
(assert-event
 (and (fn-bs-shapep (slk-appended-bs))
      (fn-lgk-relp (slk-appended-bs) (slk-appended-ks) 0 (slk-genesis) (slk-max))
      (consp (fn-lgk-inflight (slk-appended-ks)))
      (not (slob-identityp (slk-appended-bs) (slk-appended-ks)))))

; fn-lgob-recovered-segment-fence-is-identity, reachable witness: the crashed
; content of the kernel tests (two records, a torn unit, zeros), the recovery
; program run to log-recovered, then the second fence: the identity.
(assert-event
 (let* ((bs (slk-store (slk-content) nil))
        (ks (fn-lg-recovered-kernel bs 0 (slk-genesis) (slk-max) 1))
        (run (fn-lg-run bs ks (fn-lg-recover-program) nil 0))
        (final (car (last run))))
   (and (equal (len run) 4)
        (fn-lgk-relp (car final) (cdr final) 0 (slk-genesis) (slk-max))
        (slob-identityp (car final) (cdr final)))))

; fn-lgob-file-fence-keeps-entry-operations, witness: the rotated store's
; pending create survives the segment's fence.
(assert-event
 (let* ((s (fn-lgob-rotated-store))
        (op '(:set-entry :journal "000002.log" 2)))
   (and (member-equal op (fn-bs-pending s))
        (member-equal op (fn-bs-pending (fn-bs-fence-file s 2))))))
; Hypothesis removed (not a write): a pending write of the fenced inode is
; drained.
(assert-event
 (let* ((s (fn-lgob-write (fn-lgob-rotated-store) 2 '(5 5 5 5)))
        (op '(:write 2 0 (5 5 5 5))))
   (and (member-equal op (fn-bs-pending s))
        (not (member-equal op (fn-bs-pending (fn-bs-fence-file s 2)))))))
; Hypothesis removed (pending): an operation never issued is not pending after.
(assert-event
 (let ((op '(:set-entry :journal "000003.log" 3)))
   (and (not (member-equal op (fn-bs-pending (fn-lgob-rotated-store))))
        (not (member-equal op (fn-bs-pending (fn-bs-fence-file (fn-lgob-rotated-store) 2)))))))

; The counterexample's control: the same run with journal/ fenced leaves
; nothing pending, and the one-barrier run leaves exactly the create.
(assert-event
 (and (null (fn-bs-pending (fn-lgob-acked-batch t)))
      (equal (fn-bs-pending (fn-lgob-acked-batch nil))
             '((:set-entry :journal "000002.log" 2)))
      (equal (fn-bs-durable-entry (fn-bs-crash (fn-lgob-acked-batch nil) '(:apply))
                                  :journal "000002.log")
             2)))

; -----------------------------------------------------------------------------
; fn-lgob-recovered-segment-fence-is-identity (PRF-273), restated by lane
; audit-fixes (keystone-audit G4-7) with its one needed hypothesis: the
; segment's inode exists.  The weakened theorem is proved, so the six
; hypotheses it dropped (among them the owner's sole-pending-writer
; obligation) are gone rather than toothed; the two states below, each
; violating one dropped hypothesis, evaluate the conclusion true, as the
; weakened theorem says they must.

(defun slob-recovered-final (bs ino)
  (declare (xargs :verify-guards nil))
  (let ((ks (fn-lg-recovered-kernel bs ino (slk-genesis) (slk-max) 1)))
    (car (last (fn-lg-run bs ks (fn-lg-recover-program) nil ino)))))

(defun slob-recovered-conclusionp (bs ino)
  (declare (xargs :verify-guards nil))
  (let ((final (slob-recovered-final bs ino)))
    (mv-let (r bs1 ks1)
      (fn-lg-step (car final) (cdr final) '(:fence :segment :tail) :ok ino)
      (equal (list r bs1 ks1) (list :ok (car final) (cdr final))))))

; Reachable witness: the crashed content of the kernel tests, inode 0
; present; the recovery run reaches log-recovered (four states) and the
; second fence is the identity.
(assert-event
 (let ((bs (slk-store (slk-content) nil)))
   (and (assoc-equal 0 (fn-bs-inodes bs))
        (equal (len (fn-lg-run bs (fn-lg-recovered-kernel bs 0 (slk-genesis) (slk-max) 1)
                               (fn-lg-recover-program) nil 0))
               4)
        (slob-recovered-conclusionp bs 0))))

; Dropped hypotheses, the conclusion still holds (consistent with the
; weakened theorem; not teeth): a pending write of the segment (the
; program's own fence lands it), and a pending entry operation of another
; directory (the obligation's local witness fails; the file fence keeps it,
; both times).
(assert-event
 (let ((bs (slk-store (slk-content) (list (list :write 0 0 (list 1 1 1 1))))))
   (and (fn-bs-ops-for-ino (fn-bs-pending bs) 0)
        (slob-recovered-conclusionp bs 0))))
(assert-event
 (let ((bs (slk-store (slk-content) (list (list :set-entry :journal "x" 0)))))
   (and (fn-bs-ops-not-for-ino (fn-bs-pending bs) 0)
        (slob-recovered-conclusionp bs 0))))

; Hypothesis removed (the inode exists), CORRUPTED STATE: a store with a
; seventh field and no inode 7.  The program's first write is refused
; (:ebadf), the run stops there, and the fence rebuilds a six-field store.
(assert-event
 (let* ((bs (append (slk-store (slk-content) nil) '(extra)))
        (run (fn-lg-run bs (fn-lg-recovered-kernel bs 7 (slk-genesis) (slk-max) 1)
                        (fn-lg-recover-program) nil 7)))
   (and (not (assoc-equal 7 (fn-bs-inodes bs)))
        (equal (len run) 1)
        (not (slob-recovered-conclusionp bs 7)))))

; Hypothesis removed, CONSTRUCTED STATE (not known reachable): a well-shaped
; store with a pending write of inode 7, which it does not hold.  The run
; stops at the refused write, and the fence drains the orphan write.
(assert-event
 (let ((bs (slk-store (slk-content) (list (list :write 7 0 (list 1 1 1 1))))))
   (and (not (assoc-equal 7 (fn-bs-inodes bs)))
        (fn-bs-ops-for-ino (fn-bs-pending bs) 7)
        (not (slob-recovered-conclusionp bs 7)))))

; -----------------------------------------------------------------------------
; Three barriers, not five (lane open-barriers).  A store with a config file
; (inode 3, config.json in the root), segment 1 closed, and a death at
; rotate-created: 000002.log (inode 2) created, its name pending in journal/.

(defun slob-store (pending)
  (declare (xargs :verify-guards nil))
  (fn-bs-make 4 '((3 . (5 5 5 5)) (2 . (0 0 0 0)) (1 . (1 1 1 1)))
              '((:parent ("store" . :root))
                (:root ("config.json" . 3) ("journal" . :journal))
                (:journal ("000001.log" . 1)))
              pending 4))

(defconst *slob-rotating* '((:set-entry :journal "000002.log" 2)))

; P-LOG-RECOVER of segment 2: its tail zeroed, fenced.
(defun slob-recovered (pending)
  (declare (xargs :verify-guards nil))
  (fn-lgob-fsync-file (fn-lgob-write (slob-store pending) 2 '(0 0 0 0)) 2))

(defun slob-five (s seg cfg)
  (declare (xargs :verify-guards nil))
  (fn-lgob-cut-states s *fn-lgob-five-barrier-suffix* seg cfg))
(defun slob-three (s seg cfg)
  (declare (xargs :verify-guards nil))
  (fn-lgob-cut-states s (fn-lg-open-suffix) seg cfg))
(defun slob-samep (s seg cfg)
  (declare (xargs :verify-guards nil))
  (equal (slob-five s seg cfg) (list* s s (slob-three s seg cfg))))

; fn-lgob-three-barrier-open-is-the-five-at-every-cut, reachable witness:
; the recovered store after the death at rotate-created.  Every hypothesis
; holds; the three-barrier open has four cut states, the five six; the
; journal/ barrier is not the identity there (it lands the create).
(assert-event
 (let ((s (slob-recovered *slob-rotating*)))
   (and (fn-bs-shapep s) (true-listp (fn-bs-pending s))
        (fn-bs-fencedp s 2) (fn-bs-fencedp s 3)
        (equal (len (slob-three s 2 3)) 4)
        (equal (len (slob-five s 2 3)) 6)
        (not (equal (cadr (slob-three s 2 3)) s))
        (null (fn-bs-pending (car (last (slob-three s 2 3)))))
        (slob-samep s 2 3))))

; Hypothesis removed (the config file fenced): a pending write of config.json
; (not reachable at an open: fn-lgob-only-a-write-unfences-a-file and the
; publications' fsync); the config barrier lands it and the opens differ.
(assert-event
 (let ((s (slob-recovered (append *slob-rotating* '((:write 3 0 (6 6 6 6)))))))
   (and (fn-bs-shapep s) (true-listp (fn-bs-pending s)) (fn-bs-fencedp s 2)
        (not (fn-bs-fencedp s 3))
        (not (slob-samep s 2 3)))))

; Hypothesis removed (the segment fenced): a state before P-LOG-RECOVER's
; fence, a pending write of the segment; the segment's barrier lands it.
(assert-event
 (let ((s (fn-lgob-write (slob-store *slob-rotating*) 2 '(0 0 0 0))))
   (and (fn-bs-shapep s) (true-listp (fn-bs-pending s)) (fn-bs-fencedp s 3)
        (not (fn-bs-fencedp s 2))
        (not (slob-samep s 2 3)))))

; Hypothesis removed (fn-bs-shapep), CORRUPTED STATE: a seventh field; the
; first file fence rebuilds a six-field store.
(assert-event
 (let ((s (append (slob-recovered *slob-rotating*) '(extra))))
   (and (not (fn-bs-shapep s)) (true-listp (fn-bs-pending s))
        (fn-bs-fencedp s 2) (fn-bs-fencedp s 3)
        (not (slob-samep s 2 3)))))

; Hypothesis removed (a true-list pending list), CORRUPTED STATE: a pending
; list ending in an atom; a file fence rebuilds it as a true list.
(assert-event
 (let ((s (slob-store (cons '(:set-entry :journal "000002.log" 2) 'junk))))
   (and (fn-bs-shapep s) (not (true-listp (fn-bs-pending s)))
        (fn-bs-fencedp s 2) (fn-bs-fencedp s 3)
        (not (slob-samep s 2 3)))))

; fn-lgob-three-and-five-barrier-opens-have-the-same-cut-states: at the
; witness, the journal-fenced state is a cut state of both, and a state of
; neither is a cut state of neither.
(assert-event
 (let* ((s (slob-recovered *slob-rotating*))
        (j (cadr (slob-three s 2 3))))
   (and (member-equal j (slob-five s 2 3)) (member-equal j (slob-three s 2 3))
        (member-equal s (slob-five s 2 3)) (member-equal s (slob-three s 2 3))
        (not (member-equal (slob-store nil) (slob-five s 2 3)))
        (not (member-equal (slob-store nil) (slob-three s 2 3))))))

; fn-lgob-recovered-state-meets-the-segment-hypothesis and the composed
; keystone, reachable witness: the crashed kernel-test content (inode 0) with
; a config file (inode 5) and a pending create in journal/.
(defun slob-kstore (pending)
  (declare (xargs :verify-guards nil))
  (fn-bs-make (slk-unit) (list (cons 5 '(5 5 5 5)) (cons 0 (slk-content)))
              '((:root ("config.json" . 5) ("journal" . :journal)) (:journal))
              pending 6))
(defun slob-kfinal-at (bs ino)
  (declare (xargs :verify-guards nil))
  (car (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino (slk-genesis) (slk-max) 1)
                             (fn-lg-recover-program) nil ino)))))
(defun slob-kfinal (bs)
  (declare (xargs :verify-guards nil))
  (slob-kfinal-at bs 0))
(assert-event
 (let* ((bs (slob-kstore '((:set-entry :journal "000001.log" 0))))
        (final (slob-kfinal bs)))
   (and (assoc-equal 0 (fn-bs-inodes bs)) (fn-bs-fencedp bs 5)
        (fn-bs-shapep final) (fn-bs-fencedp final 0) (fn-bs-fencedp final 5)
        (slob-samep final 0 5))))
; Hypothesis removed (the config file fenced): a pending config write
; survives P-LOG-RECOVER and the two opens differ.
(assert-event
 (let* ((bs (slob-kstore '((:write 5 0 (6 6 6 6)))))
        (final (slob-kfinal bs)))
   (and (assoc-equal 0 (fn-bs-inodes bs)) (not (fn-bs-fencedp bs 5))
        (not (fn-bs-fencedp final 5))
        (not (slob-samep final 0 5)))))
; Hypothesis removed (the segment exists), CORRUPTED STATE: a seventh field
; and no inode 7; the write is refused, the run stops, the final state is not
; a byte store.
(assert-event
 (let* ((bs (append (slob-kstore nil) '(extra)))
        (final (slob-kfinal-at bs 7)))
   (and (not (assoc-equal 7 (fn-bs-inodes bs))) (fn-bs-fencedp bs 5)
        (not (fn-bs-shapep final)))))

; fn-lgob-only-a-write-unfences-a-file: witnesses of each syscall keeping
; inode 3 fenced, and its hypothesis-removal: a write of inode 3 unfences it.
(defmacro slob-after (call)
  `(mv-let (r s1) ,call (declare (ignore r)) s1))
(assert-event
 (let ((s (slob-store *slob-rotating*)))
   (and (fn-bs-fencedp s 3)
        (fn-bs-fencedp (slob-after (fn-bs-create s :journal "000003.log" :ok)) 3)
        (fn-bs-fencedp (slob-after (fn-bs-link s :journal "000001.log" :root "x" :ok)) 3)
        (fn-bs-fencedp (slob-after (fn-bs-rename s :journal "000001.log" :root "x" :ok)) 3)
        (fn-bs-fencedp (slob-after (fn-bs-unlink s :journal "000001.log" :ok)) 3)
        (fn-bs-fencedp (slob-after (fn-bs-mkdir s :root "d" :d :ok)) 3)
        (fn-bs-fencedp (slob-after (fn-bs-fsync-file s 2 :ok)) 3)
        (fn-bs-fencedp (slob-after (fn-bs-fsync-dir s :journal :ok)) 3)
        (fn-bs-fencedp (slob-after (fn-bs-write s 2 0 '(1 2 3 4) :ok)) 3)
        (not (fn-bs-fencedp (slob-after (fn-bs-write s 3 0 '(1 2 3 4) :ok)) 3)))))

; The two-barrier counterexamples' own run states (each theorem is ground;
; these check the runs are the ones the theorems name): the omitted barrier's
; directory holds exactly the operation the crash drops.
(assert-event
 (equal (fn-bs-pending (fn-lgob-open-then-batch (fn-lgob-rotated-store) 2 '(:root :parent)))
        '((:set-entry :journal "000002.log" 2))))
(assert-event
 (equal (fn-bs-pending (fn-lgob-open-then-drop '(:journal :parent)))
        '((:set-entry :root "checkpoint" 5) (:del-entry :staging ".checkpoint-stage"))))
(assert-event
 (equal (fn-bs-pending (fn-lgob-open-then-batch (fn-lgob-imported-store) 1 '(:journal :root)))
        '((:set-entry :parent "store" :root) (:del-entry :parent ".import-stage"))))
