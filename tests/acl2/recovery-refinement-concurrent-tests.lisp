; Teeth for books/recovery-refinement-concurrent (lane recovery-refinement-2,
; 2026-10-01; PRF-1214): the checkpoint publication run from the ground
; two-record log at log-written (r3 in flight, its write pending), every
; one of its ten states, under explicit crash choices: the kernel's R FAILS
; at every state after the first step (another inode's operations are
; pending beside the segment's write) while the lifted relation holds, and
; the keystone's conclusions hold on every image; the reachable positive
; witness of the concurrent theorem's complete antecedent and conclusion at
; the staged-durable cut with the batch landed whole (the exact tear, so
; the trailer premise evaluates); the MUTATION (a recovery that drops the
; acknowledged r1 is no tree-sequence member and loses r1); hypothesis
; removal, exactly one: the lifted relation (a second write to the segment
; pending inside the publication: its landed image recovers r1 r2 r3 r4,
; no tree-sequence member, every other hypothesis kept).
;
; Crash images are fn-bs-crash under explicit choices with
; fn-bs-crash-choicesp asserted (fn-bs-crash-imagep is a defun-sk and is
; not executable).  The fixture is the one of
; tests/acl2/recovery-refinement-tests.lisp (rrt-), re-made here under its
; own prefix so this book includes no test book.
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/recovery-refinement-concurrent")
(include-book "../../books/frame-trailer")

(defun rrct-unit () (declare (xargs :guard t)) 4)
(defun rrct-max () (declare (xargs :guard t)) 4096)
(defun rrct-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun rrct-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))
(defun rrct-store (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (rrct-unit) (list (cons 0 content)) nil pending 1))
(defun rrct-sels (count sel)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp count) nil (cons sel (rrct-sels (1- count) sel))))
(defun rrct-units-of (octets)
  (declare (xargs :guard t :verify-guards nil))
  (floor (len octets) (rrct-unit)))
(defun rrct-content ()
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (rrct-r 1) (rrct-r 2)) (rrct-genesis) (rrct-unit))
          '(9 9 9 9 0 0 0 0 0 0 0 0)
          (fn-bs-zeros 512)))
(defun rrct-ks0 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-recover (rrct-content) (rrct-genesis) (rrct-unit) (rrct-max) 3))
(defun rrct-recover-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-run (rrct-store (rrct-content) nil) (rrct-ks0) (fn-lg-recover-program) nil 0))
(defun rrct-bs0 () (declare (xargs :guard t :verify-guards nil)) (car (car (last (rrct-recover-run)))))
(defun rrct-ks1 () (declare (xargs :guard t :verify-guards nil)) (fn-lgk-prepare (rrct-ks0) (rrct-r 3)))
(defun rrct-append-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-run (rrct-bs0) (rrct-ks1) (fn-lg-append-program) nil 0))
; The state at log-written: r3 in flight, its write pending.
(defun rrct-bs1 () (declare (xargs :guard t :verify-guards nil)) (car (car (last (rrct-append-run)))))
(defun rrct-ks () (declare (xargs :guard t :verify-guards nil)) (cdr (car (last (rrct-append-run)))))

; Choices that land every pending operation whole: a selector per unit of
; each write, :apply for each entry operation.
(defun rrct-land-all (pending)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom pending) nil
    (cons (if (equal (car (car pending)) :write)
              (rrct-sels (rrct-units-of (nth 3 (car pending))) :new)
            :apply)
          (rrct-land-all (cdr pending)))))

; The publication run from log-written: ten states.
(defun rrct-scp-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-run (rrct-bs1) (rrct-ks) (fn-bs-scp-program ".stage-1" '(1 2 3)) nil nil 0))

(assert-event
 (and (fn-lgk-relp (rrct-bs1) (rrct-ks) 0 (rrct-genesis) (rrct-max))
      (equal (fn-lgk-inflight (rrct-ks)) (list (rrct-r 3)))
      (equal (fn-lgk-acked (rrct-ks)) 2)
      (equal (len (fn-bs-pending (rrct-bs1))) 1)
      (fn-rrc-scp-inputp (rrct-bs1) ".stage-1" nil)
      (< 0 (fn-bs-next-ino (rrct-bs1)))
      (equal (len (rrct-scp-run)) 10)))

; -----------------------------------------------------------------------------
; The lift is needed and holds: at every state after the first step the
; kernel's R fails (the staging entry, the staged write, the rename are
; pending beside the segment's write) and the lifted relation holds.

(defun rrct-relations-p (i)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp i) t
    (let ((bs (car (nth (1- i) (rrct-scp-run)))))
      (and (fn-rrc-relp bs (rrct-ks) 0 (rrct-genesis) (rrct-max))
           (iff (fn-lgk-relp bs (rrct-ks) 0 (rrct-genesis) (rrct-max))
                (equal (fn-bs-pending bs) (fn-bs-pending (rrct-bs1))))
           (rrct-relations-p (1- i))))))
(assert-event
 (and (rrct-relations-p 10)
      (not (fn-lgk-relp (car (nth 5 (rrct-scp-run))) (rrct-ks) 0 (rrct-genesis) (rrct-max)))
      (fn-rrc-relp (car (nth 5 (rrct-scp-run))) (rrct-ks) 0 (rrct-genesis) (rrct-max))))

; -----------------------------------------------------------------------------
; The keystone's conclusions on every state under three choices: nothing
; lands, the segment's write alone lands whole, everything lands whole.

(defun rrct-recovered (bs choices)
  (declare (xargs :guard t :verify-guards nil))
  (fn-rr-recovered-records (fn-bs-crash bs choices) 0 (rrct-genesis) (rrct-unit) (rrct-max) 0))
(defun rrct-ok-p (bs choices)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs))
       (fn-rr-tree-sequence-memberp (rrct-recovered bs choices)
                                    (fn-lgk-committed (rrct-ks)) (fn-lgk-inflight (rrct-ks)))
       (member-equal (rrct-r 1) (rrct-recovered bs choices))
       (member-equal (rrct-r 2) (rrct-recovered bs choices))))
(defun rrct-all-ok-p (i)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp i) t
    (let ((bs (car (nth (1- i) (rrct-scp-run)))))
      (and (rrct-ok-p bs nil)
           (rrct-ok-p bs (list (car (rrct-land-all (fn-bs-pending bs)))))
           (rrct-ok-p bs (rrct-land-all (fn-bs-pending bs)))
           (rrct-all-ok-p (1- i))))))
(assert-event (rrct-all-ok-p 10))

; -----------------------------------------------------------------------------
; The reachable positive witness of
; fn-rrc-checkpoint-crash-point-refines-with-a-batch-in-flight, complete
; antecedent and conclusion, at the staged-durable cut (state 5) and the
; durable cut (state 9) with everything landed whole (the exact tear: the
; trailer premise evaluates through its exact arm and the exhausted batch),
; over the ground medium of the generic teeth's shape.

(defun rrct-capture (configs records) (declare (xargs :guard t) (ignore configs)) records)
(defun rrct-full-open (configs frontier records)
  (declare (xargs :guard t))
  (list :opened configs frontier records))
(defun rrct-open (ckpt configs frontier suffix)
  (declare (xargs :guard t :verify-guards nil))
  (rrct-full-open configs frontier (append ckpt suffix)))
(defun rrct-select (status s count k)
  (declare (xargs :guard t))
  (if (and (equal status :ok) (natp s) (natp count) (<= s count)
           (natp k) (<= (- count s) k))
      (list :checkpoint s)
    (list :full-replay)))
(defun rrct-composed-open (status s ckpt configs frontier records k)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car (rrct-select status s (len records) k)) :checkpoint)
      (rrct-open ckpt configs frontier (nthcdr s records))
    (rrct-full-open configs frontier records)))
(defun rrct-open-okp (st) (declare (xargs :guard t :verify-guards nil)) (equal (car st) :opened))
(defun rrct-holds (st r) (declare (xargs :guard t :verify-guards nil)) (member-equal r (nth 3 st)))

; The concurrent theorem over the ground medium: the literal theorem with
; the medium's six functions replaced.
(defthm rrct-concurrent-keystone
  (let ((recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (fn-rrc-scp-inputp bs stage old-ino)
                  (natp ino) (< ino (fn-bs-next-ino bs))
                  (member-equal p (fn-bs-run bs ks2 (fn-bs-scp-program stage octets)
                                             nil groups capacity))
                  (fn-bs-crash-imagep (car p) image)
                  (fn-lg-platform-tears-p
                   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
                  (natp s)
                  (<= s (len (fn-lgk-committed ks)))
                  (equal ckpt (rrct-capture configs (take s (fn-lgk-committed ks)))))
             (and (fn-rr-tree-sequence-memberp recovered (fn-lgk-committed ks)
                                               (fn-lgk-inflight ks))
                  (equal (rrct-composed-open status s ckpt configs frontier recovered k)
                         (rrct-full-open configs frontier recovered))
                  (implies (member-equal r (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
                           (and (member-equal r recovered)
                                (implies (rrct-open-okp
                                          (rrct-composed-open status s ckpt configs frontier
                                                              recovered k))
                                         (rrct-holds
                                          (rrct-composed-open status s ckpt configs frontier
                                                              recovered k)
                                          r)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:functional-instance
                  fn-rrc-checkpoint-crash-point-refines-with-a-batch-in-flight
                  (fn-rr-medium-capture rrct-capture)
                  (fn-rr-medium-open rrct-open)
                  (fn-rr-medium-full-open rrct-full-open)
                  (fn-rr-medium-select rrct-select)
                  (fn-rr-medium-open-okp rrct-open-okp)
                  (fn-rr-medium-holds rrct-holds)
                  (fn-rr-open rrct-composed-open)))
           :in-theory (enable rrct-composed-open rrct-select rrct-open rrct-capture
                              rrct-full-open rrct-open-okp rrct-holds))))

(defun rrct-full-witness-p (i s r)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((p (nth i (rrct-scp-run)))
         (bs (car p))
         (choices (rrct-land-all (fn-bs-pending bs)))
         (image (fn-bs-crash bs choices))
         (ks (rrct-ks))
         (recovered (fn-rr-recovered-records image 0 (rrct-genesis) (fn-bs-unit (rrct-bs1)) (rrct-max) 0))
         (ckpt (rrct-capture nil (take s (fn-lgk-committed ks))))
         (opened (rrct-composed-open :ok s ckpt nil 9 recovered 4)))
    (and ; the antecedent
         (fn-lgk-relp (rrct-bs1) ks 0 (rrct-genesis) (rrct-max))
         (fn-rrc-scp-inputp (rrct-bs1) ".stage-1" nil)
         (< 0 (fn-bs-next-ino (rrct-bs1)))
         (member-equal p (rrct-scp-run))
         (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs))
         (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image 0))
                                 (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit (rrct-bs1)))
         (natp s) (<= s (len (fn-lgk-committed ks)))
         (member-equal r (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
         ; the conclusion
         (fn-rr-tree-sequence-memberp recovered (fn-lgk-committed ks) (fn-lgk-inflight ks))
         (equal recovered (list (rrct-r 1) (rrct-r 2) (rrct-r 3)))
         (equal opened (rrct-full-open nil 9 recovered))
         (member-equal r recovered)
         (rrct-open-okp opened)
         (rrct-holds opened r))))
(assert-event
 (and (rrct-full-witness-p 5 2 (rrct-r 2))
      (rrct-full-witness-p 5 1 (rrct-r 1))
      (rrct-full-witness-p 9 2 (rrct-r 1))
      ; at the durable cut the new image is published beside the landed batch
      (equal (fn-bs-durable-entry (fn-bs-crash (car (nth 9 (rrct-scp-run)))
                                               (rrct-land-all (fn-bs-pending (car (nth 9 (rrct-scp-run))))))
                                  :root "store-checkpoint.fnsc")
             (fn-bs-next-ino (rrct-bs1)))))

; -----------------------------------------------------------------------------
; MUTATION: a recovery that drops the acknowledged r1 (the recovered list
; without its first record) at the staged-durable cut: no tree-sequence
; member, and r1 is lost.

(defun rrct-mutant-recovered ()
  (declare (xargs :guard t :verify-guards nil))
  (let ((bs (car (nth 5 (rrct-scp-run)))))
    (cdr (rrct-recovered bs (rrct-land-all (fn-bs-pending bs))))))
(assert-event
 (and (equal (rrct-mutant-recovered) (list (rrct-r 2) (rrct-r 3)))
      (member-equal (rrct-r 1) (take (fn-lgk-acked (rrct-ks)) (fn-lgk-committed (rrct-ks))))))
(must-fail-checked
 (defthm rrct-dropping-an-acknowledged-record
   (fn-rr-tree-sequence-memberp (rrct-mutant-recovered)
                                (fn-lgk-committed (rrct-ks)) (fn-lgk-inflight (rrct-ks)))))
(must-fail-checked
 (defthm rrct-dropped-record-is-present
   (member-equal (rrct-r 1) (rrct-mutant-recovered))))

; -----------------------------------------------------------------------------
; Hypothesis removal, exactly one: the lifted relation.  The staged-durable
; state with a SECOND write to the segment pending (the log of r4 chained
; after r3's entry, placed after it): fn-rrc-relp fails (two writes to the
; segment), the choices are admissible, the trailer premise evaluates true
; on the image where everything lands (r3's entry is exact and the batch is
; then exhausted), S and the binding are the witness's own; the recovered
; r1 r2 r3 r4 is no tree-sequence member.

(defun rrct-second-write ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((w (car (fn-bs-pending (rrct-bs1))))
         (prev4 (fn-lg-scan-last (nth 3 w) (fn-lgk-last (rrct-ks)) (rrct-unit) (rrct-max))))
    (list :write 0 (+ (nth 2 w) (len (nth 3 w)))
          (fn-lg-log (list (rrct-r 4)) prev4 (rrct-unit)))))
(defun rrct-unrelated ()
  (declare (xargs :guard t :verify-guards nil))
  (let ((bs (car (nth 5 (rrct-scp-run)))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                (append (fn-bs-pending bs) (list (rrct-second-write)))
                (fn-bs-next-ino bs))))
(defun rrct-unrelated-image ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-crash (rrct-unrelated) (rrct-land-all (fn-bs-pending (rrct-unrelated)))))
(defun rrct-unrelated-recovered ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-rr-recovered-records (rrct-unrelated-image) 0 (rrct-genesis) (rrct-unit) (rrct-max) 0))
(assert-event
 (let ((ks (rrct-ks)))
   (and ; the omitted hypothesis fails
        (not (fn-rrc-relp (rrct-unrelated) ks 0 (rrct-genesis) (rrct-max)))
        (equal (len (fn-bs-ops-for-ino (fn-bs-pending (rrct-unrelated)) 0)) 2)
        ; every retained hypothesis holds
        (fn-bs-crash-choicesp (rrct-land-all (fn-bs-pending (rrct-unrelated)))
                              (fn-bs-pending (rrct-unrelated)) (rrct-unit))
        (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks)
                                        (fn-bs-durable-content (rrct-unrelated-image) 0))
                                (fn-lgk-inflight ks) (fn-lgk-last ks) (rrct-unit))
        (<= 2 (len (fn-lgk-committed ks)))
        ; the conclusion fails
        (equal (rrct-unrelated-recovered) (list (rrct-r 1) (rrct-r 2) (rrct-r 3) (rrct-r 4)))
        (not (fn-rr-tree-sequence-memberp (rrct-unrelated-recovered)
                                          (fn-lgk-committed ks) (fn-lgk-inflight ks))))))
(must-fail-checked
 (defthm rrct-without-the-lifted-relation
   (fn-rr-tree-sequence-memberp (rrct-unrelated-recovered)
                                (fn-lgk-committed (rrct-ks)) (fn-lgk-inflight (rrct-ks)))))
