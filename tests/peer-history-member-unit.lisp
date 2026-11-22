; Start at the retained verifier's :members boundary. This exercises member
; delivery and continuation; it does not acquire a snapshot or verify a seal.
(in-package "ACL2")
(include-book "../books/peer-history-member")

(defun fn2-phu-until (fuel dst dg fn2-event-read fn2-journal-lease fn2-journal-members
                      fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-journal-lease fn2-journal-members fn2-mk
                          fn2-b3 fn2-fields fn2-pool fn2-digests)
                 :verify-guards nil :measure (nfix fuel)))
 (b* (((when (zp fuel))
       (mv :fuel 0 0 fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code event n fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-peer-history-member 1 dst dg 0 9 0 1 fn2-event-read fn2-journal-lease fn2-journal-members
                                fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)))
  (if (eq code :more)
      (fn2-phu-until (- fuel 1) dst dg fn2-event-read fn2-journal-lease fn2-journal-members
                      fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
    (mv code event n fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests))))

(defun fn2-phu-run (fn2-event-read fn2-journal-lease fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-journal-lease fn2-journal-members fn2-mk
                          fn2-b3 fn2-fields fn2-pool fn2-digests) :verify-guards nil))
 (b* ((fn2-event-read (fn2-event-read-init 1 fn2-event-read))
      (fn2-journal-lease (fn2-journal-lease-init 1 fn2-journal-lease))
      (fn2-journal-members (fn2-journal-members-init 1 fn2-journal-members))
      (fn2-mk (fn2-mk-table-init 1 fn2-mk)) (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
      (fn2-digests (fn2-digests-init 137 fn2-digests)) (fn2-fields (fn2-fields-init 128 fn2-fields))
      (fn2-pool (fn2-pool-init '((2 . 256) (1 . 8)) 1 100 fn2-pool))
      ((mv sc src sg fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
      ((mv dc dst dg fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
      ((mv bc small bg fn2-pool) (fn2-pool-reserve 1 9 0 1 fn2-pool))
      ((mv hc & fn2-fields fn2-pool)
       (fn2-run-load-values *fn2-format-record-header* (list *record-kind-allocation* 1 1 0 1 1 1 1 0 0 0)
                            0 src sg 0 9 0 1 fn2-fields fn2-pool))
      ((mv he body fn2-pool) (fn2-format-record-header-encode 0 src sg 0 9 0 1 fn2-fields fn2-pool))
      ((mv ac & fn2-fields fn2-pool)
       (fn2-run-load-values *fn2-format-allocation* '(7 9 1 3 4) 0 src sg 0 9 0 1 fn2-fields fn2-pool))
      ((mv ae end fn2-pool) (fn2-format-allocation-encode 0 src sg body 9 0 1 fn2-fields fn2-pool))
      ((mv jc fn2-journal-members)
       (fn2-journal-members-begin 1 1 0 end src sg 9 0 1 fn2-journal-members))
      (fn2-journal-lease (fn2-journal-lease-put 0 (phase *fn2-journal-lease-phase-ready*) (token 1)
                                      (kind 9) (owner 0) (generation 1) (cut-commit 1) (cut-event 1)))
      (fn2-event-read (fn2-event-read-put 0 (phase *fn2-event-read-phase-members*)
                    (token 1) (owner-kind 9) (owner-slot 0) (owner-gen 1) (cut-commit 1) (cut-event 1)
                    (commit 1) (next-event 1) (first 1) (members 1) (slot src) (gen sg)
                    (checker 0) (field-base 0) (leaf-digest 136)))
      ((mv blocked event0 n0 fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-phu-until 20 small bg fn2-event-read fn2-journal-lease fn2-journal-members
                        fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests))
      (held (and (equal event0 0) (equal n0 0) (equal (fn2-mk-size 0 fn2-mk) 0)
                 (equal (fn2-journal-members-next-event 0 fn2-journal-members) 1)
                 (equal (fn2-journal-members-hash-phase 0 fn2-journal-members) 3)))
      ((mv sent event n fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-phu-until 2 dst dg fn2-event-read fn2-journal-lease fn2-journal-members
                       fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests))
      (same (and (equal n end) (< 8 n)
                 (equal (fn2-run-read-bytes n src sg 0 9 0 1 fn2-pool)
                        (fn2-run-read-bytes n dst dg 0 9 0 1 fn2-pool))))
      (digest (equal (fn2-digest-list (fn2-digest-slot 0 *fn2-mk-frontier*) fn2-digests)
                     (fn-b3-words 8 (fn-blake3 (cons 0 (fn2-run-read-bytes end src sg 0 9 0 1 fn2-pool))))))
      ((mv done de dn fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-phu-until 2 dst dg fn2-event-read fn2-journal-lease fn2-journal-members
                       fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)))
  (mv (list sc dc bc hc he ac ae jc blocked held sent event same digest done de dn
            (fn2-mk-size 0 fn2-mk) (fn2-event-read-next-event 0 fn2-event-read))
      fn2-event-read fn2-journal-lease fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)))

(defun fn2-phu-test ()
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-event-read fn2-journal-lease fn2-journal-members fn2-mk
                      fn2-b3 fn2-fields fn2-pool fn2-digests)
  (fn2-phu-run fn2-event-read fn2-journal-lease fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)))

(assert-event
 (equal (fn2-phu-test) '(:ok :ok :ok :ok :ok :ok :ok :ok :bounds t :member 1 t t :complete 0 0 1 2)))
