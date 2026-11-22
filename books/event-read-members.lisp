; The retained journal verifier passes its records window and held snapshot
; to this stage. One step decodes a record or advances its member hash.
(in-package "ACL2")
(include-book "event-read-state")
(include-book "c-snapshot-state")
(include-book "event-frontier")
(fn2-book-layer :c)
(local (in-theory (disable fn2-event-readp fn2-event-read-wfp fn2-event-read-rows
                           fn2-event-read-phase fn2-event-read-first fn2-event-read-members
                           fn2-event-read-commit fn2-event-read-cut-commit fn2-event-read-cut-event
                           fn2-event-read-next-event fn2-event-read-leaf-digest fn2-event-read-checker
                           fn2-event-read-field-base fn2-journal-members-phase fn2-journal-members-next-event
                           fn2-journal-membersp fn2-journal-members-wfp fn2-journal-members-rows
                           fn2-csnapshotp fn2-csnapshot-wfp fn2-csnapshot-rows
                           fn2-mkp fn2-mk-wfp fn2-mk-size fn2-mk-rows fn2-b3p fn2-b3-wfp
                           fn2-fieldsp fn2-fields-wfp fn2-digestsp fn2-digests-wfp
                           fn2-poolp fn2-pool-wfp)))

(defun fn2-event-read-ownerp (fn2-event-read fn2-csnapshot)
 (declare (xargs :stobjs (fn2-event-read fn2-csnapshot)
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-csnapshot-wfp fn2-csnapshot))))
 (and (< 0 (fn2-event-read-rows fn2-event-read))
      (fn2-csnapshot-ownerp (fn2-event-read-token 0 fn2-event-read)
       (fn2-event-read-owner-kind 0 fn2-event-read) (fn2-event-read-owner-slot 0 fn2-event-read)
       (fn2-event-read-owner-gen 0 fn2-event-read) fn2-csnapshot)
      (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
      (equal (fn2-event-read-cut-commit 0 fn2-event-read) (fn2-csnapshot-cut-commit 0 fn2-csnapshot))
      (equal (fn2-event-read-cut-event 0 fn2-event-read) (fn2-csnapshot-cut-event 0 fn2-csnapshot))))

(local (in-theory (disable fn2-fields-rows fn2-b3-rows fn2-digests-rows
                           fn2-journal-members-event fn2-journal-members-off fn2-journal-members-end
                           fn2-journal-members-start fn2-journal-members-leaf-end fn2-journal-members-hash-phase
                           fn2-journal-members-end-event)))

(local (defthm fn2-journal-members-step-field-dimensions
 (implies (and (fn2-journal-membersp fn2-journal-members) (fn2-journal-members-wfp fn2-journal-members)
               (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (let ((new (fn2-journal-members-step base fn2-journal-members fn2-fields fn2-pool)))
   (and (equal (fn2-journal-members-rows (mv-nth 1 new)) (fn2-journal-members-rows fn2-journal-members))
        (equal (fn2-fields-rows (mv-nth 2 new)) (fn2-fields-rows fn2-fields)))))
 :hints (("Goal" :in-theory (enable fn2-journal-members-step)))))

(local (defthm fn2-event-member-hash-step-field-dimensions
 (implies (and (fn2-journal-membersp fn2-journal-members) (fn2-journal-members-wfp fn2-journal-members)
               (fn2-mkp fn2-mk) (fn2-mk-wfp fn2-mk)
               (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
               (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (let ((new (fn2-event-member-hash-step row leaf fn2-journal-members fn2-mk fn2-b3 fn2-digests fn2-pool)))
   (and (equal (fn2-journal-members-rows (mv-nth 1 new)) (fn2-journal-members-rows fn2-journal-members))
        (equal (fn2-mk-rows (mv-nth 2 new)) (fn2-mk-rows fn2-mk))
        (equal (fn2-b3-rows (mv-nth 3 new)) (fn2-b3-rows fn2-b3))
        (equal (fn2-digests-rows (mv-nth 4 new)) (fn2-digests-rows fn2-digests)))))
 :hints (("Goal" :in-theory (enable fn2-event-member-hash-step)))))

(local (in-theory (disable fn2-mk-ready fn2-digest-workspacep fn2-event-read-ownerp)))

(defun fn2-event-read-member-core (fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
  :verify-guards nil
  :guard (and (fn2-event-read-wfp fn2-event-read)
              (fn2-journal-members-wfp fn2-journal-members) (fn2-mk-wfp fn2-mk) (fn2-b3-wfp fn2-b3)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (and (mbt (and (fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read)
                              (fn2-journal-membersp fn2-journal-members) (fn2-journal-members-wfp fn2-journal-members)
                              (fn2-mkp fn2-mk) (fn2-mk-wfp fn2-mk) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
                              (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
                              (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                              (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)))
                     (< 0 (fn2-event-read-rows fn2-event-read))
                     (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-members*)
                     (< 0 (fn2-journal-members-rows fn2-journal-members))))
       (mv :state fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-digests))
      (row (fn2-event-read-checker 0 fn2-event-read))
      ; Leaf output is outside all workspaces. Its absolute row is derived
      ; from the format/recovery region, not a caller-selected digest input.
      (leaf (fn2-event-read-leaf-digest 0 fn2-event-read))
      (ready (equal (fn2-journal-members-phase 0 fn2-journal-members) *fn2-journal-members-phase-leaf*))
      ((mv code fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-digests)
       (if ready
           (mv-let (code fn2-journal-members fn2-mk fn2-b3 fn2-digests)
            (fn2-event-member-hash-step row leaf fn2-journal-members fn2-mk fn2-b3 fn2-digests fn2-pool)
            (mv code fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-digests))
         (mv-let (code fn2-journal-members fn2-fields)
          (fn2-journal-members-step (fn2-event-read-field-base 0 fn2-event-read) fn2-journal-members fn2-fields fn2-pool)
          (mv code fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-digests))))
      ((when (member-eq code '(:more :leaf :appended)))
       (mv :more fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-digests))
      (next (+ (fn2-event-read-first 0 fn2-event-read) (fn2-event-read-members 0 fn2-event-read)))
      (last (equal (fn2-event-read-commit 0 fn2-event-read) (fn2-event-read-cut-commit 0 fn2-event-read)))
      (good (and (not ready) (unsigned-byte-p 60 next) (eq code :done) (fn2-mk-ready row fn2-mk fn2-digests)
                 (equal (fn2-journal-members-next-event 0 fn2-journal-members) next)
                 (equal (fn2-mk-size row fn2-mk) (- next 1))
                 (or (not last) (equal (fn2-mk-size row fn2-mk) (fn2-event-read-cut-event 0 fn2-event-read)))))
      (fn2-event-read (if good
                          (fn2-event-read-put 0 (next-event next)
                            (phase (if last *fn2-event-read-phase-complete* *fn2-event-read-phase-next*)))
                        (fn2-event-read-set-phase 0 *fn2-event-read-phase-uncertain* fn2-event-read))))
  (mv (if good (if last :complete :next) :invalid) fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-digests)))

(fn2-event-read-preserves fn2-event-read-member-core
 (fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
 :hyps ((fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read) (fn2-journal-membersp fn2-journal-members) (fn2-journal-members-wfp fn2-journal-members) (fn2-mkp fn2-mk) (fn2-mk-wfp fn2-mk) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :specs (("-EVENT-READ-DOMAIN-TYPE" fn2-event-readp 1)
         ("-EVENT-READ-DOMAIN-WFP" fn2-event-read-wfp 1)
         ("-EVENT-READ-DOMAIN-ROWS" fn2-event-read-rows 1 :frame fn2-event-read)
         ("-JOURNAL-MEMBERS-DOMAIN-TYPE" fn2-journal-membersp 2)
         ("-JOURNAL-MEMBERS-DOMAIN-WFP" fn2-journal-members-wfp 2)
         ("-JOURNAL-MEMBERS-DOMAIN-ROWS" fn2-journal-members-rows 2 :frame fn2-journal-members)
         ("-MK-DOMAIN-TYPE" fn2-mkp 3)
         ("-MK-DOMAIN-WFP" fn2-mk-wfp 3)
         ("-MK-DOMAIN-ROWS" fn2-mk-rows 3 :frame fn2-mk)
         ("-B3-DOMAIN-TYPE" fn2-b3p 4)
         ("-B3-DOMAIN-WFP" fn2-b3-wfp 4)
         ("-B3-DOMAIN-ROWS" fn2-b3-rows 4 :frame fn2-b3)
         ("-FIELDS-DOMAIN-TYPE" fn2-fieldsp 5)
         ("-FIELDS-DOMAIN-WFP" fn2-fields-wfp 5)
         ("-FIELDS-DOMAIN-ROWS" fn2-fields-rows 5 :frame fn2-fields)
         ("-DIGESTS-DOMAIN-TYPE" fn2-digestsp 6)
         ("-DIGESTS-DOMAIN-WFP" fn2-digests-wfp 6)
         ("-DIGESTS-DOMAIN-ROWS" fn2-digests-rows 6 :frame fn2-digests)))

(verify-guards fn2-event-read-member-core
 :hints (("Goal" :in-theory (e/d (fn2-mk-ready)
  (fn2-event-member-hash-step fn2-journal-members-step fn2-mkp fn2-mk-wfp
   fn2-event-readp fn2-event-read-wfp fn2-journal-membersp fn2-journal-members-wfp)))))

(defun fn2-event-read-member-step (fn2-event-read fn2-csnapshot fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-csnapshot fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
  :verify-guards nil :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-journal-members-wfp fn2-journal-members)
   (fn2-mk-wfp fn2-mk) (fn2-b3-wfp fn2-b3) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (if (not (and (mbt (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                         (fn2-csnapshotp fn2-csnapshot) (fn2-csnapshot-wfp fn2-csnapshot)))
               (fn2-event-read-ownerp fn2-event-read fn2-csnapshot)))
     (mv :state fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-digests)
   (fn2-event-read-member-core fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)))

(fn2-event-read-preserves fn2-event-read-member-step
 (fn2-event-read fn2-csnapshot fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
 :carriers ((fn2-event-read 1 :prefix "-READER") (fn2-journal-members 2 :prefix "-MEMBERS")
            (fn2-mk 3 :prefix "-TREE") (fn2-b3 4 :prefix "-HASHER")
            (fn2-fields 5 :prefix "-FIELDS") (fn2-digests 6 :prefix "-DIGESTS")))

(defthm fn2-event-read-member-step-retains-reader-dimensions
 (let ((result (fn2-event-read-member-step fn2-event-read fn2-csnapshot fn2-journal-members
                                           fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)))
  (and (equal (fn2-event-read-rows (mv-nth 1 result)) (fn2-event-read-rows fn2-event-read))
       (equal (fn2-journal-members-rows (mv-nth 2 result)) (fn2-journal-members-rows fn2-journal-members))
       (equal (fn2-mk-rows (mv-nth 3 result)) (fn2-mk-rows fn2-mk))))
 :hints (("Goal" :in-theory (enable fn2-event-read-member-step))))

(verify-guards fn2-event-read-member-step
 :hints (("Goal" :in-theory (disable fn2-event-read-member-core fn2-event-read-ownerp))))
