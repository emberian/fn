; A peer history member is emitted from a held, verified journal window
; only when the same step appends it to the retained Merkle frontier.
(in-package "ACL2")
(include-book "event-read-members")
(include-book "pool-ranges")
(fn2-book-layer :c)
(local (in-theory (disable fn2-event-readp fn2-event-read-wfp fn2-event-read-rows
                           fn2-journal-membersp fn2-journal-members-wfp fn2-journal-members-rows
                           fn2-journal-members-phase fn2-journal-members-start fn2-journal-members-leaf-end
                           fn2-journal-members-event fn2-journal-members-next-event fn2-journal-members-hash-phase
                           fn2-event-read-checker fn2-journal-leasep fn2-journal-lease-wfp fn2-journal-lease-rows
                           fn2-mkp fn2-mk-wfp fn2-mk-rows fn2-mk-size fn2-poolp fn2-pool-wfp
                           fn2-b3p fn2-b3-wfp fn2-fieldsp fn2-fields-wfp fn2-digestsp fn2-digests-wfp
                           fn2-pool-copy-range fn2-event-read-ownerp fn2-event-read-member-step
                           fn2-journal-lease-ownerp fn2-pool-readable-code fn2-pool-workspace-code
                           fn2-event-read-token fn2-event-read-slot fn2-event-read-gen fn2-event-read-phase
                           fn2-journal-members-slot fn2-journal-members-gen fn2-journal-members-owner-kind
                           fn2-journal-members-owner-slot fn2-journal-members-owner-gen)))

(defun fn2-peer-history-member (token dslot dgen doff okind oslot ogen
                               fn2-event-read fn2-journal-lease fn2-journal-members fn2-mk
                               fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-journal-lease fn2-journal-members fn2-mk
                          fn2-b3 fn2-fields fn2-pool fn2-digests)
  :verify-guards nil
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-journal-lease-wfp fn2-journal-lease)
              (fn2-journal-members-wfp fn2-journal-members) (fn2-mk-wfp fn2-mk)
              (fn2-b3-wfp fn2-b3) (fn2-fields-wfp fn2-fields)
              (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (and (< 0 (fn2-event-read-rows fn2-event-read))
                     (fn2-event-read-ownerp fn2-event-read fn2-journal-lease)
                     (fn2-journal-lease-ownerp token okind oslot ogen fn2-journal-lease)
                     (equal (fn2-event-read-token 0 fn2-event-read) token)
                     (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-members*)
                     (< 0 (fn2-journal-members-rows fn2-journal-members))))
       (mv :snapshot 0 0 fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests))
      (ready (and (equal (fn2-journal-members-phase 0 fn2-journal-members) *fn2-journal-members-phase-leaf*)
                  (equal (fn2-journal-members-hash-phase 0 fn2-journal-members) 3)))
      (event (fn2-journal-members-event 0 fn2-journal-members))
      (start (fn2-journal-members-start 0 fn2-journal-members))
      (end (fn2-journal-members-leaf-end 0 fn2-journal-members))
      (row (fn2-event-read-checker 0 fn2-event-read))
      (source (fn2-journal-members-slot 0 fn2-journal-members))
      (source-gen (fn2-journal-members-gen 0 fn2-journal-members))
      ((unless (and (equal source (fn2-event-read-slot 0 fn2-event-read))
                     (equal source-gen (fn2-event-read-gen 0 fn2-event-read))
                     (equal okind (fn2-journal-members-owner-kind 0 fn2-journal-members))
                     (equal oslot (fn2-journal-members-owner-slot 0 fn2-journal-members))
                     (equal ogen (fn2-journal-members-owner-gen 0 fn2-journal-members))
                     (not (equal source dslot))
                     (eq (fn2-pool-readable-code source source-gen okind oslot ogen fn2-pool) :ok)
                     (eq (fn2-pool-workspace-code dslot dgen okind oslot ogen fn2-pool) :ok)
                     (< row (fn2-mk-rows fn2-mk))
                     (or (not ready)
                         (and (posp event) (< start end) (<= end 4096)
                              (equal (+ 1 (fn2-mk-size row fn2-mk)) event)))))
       (mv :source 0 0 fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv copied fn2-pool)
       (if ready (fn2-pool-copy-range source source-gen start dslot dgen doff (- end start)
                  okind oslot ogen fn2-pool) (mv :ok fn2-pool)))
      ((unless (eq copied :ok))
       (mv copied 0 0 fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-digests)
       (fn2-event-read-member-step fn2-event-read fn2-journal-lease fn2-journal-members fn2-mk
        fn2-b3 fn2-fields fn2-pool fn2-digests))
      (emitted (and ready (eq code :more)
                    (equal (fn2-mk-size row fn2-mk) event)
                    (equal (fn2-journal-members-next-event 0 fn2-journal-members) (+ 1 event))
                    (equal (fn2-journal-members-phase 0 fn2-journal-members) *fn2-journal-members-phase-scanning*))))
  (mv (if emitted :member code) (if emitted event 0) (if emitted (- end start) 0)
      fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)))

(fn2-event-read-preserves fn2-peer-history-member
 (token dslot dgen doff okind oslot ogen fn2-event-read fn2-journal-lease fn2-journal-members fn2-mk
  fn2-b3 fn2-fields fn2-pool fn2-digests)
 :carriers ((fn2-event-read 3 :prefix "-READER") (fn2-journal-members 4 :prefix "-MEMBERS")
            (fn2-mk 5 :prefix "-TREE") (fn2-b3 6 :prefix "-HASHER")
            (fn2-fields 7 :prefix "-FIELDS") (fn2-pool 8 :prefix "-POOL") (fn2-digests 9 :prefix "-DIGESTS"))
 :hyps ((fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read)
        (fn2-journal-leasep fn2-journal-lease) (fn2-journal-lease-wfp fn2-journal-lease)
        (fn2-journal-membersp fn2-journal-members) (fn2-journal-members-wfp fn2-journal-members)
        (fn2-mkp fn2-mk) (fn2-mk-wfp fn2-mk)
        (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
        (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
        (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
        (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)))

(verify-guards fn2-peer-history-member
 :hints (("Goal" :in-theory (disable fn2-event-read-member-step fn2-event-read-ownerp
  fn2-pool-copy-range fn2-event-readp fn2-event-read-wfp fn2-journal-membersp
  fn2-journal-members-wfp fn2-mkp fn2-mk-wfp fn2-poolp fn2-pool-wfp))))
