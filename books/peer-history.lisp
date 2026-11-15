; Internal retained history traversal. No protocol or authorization admission
; is added here. The owner holds the actual C snapshot until release; its
; installed source edges and physical read pins are the lifetime mechanism.
(in-package "ACL2")
(include-book "event-frontier-source")
(include-book "pool-ranges")
(fn2-book-layer :c)

; Unlike checkpoint open, this consumer obtains the physical cursor namespace
; from the immutable boot-origin child. Historical journal namespaces remain
; independently authenticated by the shared seal verifier.
(defun fn2-peer-history-open (token ordinal rslot rgen dslot dgen off scratch sgen okind oslot ogen
                             fn2-event-read fn2-csnapshot fn2-commit-root fn2-extents fn2-alloc-edges
                             fn2-fc fn2-digests fn2-mk fn2-fields fn2-origin fn2-pool)
 (declare (xargs :stobjs (fn2-event-read fn2-csnapshot fn2-commit-root fn2-extents fn2-alloc-edges
                          fn2-fc fn2-digests fn2-mk fn2-fields fn2-origin fn2-pool)
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-commit-root-wfp fn2-commit-root) (fn2-extents-wfp fn2-extents)
              (fn2-alloc-edges-wfp fn2-alloc-edges) (fn2-fc-wfp fn2-fc)
              (fn2-digests-wfp fn2-digests) (fn2-mk-wfp fn2-mk)
              (fn2-fields-wfp fn2-fields) (fn2-origin-wfp fn2-origin) (fn2-pool-wfp fn2-pool))))
 (fn2-event-read-open-core (fn2-origin-history fn2-origin) (fn2-origin-history-incarnation fn2-origin)
  token ordinal rslot rgen dslot dgen off scratch sgen okind oslot ogen
  fn2-event-read fn2-csnapshot fn2-commit-root fn2-extents fn2-alloc-edges
  fn2-fc fn2-digests fn2-mk fn2-fields fn2-pool))
(fn2-event-read-preserves fn2-peer-history-open
 (token ordinal rslot rgen dslot dgen off scratch sgen okind oslot ogen
  fn2-event-read fn2-csnapshot fn2-commit-root fn2-extents fn2-alloc-edges
  fn2-fc fn2-digests fn2-mk fn2-fields fn2-origin fn2-pool)
 :carriers ((fn2-event-read 1 :prefix "-READER") (fn2-mk 2 :prefix "-TREE")
            (fn2-fields 3 :prefix "-FIELDS") (fn2-pool 4 :prefix "-POOL"))
 :hyps ((fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read)
        (fn2-csnapshotp fn2-csnapshot) (fn2-csnapshot-wfp fn2-csnapshot)
        (fn2-commit-rootp fn2-commit-root) (fn2-commit-root-wfp fn2-commit-root)
        (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
        (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges)
        (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc)
        (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
        (fn2-mkp fn2-mk) (fn2-mk-wfp fn2-mk)
        (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
        (fn2-originp fn2-origin) (fn2-origin-wfp fn2-origin)
        (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)))

; Advance exactly the existing verifier/member-hasher step. A :member result
; owns a copied canonical semantic member at DOFF, with its original journal
; event number. It is returned only when that SAME step appended the member
; to the actual Merkle frontier. The original bytes include original evidence
; and receipt identities; this traversal does not synthesize local identities.
;
; Copy before append: a full or lost destination never advances continuation.
; The copy is scratch until :member; any verifier failure exposes zero length.
(defun fn2-peer-history-member (token dslot dgen doff okind oslot ogen
                               fn2-event-read fn2-csnapshot fn2-journal-members fn2-mk
                               fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-csnapshot fn2-journal-members fn2-mk
                          fn2-b3 fn2-fields fn2-pool fn2-digests)
  :verify-guards nil
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-journal-members-wfp fn2-journal-members) (fn2-mk-wfp fn2-mk)
              (fn2-b3-wfp fn2-b3) (fn2-fields-wfp fn2-fields)
              (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (and (fn2-event-read-ownerp fn2-event-read fn2-csnapshot)
                     (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot)
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
       (fn2-event-read-member-step fn2-event-read fn2-csnapshot fn2-journal-members fn2-mk
        fn2-b3 fn2-fields fn2-pool fn2-digests))
      (emitted (and ready (eq code :more)
                    (equal (fn2-mk-size row fn2-mk) event)
                    (equal (fn2-journal-members-next-event 0 fn2-journal-members) (+ 1 event))
                    (equal (fn2-journal-members-phase 0 fn2-journal-members) *fn2-journal-members-phase-scanning*))))
  (mv (if emitted :member code) (if emitted event 0) (if emitted (- end start) 0)
      fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)))
(fn2-event-read-preserves fn2-peer-history-member
 (token dslot dgen doff okind oslot ogen fn2-event-read fn2-csnapshot fn2-journal-members fn2-mk
  fn2-b3 fn2-fields fn2-pool fn2-digests)
 :carriers ((fn2-event-read 3 :prefix "-READER") (fn2-journal-members 4 :prefix "-MEMBERS")
            (fn2-mk 5 :prefix "-TREE") (fn2-b3 6 :prefix "-HASHER")
            (fn2-fields 7 :prefix "-FIELDS") (fn2-pool 8 :prefix "-POOL") (fn2-digests 9 :prefix "-DIGESTS"))
 :hyps ((fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read)
        (fn2-csnapshotp fn2-csnapshot) (fn2-csnapshot-wfp fn2-csnapshot)
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

; Materialized beside the existing C core operations. These functions are
; internal consumers of C's held snapshot; no protocol handler calls them.
(defmacro fn2-peer-history-core-events ()
 '(progn
   (fn2-csnapshot-op fn2-peer-history-open-core
    (token ordinal rslot rgen dslot dgen off scratch sgen okind oslot ogen) 1
    (stobj-let
     ((fn2-event-read (fn2-core-event-read fn2-core)) (fn2-csnapshot (fn2-core-csnapshot fn2-core))
      (fn2-commit-root (fn2-core-commit-root fn2-core)) (fn2-extents (fn2-core-extents fn2-core))
      (fn2-alloc-edges (fn2-core-alloc-edges fn2-core)) (fn2-fc (fn2-core-fc fn2-core))
      (fn2-digests (fn2-core-digests fn2-core)) (fn2-mk (fn2-core-mk fn2-core))
      (fn2-fields (fn2-core-fields fn2-core)) (fn2-origin (fn2-core-origin fn2-core))
      (fn2-pool (fn2-core-pool fn2-core)))
     (code fn2-event-read fn2-mk fn2-fields fn2-pool)
     (fn2-peer-history-open token ordinal rslot rgen dslot dgen off scratch sgen okind oslot ogen
      fn2-event-read fn2-csnapshot fn2-commit-root fn2-extents fn2-alloc-edges
      fn2-fc fn2-digests fn2-mk fn2-fields fn2-origin fn2-pool)
     (mv code fn2-core)))
   (fn2-csnapshot-op fn2-peer-history-member-core (token dslot dgen doff okind oslot ogen) 3
    (stobj-let
     ((fn2-event-read (fn2-core-event-read fn2-core)) (fn2-csnapshot (fn2-core-csnapshot fn2-core))
      (fn2-journal-members (fn2-core-journal-members fn2-core)) (fn2-mk (fn2-core-mk fn2-core))
      (fn2-b3 (fn2-core-b3 fn2-core)) (fn2-fields (fn2-core-fields fn2-core))
      (fn2-pool (fn2-core-pool fn2-core)) (fn2-digests (fn2-core-digests fn2-core)))
     (code event length fn2-event-read fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
     (fn2-peer-history-member token dslot dgen doff okind oslot ogen
      fn2-event-read fn2-csnapshot fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)
     (mv code event length fn2-core)))
   (fn2-csnapshot-op fn2-peer-history-close (token okind oslot ogen) 1
    (b* ((ready
          (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core))
                      (fn2-csnapshot (fn2-core-csnapshot fn2-core))) (ready)
           (and (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot)
                (< 0 (fn2-event-read-rows fn2-event-read))
                (equal (fn2-event-read-pending 0 fn2-event-read) 0)
                (or (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-idle*)
                    (and (fn2-event-read-ownerp fn2-event-read fn2-csnapshot)
                         (equal token (fn2-event-read-token 0 fn2-event-read))))) ready))
         ((unless ready) (mv :busy fn2-core))
         ((mv code fn2-core) (fn2-csnapshot-release token okind oslot ogen fn2-core))
         ((unless (eq code :ok)) (mv code fn2-core)))
     (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core))) (fn2-event-read)
      (fn2-event-read-put 0 (phase *fn2-event-read-phase-idle*) (token 0))
      (mv :ok fn2-core))))))
