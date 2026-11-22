; Compose the served journal member ranges with the existing Merkle engine.
; No model record or caller-supplied leaf digest enters the retained frontier.
(in-package "ACL2")
(include-book "journal-members")
(include-book "merkle")
(fn2-book-layer :c)
(local (in-theory (disable fn2-journal-membersp fn2-journal-members-wfp fn2-journal-members-rows
                           fn2-journal-members-phase fn2-journal-members-event fn2-journal-members-next-event
                           fn2-journal-members-start fn2-journal-members-leaf-end fn2-journal-members-hash-phase
                           fn2-mkp fn2-mk-wfp fn2-mk-size fn2-mk-rows fn2-b3p fn2-b3-wfp
                           fn2-digestsp fn2-digests-wfp fn2-digests-rows fn2-poolp fn2-pool-wfp)))

; The producer owns ROW's hasher/frontier stripe and LEAF's result row until
; this member completes. It retains the scanner's exact immutable pool range
; across :more. One call starts, hashes <=4096 bytes, finalizes, or appends
; with the existing <=60-node binary carry; no journal/member may be skipped.
(defun fn2-event-member-hash-step (row leaf fn2-journal-members fn2-mk fn2-b3 fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-journal-members fn2-mk fn2-b3 fn2-digests fn2-pool)
                 :guard (and (fn2-journal-members-wfp fn2-journal-members) (fn2-mk-wfp fn2-mk)
                             (fn2-b3-wfp fn2-b3) (fn2-digests-wfp fn2-digests) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (mbt (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)))
                    (< 0 (fn2-journal-members-rows fn2-journal-members))
                    (= (fn2-journal-members-phase 0 fn2-journal-members) *fn2-journal-members-phase-leaf*)
                    (fn2-mk-ready row fn2-mk fn2-digests) (fn2-b3-ready row fn2-b3 fn2-digests)
                    (fn2-digest-rowp leaf fn2-digests)
                    (<= (* *fn2-digest-stride* (fn2-mk-rows fn2-mk)) leaf)
                    (posp (fn2-journal-members-event 0 fn2-journal-members))
                    (unsigned-byte-p 60 (+ 1 (fn2-journal-members-event 0 fn2-journal-members)))
                    (= (fn2-journal-members-event 0 fn2-journal-members) (fn2-journal-members-next-event 0 fn2-journal-members))
                    (= (+ 1 (fn2-mk-size row fn2-mk)) (fn2-journal-members-event 0 fn2-journal-members))
                    (< (fn2-journal-members-start 0 fn2-journal-members) (fn2-journal-members-leaf-end 0 fn2-journal-members))
                    (<= (fn2-journal-members-leaf-end 0 fn2-journal-members) 4096)))
       (mv :state fn2-journal-members fn2-mk fn2-b3 fn2-digests))
      (phase (fn2-journal-members-hash-phase 0 fn2-journal-members)))
  (cond
   ((= phase 0)
    (mv-let (fn2-digests fn2-b3) (fn2-mk-leaf-start row fn2-digests fn2-b3)
     (let ((fn2-journal-members (fn2-journal-members-set-hash-phase 0 1 fn2-journal-members)))
      (mv :more fn2-journal-members fn2-mk fn2-b3 fn2-digests))))
   ((= phase 1)
    (mv-let (code fn2-digests fn2-b3)
     (fn2-mk-leaf (fn2-journal-members-slot 0 fn2-journal-members) (fn2-journal-members-gen 0 fn2-journal-members)
       (fn2-journal-members-start 0 fn2-journal-members)
       (- (fn2-journal-members-leaf-end 0 fn2-journal-members) (fn2-journal-members-start 0 fn2-journal-members))
       (fn2-journal-members-owner-kind 0 fn2-journal-members)
       (fn2-journal-members-owner-slot 0 fn2-journal-members) (fn2-journal-members-owner-gen 0 fn2-journal-members)
       row fn2-digests fn2-b3 fn2-pool)
     (let ((fn2-journal-members (if (eq code :ok)
                                  (fn2-journal-members-set-hash-phase 0 2 fn2-journal-members) fn2-journal-members)))
      (mv (if (eq code :ok) :more code) fn2-journal-members fn2-mk fn2-b3 fn2-digests))))
   ((= phase 2)
    (let* ((fn2-digests (fn2-b3-finalize leaf row fn2-digests fn2-b3))
           (fn2-journal-members (fn2-journal-members-set-hash-phase 0 3 fn2-journal-members)))
     (mv :more fn2-journal-members fn2-mk fn2-b3 fn2-digests)))
   ((= phase 3)
    (mv-let (code fn2-digests fn2-mk) (fn2-mk-append row leaf fn2-digests fn2-mk)
     (if (not (eq code :ok)) (mv code fn2-journal-members fn2-mk fn2-b3 fn2-digests)
      (mv-let (consumed fn2-journal-members) (fn2-journal-members-consumed fn2-journal-members)
       (mv (if (eq consumed :ok) :appended :state) fn2-journal-members fn2-mk fn2-b3 fn2-digests)))))
   (t (mv :state fn2-journal-members fn2-mk fn2-b3 fn2-digests)))))
(fn2-journal-members-preserves fn2-event-member-hash-step
 (row leaf fn2-journal-members fn2-mk fn2-b3 fn2-digests fn2-pool)
 :carriers ((fn2-journal-members 1 :prefix "-MEMBERS") (fn2-mk 2 :prefix "-TREE")
            (fn2-b3 3 :prefix "-HASHER") (fn2-digests 4 :prefix "-DIGESTS")))
