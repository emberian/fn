; Witnesses and teeth for the byte-level storage model (crash model v2, P1
; and P2).
;
; Order: the reachable witnesses (a torn record, a lost directory entry, a
; failed fsync, a dropped rename and a staging orphan), then the composed
; runs of the five programs against the real file kernel, then one concrete
; violating value per hypothesis of each keystone of
; books/byte-store-invariants.lisp.  Every witness is reached through the
; production syscalls from an initialized store; none is written down.

(in-package "ACL2")
(include-book "../../books/byte-store-invariants")
(include-book "../../books/byte-store-programs")
(include-book "../../books/codec-attach")

; A syscall returns (mv result state); ground forms bind the pair.
(defmacro bst-res (call) `(mv-let (r s) ,call (declare (ignore s)) r))
(defmacro bst-state (call) `(mv-let (r s) ,call (declare (ignore r)) s))

; -----------------------------------------------------------------------------
; Reachable witnesses.  Unit 4, so the 10-octet frame spans three units.

(defconst *bst-stage* ".stage-1")
(defconst *bst-name* "00000000000000000000.txn")
(defconst *bst-frame* *fn-bs-sample-frame*)
(defconst *bst-store* *fn-bs-initialized-store*)
(assert-event (fn-bs-statep *bst-store*))

; After create and write_all, before the file fence: the frame is pending.
(defconst *bst-written*
  (car (nth 3 *fn-bs-run-record*)))          ; after (:cut "record-written")
(assert-event (equal (fn-bs-pending *bst-written*)
                     (list (list :set-entry :staging *bst-stage* 2)
                           (list :write 2 0 *bst-frame*))))
(assert-event (not (fn-bs-fencedp *bst-written* 2)))
(assert-event (equal (fn-bs-durable-content *bst-written* 2) nil))
(assert-event (equal (fn-bs-content *bst-written* 2) *bst-frame*))   ; the view

; A torn record: the middle unit never landed, the last unit is garbage.
(defconst *bst-torn-choices* (list :apply (list :new :zero (cons :garble '(7 7 7 7)))))
(assert-event (fn-bs-crash-choicesp *bst-torn-choices* (fn-bs-pending *bst-written*) 4))
(defconst *bst-torn* (fn-bs-crash *bst-written* *bst-torn-choices*))
(assert-event (equal (fn-bs-durable-content *bst-torn* 2) '(10 11 12 13 0 0 0 0 7 7)))
(assert-event (fn-bs-statep *bst-torn*))
(assert-event (null (fn-bs-pending *bst-torn*)))
; Truncation to a unit boundary: the trailing selectors are missing.
(defconst *bst-truncated* (fn-bs-crash *bst-written* (list :apply (list :new))))
(assert-event (equal (fn-bs-durable-content *bst-truncated* 2) '(10 11 12 13)))
; Zero-length file after crash (the name landed, the data did not).
(defconst *bst-empty-file* (fn-bs-crash *bst-written* (list :apply nil)))
(assert-event (and (equal (fn-bs-durable-entry *bst-empty-file* :staging *bst-stage*) 2)
                   (equal (fn-bs-durable-content *bst-empty-file* 2) nil)))

; A lost directory entry: at record-linked the link is pending on
; :transactions; dropping it leaves the name absent, applying it leaves the
; exact inode, and nothing else is possible.
(defconst *bst-linked*
  (car (nth 8 *fn-bs-run-record*)))          ; after (:cut "record-linked")
(assert-event (equal (fn-bs-ops-for-dir (fn-bs-pending *bst-linked*) :transactions)
                     (list (list :set-entry :transactions *bst-name* 2))))
(assert-event (fn-bs-fencedp *bst-linked* 2))
(defconst *bst-link-lost*
  (fn-bs-crash *bst-linked* (list :apply :drop)))
(defconst *bst-link-kept*
  (fn-bs-crash *bst-linked* (list :apply :apply)))
(assert-event (null (fn-bs-durable-entry *bst-link-lost* :transactions *bst-name*)))
(assert-event (equal (fn-bs-durable-entry *bst-link-kept* :transactions *bst-name*) 2))
(assert-event (equal (fn-bs-durable-content *bst-link-kept* 2) *bst-frame*))
(assert-event (equal (fn-bs-entry-outcomes
                      (fn-bs-ops-for-name (fn-bs-pending *bst-linked*) :transactions *bst-name*)
                      (fn-bs-durable-entry *bst-linked* :transactions *bst-name*))
                     '(nil 2)))

; A failed fsync: EIO after landing only the first unit; the rest is
; discarded, and a retried fsync that returns :ok fences nothing.
(assert-event (equal (bst-res (fn-bs-fsync-file *bst-written* 2 (list :eio (list :new)))) :eio))
(defconst *bst-after-eio* (bst-state (fn-bs-fsync-file *bst-written* 2 (list :eio (list :new)))))
(assert-event (equal (fn-bs-durable-content *bst-after-eio* 2) '(10 11 12 13)))
(assert-event (fn-bs-fencedp *bst-after-eio* 2))                 ; nothing left to write
(assert-event (equal (fn-bs-pending *bst-after-eio*)
                     (list (list :set-entry :staging *bst-stage* 2))))
(defconst *bst-refenced* (bst-state (fn-bs-fsync-file *bst-after-eio* 2 :ok)))
(assert-event (equal (fn-bs-inodes *bst-refenced*) (fn-bs-inodes *bst-after-eio*)))
(assert-event (fn-bs-statep *bst-after-eio*))

; A dropped rename leaves the old frontier; a dropped source removal leaves
; a staging orphan.  At frontier-replaced both entry operations are pending.
(defconst *bst-replaced*
  (car (nth 9 *fn-bs-run-frontier*)))        ; after (:cut "frontier-replaced")
(assert-event (equal (fn-bs-ops-for-dir (fn-bs-pending *bst-replaced*) :root)
                     (list (list :set-entry :root *fn-bs-frontier-name* 2))))
(defconst *bst-rename-lost* (fn-bs-crash *bst-replaced* (list :apply :drop :apply)))
(defconst *bst-orphan* (fn-bs-crash *bst-replaced* (list :apply :apply :drop)))
(assert-event (equal (fn-bs-durable-entry *bst-rename-lost* :root *fn-bs-frontier-name*) 1))
(assert-event (equal (fn-bs-durable-content *bst-rename-lost* 1) *fn-bs-sample-frontier*))
(assert-event (equal (fn-bs-durable-entry *bst-orphan* :root *fn-bs-frontier-name*) 2))
(assert-event (equal (fn-bs-durable-entry *bst-orphan* :staging ".allocation-1") 2))

; The lose-everything image is the durable state.
(assert-event (equal (fn-bs-inodes (fn-bs-crash *bst-linked* nil)) (fn-bs-inodes *bst-linked*)))
(assert-event (equal (fn-bs-dirs (fn-bs-crash *bst-linked* nil)) (fn-bs-dirs *bst-linked*)))

; -----------------------------------------------------------------------------
; The composed runs, against the real file kernel.

(defconst *bst-groups* '("fn.letters" "fn.test"))
(defconst *bst-capacity* 10)
(defconst *bst-record*
  (fn-record-make 0 0 0 "<zero@example.invalid>" '(90)
                  '("fn.letters" "fn.test")
                  "archive-zero" "content-zero" "release-zero" 2))

(defconst *bst-run-frontier*
  (fn-bs-run *bst-store* (fn-sf-initial-state) *fn-bs-p-frontier* nil
             *bst-groups* *bst-capacity*))
(assert-event (equal (len *bst-run-frontier*) (len *fn-bs-p-frontier*)))
(defconst *bst-reserved* (cdr (car (last *bst-run-frontier*))))
(assert-event (and (fn-sf-statep *bst-reserved*)
                   (equal (fn-sf-phase *bst-reserved*) :reserved)
                   (equal (fn-sf-frontier *bst-reserved*) 1)))

(defconst *bst-staged*
  (fn-sf-prepare-record *bst-reserved* *bst-record* *bst-groups* *bst-capacity*))
(assert-event (equal (fn-sf-phase *bst-staged*) :record-staged))
(defconst *bst-run-record*
  (fn-bs-run (car (car (last *bst-run-frontier*))) *bst-staged*
             *fn-bs-p-record* nil *bst-groups* *bst-capacity*))
(assert-event (equal (len *bst-run-record*) (len *fn-bs-p-record*)))
(defconst *bst-completing* (cdr (car (last *bst-run-record*))))
(assert-event (and (fn-sf-statep *bst-completing*)
                   (equal (fn-sf-phase *bst-completing*) :completing)
                   (equal (len (fn-sf-records *bst-completing*)) 1)))
(defconst *bst-run-finish*
  (fn-bs-run (car (car (last *bst-run-record*))) *bst-completing*
             *fn-bs-p-finish* nil *bst-groups* *bst-capacity*))
(defconst *bst-acknowledged* (cdr (car (last *bst-run-finish*))))
(assert-event (and (equal (fn-sf-phase *bst-acknowledged*) :ready)
                   (equal (fn-sf-successes *bst-acknowledged*) '((0 . 0)))))

; Recovery from the crash image of the acknowledged state.
(defconst *bst-crashed-bs* (fn-bs-crash (car (car (last *bst-run-finish*))) nil))
(defconst *bst-crashed-ks* (fn-sf-crash *bst-acknowledged* :old :absent))
(assert-event (equal (fn-sf-phase *bst-crashed-ks*) :replaying))
(defconst *bst-run-recover*
  (fn-bs-run *bst-crashed-bs* *bst-crashed-ks* *fn-bs-p-recover* nil
             *bst-groups* *bst-capacity*))
(assert-event (equal (len *bst-run-recover*) (len *fn-bs-p-recover*)))
(assert-event (equal (fn-sf-phase (cdr (car (last *bst-run-recover*)))) :ready))
(assert-event (null (fn-bs-pending (car (car (last *bst-run-recover*))))))

; -----------------------------------------------------------------------------
; Teeth: one concrete violating value per hypothesis.

; fn-bs-crash-keeps-fenced-content.  Without fencedp: inode 2 at
; record-written is unfenced and its content changes (the torn record).
(assert-event (not (equal (fn-bs-durable-content *bst-torn* 2)
                          (fn-bs-durable-content *bst-written* 2))))
; Without crash-imagep: a forged image with the fenced config inode altered
; fails the conclusion; no choice list produces it (that is the theorem).
(defconst *bst-forged* (fn-bs-make 4 (list (cons 0 '(9))) (fn-bs-dirs *bst-store*) nil 2))
(assert-event (fn-bs-fencedp *bst-store* 0))
(assert-event (not (equal (fn-bs-durable-content *bst-forged* 0)
                          (fn-bs-durable-content *bst-store* 0))))

; fn-bs-crash-keeps-quiet-directory.  Without dir-quietp: :transactions at
; record-linked is not quiet and the applied link changes it.
(assert-event (not (fn-bs-dir-quietp *bst-linked* :transactions)))
(assert-event (not (equal (assoc-equal :transactions (fn-bs-dirs *bst-link-kept*))
                          (assoc-equal :transactions (fn-bs-dirs *bst-linked*)))))

; fn-bs-crash-entry-is-old-or-a-pending-target.  The dir-idp and namep
; hypotheses are the proof's (the -same alist lemmas need a non-NIL key);
; no ground store with a NIL directory id or name violates the conclusion,
; because assoc-equal on an atom-keyed alist yields NIL, which is also the
; durable value.  Dropping them is an open simplification, not a tooth.
(assert-event (member-equal (fn-bs-durable-entry *bst-link-lost* :transactions *bst-name*)
                            '(nil 2)))
(assert-event (member-equal (fn-bs-durable-entry *bst-link-kept* :transactions *bst-name*)
                            '(nil 2)))

; fn-bs-refence-after-error-fences-nothing has no hypothesis: with :ok the
; first fence drains and the second finds nothing; with an error the first
; discards and the second finds nothing.  Both cases, on the witness.
(assert-event (equal (fn-bs-inodes (bst-state (fn-bs-fsync-file
                                              (bst-state (fn-bs-fsync-file *bst-written* 2 :ok))
                                              2 :ok)))
                     (fn-bs-inodes (bst-state (fn-bs-fsync-file *bst-written* 2 :ok)))))
; ... and the content the failed fence discarded never returns.
(assert-event (not (equal (fn-bs-durable-content *bst-refenced* 2) *bst-frame*)))

; K0 hypotheses.  Each violating value yields a non-state.
; fn-bs-crash-preserves-statep: choices outside fn-bs-crash-choicesp
; (a garble that is not octets) break the inode table.
(defconst *bst-bad-choices* (list :apply (list (cons :garble '(999)))))
(assert-event (not (fn-bs-crash-choicesp *bst-bad-choices* (fn-bs-pending *bst-written*) 4)))
(assert-event (not (fn-bs-statep (fn-bs-crash *bst-written* *bst-bad-choices*))))
; fn-bs-create-preserves-statep: a non-keyword directory, a non-string name.
(assert-event (not (fn-bs-statep (bst-state (fn-bs-create *bst-store* "staging" "x" :ok)))))
(assert-event (not (fn-bs-statep (bst-state (fn-bs-create *bst-store* :staging 5 :ok)))))
; fn-bs-write-preserves-statep: a negative offset, non-octet data.
(assert-event (not (fn-bs-statep (bst-state (fn-bs-write *bst-store* 0 -1 '(1) :ok)))))
(assert-event (not (fn-bs-statep (bst-state (fn-bs-write *bst-store* 0 0 '(300) :ok)))))
; ... and a bad descriptor is refused rather than invented.
(assert-event (equal (bst-res (fn-bs-write *bst-store* 7 0 '(1) :ok)) :ebadf))
; fn-bs-fsync-file-preserves-statep: a failure outcome whose choices are
; not admissible.
(assert-event (not (fn-bs-statep
                    (bst-state (fn-bs-fsync-file *bst-written* 2
                                                (list :eio (list (cons :garble '(999)))))))))
; fn-bs-fsync-dir-preserves-statep: the same on a directory (an entry choice
; is :apply or :drop; a selector list is not one, but a garbled :write
; smuggled in through the choice of a set-entry is ignored, so the tooth is
; on the file side).  Statep is preserved for every entry choice: shown.
(assert-event (fn-bs-statep (bst-state (fn-bs-fsync-dir *bst-linked* :transactions
                                                       (list :eio (list :drop))))))
; fn-bs-link-preserves-statep, fn-bs-rename-preserves-statep,
; fn-bs-unlink-preserves-statep, fn-bs-mkdir-preserves-statep.
(assert-event (not (fn-bs-statep
                    (bst-state (fn-bs-link *bst-written* :staging *bst-stage* "txn" "t" :ok)))))
(assert-event (not (fn-bs-statep
                    (bst-state (fn-bs-rename *bst-written* :staging *bst-stage* :root 5 :ok)))))
; fn-bs-unlink-preserves-statep and the source path of fn-bs-rename-
; preserves-statep have no dir-idp/namep hypotheses: the lookup that guards
; the syscall only succeeds on a typed path of a state, so a mistyped path
; is :enoent and the state is unchanged.  Shown, not assumed.
(assert-event (equal (bst-res (fn-bs-unlink *bst-written* "staging" *bst-stage* :ok)) :enoent))
(assert-event (fn-bs-statep (bst-state (fn-bs-unlink *bst-written* :staging 5 :ok))))
(assert-event (not (fn-bs-statep
                    (bst-state (fn-bs-mkdir *bst-store* :root "sub" "notakeyword" :ok)))))
; The fn-bs-statep hypothesis itself: a non-state in, a non-state out.
(assert-event (with-guard-checking :none
               (not (fn-bs-statep (bst-state (fn-bs-create nil :staging "x" :ok))))))

; Fence lemmas have no hypotheses; the witness shows the content: two
; inodes with pending writes, one fence, the other write remains.
(defconst *bst-two-writes*
  (bst-state (fn-bs-write (bst-state (fn-bs-write *bst-store* 0 0 '(5) :ok)) 1 0 '(6) :ok)))
(defconst *bst-one-fenced* (fn-bs-fence-file *bst-two-writes* 0))
(assert-event (and (fn-bs-fencedp *bst-one-fenced* 0)
                   (not (fn-bs-fencedp *bst-one-fenced* 1))
                   (equal (fn-bs-durable-content *bst-one-fenced* 0) '(5 2 3))
                   (equal (fn-bs-durable-content *bst-one-fenced* 1) '(0))))
