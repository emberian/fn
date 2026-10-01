; One borrowed retained snapshot cell per semantic scheduling step.
; Typed snapshot correspondence is carried from actual parse/replay; the
; logical recognizer below is never executed by the served cursor/guard.
; This does not authorize the cursor's fixed metadata/scalar allocation.
(in-package "ACL2")
(include-book "replay")

(defun fn-rsc-at (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (if (consp x) (car x) nil)
  (fn-rsc-at (1- n) (if (consp x) (cdr x) nil))))
(defun fn-rsc-widthp (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (null x)
  (and (consp x) (fn-rsc-widthp (1- n) (cdr x)))))
(defun fn-rsc-typed-snapshotsp (xs)
 (declare (xargs :guard t))
 (if (consp xs)
  (and (fn-stxk-p (car xs)) (fn-rsc-typed-snapshotsp (cdr xs)))
  (null xs)))

; Fixed five cells: phase,generation,borrowed remaining tail,result,source.
; SOURCE is the outer captured immutable owner/event association. The actual
; pending wrapper checks it against the current charged operation each step.
(defun fn-rsc-begin (generation snapshots source)
 (declare (xargs :guard t))
 (list :seek generation snapshots nil source))
(defun fn-rsc-step (cursor)
 (declare (xargs :guard t))
 (if (not (fn-rsc-widthp 5 cursor)) (mv :refused cursor)
  (if (not (eq (fn-rsc-at 0 cursor) :seek))
   (mv (if (member-eq (fn-rsc-at 0 cursor) '(:found :done)) :done :refused) cursor)
   (let ((xs (fn-rsc-at 2 cursor)))
    (if (not (consp xs))
     (mv :done (list :done (fn-rsc-at 1 cursor) nil nil (fn-rsc-at 4 cursor)))
     (if (equal (fn-rsc-at 1 cursor) (fn-stxk-keyring-generation (car xs)))
      (mv :done (list :found (fn-rsc-at 1 cursor) xs (car xs) (fn-rsc-at 4 cursor)))
      (mv :working (list :seek (fn-rsc-at 1 cursor) (cdr xs) nil
                         (fn-rsc-at 4 cursor)))))))))

; Proof abstraction only, never called by the host's step or completion.
(defun fn-rsc-abstract (cursor)
 (declare (xargs :guard t))
 (if (eq (fn-rsc-at 0 cursor) :seek)
  (fn-stxk-find (fn-rsc-at 1 cursor) (fn-rsc-at 2 cursor))
  (fn-rsc-at 3 cursor)))
(defun fn-rsc-invariantp (cursor)
 (declare (xargs :guard t))
 (and (fn-rsc-widthp 5 cursor)
      (member-eq (fn-rsc-at 0 cursor) '(:seek :found :done))
      (fn-rsc-typed-snapshotsp (fn-rsc-at 2 cursor))))

(local (defthm fn-rsc-typed-head
 (implies (and (fn-rsc-typed-snapshotsp xs) (consp xs))
          (fn-stxk-p (car xs)))
 :hints (("Goal" :expand ((fn-rsc-typed-snapshotsp xs))
          :in-theory (disable fn-stxk-p fn-rsc-typed-snapshotsp)))))
(local (defthm fn-rsc-typed-tail
 (implies (and (fn-rsc-typed-snapshotsp xs) (consp xs))
          (fn-rsc-typed-snapshotsp (cdr xs)))
 :hints (("Goal" :expand ((fn-rsc-typed-snapshotsp xs))
          :in-theory (disable fn-stxk-p fn-rsc-typed-snapshotsp)))))
(defthm fn-rsc-step-preserves-actual-selected-snapshot
 (implies (fn-rsc-invariantp cursor)
  (and (fn-rsc-invariantp (mv-nth 1 (fn-rsc-step cursor)))
       (equal (fn-rsc-abstract (mv-nth 1 (fn-rsc-step cursor)))
              (fn-rsc-abstract cursor))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-rsc-step fn-rsc-invariantp
                                    fn-rsc-abstract fn-rsc-widthp fn-rsc-at
                                    fn-rsc-typed-snapshotsp fn-stxk-find)
                                   (fn-stxk-p fn-stxk-keyring-generation)))))
; Establishment/preservation use the actual public replay decision. These
; properties are carried by bootstrap/writers, never recomputed over history.
(defthm fn-rsc-initial-context-has-typed-snapshots
 (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots (fn-stxk-initial-context next)))
 :hints (("Goal" :in-theory (enable fn-stxk-initial-context fn-stxk-context
                                    fn-stxk-context-snapshots fn-rsc-typed-snapshotsp))))
(local (defthm fn-rsc-snapshot-step-keeps-typed-snapshots
 (implies (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots ctx))
  (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots (fn-stxk-apply-snapshot ctx event))))
 :hints (("Goal" :in-theory (e/d (fn-stxk-apply-snapshot fn-stxk-fault
                                  fn-stxk-context fn-stxk-context-snapshots
                                  fn-rsc-typed-snapshotsp)
                                 (fn-stxk-p fn-stxk-find fn-stxk-same-snapshotp))))))
(local (defthm fn-rsc-verdict-step-keeps-snapshots
 (equal (fn-stxk-context-snapshots (fn-stxk-apply-verdict ctx event))
        (fn-stxk-context-snapshots ctx))
 :hints (("Goal" :in-theory (e/d (fn-stxk-apply-verdict fn-stxk-fault
                                  fn-stxk-context fn-stxk-context-snapshots)
                                 (fn-stxe-p fn-stxk-find fn-stxe-keyring-profile))))))
(local (defthm fn-rsc-carried-step-keeps-snapshots
 (equal (fn-stxk-context-snapshots (fn-replay-apply-carried-verdict ctx event))
        (fn-stxk-context-snapshots ctx))
 :hints (("Goal" :in-theory (e/d (fn-replay-apply-carried-verdict fn-stxk-fault
                                  fn-stxk-context fn-stxk-context-snapshots)
                                 (fn-stxe-p))))))
(local (defthm fn-rsc-revoked-step-keeps-snapshots
 (equal (fn-stxk-context-snapshots (fn-replay-apply-revoked-verdict ctx event keys))
        (fn-stxk-context-snapshots ctx))
 :hints (("Goal" :in-theory (e/d (fn-replay-apply-revoked-verdict fn-stxk-fault
                                  fn-stxk-context fn-stxk-context-snapshots)
                                 (fn-stxe-p fn-hsig-revoked-tombstone-bindsp))))))
(defthm fn-rsc-actual-replay-preserves-typed-snapshots
 (implies (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots ctx))
  (fn-rsc-typed-snapshotsp
   (fn-stxk-context-snapshots (fn-replay-identity-step ctx event))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-rsc-snapshot-step-keeps-typed-snapshots
         (event (fn-replay-identity-wire event)))
        (:instance fn-rsc-verdict-step-keeps-snapshots
         (event (fn-replay-identity-wire event)))
        (:instance fn-rsc-verdict-step-keeps-snapshots
         (event (fn-stmt-value (fn-stxe-decode-exact
          (fn-stxa-verdict-event (fn-replay-identity-wire event))))))
        (:instance fn-rsc-carried-step-keeps-snapshots
         (event (fn-stmt-value (fn-stxe-decode-exact
          (fn-stxa-verdict-event (fn-replay-identity-wire event))))))
        (:instance fn-rsc-revoked-step-keeps-snapshots
         (event (fn-stmt-value (fn-stxe-decode-exact
          (fn-stxa-verdict-event (fn-replay-identity-wire event)))))
         (keys (fn-hsig-article-event-carrier-keys (fn-replay-identity-wire event)))))
  :in-theory
  (e/d (fn-replay-identity-step fn-replay-identity-advance
         fn-stxk-fault fn-stxk-context fn-stxk-context-snapshots)
        (fn-rsc-snapshot-step-keeps-typed-snapshots
         fn-rsc-verdict-step-keeps-snapshots fn-rsc-carried-step-keeps-snapshots
         fn-rsc-revoked-step-keeps-snapshots
         fn-stxk-p fn-stxe-p fn-stxa-p fn-stxk-apply-snapshot
         fn-stxk-apply-verdict fn-replay-apply-carried-verdict
         fn-replay-apply-revoked-verdict fn-stxk-find fn-stxa-bindsp
         fn-hsig-article-event-carried-bindsp fn-hsig-article-event-revoked-bindsp
         fn-hsig-article-event-snapshot-bindsp fn-stxe-decode-exact
         fn-stmt-okp fn-stmt-value fn-rsc-typed-snapshotsp)))))

(in-theory (disable fn-rsc-begin fn-rsc-step fn-rsc-abstract fn-rsc-invariantp
                    fn-rsc-typed-snapshotsp))
