; Teeth for books/owner-retain-carried.lisp and A-RECOVERED-OPEN
; (books/assumptions-recovery.lisp), Codex review r29-F2.
;
;   1. Each producer theorem: a REACHABLE POSITIVE WITNESS -- the named
;      assumption holds (by its exported non-vacuity constraint) at the
;      empty history's checkpoint and its Store open under the default
;      configuration, and the conclusion holds there on its non-:fault
;      side, evaluated -- and a SINGLE-HYPOTHESIS REMOVAL: an input where
;      the producer yields an owner that is neither :fault nor invariant (so
;      the theorem without its hypothesis is false), and, by the theorem
;      itself, the assumption is false there (it is not everything).
;   2. The consumer and topic transitions over the ACL2 state: a positive
;      witness (the owner global at the reserved owner, the host's prepare,
;      the relation before and after) and a hypothesis-removal witness (a
;      corrupted owner: the relation fails before and after).
;
; The owners, events and the corrupted owner are owner-log-ocl-tests' and
; owner-prepare-served-events-tests'.
(in-package "ACL2")
(include-book "../../books/owner-retain-carried")
(include-book "owner-prepare-served-events-tests")

; -----------------------------------------------------------------------------
; 1a. fn-owner-store-open-install-produces-invariant.
(defconst *ort-configs* (list *fn-cfg-default-record*))
(defconst *ort-e* (fn-sco-extend (fn-sco-capture *ort-configs* nil) *ort-configs* nil))
(defconst *ort-pair* (fn-sco-store-open *ort-e* *ort-configs* 0))
(defconst *ort-pair-oc* (fn-ock-install (car *ort-pair*) (cadr *ort-pair*) 4))
; Positive: the assumption holds at the empty open's pair (exported) ...
(defthm ort-store-open-pair-assumed
  (fn-assume-store-open-pairp (car *ort-pair*) (cadr *ort-pair*))
  :rule-classes nil
  :hints (("Goal" :use fn-assume-store-open-pair-of-the-empty-history
           :in-theory (theory 'minimal-theory))))
; ... the theorem's full conclusion there ...
(defthm ort-store-open-pair-conclusion
  (or (equal (fn-ock-install (car *ort-pair*) (cadr *ort-pair*) 4) :fault)
      (fn-lgoc-invariantp (fn-ock-install (car *ort-pair*) (cadr *ort-pair*) 4)))
  :rule-classes nil
  :hints (("Goal" :use (ort-store-open-pair-assumed
                        (:instance fn-owner-store-open-install-produces-invariant
                                   (replayed (car *ort-pair*)) (opened (cadr *ort-pair*))
                                   (max-conns 4)))
           :in-theory (theory 'minimal-theory))))
; ... and on its non-:fault side: an installed owner, the invariant evaluated,
; the very owner the row's witness opens from.
(assert-event (not (equal *ort-pair-oc* :fault)))
(assert-event (fn-lgoc-invariantp *ort-pair-oc*))
(assert-event (equal *ort-pair-oc* (fn-owner-retain-witness-oc)))
; Removal: the replay of the empty history under NO configuration crossed
; with the default open: not :fault, not invariant ...
(defconst *ort-pair0* (fn-sco-store-open (fn-sco-extend (fn-sco-capture nil nil) nil nil) nil 0))
(defconst *ort-crossed-oc* (fn-ock-install (car *ort-pair0*) (cadr *ort-pair*) 4))
(assert-event (not (equal *ort-crossed-oc* :fault)))
(assert-event (not (fn-lgoc-invariantp *ort-crossed-oc*)))
; ... so the assumption is false at the crossed pair: it is not everything.
(defthm ort-crossed-pair-not-assumed
  (not (fn-assume-store-open-pairp (car *ort-pair0*) (cadr *ort-pair*)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-owner-store-open-install-produces-invariant
                                   (replayed (car *ort-pair0*)) (opened (cadr *ort-pair*))
                                   (max-conns 4)))
           :in-theory '((:executable-counterpart fn-ock-install)
                        (:executable-counterpart fn-lgoc-invariantp)
                        (:executable-counterpart equal) car-cons cdr-cons))))

; -----------------------------------------------------------------------------
; 1b. fn-owner-recover-extended-produces-invariant.  owner-checkpoint-open-
; tests' image: two retention events, two configuration records.
(defconst *ort-ev*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-ock" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-ock" "subject" "evidence" 0)))
(defconst *ort-cf*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
; Positive: the empty history's E is a capture extension (exported) ...
(defthm ort-extension-assumed
  (fn-assume-capture-extensionp *ort-e* *ort-configs*)
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-assume-capture-extension-of-the-empty-history
                                   (configs *ort-configs*)))
           :in-theory (theory 'minimal-theory))))
(defthm ort-extension-conclusion
  (or (equal (fn-ock-recover-extended *ort-e* *ort-configs* 0 4) :fault)
      (fn-lgoc-invariantp (fn-ock-recover-extended *ort-e* *ort-configs* 0 4)))
  :rule-classes nil
  :hints (("Goal" :use (ort-extension-assumed
                        (:instance fn-owner-recover-extended-produces-invariant
                                   (extended *ort-e*) (configs *ort-configs*)
                                   (frontier 0) (max-conns 4)))
           :in-theory (theory 'minimal-theory))))
(assert-event (not (equal (fn-ock-recover-extended *ort-e* *ort-configs* 0 4) :fault)))
(assert-event (fn-lgoc-invariantp (fn-ock-recover-extended *ort-e* *ort-configs* 0 4)))
; and a checkpoint split after the first event, recovered over the second:
(defconst *ort-real*
  (fn-sco-extend (fn-sco-capture *ort-cf* (list (car *ort-ev*))) *ort-cf* (cdr *ort-ev*)))
(assert-event (not (equal (fn-ock-recover-extended *ort-real* *ort-cf* 8 4) :fault)))
(assert-event (fn-lgoc-invariantp (fn-ock-recover-extended *ort-real* *ort-cf* 8 4)))
; Removal: the same checkpoint with its configuration fold taken from a
; history whose events name another subject -- a checkpoint file that is not
; this history's capture.  The producer installs it (not :fault) and the
; owner is not invariant ...
(defconst *ort-ev-other*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-ock" "subjecu" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-ock" "subjecu" "evidence" 0)))
(defconst *ort-forged*
  (update-nth 2 (nth 2 (fn-sco-extend (fn-sco-capture *ort-cf* (list (car *ort-ev-other*)))
                                      *ort-cf* (cdr *ort-ev-other*)))
              *ort-real*))
(defconst *ort-forged-oc* (fn-ock-recover-extended *ort-forged* *ort-cf* 8 4))
(assert-event (not (equal *ort-forged-oc* :fault)))
(assert-event (not (fn-lgoc-invariantp *ort-forged-oc*)))
; ... so the forged checkpoint is not a capture extension.
(defthm ort-forged-not-assumed
  (not (fn-assume-capture-extensionp *ort-forged* *ort-cf*))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-owner-recover-extended-produces-invariant
                                   (extended *ort-forged*) (configs *ort-cf*)
                                   (frontier 8) (max-conns 4)))
           :in-theory '((:executable-counterpart fn-ock-recover-extended)
                        (:executable-counterpart fn-lgoc-invariantp)
                        (:executable-counterpart equal)))))

; -----------------------------------------------------------------------------
; 2. The transitions over the ACL2 state.  The state: ACL2's built state with
; the owner global at OC (the retention carry unset: nil, fn-prc-carryp).
(defun ort-state (oc)
  (declare (xargs :verify-guards nil))
  (put-global 'fn-owner oc (build-state)))

; fn-owner-prepare-consumer-preserves-retain-state.  Positive: at the
; reserved owner the relation holds; the host's consumer prepare of ACL2's
; bootstrap proposal answers :prepared and the relation holds after.
(defthm ort-consumer-positive
  (let ((st (ort-state *lgt-reserved*)))
    (and (fn-owner-retain-statep st)
         (equal (mv-nth 1 (fn-owner-prepare-consumer *pse-consumer-event* (create-fn-arena$a) st))
                :prepared)
         (fn-owner-retain-statep
          (mv-nth 2 (fn-owner-prepare-consumer *pse-consumer-event* (create-fn-arena$a) st)))))
  :rule-classes nil)
; Hypothesis removal (corrupted state): the topic counter moved
; (*lgt-bad-reserved*): the relation fails before and after.
(defthm ort-consumer-removal
  (let ((st (ort-state *lgt-bad-reserved*)))
    (and (not (fn-owner-retain-statep st))
         (not (fn-owner-retain-statep
               (mv-nth 2 (fn-owner-prepare-consumer *pse-consumer-event*
                                                    (create-fn-arena$a) st))))))
  :rule-classes nil)

; fn-owner-prepare-topic-preserves-retain-state, likewise.
(defthm ort-topic-positive
  (let ((st (ort-state *lgt-reserved*)))
    (and (fn-owner-retain-statep st)
         (equal (mv-nth 1 (fn-owner-prepare-topic *pse-topic-event* (create-fn-arena$a) st))
                :prepared)
         (fn-owner-retain-statep
          (mv-nth 2 (fn-owner-prepare-topic *pse-topic-event* (create-fn-arena$a) st)))))
  :rule-classes nil)
(defthm ort-topic-removal
  (let ((st (ort-state *lgt-bad-reserved*)))
    (and (not (fn-owner-retain-statep st))
         (not (fn-owner-retain-statep
               (mv-nth 2 (fn-owner-prepare-topic *pse-topic-event*
                                                 (create-fn-arena$a) st))))))
  :rule-classes nil)
