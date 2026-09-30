; One consumer/authority interpreter for actual Store completion and recovery.
; The four-field result retains the account publication from the same decision.
; Owner publication must fund and install CP7/canonical carries/root atomically.
(in-package "ACL2")
(include-book "consumer-store-projection")
(include-book "consumer-account-adoption")
(include-book "consumer-authority-revision")
(include-book "config-record-order")
(include-book "control-visible-effect")

 ; Ordinary article append can publish a control cancellation or resolve a
; pending withdrawal. Event kind is therefore not a visibility certificate.
; VISIBILITY-EFFECT must come from the same ACL2 refresh/control producer as
; the changed Store view. Its full live/recovery relation is still required.
(defun fn-carf-effect-step (s visibility-effect)
  (declare (xargs :guard t))
  (cond ((eq visibility-effect :preserved) (list :ok s))
        ((eq visibility-effect :changed) (fn-carv-semantic-step s))
        ((not (fn-cp-nth 3 (fn-cp-nth 6 s)))
         ; No namespace is externally usable yet. Unknown semantic change
         ; conservatively aborts preparation before fresh namespace birth.
         (fn-carv-semantic-step s))
        (t (list :refused :visibility-effect-unproved))))

; Full result: (:ok CP newly-published-root-or-nil fence-event-count-or-nil).
; A proposal result is not durable acceptance. The actual completion and
; recovery supply the persisted event; preallocation uses the same decision.
(defun fn-carf-event-step (s event expected visibility-effect)
  (declare (xargs :guard t))
  (if (or (not (fn-cp-uintp expected))
          (>= (nfix expected) *fn-cbor-max-uint*)
          (not (equal (fn-store-event-sequence event) expected)))
      (list :refused :sequence)
    (if (fn-cac-eventp event)
        (let ((one (fn-caa-step s event)))
          (if (not (eq (car one) :ok)) one
            (let ((root (fn-cp-nth 2 one)))
              (list :ok (fn-cp-nth 1 one) root (if root (1+ expected) nil)))))
      (let ((one (fn-cpe-projection-step s event expected)))
        (if (not (eq (car one) :ok)) one
          (let* ((effect (cond ((fn-cpe-eventp event)
                                (if (eq (fn-cp-nth 0 (fn-cpe-operation event)) :rollover)
                                    :changed :preserved))
                               ((or (fn-stxk-p event) (fn-th-topic-eventp event)
                                    (fn-store-retention-event-p event)) :changed)
                               (t visibility-effect)))
                 (semantic (fn-carf-effect-step (fn-cp-nth 1 one) effect)))
            (if (eq (car semantic) :ok)
                (list :ok (fn-cp-nth 1 semantic) nil nil)
              semantic)))))))

 ; Actual shared append producer: the effect is derived from the same
; withdrawals/visible decision whose values the caller installs. No host
; Boolean or second refresh is allowed. The four-field interpreter result
; carries a newly published account root from that one authority decision.
(defun fn-carf-event-refresh-step
    (s event expected new old ws old-visible old-verdicts verdicts
       files fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t))
  (mv-let (withdrawals withdrawal-effect)
    (fn-ctl-refresh-withdrawals-effect-fx
     new old ws verdicts files fn-hist configs)
    (mv-let (visible effect)
      (fn-ctl-refresh-visible-effect
       new old old-visible withdrawals old-verdicts verdicts withdrawal-effect)
      (mv (fn-carf-event-step s event expected effect) withdrawals visible))))

 ; Pre-frontier proposal over the captured immutable history plus ONE
; prepared candidate row. The caller must bind actual projected coordinates,
; admission funding and owner/config/authority epoch, and revalidate after
; yield BEFORE allocation. This return is never durable authorization.
(defun fn-carf-append-candidate-step
    (s candidate expected new old ws old-visible old-verdicts verdicts
       files fn-hist configs)
  (declare (xargs :stobjs fn-hist :guard t))
  (mv-let (withdrawals withdrawal-effect)
    (fn-ctl-append-withdrawals-candidate-effect-fx
     new old ws verdicts files fn-hist configs candidate)
    (mv-let (visible effect)
      (fn-ctl-refresh-visible-effect
       new old old-visible withdrawals old-verdicts verdicts withdrawal-effect)
      (mv (fn-carf-event-step s candidate expected effect) withdrawals visible))))

; Live callers invoke this INSIDE accepted durable configuration install.
; Joint recovery calls it at that same cfg-first position; a pending candidate
; on the preceding base is discarded, never authorized as a side effect.
(defun fn-carf-config-step (s record)
  (declare (xargs :guard t))
  (if (fn-cfg-recordp record) (fn-carv-semantic-step s)
    (list :refused :configuration)))

; Recovery is a whole-history boundary, never a per-request lookup. The Store
; node/config fold separately establishes its physical/generation invariants.
; This fold supplies consumer authority at EACH historical event position,
; not a final config counter applied after consumer replay. EFFECTS is a
; proof/model companion from actual ACL2 view refresh, NOT host assertions or
; yet a served/recovery entry. The coherent effect producer remains OPEN.
(defun fn-carf-fold (configs events effects s root fence-count config-sequence expected)
  (declare (xargs :guard t :measure (+ (len configs) (len events))))
  (if (fn-cpr-config-firstp configs events)
      (let ((record (car configs)))
        (if (not (equal (fn-cfg-record-sequence record) config-sequence))
            (list :refused :config-sequence)
          (let ((one (fn-carf-config-step s record)))
            (if (not (eq (car one) :ok)) one
              (fn-carf-fold (cdr configs) events effects (fn-cp-nth 1 one) root fence-count
                            (1+ (nfix config-sequence)) expected)))))
    (if (consp events)
        (let ((one (fn-carf-event-step s (car events) expected (fn-cp-nth 0 effects))))
          (if (not (eq (car one) :ok)) one
            (fn-carf-fold configs (cdr events)
                          (if (consp effects) (cdr effects) nil) (fn-cp-nth 1 one)
                          (if (fn-cp-nth 2 one) (fn-cp-nth 2 one) root)
                          (if (fn-cp-nth 3 one) (fn-cp-nth 3 one) fence-count)
                          config-sequence (1+ (nfix expected)))))
      (if (and (null configs) (null events) (null effects))
          (list :ok s root fence-count)
        (list :refused :history)))))

(defun fn-carf-replay (configs events effects)
  (declare (xargs :guard t))
  (fn-carf-fold configs events effects nil nil nil 0 0))

(defthm fn-carf-effect-step-preserved-unfolds
  (equal (fn-carf-effect-step s :preserved) (list :ok s))
  :hints (("Goal" :in-theory (enable fn-carf-effect-step))))

(defthm fn-carf-effect-step-refuses-exhausted-change
  (implies (and (fn-cp-nth 3 (fn-cp-nth 6 s))
                (equal (fn-cp-nth 1 (fn-cp-nth 6 s)) *fn-cbor-max-uint*))
           (equal (fn-carf-effect-step s :changed)
                  '(:refused :authority-revision-exhausted)))
  :hints (("Goal" :in-theory
           (e/d (fn-carf-effect-step fn-carv-semantic-step)
                (fn-carv-revision-state fn-cp-nth)))))
