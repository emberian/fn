; SAME actual physical/identity decision retained through control-input yields.
; SOURCE-ASSEMBLY ONLY: actual candidate source custody, predicates/guards,
; carry establishment and allocation/retirement grants are not yet qualified.
(in-package "ACL2")
(include-book "consumer-configured-authority-replay")
(include-book "consumer-control-row-cursor")

; Fixed22 borrowed job: tag,S,nextCN,produced6,new,old,verdicts,rowcarry,CEP,
; mode,phase,remaining,reverse,forward,controlCursor,effect,chain,source,F,
; E-upper,arrivingLocks,densePredecessorCount. No externally supplied effect authorizes mutation.
(defun fn-cape-replace (n value job)
 (declare (xargs :guard t :verify-guards nil))
 (ec-call (update-nth n value job)))

; Internal pure continuation only. Live owner passes its internally retained
; actual node decision; recovery passes its ONE CPR result. This is not a
; public/native API accepting a supplied CN or semantic-authority flag.
; Typed obligation/source correspondence remains part of actual core producer
; establishment, and unsupported preparation is explicitly unavailable.
(defun fn-cape-after-node (s produced next base-row-carry cep-cursor chain captured-source f upper predecessor-count)
 (declare (xargs :guard (and (fn-cnode-statep (fn-cp-nth 1 s))
                             (fn-cnode-statep next)) :verify-guards nil))
 (if (or (not (fn-cp-uintp predecessor-count))
         (mbe :logic (not (fn-cnode-statep next)) :exec (not (consp next))))
     (list :unavailable s :semantic-preparation-unavailable)
  (let* ((cn (fn-cp-nth 1 s))
         (old (fn-state-articles (fn-node-acceptance (fn-cnode-node cn))))
         (new (fn-state-articles (fn-node-acceptance (fn-cnode-node next))))
         (verdicts (if (eq (fn-cp-nth 3 produced) :verdict)
                       (cons (fn-replay-verdict-pair (fn-cp-nth 4 produced))
                             (fn-cp-nth 11 s)) (fn-cp-nth 11 s)))
         (mode (cond ((equal new old) :unchanged)
                     ((and (consp new) (equal (cdr new) old)) :append)
                     (t :rebuild))))
   (list :yield
    (list :configured-control-event s next produced new old verdicts
          base-row-carry cep-cursor mode
          (if (eq mode :unchanged) :finish :article-begin)
          new nil (if (eq mode :unchanged) (fn-cp-nth 9 s) nil)
          nil (if (eq mode :rebuild) :changed :preserved)
          chain captured-source f upper nil predecessor-count)))))

(defun fn-cape-begin (s produced base-row-carry cep-cursor chain captured-source f upper predecessor-count)
 (declare (xargs :guard (fn-cnode-statep (fn-cp-nth 1 s)) :verify-guards nil))
 (let* ((cn (fn-cp-nth 1 s)) (event (fn-cp-nth 0 (fn-cp-nth 15 s)))
        (es (fn-cp-nth 13 s)) (checked (fn-cp-nth 0 produced)))
  (cond ((not (and (natp f) (fn-cp-uintp predecessor-count)
                    (equal f (1+ predecessor-count)) (natp es) (natp upper)))
         (list :unavailable s :control-prefix-coordinate))
        ((not (fn-store-event-p event)) (fn-capr-fault s :invalid-event))
        ((not (equal (fn-store-event-sequence event) es)) (fn-capr-fault s :event-sequence))
        ((not (eq (fn-stxk-context-kind checked) :ok)) (fn-capr-fault s :identity))
        ((not (eq (fn-cp-nth 2 produced) :carried)) (list :unavailable s :identity-carries))
        (t
         (let ((next (fn-cpr-apply-event cn event)))
          (if (mbe :logic (not (fn-cnode-statep next)) :exec (not (consp next)))
              (fn-capr-fault s :event-refusal)
           (fn-cape-after-node s produced next base-row-carry cep-cursor
                               chain captured-source f upper predecessor-count)))))))

; Complete the SAME original event once, after its actual control inputs are
; retained. This does not recompute physical or identity replay after a yield.
; Existing visible/withdrawal authority semantics remain the named subjects;
; their quantum/cost and all-writer/cold relation are still explicit debts.
(defun fn-cape-finish (job)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((s (fn-cp-nth 1 job)) (next (fn-cp-nth 2 job))
        (produced (fn-cp-nth 3 job)) (event (fn-cp-nth 0 (fn-cp-nth 15 s)))
        (es (fn-cp-nth 13 s)) (cp (fn-cp-nth 4 s)) (metadata (fn-cp-nth 5 s))
        (ws (fn-cp-nth 13 job)) (verdicts (fn-cp-nth 6 job)))
  (mv-let (visible effect)
   (fn-ctl-refresh-visible-effect (fn-cp-nth 4 job) (fn-cp-nth 5 job)
      (fn-cp-nth 10 s) ws (fn-cp-nth 11 s) verdicts (fn-cp-nth 15 job))
   (let* ((authorityp (fn-cae-eventp event))
          (full (if authorityp
                    (fn-acj-stage cp metadata (fn-cp-nth 6 s)
                       (fn-cnode-config (fn-cp-nth 1 s)) event es (fn-cp-nth 7 job))
                  (fn-carfc-event-step cp event es effect metadata (fn-cp-nth 8 job))))
          (pending (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 full))))
          (beginp (and authorityp (eq (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-begin))))
    (if (not (eq (fn-cp-nth 0 full) :ok)) (fn-capr-fault s full)
     (fn-capr-install s next (fn-cp-nth 0 produced) (fn-cp-nth 1 produced) full
       (if authorityp (fn-cp-nth 6 full) (if pending (fn-cp-nth 6 s) nil))
       (if beginp (fn-cp-nth 21 job) (if pending (fn-cp-nth 8 s) nil))
       ws visible verdicts (fn-cp-nth 12 s) (1+ (nfix es))
       (fn-cp-nth 14 s) (ec-call (cdr (fn-cp-nth 15 s)))))))))

; Consume ONE completed article decision. Its own captured locks resolve old
; withdrawals targeting an arriving article, even with no visible old target.
(defun fn-cape-article-result (job one)
 (declare (xargs :guard t :verify-guards nil))
 (cond
  ((eq (fn-cp-nth 0 one) :yield)
   (list :yield (fn-cape-replace 14 (fn-cp-nth 1 one)
                 (fn-cape-replace 10 :article job))))
  ((eq (fn-cp-nth 0 one) :read)
   (list :read job (fn-cp-nth 2 one) (fn-cp-nth 3 one)))
  ((not (eq (fn-cp-nth 0 one) :plan)) (list :unavailable job one))
  ((eq (fn-cp-nth 9 job) :append)
   (let* ((plan (fn-cp-nth 1 one)) (planp (fn-ctl-withdrawalp plan))
          (j (fn-cape-replace 20 (fn-cp-nth 3 one)
               (fn-cape-replace 14 plan
                (fn-cape-replace 12 nil
                 (fn-cape-replace 11 (fn-cp-nth 9 (fn-cp-nth 1 job))
                  (fn-cape-replace 10 :resolve job)))))))
    (list :yield (if planp (fn-cape-replace 15 :changed j) j))))
  (t
   (let* ((plan (fn-cp-nth 1 one)) (oldreverse (fn-cp-nth 12 job))
          (j (fn-cape-replace 12 (if (fn-ctl-withdrawalp plan)
                                    (cons plan oldreverse) oldreverse)
               (fn-cape-replace 11 (ec-call (cdr (fn-cp-nth 11 job)))
                (fn-cape-replace 10 :article-begin job)))))
    (list :yield j)))))

; ONE article start/input/config cell, ONE old withdrawal cell, or ONE reverse
; cell. Visibility finalization and private row/control parsing still require
; their actual profile quantum/funding relation, not an invented constant.
(defun fn-cape-step (job)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (and (fn-cbor-at-mostp job 22) (true-listp job) (equal (len job) 22)
               (eq (fn-cp-nth 0 job) :configured-control-event)))
     '(:refused :configured-control-event-cursor)
  (case (fn-cp-nth 10 job)
   (:finish (fn-cape-finish job))
   (:article-begin
    (if (not (consp (fn-cp-nth 11 job)))
        (list :yield (fn-cape-replace 10 :reverse (fn-cape-replace 13 nil job)))
     (fn-cape-article-result job
      (fn-ctcd-begin (car (fn-cp-nth 11 job)) (fn-cp-nth 6 job)
                     (fn-cp-nth 16 job) (fn-cp-nth 17 job)
                     (fn-cp-nth 18 job) (fn-cp-nth 19 job)))))
   (:article (fn-cape-article-result job (fn-ctcd-step (fn-cp-nth 14 job))))
   (:resolve
    (let ((ws (fn-cp-nth 11 job)))
     (if (not (consp ws))
         (list :yield (fn-cape-replace 10 :reverse (fn-cape-replace 13 nil job)))
      (let* ((m (fn-article-msgid (car (fn-cp-nth 4 job))))
             (w (car ws)) (matched (and (fn-ctl-withdrawalp w)
                                       (equal (fn-ctl-w-target w) m)))
             (changed (if matched (fn-ctl-w-with-tlocks w (fn-cp-nth 20 job)) w))
             (j (fn-cape-replace 11 (cdr ws)
                  (fn-cape-replace 12 (cons changed (fn-cp-nth 12 job)) job))))
       (list :yield (if matched (fn-cape-replace 15 :changed j) j))))))
   (:reverse
    (let ((rev (fn-cp-nth 12 job)))
     (if (consp rev)
         (list :yield (fn-cape-replace 12 (cdr rev)
                       (fn-cape-replace 13 (cons (car rev) (fn-cp-nth 13 job)) job)))
      (let* ((plan (fn-cp-nth 14 job))
             (ws (fn-cp-nth 13 job))
             (final (if (and (eq (fn-cp-nth 9 job) :append) (fn-ctl-withdrawalp plan))
                        (cons plan ws) ws)))
       (list :yield (fn-cape-replace 13 final (fn-cape-replace 10 :finish job)))))))
   (otherwise (list :unavailable job :configured-control-event-phase)))))

; The actual registered candidate reader calls this only upon a completed
; row from the SAME captured source. No physical re-execution, source issuance
; or prefix append occurs in this continuation.
(defun fn-cape-row (job row)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (eq (fn-cp-nth 10 job) :article))
     '(:refused :configured-control-event-read-phase)
   (fn-cape-article-result job (fn-ctcd-row (fn-cp-nth 14 job) row))))

(in-theory (disable fn-cape-replace fn-cape-after-node fn-cape-begin fn-cape-finish
                    fn-cape-article-result fn-cape-step fn-cape-row))
