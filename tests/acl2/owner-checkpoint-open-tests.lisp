; Teeth for books/owner-checkpoint-open.
;
; The witness is store-checkpoint-open-tests' image: two retention events
; and two configuration records, the second at txid 7 after both events,
; split after the first event.  The owner installed from the checkpoint is
; the owner the full open installs, and it is a configured owner, not :fault.
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/owner-checkpoint-open")

(defconst *ock-t-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "forward-ock" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "forward-ock" "subject" "evidence" 0)))
(defconst *ock-t-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(defconst *ock-t-prefix* (list (car *ock-t-events*)))
(defconst *ock-t-suffix* (cdr *ock-t-events*))
(defconst *ock-t-full* (fn-ock-recover-full *ock-t-configs* 8 *ock-t-events* 4))
(defconst *ock-t-extended*
  (fn-sco-extend (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                 *ock-t-configs* *ock-t-suffix*))

; The keystone, evaluated on a reachable owner.
(assert-event (not (equal *ock-t-full* :fault)))
(assert-event (fn-ocl-relation *ock-t-full*))
(assert-event (equal (fn-ock-recover-extended *ock-t-extended* *ock-t-configs* 8 4)
                     *ock-t-full*))
; The full path: the empty capture extended over the whole history.
(assert-event (equal (fn-ock-recover-extended
                      (fn-sco-extend (fn-sco-capture *ock-t-configs* nil)
                                     *ock-t-configs* *ock-t-events*)
                      *ock-t-configs* 8 4)
                     *ock-t-full*))
; The extended value is the capture of the whole history: the owner's base.
(assert-event (equal *ock-t-extended*
                     (fn-sco-capture *ock-t-configs* *ock-t-events*)))
; The configuration the owner serves is the replay's last generation.
(assert-event (equal (fn-cfg-generation (fn-ocfg-config *ock-t-full*)) 2))

; The keystone is not vacuous: a checkpoint of a different prefix installs a
; different owner (the checkpoint's records are the Store's history).
(must-fail-checked
 (defthm ock-t-other-prefix
   (equal (fn-ock-recover-extended
           (fn-sco-extend (fn-sco-capture *ock-t-configs* *ock-t-suffix*)
                          *ock-t-configs* *ock-t-suffix*)
           *ock-t-configs* 8 4)
          *ock-t-full*)))

; fn-ock-recover-installs-ocl-relation, its one hypothesis (the host did not
; refuse): a refused install (connection bound not natural) is :fault, and
; :fault satisfies no relation.
(assert-event (equal (fn-ock-recover-extended *ock-t-extended* *ock-t-configs* 8 nil)
                     :fault))
(must-fail-checked
 (defthm ock-t-relation-without-install
   (fn-ocl-relation (fn-ock-recover-extended *ock-t-extended* *ock-t-configs* 8 nil))))

; The publication keystone.  Witness: from the capture of the prefix the
; owner publishes the capture of the whole history, by extension.
(assert-event (fn-sn-observed-historyp 8 *ock-t-events*))
(assert-event (equal (fn-ock-next-checkpoint
                      (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                      *ock-t-configs* *ock-t-events*)
                     (fn-sco-capture *ock-t-configs* *ock-t-events*)))
(assert-event (equal (fn-sco-open (fn-ock-next-checkpoint
                                   (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                                   *ock-t-configs* *ock-t-events*)
                                  *ock-t-configs* 8 nil)
                     (fn-cpo-open-observed *ock-t-configs* 8 *ock-t-events*)))
; Its hypothesis (an admitted history) has NO must-fail: the identity
; fold's append lemma takes it, but the fault that fold stops on is
; absorbing, and these non-admitted histories give the capture too.  The
; hypothesis is therefore reported untoothed (planning/evidence/
; owner-checkpoint-open-2026-09-25.md); the owner's history always meets it.
(defconst *ock-t-improper* (cons (car *ock-t-events*) 'tail))
(assert-event (not (fn-sn-observed-historyp 8 *ock-t-improper*)))
(assert-event (not (fn-sn-observed-historyp 8 (list 'junk 'junk2))))
(assert-event (equal (fn-ock-next-checkpoint (fn-sco-capture *ock-t-configs* (list 'junk))
                                             *ock-t-configs* (list 'junk 'junk2))
                     (fn-sco-capture *ock-t-configs* (list 'junk 'junk2))))
(assert-event (equal (fn-ock-next-checkpoint (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                                             *ock-t-configs* *ock-t-improper*)
                     (fn-sco-capture *ock-t-configs* *ock-t-improper*)))

; The publication policy: not due below K/2, due at K/2, and not again at the
; count of a failed attempt.
(assert-event (not (fn-ock-publication-duep 0 1 4 nil)))
(assert-event (fn-ock-publication-duep 0 2 4 nil))
(assert-event (fn-ock-publication-duep nil 2 4 nil))
(assert-event (not (fn-ock-publication-duep 0 2 4 2)))
(assert-event (fn-ock-publication-duep 0 3 4 2))
(assert-event (equal (car (fn-sco-select :ok 0 1 4)) :checkpoint))
; fn-ock-not-due-keeps-the-checkpoint-open, one must-fail per hypothesis.
(must-fail-checked
 (defthm ock-t-not-due-without-natp-durable
   (equal (car (fn-sco-select :ok nil 0 5)) :checkpoint)))
(assert-event (not (fn-ock-publication-duep nil 0 5 nil)))
(must-fail-checked
 (defthm ock-t-not-due-without-natp-count
   (equal (car (fn-sco-select :ok 0 nil 5)) :checkpoint)))
(assert-event (not (fn-ock-publication-duep 0 nil 5 nil)))
(must-fail-checked
 (defthm ock-t-not-due-without-durable-below-count
   (equal (car (fn-sco-select :ok 5 3 5)) :checkpoint)))
(assert-event (not (fn-ock-publication-duep 5 3 5 nil)))
(must-fail-checked
 (defthm ock-t-not-due-without-natp-k
   (equal (car (fn-sco-select :ok 0 0 nil)) :checkpoint)))
(assert-event (not (fn-ock-publication-duep 0 0 nil 1)))
(must-fail-checked
 (defthm ock-t-not-due-without-a-new-count
   (equal (car (fn-sco-select :ok 0 20 4)) :checkpoint)))
(assert-event (not (fn-ock-publication-duep 0 20 4 20)))

; -----------------------------------------------------------------------------
; checkpoint-cost (PKT-141)

; The capture of the whole history (the schema-3 tables' value since lane
; checkpoint-pipeline: books/store-checkpoint-tables.lisp carries the
; witnesses of the file).
(defconst *ock-t-capture* (fn-sco-capture *ock-t-configs* *ock-t-events*))

; The one-pass Store open.  Witness: from the prefix's capture extended over
; the suffix, the open is the full open, :ok, and the configuration fold is
; the full replay.
(defconst *ock-t-store-open* (fn-sco-store-open *ock-t-extended* *ock-t-configs* 8))
(assert-event (equal (cadr *ock-t-store-open*)
                     (fn-cpo-open-observed *ock-t-configs* 8 *ock-t-events*)))
(assert-event (equal (fn-sn-open-kind (cadr *ock-t-store-open*)) :ok))
(assert-event (equal (car *ock-t-store-open*)
                     (fn-cpr-replay *ock-t-configs* *ock-t-events*)))
(assert-event (fn-sn-open-okp (cadr *ock-t-store-open*)))
; The owner from that pair is the full open's owner.
(assert-event (equal (fn-ock-install (car *ock-t-store-open*) (cadr *ock-t-store-open*) 4)
                     *ock-t-full*))

; fn-sco-store-open-of-extended-capture, the hypothesis of its second
; conjunct (the open is :ok) has NO must-fail: on these refused opens (a
; repeated history, an improper prefix, a non-event prefix) the configuration
; fold still equals the full replay.  It is reported untoothed; the host
; reads the configuration only after testing the kind
; (fn-store-sn-open-extended, host/store-node-host.lisp).
(assert-event
 (let ((r (fn-sco-store-open (fn-sco-extend (fn-sco-capture *ock-t-configs* *ock-t-events*)
                                            *ock-t-configs* *ock-t-events*)
                             *ock-t-configs* 8)))
   (and (equal (fn-sn-open-kind (cadr r)) :error)
        (equal (car r) (fn-cpr-replay *ock-t-configs*
                                      (append *ock-t-events* *ock-t-events*))))))
(assert-event
 (let ((r (fn-sco-store-open (fn-sco-extend (fn-sco-capture *ock-t-configs* (list 5))
                                            *ock-t-configs* *ock-t-suffix*)
                             *ock-t-configs* 8)))
   (and (equal (fn-sn-open-kind (cadr r)) :error)
        (equal (car r) (fn-cpr-replay *ock-t-configs* (cons 5 *ock-t-suffix*))))))

; -----------------------------------------------------------------------------
; The recovery-lag policy (checkpoint-pipeline-5, PKT-583 (b)):
; fn-ock-publication-next.  K = 4 as above.  Nothing in flight: the rule's
; word (:due at suffix 2, :idle at 1, :idle when the count is the last
; attempt's), :blocked over a recorded deferral; one in flight (the count it
; captured): never :due, the rule's observation is :coalesce, else :inflight.
(assert-event
 (and (equal (fn-ock-publication-next 0 2 4 nil nil nil) :due)
      (equal (fn-ock-publication-next 0 1 4 nil nil nil) :idle)
      (equal (fn-ock-publication-next 0 2 4 2 nil nil) :idle)
      (equal (fn-ock-publication-next 0 2 4 nil nil t) :blocked)
      (equal (fn-ock-publication-next 0 2 4 nil 2 nil) :coalesce)
      (equal (fn-ock-publication-next 0 1 4 nil 1 nil) :inflight)
      (equal (fn-ock-publication-next 0 5 4 nil 2 t) :coalesce)
      ; the finish binds S to the prefix the capture was handed
      (equal (fn-sco-sequence (fn-ock-next-checkpoint (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                                                      *ock-t-configs* *ock-t-events*))
             (len *ock-t-events*))
      ; K the fast path's threshold: suffix K served from the checkpoint, K + 1 the full replay
      (equal (car (fn-sco-select :ok 2 6 4)) :checkpoint)
      (equal (fn-sco-select :ok 2 7 4) (list :full-replay :suffix-exceeds-k))))

; fn-ock-one-publication-in-flight without its hypothesis: nothing in flight
; and the rule true is :due.
(must-fail-checked
 (defthm ock-t-one-in-flight-without-inflight
   (not (equal (fn-ock-publication-next durable count k attempted inflight blockedp) :due))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-ock-one-publication-in-flight)))))

; fn-ock-publication-next-decides-by-the-rule without its hypothesis: in
; flight, the rule true, the decision is :coalesce, not :due.
(must-fail-checked
 (defthm ock-t-decides-by-the-rule-without-not-inflight
   (iff (equal (fn-ock-publication-next durable count k attempted inflight blockedp) :due)
        (and (not blockedp) (fn-ock-publication-duep durable count k attempted)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-ock-publication-next-decides-by-the-rule)))))

; fn-ock-fast-path-within-k-by-definition without (<= s count): S ahead of the
; count is :ahead-of-history though the difference is within K.
(assert-event (and (<= (- 3 5) 4) (equal (fn-sco-select :ok 5 3 4) (list :full-replay :ahead-of-history))))
(must-fail-checked
 (defthm ock-t-fast-path-without-order
   (implies (and (natp s) (natp count) (natp k))
            (iff (equal (car (fn-sco-select :ok s count k)) :checkpoint)
                 (<= (- count s) k)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-sco-select) (fn-ock-fast-path-within-k-by-definition))))))

; fn-ock-next-checkpoint-is-the-capture
; Reachable positive witness: the capture of the one-event prefix, advanced
; over the admitted history it prefixes, is the capture of the whole history.
(assert-event
 (and (fn-sn-observed-historyp 8 *ock-t-events*)
      (fn-ock-prefixp *ock-t-prefix* *ock-t-events*)
      (equal (fn-ock-next-checkpoint (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                                     *ock-t-configs* *ock-t-events*)
             (fn-sco-capture *ock-t-configs* *ock-t-events*))))
; The history hypothesis has NO removal witness (PKT-192): on every
; non-history record list tried here the conclusion still holds, so these
; are slack witnesses, labelled apart, not teeth.  The proof reads the
; history only as the prefix's fn-sco-store-eventsp and the records'
; true-listp; a record that is not fn-store-event-p is absorbed alike by the
; prefix's capture and the whole capture.  A weakened statement without the
; hypothesis did not prove in 48 s (2026-09-29); failed search is not a
; counterexample, so the hypothesis stays and is reported untoothed.
(defmacro ock-t-next-is-capture (prefix records)
  `(equal (fn-ock-next-checkpoint (fn-sco-capture *ock-t-configs* ,prefix)
                                  *ock-t-configs* ,records)
          (fn-sco-capture *ock-t-configs* ,records)))
(assert-event (and (not (fn-sn-observed-historyp 8 *ock-t-improper*))
                   (ock-t-next-is-capture *ock-t-prefix* *ock-t-improper*)))
(assert-event (and (not (fn-sn-observed-historyp 8 (append *ock-t-events* *ock-t-events*)))
                   (ock-t-next-is-capture *ock-t-events*
                                          (append *ock-t-events* *ock-t-events*))))
(assert-event
 (let ((bad (update-nth 1 -1 (car *ock-t-events*))))
   (and (not (fn-store-event-p bad))
        (ock-t-next-is-capture (list bad) (cons bad *ock-t-events*)))))
