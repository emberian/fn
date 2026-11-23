; Eleven live semantic checkers (EXECUTION-MODEL.md 10, ROUND2 F.1).
; Missing evidence and invalid states are never passing results.
(in-package "ACL2")
(include-book "../books/assembly")
(include-book "check-core")
(include-book "check-trace")
(include-book "check-work")
(include-book "check-account")
(include-book "check-fair")
(include-book "check-history")
(include-book "check-identity")
(include-book "check-wire")
(include-book "check-consumer")
(include-book "check-recovery")
(include-book "check-reclaim")

(defconst *fn2-checker-names*
  '(:trace :work :own :account :fair :history :identity :wire :consumer :recovery :reclaim))

(defun fn2-checker-namep (name)
  (declare (xargs :guard t))
  (if (member-eq name *fn2-checker-names*) t nil))

(defun fn2-check-resultp (result)
  (declare (xargs :guard t))
  (or (eq result :pass)
      (and (consp result) (eq (car result) :fail) (consp (cdr result)))))

(defthm fn2-check-resultp-pass
  (fn2-check-resultp :pass))

(defthm fn2-check-resultp-fail
  (implies (consp rest)
           (fn2-check-resultp (cons :fail rest))))

(defthm fn2-check-resultp-never-not-yet
  (implies (fn2-check-resultp result)
           (not (equal result :not-yet))))

(defthm fn2-fair-resultp-implies-check-resultp
  (implies (fn2-fair-resultp result)
           (fn2-check-resultp result))
  :hints (("Goal" :in-theory (enable fn2-fair-resultp))))

(in-theory (disable fn2-check-resultp))

;; ---------------------------------------------------------------------------
;; Return-shape lemmas for underlying check-*.lisp entrypoints.

(local
 (defthm fn2-wire-walk-resultp
   (fn2-check-resultp (fn2-wire-walk wire lines cut closed index done fuel))
   :hints (("Goal" :induct (fn2-wire-walk wire lines cut closed index done fuel)
            :in-theory (disable fn2-wire-take-line fn2-wire-code fn2-wire-lines
                                fn2-wire-body fn2-wire-malformed-p fn2-wire-admits-p
                                fn2-wire-multiline-p fn2-wire-next-lines
                                fn2-wire-entry-keyword)))))

(defthm fn2-wire-check-resultp
  (fn2-check-resultp (fn2-wire-check client wire closed))
  :hints (("Goal" :in-theory (disable fn2-wire-walk fn2-wire-take-line
                                      fn2-wire-code fn2-wire-lines))))

(local
 (defthm fn2-acct-check-rows-resultp
   (fn2-check-resultp (fn2-acct-check-rows rows records))
   :hints (("Goal" :induct (fn2-acct-check-rows rows records)
            :in-theory (disable fn2-acct-totals nth nfix)))))

(defthm fn2-account-check-resultp
  (fn2-check-resultp (fn2-account-check rows records capacity))
  :hints (("Goal" :in-theory (disable fn2-acct-check-rows fn2-acct-sum-committed))))

(local
 (defthm fn2-cnsk-run-resultp
   (fn2-check-resultp (fn2-cnsk-run obs i conns cands interims))
   :hints (("Goal" :induct (fn2-cnsk-run obs i conns cands interims)
            :in-theory (disable fn2-cnsk-request fn2-cnsk-decode-reply fn2-cnsk-reply-keep
                                fn2-cnsk-boundary fn2-cnsk-world fn2-cnsk-publish
                                fn2-cnsk-ledger fn2-cnsk-settle fn2-cnsk-close-conn
                                fn2-cnsk-close-all fn2-cnsk-add fn2-cnsk-entry-somewhere
                                fn2-cnsk-due-wait fn2-cnsk-cursor-rows fn2-cns-get
                                nth len nfix assoc-equal put-assoc-equal
                                remove1-equal remove-duplicates-equal strip-cars member-eq)))))

(defthm fn2-consumer-check-resultp
  (fn2-check-resultp (fn2-consumer-check obs history incarnation interims))
  :hints (("Goal" :in-theory (disable fn2-cnsk-run fn2-cns-model-init))))

(defthm fn2-check-own-resultp
  (fn2-check-resultp (fn2-check-own fn2-core fn2-own))
  :hints (("Goal" :in-theory (disable fn2-pool-semanticp fn2-own-ranges-p
                                      fn2-own-output-digests-p))))

(defthm fn2-check-work-resultp
  (fn2-check-resultp (fn2-check-work records lost nobs nvisits nactions profile))
  :hints (("Goal" :in-theory (disable fn2-work-certificate fn2-work-records-p fn2-profilep))))

(defthm fn2-check-work-visible-resultp
  (fn2-check-resultp (fn2-check-work-visible records lost nobs nvisits nactions profile visible))
  :hints (("Goal" :in-theory (disable fn2-check-work fn2-work-certificate fn2-work-byte-charge))))

;; ---------------------------------------------------------------------------
;; Per-checker adapters.

(defun fn2-check-fair-core (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core)))
             (answer)
             (fn2-check-fair-sched fn2-sched)
             answer))

(defthm fn2-check-fair-core-resultp
  (fn2-check-resultp (fn2-check-fair-core fn2-core))
  :hints (("Goal" :in-theory (disable fn2-check-fair-sched))))

(defun fn2-check-fair-evidence (evidence fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core)))
             (answer)
             (fn2-check-fair-sched-with-evidence evidence fn2-sched)
             answer))

(defun fn2-trace-verdict (lost selection before after)
  (declare (xargs :guard t))
  (let ((difference (fn2-trace-classify lost selection before after)))
    (if difference (list :fail :trace difference) :pass)))

(defthm fn2-trace-verdict-resultp
  (fn2-check-resultp (fn2-trace-verdict lost selection before after)))

(defun fn2-check-trace-core (expected-selections before after fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-trace (fn2-core-trace fn2-core)))
             (answer)
             (fn2-trace-verdict (fn2-trace-lost fn2-trace)
                                (fn2-trace-selection-difference
                                 (fn2-trace-selections (fn2-trace-records fn2-trace))
                                 expected-selections)
                                before after)
             answer))

(defun fn2-check-trace-evidence (evidence fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((not (true-listp evidence)) '(:fail :trace-bad-evidence))
        ((eq (car evidence) :classify)
         (if (= (len evidence) 5)
             (fn2-trace-verdict (nth 1 evidence) (nth 2 evidence)
                                (nth 3 evidence) (nth 4 evidence))
           '(:fail :trace-bad-evidence)))
        ((eq (car evidence) :records)
         (cond ((= (len evidence) 4)
                (fn2-trace-verdict (nth 2 evidence)
                                   (fn2-trace-selection-difference
                                    (fn2-trace-selections (nth 1 evidence)) (nth 3 evidence))
                                   nil nil))
               ((= (len evidence) 6)
                (fn2-trace-verdict (nth 2 evidence)
                                   (fn2-trace-selection-difference
                                    (fn2-trace-selections (nth 1 evidence)) (nth 3 evidence))
                                   (nth 4 evidence) (nth 5 evidence)))
               (t '(:fail :trace-bad-evidence))))
        ((eq (car evidence) :core)
         (cond ((= (len evidence) 2)
                (fn2-check-trace-core (nth 1 evidence) nil nil fn2-core))
               ((= (len evidence) 4)
                (fn2-check-trace-core (nth 1 evidence) (nth 2 evidence) (nth 3 evidence) fn2-core))
               (t '(:fail :trace-bad-evidence))))
        ((and (not (keywordp (car evidence))) (= (len evidence) 4))
         (fn2-trace-verdict (nth 0 evidence) (nth 1 evidence)
                            (nth 2 evidence) (nth 3 evidence)))
        (t '(:fail :trace-bad-evidence))))

(defun fn2-check-work-core (nobs nvisits nactions profile visible-p visible fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-trace (fn2-core-trace fn2-core)))
             (answer)
             (if (fn2-trace-wfp fn2-trace)
                 (let ((records (fn2-trace-records fn2-trace))
                       (lost (fn2-trace-lost fn2-trace)))
                   (if visible-p
                       (fn2-check-work-visible records lost nobs nvisits nactions profile visible)
                     (fn2-check-work records lost nobs nvisits nactions profile)))
               '(:fail :work-bad-trace-state))
             answer))

(defun fn2-check-work-evidence (evidence fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((not (true-listp evidence)) '(:fail :work-bad-evidence))
        ((eq (car evidence) :work)
         (if (= (len evidence) 7)
             (fn2-check-work (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)
                             (nth 4 evidence) (nth 5 evidence) (nth 6 evidence))
           '(:fail :work-bad-evidence)))
        ((eq (car evidence) :visible)
         (if (= (len evidence) 8)
             (fn2-check-work-visible (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)
                                     (nth 4 evidence) (nth 5 evidence) (nth 6 evidence)
                                     (nth 7 evidence))
           '(:fail :work-bad-evidence)))
        ((eq (car evidence) :core)
         (if (= (len evidence) 5)
             (fn2-check-work-core (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)
                                  (nth 4 evidence) nil nil fn2-core)
           '(:fail :work-bad-evidence)))
        ((eq (car evidence) :core-visible)
         (if (= (len evidence) 6)
             (fn2-check-work-core (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)
                                  (nth 4 evidence) t (nth 5 evidence) fn2-core)
           '(:fail :work-bad-evidence)))
        ((and (not (and (symbolp (car evidence)) (keywordp (car evidence))))
              (= (len evidence) 6))
         (fn2-check-work (nth 0 evidence) (nth 1 evidence) (nth 2 evidence)
                         (nth 3 evidence) (nth 4 evidence) (nth 5 evidence)))
        ((and (not (and (symbolp (car evidence)) (keywordp (car evidence))))
              (= (len evidence) 7))
         (fn2-check-work-visible (nth 0 evidence) (nth 1 evidence) (nth 2 evidence)
                                 (nth 3 evidence) (nth 4 evidence) (nth 5 evidence)
                                 (nth 6 evidence)))
        (t '(:fail :work-bad-evidence))))

(defun fn2-check-account-core-rows (p n fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix (- (nfix n) (nfix p)))))
  (if (or (not (natp p)) (not (natp n)) (>= p n)) nil
    (let ((d (fn2-account-holding :connection-row)))
      (cons (list p (fn2-account-core-limit p d fn2-core)
                  (fn2-account-core-reserve p d fn2-core)
                  (fn2-account-core-hold p d fn2-core)
                  (fn2-account-core-charged p *fn2-account-charge-rx* fn2-core)
                  (fn2-account-core-charged p *fn2-account-charge-tx* fn2-core)
                  (fn2-account-core-charged p *fn2-account-charge-requests* fn2-core)
                  (fn2-listener-bookings p fn2-core))
            (fn2-check-account-core-rows (+ 1 p) n fn2-core)))))

(defun fn2-check-account-evidence (evidence fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (cond ((null evidence)
         (if (fn2-account-core-conservedp fn2-core)
             '(:fail :checker-evidence-required)
           '(:fail :ledger-not-conserved)))
        ((not (true-listp evidence)) '(:fail :account-bad-evidence))
        ((eq (car evidence) :account)
         (if (= (len evidence) 4)
             (fn2-account-check (nth 1 evidence) (nth 2 evidence) (nth 3 evidence))
           '(:fail :account-bad-evidence)))
        ((eq (car evidence) :core)
         (if (= (len evidence) 3)
             (if (not (fn2-account-core-conservedp fn2-core))
                 '(:fail :ledger-not-conserved)
               (fn2-account-check
                (fn2-check-account-core-rows 0 (fn2-account-core-rows fn2-core) fn2-core)
                (nth 1 evidence) (nth 2 evidence)))
           '(:fail :account-bad-evidence)))
        ((and (not (keywordp (car evidence))) (= (len evidence) 3))
         (fn2-account-check (nth 0 evidence) (nth 1 evidence) (nth 2 evidence)))
        (t '(:fail :account-bad-evidence))))

(defun fn2-check-history-verdict (events profile classification recovered)
  (declare (xargs :verify-guards nil))
  (if (fn2-check-history events profile classification recovered)
      :pass
    '(:fail :history)))

(defun fn2-check-history-evidence (evidence)
  (declare (xargs :verify-guards nil))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((not (true-listp evidence)) '(:fail :history-bad-evidence))
        ((eq (car evidence) :history)
         (if (= (len evidence) 5)
             (fn2-check-history-verdict (nth 1 evidence) (nth 2 evidence)
                                        (nth 3 evidence) (nth 4 evidence))
           '(:fail :history-bad-evidence)))
        ((and (not (keywordp (car evidence))) (= (len evidence) 4))
         (fn2-check-history-verdict (nth 0 evidence) (nth 1 evidence)
                                    (nth 2 evidence) (nth 3 evidence)))
        (t '(:fail :history-bad-evidence))))

(defun fn2-check-identity-verdict (events)
  (declare (xargs :guard t))
  (let ((res (fn2-check-identity events)))
    (if (and (consp res) (eq (car res) :ok))
        :pass
      (list :fail :identity res))))

(defun fn2-check-identity-evidence (evidence)
  (declare (xargs :guard t))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((not (true-listp evidence)) '(:fail :identity-bad-evidence))
        ((member-eq (car evidence) '(:identity :events))
         (if (= (len evidence) 2)
             (fn2-check-identity-verdict (nth 1 evidence))
           '(:fail :identity-bad-evidence)))
        ((consp (car evidence))
         (fn2-check-identity-verdict evidence))
        (t '(:fail :identity-bad-evidence))))

(defun fn2-check-wire-connections (conns)
  (declare (xargs :verify-guards nil))
  (if (atom conns)
      (if (null conns) :pass '(:fail :wire-bad-evidence))
    (let ((c (car conns)))
      (if (and (true-listp c) (= (len c) 3))
          (let ((v (fn2-wire-check (nth 0 c) (nth 1 c) (nth 2 c))))
            (if (eq v :pass)
                (fn2-check-wire-connections (cdr conns))
              v))
        '(:fail :wire-bad-evidence)))))

(defun fn2-check-wire-evidence (evidence)
  (declare (xargs :verify-guards nil))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((not (true-listp evidence)) '(:fail :wire-bad-evidence))
        ((eq (car evidence) :wire)
         (if (= (len evidence) 4)
             (fn2-wire-check (nth 1 evidence) (nth 2 evidence) (nth 3 evidence))
           '(:fail :wire-bad-evidence)))
        ((eq (car evidence) :connections)
         (if (and (= (len evidence) 2) (true-listp (nth 1 evidence)))
             (fn2-check-wire-connections (nth 1 evidence))
           '(:fail :wire-bad-evidence)))
        ((and (not (keywordp (car evidence))) (= (len evidence) 3))
         (fn2-wire-check (nth 0 evidence) (nth 1 evidence) (nth 2 evidence)))
        (t '(:fail :wire-bad-evidence))))

(defun fn2-check-consumer-evidence (evidence)
  (declare (xargs :verify-guards nil))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((not (true-listp evidence)) '(:fail :consumer-bad-evidence))
        ((eq (car evidence) :consumer)
         (if (= (len evidence) 5)
             (fn2-consumer-check (nth 1 evidence) (nth 2 evidence)
                                 (nth 3 evidence) (nth 4 evidence))
           '(:fail :consumer-bad-evidence)))
        ((and (not (keywordp (car evidence))) (= (len evidence) 4))
         (fn2-consumer-check (nth 0 evidence) (nth 1 evidence)
                             (nth 2 evidence) (nth 3 evidence)))
        (t '(:fail :consumer-bad-evidence))))

(defun fn2-check-recovery-verdict (events profile classification recovered outcome)
  (declare (xargs :verify-guards nil))
  (if (fn2-check-recovery events profile classification recovered outcome)
      :pass
    '(:fail :recovery)))

(defun fn2-check-recovery-evidence (evidence)
  (declare (xargs :verify-guards nil))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((not (true-listp evidence)) '(:fail :recovery-bad-evidence))
        ((eq (car evidence) :recovery)
         (if (= (len evidence) 6)
             (fn2-check-recovery-verdict (nth 1 evidence) (nth 2 evidence)
                                         (nth 3 evidence) (nth 4 evidence)
                                         (nth 5 evidence))
           '(:fail :recovery-bad-evidence)))
        ((and (not (keywordp (car evidence))) (= (len evidence) 5))
         (fn2-check-recovery-verdict (nth 0 evidence) (nth 1 evidence)
                                     (nth 2 evidence) (nth 3 evidence)
                                     (nth 4 evidence)))
        (t '(:fail :recovery-bad-evidence))))

(defun fn2-check-reclaim-verdict (events)
  (declare (xargs :guard t))
  (let ((res (fn2-check-reclaim events)))
    (if (null res)
        :pass
      (list :fail :reclaim res))))

(defun fn2-check-reclaim-evidence (evidence)
  (declare (xargs :guard t))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((not (true-listp evidence)) '(:fail :reclaim-bad-evidence))
        ((member-eq (car evidence) '(:reclaim :events))
         (if (= (len evidence) 2)
             (fn2-check-reclaim-verdict (nth 1 evidence))
           '(:fail :reclaim-bad-evidence)))
        ((consp (car evidence))
         (fn2-check-reclaim-verdict evidence))
        (t '(:fail :reclaim-bad-evidence))))

;; ---------------------------------------------------------------------------
;; Unified entrypoints: 4-arg evidence-aware and 3-arg live-core compatible.

(defun fn2-check-with-evidence (name evidence fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil))
  (case name
    (:trace (fn2-check-trace-evidence evidence fn2-core))
    (:work (fn2-check-work-evidence evidence fn2-core))
    (:own (fn2-check-own fn2-core fn2-own))
    (:account (fn2-check-account-evidence evidence fn2-core))
    (:fair (fn2-check-fair-evidence evidence fn2-core))
    (:history (fn2-check-history-evidence evidence))
    (:identity (fn2-check-identity-evidence evidence))
    (:wire (fn2-check-wire-evidence evidence))
    (:consumer (fn2-check-consumer-evidence evidence))
    (:recovery (fn2-check-recovery-evidence evidence))
    (:reclaim (fn2-check-reclaim-evidence evidence))
    (otherwise '(:fail :unknown-checker))))

(defun fn2-check (name fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil))
  (fn2-check-with-evidence name nil fn2-core fn2-own))

;; ---------------------------------------------------------------------------
;; Return-shape, anti-stub, and compatibility theorems.

(local
 (defthm fn2-check-wire-connections-resultp
   (fn2-check-resultp (fn2-check-wire-connections conns))
   :hints (("Goal" :induct (fn2-check-wire-connections conns)
            :in-theory (disable fn2-wire-check nth len)))))

(local
 (defthm fn2-check-trace-evidence-resultp
   (fn2-check-resultp (fn2-check-trace-evidence evidence fn2-core))
   :hints (("Goal" :in-theory (disable fn2-trace-verdict fn2-trace-selections
                                       fn2-trace-selection-difference
                                       fn2-trace-records fn2-trace-lost nth len)))))

(local
 (defthm fn2-check-work-evidence-resultp
   (fn2-check-resultp (fn2-check-work-evidence evidence fn2-core))
   :hints (("Goal" :in-theory (disable fn2-check-work fn2-check-work-visible
                                       fn2-trace-records fn2-trace-lost
                                       keywordp member-eq nth len)))))

(local
 (defthm fn2-check-account-evidence-resultp
   (fn2-check-resultp (fn2-check-account-evidence evidence fn2-core))
   :hints (("Goal" :in-theory (disable fn2-account-check fn2-account-core-conservedp
                                       fn2-check-account-core-rows fn2-account-core-rows
                                       keywordp nth len)))))

(local
 (defthm fn2-check-fair-evidence-resultp
   (fn2-check-resultp (fn2-check-fair-evidence evidence fn2-core))
   :hints (("Goal" :in-theory (disable fn2-check-fair-sched-with-evidence)))))

(local
 (defthm fn2-check-history-evidence-resultp
   (fn2-check-resultp (fn2-check-history-evidence evidence))
   :hints (("Goal" :in-theory (disable fn2-check-history keywordp nth len)))))

(local
 (defthm fn2-check-identity-evidence-resultp
   (fn2-check-resultp (fn2-check-identity-evidence evidence))
   :hints (("Goal" :in-theory (disable fn2-check-identity member-eq nth len)))))

(local
 (defthm fn2-check-wire-evidence-resultp
   (fn2-check-resultp (fn2-check-wire-evidence evidence))
   :hints (("Goal" :in-theory (disable fn2-wire-check fn2-check-wire-connections
                                       keywordp nth len)))))

(local
 (defthm fn2-check-consumer-evidence-resultp
   (fn2-check-resultp (fn2-check-consumer-evidence evidence))
   :hints (("Goal" :in-theory (disable fn2-consumer-check keywordp nth len)))))

(local
 (defthm fn2-check-recovery-evidence-resultp
   (fn2-check-resultp (fn2-check-recovery-evidence evidence))
   :hints (("Goal" :in-theory (disable fn2-check-recovery keywordp nth len)))))

(local
 (defthm fn2-check-reclaim-evidence-resultp
   (fn2-check-resultp (fn2-check-reclaim-evidence evidence))
   :hints (("Goal" :in-theory (disable fn2-check-reclaim member-eq nth len)))))

(defthm fn2-check-with-evidence-returns-resultp
  (fn2-check-resultp (fn2-check-with-evidence name evidence fn2-core fn2-own))
  :hints (("Goal" :in-theory (disable fn2-check-trace-evidence fn2-check-work-evidence
                                      fn2-check-own fn2-check-account-evidence
                                      fn2-check-fair-evidence fn2-check-history-evidence
                                      fn2-check-identity-evidence fn2-check-wire-evidence
                                      fn2-check-consumer-evidence fn2-check-recovery-evidence
                                      fn2-check-reclaim-evidence))))

(defthm fn2-check-returns-resultp
  (fn2-check-resultp (fn2-check name fn2-core fn2-own))
  :hints (("Goal" :in-theory (disable fn2-check-with-evidence))))

(defthm fn2-check-with-evidence-never-not-yet
  (not (equal (fn2-check-with-evidence name evidence fn2-core fn2-own) :not-yet))
  :hints (("Goal" :in-theory (disable fn2-check-with-evidence)
           :use fn2-check-with-evidence-returns-resultp)))

(defthm fn2-check-never-not-yet
  (not (equal (fn2-check name fn2-core fn2-own) :not-yet))
  :hints (("Goal" :in-theory (disable fn2-check)
           :use fn2-check-returns-resultp)))

(defthm fn2-check-equals-with-evidence-nil
  (equal (fn2-check name fn2-core fn2-own)
         (fn2-check-with-evidence name nil fn2-core fn2-own)))

(defthm fn2-check-unknown-fails
  (implies (not (fn2-checker-namep name))
           (equal (fn2-check-with-evidence name evidence fn2-core fn2-own)
                  '(:fail :unknown-checker)))
  :hints (("Goal" :in-theory (disable fn2-check-trace-evidence fn2-check-work-evidence
                                      fn2-check-own fn2-check-account-evidence
                                      fn2-check-fair-evidence fn2-check-history-evidence
                                      fn2-check-identity-evidence fn2-check-wire-evidence
                                      fn2-check-consumer-evidence fn2-check-recovery-evidence
                                      fn2-check-reclaim-evidence))))

;; ---------------------------------------------------------------------------
;; Soundness bridge theorems connecting :pass on every arm to its underlying
;; check-*.lisp semantic predicate.

(defthm fn2-check-own-sound
  (implies (equal (fn2-check-with-evidence :own evidence fn2-core fn2-own) :pass)
           (and (equal (fn2-check-own fn2-core fn2-own) :pass)
                (eq (fn2-own-status fn2-own) :pass)
                (fn2-pool-semanticp (fn2-core-pool fn2-core))
                (fn2-own-ranges-p (fn2-ops-rows (fn2-core-ops fn2-core))
                                  (fn2-core-pool fn2-core) (fn2-core-ops fn2-core))
                (fn2-own-output-digests-p (fn2-ops-rows (fn2-core-ops fn2-core))
                                          (fn2-core-pool fn2-core) (fn2-core-ops fn2-core) fn2-own)))
  :hints (("Goal" :in-theory (disable fn2-own-status fn2-pool-semanticp
                                      fn2-own-ranges-p fn2-own-output-digests-p))))

(defthm fn2-check-fair-core-sound
  (implies (and (fn2-schedp (fn2-core-sched fn2-core))
                (equal (fn2-check :fair fn2-core fn2-own) :pass)
                (fn2-sched-principalp principal (fn2-core-sched fn2-core)))
           (mv-nth 0 (fn2-sched-visits-principal
                      (fn2-sched-calendar-length (fn2-core-sched fn2-core))
                      principal (fn2-core-sched fn2-core))))
  :hints (("Goal" :in-theory (disable fn2-check-fair-sched fn2-sched-visits-principal
                                      fn2-sched-calendar-length))))

(defthm fn2-check-fair-profile-sound
  (implies (and (fn2-schedp (fn2-core-sched fn2-core))
                (equal (fn2-check-with-evidence :fair (list :profile profile) fn2-core fn2-own) :pass))
           (and (equal (fn2-check-fair-sched (fn2-core-sched fn2-core)) :pass)
                (equal (fn2-fair-sched-weights (fn2-core-sched fn2-core))
                       (fn2-profile-weights profile))))
  :hints (("Goal" :in-theory (disable fn2-check-fair-sched fn2-fair-sched-weights fn2-profile-weights))))

(defthm fn2-check-fair-trace-sound
  (implies (equal (fn2-check-with-evidence :fair (list :trace events bound drainp) fn2-core fn2-own) :pass)
           (and (posp bound)
                (fn2-fair-trace-bounded-p events nil bound drainp)))
  :hints (("Goal" :in-theory (disable fn2-fair-trace-check fn2-fair-trace-bounded-p))))

(defthm fn2-check-fair-deadlock-sound
  (implies (equal (fn2-check-with-evidence :fair (list :deadlock threads capacities retained) fn2-core fn2-own) :pass)
           (let ((res (fn2-pv-check-retained threads capacities retained)))
             (and (eq (cdr (assoc-eq :status res)) :ok)
                  (equal (cdr (assoc-eq :deadlocks res)) 0))))
  :hints (("Goal" :in-theory (disable fn2-fair-deadlock-check fn2-pv-check-retained))))

(defthm fn2-check-trace-classify-sound
  (implies (equal (fn2-check-with-evidence :trace (list :classify lost selection before after) fn2-core fn2-own) :pass)
           (not (fn2-trace-classify lost selection before after)))
  :hints (("Goal" :in-theory (disable fn2-trace-classify))))

(defthm fn2-check-trace-records-sound
  (implies (equal (fn2-check-with-evidence :trace (list :records records lost expected before after) fn2-core fn2-own) :pass)
           (not (fn2-trace-classify
                 lost
                 (fn2-trace-selection-difference (fn2-trace-selections records) expected)
                 before after)))
  :hints (("Goal" :in-theory (disable fn2-trace-classify fn2-trace-selections
                                      fn2-trace-selection-difference))))

(defthm fn2-check-trace-core-sound
  (implies (equal (fn2-check-with-evidence :trace (list :core expected before after) fn2-core fn2-own) :pass)
           (not (fn2-trace-classify
                 (fn2-trace-lost (fn2-core-trace fn2-core))
                 (fn2-trace-selection-difference
                  (fn2-trace-selections (fn2-trace-records (fn2-core-trace fn2-core)))
                  expected)
                 before after)))
  :hints (("Goal" :in-theory (disable fn2-trace-classify fn2-trace-selections
                                      fn2-trace-selection-difference
                                      fn2-trace-records fn2-trace-lost))))

(defthm fn2-check-work-sound
  (implies (equal (fn2-check-with-evidence :work (list :work records lost nobs nvisits nactions profile) fn2-core fn2-own) :pass)
           (equal (fn2-check-work records lost nobs nvisits nactions profile) :pass))
  :hints (("Goal" :in-theory (disable fn2-check-work))))

(defthm fn2-check-work-visible-sound
  (implies (equal (fn2-check-with-evidence :work (list :visible records lost nobs nvisits nactions profile visible) fn2-core fn2-own) :pass)
           (equal (fn2-check-work-visible records lost nobs nvisits nactions profile visible) :pass))
  :hints (("Goal" :in-theory (disable fn2-check-work-visible))))

(defthm fn2-check-work-core-sound
  (implies (and (fn2-core-wfp fn2-core)
                (fn2-trace-wfp (fn2-core-trace fn2-core))
                (equal (fn2-check-with-evidence :work (list :core nobs nvisits nactions profile) fn2-core fn2-own) :pass))
           (equal (fn2-check-work (fn2-trace-records (fn2-core-trace fn2-core))
                                  (fn2-trace-lost (fn2-core-trace fn2-core))
                                  nobs nvisits nactions profile)
                  :pass))
  :hints (("Goal" :in-theory (disable fn2-check-work fn2-trace-records fn2-trace-lost))))

(defthm fn2-check-work-core-visible-sound
  (implies (and (fn2-core-wfp fn2-core)
                (fn2-trace-wfp (fn2-core-trace fn2-core))
                (equal (fn2-check-with-evidence :work (list :core-visible nobs nvisits nactions profile visible) fn2-core fn2-own) :pass))
           (equal (fn2-check-work-visible (fn2-trace-records (fn2-core-trace fn2-core))
                                          (fn2-trace-lost (fn2-core-trace fn2-core))
                                          nobs nvisits nactions profile visible)
                  :pass))
  :hints (("Goal" :in-theory (disable fn2-check-work-visible fn2-trace-records fn2-trace-lost))))

(defthm fn2-check-account-sound
  (implies (equal (fn2-check-with-evidence :account (list :account rows records capacity) fn2-core fn2-own) :pass)
           (equal (fn2-account-check rows records capacity) :pass))
  :hints (("Goal" :in-theory (disable fn2-account-check))))

(defthm fn2-check-account-core-sound
  (implies (equal (fn2-check-with-evidence :account (list :core records capacity) fn2-core fn2-own) :pass)
           (and (fn2-account-core-conservedp fn2-core)
                (equal (fn2-account-check
                        (fn2-check-account-core-rows 0 (fn2-account-core-rows fn2-core) fn2-core)
                        records capacity)
                       :pass)))
  :hints (("Goal" :in-theory (disable fn2-account-check fn2-account-core-conservedp
                                      fn2-check-account-core-rows fn2-account-core-rows))))

(defthm fn2-check-history-sound
  (implies (equal (fn2-check-with-evidence :history (list :history events profile classification recovered) fn2-core fn2-own) :pass)
           (fn2-check-history events profile classification recovered))
  :hints (("Goal" :in-theory (disable fn2-check-history))))

(defthm fn2-check-identity-sound
  (implies (equal (fn2-check-with-evidence :identity (list :identity events) fn2-core fn2-own) :pass)
           (and (consp (fn2-check-identity events))
                (eq (car (fn2-check-identity events)) :ok)))
  :hints (("Goal" :in-theory (disable fn2-check-identity))))

(defthm fn2-check-wire-sound
  (implies (equal (fn2-check-with-evidence :wire (list :wire client wire closed) fn2-core fn2-own) :pass)
           (fn2-wire-pass-p client wire closed))
  :hints (("Goal" :in-theory (disable fn2-wire-check))))

(defun fn2-wire-connections-pass-p (conns)
  (declare (xargs :verify-guards nil))
  (if (atom conns)
      (null conns)
    (let ((c (car conns)))
      (and (true-listp c) (= (len c) 3)
           (fn2-wire-pass-p (nth 0 c) (nth 1 c) (nth 2 c))
           (fn2-wire-connections-pass-p (cdr conns))))))

(local
 (defthm fn2-check-wire-connections-iff
   (implies (true-listp conns)
            (iff (equal (fn2-check-wire-connections conns) :pass)
                 (fn2-wire-connections-pass-p conns)))
   :hints (("Goal" :induct (fn2-check-wire-connections conns)
            :in-theory (e/d (fn2-wire-pass-p) (fn2-wire-check nth len))))))

(defthm fn2-check-wire-connections-sound
  (implies (true-listp conns)
           (iff (equal (fn2-check-with-evidence :wire (list :connections conns) fn2-core fn2-own) :pass)
                (fn2-wire-connections-pass-p conns)))
  :hints (("Goal" :in-theory (disable fn2-wire-check fn2-wire-pass-p fn2-check-wire-connections))))

(defthm fn2-check-consumer-sound
  (implies (equal (fn2-check-with-evidence :consumer (list :consumer obs history incarnation interims) fn2-core fn2-own) :pass)
           (equal (fn2-consumer-check obs history incarnation interims) :pass))
  :hints (("Goal" :in-theory (disable fn2-consumer-check))))

(defthm fn2-check-recovery-sound
  (implies (equal (fn2-check-with-evidence :recovery (list :recovery events profile classification recovered outcome) fn2-core fn2-own) :pass)
           (fn2-check-recovery events profile classification recovered outcome))
  :hints (("Goal" :in-theory (disable fn2-check-recovery))))

(defthm fn2-check-reclaim-sound
  (implies (equal (fn2-check-with-evidence :reclaim (list :reclaim events) fn2-core fn2-own) :pass)
           (null (fn2-check-reclaim events)))
  :hints (("Goal" :in-theory (disable fn2-check-reclaim))))

;; ---------------------------------------------------------------------------
;; Structural assertions & compliance.

(assert-event (and (= (len *fn2-checker-names*) 11)
                   (no-duplicatesp-eq *fn2-checker-names*)
                   (fn2-check-resultp :pass)
                   (not (fn2-check-resultp :not-yet))
                   (fn2-check-resultp '(:fail :example))
                   (not (fn2-check-resultp nil))))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-checker-namep fn2-check-resultp fn2-check-fair-core fn2-trace-verdict
    fn2-check-work-core fn2-check-work-evidence
    fn2-check-identity-verdict fn2-check-identity-evidence
    fn2-check-reclaim-verdict fn2-check-reclaim-evidence
    fn2-own-observe-issue fn2-own-observe-output fn2-own-record-input-byte
    fn2-own-observe-read fn2-own-observe-core-write)
  (w state)))

; TRACE needs a pre-turn reference copy: call fn2-check-trace-turn.
