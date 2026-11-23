; Eleven live semantic checkers (EXECUTION-MODEL.md rule 10).
; Missing evidence, malformed inputs, and invalid states are never passing results.
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

(local (defthm fn2-wire-walk-resultp
         (fn2-check-resultp (fn2-wire-walk wire lines cut closed index done fuel))
         :hints (("Goal" :induct (fn2-wire-walk wire lines cut closed index done fuel)
                  :in-theory (disable fn2-wire-take-line fn2-wire-code fn2-wire-lines
                                      fn2-wire-body fn2-wire-malformed-p fn2-wire-admits-p
                                      fn2-wire-multiline-p fn2-wire-next-lines fn2-wire-entry-keyword)))))

(defthm fn2-wire-check-resultp
  (fn2-check-resultp (fn2-wire-check client wire closed))
  :hints (("Goal" :in-theory (disable fn2-wire-walk fn2-wire-take-line fn2-wire-code fn2-wire-lines))))

(local (defthm fn2-acct-check-rows-resultp
         (fn2-check-resultp (fn2-acct-check-rows rows records))
         :hints (("Goal" :induct (fn2-acct-check-rows rows records)
                  :in-theory (disable fn2-acct-totals nth nfix)))))

(defthm fn2-account-check-resultp
  (fn2-check-resultp (fn2-account-check rows records capacity))
  :hints (("Goal" :in-theory (disable fn2-acct-check-rows fn2-acct-sum-committed))))

(local (defthm fn2-cnsk-run-resultp
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
  :hints (("Goal" :in-theory (disable fn2-pool-semanticp fn2-own-ranges-p fn2-own-output-digests-p))))

(defthm fn2-check-work-resultp
  (fn2-check-resultp (fn2-check-work records lost nobs nvisits nactions profile))
  :hints (("Goal" :in-theory (disable fn2-work-certificate fn2-work-records-p fn2-profilep))))

(defthm fn2-check-work-visible-resultp
  (fn2-check-resultp (fn2-check-work-visible records lost nobs nvisits nactions profile visible))
  :hints (("Goal" :in-theory (disable fn2-check-work fn2-work-certificate fn2-work-byte-charge))))

;; ---------------------------------------------------------------------------
;; Per-checker adapters (strict list/type validation, zero caller-verdict bypass).

(defun fn2-check-own-evidence (evidence fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil))
  (if (or (null evidence) (eq evidence :core))
      (fn2-check-own fn2-core fn2-own)
    '(:fail :own-bad-evidence)))

(defun fn2-check-fair-core (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core)))
             (answer)
             (fn2-check-fair-sched fn2-sched)
             answer))

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
             (if (fn2-trace-wfp fn2-trace)
                 (fn2-trace-verdict (fn2-trace-lost fn2-trace)
                                    (fn2-trace-selection-difference
                                     (fn2-trace-selections (fn2-trace-records fn2-trace))
                                     expected-selections)
                                    before after)
               '(:fail :trace-bad-core-state))
             answer))

(defun fn2-check-trace-evidence (evidence fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((not (true-listp evidence)) '(:fail :trace-bad-evidence))
        ((and (eq (car evidence) :records) (= (len evidence) 6)
              (true-listp (nth 1 evidence)) (true-listp (nth 3 evidence)))
         (fn2-trace-verdict (nth 2 evidence)
                            (fn2-trace-selection-difference
                             (fn2-trace-selections (nth 1 evidence)) (nth 3 evidence))
                            (nth 4 evidence) (nth 5 evidence)))
        ((and (eq (car evidence) :core) (= (len evidence) 4)
              (true-listp (nth 1 evidence)))
         (fn2-check-trace-core (nth 1 evidence) (nth 2 evidence) (nth 3 evidence) fn2-core))
        (t '(:fail :trace-bad-evidence))))

(defun fn2-work-visible-tuplep (v)
  (declare (xargs :guard t))
  (and (true-listp v) (= (len v) 4)
       (natp (nth 0 v)) (natp (nth 1 v)) (natp (nth 2 v)) (natp (nth 3 v))))

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
        ((and (eq (car evidence) :work) (= (len evidence) 7))
         (fn2-check-work (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)
                         (nth 4 evidence) (nth 5 evidence) (nth 6 evidence)))
        ((and (eq (car evidence) :visible) (= (len evidence) 8)
              (fn2-work-visible-tuplep (nth 7 evidence)))
         (fn2-check-work-visible (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)
                                 (nth 4 evidence) (nth 5 evidence) (nth 6 evidence) (nth 7 evidence)))
        ((and (eq (car evidence) :core) (= (len evidence) 5))
         (fn2-check-work-core (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)
                              (nth 4 evidence) nil nil fn2-core))
        ((and (eq (car evidence) :core-visible) (= (len evidence) 6)
              (fn2-work-visible-tuplep (nth 5 evidence)))
         (fn2-check-work-core (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)
                              (nth 4 evidence) t (nth 5 evidence) fn2-core))
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
        ((and (eq (car evidence) :account) (= (len evidence) 4)
              (true-listp (nth 1 evidence)) (true-listp (nth 2 evidence)) (natp (nth 3 evidence)))
         (fn2-account-check (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)))
        ((and (eq (car evidence) :core) (= (len evidence) 3)
              (true-listp (nth 1 evidence)) (natp (nth 2 evidence)))
         (if (not (fn2-account-core-conservedp fn2-core))
             '(:fail :ledger-not-conserved)
           (fn2-account-check
            (fn2-check-account-core-rows 0 (fn2-account-core-rows fn2-core) fn2-core)
            (nth 1 evidence) (nth 2 evidence))))
        (t '(:fail :account-bad-evidence))))

(defun fn2-check-history-evidence (evidence)
  (declare (xargs :verify-guards nil))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((and (true-listp evidence) (eq (car evidence) :history) (= (len evidence) 5)
              (true-listp (nth 1 evidence)))
         (if (fn2-check-history (nth 1 evidence) (nth 2 evidence) (nth 3 evidence) (nth 4 evidence))
             :pass
           (mv-let (code trace) (fn2-history-translate (nth 1 evidence))
             (declare (ignore trace))
             (list :fail :history (if (eq code :ok) :disallowed-recovery code)))))
        (t '(:fail :history-bad-evidence))))

(defun fn2-check-identity-evidence (evidence)
  (declare (xargs :guard t))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((and (true-listp evidence) (eq (car evidence) :identity) (= (len evidence) 2)
              (true-listp (nth 1 evidence)))
         (let ((res (fn2-check-identity (nth 1 evidence))))
           (if (and (consp res) (eq (car res) :ok)) :pass (list :fail :identity res))))
        (t '(:fail :identity-bad-evidence))))

(defun fn2-wire-conn-entryp (c)
  (declare (xargs :guard t))
  (and (true-listp c) (= (len c) 3)
       (true-listp (nth 0 c)) (true-listp (nth 1 c)) (booleanp (nth 2 c))))

(defun fn2-check-wire-connections (conns)
  (declare (xargs :verify-guards nil))
  (if (atom conns)
      (if (null conns) :pass '(:fail :wire-bad-evidence))
    (let ((c (car conns)))
      (if (fn2-wire-conn-entryp c)
          (let ((v (fn2-wire-check (nth 0 c) (nth 1 c) (nth 2 c))))
            (if (eq v :pass) (fn2-check-wire-connections (cdr conns)) v))
        '(:fail :wire-bad-evidence)))))

(defun fn2-check-wire-evidence (evidence)
  (declare (xargs :verify-guards nil))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((not (true-listp evidence)) '(:fail :wire-bad-evidence))
        ((and (eq (car evidence) :wire) (= (len evidence) 4)
              (true-listp (nth 1 evidence)) (true-listp (nth 2 evidence)) (booleanp (nth 3 evidence)))
         (fn2-wire-check (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)))
        ((and (eq (car evidence) :connections) (= (len evidence) 2) (true-listp (nth 1 evidence)))
         (fn2-check-wire-connections (nth 1 evidence)))
        (t '(:fail :wire-bad-evidence))))

(defun fn2-check-consumer-evidence (evidence)
  (declare (xargs :verify-guards nil))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((and (true-listp evidence) (eq (car evidence) :consumer) (= (len evidence) 5)
              (true-listp (nth 1 evidence)) (true-listp (nth 4 evidence)))
         (fn2-consumer-check (nth 1 evidence) (nth 2 evidence) (nth 3 evidence) (nth 4 evidence)))
        (t '(:fail :consumer-bad-evidence))))

(defun fn2-check-recovery-evidence (evidence)
  (declare (xargs :verify-guards nil))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((and (true-listp evidence) (eq (car evidence) :recovery) (= (len evidence) 6)
              (true-listp (nth 1 evidence)))
         (if (fn2-check-recovery (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)
                                 (nth 4 evidence) (nth 5 evidence))
             :pass
           (mv-let (code trace) (fn2-history-translate (nth 1 evidence))
             (declare (ignore trace))
             (list :fail :recovery (if (eq code :ok) :disallowed-recovery-or-witness code)))))
        (t '(:fail :recovery-bad-evidence))))

(defun fn2-check-reclaim-evidence (evidence)
  (declare (xargs :guard t))
  (cond ((null evidence) '(:fail :checker-evidence-required))
        ((and (true-listp evidence) (eq (car evidence) :reclaim) (= (len evidence) 2)
              (true-listp (nth 1 evidence)))
         (let ((res (fn2-check-reclaim (nth 1 evidence))))
           (if (null res) :pass (list :fail :reclaim res))))
        (t '(:fail :reclaim-bad-evidence))))

;; ---------------------------------------------------------------------------
;; Unified entrypoints: 4-arg evidence-aware and 3-arg live-core compatible.

(defun fn2-check-with-evidence (name evidence fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil))
  (case name
    (:trace (fn2-check-trace-evidence evidence fn2-core))
    (:work (fn2-check-work-evidence evidence fn2-core))
    (:own (fn2-check-own-evidence evidence fn2-core fn2-own))
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
;; Totality, anti-stub, and missing-evidence refusal theorems.

(local (defthm fn2-check-wire-connections-resultp
         (fn2-check-resultp (fn2-check-wire-connections conns))
         :hints (("Goal" :induct (fn2-check-wire-connections conns)
                  :in-theory (disable fn2-wire-check fn2-wire-conn-entryp nth)))))

(local (defthm fn2-check-own-ev-resultp
         (fn2-check-resultp (fn2-check-own-evidence evidence fn2-core fn2-own))
         :hints (("Goal" :in-theory (disable fn2-check-own)))))
(local (defthm fn2-check-trace-ev-resultp
         (fn2-check-resultp (fn2-check-trace-evidence evidence fn2-core))
         :hints (("Goal" :in-theory (disable true-listp fn2-trace-verdict fn2-trace-selections
                                             fn2-trace-selection-difference fn2-trace-records fn2-trace-lost nth len)))))
(local (defthm fn2-check-work-ev-resultp
         (fn2-check-resultp (fn2-check-work-evidence evidence fn2-core))
         :hints (("Goal" :in-theory (disable true-listp fn2-work-visible-tuplep fn2-check-work fn2-check-work-visible
                                             fn2-trace-records fn2-trace-lost fn2-trace-wfp nth len)))))
(local (defthm fn2-check-account-ev-resultp
         (fn2-check-resultp (fn2-check-account-evidence evidence fn2-core))
         :hints (("Goal" :in-theory (disable true-listp fn2-account-check fn2-account-core-conservedp
                                             fn2-check-account-core-rows fn2-account-core-rows nth len)))))
(local (defthm fn2-check-fair-ev-resultp
         (fn2-check-resultp (fn2-check-fair-evidence evidence fn2-core))
         :hints (("Goal" :in-theory (disable fn2-check-fair-sched-with-evidence fn2-core-sched)))))
(local (defthm fn2-check-history-ev-resultp
         (fn2-check-resultp (fn2-check-history-evidence evidence))
         :hints (("Goal" :in-theory (disable true-listp fn2-check-history fn2-history-translate nth len)))))
(local (defthm fn2-check-identity-ev-resultp
         (fn2-check-resultp (fn2-check-identity-evidence evidence))
         :hints (("Goal" :in-theory (disable true-listp fn2-check-identity nth len)))))
(local (defthm fn2-check-wire-ev-resultp
         (fn2-check-resultp (fn2-check-wire-evidence evidence))
         :hints (("Goal" :in-theory (disable true-listp booleanp fn2-wire-check fn2-check-wire-connections nth len)))))
(local (defthm fn2-check-consumer-ev-resultp
         (fn2-check-resultp (fn2-check-consumer-evidence evidence))
         :hints (("Goal" :in-theory (disable true-listp fn2-consumer-check nth len)))))
(local (defthm fn2-check-recovery-ev-resultp
         (fn2-check-resultp (fn2-check-recovery-evidence evidence))
         :hints (("Goal" :in-theory (disable true-listp fn2-check-recovery fn2-history-translate nth len)))))
(local (defthm fn2-check-reclaim-ev-resultp
         (fn2-check-resultp (fn2-check-reclaim-evidence evidence))
         :hints (("Goal" :in-theory (disable true-listp fn2-check-reclaim nth len)))))

(defthm fn2-check-with-evidence-returns-resultp
  (fn2-check-resultp (fn2-check-with-evidence name evidence fn2-core fn2-own))
  :hints (("Goal" :in-theory (disable fn2-check-trace-evidence fn2-check-work-evidence
                                      fn2-check-own-evidence fn2-check-account-evidence
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
  :hints (("Goal" :in-theory (disable fn2-check) :use fn2-check-returns-resultp)))

(defthm fn2-check-unknown-fails
  (implies (not (fn2-checker-namep name))
           (equal (fn2-check-with-evidence name evidence fn2-core fn2-own)
                  '(:fail :unknown-checker)))
  :hints (("Goal" :in-theory (disable fn2-check-trace-evidence fn2-check-work-evidence
                                      fn2-check-own-evidence fn2-check-account-evidence
                                      fn2-check-fair-evidence fn2-check-history-evidence
                                      fn2-check-identity-evidence fn2-check-wire-evidence
                                      fn2-check-consumer-evidence fn2-check-recovery-evidence
                                      fn2-check-reclaim-evidence))))

(defthm fn2-check-missing-evidence-refused
  (implies (member-eq name '(:trace :work :account :history :identity :wire :consumer :recovery :reclaim))
           (not (equal (fn2-check name fn2-core fn2-own) :pass)))
  :hints (("Goal" :in-theory (disable fn2-account-core-conservedp))))

;; ---------------------------------------------------------------------------
;; Substantive semantic soundness theorems.

(defthm fn2-check-own-semantic-sound
  (iff (equal (fn2-check-with-evidence :own evidence fn2-core fn2-own) :pass)
       (and (or (null evidence) (eq evidence :core))
            (equal (fn2-own-error fn2-own) 0)
            (fn2-pool-semanticp (fn2-core-pool fn2-core))
            (fn2-own-ranges-p (fn2-ops-rows (fn2-core-ops fn2-core))
                              (fn2-core-pool fn2-core) (fn2-core-ops fn2-core))
            (fn2-own-output-digests-p (fn2-ops-rows (fn2-core-ops fn2-core))
                                      (fn2-core-pool fn2-core) (fn2-core-ops fn2-core) fn2-own)))
  :hints (("Goal" :in-theory (disable fn2-core-pool fn2-core-ops fn2-ops-rows fn2-own-error
                                      fn2-pool-semanticp fn2-own-ranges-p fn2-own-output-digests-p))))

(defthm fn2-check-fair-live-sound
  (implies (and (fn2-schedp (fn2-core-sched fn2-core))
                (equal (fn2-check :fair fn2-core fn2-own) :pass)
                (fn2-sched-principalp principal (fn2-core-sched fn2-core)))
           (let ((sched (fn2-core-sched fn2-core)))
             (and (mv-nth 0 (fn2-sched-visits-principal
                             (fn2-sched-calendar-length sched) principal sched))
                  (implies (< 0 (fn2-sched-countsi principal sched))
                           (and (equal (mv-nth 0 (fn2-sched-pop-head principal sched)) :ok)
                                (= (fn2-sched-in-queue (fn2-sched-headsi principal sched) sched) 1)
                                (= (fn2-sched-principal (fn2-sched-headsi principal sched) sched) principal))))))
  :hints (("Goal" :in-theory (disable fn2-core-sched fn2-schedp fn2-sched-principalp
                                      fn2-sched-in-queue fn2-sched-principal
                                      fn2-sched-headsi fn2-sched-countsi
                                      fn2-check-fair-sched fn2-sched-visits-principal
                                      fn2-sched-pop-head fn2-sched-calendar-length)
           :use ((:instance fn2-check-fair-sched-guarantees-visit-within-l
                            (fn2-sched (fn2-core-sched fn2-core)))
                 (:instance fn2-check-fair-sched-pop-head-ok
                            (fn2-sched (fn2-core-sched fn2-core)))))))

(defthm fn2-check-fair-trace-sound
  (implies (equal (fn2-check-with-evidence :fair (list :trace events bound drainp) fn2-core fn2-own) :pass)
           (and (posp bound)
                (fn2-fair-trace-bounded-p events nil bound drainp)))
  :hints (("Goal" :in-theory (disable fn2-core-sched fn2-fair-trace-check fn2-fair-trace-bounded-p))))

(defthm fn2-check-fair-deadlock-sound
  (implies (equal (fn2-check-with-evidence :fair (list :deadlock threads capacities retained) fn2-core fn2-own) :pass)
           (let ((res (fn2-pv-check-retained threads capacities retained)))
             (and (eq (cdr (assoc-eq :status res)) :ok)
                  (equal (cdr (assoc-eq :deadlocks res)) 0))))
  :hints (("Goal" :in-theory (disable fn2-core-sched fn2-fair-deadlock-check fn2-pv-check-retained))))

(defthm fn2-check-trace-records-sound
  (iff (equal (fn2-check-with-evidence :trace (list :records records lost expected before after) fn2-core fn2-own) :pass)
       (and (true-listp records)
            (true-listp expected)
            (equal lost 0)
            (null (fn2-trace-selection-difference (fn2-trace-selections records) expected))
            (not before)
            (not after)))
  :hints (("Goal" :in-theory (disable true-listp fn2-trace-selections fn2-trace-selection-difference))))

(defthm fn2-check-trace-core-sound
  (iff (equal (fn2-check-with-evidence :trace (list :core expected before after) fn2-core fn2-own) :pass)
       (let ((tr (fn2-core-trace fn2-core)))
         (and (true-listp expected)
              (fn2-trace-wfp tr)
              (equal (fn2-trace-lost tr) 0)
              (null (fn2-trace-selection-difference (fn2-trace-selections (fn2-trace-records tr)) expected))
              (not before)
              (not after))))
  :hints (("Goal" :in-theory (disable true-listp fn2-core-trace fn2-trace-selections
                                      fn2-trace-selection-difference fn2-trace-records
                                      fn2-trace-lost fn2-trace-wfp))))

(defthm fn2-check-work-semantic-sound
  (iff (equal (fn2-check-with-evidence :work (list :work records lost nobs nvisits nactions profile) fn2-core fn2-own) :pass)
       (let ((cert (fn2-work-certificate records)))
         (and (equal lost 0)
              (fn2-profilep profile)
              (fn2-work-records-p records profile)
              (natp nobs) (natp nvisits) (natp nactions)
              (equal nobs (fn2-work-cert-observations cert))
              (equal nvisits (fn2-work-cert-visits cert))
              (equal nactions (fn2-work-cert-actions cert))
              (<= nobs (nfix (fn2-profile-h profile)))
              (<= nvisits (nfix (fn2-profile-k profile)))
              (<= nactions (nfix (fn2-profile-aturn profile)))
              (<= (+ nvisits (nfix (fn2-work-cert-bytes cert)) (nfix (fn2-work-cert-steps cert)))
                  (+ (* (nfix (fn2-profile-h profile)) *fn2-work-transition*)
                     (* (nfix (fn2-profile-k profile)) *fn2-turn-transition-max*))))))
  :hints (("Goal" :in-theory (disable fn2-work-certificate fn2-work-records-p fn2-profilep
                                      fn2-profile-h fn2-profile-k fn2-profile-aturn
                                      fn2-work-cert-observations fn2-work-cert-visits
                                      fn2-work-cert-actions fn2-work-cert-bytes fn2-work-cert-steps))))

(defthm fn2-check-work-visible-semantic-sound
  (iff (equal (fn2-check-with-evidence :work (list :visible records lost nobs nvisits nactions profile visible) fn2-core fn2-own) :pass)
       (let ((cert (fn2-work-certificate records)))
         (and (fn2-work-visible-tuplep visible)
              (equal (fn2-check-work records lost nobs nvisits nactions profile) :pass)
              (<= (nfix (nth 0 (true-list-fix visible))) (fn2-work-byte-charge records nil))
              (<= (nfix (nth 1 (true-list-fix visible))) (fn2-work-byte-charge records t))
              (<= (+ (nfix (nth 0 (true-list-fix visible))) (nfix (nth 1 (true-list-fix visible))))
                  (nfix (fn2-work-cert-bytes cert)))
              (equal (fn2-work-cert-actions cert) (nth 2 (true-list-fix visible)))
              (equal (fn2-work-cert-observations cert) (nth 3 (true-list-fix visible))))))
  :hints (("Goal" :in-theory (disable fn2-work-visible-tuplep fn2-check-work fn2-work-certificate
                                      fn2-work-byte-charge fn2-work-cert-bytes
                                      fn2-work-cert-actions fn2-work-cert-observations
                                      true-list-fix nfix))))

(defthm fn2-check-account-core-sound
  (iff (equal (fn2-check-with-evidence :account (list :core records capacity) fn2-core fn2-own) :pass)
       (let ((rows (fn2-check-account-core-rows 0 (fn2-account-core-rows fn2-core) fn2-core)))
         (and (true-listp records)
              (natp capacity)
              (fn2-account-core-conservedp fn2-core)
              (<= (fn2-acct-sum-committed rows) capacity)
              (equal (fn2-acct-check-rows rows records) :pass))))
  :hints (("Goal" :in-theory (disable true-listp fn2-account-core-conservedp fn2-check-account-core-rows
                                      fn2-account-core-rows fn2-acct-sum-committed fn2-acct-check-rows))))

(defthm fn2-check-history-semantic-sound
  (iff (equal (fn2-check-with-evidence :history (list :history events profile classification recovered) fn2-core fn2-own) :pass)
       (mv-let (code trace) (fn2-history-translate events)
         (and (true-listp events)
              (eq code :ok)
              (fn2-lm-recovery-allowedp trace profile classification recovered))))
  :hints (("Goal" :in-theory (disable true-listp fn2-history-translate fn2-lm-recovery-allowedp))))

(defthm fn2-check-recovery-implies-history-and-witness-sound
  (iff (equal (fn2-check-with-evidence :recovery (list :recovery events profile classification recovered outcome) fn2-core fn2-own) :pass)
       (let* ((trace (mv-nth 1 (fn2-history-translate events)))
              (s (fn2-lm-trace-state trace))
              (presented (consp (fn2-lm-state-witnesses s)))
              (credited (and (fn2-cm-independent-frontier profile)
                             (fn2-lm-conflicting-witness (fn2-lm-state-witnesses s) recovered))))
         (and (equal (fn2-check-with-evidence :history (list :history events profile classification recovered) fn2-core fn2-own) :pass)
              (iff (eq outcome :rollback-detected) credited)
              (iff (eq outcome :none) (not presented))
              (iff (eq outcome :uncredited) (and presented (not (fn2-cm-independent-frontier profile))))
              (or (not (eq outcome :discontinuity)) (eq classification :damaged)))))
  :hints (("Goal" :in-theory (disable true-listp fn2-history-translate fn2-lm-recovery-allowedp
                                      fn2-lm-trace-state fn2-lm-state-witnesses
                                      fn2-cm-independent-frontier fn2-lm-conflicting-witness))))

(defun fn2-wire-connections-pass-p (conns)
  (declare (xargs :verify-guards nil))
  (if (atom conns)
      (null conns)
    (let ((c (car conns)))
      (and (fn2-wire-conn-entryp c)
           (fn2-wire-pass-p (nth 0 c) (nth 1 c) (nth 2 c))
           (fn2-wire-connections-pass-p (cdr conns))))))

(local (defthm fn2-check-wire-connections-iff
         (iff (equal (fn2-check-wire-connections conns) :pass)
              (fn2-wire-connections-pass-p conns))
         :hints (("Goal" :induct (fn2-check-wire-connections conns)
                  :in-theory (e/d (fn2-wire-pass-p) (fn2-wire-check fn2-wire-conn-entryp nth))))))

(defthm fn2-check-wire-connections-sound
  (iff (equal (fn2-check-with-evidence :wire (list :connections conns) fn2-core fn2-own) :pass)
       (and (true-listp conns) (fn2-wire-connections-pass-p conns)))
  :hints (("Goal" :in-theory (disable true-listp fn2-check-wire-connections fn2-wire-connections-pass-p))))

;; Honest pass-iff characterizations for thin list-interpreter wrappers.
(defthm fn2-check-identity-pass-iff
  (iff (equal (fn2-check-with-evidence :identity (list :identity events) fn2-core fn2-own) :pass)
       (and (true-listp events)
            (consp (fn2-check-identity events))
            (eq (car (fn2-check-identity events)) :ok)))
  :hints (("Goal" :in-theory (disable true-listp fn2-check-identity))))

(defthm fn2-check-consumer-pass-iff
  (iff (equal (fn2-check-with-evidence :consumer (list :consumer obs history incarnation interims) fn2-core fn2-own) :pass)
       (and (true-listp obs) (true-listp interims)
            (equal (fn2-consumer-check obs history incarnation interims) :pass)))
  :hints (("Goal" :in-theory (disable true-listp fn2-consumer-check))))

(defthm fn2-check-reclaim-pass-iff
  (iff (equal (fn2-check-with-evidence :reclaim (list :reclaim events) fn2-core fn2-own) :pass)
       (and (true-listp events)
            (null (fn2-check-reclaim events))))
  :hints (("Goal" :in-theory (disable true-listp fn2-check-reclaim))))

(assert-event (and (= (len *fn2-checker-names*) 11)
                   (no-duplicatesp-eq *fn2-checker-names*)
                   (fn2-check-resultp :pass)
                   (not (fn2-check-resultp :not-yet))
                   (fn2-check-resultp '(:fail :example))
                   (not (fn2-check-resultp nil))))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-checker-namep fn2-check-resultp fn2-check-fair-core fn2-trace-verdict
    fn2-work-visible-tuplep fn2-check-work-core fn2-check-work-evidence
    fn2-wire-conn-entryp fn2-check-identity-evidence fn2-check-reclaim-evidence
    fn2-own-observe-issue fn2-own-observe-output fn2-own-record-input-byte
    fn2-own-observe-read fn2-own-observe-core-write)
  (w state)))

; Full turn-level lockstep TRACE against a live reference core uses fn2-check-trace-turn.
