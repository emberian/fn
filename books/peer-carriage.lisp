; fn: the opaque-carriage resource policy and the refusal classes of a
; present carrier (PRF-099; theorems 4 and 5 of the peering spike record,
; planning/evidence/spike-peering-2026-09-25.md; review 2026-09-24, gpt-6
; direction, "Opaque carriage").
;
; 1. The budget.  A carried article (D23, fn-pa-current-plan's :carried arm)
;    is admitted against the delivering boundary's budget
;    (books/peer-carriage-rows.lisp) and the usage of that boundary so far.
;    The usage is not a host counter: it is the projection of the Store's
;    committed records, the carried kind-4 composites whose article record's
;    release evidence names the boundary (`peer-transit:NAME',
;    books/peer-inbound.lisp fn-peer-evidence), summed.  The owner carries it
;    as a (K . TALLY) cache over the first K committed records and extends it
;    by the records committed since, exactly as books/store-budget.lisp
;    carries the record-octet sum; the keystone says the carried value is the
;    projection.  Host: host/owner-host.lisp fn-owner-carried-usage and
;    fn-owner-peer-carried-relay-event, called from host/native/owner.lisp
;    fnn-owner-attempt-transit.
;
; 2. The refusal classes.  For a present carrier that is not accepted, the
;    class is one of :no-local-binding, :unsupported-profile,
;    :signature-failed and :malformed, a function of the received octets, the
;    keyring snapshots, the delivering boundary's carried list and the two
;    primitive observations.  None is `verified' and none is the unsigned
;    arm.  Host: fn-owner-transit-refusal-class, the transit refusal's detail.
(in-package "ACL2")
(include-book "peer-authored-accept")
(include-book "peer-carriage-rows")

; =============================================================================
; 1a. What one committed Store event contributes

; (EVIDENCE . CHARGE) for a carried kind-4 composite, nil for any other event.
(defun fn-pcb-event-carriage (e)
  (declare (xargs :guard t))
  (if (and (fn-stxa-p e)
           (equal (fn-stxa-schema e) *fn-stxa-carried-version*)
           (equal (fn-stxa-keyring-generation e) 0))
      (let ((verdict (fn-stxe-decode-exact (fn-stxa-verdict-event e)))
            (article (fn-record-decode-exact (fn-stxa-article-record e))))
        (if (and (fn-stmt-okp verdict)
                 (equal (fn-stxe-token (fn-stmt-value verdict)) :carried)
                 (fn-record-result-okp article))
            (cons (fn-record-release-evidence
                   (fn-record-result-record article))
                  (nfix (fn-record-charge (fn-record-result-record article))))
          nil))
    nil))

(defthm fn-pcb-event-carriage-charge-is-natural
  (implies (consp (fn-pcb-event-carriage e))
           (natp (cdr (fn-pcb-event-carriage e))))
  :rule-classes ((:forward-chaining :trigger-terms
                  ((fn-pcb-event-carriage e)))))

(defthm fn-pcb-event-carriage-needs-a-composite
  (implies (not (fn-stxa-p e))
           (equal (fn-pcb-event-carriage e) nil)))

(local
(defthm fn-pcb-refusal-is-not-a-composite
  (implies (equal (car e) :refused) (not (fn-stxa-p e)))
  :hints (("Goal" :in-theory (enable fn-stxa-p fn-stxa-sequence
                                     fn-record-uint32p)))))

(in-theory (disable fn-pcb-event-carriage))

(defun fn-pcb-car (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-pcb-cdr (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

; A usage is (CHARGE . COUNT), both naturals.
(defun fn-pcb-usage-plus (usage charge)
  (declare (xargs :guard t))
  (cons (+ (nfix charge) (nfix (fn-pcb-car usage)))
        (+ 1 (nfix (fn-pcb-cdr usage)))))

; THE PROJECTION: the carried charge and count stored through the boundary
; whose release evidence is EVIDENCE, over committed RECORDS.
(defun fn-pcb-usage (records evidence)
  (declare (xargs :guard t))
  (if (consp records)
      (let ((rest (fn-pcb-usage (cdr records) evidence))
            (c (fn-pcb-event-carriage (car records))))
        (if (and (consp c) (equal (car c) evidence))
            (fn-pcb-usage-plus rest (cdr c))
          rest))
    (cons 0 0)))

(defthm fn-pcb-usage-is-natural
  (and (consp (fn-pcb-usage records evidence))
       (acl2-numberp (car (fn-pcb-usage records evidence)))
       (acl2-numberp (cdr (fn-pcb-usage records evidence)))
       (integerp (car (fn-pcb-usage records evidence)))
       (<= 0 (car (fn-pcb-usage records evidence)))
       (integerp (cdr (fn-pcb-usage records evidence)))
       (<= 0 (cdr (fn-pcb-usage records evidence)))))

(defthm fn-pcb-usage-components-are-natural
  (and (natp (car (fn-pcb-usage records evidence)))
       (natp (cdr (fn-pcb-usage records evidence))))
  :rule-classes ((:forward-chaining :trigger-terms
                  ((fn-pcb-usage records evidence))
                  :corollary (natp (car (fn-pcb-usage records evidence))))
                 (:forward-chaining :trigger-terms
                  ((fn-pcb-usage records evidence))
                  :corollary (natp (cdr (fn-pcb-usage records evidence))))))

; =============================================================================
; 1b. The carried tally and its cache

(defun fn-pcb-tally-get (evidence tally)
  (declare (xargs :guard t))
  (if (consp tally)
      (if (and (consp (car tally)) (equal (car (car tally)) evidence))
          (cons (nfix (fn-pcb-car (cdr (car tally))))
                (nfix (fn-pcb-cdr (cdr (car tally)))))
        (fn-pcb-tally-get evidence (cdr tally)))
    (cons 0 0)))

(defun fn-pcb-tally-put (evidence usage tally)
  (declare (xargs :guard t))
  (if (consp tally)
      (if (and (consp (car tally)) (equal (car (car tally)) evidence))
          (cons (cons evidence usage) (cdr tally))
        (cons (car tally) (fn-pcb-tally-put evidence usage (cdr tally))))
    (list (cons evidence usage))))

(defthm fn-pcb-tally-get-of-put
  (equal (fn-pcb-tally-get e (fn-pcb-tally-put e2 usage tally))
         (if (equal e e2)
             (cons (nfix (fn-pcb-car usage)) (nfix (fn-pcb-cdr usage)))
           (fn-pcb-tally-get e tally))))

(defun fn-pcb-tally-records (records tally)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-pcb-tally-records
       (cdr records)
       (let ((c (fn-pcb-event-carriage (car records))))
         (if (consp c)
             (fn-pcb-tally-put (car c)
                               (fn-pcb-usage-plus
                                (fn-pcb-tally-get (car c) tally) (cdr c))
                               tally)
           tally)))
    tally))

(local (defthm fn-pcb-usage-of-append
  (equal (fn-pcb-usage (append a b) evidence)
         (let ((ua (fn-pcb-usage a evidence))
               (ub (fn-pcb-usage b evidence)))
           (cons (+ (car ua) (car ub)) (+ (cdr ua) (cdr ub)))))
  :hints (("Goal" :induct (fn-pcb-usage a evidence)))))

(local (defthm fn-pcb-tally-records-of-append
  (equal (fn-pcb-tally-records (append a b) tally)
         (fn-pcb-tally-records b (fn-pcb-tally-records a tally)))))

(local (defthm fn-pcb-tally-get-is-natural
  (and (consp (fn-pcb-tally-get e tally))
       (acl2-numberp (car (fn-pcb-tally-get e tally)))
       (acl2-numberp (cdr (fn-pcb-tally-get e tally)))
       (integerp (car (fn-pcb-tally-get e tally)))
       (<= 0 (car (fn-pcb-tally-get e tally)))
       (integerp (cdr (fn-pcb-tally-get e tally)))
       (<= 0 (cdr (fn-pcb-tally-get e tally))))))

(local (defthm fn-pcb-tally-get-components-are-natural
  (and (natp (car (fn-pcb-tally-get e tally)))
       (natp (cdr (fn-pcb-tally-get e tally))))
  :rule-classes ((:forward-chaining :trigger-terms
                  ((fn-pcb-tally-get e tally))
                  :corollary (natp (car (fn-pcb-tally-get e tally))))
                 (:forward-chaining :trigger-terms
                  ((fn-pcb-tally-get e tally))
                  :corollary (natp (cdr (fn-pcb-tally-get e tally)))))))

; The fold's reading at EVIDENCE is its starting reading plus the projection.
(defthm fn-pcb-tally-records-get
  (equal (fn-pcb-tally-get evidence (fn-pcb-tally-records records tally))
         (cons (+ (car (fn-pcb-tally-get evidence tally))
                  (car (fn-pcb-usage records evidence)))
               (+ (cdr (fn-pcb-tally-get evidence tally))
                  (cdr (fn-pcb-usage records evidence)))))
  :hints (("Goal" :induct (fn-pcb-tally-records records tally)
           :in-theory (disable floor mod))))

; The cache (K . TALLY): TALLY is the fold of the first K committed records.
(defun fn-pcb-cache-validp (cache records)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp cache) (natp (car cache)) (<= (car cache) (len records))
       (equal (cdr cache) (fn-pcb-tally-records (take (car cache) records)
                                                nil))))

(defun fn-pcb-drop (k records)
  (declare (xargs :guard (natp k)))
  (if (zp k) records
    (fn-pcb-drop (1- k) (if (consp records) (cdr records) nil))))

(local (defthm fn-pcb-drop-is-nthcdr
  (implies (natp k) (equal (fn-pcb-drop k records) (nthcdr k records)))
  :hints (("Goal" :in-theory (enable nthcdr)))))

; The tally of RECORDS from CACHE: the cached tally extended by the records
; past its count; a full walk (the projection at open) when CACHE is not a
; (K . TALLY) within RECORDS.
(defun fn-pcb-usage-extend (cache records)
  (declare (xargs :guard t))
  (if (and (consp cache) (natp (car cache)) (<= (car cache) (len records)))
      (fn-pcb-tally-records (fn-pcb-drop (car cache) records) (cdr cache))
    (fn-pcb-tally-records records nil)))

(local (defthm fn-pcb-append-take-nthcdr
  (implies (and (natp k) (<= k (len records)))
           (equal (append (take k records) (nthcdr k records))
                  records))
  :hints (("Goal" :induct (nthcdr k records)
           :in-theory (enable take nthcdr)))))

(local (defthm fn-pcb-take-of-append
  (implies (and (natp k) (<= k (len a)))
           (equal (take k (append a b)) (take k a)))
  :hints (("Goal" :induct (nthcdr k a) :in-theory (enable take nthcdr)))))

(local (defthm fn-pcb-extend-is-full-walk
  (implies (fn-pcb-cache-validp cache records)
           (equal (fn-pcb-usage-extend cache records)
                  (fn-pcb-tally-records records nil)))
  :hints (("Goal" :in-theory (disable fn-pcb-append-take-nthcdr
                                      fn-pcb-tally-records-of-append)
           :use ((:instance fn-pcb-append-take-nthcdr (k (car cache)))
                 (:instance fn-pcb-tally-records-of-append
                            (a (take (car cache) records))
                            (b (nthcdr (car cache) records))
                            (tally nil)))))))

; KEYSTONE (the carried usage is the replay projection).  From a cache that
; is the fold of a prefix of the committed records, the owner's extension
; read at EVIDENCE is exactly the projection `fn-pcb-usage'.
(defthm fn-pcb-carried-usage-is-the-projection
  (implies (fn-pcb-cache-validp cache records)
           (equal (fn-pcb-tally-get evidence
                                    (fn-pcb-usage-extend cache records))
                  (fn-pcb-usage records evidence)))
  :hints (("Goal" :in-theory (disable fn-pcb-usage-extend
                                      fn-pcb-cache-validp))))

; The cache the owner keeps after a decision is valid for the records it was
; extended over, and stays valid while committed records only grow.
(local (defthm fn-pcb-take-of-len
  (implies (true-listp records)
           (equal (take (len records) records) records))
  :hints (("Goal" :in-theory (enable take)))))

(defthm fn-pcb-full-cache-is-valid
  (implies (true-listp records)
           (fn-pcb-cache-validp (cons (len records)
                                      (fn-pcb-tally-records records nil))
                                records))
  :hints (("Goal" :in-theory (e/d (fn-pcb-cache-validp)
                                  (fn-pcb-tally-records)))))

(defthm fn-pcb-extended-cache-is-valid
  (implies (and (fn-pcb-cache-validp cache records) (true-listp records))
           (fn-pcb-cache-validp (cons (len records)
                                      (fn-pcb-usage-extend cache records))
                                records))
  :hints (("Goal" :in-theory (disable fn-pcb-usage-extend fn-pcb-tally-records
                                      fn-pcb-cache-validp
                                      fn-pcb-full-cache-is-valid)
           :use (fn-pcb-extend-is-full-walk fn-pcb-full-cache-is-valid))))

(local (defthm fn-pcb-len-of-append
  (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-pcb-cache-valid-after-commit
  (implies (fn-pcb-cache-validp cache records)
           (fn-pcb-cache-validp cache (append records more)))
  :hints (("Goal" :in-theory (e/d (fn-pcb-cache-validp)
                                  (fn-pcb-tally-records fn-pcb-take-of-append))
           :use ((:instance fn-pcb-take-of-append
                            (k (car cache)) (a records) (b more))))))

(defthm fn-pcb-empty-cache-is-valid
  (fn-pcb-cache-validp (cons 0 nil) records))

; =============================================================================
; 1c. The admission decision

; :within, or a refusal naming which bound: no budget at all, the count, or
; the charge (the operator's octets in whole Store pages).
(defun fn-pcb-admission (budget usage charge)
  (declare (xargs :guard t))
  (let ((used-charge (nfix (fn-pcb-car usage)))
        (used-count (nfix (fn-pcb-cdr usage))))
    (cond ((not (fn-pcb-budgetp budget))
           (list :refused :carried-budget-unset))
          ((< (cadr budget) (+ 1 used-count))
           (list :refused :carried-count-exhausted))
          ((< (car budget) (+ (nfix charge) used-charge))
           (list :refused :carried-octets-exhausted))
          (t :within))))

; Each exhaustion is refused by its own name.
(defthm fn-pcb-admission-without-a-budget-admits-nothing
  (implies (not (fn-pcb-budgetp budget))
           (equal (fn-pcb-admission budget usage charge)
                  (list :refused :carried-budget-unset))))

(defthm fn-pcb-admission-names-count-exhaustion
  (implies (and (fn-pcb-budgetp budget)
                (<= (cadr budget) (nfix (fn-pcb-cdr usage))))
           (equal (fn-pcb-admission budget usage charge)
                  (list :refused :carried-count-exhausted))))

(defthm fn-pcb-admission-names-octet-exhaustion
  (implies (and (fn-pcb-budgetp budget)
                (< (nfix (fn-pcb-cdr usage)) (cadr budget))
                (< (car budget) (+ (nfix charge) (nfix (fn-pcb-car usage)))))
           (equal (fn-pcb-admission budget usage charge)
                  (list :refused :carried-octets-exhausted))))

(defthm fn-pcb-admission-within-keeps-both-bounds
  (implies (equal (fn-pcb-admission budget usage charge) :within)
           (and (fn-pcb-budgetp budget)
                (<= (car (fn-pcb-usage-plus usage charge)) (car budget))
                (<= (cdr (fn-pcb-usage-plus usage charge)) (cadr budget))))
  :hints (("Goal" :in-theory (enable fn-pcb-usage-plus))))

; =============================================================================
; 1d. The carried event, gated by the budget

; The carried arm's kind-4 event (fn-pa-carried-event) when the delivering
; boundary's BUDGET admits one more article of CHARGE over USAGE; the
; admission's refusal otherwise; nil when no event is formed.  The event is
; returned only when its own committed carriage is (RELEASE-EVIDENCE .
; CHARGE), the pair the projection will count.  Host:
; host/owner-host.lisp fn-owner-peer-carried-relay-event.
(defun fn-pcb-carried-event
    (sequence txid generation msgid received groups obligation-id
              content-subject release-evidence charge snapshots carried
              clock-observation budget usage)
  (declare (xargs :guard t))
  (let ((admission (fn-pcb-admission budget usage charge)))
    (if (not (equal admission :within))
        admission
      (let ((e (fn-pa-carried-event
                sequence txid generation msgid received groups obligation-id
                content-subject release-evidence charge snapshots carried
                clock-observation)))
        (if (and e (equal (fn-pcb-event-carriage e)
                          (cons release-evidence (nfix charge))))
            e
          nil)))))

(defthm fn-pcb-carried-event-is-carried-or-refused
  (let ((r (fn-pcb-carried-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots carried
            clock-observation budget usage)))
    (or (null r)
        (and (equal (car r) :refused)
             (member-equal (cadr r) '(:carried-budget-unset
                                      :carried-count-exhausted
                                      :carried-octets-exhausted)))
        (and (fn-hsig-article-event-carried-bindsp r)
             (equal (fn-pcb-event-carriage r)
                    (cons release-evidence (nfix charge)))
             (equal (fn-pcb-admission budget usage charge) :within))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-pa-carried-event fn-pcb-event-carriage)
           :use ((:instance fn-pa-carried-event-is-a-carried-record)))))

; =============================================================================
; 1e. The budget across a trace

; RECORDS (oldest first) were admitted for EVIDENCE under BUDGET: every
; carried record naming EVIDENCE passed the admission against the usage of
; the records before it, starting from USAGE.  Records of other boundaries
; and every non-carried record are unconstrained.
(defun fn-pcb-admitted-from (records usage budget evidence)
  (declare (xargs :guard t))
  (if (consp records)
      (let ((c (fn-pcb-event-carriage (car records))))
        (if (and (consp c) (equal (car c) evidence))
            (and (equal (fn-pcb-admission budget usage (cdr c)) :within)
                 (fn-pcb-admitted-from (cdr records)
                                       (fn-pcb-usage-plus usage (cdr c))
                                       budget evidence))
          (fn-pcb-admitted-from (cdr records) usage budget evidence)))
    t))

(local (defun fn-pcb-sum-usage (usage records evidence)
  (let ((u (fn-pcb-usage records evidence)))
    (cons (+ (nfix (fn-pcb-car usage)) (car u))
          (+ (nfix (fn-pcb-cdr usage)) (cdr u))))))

(local (defthm fn-pcb-admitted-from-bounds
  (implies (and (fn-pcb-budgetp budget)
                (<= (nfix (fn-pcb-car usage)) (car budget))
                (<= (nfix (fn-pcb-cdr usage)) (cadr budget))
                (fn-pcb-admitted-from records usage budget evidence))
           (and (<= (car (fn-pcb-sum-usage usage records evidence))
                    (car budget))
                (<= (cdr (fn-pcb-sum-usage usage records evidence))
                    (cadr budget))))
  :hints (("Goal" :induct (fn-pcb-admitted-from records usage budget evidence)
           :in-theory (enable fn-pcb-usage-plus)))))

; KEYSTONE (theorem 4 of the spike record).  Across any committed history in
; which every carried record of boundary EVIDENCE was admitted, the carried
; charge stored through that boundary is at most its charge budget and the
; count at most its count budget.
(defthm fn-pcb-carried-history-within-budget
  (implies (and (fn-pcb-budgetp budget)
                (fn-pcb-admitted-from records (cons 0 0) budget evidence))
           (and (<= (car (fn-pcb-usage records evidence)) (car budget))
                (<= (cdr (fn-pcb-usage records evidence)) (cadr budget))))
  :hints (("Goal" :use ((:instance fn-pcb-admitted-from-bounds
                                   (usage (cons 0 0)))))))

; With no budget the carried arm stored nothing through the boundary.
(defthm fn-pcb-no-budget-history-carries-nothing
  (implies (and (not (fn-pcb-budgetp budget))
                (fn-pcb-admitted-from records usage budget evidence))
           (equal (fn-pcb-usage records evidence) (cons 0 0))))

(local (defthm fn-pcb-admitted-from-of-append
  (implies (and (natp (fn-pcb-car usage)) (natp (fn-pcb-cdr usage)) (consp usage))
           (equal (fn-pcb-admitted-from (append a b) usage budget evidence)
                  (and (fn-pcb-admitted-from a usage budget evidence)
                       (fn-pcb-admitted-from
                        b (fn-pcb-sum-usage usage a evidence)
                        budget evidence))))
  :hints (("Goal" :induct (fn-pcb-admitted-from a usage budget evidence)
           :in-theory (enable fn-pcb-usage-plus)))))

; KEYSTONE (the host-called constructor keeps the trace admitted).  If the
; committed history was admitted and the owner hands the constructor the
; projection of that history at the event's own release evidence (what
; fn-pcb-carried-usage-is-the-projection gives it), then the history with
; whatever the constructor returned committed is still admitted: an event
; only within the budget, and a refusal or nil carries nothing.
(defthm fn-pcb-carried-event-keeps-history-admitted
  (let ((e (fn-pcb-carried-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots carried
            clock-observation budget (fn-pcb-usage records release-evidence))))
    (implies (fn-pcb-admitted-from records (cons 0 0) budget
                                   release-evidence)
             (fn-pcb-admitted-from (append records (list e)) (cons 0 0)
                                   budget release-evidence)))
  :hints (("Goal" :in-theory (disable fn-pa-carried-event fn-pcb-event-carriage
                                      fn-pcb-carried-event
                                      fn-hsig-article-event-carried-bindsp)
           :use ((:instance fn-pcb-carried-event-is-carried-or-refused
                            (usage (fn-pcb-usage records release-evidence)))))))

; A record that is not a carried record of this boundary keeps it admitted.
(defthm fn-pcb-other-record-keeps-history-admitted
  (implies (and (fn-pcb-admitted-from records (cons 0 0) budget evidence)
                (not (equal (car (fn-pcb-event-carriage r)) evidence)))
           (fn-pcb-admitted-from (append records (list r)) (cons 0 0)
                                 budget evidence)))

; =============================================================================
; 2. The refusal classes of a present carrier

; The carrier field decodes to nine CBOR items that name no supported
; profile (fn-hc-decode-at's :profile refusal: another version, suite or
; algorithm).  fn-hc-received-plan reports that case as :carrier, so the
; class reads the field's own decode.
(defun fn-pcb-unsupported-profilep (received)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse received)))
    (and (fn-article-result-okp parsed)
         (true-listp parsed)
         (let ((article (fn-article-result-article parsed)))
           (and (true-listp article)
                (let ((field (fn-hc-find-name *fn-hc-name*
                                              (fn-article-fields article))))
                  (and (true-listp field)
                       (let ((decoded (fn-hc-field-decode-at
                                       (fn-hsig-source-version
                                        (fn-hc-authored-source article))
                                       (fn-article-field-unfolded-value field))))
                         (and (consp decoded)
                              (equal (car decoded) :unverified)
                              (consp (cdr decoded))
                              (equal (cadr decoded) :profile))))))))))

(defconst *fn-pcb-refusal-classes*
  '(:no-local-binding :unsupported-profile :signature-failed :malformed))

; The class of a present carrier this node does not accept, or nil when the
; carrier is absent, carried for the boundary, or accepted under both
; primitive observations.  ED-OBSERVATION and ML-OBSERVATION are the host's
; two primitive outcomes, :verified or anything else; they matter only on
; the :ok arm, where this node holds a binding for the carrier's keys.
(defun fn-pcb-refusal-class (received snapshots carried ed-observation
                                      ml-observation)
  (declare (xargs :guard t))
  (let ((plan (fn-pa-current-plan received snapshots carried)))
    (cond ((not (consp plan)) nil)
          ((eq (car plan) :refused)
           (cond ((equal (cadr plan) :local-enrollment) :no-local-binding)
                 ((and (equal (cadr plan) :carrier)
                       (fn-pcb-unsupported-profilep received))
                  :unsupported-profile)
                 (t :malformed)))
          ((and (eq (car plan) :ok)
                (not (and (eq ed-observation :verified)
                          (eq ml-observation :verified))))
           :signature-failed)
          (t nil))))

; KEYSTONE (theorem 5 of the spike record, over the function the host
; calls).  A present carrier (fn-pa-carrier-kind is not :absent) that is not
; carried for the boundary and not accepted under both primitive
; observations has one of the four classes, never nil: a present carrier is
; never relabelled as the unsigned arm, and never reads as verified.
(defthm fn-pcb-present-carrier-not-accepted-has-a-class
  (let ((plan (fn-pa-current-plan received snapshots carried)))
    (implies (and (not (equal (fn-pa-carrier-kind received) :absent))
                  (not (equal (car plan) :carried))
                  (not (and (equal (car plan) :ok)
                            (equal ed :verified) (equal ml :verified))))
             (member-equal (fn-pcb-refusal-class received snapshots carried
                                                 ed ml)
                           *fn-pcb-refusal-classes*)))
  :hints (("Goal" :in-theory (disable fn-pa-current-plan fn-pa-carrier-kind
                                      fn-pcb-unsupported-profilep)
           :use (fn-pa-current-plan-outcomes
                 fn-pa-absent-is-only-parser-confirmed-absence))))

; Accepted under a local binding with a failed primitive: signature-failed.
(defthm fn-pcb-bound-carrier-with-a-failed-primitive-is-signature-failed
  (implies (and (equal (car (fn-pa-current-plan received snapshots carried)) :ok)
                (not (and (equal ed :verified) (equal ml :verified))))
           (equal (fn-pcb-refusal-class received snapshots carried ed ml)
                  :signature-failed))
  :hints (("Goal" :in-theory (disable fn-pa-current-plan))))

; The class is only ever one of the four, so never :verified, :carried or
; :absent; and an absent carrier has no class.
(defthm fn-pcb-refusal-class-range
  (let ((class (fn-pcb-refusal-class received snapshots carried ed ml)))
    (or (null class) (member-equal class *fn-pcb-refusal-classes*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-pa-current-plan
                                      fn-pcb-unsupported-profilep))))

(defthm fn-pcb-absent-carrier-has-no-class
  (implies (equal (fn-pa-carrier-kind received) :absent)
           (equal (fn-pcb-refusal-class received snapshots carried ed ml) nil))
  :hints (("Goal" :in-theory (enable fn-pa-current-plan fn-pa-carrier-form))))

; Unsupported profile and a checked signature failure never collapse: a
; carrier the plan accepts under a binding is never unsupported-profile, and
; one the plan refuses is never signature-failed.
(defthm fn-pcb-refused-carrier-is-never-signature-failed
  (implies (equal (car (fn-pa-current-plan received snapshots carried)) :refused)
           (not (equal (fn-pcb-refusal-class received snapshots carried ed ml)
                       :signature-failed)))
  :hints (("Goal" :in-theory (disable fn-pa-current-plan
                                      fn-pcb-unsupported-profilep))))

(in-theory (disable fn-pcb-usage fn-pcb-tally-records
                    fn-pcb-usage-extend fn-pcb-cache-validp fn-pcb-admission
                    fn-pcb-carried-event fn-pcb-admitted-from
                    fn-pcb-unsupported-profilep fn-pcb-refusal-class))
