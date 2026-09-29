; fn: store limits as operator policy (row S1, lane limits-live, 2026-09-29).
;
; The store's profile is sealed at init: journal/000000.log carries the
; digest of config.json's frame (books/store-genesis.lisp fn-gen-open refuses
; :profile-digest), so the frame is never rewritten.  A limit the operator
; changes is a configuration event instead: `policy set max-transactions N'
; publishes the `:set-limit' row (FIELD, N) (books/config.lisp
; fn-cfg-set-limit), durable and replayed like every configuration record.
; The profile the store is served under is the sealed one with each live
; field overridden by its last row (fn-lim-effective), computed from the
; configuration history alone, before the log is read: the open, the
; launcher's heap probe and the running owner all take it from here.
;
; The live fields are those no bound applied before this fold depends on:
; the transaction budget T, the history octets H and the article octets A.
; (max-config-generations bounds the configuration readdir this fold reads;
; max-record-octets and max-open-suffix bound the log scan; they stay the
; sealed ones.)  A lowered T drags max-open-suffix down with it, as init's
; resolution does (byte-store-frame.lisp fn-bs-profile-resolve).
;
; The decision (fn-lim-decide) is ACL2's over the served profile, the
; store's use, the machine's observation and the running process's
; reservation: applied now when the new profile's heap figure fits the
; reservation the process started with; else recorded, effective at the
; next start (no data moved); refused by name, with the numbers, below the
; store's current use, when the profile would be invalid, or when the
; machine cannot hold the new figure.

(in-package "ACL2")

(include-book "config")
(include-book "byte-store-frame")
(include-book "heap-reservation")
(include-book "native-control-reason")

(defconst *fn-lim-fields*
  '("max-transactions" "max-history-octets" "max-article-octets"))

(defun fn-lim-fieldp (name)
  (declare (xargs :guard t))
  (if (member-equal name *fn-lim-fields*) t nil))

(defun fn-lim-field-index (name)
  (declare (xargs :guard t))
  (cond ((equal name "max-transactions") *fn-bs-pf-max-transactions*)
        ((equal name "max-history-octets") *fn-bs-pf-max-history-octets*)
        (t *fn-bs-pf-max-article-octets*)))

; VALUES with field I set to N (a total update-nth over a true list).
(defun fn-lim-set-nth (i n values)
  (declare (xargs :guard (natp i) :measure (nfix i)))
  (if (zp i)
      (cons n (if (consp values) (cdr values) nil))
    (cons (if (consp values) (car values) nil)
          (fn-lim-set-nth (1- i) n (if (consp values) (cdr values) nil)))))

(defthm fn-lim-nth-of-set-nth
  (equal (fn-bs-meta-nth j (fn-lim-set-nth i n values))
         (if (equal (nfix j) (nfix i)) n (fn-bs-meta-nth j values)))
  :hints (("Goal" :in-theory (enable fn-bs-meta-nth)
           :induct (list (fn-lim-set-nth i n values) (fn-bs-meta-nth j values)))))

; One row applied: FIELD := N; a T below the open-suffix bound lowers it too.
(defun fn-lim-apply-row (values field n)
  (declare (xargs :guard t))
  (let ((set (fn-lim-set-nth (fn-lim-field-index field) (nfix n) values)))
    (if (and (equal field "max-transactions")
             (< (nfix n) (fn-bs-pf *fn-bs-pf-max-open-suffix* values)))
        (fn-lim-set-nth *fn-bs-pf-max-open-suffix* (nfix n) set)
      set)))

; A record's change: its live :set-limit rows, in order.
(defun fn-lim-apply-deltas (values deltas)
  (declare (xargs :guard t))
  (if (consp deltas)
      (fn-lim-apply-deltas
       (let ((d (car deltas)))
         (if (and (equal (fn-cfg-delta-kind d) :set-limit)
                  (fn-lim-fieldp (fn-cfg-delta-a d)))
             (fn-lim-apply-row values (fn-cfg-delta-a d) (fn-cfg-delta-n d))
           values))
       (cdr deltas))
    values))

; The served profile: SEALED under every configuration record's live rows,
; oldest first.  RECORDS are the decoded configuration records
; (host/store-node-host.lisp fn-store-cfg-decode-records).
(defun fn-lim-effective (sealed records)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-lim-effective (fn-lim-apply-deltas sealed (fn-cfg-record-change (car records)))
                        (cdr records))
    sealed))

; KEYSTONE (a limit change is a configuration event replayed identically).
; The profile a live owner installs when it applies record R (the rows of R
; over the profile it serves) is the profile every later open computes from
; the history R ends (the host's open: fnn-load-config, the launcher's probe
; through it; the owner: fn-lim-owner-apply below).
(defthm fn-lim-effective-of-append-record
  (equal (fn-lim-effective sealed (append records (list r)))
         (fn-lim-apply-deltas (fn-lim-effective sealed records)
                              (fn-cfg-record-change r))))

; The row the verb publishes.
(defun fn-lim-deltas (field n)
  (declare (xargs :guard t))
  (list (fn-cfg-set-limit field (nfix n))))

(defthm fn-lim-apply-deltas-of-the-verb
  (implies (fn-lim-fieldp field)
           (equal (fn-lim-apply-deltas values (fn-lim-deltas field n))
                  (fn-lim-apply-row values field n)))
  :hints (("Goal" :in-theory (enable fn-cfg-set-limit fn-cfg-delta-make
                                     fn-cfg-ag-car fn-cfg-ag-cdr
                                     fn-cfg-delta-kind fn-cfg-delta-a fn-cfg-delta-n))))

; -----------------------------------------------------------------------------
; The decision

; USE is (TRANSACTIONS HISTORY-OCTETS): the store's committed transactions
; (store-budget.lisp fn-sbud-used) and the history octets charged
; (fn-sbud-bytes-used).  VALUES is the profile the configuration history
; records (fn-lim-effective over it: a change recorded for the next start
; is in it).  RUN-MB is the dynamic space the running process was started
; with (0 offline: no process holds a reservation).  CORE, NURSERY,
; OBSERVATIONS and OBSERVED are what the launcher's run reservation reads
; (heap-reservation.lisp fn-heap-status-decide,
; fn-heap-status-decide-is-the-launchers-run-reservation), so the figure
; judged here is the one the next start reserves.
;
; Answers
;   (:applied MB)                   serve the new profile now
;   (:refused :above-representation-ceiling FIELD CEILING)
;   (:at-restart MB)                recorded; the next start reserves MB
;   (:refused :not-a-live-limit FIELD 0)
;   (:refused :below-current-use FIELD USE)
;   (:refused :profile-invalid REASON 0)
;   (:refused REASON MB MACHINE-MB :resource)    the reservation's refusal
(defun fn-lim-use-of (field use)
  (declare (xargs :guard t))
  (cond ((equal field "max-transactions") (nfix (fn-cfg-ag-car use)))
        ((equal field "max-history-octets") (nfix (fn-cfg-ag-car (fn-cfg-ag-cdr use))))
        (t 0)))

; The immutable representation ceiling of a live field: the largest N the
; format can carry for it, whatever the machine or the policy.  The verb's
; row carries N in the configuration delta's u32 (config.lisp fn-cfg-deltap,
; fn-record-uint32p), so no live field passes *fn-cbor-max-uint*; T is
; further the txid width and A the article codec's
; (byte-store-frame.lisp fn-bs-profile-invalid-reason).  H's profile frame
; field is a :nat (eight octets), so a store initialised past 4 GiB of
; history keeps its sealed H but cannot raise it live: widening the row is a
; format change (D34), not a policy one.
(defun fn-lim-ceiling (field)
  (declare (xargs :guard t))
  (cond ((equal field "max-transactions")
         (min *fn-cbor-max-uint* *fn-bs-profile-transaction-ceiling*))
        ((equal field "max-history-octets") *fn-cbor-max-uint*)
        ((equal field "max-article-octets")
         (min *fn-cbor-max-uint* *fn-bs-profile-article-ceiling-codec*))
        (t 0)))

(defun fn-lim-decide (field n values use run-mb core nursery observations observed)
  (declare (xargs :guard t))
  (let ((candidate (fn-lim-apply-row values field n)))
    (cond ((not (fn-lim-fieldp field))
           (list :refused :not-a-live-limit field 0))
          ((< (fn-lim-ceiling field) (nfix n))
           (list :refused :above-representation-ceiling field (fn-lim-ceiling field)))
          ((< (nfix n) (fn-lim-use-of field use))
           (list :refused :below-current-use field (fn-lim-use-of field use)))
          ((not (fn-bs-profile-admittedp candidate))
           (list :refused :profile-invalid (fn-bs-profile-invalid-reason candidate) 0))
          (t
           (let ((d (fn-heap-status-decide candidate core nursery observations observed)))
             (if (not (and (consp d) (equal (car d) :heap)))
                 ; the reservation's reason: machine-cannot-hold-profile,
                 ; -hold-image, -hold-threads or machine-memory-unobserved.
                 (list :refused (fn-cfg-ag-car (fn-cfg-ag-cdr d))
                       (nfix (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr d))))
                       (nfix (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr d)))))
                       :resource)
               (let ((mb (fn-heap-decision-mb d)))
                 (if (and (posp run-mb) (<= mb (nfix run-mb)))
                     (list :applied mb)
                   (list :at-restart mb)))))))))

(defun fn-lim-acceptedp (d)
  (declare (xargs :guard t))
  (and (consp d) (member-equal (car d) '(:applied :at-restart)) t))

; KEYSTONE (the served state never exceeds the new limit after it takes
; effect).  An accepted change leaves an admitted profile, and the store's
; committed transactions and history octets at or below the new bound; the
; admission (store-budget.lisp fn-sbud-admitp: used < T) keeps them there.
; An :applied change's figure fits the reservation the process holds.
(defthm fn-lim-decide-accepted-keeps-use-within
  (let ((d (fn-lim-decide field n values use run-mb core nursery observations observed))
        (p (fn-lim-apply-row values field n)))
    (implies (fn-lim-acceptedp d)
             (and (fn-lim-fieldp field)
                  (fn-bs-profile-admittedp p)
                  (<= (fn-lim-use-of field use) (nfix n))
                  (<= (nfix n) (fn-lim-ceiling field))
                  (implies (equal (car d) :applied)
                           (<= (cadr d) (nfix run-mb))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-lim-decide fn-lim-acceptedp car-cons cdr-cons
                                                 nfix posp member-equal)
                                               (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The words.  The reply line of `policy set FIELD N' for decision D; OPEN-MS
; is how long the open this process made took (the next start's is about
; that), observed by the host.  Exit 0 for an accepted change, 1 refused.

(defun fn-lim-word (x)
  (declare (xargs :guard t))
  (cond ((stringp x) x)
        ((symbolp x) (string-downcase (symbol-name x)))
        (t (fn-heap-decimal x))))

(defun fn-lim-decision-line (field n d open-ms)
  (declare (xargs :guard t))
  (let* ((d (true-list-fix d))
         (f (fn-lim-word field))
         (head (concatenate 'string "limit " f "=" (fn-heap-decimal n))))
    (cond ((equal (car d) :applied)
           (concatenate 'string "applied " head " heap=" (fn-heap-decimal (nth 1 d))
                        " MB: served now, no data moved"))
          ((equal (car d) :at-restart)
           (concatenate 'string "recorded " head
                        " effective-at-next-start: takes effect at the next restart (about "
                        (fn-heap-decimal (+ 1 (floor (nfix open-ms) 1000)))
                        " s), no data moved; the next start reserves heap="
                        (fn-heap-decimal (nth 1 d)) " MB"))
          ((equal (nth 1 d) :below-current-use)
           (concatenate 'string "refused " head " below-current-use: the store holds "
                        (fn-heap-decimal (nth 3 d))))
          ((equal (nth 1 d) :profile-invalid)
           (concatenate 'string "refused " head " profile-invalid: " (fn-lim-word (nth 2 d))))
          ((equal (nth 1 d) :not-a-live-limit)
           (concatenate 'string "refused " head " not-a-live-limit"))
          ((equal (nth 1 d) :above-representation-ceiling)
           (concatenate 'string "refused " head
                        " above-representation-ceiling: the format carries at most "
                        (fn-heap-decimal (nth 3 d))))
          (t
           (concatenate 'string "refused " head " " (fn-lim-word (nth 1 d))
                        ": heap=" (fn-heap-decimal (nth 2 d))
                        " MB machine=" (fn-heap-decimal (nth 3 d)) " MB")))))

(defthm fn-lim-decision-line-stringp
  (stringp (fn-lim-decision-line field n d open-ms))
  :rule-classes :type-prescription)

(defun fn-lim-decision-exit (d)
  (declare (xargs :guard t))
  (if (fn-lim-acceptedp d) 0 1))

; The decision's class as one word, for the control reply's reason field
; (books/native-control-reason.lisp: printable, no spaces, folded to lower
; case).  The sentence travels as the reply's line (books/native-control-
; line.lisp, kind 23: fn-lim-decision-line).
(defun fn-lim-decision-word (d)
  (declare (xargs :guard t))
  (let ((d (true-list-fix d)))
    (cond ((equal (car d) :applied) "applied")
          ((equal (car d) :at-restart) "recorded")
          (t (fn-lim-word (nth 1 d))))))

(defun fn-lim-decision-reason (d)
  (declare (xargs :guard t))
  (intern-in-package-of-symbol (fn-lim-decision-word d) 'fn-lim-decide))

; The control status a live owner answers for decision D.
(defun fn-lim-decision-status (d)
  (declare (xargs :guard t))
  (if (fn-lim-acceptedp d) :accepted :refused))

;; -----------------------------------------------------------------------------
;; Three values (GPT-6, planning/review-2026-09-29-gpt6-decisions.md section 7,
;; PRF-996).  For each live field the operator is shown
;;   requested  the configured policy: fn-lim-effective over the configuration
;;              history (a change recorded for the next start is in it);
;;   funded     the limit the running process admits under: the profile its
;;              owner installed at its open or at an :applied change, which
;;              its reservation holds; NIL with no process;
;;   ceiling    the representation's (fn-lim-ceiling), immutable.
;; Admission reads the funded profile only (the owner's served bound,
;; fn-owner-apply-limit-profile); a recorded raise does not fund.

;; The profile the running owner serves after decision D, FUNDED before it,
;; CANDIDATE the requested profile D judged (fn-lim-apply-row over the
;; history's).  The host installs exactly this (host/native/admin.lisp
;; fnn-owner-limit-serialized).
(defun fn-lim-funded-after (d funded candidate)
  (declare (xargs :guard t))
  (if (and (consp d) (equal (car d) :applied)) candidate funded))

;; KEYSTONE (a recorded change does not make the process own that memory).
;; Whatever the live owner decides, the profile it serves afterwards is the
;; one it served before unless the decision is :applied, and an :applied one
;; is the requested candidate, admitted, within the use and the ceiling,
;; whose heap figure fits the reservation this process runs in.
(defthm fn-lim-funded-after-decide
  (let* ((d (fn-lim-decide field n values use run-mb core nursery observations observed))
         (c (fn-lim-apply-row values field n))
         (f (fn-lim-funded-after d funded c)))
    (and (implies (not (equal (car d) :applied)) (equal f funded))
         (implies (equal (car d) :applied)
                  (and (equal f c)
                       (fn-bs-profile-admittedp c)
                       (<= (fn-lim-use-of field use) (nfix n))
                       (<= (nfix n) (fn-lim-ceiling field))
                       (<= (cadr d) (nfix run-mb))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-lim-decide fn-lim-funded-after car-cons cdr-cons
                                                 nfix posp)
                                               (theory 'minimal-theory)))))

;; The class of a refusal: the operator's POLICY (not a live field, below
;; the store's use), the REPRESENTATION (past the ceiling, an invalid
;; profile), or a RESOURCE (the machine or the reservation cannot hold it:
;; the same words a start that cannot fund its store refuses with,
;; heap-reservation.lisp fn-heap-reserve-report-line).  NIL when accepted.
(defun fn-lim-refusal-class (d)
  (declare (xargs :guard t))
  (let ((d (true-list-fix d)))
    (cond ((not (equal (car d) :refused)) nil)
          ((equal (nth 4 d) :resource) :resource)
          ((member-equal (nth 1 d) '(:not-a-live-limit :below-current-use)) :policy)
          (t :representation))))

;; KEYSTONE (a resource refusal is never a policy or format verdict): the
;; decision is refused as a resource exactly when the field is live, within
;; its ceiling and the store's use, the requested profile is admitted, and
;; the reservation (fn-heap-status-decide, the launcher's run reservation)
;; does not answer a heap.
(defthm fn-lim-resource-refusal-is-the-reservations
  (let ((c (fn-lim-apply-row values field n)))
    (equal (equal (fn-lim-refusal-class
                   (fn-lim-decide field n values use run-mb core nursery observations observed))
                  :resource)
           (and (fn-lim-fieldp field)
                (<= (nfix n) (fn-lim-ceiling field))
                (<= (fn-lim-use-of field use) (nfix n))
                (fn-bs-profile-admittedp c)
                (not (and (consp (fn-heap-status-decide c core nursery observations observed))
                          (equal (car (fn-heap-status-decide c core nursery observations observed))
                                 :heap))))))
  :hints (("Goal" :in-theory (union-theories '(fn-lim-decide fn-lim-refusal-class true-list-fix
                                                 true-listp car-cons cdr-cons nth nfix
                                                 member-equal (:e zp) zp)
                                               (theory 'minimal-theory)))))

(defun fn-lim-field-value (field profile)
  (declare (xargs :guard t))
  (fn-bs-pf (fn-lim-field-index field) profile))

;; One field's three values, as the operator reads them:
;;   limit max-transactions requested=R funded=U ceiling=C
;; with `funded=none' when no process runs (FUNDED NIL).
(defun fn-lim-values-line (field requested funded)
  (declare (xargs :guard t))
  (concatenate 'string "limit " (fn-lim-word field)
               " requested=" (fn-heap-decimal (fn-lim-field-value field requested))
               " funded=" (if funded (fn-heap-decimal (fn-lim-field-value field funded)) "none")
               " ceiling=" (fn-heap-decimal (fn-lim-ceiling field))))

(defthm fn-lim-values-line-stringp
  (stringp (fn-lim-values-line field requested funded))
  :rule-classes :type-prescription)

(defun fn-lim-values-lines (requested funded)
  (declare (xargs :guard t))
  (list (fn-lim-values-line "max-transactions" requested funded)
        (fn-lim-values-line "max-history-octets" requested funded)
        (fn-lim-values-line "max-article-octets" requested funded)))

;; The history's requested profile after decision D over VALUES: the
;; candidate when D is accepted (applied now or recorded for the next start:
;; either way the verb's record is published), else VALUES.
(defun fn-lim-requested-after (d values candidate)
  (declare (xargs :guard t))
  (if (fn-lim-acceptedp d) candidate values))

;; The reply of `policy set FIELD N': ACL2's decision sentence, then the
;; field's three values after it (VALUES the history's requested profile
;; before it, FUNDED the running owner's served profile, NIL offline).
(defun fn-lim-reply-line (field n d open-ms values funded)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-lim-apply-row fn-lim-decision-line
                                                            fn-lim-values-line fn-lim-funded-after
                                                            fn-lim-acceptedp)))))
  (let* ((c (fn-lim-apply-row values field n))
         (requested (fn-lim-requested-after d values c)))
    (concatenate 'string (fn-lim-decision-line field n d open-ms) "; "
                 (fn-lim-values-line field requested
                                     (and funded (fn-lim-funded-after d funded c))))))

(defthm fn-lim-reply-line-stringp
  (stringp (fn-lim-reply-line field n d open-ms values funded))
  :rule-classes :type-prescription)

;; -----------------------------------------------------------------------------
;; The running owner's carried triple (PRF-996's live report).  CARRY is
;; (REQUESTED . FUNDED): the profile the configuration history requests and
;; the profile the owner serves.  The owner sets it at its open to the
;; history's effective profile for both (host/owner-host.lisp
;; fn-owner-install-profile: the launcher reserved that profile's heap) and
;; after each accepted, published `policy set' to fn-lim-carry-after
;; (fn-owner-limit-decided).  `status' and `health' render it
;; (fn-lim-report-octets) without walking the history.

(defun fn-lim-carry-requested (carry)
  (declare (xargs :guard t))
  (if (consp carry) (car carry) nil))

(defun fn-lim-carry-funded (carry)
  (declare (xargs :guard t))
  (if (consp carry) (cdr carry) nil))

(defun fn-lim-carry-after (field n d carry)
  (declare (xargs :guard t))
  (let* ((values (fn-lim-carry-requested carry))
         (c (fn-lim-apply-row values field n)))
    (cons (fn-lim-requested-after d values c)
          (fn-lim-funded-after d (fn-lim-carry-funded carry) c))))

(defun fn-lim-lines-octets (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (append (fn-record-string-octets (car lines)) (list 10)
              (fn-lim-lines-octets (cdr lines)))
    nil))

;; The owner's report: one `limit F requested=R funded=U ceiling=C' line per
;; live field, nothing before its open carried a profile.
(defun fn-lim-report-lines (carry)
  (declare (xargs :guard t))
  (if (fn-lim-carry-requested carry)
      (fn-lim-values-lines (fn-lim-carry-requested carry) (fn-lim-carry-funded carry))
    nil))

(defun fn-lim-report-octets (carry)
  (declare (xargs :guard t))
  (fn-lim-lines-octets (fn-lim-report-lines carry)))

;; KEYSTONE (the reported triple is the decision's triple).  After the
;; running owner decides `policy set FIELD N' (D) over its carry
;; (VALUES . FUNDED), the reply names FIELD's requested, funded and ceiling
;; values, and those are exactly the ones the owner's status and health then
;; report for FIELD from the carry it keeps (fn-lim-carry-after): the reply's
;; line is the decision sentence followed by the report's line for FIELD,
;; and that line is one of the report's lines.  The subject is
;; fn-lim-reply-line (host/native/admin.lisp fnn-lim-line) and
;; fn-lim-report-lines under fn-lim-report-octets
;; (host/native-live-status-host.lisp fn-native-live-status-host-answer
;; through fn-owner-limit-report).
(defthm fn-lim-reported-triple-is-the-decisions
  (let* ((after (fn-lim-carry-after field n d (cons values funded)))
         (line (fn-lim-values-line field (fn-lim-carry-requested after)
                                   (fn-lim-carry-funded after))))
    (implies (and (fn-lim-fieldp field) values funded)
             (and (equal (fn-lim-reply-line field n d open-ms values funded)
                         (concatenate 'string (fn-lim-decision-line field n d open-ms)
                                      "; " line))
                  (member-equal line (fn-lim-report-lines after)))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-lim-carry-after fn-lim-carry-requested
                                fn-lim-carry-funded fn-lim-reply-line
                                fn-lim-report-lines fn-lim-values-lines
                                fn-lim-fieldp fn-lim-requested-after
                                fn-lim-funded-after member-equal
                                car-cons cdr-cons fn-lim-apply-row
                                (:type-prescription fn-lim-set-nth))
                              (theory 'minimal-theory)))))

;; KEYSTONE (the carry is the history's, without walking it).  When the
;; carried requested profile is the history's (fn-lim-effective over its
;; configuration records, what every open computes: host/store-node-host.lisp
;; fn-store-lim-effective), it stays the history's after a decision: an
;; accepted one publishes the verb's record (fn-lim-deltas) and the carry
;; becomes the history that record ends; a refused one publishes nothing and
;; the carry is unchanged.
(defthm fn-lim-carry-after-is-the-history
  (implies (and (equal (fn-lim-carry-requested carry) (fn-lim-effective sealed records))
                (fn-lim-fieldp field))
           (equal (fn-lim-carry-requested (fn-lim-carry-after field n d carry))
                  (if (fn-lim-acceptedp d)
                      (fn-lim-effective sealed
                                        (append records
                                                (list (fn-cfg-record-make
                                                       s tx gen (fn-lim-deltas field n)
                                                       stamp))))
                    (fn-lim-effective sealed records))))
  :hints (("Goal" :in-theory (e/d (fn-lim-carry-after fn-lim-requested-after)
                                  (fn-lim-apply-row fn-lim-deltas fn-lim-acceptedp)))))

(in-theory (disable fn-lim-decide fn-lim-effective fn-lim-apply-deltas))
