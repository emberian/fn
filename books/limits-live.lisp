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
(include-book "heap-figure")

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
                                     fn-cfg-delta-kind fn-cfg-delta-a fn-cfg-delta-n))))

; -----------------------------------------------------------------------------
; The decision

; USE is (TRANSACTIONS HISTORY-OCTETS): the store's committed transactions
; (store-budget.lisp fn-sbud-used) and the history octets charged
; (fn-sbud's bytes).  RUN-MB is the dynamic space the running process was
; started with (the launcher's heap=, observed by the host; 0 offline: no
; process holds a reservation).  CORE, NURSERY and OBSERVATIONS are
; heap-figure.lisp fn-heap-decide's.
;
; Answers
;   (:applied MB)                   serve the new profile now
;   (:at-restart MB)                recorded; the next start reserves MB
;   (:refused :not-a-live-limit FIELD 0)
;   (:refused :below-current-use FIELD USE)
;   (:refused :profile-invalid REASON 0)
;   (:refused :machine-cannot-hold-profile MB MACHINE-MB)
(defun fn-lim-use-of (field use)
  (declare (xargs :guard t))
  (cond ((equal field "max-transactions") (nfix (fn-cfg-ag-car use)))
        ((equal field "max-history-octets") (nfix (fn-cfg-ag-car (fn-cfg-ag-cdr use))))
        (t 0)))

(defun fn-lim-decide (field n values use run-mb core nursery observations)
  (declare (xargs :guard t))
  (let ((candidate (fn-lim-apply-row values field n)))
    (cond ((not (fn-lim-fieldp field))
           (list :refused :not-a-live-limit field 0))
          ((< (nfix n) (fn-lim-use-of field use))
           (list :refused :below-current-use field (fn-lim-use-of field use)))
          ((not (fn-bs-profile-admittedp candidate))
           (list :refused :profile-invalid (fn-bs-profile-invalid-reason candidate) 0))
          (t
           (let ((d (fn-heap-decide candidate core nursery observations)))
             (if (not (equal (car d) :heap))
                 (list :refused :machine-cannot-hold-profile
                       (nfix (caddr d)) (nfix (cadddr d)))
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
  (let ((d (fn-lim-decide field n values use run-mb core nursery observations))
        (p (fn-lim-apply-row values field n)))
    (implies (fn-lim-acceptedp d)
             (and (fn-lim-fieldp field)
                  (fn-bs-profile-admittedp p)
                  (<= (fn-lim-use-of field use) (nfix n))
                  (implies (equal (car d) :applied)
                           (<= (cadr d) (nfix run-mb)))))))

(in-theory (disable fn-lim-decide fn-lim-effective fn-lim-apply-deltas))
