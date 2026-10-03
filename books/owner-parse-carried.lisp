;; fn: the owner POST's article parsed once, at take, and carried.
;
; An owner POST parsed the same article about thirteen times on the owner
; side (hbox probe of fn-article-parse-under by caller, one 2 KiB POST, N =
; 1,000; lane post-alloc-2): at take twice (fn-icar-carry-of's Path and the
; Cancel-Lock fields of fn-own-sub-stored-octets) and a third time through
; fn-ores-take-result's own fn-icar-carry-of; at the intent twice (the
; control groups and the Distribution); the control filing once; the
; carrier form once; the transit verdict three times (fn-pa-current-plan
; under the verdict, the admission verdict and the refusal class); the
; prepare twice (the row's held context: the verdict and the delta); the
; finish once (the Cancel-Lock fields again).  About 28 KB consed each.
;
; The carry is an alist ((OCTETS . PARSE) ...): each PARSE is
; fn-article-parse of its OCTETS (fn-apc-p).  fn-apc-take builds it from the
; submission fn-owner-take (host/owner-host.lisp) just took: the
; submission's octets, the injected octets and the stored octets, each
; parsed once when it is not already an entry (for a served POST without a
; login the three are one list: one parse).  That is the host's only writer
; of the global 'fn-owner-parse-carry, and fn-apc-p mentions no owner, so no
; owner step can falsify it (nil, the global's value before the first
; take, satisfies it).  A reader looks the octets it is given up by EQUAL
; (EQ on the list the take left, a compare without allocation on a copy)
; and parses when they are not there, so a stale carry costs a parse and
; never a wrong answer: fn-apc-parse-is-article-parse.
;
; Every consumer below is its reference with fn-article-parse replaced by
; fn-apc-parse and is proved equal to it under fn-apc-p.  The host calls:
;   fn-owner-take                 fn-apc-take, fn-apc-icar-carry-of,
;                                 fn-apc-take-result
;   fn-owner-submission-intent    fn-apc-submission-intent
;   fn-owner-submission-resolution fn-apc-submission-resolution-publication
;   fn-owner-control-filing       fn-apc-filing-plan (hybrid-control only;
;                                 the served attempt reads the buffer,
;                                 books/article-buffer.lisp)
;   fn-owner-peer-carrier-plan    fn-apc-current-plan
;   fn-owner-transit-verdict      fn-apc-transit-verdict
;   fn-owner-transit-refusal-class fn-apc-transit-refusal-detail
;   fn-owner-prepare-buffer       fn-apc-intern-row-at
;   fn-owner-finish-submission    fn-apc-own-finish
; The parsed form is the article parser's own result (fields, header,
; body), never octets.

(in-package "ACL2")
(include-book "owner-commit-carried")
(include-book "owner-refresh-indexed")
(include-book "owner-results")
(include-book "peer-carriage")
(include-book "owner-advance-carried")

; -----------------------------------------------------------------------------
; The carry.

; The parser stays shut: no theorem here is about its grammar.
(local (in-theory (disable fn-article-parse)))

(defun fn-apc-find (octets carry)
  (declare (xargs :guard t))
  (cond ((atom carry) nil)
        ((and (consp (car carry)) (equal (caar carry) octets)) (car carry))
        (t (fn-apc-find octets (cdr carry)))))

(defun fn-apc-p (carry)
  (declare (xargs :guard t))
  (if (atom carry)
      t
    (and (consp (car carry))
         (equal (cdar carry) (fn-article-parse (caar carry)))
         (fn-apc-p (cdr carry)))))

; The entry's shape is tested (a true list, as every parse result is) so
; the readers' guards hold over any carry, not only one fn-apc-p accepts.
(defun fn-apc-parse (octets carry)
  (declare (xargs :guard t))
  (let ((e (fn-apc-find octets carry)))
    (if (and e (true-listp (cdr e))) (cdr e) (fn-article-parse octets))))

(local
 (defthm fn-apc-find-is-its-parse
   (implies (and (fn-apc-p carry) (fn-apc-find octets carry))
            (equal (cdr (fn-apc-find octets carry))
                   (fn-article-parse octets)))))

; KEYSTONE: whatever octets a reader is given and whatever carry the global
; holds, the carried parse is the parse of those octets.
(defthm fn-apc-parse-is-article-parse
  (implies (fn-apc-p carry)
           (equal (fn-apc-parse octets carry) (fn-article-parse octets))))

(defun fn-apc-extend (octets carry)
  (declare (xargs :guard t))
  (if (fn-apc-find octets carry)
      carry
    (cons (cons octets (fn-article-parse octets)) carry)))

(defthm fn-apc-p-of-extend
  (implies (fn-apc-p carry) (fn-apc-p (fn-apc-extend octets carry))))

(defthm fn-apc-p-when-atom
  (implies (atom carry) (fn-apc-p carry)))

(in-theory (disable fn-apc-find fn-apc-p fn-apc-parse fn-apc-extend))

; -----------------------------------------------------------------------------
; The five direct parse sites, over the carried parse.

; books/owner-feed.lisp fn-own-feed-article-of.
(defun fn-apc-feed-article-of (octets carry)
  (declare (xargs :guard t))
  (let ((parsed (fn-apc-parse octets carry)))
    (if (and (fn-article-result-okp parsed)
             (true-listp parsed)
             (fn-article-syntax-p (fn-article-result-article parsed)))
        (fn-article-result-article parsed)
      nil)))

(defthm fn-apc-feed-article-of-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-feed-article-of octets carry)
                  (fn-own-feed-article-of octets)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-article-of)
                                  (fn-article-parse fn-article-syntax-p)))))

(defthm fn-apc-feed-article-of-is-syntax
  (implies (fn-apc-feed-article-of octets carry)
           (fn-article-syntax-p (fn-apc-feed-article-of octets carry))))

; books/control-authority.lisp fn-ctl-received-fields.
(defun fn-apc-received-fields (received carry)
  (declare (xargs :guard t))
  (let ((parsed (fn-apc-parse received carry)))
    (if (fn-article-result-okp parsed)
        (let ((article (fn-article-result-article parsed)))
          (if (true-listp article) (fn-article-fields article) nil))
      nil)))

(defthm fn-apc-received-fields-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-received-fields received carry)
                  (fn-ctl-received-fields received)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-received-fields)
                                  (fn-article-parse)))))

; books/control-classify.lisp fn-ctl-classify-octets.
(defun fn-apc-classify-octets (received carry)
  (declare (xargs :guard t))
  (let ((parsed (fn-apc-parse received carry)))
    (if (fn-article-result-okp parsed)
        (fn-ctl-classify (fn-article-result-article parsed))
      :unparsed)))

(defthm fn-apc-classify-octets-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-classify-octets received carry)
                  (fn-ctl-classify-octets received)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-classify-octets)
                                  (fn-article-parse fn-ctl-classify)))))

; books/peer-authored-accept.lisp fn-pa-carrier-kind.
(defun fn-apc-carrier-kind (received carry)
  (declare (xargs :guard t))
  (let ((parsed (fn-apc-parse received carry)))
    (if (not (fn-article-result-okp parsed))
        :invalid
      (let ((article (fn-article-result-article parsed)))
        (if (not (true-listp article)) :invalid
          (if (equal (fn-hc-count-name
                      *fn-hc-name* (fn-article-fields article)) 0)
              :absent
            :present))))))

(defthm fn-apc-carrier-kind-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-carrier-kind received carry)
                  (fn-pa-carrier-kind received)))
  :hints (("Goal" :in-theory (e/d (fn-pa-carrier-kind)
                                  (fn-article-parse fn-hc-count-name)))))

; books/stx-lace.lisp fn-stx-parse.
(defun fn-apc-stx-parse (octets carry)
  (declare (xargs :guard t))
  (let ((r (fn-apc-parse octets carry)))
    (if (not (and (true-listp r) (fn-article-result-okp r)))
        nil
      (let ((a (fn-article-result-article r)))
        (if (fn-article-syntax-p a) a nil)))))

(defthm fn-apc-stx-parse-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-stx-parse octets carry)
                  (fn-stx-parse octets)))
  :hints (("Goal" :in-theory (e/d ((:d fn-stx-parse))
                                  (fn-article-parse fn-article-syntax-p)))))

(defthm fn-apc-stx-parse-is-syntax-article
  (implies (fn-apc-stx-parse octets carry)
           (fn-article-syntax-p (fn-apc-stx-parse octets carry))))

(in-theory (disable fn-apc-feed-article-of fn-apc-received-fields
                    fn-apc-classify-octets fn-apc-carrier-kind
                    fn-apc-stx-parse))

; -----------------------------------------------------------------------------
; The take: the carry's writer, the stored octets and the intent carry.

; books/cancel-lock.lisp fn-cl-served-payload.
(defun fn-apc-cl-served-payload (ring account msgid payload carry)
  (declare (xargs :guard t))
  (let ((fields (fn-apc-received-fields payload carry)))
    (fn-cll-append (fn-cll-lines (fn-cl-lock-value ring account msgid fields)
                                 (fn-cl-key-values ring account fields))
                   payload)))

(defthm fn-apc-cl-served-payload-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-cl-served-payload ring account msgid payload carry)
                  (fn-cl-served-payload ring account msgid payload)))
  :hints (("Goal" :in-theory (e/d (fn-cl-served-payload)
                                  (fn-ctl-received-fields fn-cll-append
                                   fn-cll-lines fn-cl-lock-value
                                   fn-cl-key-values)))))

; books/owner-served-invariants.lisp fn-own-sub-stored-octets.
(defun fn-apc-sub-stored-octets (cfg sub secret carry)
  (declare (xargs :guard t))
  (let ((d (fn-own-sub-decision sub)))
    (if (fn-peer-submissionp d)
        (fn-peer-relayed-octets cfg (fn-peer-submission-peer d)
                                (fn-peer-submission-octets d))
      (fn-apc-cl-served-payload secret (fn-own-sub-account sub)
                                (fn-inj-decision-msgid d)
                                (fn-ipp-injected-octets d secret (fn-own-sub-account sub)
                                                        cfg)
                                carry))))

(defthm fn-apc-sub-stored-octets-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-sub-stored-octets cfg sub secret carry)
                  (fn-own-sub-stored-octets cfg sub secret)))
  :hints (("Goal" :in-theory (e/d (fn-own-sub-stored-octets)
                                  (fn-cl-served-payload fn-apc-cl-served-payload
                                   fn-peer-relayed-octets
                                   fn-ipp-injected-octets)))))

(in-theory (disable fn-apc-cl-served-payload fn-apc-sub-stored-octets))

; THE WRITER (host/owner-host.lisp fn-owner-take): (STORED . CARRY).  The
; submission's octets are parsed; the injected octets and the stored octets
; are parsed only when they are not already an entry.
(defun fn-apc-take (cfg sub secret)
  (declare (xargs :guard t))
  (let ((d (fn-own-sub-decision sub))
        (carry (fn-apc-extend (fn-own-sub-octets sub) nil)))
    (if (fn-peer-submissionp d)
        (let ((stored (fn-peer-relayed-octets cfg (fn-peer-submission-peer d)
                                              (fn-peer-submission-octets d))))
          (cons stored (fn-apc-extend stored carry)))
      (let* ((injected (fn-ipp-injected-octets d secret (fn-own-sub-account sub)
                                               cfg))
             (carry (fn-apc-extend injected carry))
             (stored (fn-apc-cl-served-payload secret (fn-own-sub-account sub)
                                               (fn-inj-decision-msgid d)
                                               injected carry)))
        (cons stored (fn-apc-extend stored carry))))))

; KEYSTONE (no hypothesis): the octets the take hands the host are
; fn-own-sub-stored-octets, and the carry it leaves satisfies fn-apc-p.
(defthm fn-apc-take-stores-the-stored-octets
  (equal (car (fn-apc-take cfg sub secret))
         (fn-own-sub-stored-octets cfg sub secret))
  :hints (("Goal" :in-theory '(fn-apc-take fn-apc-sub-stored-octets car-cons
                               fn-apc-p-of-extend fn-apc-p-when-atom)
           :use ((:instance fn-apc-sub-stored-octets-is-reference
                            (carry (fn-apc-extend
                                    (fn-ipp-injected-octets
                                     (fn-own-sub-decision sub) secret
                                     (fn-own-sub-account sub) cfg)
                                    (fn-apc-extend (fn-own-sub-octets sub)
                                                   nil))))))))

(defthm fn-apc-p-of-take
  (fn-apc-p (cdr (fn-apc-take cfg sub secret)))
  :hints (("Goal" :in-theory '(fn-apc-take cdr-cons fn-apc-p-of-extend
                               fn-apc-p-when-atom))))

(in-theory (disable fn-apc-take))

; books/owner-feed.lisp fn-own-feed-path-of.
(defun fn-apc-feed-path-of (octets carry)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :use fn-apc-feed-article-of-is-syntax
                                 :in-theory (disable fn-apc-feed-article-of-is-syntax)))))
  (let ((a (fn-apc-feed-article-of octets carry)))
    (if (null a) nil (fn-af-path-field-value a))))

(defthm fn-apc-feed-path-of-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-feed-path-of octets carry)
                  (fn-own-feed-path-of octets)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-path-of)
                                  (fn-own-feed-article-of
                                   fn-af-path-field-value)))))

; books/owner-intent-carried.lisp fn-icar-carry-of, its Path from the carry.
(defun fn-apc-icar-carry-of (sub carry)
  (declare (xargs :guard t))
  (list* sub
         (fn-own-feed-intent-id (fn-own-sub-msgid sub) (fn-own-sub-octets sub))
         (fn-apc-feed-path-of (fn-own-sub-octets sub) carry)))

(defthm fn-apc-icar-carry-of-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-icar-carry-of sub carry)
                  (fn-icar-carry-of sub)))
  :hints (("Goal" :in-theory (e/d (fn-icar-carry-of)
                                  (fn-apc-feed-path-of fn-own-feed-path-of
                                   fn-own-feed-intent-id)))))

(defthm fn-icar-carryp-of-apc-icar-carry-of
  (implies (fn-apc-p carry)
           (fn-icar-carryp (fn-apc-icar-carry-of sub carry)))
  :hints (("Goal" :in-theory (disable fn-apc-icar-carry-of))))

; books/owner-results.lisp fn-ores-take-result with its INTENT field given:
; the reference computes fn-icar-carry-of a second time for it.
(defun fn-apc-take-result (sub stored intent)
  (declare (xargs :guard t))
  (let ((decision (fn-own-sub-decision sub))
        (transitp (fn-own-transit-subp sub)))
    (fn-ores-submission-taken
     (fn-ores-take-word sub)
     (fn-own-sub-id sub)
     (if transitp
         (fn-peer-submission-msgid decision)
       (fn-inj-decision-msgid decision))
     stored
     (if transitp nil (fn-inj-decision-groups decision))
     intent
     transitp
     (if transitp (fn-peer-submission-peer decision) nil))))

; KEYSTONE for the host line (fn-owner-take): the three calls it makes are
; the SubmissionTaken of the stored octets, and the intent carry it writes
; is fn-icar-carry-of of the submission, for every configuration, submission
; and secret.
(defthm fn-apc-take-is-take-result
  (let* ((tk (fn-apc-take cfg sub secret))
         (intent (fn-apc-icar-carry-of sub (cdr tk))))
    (and (equal (fn-apc-take-result sub (car tk) intent)
                (fn-ores-take-result sub (fn-own-sub-stored-octets cfg sub secret)))
         (equal intent (fn-icar-carry-of sub))))
  :hints (("Goal" :in-theory (e/d (fn-ores-take-result)
                                  (fn-apc-icar-carry-of fn-icar-carry-of
                                   fn-ores-take-word)))))

(in-theory (disable fn-apc-feed-path-of fn-apc-icar-carry-of fn-apc-take-result))

; -----------------------------------------------------------------------------
; The intent and the resolution: the feed's views of the submission's octets.

; books/owner-feed.lisp fn-own-feed-groups-of (a transit submission's base
; groups).
(defun fn-apc-feed-groups-of (octets carry)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :use fn-apc-feed-article-of-is-syntax
                                 :in-theory (disable fn-apc-feed-article-of-is-syntax)))))
  (let ((a (fn-apc-feed-article-of octets carry)))
    (if (null a)
        nil
      (let ((check (fn-af-relayed-article-check a)))
        (if (equal (fn-af-status-kind check) :ok)
            (fn-frame-item 2 check)
          nil)))))

(defthm fn-apc-feed-groups-of-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-feed-groups-of octets carry)
                  (fn-own-feed-groups-of octets)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-groups-of)
                                  (fn-own-feed-article-of
                                   fn-af-relayed-article-check)))))

; books/owner-feed.lisp fn-own-feed-distributions-of.
(defun fn-apc-feed-distributions-of (octets carry)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :use fn-apc-feed-article-of-is-syntax
                                 :in-theory (disable fn-apc-feed-article-of-is-syntax)))))
  (let ((a (fn-apc-feed-article-of octets carry)))
    (if (null a)
        :absent
      (let ((fields (fn-article-get-headers a *fn-own-feed-distribution-name*)))
        (if (atom fields)
            :absent
          (let ((value (fn-path-single-field-value
                        a *fn-own-feed-distribution-name*)))
            (if (consp value) (fn-own-feed-dist-list value) :malformed)))))))

(defthm fn-apc-feed-distributions-of-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-feed-distributions-of octets carry)
                  (fn-own-feed-distributions-of octets)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-distributions-of)
                                  (fn-own-feed-article-of
                                   fn-article-get-headers
                                   fn-path-single-field-value
                                   fn-own-feed-dist-list)))))

; books/owner.lisp fn-own-feed-control-groups-of.
(defun fn-apc-feed-control-groups-of (octets carry)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :use fn-apc-feed-article-of-is-syntax
                                 :in-theory (disable fn-apc-feed-article-of-is-syntax
                                                     fn-ctl-classify
                                                     fn-ctl-filing-group
                                                     fn-record-string-octets)))))
  (let ((a (fn-apc-feed-article-of octets carry)))
    (if (null a)
        nil
      (let ((c (fn-ctl-classify a)))
        (if (and (consp c) (eq (car c) :control) (consp (cdr c)))
            (cons (fn-record-string-octets (fn-ctl-filing-group (cadr c)))
                  (let ((check (fn-af-relayed-article-check a)))
                    (if (equal (fn-af-status-kind check) :ok)
                        (fn-frame-item 2 check)
                      nil)))
          nil)))))

(defthm fn-apc-feed-control-groups-of-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-feed-control-groups-of octets carry)
                  (fn-own-feed-control-groups-of octets)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-control-groups-of)
                                  (fn-own-feed-article-of fn-ctl-classify
                                   fn-ctl-filing-group fn-record-string-octets
                                   fn-af-relayed-article-check)))))

(in-theory (disable fn-apc-feed-groups-of fn-apc-feed-distributions-of
                    fn-apc-feed-control-groups-of))

; books/owner.lisp fn-own-sub-feed-base-groups and fn-own-sub-feed-groups.
(defun fn-apc-sub-feed-groups (sub carry)
  (declare (xargs :guard t))
  (let* ((d (fn-own-sub-decision sub))
         (base (if (fn-peer-submissionp d)
                   (fn-apc-feed-groups-of (fn-own-sub-octets sub) carry)
                 (fn-inj-decision-groups d)))
         (ctl (fn-apc-feed-control-groups-of (fn-own-sub-octets sub) carry)))
    (if (consp ctl)
        (append (true-list-fix base) ctl)
      base)))

(defthm fn-apc-sub-feed-groups-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-sub-feed-groups sub carry)
                  (fn-own-sub-feed-groups sub)))
  :hints (("Goal" :in-theory (e/d (fn-own-sub-feed-groups
                                   fn-own-sub-feed-base-groups)
                                  (fn-own-feed-groups-of
                                   fn-own-feed-control-groups-of
                                   fn-own-sub-octets)))))

; books/owner-intent-carried.lisp fn-icar-submission-targets over the carry.
(defun fn-apc-submission-targets (o icar carry)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (if (null sub)
        nil
      (let* ((tbl (fn-own-feeds o))
             (msgid (fn-own-sub-msgid sub))
             (groups (fn-apc-sub-feed-groups sub carry))
             (targets (if (fn-mod-names-a-queuep
                           groups (fn-inj-config-closed (fn-own-config o)))
                          nil
                        (fn-own-feed-distribution-targets
                         (fn-own-feed-targets
                          tbl (fn-own-sub-origin sub) groups
                          (fn-icar-path sub icar))
                         tbl (fn-apc-feed-distributions-of
                              (fn-own-sub-octets sub) carry)))))
        (fn-own-feed-new-targets targets tbl msgid)))))

(defthm fn-apc-submission-targets-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-submission-targets o icar carry)
                  (fn-icar-submission-targets o icar)))
  :hints (("Goal" :in-theory (e/d (fn-icar-submission-targets)
                                  (fn-apc-sub-feed-groups fn-own-sub-feed-groups
                                   fn-icar-path fn-own-feed-targets
                                   fn-own-feed-new-targets
                                   fn-own-feed-distribution-targets
                                   fn-own-feed-distributions-of
                                   fn-mod-names-a-queuep)))))

(in-theory (disable fn-apc-sub-feed-groups fn-apc-submission-targets))

; books/owner-intent-carried.lisp fn-icar-submission-intent: the host's call
; at the intent (fn-owner-submission-intent).
(defun fn-apc-submission-intent (o icar carry evidence generation txid)
  (declare (xargs :guard t))
  (let* ((sub (fn-own-inflight o))
         (identity (and sub (fn-icar-intent-id sub icar)))
         (targets (fn-apc-submission-targets o icar carry))
         (result
          (cond ((null sub) :absent)
                ((or (not (fn-feed-namep identity))
                     (not (fn-feed-namep evidence))
                     (not (natp generation)) (not (natp txid)))
                 :refused)
                ((not (fn-own-feed-target-capacityp
                       targets (fn-own-feeds o) (fn-own-sub-msgid sub)))
                 :capacity)
                (t :ready))))
    (cons result
          (if (equal result :ready)
              (fn-own-feed-intent-records
               targets (fn-own-sub-msgid sub) identity
               evidence generation txid (fn-own-feed-stamp o))
            nil))))

(defthm fn-apc-submission-intent-is-icar
  (implies (fn-apc-p carry)
           (equal (fn-apc-submission-intent o icar carry evidence generation txid)
                  (fn-icar-submission-intent o icar evidence generation txid)))
  :hints (("Goal" :in-theory (e/d (fn-icar-submission-intent)
                                  (fn-apc-submission-targets
                                   fn-icar-submission-targets
                                   fn-icar-intent-id
                                   fn-own-feed-target-capacityp
                                   fn-own-feed-intent-records
                                   fn-feed-namep)))))

; KEYSTONE for the host line: under the two carries fn-owner-take writes,
; the intent is the owner.lisp reference's result and records.
(defthm fn-apc-submission-intent-is-reference
  (implies (and (fn-apc-p carry) (fn-icar-carryp icar))
           (equal (fn-apc-submission-intent o icar carry evidence generation txid)
                  (cons (fn-own-submission-intent-result o evidence generation txid)
                        (fn-own-submission-intent-records o evidence generation txid))))
  :hints (("Goal" :in-theory (disable fn-apc-submission-intent
                                      fn-icar-submission-intent))))

; books/owner-intent-carried.lisp fn-icar-submission-resolution-records.
(defun fn-apc-submission-resolution-records (o icar carry word evidence generation txid)
  (declare (xargs :guard t))
  (let* ((sub (fn-own-inflight o))
         (completion (fn-own-outcome-completion o word))
         (kind (cond ((equal completion :durable) :feed-commit)
                     ((member-equal completion '(:refused :clock-unusable))
                      :feed-abort)
                     (t nil))))
    (if (or (null sub) (null kind))
        nil
      (fn-own-feed-resolution-records
       kind (fn-apc-submission-targets o icar carry) (fn-own-sub-msgid sub)
       (fn-icar-intent-id sub icar)
       evidence generation txid (fn-own-feed-stamp o)))))

(defthm fn-apc-submission-resolution-records-is-icar
  (implies (fn-apc-p carry)
           (equal (fn-apc-submission-resolution-records
                   o icar carry word evidence generation txid)
                  (fn-icar-submission-resolution-records
                   o icar word evidence generation txid)))
  :hints (("Goal" :in-theory (e/d (fn-icar-submission-resolution-records)
                                  (fn-apc-submission-targets
                                   fn-icar-submission-targets
                                   fn-icar-intent-id
                                   fn-own-outcome-completion
                                   fn-own-feed-resolution-records)))))

; books/owner-results.lisp fn-ores-submission-resolution-publication: the
; host's call at the resolution (fn-owner-submission-resolution).
(defun fn-apc-submission-resolution-publication
    (o icar carry word evidence generation txid)
  (declare (xargs :guard t :verify-guards nil))
  (let ((records (fn-apc-submission-resolution-records
                  o icar carry word evidence generation txid)))
    (fn-ores-feed-port-publication (fn-ores-resolution-word o word records)
                                   records nil (fn-ores-inflight-token o) nil)))
(verify-guards fn-apc-submission-resolution-publication)

; KEYSTONE for the host line.
(defthm fn-apc-submission-resolution-publication-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-submission-resolution-publication
                   o icar carry word evidence generation txid)
                  (fn-ores-submission-resolution-publication
                   o icar word evidence generation txid)))
  :hints (("Goal" :in-theory (e/d (fn-ores-submission-resolution-publication)
                                  (fn-apc-submission-resolution-records
                                   fn-icar-submission-resolution-records
                                   fn-ores-resolution-word
                                   fn-ores-feed-port-publication
                                   fn-ores-inflight-token)))))

(in-theory (disable fn-apc-submission-intent fn-apc-submission-resolution-records
                    fn-apc-submission-resolution-publication))

; -----------------------------------------------------------------------------
; The ingress decisions over the stored octets.

; books/peer-authored-accept.lisp fn-pa-filing-plan (fn-owner-control-filing).
(defun fn-apc-filing-plan (received groups domain carry)
  (declare (xargs :guard t))
  (let ((classified (fn-apc-classify-octets received carry)))
    (cond ((and (consp classified) (eq (car classified) :malformed))
           (list :refused :control-malformed))
          ((and (consp classified) (eq (car classified) :control))
           (let ((group (fn-ctl-filing-group (cadr classified))))
             (if (fn-ctl-memberp group domain)
                 (list :file (list (fn-record-string-octets group)))
               (list :refused :control-not-filed))))
          (t (list :file groups)))))

; KEYSTONE for the host line.
(defthm fn-apc-filing-plan-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-filing-plan received groups domain carry)
                  (fn-pa-filing-plan received groups domain)))
  :hints (("Goal" :in-theory (e/d (fn-pa-filing-plan)
                                  (fn-ctl-classify-octets fn-ctl-filing-group
                                   fn-ctl-memberp fn-record-string-octets)))))

; -----------------------------------------------------------------------------
; The carrier plan, decided once per POST (PKT-552).  A signed POST's
; fn-hc-received-plan (the article parse, the carrier field's decode and the
; authored source's parse) was decided by the carrier form, again by each
; current plan (two per transit verdict) and by the refusal detail.  PLANS is
; a one-entry alist ((RECEIVED . PLAN)) whose PLAN is fn-hc-received-plan of
; RECEIVED (fn-apc-plansp); the host extends it (fn-apc-plans-extend) before
; each reader, so the plan is computed on the first and read on the others.
; A missing or stale entry costs a computation, never a wrong answer
; (fn-apc-plan-is-received-plan).

; fn-hc-received-plan with the article's parse read from the parse carry.
(defun fn-apc-hc-received-plan (original carry)
  (declare (xargs :guard t))
  (let ((parsed (fn-apc-parse original carry)))
    (if (not (and (fn-article-result-okp parsed)
                  (true-listp parsed)))
        (fn-hc-error :article original)
      (let* ((article (fn-article-result-article parsed))
             (fields (if (true-listp article)
                         (fn-article-fields article) nil))
             (source (fn-hc-authored-source article)))
        (if (not (and (true-listp article)
                      (equal (fn-hc-count-name *fn-hc-name* fields) 1)
                      (fn-hc-no-other-reservedp fields)))
            (fn-hc-error :carrier-count original)
          (let ((field (fn-hc-find-name *fn-hc-name* fields)))
            (if (not (true-listp field))
                (fn-hc-error :carrier original)
              (let ((carrier (fn-hc-field-decode-at
                              (fn-hsig-source-version source)
                              (fn-article-field-unfolded-value field))))
                (if (not (fn-hc-okp carrier))
                    (fn-hc-error :carrier original)
                  (let* ((source-parsed (fn-article-parse source)))
                    (if (not (and (fn-article-result-okp source-parsed)
                                  (true-listp source-parsed)
                                  (true-listp
                                   (fn-article-result-article source-parsed))
                                  (fn-hc-required-sourcep
                                   (fn-article-result-article source-parsed))
                                  (fn-hc-fields-nativep
                                   (fn-article-fields
                                    (fn-article-result-article source-parsed)))))
                        (fn-hc-error :source-profile original)
                      (fn-hc-ok (list source (fn-hc-value carrier))))))))))))))

(defthm fn-apc-hc-received-plan-is-received-plan
  (implies (fn-apc-p carry)
           (equal (fn-apc-hc-received-plan original carry)
                  (fn-hc-received-plan original)))
  :hints (("Goal" :in-theory (e/d (fn-hc-received-plan)
                                  (fn-apc-parse fn-hc-authored-source
                                   fn-hc-count-name fn-hc-no-other-reservedp
                                   fn-hc-find-name fn-hc-field-decode-at
                                   fn-hsig-source-version fn-hc-required-sourcep
                                   fn-hc-fields-nativep fn-hc-okp fn-hc-value
                                   fn-hc-error fn-hc-ok)))))

(defun fn-apc-plansp (plans)
  (declare (xargs :guard t))
  (if (atom plans)
      t
    (and (consp (car plans))
         (equal (cdar plans) (fn-hc-received-plan (caar plans)))
         (fn-apc-plansp (cdr plans)))))

(defun fn-apc-plan (received plans carry)
  (declare (xargs :guard t))
  (let ((hit (fn-apc-find received plans)))
    (if hit (cdr hit) (fn-apc-hc-received-plan received carry))))

(local
 (defthm fn-apc-find-in-plans
   (implies (and (fn-apc-plansp plans) (fn-apc-find received plans))
            (equal (cdr (fn-apc-find received plans))
                   (fn-hc-received-plan received)))
   :hints (("Goal" :induct (fn-apc-plansp plans)
            :in-theory (e/d (fn-apc-find) (fn-hc-received-plan))))))

; KEYSTONE: every reader of the carried plan reads fn-hc-received-plan.
(defthm fn-apc-plan-is-received-plan
  (implies (and (fn-apc-p carry) (fn-apc-plansp plans))
           (equal (fn-apc-plan received plans carry)
                  (fn-hc-received-plan received)))
  :hints (("Goal" :in-theory (e/d (fn-apc-plan)
                                  (fn-hc-received-plan
                                   fn-apc-hc-received-plan fn-apc-find)))))

; The host's only writer of 'fn-owner-plan-carry.  A present carrier's plan
; is decided here once; anything else leaves PLANS as it is.  One entry: the
; memo never grows past the POST it serves.
(defun fn-apc-plans-extend (received plans carry)
  (declare (xargs :guard t))
  (if (or (fn-apc-find received plans)
          (member-eq (fn-apc-carrier-kind received carry) '(:absent :invalid)))
      plans
    (list (cons received (fn-apc-hc-received-plan received carry)))))

(defthm fn-apc-plansp-of-extend
  (implies (and (fn-apc-p carry) (fn-apc-plansp plans))
           (fn-apc-plansp (fn-apc-plans-extend received plans carry)))
  :hints (("Goal" :in-theory (disable fn-hc-received-plan fn-apc-find
                                      fn-apc-hc-received-plan
                                      fn-apc-carrier-kind))))

(defthm fn-apc-plans-extend-bounded
  (<= (len (fn-apc-plans-extend received plans carry))
      (max 1 (len plans)))
  :hints (("Goal" :in-theory (disable fn-apc-find fn-apc-hc-received-plan
                                      fn-apc-carrier-kind)))
  :rule-classes :linear)

(in-theory (disable fn-apc-hc-received-plan fn-apc-plan fn-apc-plans-extend))

; books/peer-authored-accept.lisp fn-pa-carrier-form (read by the current
; plan; the host's carrier form is the buffer's, fn-ars-carrier-form).  A present carrier's field is still decoded
; by fn-hc-received-plan over the octets (a second parse on that arm only).
(defun fn-apc-carrier-form (received plans carry)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (disable fn-apc-carrier-kind
                                          fn-apc-plan)))))
  (let ((kind (fn-apc-carrier-kind received carry)))
    (if (eq kind :absent) :absent
      (if (eq kind :invalid) (list :refused :article)
        (let ((parsed (fn-apc-plan received plans carry)))
          (if (not (fn-hc-okp parsed))
              (list :refused :carrier)
            (let ((value (fn-hc-value parsed)))
              (if (not (and (true-listp value) (equal (len value) 2)))
                  (list :refused :carrier-shape)
                (let ((carrier (cadr value)))
                  (if (not (and (true-listp carrier)
                                (equal (len carrier) 3)))
                      (list :refused :carrier-shape)
                    (list :ok (car value) (car carrier) (cadr carrier)
                          (caddr carrier))))))))))))

; KEYSTONE for the host line.
(defthm fn-apc-carrier-form-is-reference
  (implies (and (fn-apc-p carry) (fn-apc-plansp plans))
           (equal (fn-apc-carrier-form received plans carry)
                  (fn-pa-carrier-form received)))
  :hints (("Goal" :in-theory (e/d (fn-pa-carrier-form fn-apc-carrier-form)
                                  (fn-pa-carrier-kind fn-hc-received-plan
                                   fn-hc-okp fn-hc-value)))))

; books/peer-authored-accept.lisp fn-pa-current-plan
; (fn-owner-peer-carrier-plan).
(defun fn-apc-current-plan (received snapshots carried transitp plans carry)
  (declare (xargs :guard t))
  (let ((form (fn-apc-carrier-form received plans carry)))
    (if (not (and (consp form) (eq (car form) :ok))) form
            (let* ((source (nth 1 form))
                   (principal (nth 2 form))
                   (keys (nth 3 form))
                   (signatures (nth 4 form))
                   (current (fn-hl-current-for-principal
                             principal snapshots))
                   (generation (if (fn-stxk-p current)
                                   (fn-stxk-keyring-generation current) nil))
                   (enrolled (fn-hl-current-enrollment
                              generation snapshots)))
              (cond ((and (true-listp enrolled)
                          (equal (len enrolled) 3)
                          (equal (car enrolled) current)
                          (equal (cadr enrolled) principal)
                          (equal (caddr enrolled) keys))
                     (list :ok source principal keys signatures
                           current generation))
                    ((and (null current)
                          (fn-pa-carriesp principal carried))
                     (list :carried source principal keys signatures))
                    ((and transitp
                          (fn-pa-revoked-tombstonep current generation
                                                    principal keys snapshots))
                     (list :revoked source principal keys signatures
                           current generation))
                    (t (list :refused :local-enrollment)))))))

; KEYSTONE for the host line.
(defthm fn-apc-current-plan-is-reference
  (implies (and (fn-apc-p carry) (fn-apc-plansp plans))
           (equal (fn-apc-current-plan received snapshots carried transitp plans carry)
                  (fn-pa-current-plan received snapshots carried transitp)))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-apc-current-plan)
                                  (fn-apc-carrier-form fn-pa-carrier-form
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment fn-stxk-p
                                   fn-stxk-keyring-generation fn-pa-carriesp
                                   fn-pa-revoked-tombstonep)))))

(in-theory (disable fn-apc-filing-plan fn-apc-carrier-form fn-apc-current-plan))

; books/peer-carriage.lisp fn-pcb-refusal-class, fn-pcb-admission-verdict,
; fn-pcb-transit-verdict and fn-pcb-transit-refusal-detail.  The admission
; verdict decides its plan once and hands it to the class (the reference
; decides it in each).
(defun fn-apc-refusal-class-of-plan (plan received ed-observation ml-observation)
  (declare (xargs :guard t))
  (cond ((not (consp plan)) nil)
        ((eq (car plan) :refused)
         (cond ((and (consp (cdr plan)) (equal (cadr plan) :local-enrollment))
                :no-local-binding)
               ((and (consp (cdr plan)) (equal (cadr plan) :carrier)
                     (fn-pcb-unsupported-profilep received))
                :unsupported-profile)
               (t :malformed)))
        ((and (eq (car plan) :ok)
              (not (and (eq ed-observation :verified)
                        (eq ml-observation :verified))))
         :signature-failed)
        (t nil)))

(defthm fn-apc-refusal-class-of-plan-is-reference
  (equal (fn-apc-refusal-class-of-plan
          (fn-pa-current-plan received snapshots carried nil)
          received ed ml)
         (fn-pcb-refusal-class received snapshots carried ed ml))
  :hints (("Goal" :in-theory (e/d (fn-pcb-refusal-class)
                                  (fn-pa-current-plan
                                   fn-pcb-unsupported-profilep)))))

; PKT-541: the enrollment refusal of a principal whose enrollment was
; revoked is :revoked-principal; the transit plan (its :revoked arm) is
; decided only on that refusal arm.
(defun fn-apc-admission-verdict-of-plan (plan received snapshots carried
                                              ed ml plans carry)
  (declare (xargs :guard t))
  (let ((class (fn-apc-refusal-class-of-plan plan received ed ml)))
    (cond ((not (consp plan)) :unsigned)
          ((eq (car plan) :carried) :carried)
          ((equal class :malformed) :malformed)
          ((equal class :signature-failed) :cryptographically-invalid)
          ((and (equal class :no-local-binding)
                (let ((tplan (fn-apc-current-plan received snapshots carried
                                                  t plans carry)))
                  (and (consp tplan) (eq (car tplan) :revoked))))
           :revoked-principal)
          ((equal class :no-local-binding) :unenrolled)
          ((equal class :unsupported-profile) :unsupported-profile)
          ((eq (car plan) :ok) :verified)
          (t :malformed))))

(defthm fn-apc-admission-verdict-of-plan-is-reference
  (implies (and (fn-apc-p carry) (fn-apc-plansp plans))
           (equal (fn-apc-admission-verdict-of-plan
                   (fn-pa-current-plan received snapshots carried nil)
                   received snapshots carried ed ml plans carry)
                  (fn-pcb-admission-verdict received snapshots carried ed ml)))
  :hints (("Goal" :in-theory (e/d (fn-pcb-admission-verdict
                                   fn-pcb-revoked-principalp)
                                  (fn-pa-current-plan fn-apc-current-plan
                                   fn-apc-refusal-class-of-plan
                                   fn-pcb-refusal-class)))))

(in-theory (disable fn-apc-refusal-class-of-plan fn-apc-admission-verdict-of-plan))

; fn-owner-transit-verdict.  Off transit the plan is decided once; on
; transit the transit plan's :revoked arm is read first, as the reference
; does, and the admission verdict is decided under the off-transit plan.
(defun fn-apc-transit-verdict (received snapshots carried transitp ed ml plans carry)
  (declare (xargs :guard t))
  (let* ((plan0 (fn-apc-current-plan received snapshots carried nil plans carry))
         (plan (if transitp
                   (fn-apc-current-plan received snapshots carried transitp plans carry)
                 plan0)))
    (if (and (consp plan) (eq (car plan) :revoked))
        (if (and (eq ed :verified) (eq ml :verified))
            :revoked
          :cryptographically-invalid)
      (fn-apc-admission-verdict-of-plan plan0 received snapshots carried
                                        ed ml plans carry))))

; KEYSTONE for the host line.
(defthm fn-apc-transit-verdict-is-reference
  (implies (and (fn-apc-p carry) (fn-apc-plansp plans))
           (equal (fn-apc-transit-verdict received snapshots carried transitp
                                          ed ml plans carry)
                  (fn-pcb-transit-verdict received snapshots carried transitp
                                          ed ml)))
  :hints (("Goal" :in-theory (e/d (fn-pcb-transit-verdict fn-apc-transit-verdict)
                                  (fn-apc-current-plan fn-pa-current-plan
                                   fn-apc-admission-verdict-of-plan
                                   fn-pcb-admission-verdict)))))

; fn-owner-transit-refusal-class.
(defun fn-apc-transit-refusal-detail (received snapshots carried ed ml plans carry)
  (declare (xargs :guard t))
  (let* ((verdict (fn-apc-admission-verdict-of-plan
                   (fn-apc-current-plan received snapshots carried nil plans carry)
                   received snapshots carried ed ml plans carry))
         (class (fn-pcb-verdict-refusal-class verdict)))
    (if class (list class verdict) nil)))

; KEYSTONE for the host line.
(defthm fn-apc-transit-refusal-detail-is-reference
  (implies (and (fn-apc-p carry) (fn-apc-plansp plans))
           (equal (fn-apc-transit-refusal-detail received snapshots carried
                                                 ed ml plans carry)
                  (fn-pcb-transit-refusal-detail received snapshots carried
                                                 ed ml)))
  :hints (("Goal" :in-theory (e/d (fn-pcb-transit-refusal-detail fn-apc-transit-refusal-detail)
                                  (fn-apc-current-plan
                                   fn-apc-admission-verdict-of-plan
                                   fn-pcb-admission-verdict
                                   fn-pcb-verdict-refusal-class)))))

(in-theory (disable fn-apc-transit-verdict fn-apc-transit-refusal-detail))

; -----------------------------------------------------------------------------
; The prepare's row and the finish.

; books/catalog-record.lisp fn-held-context-of: the verdict and the delta
; read one parse (the reference parses for each).
(defun fn-apc-held-context-of (bytes keyring generation carry)
  (declare (xargs :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (let ((a (fn-apc-stx-parse bytes carry)))
    (fn-hc-make (if a
                    (fn-stx-verdict a keyring generation)
                  (fn-stx-make-verdict :unverified :malformed generation))
                (if (and a (fn-stx-verifiedp a keyring))
                    (list (fn-stx-statement-of a))
                  nil)
                generation)))

(defthm fn-apc-held-context-of-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-held-context-of bytes keyring generation carry)
                  (fn-held-context-of bytes keyring generation)))
  :hints (("Goal" :in-theory (e/d (fn-held-context-of fn-stx-verdict-of-octets
                                   fn-stx-delta)
                                  (fn-stx-parse fn-stx-verdict fn-hc-make
                                   fn-stx-make-verdict fn-stx-verifiedp
                                   fn-stx-statement-of)))))

; books/store-intern.lisp fn-intern-row-at (fn-owner-prepare-buffer).
; books/catalog-record.lisp fn-held-facts-of: the control fact from the
; take's parse (post-alloc-2: the intern parsed the payload once more here).
(defun fn-apc-control-of (received carry)
  (declare (xargs :guard t))
  (let ((fields (fn-apc-received-fields received carry)))
    (list (fn-ctl-article-target fields)
          (fn-ctl-cancel-keys fields)
          (fn-ctl-cancel-locks fields))))

(defthm fn-apc-control-of-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-control-of received carry)
                  (fn-ctl-control-of received)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-control-of)
                                  (fn-apc-received-fields fn-ctl-received-fields
                                   fn-ctl-article-target fn-ctl-cancel-keys
                                   fn-ctl-cancel-locks)))))

(defun fn-apc-held-facts-of (bytes carry)
  (declare (xargs :guard (true-listp bytes)))
  (fn-hf-make (len bytes) (fn-hf-split-index bytes 0) (fn-hf-body-lines-of bytes)
              ;; The control facts, then the overview column from the take's
              ;; parse (lane served-columns).
              (fn-hf-control-with-nov (fn-apc-control-of bytes carry)
                                      (fn-hnov-of-parsed bytes (fn-apc-parse bytes carry)))))

(defthm fn-apc-held-facts-of-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-held-facts-of bytes carry)
                  (fn-held-facts-of bytes)))
  :hints (("Goal" :in-theory (e/d (fn-held-facts-of fn-hnov-of)
                                  (fn-apc-control-of fn-ctl-control-of fn-hf-make
                                   fn-hf-split-index fn-hf-body-lines-of
                                   fn-hnov-of-parsed fn-apc-parse fn-article-parse)))))

(in-theory (disable fn-apc-control-of fn-apc-held-facts-of))

(defun fn-apc-intern-row-at (w keyring generation h carry)
  (declare (xargs :guard (and (fn-record-p w) (fn-prin-keyringp keyring)
                              (natp generation) (natp h))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let ((bytes (fn-record-payload w)))
    (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                  (fn-record-generation w) (fn-record-msgid w) h
                  (fn-record-groups w) (fn-record-obligation-id w)
                  (fn-record-content-subject w) (fn-record-release-evidence w)
                  (fn-record-charge w) (fn-record-stamp w)
                  (fn-apc-held-facts-of bytes carry)
                  (fn-apc-held-context-of bytes keyring generation carry)
                  nil nil)))

; KEYSTONE for the host line.
(defthm fn-apc-intern-row-at-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-intern-row-at w keyring generation h carry)
                  (fn-intern-row-at w keyring generation h)))
  :hints (("Goal" :in-theory (e/d (fn-intern-row-at)
                                  (fn-apc-held-context-of fn-held-context-of
                                   fn-held-make fn-held-facts-of
                                   fn-apc-held-facts-of)))))

(in-theory (disable fn-apc-held-context-of fn-apc-intern-row-at))

; books/owner-commit-carried.lisp fn-ccar-completion-names-submission-p.
(defun fn-apc-completion-names-submission-p (o cfg fn-arena carry)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-sn-statep (fn-own-store o))
                  :guard-hints
                  (("Goal" :in-theory
                    (disable fn-ccar-completion-record-is-completion-record)))))
  (let ((sub (fn-own-inflight o))
        (record (fn-ccar-completion-record (fn-own-store o))))
    (and sub
         record
         (fn-evc-recordp record)
         (let ((w (fn-row-wire-of record fn-arena)))
           (and (equal (fn-record-msgid w)
                       (fn-record-octets-string (fn-own-sub-msgid sub)))
                (equal (fn-record-payload w)
                       (fn-apc-sub-stored-octets cfg sub (fn-own-node-secret o)
                                                 carry))))
         t)))

(defthm fn-apc-completion-names-submission-p-is-reference
  (implies (fn-apc-p carry)
           (equal (fn-apc-completion-names-submission-p o cfg fn-arena carry)
                  (fn-ccar-completion-names-submission-p o cfg fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-ccar-completion-names-submission-p)
                                  (fn-apc-sub-stored-octets fn-own-sub-stored-octets
                                   fn-ccar-completion-record fn-evc-recordp
                                   fn-row-wire-of fn-record-p)))))

; books/owner-commit-carried.lisp fn-ccar-own-finish
; (fn-owner-finish-submission).
(defun fn-apc-own-finish (o cfg fn-arena fn-hist carry)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard (fn-sn-statep (fn-own-store o))))
  (if (fn-ccar-completion-enabledp (fn-own-store o))
      (cons (if (fn-apc-completion-names-submission-p o cfg fn-arena carry)
                :durable :fault)
            (fn-rix-own-complete-enabled o fn-hist))
    (cons :fault o)))

; The completion refreshes over the history stobj
; (books/owner-refresh-indexed.lisp fn-rix-own-complete-enabled-is-ccar):
; hence R, the stobj IS the owner's Store's history, which the host
; establishes before the call (host/store-node-host.lisp fn-host-hist-sync).
(defthm fn-apc-own-finish-is-ccar-own-finish
  (implies (and (fn-apc-p carry) (fn-hist-of-storep fn-hist (fn-own-store o)))
           (equal (fn-apc-own-finish o cfg fn-arena fn-hist carry)
                  (fn-ccar-own-finish o cfg fn-arena)))
  :hints (("Goal" :in-theory '(fn-apc-own-finish fn-ccar-own-finish
                               fn-rix-own-complete-enabled-is-ccar
                               fn-apc-completion-names-submission-p-is-reference))))

; KEYSTONE for the host line: the word and the owner are fn-own-finish's.
(defthm fn-apc-own-finish-is-own-finish
  (implies (and (fn-apc-p carry) (fn-hist-of-storep fn-hist (fn-own-store o)))
           (equal (fn-apc-own-finish o cfg fn-arena fn-hist carry)
                  (fn-own-finish o cfg fn-arena)))
  :hints (("Goal" :in-theory '(fn-apc-own-finish-is-ccar-own-finish
                               fn-ccar-own-finish-is-own-finish))))

(in-theory (disable fn-apc-completion-names-submission-p fn-apc-own-finish))

; -----------------------------------------------------------------------------
; The served outcome (post-alloc-2).  books/owner-advance-carried.lisp
; fn-acar-own-outcome, which host/owner-host.lisp fn-owner-outcome calls,
; enqueues a durable article on its feeds through fn-own-feed-durable, whose
; targets (fn-own-submission-targets) parse the article again for its Path,
; its newsgroups' control groups and its Distribution.  fn-apc-own-outcome is
; it with the targets read from the intent carry and the take's parse
; (fn-apc-submission-targets).
(defun fn-apc-own-outcome (o id word icar carry)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o)))
        (sub (fn-own-inflight o)))
    (if (and conn sub (equal (fn-own-sub-id sub) id))
        (let* ((completion (fn-own-outcome-completion o word))
               (next (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                 (fn-own-next-id o) (fn-own-max-conns o)
                                 (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                 (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil
                                 (if (equal completion :durable)
                                     (fn-own-feed-enqueue-all
                                      (fn-apc-submission-targets o icar carry)
                                      (fn-own-feeds o)
                                      (fn-own-sub-msgid sub) (fn-own-feed-stamp o))
                                   (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))
          (cons (fn-served-result-effects
                 (fn-served-post-outcome
                  (fn-served-make-conn-group-indexed (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-clock o)
                                       (fn-own-conn-verdicts conn)
                                       (fn-own-conn-index conn)
                                       (fn-own-conn-group-index conn) (fn-own-conn-control conn))
                  (fn-own-post-rendering o word)))
                (if (equal completion :durable)
                    (cdr (fn-acar-own-advance-result next id))
                  next)))
      (cons nil o))))

; KEYSTONE for the host line: under the two carries' recognizers (each
; written by fn-owner-take alone, neither mentioning the owner) the outcome is
; fn-acar-own-outcome, hence fn-own-outcome
; (fn-acar-own-outcome-is-own-outcome and its relation form).
(defthm fn-apc-own-outcome-is-acar-own-outcome
  (implies (and (fn-icar-carryp icar) (fn-apc-p carry))
           (equal (fn-apc-own-outcome o id word icar carry)
                  (fn-acar-own-outcome o id word)))
  :hints (("Goal" :use ((:instance fn-apc-submission-targets-is-reference)
                        (:instance fn-icar-submission-targets-is-submission-targets (carry icar)))
           :in-theory (e/d (fn-apc-own-outcome fn-acar-own-outcome fn-own-feed-durable)
                           (fn-apc-submission-targets-is-reference
                            fn-icar-submission-targets-is-submission-targets
                            fn-apc-submission-targets fn-icar-submission-targets
                            fn-own-submission-targets fn-own-make
                            fn-own-feed-enqueue-all fn-acar-own-advance-result
                            fn-served-post-outcome fn-served-result-effects
                            fn-served-make-conn-group-indexed
                            fn-own-outcome-completion fn-own-post-rendering
                            fn-own-find-conn)))))

(in-theory (disable fn-apc-own-outcome))
