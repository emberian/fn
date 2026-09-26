; fn: the Store open refuses, by name, a history holding a control article
; that an image before C1 (9ffef4ac) filed under its Newsgroups (PKT-444's
; first half; planning/evidence/control-across-peers-2026-09-26.md,
; "Continuation: the pre-C1 open").
;
; Before C1 a signed control article was stored like any article, in the
; groups its Newsgroups names.  Since C1 a record of a signed article must
; list the groups `fn-hsig-source-filed-groups' derives from its signed
; source, and for a control article that is its filing group
; (control.<verb>), so the identity fold of the current replay
; (books/replay.lisp `fn-replay-identity-step', its `fn-stxa-p' arm) finds
; the record's groups unequal to the derived ones and stops with the
; generic `:composite-binding' fault; `fn-sco-finalize' answers
; (:error :identity) and the host printed "ACL2 replay rejected committed
; transaction history".  An open either succeeds or refuses by name: this
; book names the record the fold stopped at when it is such a record, and
; changes nothing else.  What a repair of such a Store means (replaying the
; record as filed-under-Newsgroups history, or something else) is ember's
; decision (PKT-444); this book decides only the refusal.
;
; The subject the host calls is `fn-sopc-classified-open'
; (host/store-node-host.lisp `fn-store-sn-open-extended', which every open
; of the native host reaches: `fn-store-sn-recover' for a full replay and
; `fn-store-sn-recover-from-checkpoint' for a checkpoint open).  The replay
; itself (books/replay.lisp) is unchanged: the refusal reads the position
; at which the identity fold stopped and the record there.

(in-package "ACL2")
(include-book "store-checkpoint-open")
(include-book "store-identity-sequence-invariants")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The record

; A kind-4 composite of schema 1 (the carried source is stored, so it can be
; classified) whose signed source is a control article (C1's classifier,
; books/control-classify.lisp), whose article record lists exactly the
; Newsgroups of that source (what a pre-C1 image filed), and whose groups
; are not the filing group the current replay requires.  A control article
; whose Newsgroups already are its filing group binds today and is not
; named; a record whose groups are neither is not a pre-C1 filing and is
; not named (the fault stays a fault).
(defun fn-sopc-article (event)
  (declare (xargs :guard t))
  (let ((article (fn-record-decode-exact (fn-stxa-article-record event))))
    (if (fn-record-result-okp article)
        (fn-record-result-record article)
      nil)))

(defun fn-sopc-pre-c1-control-record-p (event)
  (declare (xargs :guard t))
  (and (fn-stxa-p event)
       (equal (fn-stxa-schema event) *fn-stxa-carried-version*)
       (fn-record-result-okp
        (fn-record-decode-exact (fn-stxa-article-record event)))
       (let* ((record (fn-sopc-article event))
              (source (fn-stxa-authored-source event))
              (fields (fn-hsig-authored-source-fields source))
              (classified (fn-ctl-classify-octets source)))
         (and (fn-record-p record)
              fields
              (consp classified)
              (eq (car classified) :control)
              (equal (fn-record-groups record) (fn-hsig-second fields))
              (not (equal (fn-record-groups record)
                          (fn-hsig-source-filed-groups source fields)))))))

; No record of the history is one.
(defun fn-sopc-free-p (records)
  (declare (xargs :guard t))
  (if (consp records)
      (and (not (fn-sopc-pre-c1-control-record-p (car records)))
           (fn-sopc-free-p (cdr records)))
    t))

; -----------------------------------------------------------------------------
; The refusal

; E is the extended checkpoint the host opens from (`fn-sco-extend'): its
; records are the whole history and its identity context is the identity
; fold over them.  When that fold did not finish :ok, its cursor is the
; sequence of the record it stopped at; the refusal names that record when
; it is a pre-C1 control record at its own sequence, else there is none.
(defun fn-sopc-open-refusal (e)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((identity (fn-sco-identity e))
         (next (fn-stxk-context-next identity)))
    (if (or (equal (fn-stxk-context-kind identity) :ok)
            (not (natp next)))
        nil
      (let ((event (nth next (true-list-fix (fn-sco-records e)))))
        (if (and (fn-sopc-pre-c1-control-record-p event)
                 (equal (fn-store-event-sequence event) next))
            (list :refused :pre-c1-control-record
                  (fn-store-event-txid event)
                  (fn-record-msgid (fn-sopc-article event)))
          nil)))))

(verify-guards fn-sopc-open-refusal)

; The function the host calls: the named refusal, else the open it ran
; before (`fn-sco-store-open', the pair (REPLAYED OPENED)).
(defun fn-sopc-classified-open (e configs frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((refusal (fn-sopc-open-refusal e)))
    (if refusal refusal (fn-sco-store-open e configs frontier))))

; The decimal digits of a natural, most significant first.
(defun fn-sopc-digits (n acc)
  (declare (xargs :guard (and (natp n) (character-listp acc))
                  :measure (nfix n)))
  (if (zp n)
      acc
    (fn-sopc-digits (floor n 10)
                    (cons (code-char (+ 48 (mod n 10)))
                          acc))))

(defthm fn-sopc-digits-character-listp
  (implies (character-listp acc) (character-listp (fn-sopc-digits n acc))))

(defun fn-sopc-decimal (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) "0" (coerce (fn-sopc-digits n nil) 'string)))

; The operator's line, rendered once here (the host prints it after its
; family's word): refused operator run / store: ...
(defun fn-sopc-refusal-text (refusal)
  (declare (xargs :guard t))
  (if (and (true-listp refusal) (equal (len refusal) 4)
           (eq (car refusal) :refused)
           (eq (cadr refusal) :pre-c1-control-record)
           (natp (caddr refusal))
           (stringp (cadddr refusal)))
      (concatenate 'string
                   "pre-C1 control record (txid "
                   (fn-sopc-decimal (caddr refusal))
                   ", " (cadddr refusal)
                   "): run store repair-control")
    nil))

; The repair verb's answer until ember decides its semantics (PKT-444).
(defconst *fn-sopc-repair-undecided-text*
  "repair semantics undecided (PKT-444)")

; -----------------------------------------------------------------------------
; The fault the refusal replaces

; A pre-C1 control record binds no composite: every binding the identity
; fold admits a schema-1 composite under checks that its record lists the
; groups `fn-hsig-source-filed-groups' derives, and this record does not.
(defthm fn-sopc-pre-c1-control-record-facts
  (implies (fn-sopc-pre-c1-control-record-p event)
           (and (fn-stxa-p event)
                (equal (fn-stxa-schema event) *fn-stxa-carried-version*)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-sopc-pre-c1-control-record-p)))))

(defthm fn-sopc-pre-c1-record-has-no-carried-metadata
  (implies (fn-sopc-pre-c1-control-record-p event)
           (not (fn-hsig-carried-record-metadatap
                 (fn-stxa-authored-source event) received
                 (fn-record-result-record
                  (fn-record-decode-exact (fn-stxa-article-record event))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-sopc-pre-c1-control-record-p
                                               fn-sopc-article
                                               fn-hsig-carried-record-metadatap)))))

(defthm fn-sopc-pre-c1-record-binds-no-composite
  (implies (fn-sopc-pre-c1-control-record-p event)
           (and (not (fn-hsig-article-event-carried-bindsp event))
                (not (fn-hsig-article-event-revoked-bindsp event))
                (not (fn-hsig-article-event-snapshot-bindsp event snapshot))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-hsig-article-event-carried-bindsp
                                               fn-hsig-article-event-revoked-bindsp
                                               fn-hsig-article-event-snapshot-bindsp
                                               fn-hsig-article-event-snapshot-bindsp-v1
                                               fn-sopc-pre-c1-record-has-no-carried-metadata
                                               (:executable-counterpart equal)
                                               fn-sopc-pre-c1-control-record-facts))
           :use ((:instance fn-sopc-pre-c1-record-has-no-carried-metadata
                            (received (fn-record-payload
                                       (fn-record-result-record
                                        (fn-record-decode-exact
                                         (fn-stxa-article-record event))))))
                 (:instance fn-sopc-pre-c1-record-has-no-carried-metadata
                            (received (and (fn-record-result-okp
                                            (fn-record-decode-exact
                                             (fn-stxa-article-record event)))
                                           (fn-record-payload
                                            (fn-record-result-record
                                             (fn-record-decode-exact
                                              (fn-stxa-article-record event)))))))))))

; The three identity event kinds are records of different widths.
(defthm fn-sopc-stxa-is-neither-stxk-nor-stxe
  (implies (fn-stxa-p x)
           (and (not (fn-stxk-p x)) (not (fn-stxe-p x))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-stxa-p fn-stxk-p fn-stxe-p
                                               fn-stxa-shapep fn-stxk-shapep fn-stxe-shapep
                                               (:executable-counterpart equal))))))

; KEYSTONE (the site).  No identity step admits a pre-C1 control record: from
; any context the step answers a context that is not :ok, at the same
; cursor.  So the fold stops exactly at such a record and names nothing
; past it.
(defthm fn-replay-identity-step-never-admits-a-pre-c1-control-record
  (implies (fn-sopc-pre-c1-control-record-p event)
           (and (not (equal (fn-stxk-context-kind (fn-replay-identity-step ctx event))
                            :ok))
                (equal (fn-stxk-context-next (fn-replay-identity-step ctx event))
                       (fn-stxk-context-next ctx))))
  :hints (("Goal"
           :use ((:instance fn-sopc-stxa-is-neither-stxk-nor-stxe (x event))
                 (:instance fn-sopc-pre-c1-record-binds-no-composite
                            (snapshot (fn-stxk-find (fn-stxa-keyring-generation event)
                                                    (fn-stxk-context-snapshots ctx)))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-replay-identity-step fn-stxk-fault
                                        fn-stxk-context fn-stxk-context-kind
                                        fn-stxk-context-next
                                        fn-sopc-pre-c1-control-record-facts
                                        car-cons cdr-cons
                                        (:executable-counterpart equal))))))

; A stopped fold stays stopped at its cursor, whatever follows.
(defthm fn-sopc-identity-loop-stays-stopped
  (implies (not (equal (fn-stxk-context-kind ctx) :ok))
           (and (not (equal (fn-stxk-context-kind (fn-replay-identity-loop records ctx))
                            :ok))
                (equal (fn-stxk-context-next (fn-replay-identity-loop records ctx))
                       (fn-stxk-context-next ctx))))
  :hints (("Goal" :induct (fn-replay-identity-loop records ctx)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-replay-identity-loop fn-replay-identity-step
                                        fn-stxk-fault fn-stxk-context
                                        fn-stxk-context-kind fn-stxk-context-next
                                        car-cons cdr-cons
                                        (:executable-counterpart equal))))))

; A fold that finishes :ok ran over a proper list of Store events.
(defthm fn-sopc-identity-loop-ok-is-store-events
  (implies (equal (fn-stxk-context-kind (fn-replay-identity-loop records ctx)) :ok)
           (and (fn-sco-store-eventsp records)
                (true-listp records)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-replay-identity-loop records ctx)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-replay-identity-loop fn-sco-store-eventsp
                                        fn-stxk-fault fn-stxk-context
                                        fn-stxk-context-kind true-listp
                                        car-cons cdr-cons
                                        (:executable-counterpart equal))))
          ("Subgoal *1/1" :use ((:instance fn-sopc-identity-loop-stays-stopped
                                           (records (cdr records))
                                           (ctx (fn-replay-identity-step ctx (car records))))))))

(defthm fn-sopc-identity-stops-at-the-pre-c1-record
  (implies (and (equal (fn-stxk-context-kind (fn-replay-identity prefix)) :ok)
                (fn-sopc-pre-c1-control-record-p event))
           (let ((ctx (fn-replay-identity-loop (append prefix (cons event rest))
                                               (fn-stxk-initial-context 0))))
             (and (not (equal (fn-stxk-context-kind ctx) :ok))
                  (equal (fn-stxk-context-next ctx) (len prefix)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sopc-identity-loop-ok-is-store-events
                            (records prefix) (ctx (fn-stxk-initial-context 0)))
                 (:instance fn-replay-identity-append
                            (suffix (cons event rest))
                            (ctx (fn-stxk-initial-context 0)))
                 (:instance fn-replay-identity-ok-next-is-record-count (records prefix))
                 (:instance fn-replay-identity-step-never-admits-a-pre-c1-control-record
                            (ctx (fn-replay-identity prefix)))
                 (:instance fn-sopc-identity-loop-stays-stopped
                            (records rest)
                            (ctx (fn-replay-identity-step (fn-replay-identity prefix) event))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-replay-identity fn-store-event-p
                                        fn-sopc-pre-c1-control-record-facts
                                        car-cons cdr-cons
                                        (:definition fn-replay-identity-loop)
                                        (:executable-counterpart equal))))))

(local
 (defthm fn-sopc-full-capture-parts
  (and (equal (fn-sco-identity (fn-sco-extend (fn-sco-capture configs nil) configs h))
              (fn-replay-identity-loop h (fn-stxk-initial-context 0)))
       (equal (fn-sco-records (fn-sco-extend (fn-sco-capture configs nil) configs h))
              h))
  :hints (("Goal" :in-theory (e/d (fn-sco-extend fn-sco-capture fn-sco-make
                                   fn-sco-identity fn-sco-records)
                                  (fn-replay-identity-step fn-sco-cpr-prefix
                                   fn-sco-cpr-resume fn-sco-consumer-resume
                                   fn-cpe-projection-replay fn-th-prefix-loop
                                   fn-cei-build-aux))
           :expand ((fn-replay-identity-loop nil (fn-stxk-initial-context 0)))))))

(local
 (defthm fn-sopc-nth-len-of-append
  (equal (nth (len prefix) (true-list-fix (append prefix (cons event rest))))
         event)))

; KEYSTONE (the open).  The open the host runs over a history whose identity
; fold reaches a pre-C1 control record at its own sequence is the named
; refusal of that record, never a fault: its transaction id and its
; Message-ID.  Host line: host/store-node-host.lisp fn-store-sn-open-extended
; calls fn-sopc-classified-open on the extended capture E; this is the full
; open (E the capture of no prefix extended over the history), and
; fn-sopc-checkpoint-open-names-what-the-full-open-names carries it to the
; checkpoint open.
(defthm fn-replay-never-faults-on-a-pre-c1-control-record
  (implies (and (equal (fn-stxk-context-kind (fn-replay-identity prefix)) :ok)
                (fn-sopc-pre-c1-control-record-p event)
                (equal (fn-store-event-sequence event) (len prefix)))
           (equal (fn-sopc-classified-open
                   (fn-sco-extend (fn-sco-capture configs nil) configs
                                  (append prefix (cons event rest)))
                   configs frontier)
                  (list :refused :pre-c1-control-record
                        (fn-store-event-txid event)
                        (fn-record-msgid (fn-sopc-article event)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sopc-identity-stops-at-the-pre-c1-record))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-sopc-classified-open fn-sopc-open-refusal
                                        fn-sopc-full-capture-parts
                                        fn-sopc-nth-len-of-append
                                        natp len (:type-prescription len)
                                        (:executable-counterpart equal)
                                        (:executable-counterpart not))))))

; The checkpoint open names what the full open names.
(defthm fn-sopc-checkpoint-open-names-what-the-full-open-names
  (implies (and (fn-sco-store-eventsp (true-list-fix prefix))
                (true-listp suffix))
           (equal (fn-sopc-classified-open
                   (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                   configs frontier)
                  (fn-sopc-classified-open
                   (fn-sco-extend (fn-sco-capture configs nil) configs
                                  (append prefix suffix))
                   configs frontier)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-sco-extend-of-capture
                 (:instance fn-sco-extend-of-capture
                            (prefix nil) (suffix (append prefix suffix))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(true-listp-append true-list-fix
                                        (:executable-counterpart fn-sco-store-eventsp)
                                        (:executable-counterpart true-list-fix)
                                        append)))))

; -----------------------------------------------------------------------------
; The refinement: invisible to every other history

(defthm fn-sopc-free-p-has-no-pre-c1-record
  (implies (fn-sopc-free-p records)
           (not (fn-sopc-pre-c1-control-record-p (nth n (true-list-fix records)))))
  :hints (("Goal" :induct (nth n records)
           :in-theory (e/d (nth true-list-fix fn-sopc-free-p)
                           (fn-sopc-pre-c1-control-record-p)))
          ("Subgoal *1/1" :in-theory (enable fn-sopc-pre-c1-control-record-p
                                             true-list-fix))))

; KEYSTONE (the refinement).  On a history holding no pre-C1 control record,
; the classified open is the open the host ran before this book
; (fn-sco-store-open; for the full open that is fn-cpr-replay and
; fn-cpo-open-observed, fn-sco-store-open-of-extended-capture).
(defthm fn-sopc-classified-open-is-the-open-without-a-pre-c1-record
  (implies (fn-sopc-free-p (fn-sco-records e))
           (equal (fn-sopc-classified-open e configs frontier)
                  (fn-sco-store-open e configs frontier)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-sopc-classified-open
                                               fn-sopc-open-refusal
                                               fn-sopc-free-p-has-no-pre-c1-record)))))
