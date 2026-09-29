; fn: the typed results the native owner's wrappers return (wave 5,
; adapter retirement; design-2026-09-26-consolidation section 4.6; gpt-6's
; review section 7).
;
; Before this book, a host/owner-host.lisp wrapper answered one action
; keyword and left the rest of its result in `f-put-global' mailboxes
; (`fn-owner-feed-frames', `fn-owner-config-reason', ...) that the raw native
; host read back with `fnn-global', and two results crossed the boundary in
; an internal wire grammar: peer names joined with LF and split again in raw
; Lisp (`fnn-owner-name-list'), and a feed flush that fetched each sealed
; frame BY INDEX against a separately returned peer list
; (`fn-owner-feed-record-peers', `fn-owner-feed-sealed-frame').  Here every
; such result is one ACL2 value with a guard-verified recognizer; the wrapper
; returns it (`(value result)'), the native host checks the recognizer ONCE
; at the boundary (host/native/owner.lisp `fnn-owner-result', a shape check,
; never a semantic one) and reads fields through the accessors below.  Text
; is rendered at the CLI and log boundaries, bytes are encoded at the wire
; and storage boundaries; ACL2 constructs the value and the adapter executes
; it.
;
; The shapes (tagged lists, fields in this order):
;   FeedPublication  (:feed-publication WORD PEER PLAN TOKEN COMMAND STATUS LOG-LINE)
;   SubmissionTaken  (:submission-taken WORD ID MSGID OCTETS GROUPS INTENT TRANSITP PEER)
;   ServedStep       (:served-step WORD REPLY CLOSEP STARTTLSP SUBMITTEDP CONSUMED LOG-LINE)
;   Capture          (:capture COUNT FILL ROOTS FRONTIER BUDGET)
;   ConfigResult     (:config-result WORD OCTETS REASON)
;
; TOKEN (the completion token) carries today's value, the in-flight
; submission's id or nil; the catalog slice (design 1.3) puts its
; PreparedCommit token (txid . expected) there, so the recognizer admits nil,
; a natural or a cons.  OCTETS in SubmissionTaken is the octet list until
; ingress-span-2's buffer range replaces it; REPLY in ServedStep likewise
; until egress-span's range does.
;
; The builders call functions the tree leaves guard-unverified (the FNFD
; codec `fn-feed-encode', `fn-frame-protected-prefix', the attached trailer
; `fn-frame-trailer', the outbound renderer `fn-wire-render-feed-command'),
; so they are admitted in :logic mode with their guards unverified, exactly
; as those callees are; the recognizers and the accessors the host calls
; are guard-verified.

(in-package "ACL2")

(include-book "owner-feed")
(include-book "wire")
(include-book "frame-trailer")
(include-book "records-shape")
(include-book "nntp-syntax")
(include-book "config")
(include-book "owner-intent-carried")

; ---------------------------------------------------------------------------
; Shared field recognizers.

(defun fn-ores-octet-lists-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (fn-cbor-octet-listp (car x))
           (fn-ores-octet-lists-p (cdr x)))
    (null x)))

; The owner's submission ids: a served connection's number (fn-own-read
; enqueues under the connection id) or the control id `*fn-own-control-id*'
; (books/owner.lisp: every `operator post', BP application and transit
; submission is enqueued under it).  The first recognizer admitted only a
; natural, so every operator post faulted at the submission intent (the
; batch AM revert, dev 54d23d01).
(defun fn-ores-submission-idp (x)
  (declare (xargs :guard t))
  (or (natp x) (equal x *fn-own-control-id*)))

(defun fn-ores-tokenp (x)
  ; nil, today's submission id, or the catalog slice's (txid . expected).
  (declare (xargs :guard t))
  (or (null x) (fn-ores-submission-idp x) (consp x)))

; ---------------------------------------------------------------------------
; FeedPublication.
;
; PLAN is the sealed frame plan: one (PEER . SEALED-FRAME) pair per journal
; record, in the order the records must be appended.  The pair replaces the
; two parallel answers the host used to join by position.

(defun fn-ores-sealed-plan-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (stringp (car (car x)))
           (fn-cbor-octet-listp (cdr (car x)))
           (consp (cdr (car x)))
           (fn-ores-sealed-plan-p (cdr x)))
    (null x)))

(defun fn-ores-feed-publication-p (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 8)
       (equal (nth 0 x) :feed-publication)
       (symbolp (nth 1 x))
       (or (null (nth 2 x)) (stringp (nth 2 x)))
       (fn-ores-sealed-plan-p (nth 3 x))
       (fn-ores-tokenp (nth 4 x))
       (fn-cbor-octet-listp (nth 5 x))
       (symbolp (nth 6 x))
       (fn-cbor-octet-listp (nth 7 x))))

(defun fn-ores-feedpub-word (x) (declare (xargs :guard t)) (fn-frame-item 1 x))
(defun fn-ores-feedpub-peer (x) (declare (xargs :guard t)) (fn-frame-item 2 x))
(defun fn-ores-feedpub-plan (x) (declare (xargs :guard t)) (fn-frame-item 3 x))
(defun fn-ores-feedpub-token (x) (declare (xargs :guard t)) (fn-frame-item 4 x))
(defun fn-ores-feedpub-command (x) (declare (xargs :guard t)) (fn-frame-item 5 x))
(defun fn-ores-feedpub-status (x) (declare (xargs :guard t)) (fn-frame-item 6 x))
(defun fn-ores-feedpub-log-line (x) (declare (xargs :guard t)) (fn-frame-item 7 x))

; The frames carry a ZERO trailer from the codec; the seal replaces it with
; the constrained trailer over the protected prefix (A-CRYPTO).  This was
; host/owner-host.lisp's `*fn-owner-feed-zero-trailer*' and
; `fn-owner-feed-encode-records' (program mode), now the book's.
(defconst *fn-ores-zero-trailer*
  '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))

(defun fn-ores-encode-records (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (cons (fn-feed-encode (fn-feed-journal-kind (car records))
                            (fn-feed-journal-values (car records))
                            *fn-ores-zero-trailer*)
            (fn-ores-encode-records (cdr records)))
    nil))

; Which peer's journal a record belongs in: its own field 0, as the string
; the journal table is keyed by.  This was `fn-owner-feed-record-peer-names'.
(defun fn-ores-record-peer (record)
  (declare (xargs :guard t :verify-guards nil))
  (fn-record-octets-string
   (fn-feed-record-peer (fn-feed-journal-values record))))

(verify-guards fn-ores-record-peer)

(defun fn-ores-record-peers (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (cons (fn-ores-record-peer (car records))
            (fn-ores-record-peers (cdr records)))
    nil))

; The sealed frame: the protected prefix and its trailer.  This was
; `fn-owner-feed-sealed-frame', applied to the frame at an index; a frame the
; codec refused (:bad) seals to :bad, which the recognizer rejects, so the
; host faults exactly where it faulted before ("malformed sealed FNFD frame").
(defun fn-ores-seal (frame)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-cbor-octet-listp frame)
      (let ((prefix (fn-frame-protected-prefix frame)))
        (mbe :logic (append prefix (fn-frame-trailer prefix))
             :exec (fn-ag-append prefix (fn-frame-trailer prefix))))
    :bad))

(verify-guards fn-ores-seal)

; Executes by a loop (lane depth-debt, PRF-919): one record per target peer,
; operator data with no fixed cap (D27).  (mbe :logic <the recursion,
; unchanged> :exec <a loop>).  The seal, the entry, the loop and the plan are
; guard-verified (lane depth-debt-2), so the host's call runs the :exec; the
; equality is fn-ores-sealed-plan-loop-is-rev-onto.
(defun fn-ores-sealed-entry (r)
  (declare (xargs :guard t :verify-guards nil))
  (cons (fn-ores-record-peer r)
        (fn-ores-seal
         (fn-feed-encode (fn-feed-journal-kind r)
                         (fn-feed-journal-values r)
                         *fn-ores-zero-trailer*))))

(defun fn-ores-sealed-plan-loop (records acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (fn-ores-sealed-plan-loop (cdr records)
                                (cons (fn-ores-sealed-entry (car records)) acc))
    (fn-ag-rev-onto acc nil)))

(verify-guards fn-ores-sealed-entry)
(verify-guards fn-ores-sealed-plan-loop)

(defun fn-ores-sealed-plan (records)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp records)
                  (cons (cons (fn-ores-record-peer (car records))
                              (fn-ores-seal
                               (fn-feed-encode (fn-feed-journal-kind (car records))
                                               (fn-feed-journal-values (car records))
                                               *fn-ores-zero-trailer*)))
                        (fn-ores-sealed-plan (cdr records)))
                nil)
       :exec (fn-ores-sealed-plan-loop records nil)))

(defthm fn-ores-sealed-plan-loop-is-rev-onto
  (equal (fn-ores-sealed-plan-loop records acc)
         (fn-ag-rev-onto acc (fn-ores-sealed-plan records)))
  :hints (("Goal" :induct (fn-ores-sealed-plan-loop records acc)
                  :in-theory (union-theories
                              '(fn-ores-sealed-plan-loop fn-ores-sealed-plan
                                fn-ag-rev-onto car-cons cdr-cons fn-ores-sealed-entry)
                              (theory 'minimal-theory)))))

(verify-guards fn-ores-sealed-plan
  :hints (("Goal" :in-theory (disable fn-ores-sealed-entry fn-ores-seal fn-ores-record-peer))))

(defun fn-ores-feed-publication (word peer records token command status log-line)
  (declare (xargs :guard t :verify-guards nil))
  (list :feed-publication word peer (fn-ores-sealed-plan records) token
        command status log-line))

; The feed port's publication: the step's records, its effect's peer and its
; rendered command.  This is what host/owner-host.lisp
; `fn-owner-feed-install-feed' wrote into five globals.
(defun fn-ores-feed-port-publication (word records effects token log-line)
  (declare (xargs :guard t :verify-guards nil))
  (let ((rendered (fn-wire-render-feed-command
                   (fn-own-feed-effect-octets effects)
                   *fn-nntp-max-initial-line-octets*
                   *fn-record-max-payload*)))
    (fn-ores-feed-publication
     word (fn-own-feed-effect-peer effects) records token
     (fn-wire-outbound-octets rendered)
     (if (fn-wire-outbound-okp rendered) :ok (fn-wire-outbound-reason rendered))
     log-line)))

;; The submission path.  host/owner-host.lisp `fn-owner-submission-intent'
;; and `fn-owner-submission-resolution' return exactly these values; the
;; token is the in-flight submission's id.
(defun fn-ores-inflight-token (o)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (and sub (fn-own-sub-id sub))))

; The publication of an intent pair (result . records); the wrapper calls
; fn-icar-submission-intent itself (the subject capability P7 names) and hands
; its value here.
(defun fn-ores-intent-publication (intent token)
  ; Total in INTENT (the host hands it a parsed intent): the executable
  ; accessors refuse nothing, an atom reads as the empty intent, exactly as
  ; the logical car/cdr do.
  (declare (xargs :guard t :verify-guards nil))
  (fn-ores-feed-port-publication
   (mbe :logic (car intent) :exec (if (consp intent) (car intent) nil))
   (mbe :logic (cdr intent) :exec (if (consp intent) (cdr intent) nil))
   nil token nil))
(verify-guards fn-ores-feed-publication)
(verify-guards fn-ores-feed-port-publication)
(verify-guards fn-ores-intent-publication)

(defun fn-ores-submission-intent-publication (o carry evidence generation txid)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ores-intent-publication
   (fn-icar-submission-intent o carry evidence generation txid)
   (fn-ores-inflight-token o)))

; What host/owner-host.lisp fn-owner-submission-intent computes (two calls)
; is the keystone's subject.
(defthm fn-ores-submission-intent-publication-unfolds
  (equal (fn-ores-intent-publication
          (fn-icar-submission-intent o carry evidence generation txid)
          (fn-ores-inflight-token o))
         (fn-ores-submission-intent-publication o carry evidence generation txid)))

(defun fn-ores-resolution-word (o word records)
  (declare (xargs :guard t))
  (cond ((consp records) (fn-feed-journal-kind (car records)))
        ((equal (fn-own-outcome-completion o word) :uncertain) :uncertain)
        (t :none)))

(defun fn-ores-submission-resolution-publication
    (o carry word evidence generation txid)
  (declare (xargs :guard t :verify-guards nil))
  (let ((records (fn-icar-submission-resolution-records
                  o carry word evidence generation txid)))
    (fn-ores-feed-port-publication (fn-ores-resolution-word o word records)
                                   records nil (fn-ores-inflight-token o) nil)))

; KEYSTONE.  The plan is the by-index fetch it replaces: its I-th pair is the
; I-th peer of the old peer list and the seal of the I-th encoded frame, and
; it has exactly one pair per record (so the old "frame/peer count mismatch"
; fault is unreachable by construction).
(defthm fn-ores-len-of-sealed-plan
  (equal (len (fn-ores-sealed-plan records)) (len records)))

(defthm fn-ores-len-of-record-peers
  (equal (len (fn-ores-record-peers records)) (len records)))

(defthm fn-ores-len-of-encode-records
  (equal (len (fn-ores-encode-records records)) (len records)))

(local (defun fn-ores-index-induction (i records)
  (declare (xargs :measure (acl2-count records)))
  (if (and (consp records) (not (zp i)))
      (fn-ores-index-induction (- i 1) (cdr records))
    (list i records))))

(defthm fn-ores-nth-of-sealed-plan
  (equal (nth i (fn-ores-sealed-plan records))
         (if (< (nfix i) (len records))
             (cons (fn-ores-record-peer (nth i records))
                   (fn-ores-seal
                    (fn-feed-encode (fn-feed-journal-kind (nth i records))
                                    (fn-feed-journal-values (nth i records))
                                    *fn-ores-zero-trailer*)))
           nil))
  :hints (("Goal" :induct (fn-ores-index-induction i records)
                  :expand ((fn-ores-sealed-plan records))
                  :in-theory (disable fn-ores-seal fn-ores-record-peer fn-feed-encode
                                      fn-feed-journal-kind fn-feed-journal-values
                                      fn-ores-len-of-sealed-plan))))
(defthm fn-ores-nth-of-record-peers
  (equal (nth i (fn-ores-record-peers records))
         (if (< (nfix i) (len records))
             (fn-ores-record-peer (nth i records))
           nil))
  :hints (("Goal" :induct (fn-ores-index-induction i records)
                  :expand ((fn-ores-record-peers records))
                  :in-theory (disable fn-ores-record-peer fn-ores-len-of-record-peers))))
(defthm fn-ores-frame-item-of-encode-records
  (implies (natp i)
           (equal (fn-frame-item i (fn-ores-encode-records records))
                  (if (< i (len records))
                      (fn-feed-encode (fn-feed-journal-kind (nth i records))
                                      (fn-feed-journal-values (nth i records))
                                      *fn-ores-zero-trailer*)
                    nil)))
  :hints (("Goal" :induct (fn-ores-index-induction i records)
                  :expand ((fn-ores-encode-records records))
                  :in-theory (e/d (fn-frame-item)
                                  (fn-feed-encode fn-feed-journal-kind
                                   fn-feed-journal-values
                                   fn-ores-len-of-encode-records)))))
(defthm fn-ores-sealed-plan-is-indexed-fetch
  ; No hypothesis: past the end both sides are nil, and a non-natural index
  ; is the natural nth and fn-frame-item both read.
  (equal (nth i (fn-ores-sealed-plan records))
         (if (< (nfix i) (len records))
             (cons (nth i (fn-ores-record-peers records))
                   (fn-ores-seal
                    (fn-frame-item (nfix i) (fn-ores-encode-records records))))
           nil))
  :hints (("Goal" :in-theory (disable fn-ores-seal fn-ores-record-peer fn-feed-encode
                                      fn-feed-journal-kind fn-feed-journal-values
                                      fn-ores-sealed-plan fn-ores-record-peers
                                      fn-ores-encode-records))))

; ---------------------------------------------------------------------------
; SubmissionTaken: what fn-owner-take wrote into seven globals.

(defun fn-ores-taken-wordp (x)
  (declare (xargs :guard t))
  (and (member-eq x '(:idle :taken :taken-control :taken-transit)) t))

(defun fn-ores-submission-taken-p (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 9)
       (equal (nth 0 x) :submission-taken)
       (fn-ores-taken-wordp (nth 1 x))
       (or (null (nth 2 x)) (fn-ores-submission-idp (nth 2 x)))
       (fn-cbor-octet-listp (nth 3 x))
       (fn-cbor-octet-listp (nth 4 x))
       (fn-ores-octet-lists-p (nth 5 x))
       ; INTENT (nth 6) is the carry ACL2 keeps for the intent and the
       ; resolution, and PEER (nth 8) the transit submission's peer; the
       ; host reads neither, so neither is checked here (the batch AM
       ; fault: a check on a field the host does not read only adds faults).
       (booleanp (nth 7 x))))

(defun fn-ores-taken-word (x) (declare (xargs :guard t)) (fn-frame-item 1 x))
(defun fn-ores-taken-id (x) (declare (xargs :guard t)) (fn-frame-item 2 x))
(defun fn-ores-taken-msgid (x) (declare (xargs :guard t)) (fn-frame-item 3 x))
(defun fn-ores-taken-octets (x) (declare (xargs :guard t)) (fn-frame-item 4 x))
(defun fn-ores-taken-groups (x) (declare (xargs :guard t)) (fn-frame-item 5 x))
(defun fn-ores-taken-intent (x) (declare (xargs :guard t)) (fn-frame-item 6 x))
(defun fn-ores-taken-transitp (x) (declare (xargs :guard t)) (fn-frame-item 7 x))
(defun fn-ores-taken-peer (x) (declare (xargs :guard t)) (fn-frame-item 8 x))

(defun fn-ores-submission-taken (word id msgid octets groups intent transitp peer)
  (declare (xargs :guard t))
  (list :submission-taken word id msgid octets groups intent transitp peer))

;; The take (host/owner-host.lisp fn-owner-take; host/native/owner.lisp
;; fnn-owner-take checks the recognizer).  This is what fn-owner-take wrote
;; into fn-owner-submit-id, -transitp, -peer, -msgid, -octets, -groups and
;; -intent (fn-ores-take-result-by-definition).  STORED is
;; fn-own-sub-stored-octets of the live configuration, computed by the
;; wrapper (books/owner-served-invariants.lisp is not in this book's closure).
;; A transit take's groups are nil: fn-owner-transit-decide computes them
;; over the live node afterwards.
(defun fn-ores-take-word (sub)
  (declare (xargs :guard t))
  (cond ((fn-own-transit-subp sub) :taken-transit)
        ((fn-own-control-submissionp sub) :taken-control)
        (t :taken)))

(defun fn-ores-take-result (sub stored)
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
     (fn-icar-carry-of sub)
     transitp
     (if transitp (fn-peer-submission-peer decision) nil))))

(defconst *fn-ores-take-idle*
  '(:submission-taken :idle nil nil nil nil nil nil nil))

(defthm fn-ores-take-result-by-definition
  (let ((x (fn-ores-take-result sub stored))
        (decision (fn-own-sub-decision sub)))
    (and (equal (fn-ores-taken-word x)
                (cond ((fn-own-transit-subp sub) :taken-transit)
                      ((fn-own-control-submissionp sub) :taken-control)
                      (t :taken)))
         ; fn-owner-submit-id
         (equal (fn-ores-taken-id x) (fn-own-sub-id sub))
         ; fn-owner-submit-msgid
         (equal (fn-ores-taken-msgid x)
                (if (fn-own-transit-subp sub)
                    (fn-peer-submission-msgid decision)
                  (fn-inj-decision-msgid decision)))
         ; fn-owner-submit-octets
         (equal (fn-ores-taken-octets x) stored)
         ; fn-owner-submit-groups (as the take wrote it)
         (equal (fn-ores-taken-groups x)
                (if (fn-own-transit-subp sub) nil
                  (fn-inj-decision-groups decision)))
         ; fn-owner-submit-intent
         (equal (fn-ores-taken-intent x) (fn-icar-carry-of sub))
         ; fn-owner-submit-transitp, fn-owner-submit-peer
         (equal (fn-ores-taken-transitp x) (fn-own-transit-subp sub))
         (equal (fn-ores-taken-peer x)
                (if (fn-own-transit-subp sub)
                    (fn-peer-submission-peer decision)
                  nil))))
  :hints (("Goal" :in-theory (disable fn-own-transit-subp fn-own-control-submissionp
                                      fn-own-sub-decision fn-own-sub-id
                                      fn-icar-carry-of))))

; The take's id is the in-flight id the submission path's keystones name: a
; take whose submission's id is a submission id answers a well-formed id
; field, and the idle answer is well-formed.
(defthm fn-ores-take-idle-is-a-result
  (fn-ores-submission-taken-p *fn-ores-take-idle*))

; ---------------------------------------------------------------------------
; ServedStep: the served step's reply and flags (fn-owner-install-effects,
; fn-owner-chunk-span-at).

(defun fn-ores-served-step-p (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 8)
       (equal (nth 0 x) :served-step)
       (symbolp (nth 1 x))
       (fn-cbor-octet-listp (nth 2 x))
       (booleanp (nth 3 x))
       (booleanp (nth 4 x))
       (booleanp (nth 5 x))
       (or (null (nth 6 x)) (natp (nth 6 x)))
       (fn-cbor-octet-listp (nth 7 x))))

(defun fn-ores-served-word (x) (declare (xargs :guard t)) (fn-frame-item 1 x))
(defun fn-ores-served-reply (x) (declare (xargs :guard t)) (fn-frame-item 2 x))
(defun fn-ores-served-closep (x) (declare (xargs :guard t)) (fn-frame-item 3 x))
(defun fn-ores-served-starttlsp (x) (declare (xargs :guard t)) (fn-frame-item 4 x))
(defun fn-ores-served-submittedp (x) (declare (xargs :guard t)) (fn-frame-item 5 x))
(defun fn-ores-served-consumed (x) (declare (xargs :guard t)) (fn-frame-item 6 x))
(defun fn-ores-served-log-line (x) (declare (xargs :guard t)) (fn-frame-item 7 x))

(defun fn-ores-served-step (word reply closep starttlsp submittedp consumed log-line)
  (declare (xargs :guard t))
  (list :served-step word reply closep starttlsp submittedp consumed log-line))

; ---------------------------------------------------------------------------
; Capture: the checkpoint capture, in checkpoint-pipeline-5's names and order
; (its host/owner-host.lisp fn-owner-sco-capture answers these ten values
; positionally, 2026-09-27; its LANEDUMP section "The schema"):
;   BASE     the checkpoint the publication extends
;   CONFIGS  the configuration history (by pointer)
;   RECORDS  the record list (by pointer)
;   SEGMENT  the profile's record bound (fn-bs-profile-max-record-octets)
;   COUNT    the records captured (the F row's S)
;   SUFFIX   the records past the durable checkpoint
;   BUDGET   the checkpoint budget (fn-owner-sco-budget)
;   FRONTIER the store's frontier txid at the capture (the F row)
;   FREE     the free octets the host observed (statvfs)
;   REVISION the writer's source revision (a string the host supplies)
; The native host only checks the shape and hands the whole value back to
; ACL2 off the mutex (fnn-owner-publish-captured), so the recognizer checks
; the tag, the length and the three counts the publication's bounds read.
; Wiring fn-owner-sco-capture to return this is that lane's step (or the
; first batch holding both lanes); this book only fixes the names.

(defun fn-ores-capture-p (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 11)
       (equal (nth 0 x) :capture)
       (natp (nth 5 x))
       (natp (nth 6 x))
       (natp (nth 7 x))))

(defun fn-ores-capture-base (x) (declare (xargs :guard t)) (fn-frame-item 1 x))
(defun fn-ores-capture-configs (x) (declare (xargs :guard t)) (fn-frame-item 2 x))
(defun fn-ores-capture-records (x) (declare (xargs :guard t)) (fn-frame-item 3 x))
(defun fn-ores-capture-segment (x) (declare (xargs :guard t)) (fn-frame-item 4 x))
(defun fn-ores-capture-count (x) (declare (xargs :guard t)) (fn-frame-item 5 x))
(defun fn-ores-capture-suffix (x) (declare (xargs :guard t)) (fn-frame-item 6 x))
(defun fn-ores-capture-budget (x) (declare (xargs :guard t)) (fn-frame-item 7 x))
(defun fn-ores-capture-frontier (x) (declare (xargs :guard t)) (fn-frame-item 8 x))
(defun fn-ores-capture-free (x) (declare (xargs :guard t)) (fn-frame-item 9 x))
(defun fn-ores-capture-revision (x) (declare (xargs :guard t)) (fn-frame-item 10 x))

(defun fn-ores-capture (base configs records segment count suffix budget
                             frontier free revision)
  (declare (xargs :guard t))
  (list :capture base configs records segment count suffix budget
        frontier free revision))

; ---------------------------------------------------------------------------
; ConfigResult: the live configuration staging step (fn-owner-reconfigure*,
; and the stage wrappers of host/native-admin-host.lisp and
; host/peer-invite-host.lisp).  :staged carries exactly one encoded
; configuration record; :refused carries ACL2's named reason.

(defun fn-ores-config-result-p (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 4)
       (equal (nth 0 x) :config-result)
       (member-eq (nth 1 x) '(:staged :refused))
       (fn-cbor-octet-listp (nth 2 x))
       (symbolp (nth 3 x))
       (if (eq (nth 1 x) :staged) (consp (nth 2 x)) (null (nth 2 x)))))

(defun fn-ores-config-word (x) (declare (xargs :guard t)) (fn-frame-item 1 x))
(defun fn-ores-config-octets (x) (declare (xargs :guard t)) (fn-frame-item 2 x))
(defun fn-ores-config-reason (x) (declare (xargs :guard t)) (fn-frame-item 3 x))

(defun fn-ores-config-refused (reason)
  (declare (xargs :guard t))
  (list :config-result :refused nil (if (symbolp reason) reason :invalid)))

; The staging step's result: what fn-owner-reconfigure-deltas wrote into
; `fn-owner-config-octets' and `fn-owner-config-reason'.
(defun fn-ores-config-staged-result (staged reason)
  (declare (xargs :guard t))
  (if staged
      (list :config-result :staged (fn-cfg-encode staged) nil)
    (fn-ores-config-refused reason)))

; ---------------------------------------------------------------------------
; The by-definition equations: the value's fields are what the globals held
; under the same owner.  The wrappers are :program mode; each equation is
; over the :logic function the wrapper calls (named in its comment in
; host/owner-host.lisp).

(defthm fn-ores-feed-port-publication-by-definition
  (let ((p (fn-ores-feed-port-publication word records effects token log-line))
        (rendered (fn-wire-render-feed-command
                   (fn-own-feed-effect-octets effects)
                   *fn-nntp-max-initial-line-octets*
                   *fn-record-max-payload*)))
    (and (equal (fn-ores-feedpub-word p) word)
         ; fn-owner-feed-peer
         (equal (fn-ores-feedpub-peer p) (fn-own-feed-effect-peer effects))
         ; fn-owner-feed-records + fn-owner-feed-frames, joined by the keystone
         (equal (fn-ores-feedpub-plan p) (fn-ores-sealed-plan records))
         (equal (fn-ores-feedpub-token p) token)
         ; fn-owner-feed-command
         (equal (fn-ores-feedpub-command p) (fn-wire-outbound-octets rendered))
         ; fn-owner-feed-command-status
         (equal (fn-ores-feedpub-status p)
                (if (fn-wire-outbound-okp rendered) :ok
                  (fn-wire-outbound-reason rendered)))
         ; fn-owner-feed-log-line
         (equal (fn-ores-feedpub-log-line p) log-line))))

(defthm fn-ores-submission-taken-by-definition
  (let ((x (fn-ores-submission-taken word id msgid octets groups intent transitp peer)))
    (and (equal (fn-ores-taken-word x) word)
         (equal (fn-ores-taken-id x) id)
         (equal (fn-ores-taken-msgid x) msgid)
         (equal (fn-ores-taken-octets x) octets)
         (equal (fn-ores-taken-groups x) groups)
         (equal (fn-ores-taken-intent x) intent)
         (equal (fn-ores-taken-transitp x) transitp)
         (equal (fn-ores-taken-peer x) peer))))

(defthm fn-ores-served-step-by-definition
  (let ((x (fn-ores-served-step word reply closep starttlsp submittedp consumed log-line)))
    (and (equal (fn-ores-served-word x) word)
         (equal (fn-ores-served-reply x) reply)
         (equal (fn-ores-served-closep x) closep)
         (equal (fn-ores-served-starttlsp x) starttlsp)
         (equal (fn-ores-served-submittedp x) submittedp)
         (equal (fn-ores-served-consumed x) consumed)
         (equal (fn-ores-served-log-line x) log-line))))

(defthm fn-ores-capture-by-definition
  (let ((x (fn-ores-capture base configs records segment count suffix budget
                            frontier free revision)))
    (and (equal (fn-ores-capture-base x) base)
         (equal (fn-ores-capture-configs x) configs)
         (equal (fn-ores-capture-records x) records)
         (equal (fn-ores-capture-segment x) segment)
         (equal (fn-ores-capture-count x) count)
         (equal (fn-ores-capture-suffix x) suffix)
         (equal (fn-ores-capture-budget x) budget)
         (equal (fn-ores-capture-frontier x) frontier)
         (equal (fn-ores-capture-free x) free)
         (equal (fn-ores-capture-revision x) revision))))

(defthm fn-ores-config-staged-result-by-definition
  (let ((x (fn-ores-config-staged-result staged reason)))
    (and (equal (fn-ores-config-word x) (if staged :staged :refused))
         ; fn-owner-config-octets
         (equal (fn-ores-config-octets x) (if staged (fn-cfg-encode staged) nil))
         ; fn-owner-config-reason
         (equal (fn-ores-config-reason x)
                (if staged nil (if (symbolp reason) reason :invalid))))))

; A refusal, whatever reason it was handed, is a result the host accepts.
(defthm fn-ores-config-refused-is-a-result
  (fn-ores-config-result-p (fn-ores-config-refused reason)))

; ---------------------------------------------------------------------------
; The submission path's results are well-formed (PRF-208, adapter-retirement-2).
;
; host/owner-host.lisp `fn-owner-submission-intent' returns
; `fn-ores-submission-intent-publication' and `fn-owner-submission-resolution'
; returns `fn-ores-submission-resolution-publication'; host/native/owner.lisp
; `fnn-owner-feed-step' checks `fn-ores-feed-publication-p' of each and faults
; (exit 4) when it fails.  Batch AM's image faulted on every `operator post':
; the in-flight id there is `*fn-own-control-id*' and the token recognizer
; admitted only a natural.  These theorems say the check holds on both
; submission paths for every outcome word, under two named conditions:
;
;  - `fn-ores-inflight-idp': the in-flight submission's id, when there is
;    one, is one of the owner's two submission ids (a connection number from
;    `fn-own-read', `*fn-own-control-id*' from the control, BP application
;    and BP transit submits; those are every `fn-own-sub-make' in books/).
;    The owner relation (books/owner-invariants.lisp fn-own-relation) does
;    not yet carry the queue's ids; PKT-616 (c) files that.
;  - `fn-ores-records-sealp': the codec accepts each journal record (a record
;    it refuses seals to :bad; the host faulted there before this lane, with
;    "malformed sealed FNFD frame").

(defun fn-ores-inflight-idp (o)
  (declare (xargs :guard t))
  (let ((token (fn-ores-inflight-token o)))
    (or (null token) (fn-ores-submission-idp token))))

(defun fn-ores-records-sealp (records)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ores-sealed-plan-p (fn-ores-sealed-plan records)))

(defthm fn-ores-feed-port-publication-p-without-effects
  (implies (and (symbolp word)
                (fn-ores-sealed-plan-p (fn-ores-sealed-plan records))
                (fn-ores-tokenp token))
           (fn-ores-feed-publication-p
            (fn-ores-feed-port-publication word records nil token nil)))
  :hints (("Goal" :in-theory (disable fn-ores-sealed-plan fn-ores-sealed-plan-p
                                      fn-ores-tokenp))))

(defthm fn-ores-symbolp-of-submission-intent-word
  (symbolp (car (fn-icar-submission-intent o carry evidence generation txid)))
  :hints (("Goal" :in-theory (union-theories '(fn-icar-submission-intent car-cons)
                                             (theory 'minimal-theory)))))

(defthm fn-ores-car-car-of-feed-resolution-records
  (implies (consp (fn-own-feed-resolution-records
                   kind names msgid identity evidence generation txid tick))
           (equal (car (car (fn-own-feed-resolution-records
                             kind names msgid identity evidence generation txid tick)))
                  kind))
  :hints (("Goal" :expand ((fn-own-feed-resolution-records
                            kind names msgid identity evidence generation txid tick))
                  :in-theory (enable fn-feed-journal-entry))))

(defthm fn-ores-symbolp-of-resolution-word
  (symbolp (fn-ores-resolution-word
            o word (fn-icar-submission-resolution-records
                    o carry word evidence generation txid)))
  :hints (("Goal" :in-theory (disable fn-own-outcome-completion
                                      fn-icar-submission-targets
                                      fn-own-feed-intent-values fn-icar-intent-id))))

; KEYSTONE (the intent).  Host callers, host/native/owner.lisp:
; fnn-owner-drain-one (served and control drains, the operator post's path),
; fnn-owner-complete-bound-submission and
; fnn-owner-complete-bp-transit-submission.
(defthm fn-ores-submission-intent-publication-is-well-formed
  (implies (and (fn-ores-inflight-idp o)
                (fn-ores-records-sealp
                 (cdr (fn-icar-submission-intent o carry evidence generation txid))))
           (fn-ores-feed-publication-p
            (fn-ores-submission-intent-publication o carry evidence generation txid)))
  :hints (("Goal" :in-theory (e/d (fn-ores-records-sealp fn-ores-tokenp
                                   fn-ores-intent-publication)
                                  (fn-icar-submission-intent fn-ores-feed-port-publication
                                   fn-ores-feed-publication-p fn-ores-sealed-plan
                                   fn-ores-sealed-plan-p
                                   fn-ores-feed-port-publication-p-without-effects))
                  :use ((:instance fn-ores-feed-port-publication-p-without-effects
                                   (word (car (fn-icar-submission-intent
                                               o carry evidence generation txid)))
                                   (records (cdr (fn-icar-submission-intent
                                                  o carry evidence generation txid)))
                                   (token (fn-ores-inflight-token o)))))))

; KEYSTONE (the resolution; the same three host callers, after the outcome).
(defthm fn-ores-submission-resolution-publication-is-well-formed
  (implies (and (fn-ores-inflight-idp o)
                (fn-ores-records-sealp
                 (fn-icar-submission-resolution-records
                  o carry word evidence generation txid)))
           (fn-ores-feed-publication-p
            (fn-ores-submission-resolution-publication
             o carry word evidence generation txid)))
  :hints (("Goal" :in-theory (e/d (fn-ores-records-sealp fn-ores-tokenp)
                                  (fn-icar-submission-resolution-records
                                   fn-ores-resolution-word
                                   fn-ores-feed-port-publication
                                   fn-ores-feed-publication-p fn-ores-sealed-plan
                                   fn-ores-sealed-plan-p
                                   fn-ores-feed-port-publication-p-without-effects))
                  :use ((:instance fn-ores-feed-port-publication-p-without-effects
                                   (word (fn-ores-resolution-word
                                          o word
                                          (fn-icar-submission-resolution-records
                                           o carry word evidence generation txid)))
                                   (records (fn-icar-submission-resolution-records
                                             o carry word evidence generation txid))
                                   (token (fn-ores-inflight-token o)))))))
