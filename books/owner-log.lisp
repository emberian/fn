; fn: the native owner's service log lines.
;
; One line per submission the owner completes (a served POST and a local
; control post) and one per connection it accepts, outcome word first,
; rendered here from ACL2's own classification so the log says what the
; reply says: a served line reads `accepted' exactly when
; fn-own-outcome-completion is :durable, the completion fn-own-outcome
; renders into the 240, and a control line carries the word
; fn-own-control-outcome-result gives the control reply.  The host
; (host/owner-host.lisp fn-owner-outcome, fn-owner-control-outcome,
; fn-owner-open, fn-owner-open-peer) reads the line off the owner BEFORE the
; event moves it and leaves it in the global `fn-owner-log-line'; the native
; owner (host/native/owner.lisp fnn-owner-log) writes those octets and one
; LF to the configured `[log] path' or to stderr, and decides nothing.
;
; Every rendered field passes through fn-olog-visible, which keeps at most
; 256 octets and turns every octet outside 33..126 into `?', so a line is one
; line whatever a client sent (fn-olog-served-post-line-is-one-line and its
; two siblings).  There is no rotation: the file is opened append-only and
; the operator's log tooling owns its size.

(in-package "ACL2")
(include-book "owner")

(defconst *fn-olog-max-field-octets* 256)

(defun fn-olog-text (s)
  (declare (xargs :guard t))
  (fn-record-string-octets s))

(defun fn-olog-visible-aux (xs n)
  ; Each octet outside 33..126 becomes `?', and at most N are kept.
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (and (consp xs) (not (zp n)))
      (cons (if (and (natp (car xs)) (<= 33 (car xs)) (<= (car xs) 126))
                (car xs)
              63)
            (fn-olog-visible-aux (cdr xs) (1- n)))
    nil))

(defun fn-olog-visible (xs)
  (declare (xargs :guard t))
  (fn-olog-visible-aux xs *fn-olog-max-field-octets*))

(defun fn-olog-strip-zeros (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (consp (cdr xs)) (equal (car xs) 48))
      (fn-olog-strip-zeros (cdr xs))
    xs))

(defun fn-olog-decimal (n)
  (declare (xargs :guard t))
  (fn-olog-strip-zeros (fn-inj-digits n 20)))

(defun fn-olog-time (obs)
  "YYYY-MM-DDTHH:MM:SSZ of the owner's wall reading, or `none'."
  (declare (xargs :guard t))
  (if (and (fn-clock-observationp obs) (fn-clock-has-wall obs))
      (let ((i (fn-inj-instant-of (fn-clock-wall obs))))
        (fn-inj-append
         (fn-inj-digits (fn-inj-instant-year i) 4)
         (cons 45
         (fn-inj-append
          (fn-inj-digits (fn-inj-instant-month i) 2)
          (cons 45
          (fn-inj-append
           (fn-inj-digits (fn-inj-instant-day i) 2)
           (cons 84
           (fn-inj-append
            (fn-inj-digits (fn-inj-instant-hour i) 2)
            (cons 58
            (fn-inj-append
             (fn-inj-digits (fn-inj-instant-minute i) 2)
             (cons 58
             (fn-inj-append
              (fn-inj-digits (fn-inj-instant-second i) 2)
              (list 90)))))))))))))
    (fn-olog-text "none")))

(defun fn-olog-join (parts)
  ; PARTS joined by one space.
  (declare (xargs :guard t))
  (if (consp parts)
      (if (consp (cdr parts))
          (append (true-list-fix (car parts))
                  (cons 32 (fn-olog-join (cdr parts))))
        (true-list-fix (car parts)))
    nil))

(defun fn-olog-field (name value)
  (declare (xargs :guard t))
  (append (fn-olog-text name) (cons 61 (fn-olog-visible value))))

(defun fn-olog-class-word (class)
  (declare (xargs :guard t))
  (cond ((equal class :accepted) (fn-olog-text "accepted"))
        ((equal class :duplicate) (fn-olog-text "duplicate"))
        ((equal class :refused) (fn-olog-text "refused"))
        (t (fn-olog-text "uncertain"))))

; -----------------------------------------------------------------------------
; The lines

; A served submission's outcome in the words its reply uses: the completion
; fn-own-outcome renders (fn-served-post-outcome), so `accepted' only for a
; completion consumed after the take, and a host :duplicate is the refusal
; the client was sent.
(defun fn-olog-served-class (o word)
  (declare (xargs :guard t))
  (let ((completion (fn-own-outcome-completion o word)))
    (cond ((equal completion :durable) :accepted)
          ((equal completion :refused) :refused)
          (t :uncertain))))

(defun fn-olog-served-post-line (o id word)
  "The line for served submission ID completing with host word WORD.

Read from the owner before fn-own-outcome consumes the in-flight
submission.  The agent is the one the connection pinned, which is the one
its article's Injection-Info names (books/owner-agent.lisp)."
  (declare (xargs :guard t))
  (let* ((sub (fn-own-inflight o))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (agent (if conn
                    (fn-inj-config-agent (fn-own-conn-config conn))
                  (fn-inj-config-agent (fn-own-config o)))))
    (fn-olog-join
     (list (fn-olog-class-word (fn-olog-served-class o word))
           (fn-olog-text "post")
           (fn-olog-field "path" (fn-olog-text "served"))
           (fn-olog-field "connection" (fn-olog-decimal id))
           (fn-olog-field "message-id" (fn-own-sub-msgid sub))
           (fn-olog-field "agent" agent)
           (fn-olog-field "time" (fn-olog-time (fn-own-clock o)))))))

(defun fn-olog-control-post-line (o word)
  "The line for the local-control submission in flight completing with WORD.

A control post stores an already-authored article exactly
(fn-own-control-decision): no injecting agent writes a field into it, so the
line names none."
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o))
        (class (fn-own-control-outcome-result o word)))
    (fn-olog-join
     (list (fn-olog-class-word class)
           (fn-olog-text "post")
           (fn-olog-field "path" (fn-olog-text "control"))
           (fn-olog-field "message-id" (fn-own-sub-msgid sub))
           (fn-olog-field "time" (fn-olog-time (fn-own-clock o)))))))

(defun fn-olog-connection-line (o id peer)
  "The line for connection ID the owner just opened; PEER is the record name
the owner resolved the source address to, or nil for a reader."
  (declare (xargs :guard t))
  (fn-olog-join
   (if peer
       (list (fn-olog-text "accepted") (fn-olog-text "peer")
             (fn-olog-field "connection" (fn-olog-decimal id))
             (fn-olog-field "peer" peer)
             (fn-olog-field "time" (fn-olog-time (fn-own-clock o))))
     (list (fn-olog-text "accepted") (fn-olog-text "reader")
           (fn-olog-field "connection" (fn-olog-decimal id))
           (fn-olog-field "time" (fn-olog-time (fn-own-clock o)))))))

;; -----------------------------------------------------------------------------
;; Peer transfer lines: the receiver's transit outcome and the sender's feed
;; reply.  Before these, a peer transfer that was refused left no line on
;; either side (native subsets 1a9dd747, failure 8: a signed carrier refused
;; for want of receiver-local enrollment answered 439 and both owners were
;; silent).  The code on each line is the code on the wire: the receiver's
;; is fn-peer-transit-code over the same decision and completion
;; fn-own-transit-outcome renders; the sender's is the one ACL2 parsed.

; A keyword's name in lower case (`:local-enrollment' reads
; `local-enrollment'); anything else reads `none'.
(defun fn-olog-downcase-octets (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (if (and (natp (car xs)) (<= 65 (car xs)) (<= (car xs) 90))
                (+ 32 (car xs))
              (car xs))
            (fn-olog-downcase-octets (cdr xs)))
    nil))

(defun fn-olog-symbol-text (x)
  (declare (xargs :guard t))
  (if (and (symbolp x) x)
      (fn-olog-downcase-octets (fn-olog-text (symbol-name x)))
    (fn-olog-text "none")))

; The class a peer-transfer code carries: the three outcomes stay distinct,
; and a deferral (the peer is asked to retry) is named as one.
(defun fn-olog-code-class-word (code)
  (declare (xargs :guard t))
  (cond ((member-equal code '(235 239)) (fn-olog-text "accepted"))
        ((member-equal code '(435 438)) (fn-olog-text "duplicate"))
        ((member-equal code '(437 439)) (fn-olog-text "refused"))
        ((member-equal code '(431 436)) (fn-olog-text "deferred"))
        (t (fn-olog-text "uncertain"))))

; The completion fn-own-transit-outcome renders with: the owner's completion
; for the host word when the transfer decision was :want, else none.
(defun fn-olog-transit-completion (o kind word)
  (declare (xargs :guard t))
  (if (equal kind :want) (fn-own-outcome-completion o word) nil))

(defun fn-olog-transit-code (o kind reason word)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (fn-peer-transit-code
     (fn-peer-submission-kind (fn-own-sub-decision sub))
     (fn-peer-decision kind reason)
     (fn-olog-transit-completion o kind word))))

; An uncertain completion is uncertain whatever its code (436 also names a
; deferral); every other line is classed by the code the peer was sent.
(defun fn-olog-transit-class-word (o kind reason word)
  (declare (xargs :guard t))
  (if (equal (fn-olog-transit-completion o kind word) :uncertain)
      (fn-olog-text "uncertain")
    (fn-olog-code-class-word (fn-olog-transit-code o kind reason word))))

(defun fn-olog-transit-line (o id kind reason word detail)
  "The line for transit submission ID completing with KIND, REASON and WORD.

Read from the owner before fn-own-transit-outcome consumes the in-flight
submission, with the same arguments.  DETAIL is the ACL2 refusal the host
relays from the ingress attempt (fn-pa-current-plan's `:local-enrollment',
for one), or nil."
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (fn-olog-join
     (list (fn-olog-transit-class-word o kind reason word)
           (fn-olog-text "transit")
           (fn-olog-field "connection" (fn-olog-decimal id))
           (fn-olog-field "message-id" (fn-own-sub-msgid sub))
           (fn-olog-field "code"
                          (fn-olog-decimal (fn-olog-transit-code o kind reason word)))
           (fn-olog-field "decision" (fn-olog-symbol-text kind))
           (fn-olog-field "reason" (fn-olog-symbol-text reason))
           (fn-olog-field "detail" (fn-olog-symbol-text detail))
           (fn-olog-field "time" (fn-olog-time (fn-own-clock o)))))))

; A feed name as octets: the feed's peer is a string, its Message-ID the
; octets fn-feed-namep admits.
(defun fn-olog-name-octets (x)
  (declare (xargs :guard t))
  (if (stringp x) (fn-olog-text x) x))

; The sender's line for one parsed feed reply, or nil for a 335/238 (the
; peer asked for the article; the TAKETHIS/IHAVE body is not an outcome).
(defun fn-olog-feed-reply-line (o peer response)
  (declare (xargs :guard t))
  (let ((code (fn-feed-response-code response)))
    (if (member-equal code '(335 238))
        nil
      (fn-olog-join
       (list (fn-olog-code-class-word code)
             (fn-olog-text "feed")
             (fn-olog-field "peer" (fn-olog-name-octets peer))
             (fn-olog-field "message-id"
                            (fn-olog-name-octets
                             (fn-feed-response-msgid response)))
             (fn-olog-field "code" (fn-olog-decimal code))
             (fn-olog-field "time" (fn-olog-time (fn-own-clock o))))))))

;; -----------------------------------------------------------------------------
;; The store's swallowed staging cleanup.  P-RECORD (specs/crash-model-v2.md)
;; ends with a best-effort unlink of the stage and a barrier on staging after
;; the record's directory barrier: the record is durable, the reply is 240,
;; and an error there changes no outcome.  Before this line the host
;; (host/native/io.lisp fnn-publish) discarded that error and wrote nothing,
;; so a persistent EIO in staging cleanup was silent on every post
;; (planning/evidence/probe-tables-2026-09-24.md, S1).  The host renders this
;; line once per swallowed error and writes it through the owner's log path.
;; Its first word is `failed', never an outcome word: the submission's own
;; line still says what the reply said.

; STEP is the cleanup step that was running (:unlink, or :directory-barrier
; once the unlink returned); NAME the staging path, SEQUENCE the sequence the
; durable record was published under, ERRNO the OS errno or nil when the
; condition carried none, and TEXT the condition's report as the host gave it.
(defun fn-olog-staging-cleanup-line (step name sequence errno text)
  (declare (xargs :guard t))
  (fn-olog-join
   (list (fn-olog-text "failed")
         (fn-olog-text "staging")
         (fn-olog-text "cleanup")
         (fn-olog-field "step" (fn-olog-symbol-text step))
         (fn-olog-field "sequence" (fn-olog-decimal sequence))
         (fn-olog-field "name" (fn-olog-name-octets name))
         (fn-olog-field "errno" (if (natp errno)
                                    (fn-olog-decimal errno)
                                  (fn-olog-text "none")))
         (fn-olog-field "error" (fn-olog-name-octets text)))))

; -----------------------------------------------------------------------------
; A line is one line

(defun fn-olog-no-breakp (xs)
  ; No octet of XS is LF or CR.
  (declare (xargs :guard t))
  (if (consp xs)
      (and (not (equal (car xs) 10))
           (not (equal (car xs) 13))
           (fn-olog-no-breakp (cdr xs)))
    t))

(local
 (defthm fn-olog-no-break-of-append
   (equal (fn-olog-no-breakp (append a b))
          (and (fn-olog-no-breakp a) (fn-olog-no-breakp b)))))

(local
 (defthm fn-olog-no-break-of-true-list-fix
   (equal (fn-olog-no-breakp (true-list-fix a))
          (fn-olog-no-breakp a))))

(defthm fn-olog-visible-aux-has-no-break
  (fn-olog-no-breakp (fn-olog-visible-aux xs n)))

(local
 (defthm fn-olog-field-has-no-break
   (implies (fn-olog-no-breakp (fn-olog-text name))
            (fn-olog-no-breakp (fn-olog-field name value)))
   :hints (("Goal" :in-theory (e/d (fn-olog-field fn-olog-visible)
                                   (fn-olog-text fn-olog-visible-aux-has-no-break))
            :use ((:instance fn-olog-visible-aux-has-no-break
                             (xs value) (n *fn-olog-max-field-octets*)))))))

(local
 (defthm fn-olog-class-word-has-no-break
   (fn-olog-no-breakp (fn-olog-class-word class))))

(defun fn-olog-parts-no-breakp (parts)
  (declare (xargs :guard t))
  (if (consp parts)
      (and (fn-olog-no-breakp (car parts))
           (fn-olog-parts-no-breakp (cdr parts)))
    t))

(local
 (defthm fn-olog-join-has-no-break
   (implies (fn-olog-parts-no-breakp parts)
            (fn-olog-no-breakp (fn-olog-join parts)))))

(local (in-theory (disable fn-olog-field fn-olog-class-word fn-olog-no-breakp
                           fn-olog-text fn-olog-decimal fn-olog-time)))

(defthm fn-olog-served-post-line-is-one-line
  (fn-olog-no-breakp (fn-olog-served-post-line o id word))
  :hints (("Goal" :in-theory (disable fn-olog-join))))

(defthm fn-olog-control-post-line-is-one-line
  (fn-olog-no-breakp (fn-olog-control-post-line o word))
  :hints (("Goal" :in-theory (disable fn-olog-join))))

(defthm fn-olog-connection-line-is-one-line
  (fn-olog-no-breakp (fn-olog-connection-line o id peer))
  :hints (("Goal" :in-theory (disable fn-olog-join))))

(local
 (defthm fn-olog-code-class-word-has-no-break
   (fn-olog-no-breakp (fn-olog-code-class-word code))
   :hints (("Goal" :in-theory (enable fn-olog-code-class-word fn-olog-text
                                      fn-olog-no-breakp)))))

(defthm fn-olog-transit-line-is-one-line
  (fn-olog-no-breakp (fn-olog-transit-line o id kind reason word detail))
  :hints (("Goal" :in-theory (e/d (fn-olog-transit-class-word)
                                  (fn-olog-join fn-olog-code-class-word
                                   fn-olog-transit-code fn-olog-symbol-text)))))

(defthm fn-olog-feed-reply-line-is-one-line
  (fn-olog-no-breakp (fn-olog-feed-reply-line o peer response))
  :hints (("Goal" :in-theory (disable fn-olog-join fn-olog-code-class-word))))

; Whatever octets the staging path or the OS error text held.
(defthm fn-olog-staging-cleanup-line-is-one-line
  (fn-olog-no-breakp (fn-olog-staging-cleanup-line step name sequence errno text))
  :hints (("Goal" :in-theory (disable fn-olog-join fn-olog-symbol-text
                                      fn-olog-name-octets))))

; -----------------------------------------------------------------------------
; The log says what the reply says

(defun fn-olog-line-word (line)
  ; The octets before the first space.
  (declare (xargs :guard t))
  (if (and (consp line) (not (equal (car line) 32)))
      (cons (car line) (fn-olog-line-word (cdr line)))
    nil))

; KEYSTONE.  A served line says `accepted' exactly when the owner's
; completion for the word is :durable -- the completion fn-own-outcome hands
; fn-served-post-outcome, which is the only path to a 240
; (fn-own-durable-reply-names-a-durable-record).  A host word alone never
; makes the line say accepted.
(defthm fn-olog-served-post-line-says-accepted-iff-durable
  (equal (equal (fn-olog-line-word (fn-olog-served-post-line o id word))
                (fn-olog-text "accepted"))
         (equal (fn-own-outcome-completion o word) :durable))
  :hints (("Goal" :in-theory (e/d (fn-olog-class-word fn-olog-text)
                                  (fn-own-outcome-completion fn-olog-field
                                   fn-olog-decimal fn-olog-time)))))

; A control line's first word is the control reply's word.
(defthm fn-olog-control-post-line-says-the-control-result
  (equal (fn-olog-line-word (fn-olog-control-post-line o word))
         (fn-olog-class-word (fn-own-control-outcome-result o word)))
  :hints (("Goal" :in-theory (e/d (fn-olog-class-word fn-olog-text)
                                  (fn-own-control-outcome-result fn-olog-field
                                   fn-olog-decimal fn-olog-time)))))

; KEYSTONE (receiver).  A transit line says `refused' exactly when the code
; the peer was sent is a rejection (437/439) and the completion was not
; uncertain -- the same fn-peer-transit-code fn-own-transit-outcome renders,
; so the log names the refusal the wire carried, never a host word.
(defthm fn-olog-transit-line-says-refused-iff-rejected
  (equal (equal (fn-olog-line-word
                 (fn-olog-transit-line o id kind reason word detail))
                (fn-olog-text "refused"))
         (and (not (equal (fn-olog-transit-completion o kind word) :uncertain))
              (if (member-equal (fn-olog-transit-code o kind reason word)
                                '(437 439))
                  t nil)))
  :hints (("Goal" :in-theory (e/d (fn-olog-transit-class-word
                                   fn-olog-code-class-word fn-olog-text)
                                  (fn-olog-transit-code fn-olog-transit-completion
                                   fn-olog-field fn-olog-decimal fn-olog-time
                                   fn-olog-symbol-text)))))

; KEYSTONE (sender).  A feed line exists exactly for a reply that is not a
; send-it prompt, and its first word is the class of the code ACL2 parsed.
(defthm fn-olog-feed-reply-line-says-the-code-class
  (equal (fn-olog-line-word (fn-olog-feed-reply-line o peer response))
         (if (member-equal (fn-feed-response-code response) '(335 238))
             nil
           (fn-olog-code-class-word (fn-feed-response-code response))))
  :hints (("Goal" :in-theory (e/d (fn-olog-code-class-word fn-olog-text)
                                  (fn-olog-field fn-olog-decimal fn-olog-time)))))
