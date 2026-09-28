; fn: what a local consumer command tells its caller (PKT-709, PKT-710;
; lane friend-blockers-2, the stranger rehearsal's stop 7).
;
; Three things a program driving `fn consumer' needs and did not have:
;
; 1. The refusal's reason on the wire.  The consumer replies (FNCT kinds 5,
;    6 and 9, books/consumer-local-control.lisp) carry a status and no
;    reason, and their payloads are exactly their fields, so a reason
;    appended to them would turn an old client's refusal into a frame it
;    cannot read (uncertain).  The reason therefore travels as PKT-453's
;    does (books/native-control-reason.lisp): the new client sends the
;    consumer request's payload, unchanged, in FNCT kind 22; the owner
;    answers such a frame's refusal (and a fault or an uncertain end) with
;    the reasoned reply, kind 18 (the status and the reason word), and its
;    acceptance with the consumer reply it always sent.  An old owner cannot
;    decode kind 22 and answers the plain refusal (kind 2) before acting on
;    anything; the new client then sends the kind-4 request once
;    (`fn-native-control-reasoned-client-step''s :resend).  An old client
;    never sends kind 22 and never receives kind 18.
;
; 2. One JSON line per command (`fn consumer --json COMMAND ...'), rendered
;    here from the outcome, the reason word and the decoded report, so an
;    agent reads results without parsing prose or cursor bytes.  Every
;    octet of the line is printable ASCII (`fn-ncr-json-object-is-ascii').
;
; 3. The withdrawal report (PKT-710): what a poll delivers in place of an
;    article its author's cancel (or a supersession) withdrew: the magic
;    "FNWD", version 1, then the withdrawn article's Message-ID octets.  No
;    article content is in it (`fn-ncr-withdrawal-report' reads the
;    Message-ID alone).  The owner's decision to deliver one is
;    books/consumer-withdrawal.lisp's; this book holds the byte form both
;    sides read, below the owner.
;
; Host callers: host/native-control-host.lisp
; `fn-native-control-host-consumer-reasoned-request-encode', `-decode',
; `-framep', `fn-native-control-host-consumer-client-read',
; `fn-native-control-host-consumer-json-line',
; `fn-native-control-host-consumer-report-summary' and
; `fn-native-control-host-consumer-cli-after', which
; host/native/control.lisp and host/native/consumer-local.lisp call.
;
; Prefix `fn-ncr-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "consumer-wait-codec")
(include-book "native-control-reason")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; 1. The reasoned consumer request (FNCT kind 22).

(defconst *fn-ncr-request-kind* 22)

; The kind-4 request's payload in the kind-22 frame, or :bad exactly when
; the plain encoder refuses.
(defun fn-ncr-request-encode (kind first second)
  (declare (xargs :guard t))
  (let* ((plain (fn-cwait-request-encode kind first second))
         (opened (fn-nctrl-open plain *fn-ncl-request-kind*)))
    (if (fn-frame-result-okp opened)
        (fn-nctrl-seal *fn-ncr-request-kind* (fn-frame-result-payload opened))
      :bad)))

; The owner's decode: the kind-22 frame's payload decided exactly as the
; kind-4 request with that payload (`fn-ncr-request-decode-is-the-plain-decode').
(defun fn-ncr-request-decode (octets)
  (declare (xargs :guard t))
  (let ((opened (fn-nctrl-open octets *fn-ncr-request-kind*)))
    (if (fn-frame-result-okp opened)
        (fn-cwait-request-decode
         (fn-nctrl-seal *fn-ncl-request-kind* (fn-frame-result-payload opened)))
      (list :refused :frame))))

; Whether a frame asked for the reasoned consumer reply.
(defun fn-ncr-framep (octets)
  (declare (xargs :guard t))
  (fn-frame-result-okp (fn-nctrl-open octets *fn-ncr-request-kind*)))

(defthm fn-ncr-request-decode-is-the-plain-decode
  (implies (and (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-nctrl-max-payload*))
           (equal (fn-ncr-request-decode
                   (fn-nctrl-seal *fn-ncr-request-kind* payload))
                  (fn-cwait-request-decode
                   (fn-nctrl-seal *fn-ncl-request-kind* payload))))
  :hints (("Goal" :use ((:instance fn-nctrl-open-of-seal
                                   (kind *fn-ncr-request-kind*)))
           :in-theory (e/d (fn-ncr-request-decode fn-frame-result-okp
                            fn-frame-ok fn-frame-result-payload)
                           (fn-nctrl-open-of-seal fn-nctrl-open fn-nctrl-seal
                            fn-cwait-request-decode)))))

(defthm fn-ncr-framep-of-seal
  (implies (and (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-nctrl-max-payload*))
           (fn-ncr-framep (fn-nctrl-seal *fn-ncr-request-kind* payload)))
  :hints (("Goal" :use ((:instance fn-nctrl-open-of-seal
                                   (kind *fn-ncr-request-kind*)))
           :in-theory (e/d (fn-ncr-framep fn-frame-result-okp fn-frame-ok)
                           (fn-nctrl-open-of-seal fn-nctrl-open fn-nctrl-seal)))))

; -----------------------------------------------------------------------------
; The client's read of the owner's answer to a kind-22 request.

; The consumer reply decoder the operation's answer uses.
(defun fn-ncr-consumer-reply-decode (operation octets)
  (declare (xargs :guard t))
  (case operation
    ((:poll :bound-poll :wait :bound-wait) (fn-ncl-poll-reply-decode octets))
    (:status (fn-ncl-status-reply-decode octets))
    (otherwise (fn-ncl-reply-decode octets))))

; (:status STATUS WORD) from a reasoned reply (the owner refused, or ended
; uncertain or in a fault, and named why), (:reply REPLY) from the consumer
; reply the owner sends an acceptance on, (:resend) for an old owner's plain
; refusal of a frame it could not decode, (:status STATUS NONE) for its other
; plain statuses, else (:transport).
(defun fn-ncr-client-read (operation octets)
  (declare (xargs :guard t))
  (let ((reasoned (fn-native-control-reasoned-reply-read octets)))
    (if (and (consp reasoned) (member-equal (car reasoned) *fn-nctrl-statuses*))
        (fn-native-control-reasoned-client-step reasoned)
      (let ((reply (fn-ncr-consumer-reply-decode operation octets)))
        (if (and (consp reply)
                 (member-eq (car reply) '(:consumer-reply :consumer-poll-reply
                                          :consumer-status-reply)))
            (list :reply reply)
          (fn-native-control-reasoned-client-step reasoned))))))

; KEYSTONE (PKT-709: the printed consumer refusal names the owner's reason).
; The owner seals its decision's status and reason
; (host/native/control.lisp fnn-control-reply-octets through
; `fn-native-control-host-reasoned-reply-encode'); the consumer client
; reads that frame with `fn-ncr-client-read' (host/native/control.lisp
; fnn-control-consumer-local through
; `fn-native-control-host-consumer-client-read') for whatever operation it
; sent, and prints the word `fn-native-control-reply-detail' answers
; (host/native/consumer-local.lisp fnn-command-consumer-local).  For every
; status the client reads the owner's status and word; for a refusal that
; named a reason the printed word is exactly the reason's.
(defthm fn-ncr-printed-reason-is-the-decisions
  (implies (member-equal status *fn-nctrl-statuses*)
           (let ((read (fn-ncr-client-read
                        operation
                        (fn-native-control-reasoned-reply-encode status reason))))
             (and (equal read (list :status status (fn-nctrl-reason-word reason)))
                  (implies (and (equal (fn-native-control-status-class status)
                                       :refused)
                                reason)
                           (equal (fn-native-control-reply-detail
                                   (cadr read) (caddr read))
                                  (fn-nctrl-reason-word reason))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nctrl-reasoned-read-of-encode)
                 (:instance fn-native-control-printed-reason-is-the-decisions))
           :in-theory (e/d (fn-ncr-client-read)
                           (fn-nctrl-reasoned-read-of-encode
                            fn-native-control-printed-reason-is-the-decisions
                            fn-ncr-consumer-reply-decode
                            fn-native-control-reasoned-reply-read
                            fn-native-control-reasoned-reply-encode
                            member-equal (:e member-equal))))))

; -----------------------------------------------------------------------------
; The command line: `fn consumer --json COMMAND ...' is COMMAND's plan with
; the JSON line for its output; every other line is `fn-cwait-cli-plan''s,
; unchanged (`fn-ncr-cli-plan-without-the-flag-by-definition').

(defconst *fn-ncr-json-flag* '(45 45 106 115 111 110)) ; --json

(defun fn-ncr-cli-plan (command argv)
  (declare (xargs :guard t))
  (if (equal command *fn-ncr-json-flag*)
      (list :json (fn-cwait-cli-plan (and (consp argv) (car argv))
                                     (and (consp argv) (cdr argv))))
    (fn-cwait-cli-plan command argv)))

(defthm fn-ncr-cli-plan-without-the-flag-by-definition
  (implies (not (equal command *fn-ncr-json-flag*))
           (equal (fn-ncr-cli-plan command argv)
                  (fn-cwait-cli-plan command argv))))

; -----------------------------------------------------------------------------
; `register' on a node whose consumer history was never made (PKT-709).  The
; host sends the register once; when the owner refuses it for want of that
; history (the word `unbootstrapped'), or an old owner refused it with no
; word (NONE), the host sends these steps, bootstrap then the register again,
; and the last one's outcome is the command's.  A register refused for any
; other named reason, and every outcome that is not a refusal (an uncertain
; one above all), sends nothing more.

(defconst *fn-ncr-unbootstrapped-word*
  '(117 110 98 111 111 116 115 116 114 97 112 112 101 100)) ; unbootstrapped

(defun fn-ncr-cli-after (operation status word)
  (declare (xargs :guard t))
  (if (and (equal operation :register) (equal status :refused)
           (or (equal word *fn-ncr-unbootstrapped-word*)
               (equal word *fn-nctrl-no-reason-word*)))
      (list :bootstrap :register)
    nil))

(defthm fn-ncr-cli-after-retries-only-an-unbootstrapped-register
  (iff (fn-ncr-cli-after operation status word)
       (and (equal operation :register) (equal status :refused)
            (or (equal word *fn-ncr-unbootstrapped-word*)
                (equal word *fn-nctrl-no-reason-word*)))))

; -----------------------------------------------------------------------------
; 3. The withdrawal report (PKT-710).

(defconst *fn-ncr-withdrawal-magic* '(70 78 87 68 1)) ; FNWD, version 1

; The report for the article whose Message-ID octets are MSGID, or nil when
; MSGID is no Message-ID the report can carry.  Its length is the magic's
; five octets plus the Message-ID's.
(defun fn-ncr-withdrawal-report (msgid)
  (declare (xargs :guard t))
  (if (and (consp msgid) (fn-cbor-octet-listp msgid)
           (<= (len msgid) *fn-cp-max-token*))
      (append *fn-ncr-withdrawal-magic* msgid)
    nil))

(defun fn-ncr-withdrawal-decode (octets)
  (declare (xargs :guard t))
  (if (and (true-listp octets)
           (< 5 (len octets))
           (equal (take 5 octets) *fn-ncr-withdrawal-magic*)
           (fn-cbor-octet-listp (nthcdr 5 octets))
           (<= (len (nthcdr 5 octets)) *fn-cp-max-token*))
      (list :withdrawn (nthcdr 5 octets))
    (list :refused :withdrawal)))

(local
 (defthm fn-ncr-take-and-drop-of-magic
   (and (equal (take 5 (append *fn-ncr-withdrawal-magic* x))
               *fn-ncr-withdrawal-magic*)
        (equal (nthcdr 5 (append *fn-ncr-withdrawal-magic* x)) x))))

(defthm fn-ncr-withdrawal-roundtrip
  (implies (fn-ncr-withdrawal-report msgid)
           (equal (fn-ncr-withdrawal-decode (fn-ncr-withdrawal-report msgid))
                  (list :withdrawn msgid)))
  :hints (("Goal" :in-theory (enable fn-ncr-withdrawal-report
                                     fn-ncr-withdrawal-decode))))

; A withdrawal report is an event report the poll reply carries.
(defthm fn-ncr-withdrawal-report-fits-the-poll-reply
  (implies (fn-ncr-withdrawal-report msgid)
           (fn-ncl-poll-event-bytesp (fn-ncr-withdrawal-report msgid)))
  :hints (("Goal" :in-theory (enable fn-ncr-withdrawal-report
                                     fn-ncl-poll-event-bytesp))))

; -----------------------------------------------------------------------------
; What a poll report is, for the caller (the report decoder PKT-709 asks
; for): (:empty), (:withdrawn MSGID), (:article MSGID PAYLOAD) with the
; stored article's octets, or (:unreadable).  MSGID is octets.
(defun fn-ncr-report-summary (octets)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((null octets) (list :empty))
        ((equal (car (fn-ncr-withdrawal-decode octets)) :withdrawn)
         (list :withdrawn (cadr (fn-ncr-withdrawal-decode octets))))
        (t (let ((article (fn-cwait-report-article octets)))
             (if (and (equal (car article) :ok) (stringp (cadr article)))
                 (list :article (fn-record-string-octets (cadr article))
                       (caddr article))
               (list :unreadable))))))

; -----------------------------------------------------------------------------
; 2. The JSON line.

(defun fn-ncr-hex-digit (n)
  (declare (xargs :guard t))
  (let ((n (nfix n)))
    (if (< n 10) (+ 48 n) (+ 87 (min n 15)))))

; One octet inside a JSON string: printable ASCII but `"' and `\' as
; itself, those two escaped, every other octet as \u00XX.
(defun fn-ncr-json-octet (x)
  (declare (xargs :guard t))
  (let ((x (nfix x)))
    (cond ((or (equal x 34) (equal x 92)) (list 92 x))
          ((and (<= 32 x) (<= x 126)) (list x))
          (t (list 92 117 48 48
                   (fn-ncr-hex-digit (floor (min x 255) 16))
                   (fn-ncr-hex-digit (mod (min x 255) 16)))))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-ncr-json-escape-loop (octets acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp octets)
      (fn-ncr-json-escape-loop (cdr octets)
                               (fn-ag-rev-onto (fn-ncr-json-octet (car octets)) acc))
    (revappend acc nil)))

(defun fn-ncr-json-escape (octets)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp octets)
           (append (fn-ncr-json-octet (car octets))
                   (fn-ncr-json-escape (cdr octets)))
         nil)
       :exec (fn-ncr-json-escape-loop octets nil)))

(local
 (defthm fn-ncr-json-escape-loop-rev-onto-append
   (equal (revappend (fn-ag-rev-onto x acc) y)
          (revappend acc (append x y)))))

(local
 (defthm fn-ncr-json-escape-loop-is-revappend
   (equal (fn-ncr-json-escape-loop octets acc)
          (revappend acc (fn-ncr-json-escape octets)))
   :hints (("Goal" :induct (fn-ncr-json-escape-loop octets acc)
                   :in-theory (union-theories '(fn-ncr-json-escape-loop fn-ncr-json-escape revappend car-cons cdr-cons fn-ncr-json-escape-loop-rev-onto-append)
                                              (theory 'minimal-theory))))))

(verify-guards fn-ncr-json-escape-loop)

(verify-guards fn-ncr-json-escape
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-ncr-json-escape)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-ncr-json-escape-loop-is-revappend (acc nil))))))


(defun fn-ncr-decimal-aux (n acc)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (< n 10)
        (cons (+ 48 n) acc)
      (fn-ncr-decimal-aux (floor n 10) (cons (+ 48 (mod n 10)) acc)))))

(defthm fn-ncr-true-listp-of-json-escape
  (true-listp (fn-ncr-json-escape xs))
  :rule-classes :type-prescription)

(defthm fn-ncr-true-listp-of-decimal-aux
  (implies (true-listp acc) (true-listp (fn-ncr-decimal-aux n acc)))
  :rule-classes :type-prescription)

(defun fn-ncr-decimal (n)
  (declare (xargs :guard t))
  (fn-ncr-decimal-aux n nil))

; A value: (:str . OCTETS), (:num . N), :null, :true or :false.
(defun fn-ncr-json-value (v)
  (declare (xargs :guard t))
  (cond ((and (consp v) (equal (car v) :str))
         (append (list 34) (fn-ncr-json-escape (cdr v)) (list 34)))
        ((and (consp v) (equal (car v) :num)) (fn-ncr-decimal (cdr v)))
        ((equal v :true) (list 116 114 117 101))
        ((equal v :false) (list 102 97 108 115 101))
        (t (list 110 117 108 108))))

(defthm fn-ncr-true-listp-of-json-value
  (true-listp (fn-ncr-json-value v))
  :rule-classes :type-prescription)

; PAIRS: a list of (KEY-OCTETS . VALUE).
(defun fn-ncr-json-members (pairs)
  (declare (xargs :guard t))
  (if (consp pairs)
      (append (fn-ncr-json-value (cons :str (and (consp (car pairs))
                                                 (car (car pairs)))))
              (list 58)
              (fn-ncr-json-value (and (consp (car pairs)) (cdr (car pairs))))
              (if (consp (cdr pairs)) (list 44) nil)
              (fn-ncr-json-members (cdr pairs)))
    nil))

(defun fn-ncr-json-object (pairs)
  (declare (xargs :guard t))
  (append (list 123) (fn-ncr-json-members pairs) (list 125)))

; Every octet printable ASCII (32 to 126): the line holds no control octet.
(defun fn-ncr-asciip (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (<= 32 (car xs)) (<= (car xs) 126)
           (fn-ncr-asciip (cdr xs)))
    t))

(local
 (defthm fn-ncr-asciip-of-append
   (equal (fn-ncr-asciip (append a b))
          (and (fn-ncr-asciip a) (fn-ncr-asciip b)))))

(local
 (defthm fn-ncr-asciip-of-json-octet
   (fn-ncr-asciip (fn-ncr-json-octet x))
   :hints (("Goal" :in-theory (enable fn-ncr-hex-digit)))))

(local
 (defthm fn-ncr-asciip-of-json-escape
   (fn-ncr-asciip (fn-ncr-json-escape xs))
   :hints (("Goal" :in-theory (disable fn-ncr-json-octet)))))

(local
 (defthm fn-ncr-asciip-of-decimal-aux
   (implies (fn-ncr-asciip acc)
            (fn-ncr-asciip (fn-ncr-decimal-aux n acc)))))

(local
 (defthm fn-ncr-asciip-of-json-value
   (fn-ncr-asciip (fn-ncr-json-value v))
   :hints (("Goal" :in-theory (disable fn-ncr-json-escape fn-ncr-decimal-aux)))))

(local
 (defthm fn-ncr-asciip-of-json-members
   (fn-ncr-asciip (fn-ncr-json-members pairs))
   :hints (("Goal" :in-theory (disable fn-ncr-json-value)))))

(defthm fn-ncr-json-object-is-ascii
  (fn-ncr-asciip (fn-ncr-json-object pairs))
  :hints (("Goal" :in-theory (disable fn-ncr-json-members))))

; A keyword's lower-case name, the word the text output prints.
(defun fn-ncr-keyword-word (k)
  (declare (xargs :guard t))
  (let ((w (and (symbolp k)
                (fn-nctrl-word-chars-octets (coerce (symbol-name k) 'list)))))
    (if (and (consp w) (true-listp w)) w (list 63))))

(defun fn-ncr-word-value (word)
  (declare (xargs :guard t))
  (if (or (not (consp word)) (equal word *fn-nctrl-no-reason-word*))
      :null
    (cons :str word)))

; The report's members of a poll or wait line.
(defun fn-ncr-report-members (summary)
  (declare (xargs :guard t))
  (let ((kind (and (consp summary) (car summary)))
        (msgid (and (consp summary) (consp (cdr summary)) (cadr summary))))
    (case kind
      (:empty (list (cons (fn-ncr-keyword-word :report) (cons :str (fn-ncr-keyword-word :empty)))))
      (:withdrawn (list (cons (fn-ncr-keyword-word :report)
                              (cons :str (fn-ncr-keyword-word :withdrawn)))
                        (cons (fn-ncr-keyword-word :message_id) (cons :str msgid))))
      (:article (list (cons (fn-ncr-keyword-word :report)
                            (cons :str (fn-ncr-keyword-word :article)))
                      (cons (fn-ncr-keyword-word :message_id) (cons :str msgid))))
      (otherwise (list (cons (fn-ncr-keyword-word :report)
                             (cons :str (fn-ncr-keyword-word :unreadable))))))))

; The one JSON line of a consumer command: {"command":..,"outcome":..,
; "reason":..} and, for an accepted status, its three counts, for an
; accepted poll or wait, the report's kind and Message-ID.  STATUS-COUNTS
; is (ACK FRONTIER DISTANCE) or nil; SUMMARY is `fn-ncr-report-summary''s
; answer or nil.
(defun fn-ncr-json-line (operation status word status-counts summary)
  (declare (xargs :guard t))
  (fn-ncr-json-object
   (append
    (list (cons (fn-ncr-keyword-word :command)
                (cons :str (fn-ncr-keyword-word operation)))
          (cons (fn-ncr-keyword-word :outcome)
                (cons :str (fn-ncr-keyword-word status)))
          (cons (fn-ncr-keyword-word :reason) (fn-ncr-word-value word)))
    (if (and (equal status :accepted) (true-listp status-counts)
             (equal (len status-counts) 3))
        (list (cons (fn-ncr-keyword-word :committed_ack)
                    (cons :num (nfix (car status-counts))))
              (cons (fn-ncr-keyword-word :journal_frontier)
                    (cons :num (nfix (cadr status-counts))))
              (cons (fn-ncr-keyword-word :journal_event_distance)
                    (cons :num (nfix (caddr status-counts)))))
      nil)
    (if (and (equal status :accepted) summary)
        (fn-ncr-report-members summary)
      nil))))

; The JSON line `fn consumer-article --json REPORT' prints: the report's
; kind, its Message-ID and, for an article, the stored octets in hex.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-ncr-hex-loop (rev acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rev)
      (fn-ncr-hex-loop (cdr rev)
                       (list* (fn-ncr-hex-digit (floor (min (nfix (car rev)) 255) 16))
                              (fn-ncr-hex-digit (mod (min (nfix (car rev)) 255) 16))
                              acc))
    acc))

(defun fn-ncr-hex (octets)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp octets)
           (list* (fn-ncr-hex-digit (floor (min (nfix (car octets)) 255) 16))
                  (fn-ncr-hex-digit (mod (min (nfix (car octets)) 255) 16))
                  (fn-ncr-hex (cdr octets)))
         nil)
       :exec (fn-ncr-hex-loop (fn-ag-rev-onto octets nil) nil)))

(local
 (defthm fn-ncr-hex-loop-of-rev-onto
   (equal (fn-ncr-hex-loop (fn-ag-rev-onto octets zs) nil)
          (fn-ncr-hex-loop zs (fn-ncr-hex octets)))
   :hints (("Goal" :induct (fn-ag-rev-onto octets zs)
                   :in-theory (union-theories '(fn-ncr-hex-loop fn-ncr-hex fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-ncr-hex-loop)

(verify-guards fn-ncr-hex
  :hints (("Goal" :in-theory (union-theories '(fn-ncr-hex fn-ncr-hex-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-ncr-hex-loop-of-rev-onto (zs nil))))))


(defun fn-ncr-article-json (summary)
  (declare (xargs :guard t))
  (fn-ncr-json-object
   (append (fn-ncr-report-members summary)
           (if (and (consp summary) (equal (car summary) :article)
                    (consp (cdr summary)) (consp (cddr summary)))
               (list (cons (fn-ncr-keyword-word :article_hex)
                           (cons :str (fn-ncr-hex (caddr summary)))))
             nil))))

(verify-guards fn-ncr-report-summary)
