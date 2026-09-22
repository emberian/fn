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
