; fn: the duplicate-versus-conflict decision keys on the poster's source (D25).
;
; A Message-ID the Store already holds is answered one of two ways: the
; submission is the held article again (:duplicate, "already stored here"),
; or it is a different article under that Message-ID (:conflict).  Until
; 2026-09-24 the comparison was octet equality of the whole stored payload
; (fn-sn-existing-action, books/store-node.lisp), and a served POST is stored
; with the Injection-Date of the second it was injected in, so a resend of the
; same source at a later second was a conflict (finding K1).
;
; The comparison subject is the poster's source, recovered from each article
; by the injection inverse (books/injection.lisp fn-inj-source-of): the exact
; injected block of this agent's recipe, which names the fields it generated,
; and after it the source octet for octet.  The submission's agent is read
; from its own Path line (it was injected a moment ago by the live
; configuration), and the held article is read under that same agent.  When
; both articles give back a source, the sources and the groups are compared;
; otherwise -- an article this agent did not inject, a v1 record whose source
; is ambiguous, a relayed article -- the payloads are compared octet for
; octet, exactly as before D25.  Nothing is dropped from either side: an
; authored Date, a carried signature (FN-Authorship, FN-Statement,
; FN-Policy) and every other poster octet stay in the subject.
;
; Cost: this runs only on the branch where the Message-ID is already held,
; over the submission and that one stored article, linear in the injected
; block.  It never walks the store.

(in-package "ACL2")
(include-book "store-node")
; The injection inverse (fn-inj-source-of) and the injected-block octets.
; Reached through books/hybrid-store.lisp until that book included only
; books/injection-shape.lisp (audit 2026-09-25, packet 1).
(include-book "injection")
; The node's generated RFC 8315 lines in front of the block (SEC-006):
; fn-cll-skip sets them aside.
(include-book "cancel-lock-lines")

; The agent of a Path line this node writes, `Path: AGENT!not-for-mail' CRLF,
; at the front of x; nil when x does not open with such a line.
(defconst *fn-pb-path-tail-length* 15)   ; "!not-for-mail" CRLF

(defun fn-pb-line (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) 10)
          (list 10)
        (cons (car x) (fn-pb-line (cdr x))))
    nil))

(defun fn-pb-path-line-agent (x)
  (declare (xargs :guard t))
  (let* ((line (fn-pb-line x))
         (r (fn-inj-strip *fn-inj-path-field* line)))
    (if (and (true-listp r) (< *fn-pb-path-tail-length* (len r)))
        (let ((agent (fn-inj-take (- (len r) *fn-pb-path-tail-length*) r)))
          (if (equal (fn-inj-path-line agent) line) agent nil))
      nil)))

; The agent a recipe v3 record's block names (a supplied Path, D32).  The
; block is [Injection-Date line, 49 octets] [the Message-ID line of `msgid']
; [a generated Date line, 39 octets] and the Injection-Info line that closes
; it; each optional line is recognised by its field name, and the date is
; always 31 octets (fn-inj-date-octets).
(defconst *fn-pb-stamp-line-length* 49)  ; "Injection-Date: " date CRLF
(defconst *fn-pb-date-line-length* 39)   ; "Date: " date CRLF

(defun fn-pb-opensp (field x)
  (declare (xargs :guard t))
  (not (equal (fn-inj-strip field x) :no)))

; The octets of r before its first ";", or :no when it has none.
(defun fn-pb-upto-semicolon (r)
  (declare (xargs :guard t))
  (if (consp r)
      (if (equal (car r) 59)
          nil
        (let ((rest (fn-pb-upto-semicolon (cdr r))))
          (if (equal rest :no) :no (cons (car r) rest))))
    :no))

; The agent an Injection-Info LINE with parameters names (PKT-597,
; books/injection-info-params.lisp): the octets before the first ";", when
; the whole line is that agent's line with a parameter run
; (books/injection.lisp fn-inj-strip-info leaves nothing after it).
(defun fn-pb-params-line-agent (line)
  (declare (xargs :guard t))
  (let ((agent (fn-pb-upto-semicolon
                (fn-inj-strip *fn-inj-injection-info-field* line))))
    (if (and (consp agent) (equal (fn-inj-strip-info agent line) nil))
        agent
      nil)))

(in-theory (disable fn-pb-params-line-agent))

; The plain line's agent, else the agent of the line with parameters: an
; article stored with Injection-Info parameters still names its agent, so
; D25 reads its v3 block as before.  An agent is a dot-atom and never holds
; ";", so a line with parameters is never read as a plain line naming
; AGENT; PARAMS (fn-ipp-a-supplied-path-retry-is-the-same-article).
(defun fn-pb-info-line-agent (x)
  (declare (xargs :guard t))
  (let* ((line (fn-pb-line x))
         (r (fn-inj-strip *fn-inj-injection-info-field* line)))
    (or (if (and (true-listp r) (< 2 (len r)))
            (let ((agent (fn-inj-take (- (len r) 2) r)))
              (if (and (equal (fn-inj-injection-info-line agent) line)
                       (not (member-equal 59 agent)))
                  agent
                nil))
          nil)
        (fn-pb-params-line-agent line))))

(defun fn-pb-block-agent (x msgid)
  (declare (xargs :guard t))
  (let* ((x1 (if (fn-pb-opensp *fn-inj-injection-date-field* x)
                 (fn-inj-drop *fn-pb-stamp-line-length* x)
               x))
         (x2 (fn-inj-strip-optional (fn-inj-message-id-line msgid) x1))
         (x3 (if (fn-pb-opensp *fn-inj-date-field* x2)
                 (fn-inj-drop *fn-pb-date-line-length* x2)
               x2)))
    (fn-pb-info-line-agent x3)))

; The injecting agent a submission names: its leading Path line's (recipe v1
; and v2), else its v3 block's Injection-Info line's.  Whichever it names,
; the inverse checks the whole block, so a wrong guess gives no source and
; the octets are compared exactly.
; SEC-006 (D25 restored, gpt-6's wave-5 review section 3): both are read
; after `fn-cll-skip', which sets aside the Cancel-Lock and Cancel-Key lines
; the node generates in front of its block (books/cancel-lock-lines.lisp),
; so those lines are never part of the comparison subject, whatever account
; or key epoch wrote them.  A Cancel-Lock the poster wrote stays in the
; source.
(defun fn-pb-path-agent (x msgid)
  (declare (xargs :guard t))
  (let ((x (fn-cll-skip x)))
    (or (fn-pb-path-line-agent x) (fn-pb-block-agent x msgid))))

; The comparison subject of an article: its source when this agent's recipe
; gives one back, else the article's own octets.  The two arms are tagged,
; so a source can never equal a payload compared exactly.
(defun fn-pb-subject (octets agent msgid)
  (declare (xargs :guard t))
  (let ((source (fn-inj-source-of (fn-cll-skip octets) agent msgid)))
    (if source
        (cons :source (cdr source))
      (cons :octets octets))))

; The two articles are one when both give back a source and the sources are
; equal, or when either does not and the octets are equal.
(defun fn-pb-same-articlep (msgid payload held-payload)
  (declare (xargs :guard t))
  (let ((agent (fn-pb-path-agent payload msgid)))
    (let ((a (fn-pb-subject payload agent msgid))
          (b (fn-pb-subject held-payload agent msgid)))
      (if (and (equal (car a) :source) (equal (car b) :source))
          (equal a b)
        (equal payload held-payload)))))

; D25's decision for an already held Message-ID, keyed on the poster's
; source, over an OCTET-MODEL article list (each payload the article's
; bytes).  The host's entry is books/store-intern.lisp
; fn-store-existing-action (host/owner-host.lisp fn-owner-existing-action and
; fn-owner-prepare, host/store-node-host.lisp's prepare/query sites; the
; buffer entry fn-pidx-existing-action), which reads the held bytes through
; the arena; books/store-existing-alpha.lisp
; fn-store-existing-action-is-pb-over-alpha equates it with this decision
; over ALPHA of the Store's articles.  MSGID is the Store's string key; the
; injection inverse reads the Message-ID line's octets, which are its codes.
; The store-shaped twin fn-pb-existing-action compared the offered octets
; with a handle and was retired (PKT-EG-4, lane entry-guards-2).
(fn-payload-kind fn-pb-action-over :wire "the verdict over an octet-model article list (alpha)")
(defun fn-pb-action-over (msgid payload groups articles)
  (declare (xargs :guard t))
  (let ((article (fn-find-article msgid articles)))
    (if article
        (if (and (fn-pb-same-articlep (fn-record-string-octets msgid) payload
                                      (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))
