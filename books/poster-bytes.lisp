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

(defun fn-pb-info-line-agent (x)
  (declare (xargs :guard t))
  (let* ((line (fn-pb-line x))
         (r (fn-inj-strip *fn-inj-injection-info-field* line)))
    (if (and (true-listp r) (< 2 (len r)))
        (let ((agent (fn-inj-take (- (len r) 2) r)))
          (if (equal (fn-inj-injection-info-line agent) line) agent nil))
      nil)))

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
(defun fn-pb-path-agent (x msgid)
  (declare (xargs :guard t))
  (or (fn-pb-path-line-agent x) (fn-pb-block-agent x msgid)))

; The comparison subject of an article: its source when this agent's recipe
; gives one back, else the article's own octets.  The two arms are tagged,
; so a source can never equal a payload compared exactly.
(defun fn-pb-subject (octets agent msgid)
  (declare (xargs :guard t))
  (let ((source (fn-inj-source-of octets agent msgid)))
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

; The live Store's decision for an already held Message-ID, keyed on the
; poster's source.  The host calls it at host/owner-host.lisp
; fn-owner-existing-action and fn-owner-prepare and at
; host/store-node-host.lisp's two prepare/query sites.  Its guard, like
; fn-sn-existing-action's, is independent of fn-sn-statep, which walks the
; store.  MSGID is the Store's string key; the injection inverse reads the
; Message-ID line's octets, which are its codes.
(defun fn-pb-existing-action (msgid payload groups s)
  (declare (xargs :guard t))
  (let ((article (fn-find-article
                  msgid (fn-state-articles
                         (fn-node-acceptance (fn-sn-node s))))))
    (if article
        (if (and (fn-pb-same-articlep (fn-record-string-octets msgid) payload
                                      (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))
