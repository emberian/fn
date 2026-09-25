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

(defun fn-pb-path-agent (x)
  (declare (xargs :guard t))
  (let* ((line (fn-pb-line x))
         (r (fn-inj-strip *fn-inj-path-field* line)))
    (if (and (true-listp r) (< *fn-pb-path-tail-length* (len r)))
        (let ((agent (fn-inj-take (- (len r) *fn-pb-path-tail-length*) r)))
          (if (equal (fn-inj-path-line agent) line) agent nil))
      nil)))

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
  (let ((agent (fn-pb-path-agent payload)))
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
