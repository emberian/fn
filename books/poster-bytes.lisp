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
(include-book "poster-bytes-source")

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
