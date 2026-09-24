; fn: the duplicate-versus-conflict decision keys on the poster's bytes (D25).
;
; A Message-ID the Store already holds is answered one of two ways: the
; submission is the held article again (:duplicate, "already stored here"),
; or it is a different article under that Message-ID (:conflict).  Until
; 2026-09-24 the comparison was octet equality of the whole stored payload
; (fn-sn-existing-action, books/store-node.lisp), and a served POST is stored
; with the Injection-Date of the second it was injected in.  A resend of the
; same poster octets at any later second was therefore a conflict: 35 of 35
; resubmissions after a death in the 47bdb9a4 campaign (finding K1).
;
; D25: the comparison drops the fields the node injects -- Path, Xref,
; Injection-Date and Injection-Info, and a Date the node generated because the
; poster sent none -- and compares what remains.  The names
; are books/hybrid-carrier.lisp's constants, the four mutable relay fields
; fn-hc-authored-source already excludes from a signature subject; the other
; three names that projection drops (FN-Authorship, FN-Statement, FN-Policy)
; are poster-supplied on a served POST and stay in the key, so two articles
; that differ only in a carried signature remain a conflict and neither
; signature is silently discarded.  The stored record keeps the injected
; fields; only the key drops them.
;
; The projection works on octets, line by line, and does not call the article
; parser.  The parser has bounds on header lines, header octets and field
; count, so a parse-level projection of `prefix ++ source' is not a function
; of the source's parse, and the decision must be total on whatever octets a
; stored record carries.  Line structure is what injection changes: it
; prepends whole header lines (books/injection.lisp fn-inj-prefix).
;
; Cost: this runs only on the branch where the Message-ID is already held,
; over the submission and that one stored article, linear in their length.
; It never walks the store.

(in-package "ACL2")
(include-book "store-node")

; The four injected names, lowercased as field names compare.
(defconst *fn-pb-injected-names*
  (list *fn-hc-path-name* *fn-hc-xref-name*
        *fn-hc-injection-date-name* *fn-hc-injection-info-name*))

(defun fn-pb-injected-namep (name)
  (declare (xargs :guard t))
  (if (member-equal name *fn-pb-injected-names*) t nil))

; One line: the octets up to and including the first LF, and what follows.
(defun fn-pb-line (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) 10)
          (list 10)
        (cons (car x) (fn-pb-line (cdr x))))
    nil))

(defun fn-pb-rest (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) 10)
          (cdr x)
        (fn-pb-rest (cdr x)))
    nil))

(defthm fn-pb-rest-is-shorter
  (implies (consp x)
           (< (len (fn-pb-rest x)) (len x)))
  :rule-classes :linear)

; A field line's name: the octets before the first colon, lowercased.
(defun fn-pb-name-octets (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (or (equal (car x) 58) (equal (car x) 10))
          nil
        (cons (car x) (fn-pb-name-octets (cdr x))))
    nil))

(defun fn-pb-line-injectedp (x)
  (declare (xargs :guard t))
  (fn-pb-injected-namep (fn-article-ascii-downcase (fn-pb-name-octets x))))

;; A field line's value: the octets after its first colon, before the LF.
(defun fn-pb-upto-lf (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) 10) nil (cons (car x) (fn-pb-upto-lf (cdr x))))
    nil))

(defun fn-pb-value (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cond ((equal (car x) 10) nil)
            ((equal (car x) 58) (fn-pb-upto-lf (cdr x)))
            (t (fn-pb-value (cdr x))))
    nil))

(defun fn-pb-line-namedp (x name)
  (declare (xargs :guard t))
  (equal (fn-article-ascii-downcase (fn-pb-name-octets x)) name))

(defconst *fn-pb-message-id-name* '(109 101 115 115 97 103 101 45 105 100))

; The header of X with every injected field removed, a field being its line
; and the continuation lines (leading space or tab) that follow it; DROP says
; the field in progress is dropped.  The empty line that ends the header, and
; the body after it, are kept verbatim.
;
; A Date the node generated is injected too (RFC 5537 section 3.5 item 5;
; books/injection.lisp fn-inj-prefix writes it with the Injection-Date's own
; date, after Injection-Info and an optional generated Message-ID).  IDATE is
; the value of the Injection-Date just read while no poster field other than
; Message-ID has been kept since: in that position a Date whose value equals
; it is the generated one and is dropped.  A Date the poster supplied is kept
; unless it opens the source and equals the injection's rendering octet for
; octet (fn-pb-opens-with-a-date, the hypothesis of the invariance theorem).
(defun fn-pb-project (x drop idate)
  (declare (xargs :guard t :measure (len x)))
  (if (not (consp x))
      nil
    (let ((line (fn-pb-line x))
          (rest (fn-pb-rest x)))
      (cond ((equal line '(13 10)) x)
            ((fn-article-wspp (car x))
             (if drop
                 (fn-pb-project rest drop idate)
               (append line (fn-pb-project rest nil idate))))
            ((fn-pb-line-injectedp x)
             (fn-pb-project rest t
                            (if (fn-pb-line-namedp x *fn-hc-injection-date-name*)
                                (fn-pb-value x)
                              idate)))
            ((and idate
                  (fn-pb-line-namedp x *fn-inj-date-name*)
                  (equal (fn-pb-value x) idate))
             (fn-pb-project rest t nil))
            ((fn-pb-line-namedp x *fn-pb-message-id-name*)
             (append line (fn-pb-project rest nil idate)))
            (t (append line (fn-pb-project rest nil nil)))))))

(defthm fn-pb-true-listp-of-line
  (true-listp (fn-pb-line x)))

(verify-guards fn-pb-project)

; The poster's bytes of an article's octets: the D25 key.
(defun fn-pb-poster-bytes (octets)
  (declare (xargs :guard t))
  (fn-pb-project octets nil nil))

; The live Store's decision for an already held Message-ID, keyed on the
; poster's bytes.  The host calls it at host/owner-host.lisp
; fn-owner-existing-action and fn-owner-prepare and at
; host/store-node-host.lisp's two prepare/query sites.  Its guard, like
; fn-sn-existing-action's, is independent of fn-sn-statep, which walks the
; store.
(defun fn-pb-existing-action (msgid payload groups s)
  (declare (xargs :guard t))
  (let ((article (fn-find-article
                  msgid (fn-state-articles
                         (fn-node-acceptance (fn-sn-node s))))))
    (if article
        (if (and (equal (fn-pb-poster-bytes payload)
                        (fn-pb-poster-bytes (fn-article-payload article)))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))
