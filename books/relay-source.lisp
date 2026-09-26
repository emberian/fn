; fn: relaying cannot change who wrote an article (PRF-127; the Fable
; mandate section 5.3; D25, D32).
;
; A receiving node stores what a peer transferred as
; fn-peer-relayed-octets (books/peer-inbound.lisp): the received octets with
; this node's identity spliced into Path and any Xref removed, nothing else
; (fn-peer-relayed-octets-change-only-path-and-xref).  The authored source a
; carried signature is checked over is fn-hc-authored-source
; (books/hybrid-carrier.lisp): the parsed article's header fields with the
; node-added ones (FN-Authorship, Path, Xref, Injection-Date,
; Injection-Info, the statement and the policy field) dropped, the blank
; line and the body.  This book proves the two agree: the authored source
; of what B stores is the authored source of what A sent.
;
; The join is a parser fact.  fn-hc-authored-source reads the parse, and
; path-update's keystones read the raw lines.  For every article the parser
; accepts, the authored source equals a line walk over the octets with Path
; and Xref already stripped (fn-rs-authored-source-is-the-walk): the fields
; view is a partition of the header (fn-article-successful-parse-fields-
; recompose-header, fn-article-successful-parse-fields-correspond), so the
; walk drops exactly the fields the projection drops.  Path and Xref are
; among those fields, so the strip that relaying leaves unchanged determines
; the authored source.
;
; Host calls:
;   - host/owner-host.lisp fn-owner-take stages fn-peer-relayed-octets for
;     an NNTP transit (fn-peer-transfer, fn-peer-injection-arguments):
;     fn-rs-a-wanted-transfer-keeps-the-authored-source.
;   - host/bp-native-app-host.lisp fn-owner-app-plan-install calls
;     fn-bpaj-transit-plan for a BP-carried request:
;     fn-rs-a-bp-transit-keeps-the-authored-source.
; Neither needs a hypothesis about the article: the transfer decision
; refuses before it wants an article the parser rejects, before or after
; the Path update (fn-peer-decide-transfer's :proto-article and :oversize).
;
; What it does not say: nothing here about signatures, only that the bytes
; a signature covers are the same bytes at both nodes.  A's own injection is
; PRF-117's (books/source-routes.lisp) and books/injection-path.lisp's
; (fn-inj-source-of-inverts-the-injection, fn-inj-unsplice-of-a-splice).

(in-package "ACL2")
(include-book "article-properties")
(include-book "hybrid-carrier")
(include-book "path-update")

; -----------------------------------------------------------------------------
; The line walk.  A field is well formed when the parser could have produced
; it: its first raw line opens with a non-WSP octet and has a colon, its
; continuation lines open with WSP, no line carries CR or LF, and its name
; is the first line's name.  fn-rs-source-walk is fn-pu-strip's walk with
; the projection's reserved names in place of Path and Xref.

(defun fn-rs-field-wfp (field)
  (declare (xargs :guard t))
  (let ((lines (if (true-listp field) (fn-article-field-raw-lines field) nil)))
    (and (true-listp field)
         (consp lines)
         (fn-article-plain-linesp lines)
         (fn-article-wsp-startsp (cdr lines))
         (consp (car lines))
         (not (fn-pu-wspp (car (car lines))))
         (fn-article-has-colonp (car lines))
         (equal (fn-article-field-name field)
                (fn-article-ascii-downcase
                 (fn-article-name-before-colon (car lines)))))))

(defun fn-rs-fields-wfp (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (fn-rs-field-wfp (car fields))
           (fn-rs-fields-wfp (cdr fields)))
    (null fields)))

(defun fn-rs-path-or-xref-fieldp (field)
  (declare (xargs :guard t))
  (let ((line (append (if (and (true-listp field)
                               (consp (fn-article-field-raw-lines field))
                               (true-listp (car (fn-article-field-raw-lines field))))
                          (car (fn-article-field-raw-lines field))
                        nil)
                      '(13 10))))
    (or (fn-pu-named-p line *fn-pu-xref-colon*)
        (fn-pu-named-p line *fn-pu-path-colon*))))

(defun fn-rs-drop-path-xref (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (if (fn-rs-path-or-xref-fieldp (car fields))
          (fn-rs-drop-path-xref (cdr fields))
        (cons (car fields) (fn-rs-drop-path-xref (cdr fields))))
    nil))

(defun fn-rs-reserved-fieldp (field)
  (declare (xargs :guard t))
  (and (true-listp field)
       (fn-hc-reserved-namep (fn-article-field-name field))))

(defun fn-rs-authored-fields (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (if (fn-rs-reserved-fieldp (car fields))
          (fn-rs-authored-fields (cdr fields))
        (cons (car fields) (fn-rs-authored-fields (cdr fields))))
    nil))

(defun fn-rs-reserved-linep (line)
  (declare (xargs :guard t))
  (fn-hc-reserved-namep
   (fn-article-ascii-downcase (fn-article-name-before-colon line))))

(defun fn-rs-source-walk (x dropping)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (atom x)
      x
    (let ((line (fn-pu-line x))
          (rest (fn-pu-after-line x)))
      (cond ((equal line '(13 10)) x)
            ((fn-pu-wspp (car line))
             (if dropping
                 (fn-rs-source-walk rest t)
               (fn-pu-append line (fn-rs-source-walk rest nil))))
            ((fn-rs-reserved-linep line) (fn-rs-source-walk rest t))
            (t (fn-pu-append line (fn-rs-source-walk rest nil)))))))

; -----------------------------------------------------------------------------
; One physical line at a time.

(local
 (defthm fn-rs-pu-append-is-append
   (equal (fn-pu-append a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-pu-append)))))

(local
 (defthm fn-rs-line-of-a-plain-line
   (implies (fn-article-crlf-freep l)
            (equal (fn-pu-line (append l (cons 13 (cons 10 r))))
                   (append l '(13 10))))
   :hints (("Goal" :in-theory (enable fn-pu-line fn-pu-crlf-atp)))))

(local
 (defthm fn-rs-after-a-plain-line
   (implies (fn-article-crlf-freep l)
            (equal (fn-pu-after-line (append l (cons 13 (cons 10 r))))
                   r))
   :hints (("Goal" :in-theory (enable fn-pu-after-line fn-pu-crlf-atp)))))

(local
 (defthm fn-rs-blank-line
   (and (equal (fn-pu-line (cons 13 (cons 10 r))) '(13 10))
        (equal (fn-pu-after-line (cons 13 (cons 10 r))) r))
   :hints (("Goal" :in-theory (enable fn-pu-line fn-pu-after-line fn-pu-crlf-atp)))))

(local
 (defthm fn-rs-car-of-plain-line
   (implies (consp l)
            (equal (car (append l r)) (car l)))))

(local
 (defthm fn-rs-plain-line-not-blank
   (implies (and (consp l) (fn-article-crlf-freep l))
            (not (equal (append l '(13 10)) '(13 10))))))

(local
 (defthm fn-rs-strip-continuations-dropped
   (implies (and (fn-article-plain-linesp conts)
                 (fn-article-wsp-startsp conts))
            (equal (fn-pu-strip (append (fn-article-lines-octets conts) r) t)
                   (fn-pu-strip r t)))
   :hints (("Goal" :induct (fn-article-lines-octets conts)
            :in-theory (enable fn-article-lines-octets fn-pu-wspp)
            :expand ((fn-pu-strip (append (car conts)
                                          (cons 13 (cons 10 (append (fn-article-lines-octets (cdr conts)) r))))
                                  t))))))

(local
 (defthm fn-rs-strip-continuations-kept
   (implies (and (fn-article-plain-linesp conts)
                 (fn-article-wsp-startsp conts))
            (equal (fn-pu-strip (append (fn-article-lines-octets conts) r) nil)
                   (append (fn-article-lines-octets conts) (fn-pu-strip r nil))))
   :hints (("Goal" :induct (fn-article-lines-octets conts)
            :in-theory (enable fn-article-lines-octets fn-pu-wspp)
            :expand ((fn-pu-strip (append (car conts)
                                          (cons 13 (cons 10 (append (fn-article-lines-octets (cdr conts)) r))))
                                  nil))))))

(local
 (defthm fn-rs-walk-continuations-dropped
   (implies (and (fn-article-plain-linesp conts)
                 (fn-article-wsp-startsp conts))
            (equal (fn-rs-source-walk (append (fn-article-lines-octets conts) r) t)
                   (fn-rs-source-walk r t)))
   :hints (("Goal" :induct (fn-article-lines-octets conts)
            :in-theory (enable fn-article-lines-octets fn-pu-wspp)
            :expand ((fn-rs-source-walk (append (car conts)
                                          (cons 13 (cons 10 (append (fn-article-lines-octets (cdr conts)) r))))
                                  t))))))

(local
 (defthm fn-rs-walk-continuations-kept
   (implies (and (fn-article-plain-linesp conts)
                 (fn-article-wsp-startsp conts))
            (equal (fn-rs-source-walk (append (fn-article-lines-octets conts) r) nil)
                   (append (fn-article-lines-octets conts) (fn-rs-source-walk r nil))))
   :hints (("Goal" :induct (fn-article-lines-octets conts)
            :in-theory (enable fn-article-lines-octets fn-pu-wspp)
            :expand ((fn-rs-source-walk (append (car conts)
                                          (cons 13 (cons 10 (append (fn-article-lines-octets (cdr conts)) r))))
                                  nil))))))

(local
 (defthm fn-rs-strip-of-a-field-line
   (implies (and (consp l) (fn-article-crlf-freep l) (not (fn-pu-wspp (car l))))
            (equal (fn-pu-strip (append l (cons 13 (cons 10 r))) d)
                   (if (or (fn-pu-named-p (append l '(13 10)) *fn-pu-xref-colon*)
                           (fn-pu-named-p (append l '(13 10)) *fn-pu-path-colon*))
                       (fn-pu-strip r t)
                     (append (append l '(13 10)) (fn-pu-strip r nil)))))
   :hints (("Goal" :expand ((fn-pu-strip (append l (cons 13 (cons 10 r))) d))))))

(local
 (defthm fn-rs-strip-of-the-blank-line
   (equal (fn-pu-strip (cons 13 (cons 10 r)) d) (cons 13 (cons 10 r)))
   :hints (("Goal" :expand ((fn-pu-strip (cons 13 (cons 10 r)) d))))))

(local
 (defthm fn-rs-walk-of-a-field-line
   (implies (and (consp l) (fn-article-crlf-freep l) (not (fn-pu-wspp (car l))))
            (equal (fn-rs-source-walk (append l (cons 13 (cons 10 r))) d)
                   (if (fn-rs-reserved-linep (append l '(13 10)))
                       (fn-rs-source-walk r t)
                     (append (append l '(13 10)) (fn-rs-source-walk r nil)))))
   :hints (("Goal" :expand ((fn-rs-source-walk (append l (cons 13 (cons 10 r))) d))))))

(local
 (defthm fn-rs-walk-of-the-blank-line
   (equal (fn-rs-source-walk (cons 13 (cons 10 r)) d) (cons 13 (cons 10 r)))
   :hints (("Goal" :expand ((fn-rs-source-walk (cons 13 (cons 10 r)) d))))))

; -----------------------------------------------------------------------------
; A header of well-formed fields, walked: fn-pu-strip drops Path and Xref,
; the source walk drops the reserved fields.

(local
 (defun fn-rs-fields-induct (fields d)
   (if (consp fields)
       (list (fn-rs-fields-induct (cdr fields) t)
             (fn-rs-fields-induct (cdr fields) nil))
     d)))

(local
 (defthm fn-rs-fields-octets-of-cons
   (equal (fn-article-fields-octets (cons f rest))
          (append (fn-article-lines-octets (fn-article-field-raw-lines f))
                  (fn-article-fields-octets rest)))
   :hints (("Goal" :in-theory (enable fn-article-fields-octets)))))

(local
 (defthm fn-rs-strip-of-a-field
   (implies (and (consp fields) (fn-rs-field-wfp (car fields)))
            (equal (fn-pu-strip (append (fn-article-fields-octets fields) r) d)
                   (if (fn-rs-path-or-xref-fieldp (car fields))
                       (fn-pu-strip (append (fn-article-fields-octets (cdr fields)) r) t)
                     (append (fn-article-lines-octets (fn-article-field-raw-lines (car fields)))
                             (fn-pu-strip (append (fn-article-fields-octets (cdr fields)) r) nil)))))
   :hints (("Goal" :in-theory (e/d (fn-article-lines-octets) (fn-article-fields-octets fn-pu-named-p fn-pu-strip))
            :expand ((fn-article-fields-octets fields))
            :do-not '(generalize fertilize)))))

(local
 (defthm fn-rs-strip-of-wf-fields
   (implies (fn-rs-fields-wfp fields)
            (equal (fn-pu-strip (append (fn-article-fields-octets fields)
                                        (cons 13 (cons 10 body)))
                                d)
                   (append (fn-article-fields-octets (fn-rs-drop-path-xref fields))
                           (cons 13 (cons 10 body)))))
   :hints (("Goal" :induct (fn-rs-fields-induct fields d)
            :in-theory (e/d () (fn-article-fields-octets fn-rs-field-wfp fn-rs-path-or-xref-fieldp fn-pu-strip)))
           )))

(local
 (defthm fn-rs-name-before-colon-of-append
   (implies (fn-article-has-colonp l)
            (equal (fn-article-name-before-colon (append l r))
                   (fn-article-name-before-colon l)))))

(local
 (defthm fn-rs-walk-of-a-field
   (implies (and (consp fields) (fn-rs-field-wfp (car fields)))
            (equal (fn-rs-source-walk (append (fn-article-fields-octets fields) r) d)
                   (if (fn-rs-reserved-fieldp (car fields))
                       (fn-rs-source-walk (append (fn-article-fields-octets (cdr fields)) r) t)
                     (append (fn-article-lines-octets (fn-article-field-raw-lines (car fields)))
                             (fn-rs-source-walk (append (fn-article-fields-octets (cdr fields)) r) nil)))))
   :hints (("Goal" :in-theory (e/d (fn-article-lines-octets) (fn-article-fields-octets fn-hc-reserved-namep fn-rs-source-walk))
            :expand ((fn-article-fields-octets fields))
            :do-not '(generalize fertilize)))))

(local
 (defthm fn-rs-walk-of-wf-fields
   (implies (fn-rs-fields-wfp fields)
            (equal (fn-rs-source-walk (append (fn-article-fields-octets fields)
                                        (cons 13 (cons 10 body)))
                                d)
                   (append (fn-article-fields-octets (fn-rs-authored-fields fields))
                           (cons 13 (cons 10 body)))))
   :hints (("Goal" :induct (fn-rs-fields-induct fields d)
            :in-theory (e/d () (fn-article-fields-octets fn-rs-field-wfp fn-rs-reserved-fieldp fn-rs-source-walk))))))

; -----------------------------------------------------------------------------
; A field fn-pu-strip drops is a reserved one, so dropping Path and Xref
; first changes nothing the projection keeps.

(local
 (defun fn-rs-colon-freep (n)
   (declare (xargs :guard t))
   (if (consp n) (and (not (equal (car n) 58)) (fn-rs-colon-freep (cdr n))) (null n))))

(local
 (defthm fn-rs-named-p-names-the-field
   (implies (and (fn-pu-named-p line (append n '(58)))
                 (fn-rs-colon-freep n))
            (equal (fn-article-ascii-downcase (fn-article-name-before-colon line)) n))
   :hints (("Goal" :induct (fn-pu-named-p line n)
            :in-theory (enable fn-pu-named-p fn-pu-downcase)))))

(local
 (defthm fn-rs-a-path-or-xref-field-is-reserved
   (implies (and (fn-rs-field-wfp f) (fn-rs-path-or-xref-fieldp f))
            (fn-rs-reserved-fieldp f))
   :hints (("Goal" :in-theory (disable fn-rs-named-p-names-the-field fn-pu-named-p)
            :use ((:instance fn-rs-named-p-names-the-field
                   (line (append (car (fn-article-field-raw-lines f)) '(13 10)))
                   (n '(112 97 116 104)))
                  (:instance fn-rs-named-p-names-the-field
                   (line (append (car (fn-article-field-raw-lines f)) '(13 10)))
                   (n '(120 114 101 102))))))))

(local
 (defthm fn-rs-drop-path-xref-keeps-wf
   (implies (fn-rs-fields-wfp fields)
            (fn-rs-fields-wfp (fn-rs-drop-path-xref fields)))
   :hints (("Goal" :in-theory (disable fn-rs-field-wfp fn-rs-path-or-xref-fieldp)))))

(local
 (defthm fn-rs-authored-fields-of-drop-path-xref
   (implies (fn-rs-fields-wfp fields)
            (equal (fn-rs-authored-fields (fn-rs-drop-path-xref fields))
                   (fn-rs-authored-fields fields)))
   :hints (("Goal" :in-theory (disable fn-rs-field-wfp fn-rs-path-or-xref-fieldp fn-rs-reserved-fieldp)))))

; -----------------------------------------------------------------------------
; A parsed article is its fields: every field is well formed, and the
; octets are the fields' raw lines, the blank line and the body.

(local
 (defthm fn-rs-a-named-line-opens-with-ftext
   (implies (fn-article-namep (fn-article-ascii-downcase (fn-article-name-before-colon l)))
            (and (consp l) (not (fn-pu-wspp (car l)))))
   :hints (("Goal" :in-theory (enable fn-pu-wspp)
            :expand ((fn-article-name-before-colon l)
                     (fn-article-ascii-downcase (fn-article-name-before-colon l)))))))

(local
 (defthm fn-rs-a-parsed-field-is-wf
   (implies (and (fn-article-field-correspondsp f) (fn-article-fieldp f))
            (fn-rs-field-wfp f))
   :hints (("Goal" :in-theory (e/d (fn-article-lower-namep)
                                   (fn-article-unfold-reference fn-article-namep fn-article-ascii-downcase
                                    fn-article-header-bytes-p fn-article-name-before-colon
                                    fn-article-has-colonp fn-article-plain-linesp fn-article-wsp-startsp))
            :use ((:instance fn-rs-a-named-line-opens-with-ftext
                   (l (car (fn-article-field-raw-lines f)))))))))

(local
 (defthm fn-rs-parsed-fields-are-wf
   (implies (and (fn-article-fields-correspondp fields) (fn-article-field-listp fields))
            (fn-rs-fields-wfp fields))
   :hints (("Goal" :in-theory (disable fn-rs-field-wfp fn-article-field-correspondsp fn-article-fieldp)))))

(local
 (defthm fn-rs-stx-field-octets-is-lines-octets
   (implies (fn-article-plain-linesp lines)
            (equal (fn-stx-field-octets lines) (fn-article-lines-octets lines)))
   :hints (("Goal" :induct (fn-article-lines-octets lines)
            :in-theory (union-theories '(fn-stx-field-octets fn-article-lines-octets fn-article-plain-linesp
                                         (:e binary-append) binary-append car-cons cdr-cons)
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-rs-a-wf-field-has-plain-lines
   (implies (fn-rs-field-wfp f)
            (and (true-listp f)
                 (fn-article-plain-linesp (fn-article-field-raw-lines f))))
   :hints (("Goal" :in-theory (e/d (fn-rs-field-wfp)
                                   (fn-article-plain-linesp fn-article-wsp-startsp fn-article-has-colonp
                                    fn-article-name-before-colon fn-article-ascii-downcase fn-pu-wspp))))))

(local
 (defthm fn-rs-source-header-is-the-authored-fields
   (implies (fn-rs-fields-wfp fields)
            (equal (fn-hc-source-header fields)
                   (fn-article-fields-octets (fn-rs-authored-fields fields))))
   :hints (("Goal" :induct (fn-hc-source-header fields)
            :in-theory (union-theories '(fn-hc-source-header fn-rs-fields-wfp fn-rs-authored-fields
                                         fn-rs-reserved-fieldp fn-rs-fields-octets-of-cons
                                         fn-rs-stx-field-octets-is-lines-octets fn-rs-a-wf-field-has-plain-lines
                                         (:e fn-article-fields-octets) (:e fn-rs-authored-fields)
                                         car-cons cdr-cons)
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-rs-a-parsed-article-is-its-fields
   (implies (fn-article-result-okp (fn-article-parse y))
            (let ((article (fn-article-result-article (fn-article-parse y))))
              (and (true-listp article)
                   (fn-rs-fields-wfp (fn-article-fields article))
                   (true-listp (fn-article-body article))
                   (equal y (append (fn-article-fields-octets (fn-article-fields article))
                                    (cons 13 (cons 10 (fn-article-body article))))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-article-syntax-p fn-article-source
                                                fn-article-octet-list-true-listp
                                                fn-article-append-associative (:e binary-append) binary-append car-cons cdr-cons)
                                              (theory 'minimal-theory))
            :use ((:instance fn-article-successful-parse-syntax-p (octets y))
                  (:instance fn-article-successful-parse-fields-correspond (octets y))
                  (:instance fn-article-successful-parse-preserves-source (octets y))
                  (:instance fn-article-successful-parse-fields-recompose-header (octets y))
                  (:instance fn-rs-parsed-fields-are-wf
                   (fields (fn-article-fields (fn-article-result-article (fn-article-parse y))))))))))

(local
 (defthm fn-rs-walk-of-stripped-fields
   (implies (and (fn-rs-fields-wfp f)
                 (equal y (append (fn-article-fields-octets f) (cons 13 (cons 10 b)))))
            (equal (fn-rs-source-walk (fn-pu-strip y nil) nil)
                   (append (fn-article-fields-octets (fn-rs-authored-fields f))
                           (cons 13 (cons 10 b)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-rs-strip-of-wf-fields fn-rs-walk-of-wf-fields
                                                fn-rs-drop-path-xref-keeps-wf
                                                fn-rs-authored-fields-of-drop-path-xref)
                                              (theory 'minimal-theory))))))

; -----------------------------------------------------------------------------
; The characterization: for every article the parser accepts, the authored
; source is the reserved-field walk over the octets with Path and Xref
; stripped.  It is the parser lemma the relay keystones rest on.

(defthm fn-rs-authored-source-is-the-walk
  (implies (fn-article-result-okp (fn-article-parse y))
           (equal (fn-hc-authored-source
                   (fn-article-result-article (fn-article-parse y)))
                  (fn-rs-source-walk (fn-pu-strip y nil) nil)))
  :hints (("Goal" :in-theory (union-theories '(fn-hc-authored-source
                                               fn-rs-source-header-is-the-authored-fields
                                               fn-article-append-associative car-cons cdr-cons
                                               (:e binary-append) binary-append)
                                             (theory 'minimal-theory))
           :use (fn-rs-a-parsed-article-is-its-fields
                 (:instance fn-rs-walk-of-stripped-fields
                  (f (fn-article-fields (fn-article-result-article (fn-article-parse y))))
                  (b (fn-article-body (fn-article-result-article (fn-article-parse y)))))))))
