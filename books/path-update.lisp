; fn: what a relaying and serving agent changes in an article it accepts from
; a peer: Path and Xref, and nothing else (RFC 5537 sections 3.6 and 3.7).
;
; RFC 5537 section 3.6 step 7 and section 3.7 step 6: an agent that accepts
; an article MUST update Path as section 3.2.1 describes; section 3.6 step 8
; permits a relaying agent to delete a received Xref, and section 3.7 step 7
; has a serving agent remove it (the sender's Xref names the sender's article
; numbers).  Section 3.6's last paragraph: nothing else in the article may be
; altered, deleted or rearranged, and the body never.
;
; fn's relaying agent (the transit port, books/peer-inbound.lisp) and its
; serving agent (the reader, books/nntp.lisp) are one news server over one
; store, so the update is made ONCE, when the article is accepted, and the
; stored octets are the served octets.  Section 3.2.1's first sentence permits
; exactly this: "If a relaying or serving agent receives an article from an
; injecting or serving agent that is part of the same news server, it MAY
; leave the Path header field of the article unchanged."  The alternative,
; rewriting at serving time, puts a transformation on every served read, makes
; the stored bytes differ from the served ones, and gives replay and the
; outbound feed a second rendering to agree with; see specs/peering.md 2.3.
;
; The update (section 3.2.1 steps 1 and 3): prepend "!", then the
; <path-diagnostic> of the expected identity of the source -- "!" when it is
; the leftmost <path-identity> of the received Path, ".MISMATCH." and the
; expected identity otherwise -- then the agent's own <path-identity>.  The
; result begins `<identity>!!' or `<identity>!.MISMATCH.<expected>!'.  The
; diagnostic is books/path.lisp's `fn-path-diagnostic', the one owner of that
; decision; this book renders what it is given.
;
; The transformation is a walk over the raw header lines, never a parse and a
; re-serialization, so an octet it does not mean to change cannot move:
;
;   a field line named Xref (case-insensitively) is deleted with its
;     continuation lines;
;   a field line named Path has the insertion placed after `Path:' and its
;     whitespace, unless its content already begins with `<identity>!' -- the
;     agent has already updated it, which is what makes the walk idempotent;
;   every other line, the blank line and the body are copied.
;
; What is proved of it (below): removing every Path and Xref field from the
; input and from the output leaves the same octets (so every other header and
; the body are byte-identical, in order); a second pass changes nothing; the
; output has no Xref field; and every Path field of the output begins with
; the agent's identity.  The walk is total and structural, and reads nothing
; through the Lisp reader.

(in-package "ACL2")
(include-book "path")

(defconst *fn-pu-path-colon* '(112 97 116 104 58)) ; "path:"
(defconst *fn-pu-xref-colon* '(120 114 101 102 58)) ; "xref:"
(defconst *fn-pu-mismatch* '(46 77 73 83 77 65 84 67 72 46)) ; ".MISMATCH."

; -----------------------------------------------------------------------------
; Total list vocabulary

(defun fn-pu-append (a b)
  (declare (xargs :guard t))
  (if (consp a) (cons (car a) (fn-pu-append (cdr a) b)) b))

(defun fn-pu-take (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (or (zp n) (atom x)) nil
      (cons (car x) (fn-pu-take (- n 1) (cdr x))))))

(defun fn-pu-drop (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (or (zp n) (atom x)) x
      (fn-pu-drop (- n 1) (cdr x)))))

(defun fn-pu-wspp (c)
  (declare (xargs :guard t))
  (or (equal c 32) (equal c 9)))

(defun fn-pu-take-wsp (x)
  (declare (xargs :guard t))
  (if (and (consp x) (fn-pu-wspp (car x)))
      (cons (car x) (fn-pu-take-wsp (cdr x)))
    nil))

(defun fn-pu-skip-wsp (x)
  (declare (xargs :guard t))
  (if (and (consp x) (fn-pu-wspp (car x)))
      (fn-pu-skip-wsp (cdr x))
    x))

(defun fn-pu-no-crp (x)
  ; no CR octet anywhere in x
  (declare (xargs :guard t))
  (if (consp x)
      (and (not (equal (car x) 13)) (fn-pu-no-crp (cdr x)))
    t))

(defun fn-pu-prefixp (p x)
  (declare (xargs :guard t))
  (if (consp p)
      (and (consp x) (equal (car p) (car x)) (fn-pu-prefixp (cdr p) (cdr x)))
    t))

(defun fn-pu-downcase (c)
  (declare (xargs :guard t))
  (if (and (integerp c) (<= 65 c) (<= c 90)) (+ c 32) c))

; `line' begins with `name' (lower case, with its colon), ASCII
; case-insensitively.
(defun fn-pu-named-p (line name)
  (declare (xargs :guard t))
  (if (consp name)
      (and (consp line)
           (equal (fn-pu-downcase (car line)) (car name))
           (fn-pu-named-p (cdr line) (cdr name)))
    t))

; -----------------------------------------------------------------------------
; Physical lines.  `fn-pu-line' is x up to and including its first CRLF (all
; of x when it has none); `fn-pu-after-line' is what follows.

(defun fn-pu-crlf-atp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) 13) (consp (cdr x)) (equal (cadr x) 10)))

(defun fn-pu-line (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((fn-pu-crlf-atp x) (list 13 10))
        (t (cons (car x) (fn-pu-line (cdr x))))))

(defun fn-pu-after-line (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((fn-pu-crlf-atp x) (cddr x))
        (t (fn-pu-after-line (cdr x)))))

(defthm fn-pu-after-line-is-smaller
  (implies (consp x)
           (< (acl2-count (fn-pu-after-line x)) (acl2-count x)))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; The Path edit

(defun fn-pu-insertion (id dg)
  ; <id> "!" <dg> "!": with dg empty this is `<id>!!' (diag-match).
  (declare (xargs :guard t))
  (fn-pu-append id (cons 33 (fn-pu-append dg (list 33)))))

; The content of a Path line already begins with `<id>!'.
(defun fn-pu-markedp (line id)
  (declare (xargs :guard t))
  (fn-pu-prefixp (fn-pu-append id (list 33))
                  (fn-pu-skip-wsp (fn-pu-drop 5 line))))

(defun fn-pu-edit-path (line id dg)
  (declare (xargs :guard t))
  (if (or (atom id) (fn-pu-markedp line id))
      line
    (let ((r (fn-pu-drop 5 line)))
      (fn-pu-append (fn-pu-take 5 line)
                     (fn-pu-append (fn-pu-take-wsp r)
                                    (fn-pu-append (fn-pu-insertion id dg)
                                                   (fn-pu-skip-wsp r)))))))

; -----------------------------------------------------------------------------
; The walk.  `dropping' is set after an Xref field line, so its continuation
; lines go with it.  The header block ends at the blank line (a line that is
; exactly CRLF); that line and everything after it are returned as they are.

(defun fn-pu-walk (x id dg dropping)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (atom x)
      x
    (let ((line (fn-pu-line x))
          (rest (fn-pu-after-line x)))
      (cond ((equal line '(13 10)) x)
            ((fn-pu-wspp (car line))
             (if dropping
                 (fn-pu-walk rest id dg t)
               (fn-pu-append line (fn-pu-walk rest id dg nil))))
            ((fn-pu-named-p line *fn-pu-xref-colon*)
             (fn-pu-walk rest id dg t))
            ((fn-pu-named-p line *fn-pu-path-colon*)
             (fn-pu-append (fn-pu-edit-path line id dg)
                            (fn-pu-walk rest id dg nil)))
            (t (fn-pu-append line (fn-pu-walk rest id dg nil)))))))

; The specification side of "nothing else changed": the article with every
; Path and Xref field (and their continuation lines) removed.
(defun fn-pu-strip (x dropping)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (atom x)
      x
    (let ((line (fn-pu-line x))
          (rest (fn-pu-after-line x)))
      (cond ((equal line '(13 10)) x)
            ((fn-pu-wspp (car line))
             (if dropping
                 (fn-pu-strip rest t)
               (fn-pu-append line (fn-pu-strip rest nil))))
            ((or (fn-pu-named-p line *fn-pu-xref-colon*)
                 (fn-pu-named-p line *fn-pu-path-colon*))
             (fn-pu-strip rest t))
            (t (fn-pu-append line (fn-pu-strip rest nil)))))))

; No field line of the header block is an Xref.
(defun fn-pu-xref-freep (x)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (atom x)
      t
    (let ((line (fn-pu-line x)))
      (cond ((equal line '(13 10)) t)
            ((and (not (fn-pu-wspp (car line)))
                  (fn-pu-named-p line *fn-pu-xref-colon*))
             nil)
            (t (fn-pu-xref-freep (fn-pu-after-line x)))))))

; Every Path field line of the header block begins with `<id>!'.
(defun fn-pu-path-markedp (x id)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (atom x)
      t
    (let ((line (fn-pu-line x)))
      (cond ((equal line '(13 10)) t)
            ((and (not (fn-pu-wspp (car line)))
                  (not (fn-pu-named-p line *fn-pu-xref-colon*))
                  (fn-pu-named-p line *fn-pu-path-colon*)
                  (not (fn-pu-markedp line id)))
             nil)
            (t (fn-pu-path-markedp (fn-pu-after-line x) id))))))

; What the walk may insert: nothing (an agent with no identity only strips
; Xref), or an identity that begins with a non-WSP octet, where neither the
; identity nor the diagnostic carries a CR.  A <path-identity> (books/path.lisp
; `fn-path-identityp') and the rendered diagnostic always are.
(defun fn-pu-insertablep (id dg)
  (declare (xargs :guard t))
  (or (atom id)
      (and (not (fn-pu-wspp (car id)))
           (fn-pu-no-crp id)
           (fn-pu-no-crp dg))))

; The rendered <path-diagnostic> of books/path.lisp `fn-path-diagnostic':
; (:match) is the empty diag-match, (:mismatch expected) is ".MISMATCH."
; and the expected identity.
(defun fn-pu-diagnostic-octets (diagnostic)
  (declare (xargs :guard t))
  (if (and (consp diagnostic) (equal (car diagnostic) :mismatch)
           (consp (cdr diagnostic)))
      (fn-pu-append *fn-pu-mismatch* (cadr diagnostic))
    nil))

(defun fn-pu-relay (x id dg)
  ; The entry point: x is the received article, id the agent's own
  ; <path-identity> (or nil), dg the rendered diagnostic.
  (declare (xargs :guard t))
  (if (fn-pu-insertablep id dg)
      (fn-pu-walk x id dg nil)
    (fn-pu-walk x nil nil nil)))

; -----------------------------------------------------------------------------
; The proofs.  A physical line of a walk's output is re-read by a second walk
; as the same line: a line that ends in CRLF is re-read exactly
; (fn-pu-line-of-a-crlf-ended-piece), the last line of an article with no
; final CRLF is followed by nothing, and the Path edit inserts no CR, so an
; edited line ends where it ended (fn-pu-edit-path-keeps-crlf-endedp).  From
; that, each property is one induction over the walk.

(defun fn-pu-has-crlfp (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((fn-pu-crlf-atp x) t)
        (t (fn-pu-has-crlfp (cdr x)))))

(defun fn-pu-crlf-endedp (l)
  (declare (xargs :guard t))
  (cond ((atom l) nil)
        ((fn-pu-crlf-atp l) (atom (cddr l)))
        (t (fn-pu-crlf-endedp (cdr l)))))

(local
 (defthm fn-pu-true-listp-of-append
   (equal (true-listp (fn-pu-append a b)) (true-listp b))))

(local
 (defthm fn-pu-append-nil-right
   (implies (true-listp a) (equal (fn-pu-append a nil) a))))

(local
 (defthm fn-pu-append-assoc
   (equal (fn-pu-append (fn-pu-append a b) c)
          (fn-pu-append a (fn-pu-append b c)))))

(local
 (defthm fn-pu-true-listp-of-line
   (true-listp (fn-pu-line x))))

(local
 (defthm fn-pu-line-and-after-recompose
   (implies (true-listp x)
            (equal (fn-pu-append (fn-pu-line x) (fn-pu-after-line x)) x))))

(local
 (defthm fn-pu-line-of-a-line-without-crlf
   (implies (and (not (fn-pu-has-crlfp x)) (true-listp x))
            (and (equal (fn-pu-line x) x)
                 (equal (fn-pu-after-line x) nil)))))

(local
 (defthm fn-pu-line-with-crlf-is-crlf-ended
   (implies (fn-pu-has-crlfp x)
            (fn-pu-crlf-endedp (fn-pu-line x)))))

(local
 (defthm fn-pu-line-of-a-crlf-ended-piece
   (implies (fn-pu-crlf-endedp l)
            (and (equal (fn-pu-line (fn-pu-append l z)) (fn-pu-line l))
                 (equal (fn-pu-after-line (fn-pu-append l z)) z)))))

(local
 (defthm fn-pu-line-of-crlf-ended
   (implies (and (fn-pu-crlf-endedp l) (true-listp l))
            (equal (fn-pu-line l) l))))

(local
 (defthm fn-pu-crlf-endedp-of-append-no-cr
   (implies (fn-pu-no-crp a)
            (equal (fn-pu-crlf-endedp (fn-pu-append a b))
                   (fn-pu-crlf-endedp b)))))

(local
 (defthm fn-pu-has-crlfp-of-append-no-cr
   (implies (fn-pu-no-crp a)
            (equal (fn-pu-has-crlfp (fn-pu-append a b))
                   (fn-pu-has-crlfp b)))))

(local
 (defthm fn-pu-no-crp-of-append
   (equal (fn-pu-no-crp (fn-pu-append a b))
          (and (fn-pu-no-crp a) (fn-pu-no-crp b)))))

(local
 (defthm fn-pu-take-wsp-and-skip-wsp-recompose
   (equal (fn-pu-append (fn-pu-take-wsp x) (fn-pu-skip-wsp x)) x)))

(local
 (defthm fn-pu-no-crp-of-take-wsp
   (fn-pu-no-crp (fn-pu-take-wsp x))))

(local
 (defthm fn-pu-take-and-drop-recompose
   (implies (true-listp x)
            (equal (fn-pu-append (fn-pu-take n x) (fn-pu-drop n x)) x))))

(local
 (defthm fn-pu-named-p-no-cr-take
   (implies (and (fn-pu-named-p line name)
                 (fn-pu-no-crp name)
                 (equal n (len name)))
            (fn-pu-no-crp (fn-pu-take n line)))))

(local
 (defthm fn-pu-named-p-of-append-at-length
   (implies (equal (len a) (len name))
            (equal (fn-pu-named-p (fn-pu-append a y) name)
                   (fn-pu-named-p a name)))))

(local
 (defthm fn-pu-len-of-take
   (implies (<= (nfix n) (len x))
            (equal (len (fn-pu-take n x)) (nfix n)))))

(local
 (defthm fn-pu-named-p-long-enough
   (implies (fn-pu-named-p line name)
            (<= (len name) (len line)))
   :rule-classes :linear))

(local
 (defthm fn-pu-named-p-of-take-at-length
   (implies (equal n (len name))
            (equal (fn-pu-named-p (fn-pu-take n line) name)
                   (fn-pu-named-p line name)))))

(local
 (defthm fn-pu-crlf-endedp-past-a-no-cr-prefix
   (implies (fn-pu-no-crp (fn-pu-take n x))
            (equal (fn-pu-crlf-endedp (fn-pu-drop n x))
                   (fn-pu-crlf-endedp x)))))

(local
 (defthm fn-pu-has-crlfp-past-a-no-cr-prefix
   (implies (fn-pu-no-crp (fn-pu-take n x))
            (equal (fn-pu-has-crlfp (fn-pu-drop n x))
                   (fn-pu-has-crlfp x)))))

(local
 (defthm fn-pu-crlf-endedp-of-skip-wsp
   (equal (fn-pu-crlf-endedp (fn-pu-skip-wsp x))
          (fn-pu-crlf-endedp x))))

(local
 (defthm fn-pu-has-crlfp-of-skip-wsp
   (equal (fn-pu-has-crlfp (fn-pu-skip-wsp x))
          (fn-pu-has-crlfp x))))

(local
 (defthm fn-pu-edit-path-keeps-crlf-endedp
   (implies (and (fn-pu-named-p line *fn-pu-path-colon*)
                 (fn-pu-insertablep id dg))
            (equal (fn-pu-crlf-endedp (fn-pu-edit-path line id dg))
                   (fn-pu-crlf-endedp line)))))

(local
 (defthm fn-pu-edit-path-keeps-has-crlfp
   (implies (and (fn-pu-named-p line *fn-pu-path-colon*)
                 (fn-pu-insertablep id dg))
            (equal (fn-pu-has-crlfp (fn-pu-edit-path line id dg))
                   (fn-pu-has-crlfp line)))))

(local
 (defthm fn-pu-true-listp-of-drop
   (implies (true-listp x) (true-listp (fn-pu-drop n x)))))

(local
 (defthm fn-pu-true-listp-of-skip-wsp
   (implies (true-listp x) (true-listp (fn-pu-skip-wsp x)))))

(local
 (defthm fn-pu-true-listp-of-edit-path
   (implies (true-listp line)
            (true-listp (fn-pu-edit-path line id dg)))))

(local
 (defthm fn-pu-edit-path-keeps-the-name
   (implies (and (fn-pu-named-p line *fn-pu-path-colon*)
                 (equal (len name) 5))
            (equal (fn-pu-named-p (fn-pu-edit-path line id dg) name)
                   (fn-pu-named-p line name)))))

(local
 (defthm fn-pu-edit-path-keeps-the-first-octet
   (implies (fn-pu-named-p line *fn-pu-path-colon*)
            (equal (car (fn-pu-edit-path line id dg)) (car line)))))

(local
 (defthm fn-pu-named-path-is-not-crlf
   (implies (fn-pu-named-p line *fn-pu-path-colon*)
            (and (not (equal line '(13 10)))
                 (consp line)
                 (not (fn-pu-wspp (car line)))))))

(local
 (defthm fn-pu-prefixp-of-append
   (implies (true-listp a)
            (fn-pu-prefixp a (fn-pu-append a b)))))

(local
 (defthm fn-pu-skip-wsp-of-wsp-prefix
   (equal (fn-pu-skip-wsp (fn-pu-append (fn-pu-take-wsp x) y))
          (fn-pu-skip-wsp y))))

(local
 (defthm fn-pu-drop-of-take-append
   (implies (equal n (len (fn-pu-take n x)))
            (equal (fn-pu-drop n (fn-pu-append (fn-pu-take n x) y)) y))))

(local
 (defthm fn-pu-skip-wsp-of-append-non-wsp
   (implies (and (consp a) (not (fn-pu-wspp (car a))))
            (equal (fn-pu-skip-wsp (fn-pu-append a b)) (fn-pu-append a b)))))

(local
 (defthm fn-pu-prefixp-of-append-both
   (equal (fn-pu-prefixp (fn-pu-append a b) (fn-pu-append a c))
          (fn-pu-prefixp b c))))

(local
 (defthm fn-pu-edit-path-is-marked
   (implies (and (fn-pu-named-p line *fn-pu-path-colon*)
                 (fn-pu-insertablep id dg)
                 (consp id)
                 (true-listp id))
            (fn-pu-markedp (fn-pu-edit-path line id dg) id))
   :hints (("Goal" :in-theory (enable fn-pu-insertion)))))

(local
 (defthm fn-pu-edit-path-is-idempotent
   (implies (and (fn-pu-named-p line *fn-pu-path-colon*)
                 (fn-pu-insertablep id dg)
                 (true-listp id))
            (equal (fn-pu-edit-path (fn-pu-edit-path line id dg) id dg2)
                   (fn-pu-edit-path line id dg)))
   :hints (("Goal" :in-theory (disable fn-pu-markedp)
            :use fn-pu-edit-path-is-marked
            :expand ((fn-pu-edit-path line id dg))))))

(local
 (defthm fn-pu-line-of-line
   (equal (fn-pu-line (fn-pu-line x)) (fn-pu-line x))))

(local
 (defthm fn-pu-after-line-of-line
   (equal (fn-pu-after-line (fn-pu-line x)) nil)))

(local
 (defthm fn-pu-has-crlfp-of-line
   (equal (fn-pu-has-crlfp (fn-pu-line x)) (fn-pu-has-crlfp x))))

(local
 (defthm fn-pu-reparse-a-line
   (implies (and (consp x)
                 (or (fn-pu-has-crlfp x) (null z)))
            (and (equal (fn-pu-line (fn-pu-append (fn-pu-line x) z))
                        (fn-pu-line x))
                 (equal (fn-pu-after-line (fn-pu-append (fn-pu-line x) z))
                        z)))
   :hints (("Goal" :cases ((fn-pu-has-crlfp x))))))

(local
 (defthm fn-pu-reparse-an-edited-line
   (implies (and (consp x)
                 (fn-pu-named-p (fn-pu-line x) *fn-pu-path-colon*)
                 (fn-pu-insertablep id dg)
                 (or (fn-pu-has-crlfp x) (null z)))
            (and (equal (fn-pu-line (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z))
                        (fn-pu-edit-path (fn-pu-line x) id dg))
                 (equal (fn-pu-after-line (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z))
                        z)))
   :hints (("Goal" :cases ((fn-pu-has-crlfp x))
            :in-theory (disable fn-pu-edit-path))
           ("Subgoal 2" :use ((:instance fn-pu-line-of-a-line-without-crlf
                                         (x (fn-pu-edit-path (fn-pu-line x) id dg))))))))

(local
 (defthm fn-pu-true-listp-of-after-line
   (implies (true-listp x) (true-listp (fn-pu-after-line x)))))

(local
 (defthm fn-pu-after-line-without-crlf
   (implies (not (fn-pu-has-crlfp x))
            (equal (fn-pu-after-line x) nil))))

(local
 (defthm fn-pu-consp-line
   (implies (consp x) (consp (fn-pu-line x)))))

(local
 (defthm fn-pu-car-of-line
   (implies (consp x) (equal (car (fn-pu-line x)) (car x)))))

(local
 (defthm fn-pu-true-listp-of-walk
   (implies (true-listp x)
            (true-listp (fn-pu-walk x id dg d)))
   :hints (("Goal" :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                       fn-pu-edit-path)))))

(local
 (defthm fn-pu-consp-of-append
   (implies (consp a) (consp (fn-pu-append a b)))))

(local
 (defthm fn-pu-consp-of-edit-path
   (implies (fn-pu-named-p line *fn-pu-path-colon*)
            (consp (fn-pu-edit-path line id dg)))))

(local
 (defthm fn-pu-walk-of-a-line-piece
   (implies (and (consp x)
                 (or (fn-pu-has-crlfp x) (null z))
                 (not (equal (fn-pu-line x) '(13 10))))
            (equal (fn-pu-walk (fn-pu-append (fn-pu-line x) z) id dg d)
                   (let ((line (fn-pu-line x)))
                     (cond ((fn-pu-wspp (car line))
                            (if d
                                (fn-pu-walk z id dg t)
                              (fn-pu-append line (fn-pu-walk z id dg nil))))
                           ((fn-pu-named-p line *fn-pu-xref-colon*)
                            (fn-pu-walk z id dg t))
                           ((fn-pu-named-p line *fn-pu-path-colon*)
                            (fn-pu-append (fn-pu-edit-path line id dg)
                                          (fn-pu-walk z id dg nil)))
                           (t (fn-pu-append line (fn-pu-walk z id dg nil)))))))
   :hints (("Goal" :expand ((fn-pu-walk (fn-pu-append (fn-pu-line x) z) id dg d)
                            (fn-pu-walk (fn-pu-line x) id dg d))
            :do-not-induct t
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep)))))

(local
 (defthm fn-pu-named-path-line-starts-with-p
   (implies (and (consp x) (fn-pu-named-p (fn-pu-line x) *fn-pu-path-colon*))
            (and (not (equal (car x) 32)) (not (equal (car x) 9))
                 (not (equal (car x) 13))))
   :hints (("Goal" :use ((:instance fn-pu-car-of-line))
            :in-theory (e/d (fn-pu-named-p) (fn-pu-car-of-line fn-pu-line))))))

(local
 (defthm fn-pu-line-of-an-edited-line
   (implies (and (consp x)
                 (fn-pu-named-p (fn-pu-line x) *fn-pu-path-colon*)
                 (fn-pu-insertablep id dg))
            (and (equal (fn-pu-line (fn-pu-edit-path (fn-pu-line x) id dg))
                        (fn-pu-edit-path (fn-pu-line x) id dg))
                 (equal (fn-pu-after-line (fn-pu-edit-path (fn-pu-line x) id dg))
                        nil)))
   :hints (("Goal" :use ((:instance fn-pu-reparse-an-edited-line (z nil)))
            :in-theory (disable fn-pu-reparse-an-edited-line fn-pu-edit-path
                                fn-pu-line fn-pu-after-line fn-pu-insertablep)))))

(local
 (defthm fn-pu-walk-of-an-edited-piece
   (implies (and (consp x)
                 (fn-pu-named-p (fn-pu-line x) *fn-pu-path-colon*)
                 (not (fn-pu-named-p (fn-pu-line x) *fn-pu-xref-colon*))
                 (fn-pu-insertablep id dg)
                 (true-listp id)
                 (or (fn-pu-has-crlfp x) (null z)))
            (equal (fn-pu-walk (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z)
                               id dg2 d)
                   (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg)
                                 (fn-pu-walk z id dg2 nil))))
   :hints (("Goal" :expand ((fn-pu-walk (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z)
                                        id dg2 d)
                            (fn-pu-walk (fn-pu-edit-path (fn-pu-line x) id dg) id dg2 d))
            :do-not-induct t
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep)))))

(local
 (defthm fn-pu-walk-is-idempotent
   (implies (and (fn-pu-insertablep id dg)
                 (true-listp id))
            (equal (fn-pu-walk (fn-pu-walk x id dg d) id dg2 nil)
                   (fn-pu-walk x id dg d)))
   :hints (("Goal" :induct (fn-pu-walk x id dg d)
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep))
           ("Subgoal *1/7" :cases ((fn-pu-has-crlfp x)))
           ("Subgoal *1/6" :cases ((fn-pu-has-crlfp x)))
           ("Subgoal *1/4" :cases ((fn-pu-has-crlfp x))))))

(local
 (defthm fn-pu-strip-of-a-line-piece
   (implies (and (consp x)
                 (or (fn-pu-has-crlfp x) (null z))
                 (not (equal (fn-pu-line x) '(13 10))))
            (equal (fn-pu-strip (fn-pu-append (fn-pu-line x) z) d)
                   (let ((line (fn-pu-line x)))
                     (cond ((fn-pu-wspp (car line))
                            (if d
                                (fn-pu-strip z t)
                              (fn-pu-append line (fn-pu-strip z nil))))
                           ((or (fn-pu-named-p line *fn-pu-xref-colon*)
                                (fn-pu-named-p line *fn-pu-path-colon*))
                            (fn-pu-strip z t))
                           (t (fn-pu-append line (fn-pu-strip z nil)))))))
   :hints (("Goal" :expand ((fn-pu-strip (fn-pu-append (fn-pu-line x) z) d)
                            (fn-pu-strip (fn-pu-line x) d))
            :do-not-induct t
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep)))))

(local
 (defthm fn-pu-strip-of-an-edited-piece
   (implies (and (consp x)
                 (fn-pu-named-p (fn-pu-line x) *fn-pu-path-colon*)
                 (fn-pu-insertablep id dg)
                 (or (fn-pu-has-crlfp x) (null z)))
            (equal (fn-pu-strip (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z) d)
                   (fn-pu-strip z t)))
   :hints (("Goal" :expand ((fn-pu-strip (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z) d)
                            (fn-pu-strip (fn-pu-edit-path (fn-pu-line x) id dg) d))
            :do-not-induct t
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep)))))

(local
 (defun fn-pu-walk-strip-induct (x id dg d1 d2)
   (declare (xargs :measure (acl2-count x)))
   (if (atom x)
       (list x id dg d1 d2)
     (let ((rest (fn-pu-after-line x)))
       (list (fn-pu-walk-strip-induct rest id dg nil nil)
             (fn-pu-walk-strip-induct rest id dg nil t)
             (fn-pu-walk-strip-induct rest id dg t nil)
             (fn-pu-walk-strip-induct rest id dg t t))))))

(local
 (defthm fn-pu-walk-changes-only-path-and-xref
   (implies (and (fn-pu-insertablep id dg)
                 (true-listp id)
                 (booleanp d1) (booleanp d2))
            (equal (fn-pu-strip (fn-pu-walk x id dg d1) d2)
                   (fn-pu-strip x (or d1 d2))))
   :hints (("Goal" :induct (fn-pu-walk-strip-induct x id dg d1 d2)
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep))
           ("Subgoal *1/2" :cases ((and (fn-pu-has-crlfp x) (equal d2 t))
                                   (and (fn-pu-has-crlfp x) (equal d2 nil))
                                   (and (not (fn-pu-has-crlfp x)) (equal d2 t))
                                   (and (not (fn-pu-has-crlfp x)) (equal d2 nil)))))))

(local
 (defthm fn-pu-xref-freep-of-a-line-piece
   (implies (and (consp x)
                 (or (fn-pu-has-crlfp x) (null z))
                 (not (equal (fn-pu-line x) '(13 10))))
            (equal (fn-pu-xref-freep (fn-pu-append (fn-pu-line x) z))
                   (if (and (not (fn-pu-wspp (car (fn-pu-line x))))
                            (fn-pu-named-p (fn-pu-line x) *fn-pu-xref-colon*))
                       nil
                     (fn-pu-xref-freep z))))
   :hints (("Goal" :expand ((fn-pu-xref-freep (fn-pu-append (fn-pu-line x) z))
                            (fn-pu-xref-freep (fn-pu-line x)))
            :do-not-induct t
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep)))))

(local
 (defthm fn-pu-xref-freep-of-an-edited-piece
   (implies (and (consp x)
                 (fn-pu-named-p (fn-pu-line x) *fn-pu-path-colon*)
                 (not (fn-pu-named-p (fn-pu-line x) *fn-pu-xref-colon*))
                 (fn-pu-insertablep id dg)
                 (or (fn-pu-has-crlfp x) (null z)))
            (equal (fn-pu-xref-freep (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z))
                   (fn-pu-xref-freep z)))
   :hints (("Goal" :expand ((fn-pu-xref-freep (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z))
                            (fn-pu-xref-freep (fn-pu-edit-path (fn-pu-line x) id dg)))
            :do-not-induct t
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep)))))

(local
 (defthm fn-pu-walk-leaves-no-xref
   (implies (and (fn-pu-insertablep id dg)
                 (true-listp id))
            (fn-pu-xref-freep (fn-pu-walk x id dg d)))
   :hints (("Goal" :induct (fn-pu-walk x id dg d)
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep))
           ("Subgoal *1/7" :cases ((fn-pu-has-crlfp x)))
           ("Subgoal *1/6" :cases ((fn-pu-has-crlfp x)))
           ("Subgoal *1/4" :cases ((fn-pu-has-crlfp x))))))

(local
 (defthm fn-pu-path-markedp-of-a-line-piece
   (implies (and (consp x)
                 (or (fn-pu-has-crlfp x) (null z))
                 (not (equal (fn-pu-line x) '(13 10))))
            (equal (fn-pu-path-markedp (fn-pu-append (fn-pu-line x) z) id)
                   (if (and (not (fn-pu-wspp (car (fn-pu-line x))))
                            (not (fn-pu-named-p (fn-pu-line x) *fn-pu-xref-colon*))
                            (fn-pu-named-p (fn-pu-line x) *fn-pu-path-colon*)
                            (not (fn-pu-markedp (fn-pu-line x) id)))
                       nil
                     (fn-pu-path-markedp z id))))
   :hints (("Goal" :expand ((fn-pu-path-markedp (fn-pu-append (fn-pu-line x) z) id)
                            (fn-pu-path-markedp (fn-pu-line x) id))
            :do-not-induct t
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep fn-pu-markedp)))))

(local
 (defthm fn-pu-path-markedp-of-an-edited-piece
   (implies (and (consp x)
                 (fn-pu-named-p (fn-pu-line x) *fn-pu-path-colon*)
                 (not (fn-pu-named-p (fn-pu-line x) *fn-pu-xref-colon*))
                 (fn-pu-insertablep id dg)
                 (consp id) (true-listp id)
                 (or (fn-pu-has-crlfp x) (null z)))
            (equal (fn-pu-path-markedp (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z) id)
                   (fn-pu-path-markedp z id)))
   :hints (("Goal" :expand ((fn-pu-path-markedp (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z) id)
                            (fn-pu-path-markedp (fn-pu-edit-path (fn-pu-line x) id dg) id))
            :do-not-induct t
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep fn-pu-markedp)))))

(local
 (defthm fn-pu-walk-marks-every-path
   (implies (and (fn-pu-insertablep id dg)
                 (consp id) (true-listp id))
            (fn-pu-path-markedp (fn-pu-walk x id dg d) id))
   :hints (("Goal" :induct (fn-pu-walk x id dg d)
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep fn-pu-markedp))
           ("Subgoal *1/7" :cases ((fn-pu-has-crlfp x)))
           ("Subgoal *1/6" :cases ((fn-pu-has-crlfp x)))
           ("Subgoal *1/4" :cases ((fn-pu-has-crlfp x))))))

; -----------------------------------------------------------------------------
; The article-level entry: the agent's own <path-identity> (anything else,
; including an unset policy slot, updates no Path and only removes Xref), the
; expected identity of the source (the peer record's), and the received
; octets.  The diagnostic is books/path.lisp's decision over the received
; Path; an article the parser refuses has no Path to read, and its
; diagnostic is decided over none (the transfer decision refuses such an
; article before it is stored, books/peer-inbound.lisp).

(defun fn-pu-received-path (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((parsed (fn-article-parse octets))
         (article (if (and (fn-article-result-okp parsed) (true-listp parsed))
                      (fn-article-result-article parsed)
                    nil)))
    (if (and article (fn-article-syntax-p article))
        (fn-af-path-field-value article)
      nil)))

; An expected identity that could carry a CR into the Path line is read as
; none: a peer record's is always a <path-identity> (fn-cfg-peer-okp), which
; carries none (fn-pu-path-identity-has-no-cr), so this changes nothing a
; checked configuration can reach, and it makes every keystone below hold
; with no hypothesis about the caller's argument.
(defun fn-pu-expected (expected)
  (declare (xargs :guard t))
  (if (fn-pu-no-crp expected) expected nil))

(defun fn-pu-relay-article (octets identity expected)
  (declare (xargs :guard t :verify-guards nil))
  (fn-pu-relay octets
               (if (fn-path-identityp identity) identity nil)
               (fn-pu-diagnostic-octets
                (fn-path-diagnostic (fn-pu-expected expected)
                                    (fn-pu-received-path octets)))))

(local
 (defthm fn-pu-identity-chars-have-no-cr
   (implies (fn-path-identity-charsp x)
            (and (fn-pu-no-crp x) (true-listp x)))
   :hints (("Goal" :in-theory (enable fn-path-identity-charsp
                                      fn-path-identity-charp)))))

(local
 (defthm fn-pu-path-identity-is-insertable
   (implies (fn-path-identityp identity)
            (and (consp identity) (true-listp identity)
                 (not (fn-pu-wspp (car identity)))
                 (fn-pu-no-crp identity)))
   :hints (("Goal" :in-theory (enable fn-path-identityp fn-path-identity-charp
                                      fn-path-identity-charsp)))))

; A <path-identity> carries no CR (books/path.lisp: alphanumerics, "-", "_",
; "."), so it is an expected identity every keystone below admits.
(defthm fn-pu-path-identity-has-no-cr
  (implies (fn-path-identityp e) (fn-pu-no-crp e))
  :hints (("Goal" :in-theory (disable fn-path-identityp))))

(local
 (defthm fn-pu-no-crp-of-a-diagnostic
   (fn-pu-no-crp (fn-pu-diagnostic-octets
                  (fn-path-diagnostic (fn-pu-expected expected) path)))
   :hints (("Goal" :in-theory (enable fn-path-diagnostic)))))

(local
 (defthm fn-pu-relay-article-inserts-an-insertable
   (fn-pu-insertablep (if (fn-path-identityp identity) identity nil)
                      (fn-pu-diagnostic-octets
                       (fn-path-diagnostic (fn-pu-expected expected) path)))
   :hints (("Goal" :in-theory (e/d (fn-pu-insertablep)
                                   (fn-pu-diagnostic-octets fn-path-diagnostic
                                    fn-path-identityp fn-pu-expected))))))

(local
 (defthm fn-pu-an-identity-is-insertable-with-a-diagnostic
   (implies (fn-path-identityp identity)
            (fn-pu-insertablep identity
                               (fn-pu-diagnostic-octets
                                (fn-path-diagnostic (fn-pu-expected expected)
                                                    path))))
   :hints (("Goal" :in-theory (e/d (fn-pu-insertablep)
                                   (fn-pu-diagnostic-octets fn-path-diagnostic
                                    fn-path-identityp))))))

(local
 (defthm fn-pu-relay-article-is-the-walk
   (equal (fn-pu-relay-article octets identity expected)
          (fn-pu-walk octets
                      (if (fn-path-identityp identity) identity nil)
                      (fn-pu-diagnostic-octets
                       (fn-path-diagnostic
                        (fn-pu-expected expected) (fn-pu-received-path octets)))
                      nil))
   :hints (("Goal" :in-theory (e/d (fn-pu-insertablep)
                                   (fn-pu-walk fn-pu-received-path fn-pu-expected
                                    fn-pu-diagnostic-octets fn-path-diagnostic))))))

; RFC 5537 section 3.6's last paragraph: removing every Path and Xref field
; from what was received and from what is stored leaves the same octets --
; every other header field, in order, the blank line and the body.
(defthm fn-pu-relay-article-changes-only-path-and-xref
  (equal (fn-pu-strip (fn-pu-relay-article octets identity expected) nil)
         (fn-pu-strip octets nil))
  :hints (("Goal" :in-theory (disable fn-pu-walk fn-pu-strip fn-pu-received-path
                                      fn-pu-diagnostic-octets fn-path-diagnostic
                                      fn-path-identityp fn-pu-insertablep
                                      fn-pu-expected)
           :use ((:instance fn-pu-walk-changes-only-path-and-xref
                            (x octets)
                            (id (if (fn-path-identityp identity) identity nil))
                            (dg (fn-pu-diagnostic-octets
                                 (fn-path-diagnostic
                                  (fn-pu-expected expected)
                                  (fn-pu-received-path octets))))
                            (d1 nil) (d2 nil))))))

; A second pass changes nothing: the stored Path already begins with the
; agent's identity, and no Xref is left.  So replaying or re-relaying a
; stored article is harmless, and the outbound feed and the reader see one
; rendering.
(defthm fn-pu-relay-article-is-idempotent
  (equal (fn-pu-relay-article (fn-pu-relay-article octets identity expected)
                              identity expected)
         (fn-pu-relay-article octets identity expected))
  :hints (("Goal" :in-theory (disable fn-pu-walk fn-pu-received-path
                                      fn-pu-diagnostic-octets fn-path-diagnostic
                                      fn-path-identityp fn-pu-insertablep
                                      fn-pu-expected)
           :use ((:instance fn-pu-walk-is-idempotent
                            (x octets)
                            (id (if (fn-path-identityp identity) identity nil))
                            (dg (fn-pu-diagnostic-octets
                                 (fn-path-diagnostic
                                  (fn-pu-expected expected)
                                  (fn-pu-received-path octets))))
                            (d nil)
                            (dg2 (fn-pu-diagnostic-octets
                                  (fn-path-diagnostic
                                   (fn-pu-expected expected)
                                   (fn-pu-received-path
                                    (fn-pu-relay-article octets identity expected))))))))))

; RFC 5537 section 3.7 step 7 and specs/peering.md 2.3: no Xref is stored.
(defthm fn-pu-relay-article-leaves-no-xref
  (fn-pu-xref-freep (fn-pu-relay-article octets identity expected))
  :hints (("Goal" :in-theory (disable fn-pu-walk fn-pu-xref-freep fn-pu-received-path
                                      fn-pu-diagnostic-octets fn-path-diagnostic
                                      fn-path-identityp fn-pu-insertablep
                                      fn-pu-expected)
           :use ((:instance fn-pu-walk-leaves-no-xref
                            (x octets)
                            (id (if (fn-path-identityp identity) identity nil))
                            (dg (fn-pu-diagnostic-octets
                                 (fn-path-diagnostic
                                  (fn-pu-expected expected)
                                  (fn-pu-received-path octets))))
                            (d nil))))))

; RFC 5537 section 3.6 step 7 / 3.7 step 6: every Path field of the stored
; article begins with the agent's own <path-identity> and "!".
(defthm fn-pu-relay-article-names-the-agent-in-every-path
  (implies (fn-path-identityp identity)
           (fn-pu-path-markedp (fn-pu-relay-article octets identity expected)
                               identity))
  :hints (("Goal" :in-theory (disable fn-pu-walk fn-pu-path-markedp fn-pu-received-path
                                      fn-pu-diagnostic-octets fn-path-diagnostic
                                      fn-path-identityp fn-pu-insertablep
                                      fn-pu-expected)
           :use ((:instance fn-pu-walk-marks-every-path
                            (x octets)
                            (id (if (fn-path-identityp identity) identity nil))
                            (dg (fn-pu-diagnostic-octets
                                 (fn-path-diagnostic
                                  (fn-pu-expected expected)
                                  (fn-pu-received-path octets))))
                            (d nil))))))

(verify-guards fn-pu-received-path)
(verify-guards fn-pu-relay-article)

(deftheory fn-pu-vocabulary
  '((:d fn-pu-append) (:d fn-pu-take) (:d fn-pu-drop) (:d fn-pu-wspp)
    (:d fn-pu-take-wsp) (:d fn-pu-skip-wsp) (:d fn-pu-no-crp) (:d fn-pu-prefixp)
    (:d fn-pu-downcase) (:d fn-pu-named-p) (:d fn-pu-crlf-atp) (:d fn-pu-line)
    (:d fn-pu-after-line) (:d fn-pu-has-crlfp) (:d fn-pu-crlf-endedp)
    (:d fn-pu-insertion) (:d fn-pu-markedp) (:d fn-pu-edit-path) (:d fn-pu-walk)
    (:d fn-pu-strip) (:d fn-pu-xref-freep) (:d fn-pu-path-markedp)
    (:d fn-pu-insertablep) (:d fn-pu-diagnostic-octets) (:d fn-pu-relay)
    (:d fn-pu-received-path) (:d fn-pu-expected) (:d fn-pu-relay-article)))

(in-theory (disable fn-pu-vocabulary))
