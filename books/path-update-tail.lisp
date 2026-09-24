; fn: the received Path survives as the tail of the stored Path (RFC 5537
; sections 3.2.1, 3.6 step 7 and 3.7 step 6).
;
; books/path-update.lisp proves four article-level properties of the relay
; walk: nothing but Path and Xref changes, a second pass changes nothing, no
; Xref remains, and every Path field begins with the agent's identity.  None
; of them says what FOLLOWS the identity.  A walk that replaced the received
; Path by `<identity>!!' alone would satisfy all four.  RFC 5537 section
; 3.2.1 says the update PREPENDS: the agent's identity, "!", the diagnostic
; and "!" go in front of the received content, which is kept.  This book
; states that half.
;
; `fn-pu-path-contents' reads, in order, the content of each Path field line
; of the header block -- the octets after `Path:' and its whitespace, up to
; and including the line's CRLF -- with exactly the line classification the
; walk and `fn-pu-path-markedp' use.  The keystone: the contents of the
; stored article are the received contents, each with the insertion
; prepended, except a line that already begins with `<identity>!', which the
; walk leaves alone (that is what makes it idempotent).  Covered scope: the
; first physical line of each Path field; a folded Path's continuation lines
; are copied by the walk and are not read here.
;
; The walk's re-read lemmas are local to books/path-update.lisp; the ones
; this proof needs are restated below, locally, so that path-update (under
; the whole tree) keeps its certificate.

(in-package "ACL2")
(include-book "path-update")

(local (in-theory (enable fn-pu-vocabulary)))

; -----------------------------------------------------------------------------
; The reading

(defun fn-pu-path-content (line)
  (declare (xargs :guard t))
  (fn-pu-skip-wsp (fn-pu-drop 5 line)))

(defun fn-pu-path-contents (x)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (atom x)
      nil
    (let ((line (fn-pu-line x)))
      (cond ((equal line '(13 10)) nil)
            ((and (not (fn-pu-wspp (car line)))
                  (not (fn-pu-named-p line *fn-pu-xref-colon*))
                  (fn-pu-named-p line *fn-pu-path-colon*))
             (cons (fn-pu-path-content line)
                   (fn-pu-path-contents (fn-pu-after-line x))))
            (t (fn-pu-path-contents (fn-pu-after-line x)))))))

; What the update does to one received content: prepend `<id>!<dg>!', unless
; the content already begins with `<id>!'.
(defun fn-pu-prepend-path (content id dg)
  (declare (xargs :guard t))
  (if (fn-pu-prefixp (fn-pu-append id (list 33)) content)
      content
    (fn-pu-append (fn-pu-insertion id dg) content)))

(defun fn-pu-prepend-paths (contents id dg)
  (declare (xargs :guard t))
  (if (consp contents)
      (cons (fn-pu-prepend-path (car contents) id dg)
            (fn-pu-prepend-paths (cdr contents) id dg))
    nil))

; -----------------------------------------------------------------------------
; Restated from books/path-update.lisp (local there)

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

; -----------------------------------------------------------------------------
; One line

(local
 (defthm fn-pu-len-of-path-colon-take
   (implies (fn-pu-named-p line *fn-pu-path-colon*)
            (equal (len (fn-pu-take 5 line)) 5))))

; The edit on one Path line prepends the insertion to its content, or leaves
; a content that already begins with `<id>!'.
(local
 (defthm fn-pu-path-content-of-edit-path
   (implies (and (fn-pu-named-p line *fn-pu-path-colon*)
                 (fn-pu-insertablep id dg)
                 (consp id))
            (equal (fn-pu-path-content (fn-pu-edit-path line id dg))
                   (fn-pu-prepend-path (fn-pu-path-content line) id dg)))
   :hints (("Goal" :in-theory (e/d (fn-pu-insertion) (fn-pu-named-p))))))

; -----------------------------------------------------------------------------
; The walk, a line at a time

(local
 (defthm fn-pu-path-contents-of-a-line-piece
   (implies (and (consp x)
                 (or (fn-pu-has-crlfp x) (null z))
                 (not (equal (fn-pu-line x) '(13 10))))
            (equal (fn-pu-path-contents (fn-pu-append (fn-pu-line x) z))
                   (if (and (not (fn-pu-wspp (car (fn-pu-line x))))
                            (not (fn-pu-named-p (fn-pu-line x) *fn-pu-xref-colon*))
                            (fn-pu-named-p (fn-pu-line x) *fn-pu-path-colon*))
                       (cons (fn-pu-path-content (fn-pu-line x))
                             (fn-pu-path-contents z))
                     (fn-pu-path-contents z))))
   :hints (("Goal" :expand ((fn-pu-path-contents (fn-pu-append (fn-pu-line x) z)))
            :do-not-induct t
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep fn-pu-path-content)))))

(local
 (defthm fn-pu-path-contents-of-an-edited-piece
   (implies (and (consp x)
                 (fn-pu-named-p (fn-pu-line x) *fn-pu-path-colon*)
                 (not (fn-pu-named-p (fn-pu-line x) *fn-pu-xref-colon*))
                 (fn-pu-insertablep id dg)
                 (true-listp id)
                 (or (fn-pu-has-crlfp x) (null z)))
            (equal (fn-pu-path-contents
                    (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z))
                   (cons (fn-pu-path-content (fn-pu-edit-path (fn-pu-line x) id dg))
                         (fn-pu-path-contents z))))
   :hints (("Goal" :expand ((fn-pu-path-contents
                             (fn-pu-append (fn-pu-edit-path (fn-pu-line x) id dg) z)))
            :do-not-induct t
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep fn-pu-path-content)))))

(local
 (defthm fn-pu-walk-prepends-to-every-path
   (implies (and (fn-pu-insertablep id dg)
                 (consp id) (true-listp id))
            (equal (fn-pu-path-contents (fn-pu-walk x id dg d))
                   (fn-pu-prepend-paths (fn-pu-path-contents x) id dg)))
   :hints (("Goal" :induct (fn-pu-walk x id dg d)
            :in-theory (disable fn-pu-line fn-pu-after-line fn-pu-named-p
                                fn-pu-edit-path fn-pu-insertablep
                                fn-pu-path-content fn-pu-prepend-path))
           ("Subgoal *1/7" :cases ((fn-pu-has-crlfp x)))
           ("Subgoal *1/6" :cases ((fn-pu-has-crlfp x)))
           ("Subgoal *1/4" :cases ((fn-pu-has-crlfp x))))))

; -----------------------------------------------------------------------------
; KEYSTONE.  RFC 5537 section 3.2.1: the stored article's Path contents are
; the received ones, each with `<identity>!<diagnostic>!' prepended (a
; content that already begins with `<identity>!' is kept as it is).  With
; fn-pu-relay-article-names-the-agent-in-every-path this is the whole update:
; the head is this agent, and the tail is exactly what arrived.
(defthm fn-pu-relay-article-keeps-the-received-path-tail
  (implies (fn-path-identityp identity)
           (equal (fn-pu-path-contents
                   (fn-pu-relay-article octets identity expected))
                  (fn-pu-prepend-paths
                   (fn-pu-path-contents octets)
                   identity
                   (fn-pu-diagnostic-octets
                    (fn-path-diagnostic (fn-pu-expected expected)
                                        (fn-pu-received-path octets))))))
  :hints (("Goal" :in-theory (disable fn-pu-walk fn-pu-path-contents fn-pu-walk-prepends-to-every-path
                                      fn-pu-prepend-paths fn-pu-received-path
                                      fn-pu-diagnostic-octets fn-path-diagnostic
                                      fn-path-identityp fn-pu-insertablep
                                      fn-pu-expected)
           :use ((:instance fn-pu-walk-prepends-to-every-path
                            (x octets)
                            (id identity)
                            (dg (fn-pu-diagnostic-octets
                                 (fn-path-diagnostic
                                  (fn-pu-expected expected)
                                  (fn-pu-received-path octets))))
                            (d nil))))))

(in-theory (disable fn-pu-path-content fn-pu-path-contents
                    fn-pu-prepend-path fn-pu-prepend-paths))
