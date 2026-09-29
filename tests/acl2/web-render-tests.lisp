; Witnesses and teeth for books/web-render.lisp (lane web-native, PRF-338).
(in-package "ACL2")
(include-book "../../books/web-render-keystones")
(include-book "must-fail-checked")

(defun wrnt-octs (s)
  (declare (xargs :guard (stringp s)))
  (fn-wrq-chars-octets (coerce s 'list)))

; The host's call: the reply octets in fn-web-in, the page emitted into an
; empty fn-web-out, read back.
(defun wrnt-emit (segs in)
  (declare (xargs :guard (and (fn-wr-segsp segs) (fn-cbor-octet-listp in)
                              (fn-wr-segs-within segs (len in)))))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (with-local-stobj fn-web-out
        (mv-let (r fn-web-in fn-web-out)
          (let* ((fn-web-in (fn-octets-from-list in fn-web-in))
                 (fn-web-out (fn-octets-clear fn-web-out))
                 (fn-web-out (fn-wr-emit segs fn-web-in fn-web-out)))
            (mv (fn-octets-list fn-web-out) fn-web-in fn-web-out))
          (mv r fn-web-in)))
      r)))

; An article body with markup, an entity, quotes and a stuffed dot line.
(defconst *wrnt-in*
  (append (wrnt-octs "<script>alert(\"x\")</script> & 'q'") '(13 10)
          (wrnt-octs "..leading dot") '(13 10)))

(defconst *wrnt-segs*
  (list (fn-wm "</pre><pre class='body'>")
        (cons :d (cons 0 (len *wrnt-in*)))
        (fn-wm "</pre><nav class='keys'>")
        (fn-wr-txt (wrnt-octs "a<b"))
        (fn-wr-url (wrnt-octs "local.general&x"))))

(defconst *wrnt-page* (wrnt-emit *wrnt-segs* *wrnt-in*))

(assert-event
 (equal *wrnt-page*
        (append (wrnt-octs "</pre><pre class='body'>")
                (wrnt-octs "&lt;script&gt;alert(&quot;x&quot;)&lt;/script&gt; &amp; &#39;q&#39;") '(13 10)
                (wrnt-octs ".leading dot") '(13 10)
                (wrnt-octs "</pre><nav class='keys'>a&lt;blocal.general%26x"))))

; KEYSTONE fn-wr-emit-is-seq: reached witness (both hypotheses hold).
(assert-event (and (true-listp nil) (fn-wr-segsp *wrnt-segs*)
                   (equal *wrnt-page* (append nil (fn-wr-seq *wrnt-segs* *wrnt-in*)))))
; Teeth.  Without true-listp of the page buffer: no segments, buffer 5.
; (A stobj function applied to a non-stobj constant is stated as a
; theorem: the prover evaluates it by its definition.)
(thm (and (fn-wr-segsp nil)
          (not (true-listp 5))
          (not (equal (fn-wr-emit nil in 5) (append 5 (fn-wr-seq nil in))))))
(must-fail-checked
 (defthm wrnt-tooth-emit-needs-true-listp
   (implies (fn-wr-segsp segs)
            (equal (fn-wr-emit segs fn-web-in fn-web-out)
                   (append fn-web-out (fn-wr-seq segs fn-web-in))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-wr-emit fn-wr-seq)))))
; Without segsp: a markup segment whose octets are not a list.
(thm (and (not (fn-wr-segsp '((:m . 5))))
          (true-listp nil)
          (not (equal (fn-wr-emit '((:m . 5)) in nil)
                      (append nil (fn-wr-seq '((:m . 5)) in))))))
(must-fail-checked
 (defthm wrnt-tooth-emit-needs-segsp
   (implies (true-listp fn-web-out)
            (equal (fn-wr-emit segs fn-web-in fn-web-out)
                   (append fn-web-out (fn-wr-seq segs fn-web-in))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-wr-emit fn-wr-seq)))))

; KEYSTONE fn-wr-escape-is-safe: witness, and a MUTATION witness (labelled):
; the text unescaped is not safe text.
(assert-event (fn-wr-safe-textp (fn-wr-escape (wrnt-octs "<a href=\"x\">&amp;</a>"))))
(assert-event (not (fn-wr-safe-textp (wrnt-octs "<a href=\"x\">"))))
(assert-event (not (fn-wr-safe-textp (wrnt-octs "&ampx"))))

; fn-wr-unescape-escape: witness; tooth without true-listp.
(assert-event (equal (fn-wr-unescape (fn-wr-escape (wrnt-octs "<&\"'>"))) (wrnt-octs "<&\"'>")))
(assert-event (and (not (true-listp '(60 . 7)))
                   (not (equal (fn-wr-unescape (fn-wr-escape '(60 . 7))) '(60 . 7)))))
(must-fail-checked
 (defthm wrnt-tooth-unescape-needs-true-listp
   (equal (fn-wr-unescape (fn-wr-escape xs)) xs)
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-wr-unescape fn-wr-escape)))))

; fn-wr-pieces-okp-of-okp-segs (the model form of the keystone below): a reached page (the
; group page over a reply buffer) is accepted and its pieces are the
; vocabulary's or safe; tooth: a segment list with foreign markup.
(defconst *wrnt-group*
  (fn-wr-frame (wrnt-octs "local.general") (wrnt-octs "Friends news") :dark
               (wrnt-octs "carol") (wrnt-octs "tok")
               (fn-wr-group-main (wrnt-octs "local.general")
                                 (list (list (wrnt-octs "3") '(0 . 8) '(9 . 20) '(21 . 30)))
                                 (wrnt-octs "1"))))
(assert-event (and (fn-wr-segs-okp *wrnt-group*)
                   (fn-wr-pieces-okp (fn-wr-pieces *wrnt-group* *wrnt-in*))))

; What a friend reads on the groups and compose pages (lane
; operability-review, 2026-09-29): the groups table counts "Posts", and the
; compose page offers a way back without posting, in the outcome page's own
; words (no new markup: fn-wr-segs-okp holds as before).
(defun wrnt-chars (xs) (declare (xargs :mode :program))
  (if (consp xs) (cons (code-char (car xs)) (wrnt-chars (cdr xs))) nil))
(defun wrnt-str (xs) (declare (xargs :mode :program)) (coerce (wrnt-chars xs) 'string))
(assert-event
 (let ((groups (wrnt-emit (fn-wr-groups-main (list (list (wrnt-octs "local.general") (wrnt-octs "3") nil))) nil))
       (compose (fn-wr-compose-main (wrnt-octs "local.general") (wrnt-octs "tok") nil nil nil)))
   (and (search "<th class='num'>Posts</th>" (wrnt-str groups))
        (not (search "Arts" (wrnt-str groups)))
        (fn-wr-segs-okp compose)
        (search "'>back to the group</a>] [<a href='/'>groups</a>]</p>" (wrnt-str (wrnt-emit compose nil)))
        (search "href='/g?name=local.general'>back to the group" (wrnt-str (wrnt-emit compose nil))))))
(assert-event (and (not (fn-wr-segs-okp (list (cons :m (wrnt-octs "<script>")))))
                   (not (fn-wr-pieces-okp (fn-wr-pieces (list (cons :m (wrnt-octs "<script>"))) nil)))))
(must-fail-checked
 (defthm wrnt-tooth-pieces-need-okp
   (fn-wr-pieces-okp (fn-wr-pieces segs in))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-wr-pieces fn-wr-pieces-okp)))))

; fn-wr-seq-reads-only-its-spans: garbage past the spans changes nothing.
(assert-event (equal (fn-wr-seq *wrnt-group* (append *wrnt-in* (wrnt-octs "<garbage>")))
                     (fn-wr-seq *wrnt-group* *wrnt-in*)))
; The page contains the site's markup and the escaped spans, and the CSS
; is ASCII octets.
(assert-event (fn-cbor-octet-listp *fn-web-css*))

; KEYSTONE fn-wr-emit-writes-vocabulary-or-escaped.  Reached witness: the
; group page emitted over the reply buffer, both hypotheses holding.
(assert-event (and (true-listp nil) (fn-wr-segs-okp *wrnt-group*)
                   (equal (wrnt-emit *wrnt-group* *wrnt-in*)
                          (append nil (fn-wr-flat (fn-wr-pieces *wrnt-group* *wrnt-in*))))
                   (fn-wr-pieces-okp (fn-wr-pieces *wrnt-group* *wrnt-in*))))
; Without true-listp of the page buffer: 5 and no segments.
(thm (and (fn-wr-segs-okp nil) (not (true-listp 5))
          (not (equal (fn-wr-emit nil in 5) (append 5 (fn-wr-flat (fn-wr-pieces nil in)))))))
(must-fail-checked
 (defthm wrnt-tooth-writes-needs-true-listp
   (implies (fn-wr-segs-okp segs)
            (equal (fn-wr-emit segs fn-web-in fn-web-out)
                   (append fn-web-out (fn-wr-flat (fn-wr-pieces segs fn-web-in)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-wr-emit fn-wr-pieces fn-wr-flat)))))
; Without segs-okp: markup outside the vocabulary is written, and it is no
; vocabulary piece and no escaped text.
(assert-event (and (true-listp nil)
                   (not (fn-wr-segs-okp (list (cons :m (wrnt-octs "<script>")))))
                   (not (fn-wr-pieces-okp (fn-wr-pieces (list (cons :m (wrnt-octs "<script>"))) nil)))))
(must-fail-checked
 (defthm wrnt-tooth-writes-needs-okp
   (implies (true-listp fn-web-out)
            (fn-wr-pieces-okp (fn-wr-pieces segs fn-web-in)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-wr-pieces fn-wr-pieces-okp)))))

; KEYSTONE fn-wr-emit-reads-only-its-spans.  Reached witness: the group
; page over the reply and over the reply with garbage after it.
(defconst *wrnt-garbage* (append *wrnt-in* (wrnt-octs "<garbage>")))
(assert-event (and (fn-wr-segsp *wrnt-group*) (fn-wr-segs-within *wrnt-group* (len *wrnt-in*))
                   (equal (take (len *wrnt-in*) *wrnt-garbage*) *wrnt-in*)
                   (equal (wrnt-emit *wrnt-group* (take (len *wrnt-in*) *wrnt-garbage*))
                          (wrnt-emit *wrnt-group* *wrnt-garbage*))))
; Without segsp: a segment of no kind is written as a span, past N.
; (The buffer's reads, stated as theorems, need the slice as take/nthcdr.)
(defthm wrnt-car-nthcdr (equal (car (nthcdr i x)) (nth i x))
  :hints (("Goal" :in-theory (enable nth nthcdr))))
(defthm wrnt-cdr-nthcdr (implies (natp i) (equal (cdr (nthcdr i x)) (nthcdr (1+ i) x)))
  :hints (("Goal" :in-theory (enable nthcdr))))
(defthm wrnt-slice-take
  (implies (and (natp i) (natp n) (<= i n))
           (equal (fn-oct-slice-list i n st) (take (- n i) (nthcdr i st))))
  :hints (("Goal" :induct (fn-oct-slice-list i n st) :in-theory (enable fn-oct-slice-list))
          ("Subgoal *1/2" :expand ((take (+ n (- i)) (nthcdr i st))))))
(thm (and (not (fn-wr-segsp '((:x 0 . 3)))) (fn-wr-segs-within '((:x 0 . 3)) 0)
          (equal (take 0 '(65 66 67)) nil)
          (not (equal (fn-wr-emit '((:x 0 . 3)) nil nil)
                      (fn-wr-emit '((:x 0 . 3)) '(65 66 67) nil))))
     :hints (("Goal" :expand ((:free (x) (hide x))))))
(must-fail-checked
 (defthm wrnt-tooth-spans-need-segsp
   (implies (fn-wr-segs-within segs n)
            (equal (fn-wr-emit segs (take n fn-web-in) fn-web-out)
                   (fn-wr-emit segs fn-web-in fn-web-out)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-wr-emit fn-wr-segs-within)))))
; Without the span bound: a span past N reads what TAKE removed.
(thm (and (fn-wr-segsp '((:s 0 . 3))) (not (fn-wr-segs-within '((:s 0 . 3)) 1))
          (equal (take 1 '(65 66 67)) '(65))
          (not (equal (fn-wr-emit '((:s 0 . 3)) '(65) nil)
                      (fn-wr-emit '((:s 0 . 3)) '(65 66 67) nil))))
     :hints (("Goal" :expand ((:free (x) (hide x))))))
(must-fail-checked
 (defthm wrnt-tooth-spans-need-within
   (implies (fn-wr-segsp segs)
            (equal (fn-wr-emit segs (take n fn-web-in) fn-web-out)
                   (fn-wr-emit segs fn-web-in fn-web-out)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-wr-emit fn-wr-segsp)))))

; -----------------------------------------------------------------------------
; RFC 2047 (books/web-2047.lisp, PRF-353): the (:w) segment.

(defun wrnt-2047 (s)
  (declare (xargs :guard (stringp s)))
  (fn-w47-decode (wrnt-octs s)))

; Witnesses over the list model: B and Q, a joined pair (6.2), a word then
; text (the space kept), ISO-8859-1 to UTF-8, a charset suffix (RFC 2231).
(assert-event (equal (wrnt-2047 "=?UTF-8?B?R3LDvMOfZQ==?=") '(71 114 195 188 195 159 101)))
(assert-event (equal (wrnt-2047 "=?utf-8?q?a_=3Cb=3E?= =?utf-8?q?c?=") (wrnt-octs "a <b>c")))
(assert-event (equal (wrnt-2047 "=?utf-8?q?a?= x") (wrnt-octs "a x")))
(assert-event (equal (wrnt-2047 "=?iso-8859-1?q?caf=E9?=") '(99 97 102 195 169)))
(assert-event (equal (wrnt-2047 "Re: =?UTF-8*en?Q?x?=  tail") (wrnt-octs "Re: x  tail")))
; Shown as they are: another charset, a malformed B text, 8-bit octets
; under US-ASCII, an unterminated word, a word over 75 octets.
(assert-event (equal (wrnt-2047 "=?koi8-r?q?a?=") (wrnt-octs "=?koi8-r?q?a?=")))
(assert-event (equal (wrnt-2047 "=?utf-8?b?***?=") (wrnt-octs "=?utf-8?b?***?=")))
(assert-event (equal (wrnt-2047 "=?us-ascii?q?caf=E9?=") (wrnt-octs "=?us-ascii?q?caf=E9?=")))
(assert-event (equal (wrnt-2047 "=?utf-8?q?abc") (wrnt-octs "=?utf-8?q?abc")))
(defconst *wrnt-long-word*
  (append (wrnt-octs "=?utf-8?q?") (make-list 70 :initial-element 97) (wrnt-octs "?=")))
(assert-event (equal (fn-w47-decode *wrnt-long-word*) *wrnt-long-word*))

; KEYSTONE fn-w47-decode-without-openers-is-identity.  Positive: the
; antecedent and the conclusion on a field with "=" and "?" but no "=?".
(assert-event (let ((x (wrnt-octs "Re: a = b? (? =)")))
                (and (fn-w47-no-openersp x) (equal (fn-w47-decode x) x))))
; Hypothesis removal: a field with an opener fails the hypothesis and the
; conclusion.
(assert-event (let ((x (wrnt-octs "=?utf-8?q?a?=")))
                (and (not (fn-w47-no-openersp x)) (not (equal (fn-w47-decode x) x)))))
(must-fail-checked
 (defthm wrnt-tooth-2047-identity-needs-no-openers
   (equal (fn-w47-decode xs) xs)
   :rule-classes nil))

; KEYSTONE fn-w47-decode-octets.  Positive, and hypothesis removal: a
; non-octet field is not made octets (it has no opener, so it is shown as
; it is).
(assert-event (let ((x (wrnt-octs "=?utf-8?q?=FF?=")))
                (and (fn-cbor-octet-listp x) (fn-cbor-octet-listp (fn-w47-decode x))
                     (equal (fn-w47-decode x) '(255)))))
(assert-event (and (not (fn-cbor-octet-listp '(300)))
                   (not (fn-cbor-octet-listp (fn-w47-decode '(300))))))
(must-fail-checked
 (defthm wrnt-tooth-2047-octets-need-octets
   (fn-cbor-octet-listp (fn-w47-decode xs))
   :rule-classes nil))

; A field past *fn-w47-max* is shown as it is (fn-w47-decode-of-long):
; the same word decodes inside the bound and not past it.
(defconst *wrnt-long-field*
  (append (wrnt-octs "=?utf-8?q?a?=") (make-list *fn-w47-max* :initial-element 32)))
(assert-event (and (< *fn-w47-max* (len *wrnt-long-field*))
                   (equal (fn-w47-decode *wrnt-long-field*) *wrnt-long-field*)
                   (equal (fn-w47-decode (take 13 *wrnt-long-field*)) '(97))))

; The page: an encoded "<b>" is decoded, then escaped by the host-called
; emitter; the same span as (:s) is shown raw.  Both pieces are safe text.
(defconst *wrnt-w-in* (wrnt-octs "=?utf-8?q?=3Cb=3E_&?="))
(assert-event (equal (wrnt-emit (list (cons :w (cons 0 (len *wrnt-w-in*)))) *wrnt-w-in*)
                     (wrnt-octs "&lt;b&gt; &amp;")))
(assert-event (equal (wrnt-emit (list (cons :s (cons 0 (len *wrnt-w-in*)))) *wrnt-w-in*)
                     (wrnt-octs "=?utf-8?q?=3Cb=3E_&amp;?=")))
(assert-event (fn-wr-pieces-okp (fn-wr-pieces (list (cons :w (cons 0 (len *wrnt-w-in*))))
                                              *wrnt-w-in*)))
; The emitter's long branch (read in place) writes what the model says.
(assert-event (equal (wrnt-emit (list (cons :w (cons 0 (len *wrnt-long-field*)))) *wrnt-long-field*)
                     *wrnt-long-field*))
