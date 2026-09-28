; Witnesses and teeth for books/web-render.lisp (lane web-native, PRF-338).
(in-package "ACL2")
(include-book "../../books/web-render")
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

; KEYSTONE fn-wr-pieces-are-vocabulary-or-escaped: a reached page (the
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
