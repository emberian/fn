; fn: the node's own web face, part 2 -- pages (lane web-native, PRF-338,
; WEB-005; 2026-09-28).
;
; Every page is a list of SEGMENTS, and one emitter writes a segment list
; into `fn-web-out' (books/web-request.lisp):
;
;   (:m . OCTETS)     markup the renderer wrote: a constant of this book
;   (:t . OCTETS)     text, written HTML-escaped
;   (:u . OCTETS)     a URL component, written percent-encoded, then escaped
;   (:s S . E)        text read in place from fn-web-in [S, E), escaped
;   (:d S . E)        a dot-stuffed NNTP block read in place from fn-web-in
;                     [S, E), un-stuffed (RFC 3977 3.1.1) and escaped
;   (:w S . E)        a header field (Subject, From) from fn-web-in [S, E),
;                     its RFC 2047 encoded-words decoded (books/web-2047.lisp
;                     fn-w47-decode), then escaped
;
; The article body and the overview fields are never copied into lists: a
; (:s) or (:d) segment names where they are in the reply the host placed in
; fn-web-in, and the emitter escapes them from there into the page (D27).
;
; THE ESCAPING THEOREM.  `fn-wr-emit' writes exactly `fn-wr-seq' of the
; segments (`fn-wr-emit-is-seq'), and `fn-wr-seq' is the concatenation of
; `fn-wr-pieces' (`fn-wr-seq-is-flat-pieces'), each piece either a markup
; constant from the renderer's own vocabulary *fn-wr-vocabulary* or the
; escape of some octets (`fn-wr-pieces-are-vocabulary-or-escaped', for
; every segment list `fn-wr-segs-okp' accepts; every page function's
; segments are accepted: `fn-wr-page-segs-ok' and the per-page theorems).
; An escaped piece contains no `<', `>', `"' or `'', and every `&' in it
; opens one of the five entities (`fn-wr-escape-is-safe'), and escaping
; loses nothing (`fn-wr-unescape-escape').  So the rendered octets for any
; article, overview line, group name or form value contain no unescaped
; `<', `&' or `"' outside the tags the renderer itself emits.
;
; IDENTICAL INPUT, IDENTICAL OCTETS: `fn-wr-seq' reads fn-web-in only at the
; spans its segments name (`fn-wr-seq-reads-only-its-spans'): two buffers
; that agree below the segments' highest span end give byte-identical pages.
;
; THE LOOK is the static newsreader's (site/style.css, site/build_site.py):
; Netscape gray in light, an amber terminal in dark, monospace, no scripts,
; no web fonts; *fn-web-css* is that sheet with the reader's forms added,
; served by the node as constant octets at /style.css.

(in-package "ACL2")
(include-book "web-request")
(include-book "web-2047")
(include-book "rev-onto") ; the loop twins' step (PKT-877)

; -----------------------------------------------------------------------------
; Escaping (HTML 13.1.2.4: text and quoted attribute values).

(defun fn-wr-escape-octet (o)
  (declare (xargs :guard t))
  (case o
    (38 (fn-wrq-oct "&amp;"))
    (60 (fn-wrq-oct "&lt;"))
    (62 (fn-wrq-oct "&gt;"))
    (34 (fn-wrq-oct "&quot;"))
    (39 (fn-wrq-oct "&#39;"))
    (otherwise (list o))))

(defun fn-wr-escape (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (append (fn-wr-escape-octet (car xs)) (fn-wr-escape (cdr xs)))
    nil))

; What an escaped piece is: no < > " ', and each & opens an entity.
(defconst *fn-wr-entity-tails*
  (list (fn-wrq-oct "amp;") (fn-wrq-oct "lt;") (fn-wrq-oct "gt;")
        (fn-wrq-oct "quot;") (fn-wrq-oct "#39;")))

(defun fn-wr-entity-tail (xs tails)
  ; The tail of TAILS that XS opens with, or nil.
  (declare (xargs :guard (true-list-listp tails)))
  (if (consp tails)
      (if (fn-oct-list-prefixp (car tails) xs)
          (car tails)
        (fn-wr-entity-tail xs (cdr tails)))
    nil))

(defthm fn-wr-len-drop
  (<= (len (fn-wrq-drop n xs)) (len xs))
  :rule-classes :linear)

(defun fn-wr-safe-textp (xs)
  (declare (xargs :guard t :measure (len xs)))
  (if (consp xs)
      (let ((o (car xs)))
        (cond ((member o '(60 62 34 39)) nil)
              ((equal o 38)
               (let ((tail (fn-wr-entity-tail (cdr xs) *fn-wr-entity-tails*)))
                 (and tail
                      (fn-wr-safe-textp (fn-wrq-drop (len tail) (cdr xs))))))
              (t (fn-wr-safe-textp (cdr xs)))))
    t))

(defthm fn-wr-safe-textp-append-escape-octet
  (implies (fn-wr-safe-textp ys)
           (fn-wr-safe-textp (append (fn-wr-escape-octet o) ys))))

(defthm fn-wr-escape-is-safe
  ; KEYSTONE (PRF-338): an escaped piece carries no markup.
  (fn-wr-safe-textp (fn-wr-escape xs)))

(defun fn-wr-unescape (xs)
  (declare (xargs :guard t :measure (len xs)))
  (if (consp xs)
      (if (equal (car xs) 38)
          (cond ((fn-oct-list-prefixp (fn-wrq-oct "amp;") (cdr xs))
                 (cons 38 (fn-wr-unescape (fn-wrq-drop 4 (cdr xs)))))
                ((fn-oct-list-prefixp (fn-wrq-oct "lt;") (cdr xs))
                 (cons 60 (fn-wr-unescape (fn-wrq-drop 3 (cdr xs)))))
                ((fn-oct-list-prefixp (fn-wrq-oct "gt;") (cdr xs))
                 (cons 62 (fn-wr-unescape (fn-wrq-drop 3 (cdr xs)))))
                ((fn-oct-list-prefixp (fn-wrq-oct "quot;") (cdr xs))
                 (cons 34 (fn-wr-unescape (fn-wrq-drop 5 (cdr xs)))))
                ((fn-oct-list-prefixp (fn-wrq-oct "#39;") (cdr xs))
                 (cons 39 (fn-wr-unescape (fn-wrq-drop 4 (cdr xs)))))
                (t (cons 38 (fn-wr-unescape (cdr xs)))))
        (cons (car xs) (fn-wr-unescape (cdr xs))))
    nil))

(defthm fn-wr-unescape-escape
  ; Escaping is faithful: the browser reads back exactly the octets.
  (implies (true-listp xs)
           (equal (fn-wr-unescape (fn-wr-escape xs)) xs)))

; -----------------------------------------------------------------------------
; URL components (RFC 3986 2.1, 2.3): unreserved octets as themselves, every
; other octet %XX.  The result is unreserved octets and "%" only, so its
; escape is itself; it is escaped anyway, uniformly.

(defun fn-wr-unreservedp (o)
  (declare (xargs :guard t))
  (or (fn-ot-digitp o) (fn-ot-alphap o) (member o '(45 46 95 126))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-wr-pct-encode-loop (rev acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rev)
      (fn-wr-pct-encode-loop (cdr rev)
                             (let ((o (car rev)))
                               (if (fn-wr-unreservedp o)
                                   (cons o acc)
                                 (let ((n (if (and (natp o) (< o 256)) o 0)))
                                   (list* 37
                                          (fn-ot-hex-digit-upper (floor n 16))
                                          (fn-ot-hex-digit-upper (mod n 16))
                                          acc)))))
    acc))

(defun fn-wr-pct-encode (xs)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp xs)
           (let ((o (car xs)))
             (if (fn-wr-unreservedp o)
                 (cons o (fn-wr-pct-encode (cdr xs)))
               (let ((n (if (and (natp o) (< o 256)) o 0)))
                 (list* 37 (fn-ot-hex-digit-upper (floor n 16)) (fn-ot-hex-digit-upper (mod n 16))
                        (fn-wr-pct-encode (cdr xs))))))
         nil)
       :exec (fn-wr-pct-encode-loop (fn-ag-rev-onto xs nil) nil)))

(local
 (defthm fn-wr-pct-encode-loop-of-rev-onto
   (equal (fn-wr-pct-encode-loop (fn-ag-rev-onto xs zs) nil)
          (fn-wr-pct-encode-loop zs (fn-wr-pct-encode xs)))
   :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                   :in-theory (union-theories '(fn-wr-pct-encode-loop fn-wr-pct-encode fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-wr-pct-encode-loop)

(verify-guards fn-wr-pct-encode
  :hints (("Goal" :in-theory (union-theories '(fn-wr-pct-encode fn-wr-pct-encode-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-wr-pct-encode-loop-of-rev-onto (zs nil))))))


; -----------------------------------------------------------------------------
; Un-stuffing a multi-line block (RFC 3977 3.1.1): a line that opens with
; ".." loses its first ".".  BOL says the next octet begins a line.

(defun fn-wr-unstuff (xs bol)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (and bol (equal (car xs) 46) (consp (cdr xs)) (equal (cadr xs) 46))
          (fn-wr-unstuff (cdr xs) nil)
        (cons (car xs) (fn-wr-unstuff (cdr xs) (equal (car xs) 10))))
    nil))

; -----------------------------------------------------------------------------
; Segments and their octets (the logical model).

(defun fn-wr-segp (seg)
  (declare (xargs :guard t))
  (and (consp seg)
       (case (car seg)
         ((:m :t :u) (fn-cbor-octet-listp (cdr seg)))
         ((:s :d :w) (and (consp (cdr seg)) (natp (cadr seg)) (natp (cddr seg))
                       (<= (cadr seg) (cddr seg))))
         (otherwise nil))))

(defun fn-wr-segsp (segs)
  (declare (xargs :guard t))
  (if (consp segs)
      (and (fn-wr-segp (car segs)) (fn-wr-segsp (cdr segs)))
    (null segs)))

(defun fn-wr-piece (seg in)
  ; The octets one segment stands for, over the logical buffer IN.
  (declare (xargs :guard (true-listp in)))
  (if (consp seg)
      (case (car seg)
        (:m (fn-wrq-true (cdr seg)))
        (:t (fn-wr-escape (cdr seg)))
        (:u (fn-wr-escape (fn-wr-pct-encode (cdr seg))))
        (:s (if (consp (cdr seg))
                (fn-wr-escape (take (nfix (- (nfix (cddr seg)) (nfix (cadr seg))))
                                    (nthcdr (nfix (cadr seg)) in)))
              nil))
        (:w (if (consp (cdr seg))
                (fn-wr-escape (fn-w47-decode (take (nfix (- (nfix (cddr seg)) (nfix (cadr seg))))
                                                   (nthcdr (nfix (cadr seg)) in))))
              nil))
        (:d (if (consp (cdr seg))
                (fn-wr-escape (fn-wr-unstuff (take (nfix (- (nfix (cddr seg)) (nfix (cadr seg))))
                                                   (nthcdr (nfix (cadr seg)) in))
                                             t))
              nil))
        (otherwise nil))
    nil))

(defun fn-wr-pieces (segs in)
  (declare (xargs :guard (true-listp in)))
  (if (consp segs)
      (cons (fn-wr-piece (car segs) in) (fn-wr-pieces (cdr segs) in))
    nil))

(defun fn-wr-flat (pieces)
  (declare (xargs :guard t))
  (if (consp pieces)
      (append (fn-wrq-true (car pieces)) (fn-wr-flat (cdr pieces)))
    nil))

(defun fn-wr-seq (segs in)
  (declare (xargs :guard (true-listp in)))
  (if (consp segs)
      (append (fn-wr-piece (car segs) in) (fn-wr-seq (cdr segs) in))
    nil))

(defun fn-wr-segs-within (segs n)
  ; Every span of SEGS ends at or below N.
  (declare (xargs :guard t))
  (if (consp segs)
      (and (or (not (consp (car segs)))
               (not (member (car (car segs)) '(:s :d :w)))
               (and (consp (cdr (car segs))) (natp (cddr (car segs)))
                    (<= (cddr (car segs)) (nfix n))))
           (fn-wr-segs-within (cdr segs) n))
    t))

; -----------------------------------------------------------------------------
; The emitter: segments into fn-web-out, spans read in place from fn-web-in.

(defthm fn-wr-escape-octet-octets
  (implies (fn-cbor-octetp o) (fn-cbor-octet-listp (fn-wr-escape-octet o))))

(defthm fn-wr-escape-octets
  (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (fn-wr-escape xs))))

(defthm fn-wr-pct-encode-octets
  (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (fn-wr-pct-encode xs))))

(defun fn-wr-emit-list (xs fn-web-out)
  ; escape(XS) appended.
  (declare (xargs :stobjs fn-web-out :guard (fn-cbor-octet-listp xs)))
  (if (consp xs)
      (let ((fn-web-out (fn-octets-append-list (fn-wr-escape-octet (car xs)) fn-web-out)))
        (fn-wr-emit-list (cdr xs) fn-web-out))
    fn-web-out))

(defun fn-wr-emit-span (s e fn-web-in fn-web-out)
  ; escape(in[s, e)) appended, read in place.
  (declare (xargs :stobjs (fn-web-in fn-web-out)
                  :guard (and (natp s) (natp e) (<= e (fn-octets-len fn-web-in)))
                  :measure (nfix (- e s))))
  (if (or (not (natp s)) (not (natp e)) (<= e s))
      fn-web-out
    (let ((fn-web-out (fn-octets-append-list
                       (fn-wr-escape-octet (fn-octets-get s fn-web-in)) fn-web-out)))
      (fn-wr-emit-span (1+ s) e fn-web-in fn-web-out))))

(defun fn-wr-emit-unstuffed (s e bol fn-web-in fn-web-out)
  ; escape(unstuff(in[s, e), BOL)) appended, read in place.
  (declare (xargs :stobjs (fn-web-in fn-web-out)
                  :guard (and (natp s) (natp e) (<= e (fn-octets-len fn-web-in)))
                  :measure (nfix (- e s))))
  (if (or (not (natp s)) (not (natp e)) (<= e s))
      fn-web-out
    (let ((o (fn-octets-get s fn-web-in)))
      (if (and bol (equal o 46) (< (1+ s) e) (equal (fn-octets-get (1+ s) fn-web-in) 46))
          (fn-wr-emit-unstuffed (1+ s) e nil fn-web-in fn-web-out)
        (let ((fn-web-out (fn-octets-append-list (fn-wr-escape-octet o) fn-web-out)))
          (fn-wr-emit-unstuffed (1+ s) e (equal o 10) fn-web-in fn-web-out))))))

(defthm fn-wr-slice-octets
  (implies (and (fn-cbor-octet-listp st) (natp n) (<= n (len st)))
           (fn-cbor-octet-listp (fn-oct-slice-list i n st)))
  :hints (("Goal" :induct (fn-oct-slice-list i n st) :in-theory (enable fn-oct-slice-list nth))))

(defun fn-wr-emit-decoded (s e fn-web-in fn-web-out)
  ; escape(fn-w47-decode(in[s, e))) appended.  A field longer than
  ; *fn-w47-max* is shown as it is (fn-w47-decode's own rule), read in place;
  ; a shorter one is copied into a list of at most that many octets.
  (declare (xargs :stobjs (fn-web-in fn-web-out)
                  :guard (and (natp s) (natp e) (<= s e) (<= e (fn-octets-len fn-web-in)))))
  (if (<= (- e s) *fn-w47-max*)
      (fn-wr-emit-list (fn-w47-decode (fn-oct-slice-list s e fn-web-in)) fn-web-out)
    (fn-wr-emit-span s e fn-web-in fn-web-out)))

(defthm fn-wr-segsp-car
  (implies (and (fn-wr-segsp segs) (consp segs))
           (and (consp (car segs))
                (implies (member (car (car segs)) '(:m :t :u))
                         (fn-cbor-octet-listp (cdr (car segs))))
                (implies (not (member (car (car segs)) '(:m :t :u)))
                         (and (member (car (car segs)) '(:s :d :w))
                              (consp (cdr (car segs)))
                              (natp (cadr (car segs)))
                              (natp (cddr (car segs)))
                              (<= (cadr (car segs)) (cddr (car segs)))))
                (fn-wr-segsp (cdr segs)))))

(defthm fn-wr-segs-within-car
  (implies (and (fn-wr-segs-within segs n) (natp n) (fn-wr-segsp segs) (consp segs)
                (not (member (car (car segs)) '(:m :t :u))))
           (<= (cddr (car segs)) n))
  :rule-classes :linear
  :hints (("Goal" :expand ((fn-wr-segsp segs) (fn-wr-segp (car segs))))))

(defthm fn-wr-segs-within-cdr
  (implies (fn-wr-segs-within segs n) (fn-wr-segs-within (cdr segs) n)))

(defthm fn-wr-emit-list-octets
  (implies (and (fn-cbor-octet-listp out) (fn-cbor-octet-listp xs))
           (fn-cbor-octet-listp (fn-wr-emit-list xs out))))

(in-theory (disable fn-wr-segsp fn-wr-segs-within))

(defun fn-wr-emit (segs fn-web-in fn-web-out)
  ; THE HOST-CALLED EMITTER's body (books/web-session.lisp fn-web-page-emit).
  (declare (xargs :stobjs (fn-web-in fn-web-out)
                  :guard (and (fn-wr-segsp segs)
                              (fn-wr-segs-within segs (fn-octets-len fn-web-in)))
                  :guard-hints (("Goal" :do-not-induct t))))
  (if (consp segs)
      (let* ((seg (car segs))
             (fn-web-out
              (case (car seg)
                (:m (fn-octets-append-list (cdr seg) fn-web-out))
                (:t (fn-wr-emit-list (cdr seg) fn-web-out))
                (:u (fn-wr-emit-list (fn-wr-pct-encode (cdr seg)) fn-web-out))
                (:s (fn-wr-emit-span (cadr seg) (cddr seg) fn-web-in fn-web-out))
                (:w (fn-wr-emit-decoded (cadr seg) (cddr seg) fn-web-in fn-web-out))
                (otherwise (fn-wr-emit-unstuffed (cadr seg) (cddr seg) t
                                                 fn-web-in fn-web-out)))))
        (fn-wr-emit (cdr segs) fn-web-in fn-web-out))
    fn-web-out))

; -----------------------------------------------------------------------------
; The emitter writes the model's octets.

(local
 (defthm fn-wr-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-wr-slice-open
   (implies (and (natp s) (natp e) (< s e))
            (equal (fn-oct-slice-list s e fn-octets)
                   (cons (nth s fn-octets) (fn-oct-slice-list (1+ s) e fn-octets))))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-wr-slice-empty
   (implies (or (not (natp s)) (not (natp e)) (<= e s))
            (equal (fn-oct-slice-list s e fn-octets) nil))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(defthm fn-wr-emit-list-is-append
  (implies (true-listp out)
           (equal (fn-wr-emit-list xs out) (append out (fn-wr-escape xs)))))

(defthm fn-wr-escape-is-emit-list
  ; The model's escape is what the host-reached writer appends to an empty
  ; page (the escaping keystones are about what the host runs).
  (equal (fn-wr-escape xs) (fn-wr-emit-list xs nil))
  :rule-classes nil)

(defthm fn-wr-emit-span-is-append
  (implies (true-listp fn-web-out)
           (equal (fn-wr-emit-span s e fn-web-in fn-web-out)
                  (append fn-web-out (fn-wr-escape (fn-oct-slice-list s e fn-web-in)))))
  :hints (("Goal" :induct (fn-wr-emit-span s e fn-web-in fn-web-out))))

(defthm fn-wr-emit-unstuffed-is-append
  (implies (true-listp fn-web-out)
           (equal (fn-wr-emit-unstuffed s e bol fn-web-in fn-web-out)
                  (append fn-web-out
                          (fn-wr-escape (fn-wr-unstuff (fn-oct-slice-list s e fn-web-in) bol)))))
  :hints (("Goal" :induct (fn-wr-emit-unstuffed s e bol fn-web-in fn-web-out)
           :expand ((:free (x y b) (fn-wr-unstuff (cons x y) b))
                    (fn-oct-slice-list (+ 1 s) e fn-web-in)))))

(defthm fn-wr-len-slice
  (equal (len (fn-oct-slice-list s e st))
         (if (and (natp s) (natp e) (< s e)) (- e s) 0))
  :hints (("Goal" :induct (fn-oct-slice-list s e st) :in-theory (enable fn-oct-slice-list))))

(defthm fn-wr-emit-decoded-is-append
  (implies (and (true-listp fn-web-out) (natp s) (natp e))
           (equal (fn-wr-emit-decoded s e fn-web-in fn-web-out)
                  (append fn-web-out
                          (fn-wr-escape (fn-w47-decode (fn-oct-slice-list s e fn-web-in))))))
  :hints (("Goal" :in-theory (disable fn-wr-slice-open))))

(local
 (defthm fn-wr-octet-listp-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :rule-classes (:forward-chaining :rewrite)))

(local
 (defthm fn-wr-car-nthcdr
   (equal (car (nthcdr i x)) (nth i x))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-wr-cdr-nthcdr
   (implies (natp i) (equal (cdr (nthcdr i x)) (nthcdr (1+ i) x)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-wr-slice-is-take-nthcdr
   ; Everywhere, not only within the buffer: past its end both read nil.
   (implies (and (natp i) (natp n) (<= i n))
            (equal (fn-oct-slice-list i n st) (take (- n i) (nthcdr i st))))
   :hints (("Goal" :induct (fn-oct-slice-list i n st) :in-theory (enable fn-oct-slice-list))
           ("Subgoal *1/2" :expand ((take (+ n (- i)) (nthcdr i st)))))))

(defthm fn-wr-emit-is-seq
  ; KEYSTONE (PRF-338): the octets the emitter writes into the page buffer
  ; are the model's, fn-wr-seq of the segments over the buffer's logical
  ; value.  (Where the spans lie needs no hypothesis: the guard keeps them
  ; inside the buffer, and the equality holds either way.)
  (implies (and (true-listp fn-web-out) (fn-wr-segsp segs))
           (equal (fn-wr-emit segs fn-web-in fn-web-out)
                  (append fn-web-out (fn-wr-seq segs fn-web-in))))
  :hints (("Goal" :induct (fn-wr-emit segs fn-web-in fn-web-out)
           :in-theory (e/d (fn-wr-segsp) (fn-wr-segsp-car fn-wr-segs-within-car
                                          fn-wr-emit-decoded)))))

; -----------------------------------------------------------------------------
; The pieces: the page is its pieces, flattened.

(defthm fn-wr-piece-true-listp
  (true-listp (fn-wr-piece seg in))
  :rule-classes :type-prescription)

(defthm fn-wr-seq-is-flat-pieces
  (equal (fn-wr-seq segs in) (fn-wr-flat (fn-wr-pieces segs in))))

; -----------------------------------------------------------------------------
; THE VOCABULARY: every markup constant a page may contain.  `fn-wm' refuses,
; at macro expansion, a string that is not in it; so a page's markup is
; this list's and nothing else (`fn-wr-page-segs-ok' below).  Generated from
; the (fn-wm "...") calls of this book; kept in the order they first occur.
;; BEGIN VOCABULARY
(defconst *fn-wr-vocabulary*
  (list
   "..."
   " data-theme='light'"
   " data-theme='dark'"
   "<button type='submit' name='theme' value='light' class='quiet'"
   "<button type='submit' name='theme' value='dark' class='quiet'"
   "<button type='submit' name='theme' value='auto' class='quiet'"
   " aria-pressed='true'"
   ">"
   "</button> "
   "<nav class='menu' aria-label='Main'>[<a href='/'>groups</a>] <span>"
   "</span> <form method='post' action='/signout'><input type='hidden' name='csrf' value='"
   "'><button class='quiet' type='submit'>Sign out</button></form></nav>"
   "<!doctype html><html lang='en'"
   "><head><meta charset='utf-8'><meta name='viewport' content='width=device-width, initial-scale=1'><meta name='color-scheme' content='light dark'><title>"
   " - "
   "</title><link rel='stylesheet' href='/style.css'></head><body><a class='skip' href='#main'>Skip to the page</a><div class='screen'><header class='top'><p class='bar'><a href='/'>"
   "</a> <span>news</span></p>"
   "</header><main id='main'>"
   "</main><footer><hr><form method='post' action='/theme'>Colours: "
   "</form></footer></div></body></html>"
   "<p class='note ok' role='status'>"
   "<p class='note maybe' role='status'>"
   "<p class='note no' role='alert'>"
   "</p>"
   "<h1>Sign in</h1><p class='dim'>Use the name and password you chose when you accepted your invitation.</p>"
   "<form method='post' action='/signin'><input type='hidden' name='pre' value='"
   "'><input type='hidden' name='next' value='"
   "'><label for='user'>Name</label><input type='text' id='user' name='user' value='"
   "' autocomplete='username' autocapitalize='none' spellcheck='false' required><label for='password'>Password</label><input type='password' id='password' name='password' autocomplete='current-password' required><p><button type='submit'>Sign in</button></p></form><p class='dim'>New here, with an invitation code? <a href='/redeem'>Make your account</a>.</p>"
   "<h1>Make your account</h1><p class='dim'>Type the invitation code you were given, then choose a name and a password. The code works once.</p>"
   "<form method='post' action='/redeem'><input type='hidden' name='pre' value='"
   "'><label for='code'>Invitation code</label><input type='text' id='code' name='code' value='"
   "' autocomplete='off' autocapitalize='none' spellcheck='false' required><label for='user'>Your name for signing in</label><input type='text' id='user' name='user' value='"
   "' autocomplete='username' autocapitalize='none' spellcheck='false' required><p class='dim'>Letters, digits, dots, dashes and underscores.</p><label for='password'>Password</label><input type='password' id='password' name='password' autocomplete='new-password' required><label for='again'>The same password again</label><input type='password' id='again' name='again' autocomplete='new-password' required><p><button type='submit'>Make my account</button></p></form><p class='dim'>Already have one? <a href='/signin'>Sign in</a>.</p>"
   "<tr><td class='num'>"
   "</td><td><a class='title' href='/g?name="
   "'>"
   "</a>"
   " <span class='dim'>(read only)</span>"
   "</td></tr>"
   "<h1>Groups</h1><table class='index'><thead><tr><th class='num'>Arts</th><th>Group</th></tr></thead><tbody>"
   "</tbody></table>"
   "<h1>Groups</h1><p class='dim'>There are no groups you can read here yet.</p>"
   "</td><td class='subj'><a class='title' href='/a?g="
   "&amp;n="
   "</a></td><td class='from'>"
   "</td><td class='date'>"
   "<h1>"
   "</h1><nav class='keys'>[<a href='/new?g="
   "'>post to this group</a>] [<a href='/'>all groups</a>]</nav>"
   "<table class='index'><thead><tr><th class='num'>#</th><th>Subject</th><th class='from'>From</th><th class='date'>Date</th></tr></thead><tbody>"
   "<p class='dim'>No posts here yet.</p>"
   "<p class='keys'>[<a href='/g?name="
   "&amp;before="
   "'>older posts</a>]</p>"
   "<span class='hk'>"
   ":</span> "
   "
"
   "</a>]</p><h1>"
   "</h1><pre class='headers'>"
   "</pre><pre class='body'>"
   "</pre><nav class='keys'>"
   "[<a href='/remove?g="
   "&amp;id="
   "'>Remove my post</a>] "
   "[<a href='/new?g="
   "'>post to this group</a>]</nav>"
   "<h1>Post to "
   "</h1>"
   "<form method='post' action='/post'><input type='hidden' name='csrf' value='"
   "'><input type='hidden' name='g' value='"
   "'><label for='subject'>Subject</label><input type='text' id='subject' name='subject' value='"
   "' required><label for='body'>Message</label><textarea id='body' name='body' required>"
   "</textarea><p><button type='submit'>Post</button></p></form>"
   "<h1>Remove your post?</h1><p>It will disappear from this server for everyone. Copies other servers already have may stay there.</p><form method='post' action='/remove'><input type='hidden' name='csrf' value='"
   "'><input type='hidden' name='id' value='"
   "'><p><button class='danger' type='submit'>Remove it</button> <a href='/g?name="
   "'>Keep it</a></p></form>"
   "<p class='said dim'>"
   "'>back to the group</a>] [<a href='/'>groups</a>]</p>"
   "<p class='keys'>[<a href='/'>groups</a>]</p>"))

(defun fn-wr-strings-octets (ss)
  (declare (xargs :guard (string-listp ss)))
  (if (consp ss)
      (cons (fn-wrq-chars-octets (coerce (car ss) 'list)) (fn-wr-strings-octets (cdr ss)))
    nil))

(defconst *fn-wr-vocabulary-octets* (fn-wr-strings-octets *fn-wr-vocabulary*))
;; END VOCABULARY

(defmacro fn-wm (s)
  (if (and (stringp s) (member-equal s *fn-wr-vocabulary*))
      (list 'quote (cons :m (fn-wrq-chars-octets (coerce s 'list))))
    (er hard 'fn-wm "Markup not in *fn-wr-vocabulary*: ~x0" s)))

(defmacro fn-wt (s)
  (list 'quote (cons :t (fn-wrq-chars-octets (coerce s 'list)))))

(defun fn-wr-markup-okp (segs)
  (declare (xargs :guard t))
  (if (consp segs)
      (and (or (not (consp (car segs)))
               (not (equal (car (car segs)) :m))
               (member-equal (cdr (car segs)) *fn-wr-vocabulary-octets*))
           (fn-wr-markup-okp (cdr segs)))
    t))

(defun fn-wr-segs-okp (segs)
  (declare (xargs :guard t))
  (and (fn-wr-segsp segs) (fn-wr-markup-okp segs)))

(defun fn-wr-piece-okp (piece)
  (declare (xargs :guard t))
  (or (member-equal piece *fn-wr-vocabulary-octets*)
      (fn-wr-safe-textp piece)))

(defun fn-wr-pieces-okp (pieces)
  (declare (xargs :guard t))
  (if (consp pieces)
      (and (fn-wr-piece-okp (car pieces)) (fn-wr-pieces-okp (cdr pieces)))
    t))

(local
 (defthm fn-wr-piece-okp-one
   (implies (and (fn-wr-segp seg)
                 (or (not (equal (car seg) :m))
                     (member-equal (cdr seg) *fn-wr-vocabulary-octets*)))
            (fn-wr-piece-okp (fn-wr-piece seg in)))
   :hints (("Goal" :in-theory (disable member-equal fn-wr-escape fn-wr-safe-textp
                                       fn-wr-pct-encode fn-wr-unstuff)))))

(defthm fn-wr-pieces-okp-of-okp-segs
  ; Every piece of an accepted page is the renderer's own markup or escaped
  ; text (the emitter's form below is the keystone).
  (implies (fn-wr-segs-okp segs)
           (fn-wr-pieces-okp (fn-wr-pieces segs in)))
  :hints (("Goal" :in-theory (e/d (fn-wr-segsp) (member-equal fn-wr-piece fn-wr-piece-okp)))))

; -----------------------------------------------------------------------------
; Segment builders for values.

(defun fn-wr-octets-only (xs)
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp xs) xs nil))

(defun fn-wr-txt (xs)
  ; Text from a value: the octets kept as octets.
  (declare (xargs :guard t))
  (cons :t (fn-wr-octets-only xs)))

(defun fn-wr-url (xs)
  (declare (xargs :guard t))
  (cons :u (fn-wr-octets-only xs)))

(defun fn-wr-span (span)
  ; A (S . E) span of fn-web-in as text; an empty or malformed one is nothing.
  (declare (xargs :guard t))
  (if (and (consp span) (natp (car span)) (natp (cdr span)) (< (car span) (cdr span)))
      (list (cons :s (cons (car span) (cdr span))))
    nil))

(defun fn-wr-span-or (span alt)
  (declare (xargs :guard t))
  (or (fn-wr-span span) (list alt)))

(defun fn-wr-wspan (span)
  ; A header field's span, shown RFC 2047-decoded (the (:w) segment).
  (declare (xargs :guard t))
  (if (and (consp span) (natp (car span)) (natp (cdr span)) (< (car span) (cdr span)))
      (list (cons :w (cons (car span) (cdr span))))
    nil))

(defun fn-wr-wspan-or (span alt)
  (declare (xargs :guard t))
  (or (fn-wr-wspan span) (list alt)))

; -----------------------------------------------------------------------------
; The frame every page shares.

(defun fn-wr-theme-attr (theme)
  (declare (xargs :guard t))
  (cond ((equal theme :light) (list (fn-wm " data-theme='light'")))
        ((equal theme :dark) (list (fn-wm " data-theme='dark'")))
        (t nil)))

(defun fn-wr-theme-button (value label theme)
  (declare (xargs :guard t))
  (append (case value
            (:light (list (fn-wm "<button type='submit' name='theme' value='light' class='quiet'")))
            (:dark (list (fn-wm "<button type='submit' name='theme' value='dark' class='quiet'")))
            (otherwise (list (fn-wm "<button type='submit' name='theme' value='auto' class='quiet'"))))
          (if (equal value theme) (list (fn-wm " aria-pressed='true'")) nil)
          (list (fn-wm ">") label (fn-wm "</button> "))))

(defun fn-wr-nav (user csrf)
  ; Signed in: the groups, the name, and the sign-out form.
  (declare (xargs :guard t))
  (if (consp user)
      (list (fn-wm "<nav class='menu' aria-label='Main'>[<a href='/'>groups</a>] <span>")
            (fn-wr-txt user)
            (fn-wm "</span> <form method='post' action='/signout'><input type='hidden' name='csrf' value='")
            (fn-wr-txt csrf)
            (fn-wm "'><button class='quiet' type='submit'>Sign out</button></form></nav>"))
    nil))

(defun fn-wr-frame (title site theme user csrf main)
  (declare (xargs :guard (true-listp main)))
  (append (list (fn-wm "<!doctype html><html lang='en'"))
          (fn-wr-theme-attr theme)
          (list (fn-wm "><head><meta charset='utf-8'><meta name='viewport' content='width=device-width, initial-scale=1'><meta name='color-scheme' content='light dark'><title>")
                (fn-wr-txt title) (fn-wm " - ") (fn-wr-txt site)
                (fn-wm "</title><link rel='stylesheet' href='/style.css'></head><body><a class='skip' href='#main'>Skip to the page</a><div class='screen'><header class='top'><p class='bar'><a href='/'>")
                (fn-wr-txt site)
                (fn-wm "</a> <span>news</span></p>"))
          (fn-wr-nav user csrf)
          (list (fn-wm "</header><main id='main'>"))
          main
          (list (fn-wm "</main><footer><hr><form method='post' action='/theme'>Colours: "))
          (fn-wr-theme-button :light (fn-wt "Light") theme)
          (fn-wr-theme-button :dark (fn-wt "Dark") theme)
          (fn-wr-theme-button :auto (fn-wt "Automatic") theme)
          (list (fn-wm "</form></footer></div></body></html>"))))

(defun fn-wr-note (kind message)
  (declare (xargs :guard t))
  (if (consp message)
      (list (case kind
              (:ok (fn-wm "<p class='note ok' role='status'>"))
              (:maybe (fn-wm "<p class='note maybe' role='status'>"))
              (otherwise (fn-wm "<p class='note no' role='alert'>")))
            (fn-wr-txt message)
            (fn-wm "</p>"))
    nil))

; -----------------------------------------------------------------------------
; The pages.  Each answers the MAIN segments; fn-wr-frame wraps them.

(defun fn-wr-signin-main (message pre next user)
  (declare (xargs :guard t))
  (append (list (fn-wm "<h1>Sign in</h1><p class='dim'>Use the name and password you chose when you accepted your invitation.</p>"))
          (fn-wr-note :no message)
          (list (fn-wm "<form method='post' action='/signin'><input type='hidden' name='pre' value='")
                (fn-wr-txt pre)
                (fn-wm "'><input type='hidden' name='next' value='")
                (fn-wr-txt next)
                (fn-wm "'><label for='user'>Name</label><input type='text' id='user' name='user' value='")
                (fn-wr-txt user)
                (fn-wm "' autocomplete='username' autocapitalize='none' spellcheck='false' required><label for='password'>Password</label><input type='password' id='password' name='password' autocomplete='current-password' required><p><button type='submit'>Sign in</button></p></form><p class='dim'>New here, with an invitation code? <a href='/redeem'>Make your account</a>.</p>"))))

(defun fn-wr-redeem-main (message pre code user)
  (declare (xargs :guard t))
  (append (list (fn-wm "<h1>Make your account</h1><p class='dim'>Type the invitation code you were given, then choose a name and a password. The code works once.</p>"))
          (fn-wr-note :no message)
          (list (fn-wm "<form method='post' action='/redeem'><input type='hidden' name='pre' value='")
                (fn-wr-txt pre)
                (fn-wm "'><label for='code'>Invitation code</label><input type='text' id='code' name='code' value='")
                (fn-wr-txt code)
                (fn-wm "' autocomplete='off' autocapitalize='none' spellcheck='false' required><label for='user'>Your name for signing in</label><input type='text' id='user' name='user' value='")
                (fn-wr-txt user)
                (fn-wm "' autocomplete='username' autocapitalize='none' spellcheck='false' required><p class='dim'>Letters, digits, dots, dashes and underscores.</p><label for='password'>Password</label><input type='password' id='password' name='password' autocomplete='new-password' required><label for='again'>The same password again</label><input type='password' id='again' name='again' autocomplete='new-password' required><p><button type='submit'>Make my account</button></p></form><p class='dim'>Already have one? <a href='/signin'>Sign in</a>.</p>"))))

; A group row: (NAME COUNT READ-ONLY-P), NAME and COUNT octets.
; Executes by a loop (lane depth-debt, PRF-919): its depth was the length of
; operator data (D27: no fixed cap), one control-stack frame per element.
(defun fn-wr-group-row-segments (name-text name-url count readonly rest)
  (declare (xargs :guard t))
  (append (list (fn-wm "<tr><td class='num'>") (fn-wr-txt count)
                (fn-wm "</td><td><a class='title' href='/g?name="))
          (fn-wrq-true name-url) (list (fn-wm "'>")) (fn-wrq-true name-text)
          (list (fn-wm "</a>"))
          (if readonly (list (fn-wm " <span class='dim'>(read only)</span>")) nil)
          (list (fn-wm "</td></tr>")) rest))

(defun fn-wr-group-rows-step (x rest)
  (declare (xargs :guard t))
  (fn-wr-group-row-segments (list (fn-wr-txt (fn-wrq-nth 0 x)))
                            (list (fn-wr-url (fn-wrq-nth 0 x)))
                            (fn-wrq-nth 1 x) (fn-wrq-nth 2 x) rest))

(defun fn-wr-group-rows-loop (rev acc)
  (declare (xargs :guard t))
  (if (consp rev)
      (fn-wr-group-rows-loop (cdr rev) (fn-wr-group-rows-step (car rev) acc))
    acc))

(defun fn-wr-group-rows (rows)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp rows)
           (let ((row (car rows)))
             (append (list (fn-wm "<tr><td class='num'>")
                           (fn-wr-txt (fn-wrq-nth 1 row))
                           (fn-wm "</td><td><a class='title' href='/g?name=")
                           (fn-wr-url (fn-wrq-nth 0 row))
                           (fn-wm "'>")
                           (fn-wr-txt (fn-wrq-nth 0 row))
                           (fn-wm "</a>"))
                     (if (fn-wrq-nth 2 row) (list (fn-wm " <span class='dim'>(read only)</span>")) nil)
                     (list (fn-wm "</td></tr>"))
                     (fn-wr-group-rows (cdr rows))))
         nil)
       :exec (fn-wr-group-rows-loop (fn-ag-rev-onto rows nil) nil)))

(defthm fn-wr-group-rows-loop-of-rev-onto
  (equal (fn-wr-group-rows-loop (fn-ag-rev-onto rows zs) nil)
         (fn-wr-group-rows-loop zs (fn-wr-group-rows rows)))
  :hints (("Goal" :induct (fn-ag-rev-onto rows zs)
                  :in-theory (union-theories
                              '(fn-wr-group-rows-loop fn-wr-group-rows fn-wr-group-rows-step fn-wr-group-row-segments fn-wrq-true fn-ag-rev-onto
                                binary-append car-cons cdr-cons)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(verify-guards fn-wr-group-rows
  :hints (("Goal" :use ((:instance fn-wr-group-rows-loop-of-rev-onto (zs nil)))
                  :in-theory (union-theories
                              '(fn-wr-group-rows-loop fn-wr-group-rows)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defun fn-wr-groups-main-segments (row-segs)
  (declare (xargs :guard t))
  (if (consp row-segs)
      (append (list (fn-wm "<h1>Groups</h1><table class='index'><thead><tr><th class='num'>Arts</th><th>Group</th></tr></thead><tbody>"))
              (fn-wrq-true row-segs)
              (list (fn-wm "</tbody></table>")))
    (list (fn-wm "<h1>Groups</h1><p class='dim'>There are no groups you can read here yet.</p>"))))

(defun fn-wr-groups-main (rows)
  (declare (xargs :guard t))
  (fn-wr-groups-main-segments (fn-wr-group-rows rows)))

; An overview row: (NUMBER SUBJECT FROM DATE), NUMBER octets, the others
; spans of fn-web-in (the OVER reply, books/web-session.lisp).
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-wr-over-row-segments (group number-segs number-url subject from date rest)
  (declare (xargs :guard t))
  (append (list (fn-wm "<tr><td class='num'>")) (fn-wrq-true number-segs)
          (list (fn-wm "</td><td class='subj'><a class='title' href='/a?g=")
                (fn-wr-url group) (fn-wm "&amp;n=")) (fn-wrq-true number-url)
          (list (fn-wm "'>")) (fn-wr-wspan-or subject (fn-wt "(no subject)"))
          (list (fn-wm "</a></td><td class='from'>")) (fn-wr-wspan from)
          (list (fn-wm "</td><td class='date'>")) (fn-wr-span date)
          (list (fn-wm "</td></tr>")) rest))

(defun fn-wr-over-rows-loop (group rev acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rev)
      (let ((row (car rev)))
        (fn-wr-over-rows-loop group (cdr rev)
          (fn-wr-over-row-segments group
            (list (fn-wr-txt (fn-wrq-nth 0 row))) (list (fn-wr-url (fn-wrq-nth 0 row)))
            (fn-wrq-nth 1 row) (fn-wrq-nth 2 row) (fn-wrq-nth 3 row) acc)))
    acc))

(defun fn-wr-over-rows (group rows)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp rows)
           (let ((row (car rows)))
             (append (list (fn-wm "<tr><td class='num'>")
                           (fn-wr-txt (fn-wrq-nth 0 row))
                           (fn-wm "</td><td class='subj'><a class='title' href='/a?g=")
                           (fn-wr-url group)
                           (fn-wm "&amp;n=")
                           (fn-wr-url (fn-wrq-nth 0 row))
                           (fn-wm "'>"))
                     (fn-wr-wspan-or (fn-wrq-nth 1 row) (fn-wt "(no subject)"))
                     (list (fn-wm "</a></td><td class='from'>"))
                     (fn-wr-wspan (fn-wrq-nth 2 row))
                     (list (fn-wm "</td><td class='date'>"))
                     (fn-wr-span (fn-wrq-nth 3 row))
                     (list (fn-wm "</td></tr>"))
                     (fn-wr-over-rows group (cdr rows))))
         nil)
       :exec (fn-wr-over-rows-loop group (fn-ag-rev-onto rows nil) nil)))

(local
 (defthm fn-wr-over-rows-loop-of-rev-onto
   (equal (fn-wr-over-rows-loop group (fn-ag-rev-onto rows zs) nil)
          (fn-wr-over-rows-loop group zs (fn-wr-over-rows group rows)))
   :hints (("Goal" :induct (fn-ag-rev-onto rows zs)
                   :in-theory (union-theories '(fn-wr-over-rows-loop fn-wr-over-rows fn-wr-over-row-segments fn-wrq-true fn-ag-rev-onto
                                                binary-append car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-wr-over-rows-loop)

(verify-guards fn-wr-over-rows
  :hints (("Goal" :in-theory (union-theories '(fn-wr-over-rows fn-wr-over-rows-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-wr-over-rows-loop-of-rev-onto (zs nil))))))


(defun fn-wr-group-main-segments (group row-segs older)
  ; OLDER: the number to page back from, or nil.
  (declare (xargs :guard t))
  (append (list (fn-wm "<h1>") (fn-wr-txt group)
                (fn-wm "</h1><nav class='keys'>[<a href='/new?g=") (fn-wr-url group)
                (fn-wm "'>post to this group</a>] [<a href='/'>all groups</a>]</nav>"))
          (if (consp row-segs)
              (append (list (fn-wm "<table class='index'><thead><tr><th class='num'>#</th><th>Subject</th><th class='from'>From</th><th class='date'>Date</th></tr></thead><tbody>"))
                      (fn-wrq-true row-segs)
                      (list (fn-wm "</tbody></table>")))
            (list (fn-wm "<p class='dim'>No posts here yet.</p>")))
          (if (consp older)
              (list (fn-wm "<p class='keys'>[<a href='/g?name=") (fn-wr-url group)
                    (fn-wm "&amp;before=") (fn-wr-url older) (fn-wm "'>older posts</a>]</p>"))
            nil)))

(defun fn-wr-group-main (group rows older)
  (declare (xargs :guard t))
  (fn-wr-group-main-segments group (fn-wr-over-rows group rows) older))

(defun fn-wr-header-line (label span)
  (declare (xargs :guard t))
  (if (fn-wr-span span)
      (append (list (fn-wm "<span class='hk'>") label (fn-wm ":</span> "))
              (fn-wr-span span)
              (list (fn-wm "
")))
    nil))

(defun fn-wr-wheader-line (label span)
  ; The same line, the value RFC 2047-decoded (From).
  (declare (xargs :guard t))
  (if (fn-wr-wspan span)
      (append (list (fn-wm "<span class='hk'>") label (fn-wm ":</span> "))
              (fn-wr-wspan span)
              (list (fn-wm "
")))
    nil))

; FIELDS: (SUBJECT FROM DATE NEWSGROUPS MESSAGE-ID) spans; BODY a span of
; the dot-stuffed body; OWN whether the page offers "Remove my post" (the
; node decides whether the removal withdraws anything); MSGID octets.
(defun fn-wr-article-main-segments (group fields body own msgid-segs)
  (declare (xargs :guard t))
  (append (list (fn-wm "<p class='keys'>[<a href='/g?name=") (fn-wr-url group) (fn-wm "'>")
                (fn-wr-txt group) (fn-wm "</a>]</p><h1>"))
          (fn-wr-wspan-or (fn-wrq-nth 0 fields) (fn-wt "(no subject)"))
          (list (fn-wm "</h1><pre class='headers'>"))
          (fn-wr-wheader-line (fn-wt "From") (fn-wrq-nth 1 fields))
          (fn-wr-header-line (fn-wt "Date") (fn-wrq-nth 2 fields))
          (fn-wr-header-line (fn-wt "Newsgroups") (fn-wrq-nth 3 fields))
          (fn-wr-header-line (fn-wt "Message-ID") (fn-wrq-nth 4 fields))
          (list (fn-wm "</pre><pre class='body'>"))
          (if (and (consp body) (natp (car body)) (natp (cdr body)) (<= (car body) (cdr body)))
              (list (cons :d (cons (car body) (cdr body))))
            nil)
          (list (fn-wm "</pre><nav class='keys'>"))
          (if own
              (append (list (fn-wm "[<a href='/remove?g=") (fn-wr-url group) (fn-wm "&amp;id="))
                      (fn-wrq-true msgid-segs) (list (fn-wm "'>Remove my post</a>] ")))
            nil)
          (list (fn-wm "[<a href='/new?g=") (fn-wr-url group)
                (fn-wm "'>post to this group</a>]</nav>"))))

(defun fn-wr-article-main (group fields body own msgid)
  (declare (xargs :guard t))
  (fn-wr-article-main-segments group fields body own (list (fn-wr-url msgid))))

(defun fn-wr-compose-main (group csrf message subject body)
  (declare (xargs :guard t))
  (append (list (fn-wm "<h1>Post to ") (fn-wr-txt group) (fn-wm "</h1>"))
          (fn-wr-note :no message)
          (list (fn-wm "<form method='post' action='/post'><input type='hidden' name='csrf' value='")
                (fn-wr-txt csrf)
                (fn-wm "'><input type='hidden' name='g' value='")
                (fn-wr-txt group)
                (fn-wm "'><label for='subject'>Subject</label><input type='text' id='subject' name='subject' value='")
                (fn-wr-txt subject)
                (fn-wm "' required><label for='body'>Message</label><textarea id='body' name='body' required>")
                (fn-wr-txt body)
                (fn-wm "</textarea><p><button type='submit'>Post</button></p></form>"))))

(defun fn-wr-remove-main (group csrf msgid)
  (declare (xargs :guard t))
  (list (fn-wm "<h1>Remove your post?</h1><p>It will disappear from this server for everyone. Copies other servers already have may stay there.</p><form method='post' action='/remove'><input type='hidden' name='csrf' value='")
        (fn-wr-txt csrf)
        (fn-wm "'><input type='hidden' name='id' value='")
        (fn-wr-txt msgid)
        (fn-wm "'><input type='hidden' name='g' value='")
        (fn-wr-txt group)
        (fn-wm "'><p><button class='danger' type='submit'>Remove it</button> <a href='/g?name=")
        (fn-wr-url group)
        (fn-wm "'>Keep it</a></p></form>")))

; An outcome: KIND :ok, :maybe or :no; TITLE and MESSAGE text, DETAIL the
; node's own line (or nil); BACK the group to return to (or nil: the groups).
(defun fn-wr-outcome-main-segments (kind title message detail-segs back)
  (declare (xargs :guard t))
  (append (list (fn-wm "<h1>") (fn-wr-txt title) (fn-wm "</h1>"))
          (fn-wr-note kind message)
          (if (consp detail-segs)
              (append (list (fn-wm "<p class='said dim'>")) (fn-wrq-true detail-segs) (list (fn-wm "</p>")))
            nil)
          (if (consp back)
              (list (fn-wm "<p class='keys'>[<a href='/g?name=") (fn-wr-url back)
                    (fn-wm "'>back to the group</a>] [<a href='/'>groups</a>]</p>"))
            (list (fn-wm "<p class='keys'>[<a href='/'>groups</a>]</p>")))))

(defun fn-wr-outcome-main (kind title message detail back)
  (declare (xargs :guard t))
  (fn-wr-outcome-main-segments kind title message (and (consp detail) (list (fn-wr-txt detail))) back))

; -----------------------------------------------------------------------------
; Every page's segments are accepted (fn-wr-page-segs-ok): the markup is the
; vocabulary's, every span well formed.

(defthm fn-wr-segs-okp-append
  (implies (true-listp a)
           (equal (fn-wr-segs-okp (append a b))
                  (and (fn-wr-segs-okp a) (fn-wr-segs-okp b))))
  :hints (("Goal" :in-theory (enable fn-wr-segsp))))

(defthm fn-wr-segs-okp-cons
  (equal (fn-wr-segs-okp (cons x y))
         (and (fn-wr-segp x)
              (or (not (consp x)) (not (equal (car x) :m))
                  (member-equal (cdr x) *fn-wr-vocabulary-octets*))
              (fn-wr-segs-okp y)))
  :hints (("Goal" :in-theory (enable fn-wr-segsp))))

(defthm fn-wr-segs-okp-nil (fn-wr-segs-okp nil))

(in-theory (disable fn-wr-segs-okp))

(defthm fn-wr-segp-txt (fn-wr-segp (fn-wr-txt x)))
(defthm fn-wr-segp-url (fn-wr-segp (fn-wr-url x)))
(defthm fn-wr-car-txt (equal (car (fn-wr-txt x)) :t))
(defthm fn-wr-car-url (equal (car (fn-wr-url x)) :u))
(defthm fn-wr-segs-okp-span (fn-wr-segs-okp (fn-wr-span span))
  :hints (("Goal" :in-theory (enable fn-wr-segs-okp fn-wr-segsp))))
(defthm fn-wr-true-listp-span (true-listp (fn-wr-span span)))
(defthm fn-wr-segs-okp-span-or
  (implies (fn-wr-segs-okp (list alt)) (fn-wr-segs-okp (fn-wr-span-or span alt))))
(defthm fn-wr-true-listp-span-or (true-listp (fn-wr-span-or span alt)))
(defthm fn-wr-segs-okp-wspan (fn-wr-segs-okp (fn-wr-wspan span))
  :hints (("Goal" :in-theory (enable fn-wr-segs-okp fn-wr-segsp))))
(defthm fn-wr-true-listp-wspan (true-listp (fn-wr-wspan span)))
(defthm fn-wr-segs-okp-wspan-or
  (implies (fn-wr-segs-okp (list alt)) (fn-wr-segs-okp (fn-wr-wspan-or span alt))))
(defthm fn-wr-true-listp-wspan-or (true-listp (fn-wr-wspan-or span alt)))

(in-theory (disable fn-wr-txt fn-wr-url fn-wr-span fn-wr-span-or fn-wr-wspan fn-wr-wspan-or))

(defthm fn-wr-theme-attr-ok (fn-wr-segs-okp (fn-wr-theme-attr theme)))
(defthm fn-wr-theme-button-ok
  (implies (fn-wr-segs-okp (list label)) (fn-wr-segs-okp (fn-wr-theme-button value label theme))))
(defthm fn-wr-nav-ok (fn-wr-segs-okp (fn-wr-nav user csrf)))
(defthm fn-wr-note-ok (fn-wr-segs-okp (fn-wr-note kind message)))
(defthm fn-wr-true-listp-misc
  (and (true-listp (fn-wr-theme-attr theme)) (true-listp (fn-wr-theme-button v l theme))
       (true-listp (fn-wr-nav user csrf)) (true-listp (fn-wr-note kind message))))
(in-theory (disable fn-wr-theme-attr fn-wr-theme-button fn-wr-nav fn-wr-note))

(defthm fn-wr-frame-ok
  (implies (and (true-listp main) (fn-wr-segs-okp main))
           (fn-wr-segs-okp (fn-wr-frame title site theme user csrf main))))

(defthm fn-wr-group-rows-ok
  (and (true-listp (fn-wr-group-rows rows)) (fn-wr-segs-okp (fn-wr-group-rows rows))))
(defthm fn-wr-over-rows-ok
  (and (true-listp (fn-wr-over-rows group rows)) (fn-wr-segs-okp (fn-wr-over-rows group rows))))
(defthm fn-wr-header-line-ok
  (implies (fn-wr-segs-okp (list label))
           (and (true-listp (fn-wr-header-line label span))
                (fn-wr-segs-okp (fn-wr-header-line label span)))))

(defthm fn-wr-wheader-line-ok
  (implies (fn-wr-segs-okp (list label))
           (and (true-listp (fn-wr-wheader-line label span))
                (fn-wr-segs-okp (fn-wr-wheader-line label span)))))

(defthm fn-wr-page-segs-ok
  ; Every page main is accepted, and so is every framed page.
  (and (fn-wr-segs-okp (fn-wr-signin-main message pre next user))
       (fn-wr-segs-okp (fn-wr-redeem-main message pre code user))
       (fn-wr-segs-okp (fn-wr-groups-main rows))
       (fn-wr-segs-okp (fn-wr-group-main group rows older))
       (fn-wr-segs-okp (fn-wr-article-main group fields body own msgid))
       (fn-wr-segs-okp (fn-wr-compose-main group csrf message subject body))
       (fn-wr-segs-okp (fn-wr-remove-main group csrf msgid))
       (fn-wr-segs-okp (fn-wr-outcome-main kind title message detail back))
       (true-listp (fn-wr-signin-main message pre next user))
       (true-listp (fn-wr-redeem-main message pre code user))
       (true-listp (fn-wr-groups-main rows))
       (true-listp (fn-wr-group-main group rows older))
       (true-listp (fn-wr-article-main group fields body own msgid))
       (true-listp (fn-wr-compose-main group csrf message subject body))
       (true-listp (fn-wr-remove-main group csrf msgid))
       (true-listp (fn-wr-outcome-main kind title message detail back))))

; -----------------------------------------------------------------------------
; Identical input, identical octets: a page reads the buffer only at its
; spans.

(local
 (defun fn-wr-ind-sn (s n in)
   (if (or (zp s) (zp n) (atom in))
       (list s n in)
     (fn-wr-ind-sn (1- s) (1- n) (cdr in)))))

(local
 (defthm fn-wr-nthcdr-take
   (implies (and (natp s) (natp n) (<= s n))
            (equal (nthcdr s (take n in)) (take (- n s) (nthcdr s in))))
   :hints (("Goal" :induct (fn-wr-ind-sn s n in) :in-theory (enable take nthcdr)))))

(local
 (defun fn-wr-ind-kj (k j x)
   (if (or (zp k) (zp j))
       (list k j x)
     (fn-wr-ind-kj (1- k) (1- j) (cdr x)))))

(local
 (defthm fn-wr-take-take
   (implies (and (natp k) (natp j) (<= k j))
            (equal (take k (take j x)) (take k x)))
   :hints (("Goal" :induct (fn-wr-ind-kj k j x) :in-theory (enable take)))))

(local
 (defthm fn-wr-take-nthcdr-take
   (implies (and (natp s) (natp k) (natp n) (<= (+ s k) n))
            (equal (take k (nthcdr s (take n in)))
                   (take k (nthcdr s in))))))

(defthm fn-wr-seq-reads-only-its-spans-model
  (implies (and (fn-wr-segsp segs) (natp n) (fn-wr-segs-within segs n) (<= n (len in)))
           (equal (fn-wr-seq segs (take n in)) (fn-wr-seq segs in)))
  :hints (("Goal" :in-theory (e/d (fn-wr-segsp fn-wr-segs-within)
                                  (fn-wr-seq-is-flat-pieces fn-wr-nthcdr-take)))))

; -----------------------------------------------------------------------------
; The style sheet, served at /style.css as these octets (ASCII).
(defconst *fn-web-css-text* "/* fn's web face: the newsreader screen of the static site (site/style.css).
   Light is the Netscape-era gray page, dark an amber terminal.
   No scripts, no web fonts, nothing from another site. */
:root{--bg:#c0c0c0;--fg:#000000;--dim:#404040;--link:#0000ee;--visited:#551a8b;--bar-bg:#000080;--bar-fg:#ffffff;--rule:#808080;--rule-hi:#ffffff;--cmd-bg:#ffffff;--ok:#005000;--no:#8b0000;--maybe:#6a4b00;--glow:none;color-scheme:light}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]){--bg:#0a0700;--fg:#ffb000;--dim:#b07a00;--link:#ffcc4d;--visited:#d9a030;--bar-bg:#ffb000;--bar-fg:#0a0700;--rule:#6b4a00;--rule-hi:#6b4a00;--cmd-bg:#140e00;--ok:#ffcc4d;--no:#ff7a4d;--maybe:#ffe39a;--glow:0 0 2px rgba(255,176,0,0.45);color-scheme:dark}}
:root[data-theme=dark]{--bg:#0a0700;--fg:#ffb000;--dim:#b07a00;--link:#ffcc4d;--visited:#d9a030;--bar-bg:#ffb000;--bar-fg:#0a0700;--rule:#6b4a00;--rule-hi:#6b4a00;--cmd-bg:#140e00;--ok:#ffcc4d;--no:#ff7a4d;--maybe:#ffe39a;--glow:0 0 2px rgba(255,176,0,0.45);color-scheme:dark}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%;text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--fg);font-family:ui-monospace,\"SF Mono\",Menlo,Monaco,Consolas,\"DejaVu Sans Mono\",\"Liberation Mono\",\"Courier New\",monospace;font-size:15px;line-height:1.35;text-shadow:var(--glow)}
.screen{max-width:82ch;margin:0 auto;padding:12px 16px 24px}
a{color:var(--link)}a:visited{color:var(--visited)}
a:focus-visible,button:focus-visible,input:focus-visible,textarea:focus-visible{outline:2px dotted currentColor;outline-offset:1px}
.skip{position:absolute;left:-999px}.skip:focus{left:8px;top:8px;background:var(--cmd-bg);padding:4px}
hr{border:0;border-top:1px solid var(--rule);border-bottom:1px solid var(--rule-hi);margin:12px 0}
h1{font-size:1em;margin:12px 0 4px;overflow-wrap:anywhere}
pre,code{font:inherit}
.bar{margin:0;padding:2px 1ch;background:var(--bar-bg);color:var(--bar-fg);display:flex;justify-content:space-between;gap:2ch;flex-wrap:wrap;text-shadow:none;font-weight:bold}
.bar a,.bar a:visited{color:inherit;text-decoration:none}
.menu{margin:4px 0 0;display:flex;flex-wrap:wrap;gap:0 1ch;align-items:baseline}
.menu form{display:inline}
.dim{color:var(--dim)}
.headers{margin:0 0 1.35em;white-space:pre-wrap;overflow-wrap:anywhere}
.hk{font-weight:bold}
pre.body{margin:0 0 1.35em;white-space:pre-wrap;overflow-wrap:anywhere}
.keys{margin-top:1em;word-spacing:0.5ch}
table.index{border-collapse:collapse;width:100%;margin-top:8px;table-layout:fixed}
table.index th{text-align:left;background:var(--bar-bg);color:var(--bar-fg);text-shadow:none;padding:0 1ch;font-weight:bold}
table.index td{padding:1px 1ch;vertical-align:top;overflow-wrap:anywhere}
table.index .num{text-align:right;width:7ch}
table.index .subj{white-space:pre-wrap}
table.index .from{width:22ch}
table.index .date{width:18ch}
label{display:block;font-weight:bold;margin:10px 0 2px}
input[type=text],input[type=password],textarea{width:100%;font:inherit;color:var(--fg);background:var(--cmd-bg);border:2px inset var(--rule);padding:4px}
textarea{min-height:14em;resize:vertical}
button{font:inherit;color:var(--fg);background:var(--bg);border:2px outset var(--rule-hi);padding:2px 1.5ch;cursor:pointer}
button:active{border-style:inset}
button.quiet{border-width:1px}
button[aria-pressed=true]{font-weight:bold;border-style:inset}
.note{border:1px solid var(--rule);padding:6px 1ch;margin:10px 0;background:var(--cmd-bg)}
.note.ok{color:var(--ok)}.note.no{color:var(--no)}.note.maybe{color:var(--maybe)}
.said{overflow-wrap:anywhere}
footer{margin-top:24px}footer p{margin:0 0 4px}footer form{display:inline}
.status{font-weight:bold}
@media (max-width:640px){body{font-size:13px}.screen{padding:8px 16px 16px}table.index .date{display:none}table.index .from{width:12ch}}
")

(defconst *fn-web-css* (fn-wrq-chars-octets (coerce *fn-web-css-text* 'list)))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-wr-pct-encode)))
