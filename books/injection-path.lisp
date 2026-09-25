;; fn: a supplied Path (D32, 2026-09-25): its grammar, where its content
;; begins in the proto-article's octets, and the insertion the injecting
;; agent makes there.
;
; RFC 5537 section 3.4.1 lets a proto-article carry Path; section 3.2.1 has
; the injecting agent prepend its own <path-identity> and "!" to the Path
; content.  books/injection.lisp decides; this book supplies three pieces:
;
;   * fn-inj-path-valuep, RFC 5536 section 3.1.5's grammar
;       path      = "Path:" SP *WSP path-list tail-entry *WSP CRLF
;       path-list = *( path-identity [FWS] [path-diagnostic] "!" )
;     read over the parser's unfolded field value, in one bounded pass that
;     splits the value at "!" and checks each segment once.  Every function
;     is linear in the value, which the header block bounds before this runs.
;   * fn-inj-path-scan, the offset in the source octets where the Path
;     content begins: the first header line that opens with "Path: " (the
;     name in any case), before the empty line that ends the header.
;   * fn-inj-splice and fn-inj-unsplice: the insertion at that offset and
;     its exact inverse (fn-inj-unsplice-of-a-splice), so the injected
;     article still names the poster's source octet for octet.
;
; The grammar is RFC 5536's, with one stated difference: the value must
; begin with its first path element, one SP after the colon (the insertion
; lands there, and "AGENT!" before extra WSP would not be a path).  A
; supplied Path with leading extra WSP is refused as malformed.

(in-package "ACL2")

(defconst *fn-inj-posted-keyword* '(112 111 115 116 101 100)) ; "posted"

; -----------------------------------------------------------------------------
; Octet classes

(defun fn-inj-take-n (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (or (not (posp n)) (atom x)) nil
    (cons (car x) (fn-inj-take-n (- n 1) (cdr x)))))

(defun fn-inj-drop-n (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (or (not (posp n)) (atom x)) x
    (fn-inj-drop-n (- n 1) (cdr x))))



(defun fn-inj-alphap (c)
  (declare (xargs :guard t))
  (and (integerp c) (or (and (<= 65 c) (<= c 90)) (and (<= 97 c) (<= c 122)))))

(defun fn-inj-digitp (c)
  (declare (xargs :guard t))
  (and (integerp c) (<= 48 c) (<= c 57)))

(defun fn-inj-alnump (c)
  (declare (xargs :guard t))
  (or (fn-inj-alphap c) (fn-inj-digitp c)))

(defun fn-inj-wspp (c)
  (declare (xargs :guard t))
  (or (equal c 32) (equal c 9)))

; alphanum / "-" / "_": path-nodot's octets, and the octet a supplied path
; content must open with.
(defun fn-inj-nodot-octetp (c)
  (declare (xargs :guard t))
  (or (fn-inj-alnump c) (equal c 45) (equal c 95)))

(defun fn-inj-all-nodotp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (fn-inj-nodot-octetp (car x)) (fn-inj-all-nodotp (cdr x)))
    t))

(defun fn-inj-all-ldhp (x)
  ; alphanum / "-"
  (declare (xargs :guard t))
  (if (consp x)
      (and (or (fn-inj-alnump (car x)) (equal (car x) 45))
           (fn-inj-all-ldhp (cdr x)))
    t))

(defun fn-inj-any-alpha-or-hyphenp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (or (fn-inj-alphap (car x)) (equal (car x) 45)
          (fn-inj-any-alpha-or-hyphenp (cdr x)))
    nil))

(defun fn-inj-last (x)
  (declare (xargs :guard t))
  (if (consp x) (if (consp (cdr x)) (fn-inj-last (cdr x)) (car x)) nil))

; -----------------------------------------------------------------------------
; Splitting at one separator octet, and trimming WSP

(defun fn-inj-rev (x acc)
  (declare (xargs :guard t))
  (if (consp x) (fn-inj-rev (cdr x) (cons (car x) acc)) acc))

(defun fn-inj-split-at (sep x cur)
  ; The segments of x separated by `sep', in order; `cur' is the current
  ; segment reversed.  One pass.
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) sep)
          (cons (fn-inj-rev cur nil) (fn-inj-split-at sep (cdr x) nil))
        (fn-inj-split-at sep (cdr x) (cons (car x) cur)))
    (list (fn-inj-rev cur nil))))

(defun fn-inj-drop-wsp (x)
  (declare (xargs :guard t))
  (if (and (consp x) (fn-inj-wspp (car x))) (fn-inj-drop-wsp (cdr x)) x))

(defun fn-inj-trim-wsp-right (x)
  ; x without its trailing WSP; x has no WSP inside a valid element, so the
  ; first WSP starts the trailing run.
  (declare (xargs :guard t))
  (if (consp x)
      (if (fn-inj-wspp (car x))
          (if (fn-inj-drop-wsp x) (cons (car x) (fn-inj-trim-wsp-right (cdr x))) nil)
        (cons (car x) (fn-inj-trim-wsp-right (cdr x))))
    nil))

; -----------------------------------------------------------------------------
; RFC 5536 section 3.1.5 elements

; path-nodot = 1*( alphanum / "-" / "_" )
(defun fn-inj-path-nodotp (x)
  (declare (xargs :guard t))
  (and (consp x) (fn-inj-all-nodotp x)))

; label = alphanum [ *( alphanum / "-" ) alphanum ]
(defun fn-inj-labelp (x)
  (declare (xargs :guard t))
  (and (consp x) (fn-inj-all-ldhp x)
       (fn-inj-alnump (car x)) (fn-inj-alnump (fn-inj-last x))))

; toplabel's three alternatives are, together, a string of alphanum and "-"
; of at least two octets that opens and closes with alphanum and holds an
; ALPHA or a "-" (so it is never all digits).
(defun fn-inj-toplabelp (x)
  (declare (xargs :guard t))
  (and (fn-inj-labelp x) (consp (cdr x)) (fn-inj-any-alpha-or-hyphenp x)))

(defun fn-inj-labelsp (xs)
  ; every element but the last is a label, the last a toplabel
  (declare (xargs :guard t))
  (if (consp xs)
      (if (consp (cdr xs))
          (and (fn-inj-labelp (car xs)) (fn-inj-labelsp (cdr xs)))
        (fn-inj-toplabelp (car xs)))
    nil))

; path-identity = ( 1*( label "." ) toplabel ) / path-nodot
(defun fn-inj-path-identityp (x)
  (declare (xargs :guard t))
  (or (fn-inj-path-nodotp x)
      (let ((parts (fn-inj-split-at 46 x nil)))
        (and (consp (cdr parts)) (fn-inj-labelsp parts)))))

(defun fn-inj-dec-octetp (x)
  ; 1 to 3 digits
  (declare (xargs :guard t))
  (and (consp x) (<= (len x) 3)
       (fn-inj-digitp (car x))
       (or (atom (cdr x))
           (and (fn-inj-digitp (cadr x))
                (or (atom (cddr x)) (fn-inj-digitp (caddr x)))))))

(defun fn-inj-all-dec-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-inj-dec-octetp (car xs)) (fn-inj-all-dec-octetsp (cdr xs)))
    t))

; IPv4address, four 1-3 digit groups (the value range is not read: this is
; a syntax check of the kind RFC 5536 asks, not an address check).
(defun fn-inj-ipv4p (x)
  (declare (xargs :guard t))
  (let ((parts (fn-inj-split-at 46 x nil)))
    (and (equal (len parts) 4) (fn-inj-all-dec-octetsp parts))))

(defun fn-inj-ipv6-octetsp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (or (fn-inj-digitp (car x))
               (and (integerp (car x))
                    (or (and (<= 65 (car x)) (<= (car x) 70))
                        (and (<= 97 (car x)) (<= (car x) 102))))
               (equal (car x) 58) (equal (car x) 46))
           (fn-inj-ipv6-octetsp (cdr x)))
    t))

(defun fn-inj-has-colonp (x)
  (declare (xargs :guard t))
  (if (consp x) (or (equal (car x) 58) (fn-inj-has-colonp (cdr x))) nil))

; IPv6address, read as HEXDIG, ":" and "." with at least one ":".  Wider
; than RFC 3986's production; it only ever follows ".MISMATCH." and the
; like, where it names a source the node does not act on.
(defun fn-inj-ipv6p (x)
  (declare (xargs :guard t))
  (and (consp x) (fn-inj-ipv6-octetsp x) (fn-inj-has-colonp x)))

(defun fn-inj-all-alphap (x)
  (declare (xargs :guard t))
  (if (consp x) (and (fn-inj-alphap (car x)) (fn-inj-all-alphap (cdr x))) t))

(defun fn-inj-downcase (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (if (and (integerp (car x)) (<= 65 (car x)) (<= (car x) 90))
                (+ 32 (car x)) (car x))
            (fn-inj-downcase (cdr x)))
    nil))

; diag-other without its leading "!": "." diag-keyword [ "." diag-identity ].
; The keyword runs to the next "."; the identity is the rest.
(defun fn-inj-diag-keyword (x)
  (declare (xargs :guard t))
  (if (and (consp x) (not (equal (car x) 46)))
      (cons (car x) (fn-inj-diag-keyword (cdr x)))
    nil))

(defun fn-inj-after-keyword (x)
  (declare (xargs :guard t))
  (if (and (consp x) (not (equal (car x) 46)))
      (fn-inj-after-keyword (cdr x))
    x))

(defun fn-inj-diag-otherp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) 46)
       (let* ((kw (fn-inj-diag-keyword (cdr x)))
              (rest (fn-inj-after-keyword (cdr x))))
         (and (consp kw) (fn-inj-all-alphap kw)
              (or (atom rest)
                  (and (equal (car rest) 46)
                       (or (fn-inj-path-identityp (cdr rest))
                           (fn-inj-ipv4p (cdr rest))
                           (fn-inj-ipv6p (cdr rest)))))))))

(defun fn-inj-diag-postedp (x)
  ; a diag-other segment whose keyword is POSTED, in any case
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) 46)
       (equal (fn-inj-downcase (fn-inj-diag-keyword (cdr x)))
              *fn-inj-posted-keyword*)))

; -----------------------------------------------------------------------------
; The path value, segment by segment
;
; Split at "!", a value is s0 ! s1 ! ... ! sn.  sn, less trailing WSP, is the
; tail-entry.  s0 .. s(n-1) are read in order with one bit of state: whether
; the previous segment was a path-identity (so a path-diagnostic may follow)
; or not (so the next must be a path-identity).  After a path-identity: an
; empty segment is diag-match ("!!"), a segment opening with "." is
; diag-other, an IPv4 address is diag-deprecated, and another path-identity
; opens the next unit.  FWS (here WSP, the value being unfolded) may trail a
; path-identity, a diag-other or a diag-deprecated.

(defun fn-inj-path-list-segmentsp (segs after-id)
  (declare (xargs :guard t))
  (if (consp segs)
      (let ((s (fn-inj-trim-wsp-right (car segs))))
        (cond ((fn-inj-path-identityp s)
               (fn-inj-path-list-segmentsp (cdr segs) t))
              ((not after-id) nil)
              ((and (atom (car segs)))
               (fn-inj-path-list-segmentsp (cdr segs) nil))
              ((or (fn-inj-diag-otherp s) (fn-inj-ipv4p s))
               (fn-inj-path-list-segmentsp (cdr segs) nil))
              (t nil)))
    t))

(defun fn-inj-but-last (x)
  (declare (xargs :guard t))
  (if (and (consp x) (consp (cdr x))) (cons (car x) (fn-inj-but-last (cdr x))) nil))

(defun fn-inj-path-valuep (value)
  (declare (xargs :guard t))
  (let ((segs (fn-inj-split-at 33 (fn-inj-drop-wsp value) nil)))
    (and (fn-inj-path-nodotp (fn-inj-trim-wsp-right (fn-inj-last segs)))
         (fn-inj-path-list-segmentsp (fn-inj-but-last segs) nil))))

(defun fn-inj-any-postedp (segs)
  (declare (xargs :guard t))
  (if (consp segs)
      (or (fn-inj-diag-postedp (fn-inj-trim-wsp-right (car segs)))
          (fn-inj-any-postedp (cdr segs)))
    nil))

; RFC 5537 section 3.4.1: a proto-article's Path SHOULD NOT carry a POSTED
; diag-keyword.  fn refuses one (local policy): it would claim an injection
; this node did not make.
(defun fn-inj-path-postedp (value)
  (declare (xargs :guard t))
  (fn-inj-any-postedp (fn-inj-split-at 33 (fn-inj-drop-wsp value) nil)))

; -----------------------------------------------------------------------------
; Where the Path content begins in the source octets

; "Path: " with the name in any case.
(defun fn-inj-path-openp (x)
  (declare (xargs :guard t))
  (let ((h (fn-inj-take-n 6 x)))
    (and (equal (len h) 6)
         (equal (fn-inj-downcase (fn-inj-take-n 4 h)) '(112 97 116 104))
         (equal (nth 4 h) 58)
         (equal (nth 5 h) 32))))

; The offset of the octet after "Path: " on the first header line that opens
; with it, or nil.  `bol' says x is at the start of a line.  A line ends at
; CR LF; an empty line (a line opening with CR) ends the header.
(defun fn-inj-path-scan (x bol)
  (declare (xargs :guard t :measure (acl2-count x)))
  (cond ((atom x) nil)
        ((and bol (fn-inj-path-openp x)) 6)
        ((and bol (equal (car x) 13)) nil)
        ((and (equal (car x) 13) (consp (cdr x)) (equal (cadr x) 10))
         (let ((r (fn-inj-path-scan (cddr x) t)))
           (if r (+ 2 r) nil)))
        (t (let ((r (fn-inj-path-scan (cdr x) nil)))
             (if r (+ 1 r) nil)))))

(defun fn-inj-path-offset (source)
  (declare (xargs :guard t))
  (fn-inj-path-scan source t))

(defun fn-inj-frontp (prefix x)
  ; x opens with the octets of `prefix'
  (declare (xargs :guard t))
  (if (consp prefix)
      (and (consp x) (equal (car x) (car prefix))
           (fn-inj-frontp (cdr prefix) (cdr x)))
    t))

; `ins' placed at offset k of x.
(defun fn-inj-splice (x k ins)
  (declare (xargs :guard t))
  (append (fn-inj-take-n k x) (append (true-list-fix ins) (fn-inj-drop-n k x))))

; The prefix octets "AGENT!" the injecting agent inserts.
(defun fn-inj-path-insert (agent)
  (declare (xargs :guard t))
  (append (true-list-fix agent) '(33)))

; The inverse: y with AGENT! removed from the start of its Path content, as
; (t . x), or nil when y has no Path line or its content does not open with
; AGENT!.
(defun fn-inj-unsplice (y agent)
  (declare (xargs :guard t))
  (let ((k (fn-inj-path-offset y)))
    (if (not k) nil
      (let ((ins (fn-inj-path-insert agent))
            (r (fn-inj-drop-n k y)))
        (if (fn-inj-frontp ins r)
            (cons t (append (fn-inj-take-n k y) (fn-inj-drop-n (len ins) r)))
          nil)))))

; -----------------------------------------------------------------------------
; The splice's inverse

(local
 (defthm fn-inj-len-of-take-n-bound
   (<= (len (fn-inj-take-n n x)) (len x))
   :rule-classes :linear))

(local
 (defthm fn-inj-path-scan-is-at-least-six
   (implies (fn-inj-path-scan x bol)
            (and (<= 6 (fn-inj-path-scan x bol))
                 (<= (fn-inj-path-scan x bol) (len x))))
   :rule-classes :linear))

(local
 (defthm fn-inj-path-scan-type
   (or (null (fn-inj-path-scan x bol))
       (natp (fn-inj-path-scan x bol)))
   :rule-classes :type-prescription))

(local
 (defthm fn-inj-take-n-of-append-take-longer
   (implies (and (natp i) (natp k) (<= i k) (<= k (len x)))
            (equal (fn-inj-take-n i (append (fn-inj-take-n k x) y))
                   (fn-inj-take-n i x)))))

(local
 (defthm fn-inj-path-openp-of-append-take
   (implies (and (natp k) (<= 6 k) (<= k (len x)))
            (equal (fn-inj-path-openp (append (fn-inj-take-n k x) y))
                   (fn-inj-path-openp x)))))

(local
 (defthm fn-inj-path-openp-has-six-octets
   (implies (fn-inj-path-openp x) (<= 6 (len x)))
   :rule-classes :linear))

(local
 (defthm fn-inj-path-openp-of-cons-append-take
   (implies (and (natp k) (<= 5 k) (<= k (len z)))
            (equal (fn-inj-path-openp (cons a (append (fn-inj-take-n k z) y)))
                   (fn-inj-path-openp (cons a z))))
   :hints (("Goal" :in-theory (disable fn-inj-take-n-of-append-take-longer)
            :use ((:instance fn-inj-take-n-of-append-take-longer
                             (i 5) (x z)))
            :expand ((fn-inj-take-n 6 (cons a (append (fn-inj-take-n k z) y)))
                     (fn-inj-take-n 6 (cons a z)))))))

(local
 (defthm fn-inj-take-n-of-a-cons-is-a-cons
   (implies (and (posp n) (consp x))
            (consp (fn-inj-take-n n x)))
   :hints (("Goal" :expand ((fn-inj-take-n n x))))))

(local
 (defthm fn-inj-append-of-a-cons-is-a-cons
   (implies (consp a) (consp (append a y)))))

(local
 (defthm fn-inj-take-n-of-cons
   (implies (and (natp k) (< 0 k))
            (equal (fn-inj-take-n k (cons a x))
                   (cons a (fn-inj-take-n (- k 1) x))))))

; The scan reads nothing at or past the offset it returns, so any octets put
; there leave the offset where it was.
(defthm fn-inj-path-scan-of-a-kept-prefix
  (implies (fn-inj-path-scan x bol)
           (equal (fn-inj-path-scan
                   (append (fn-inj-take-n (fn-inj-path-scan x bol) x) y) bol)
                  (fn-inj-path-scan x bol)))
  :hints (("Goal" :induct (fn-inj-path-scan x bol)
           :in-theory (disable fn-inj-path-openp))))

(local
 (defthm fn-inj-len-take-n
   (implies (and (natp k) (<= k (len x)))
            (equal (len (fn-inj-take-n k x)) k))))

(local
 (defthm fn-inj-drop-n-of-append-take
   (implies (and (natp k) (<= k (len x)))
            (equal (fn-inj-drop-n k (append (fn-inj-take-n k x) y)) y))))

(local
 (defthm fn-inj-take-n-of-append-take
   (implies (and (natp k) (<= k (len x)))
            (equal (fn-inj-take-n k (append (fn-inj-take-n k x) y))
                   (fn-inj-take-n k x)))))

(local
 (defthm fn-inj-frontp-of-append
   (fn-inj-frontp a (append a b))))

(local
 (defthm fn-inj-drop-n-len-of-append
   (implies (true-listp a)
            (equal (fn-inj-drop-n (len a) (append a b)) b))))

(local
 (defthm fn-inj-append-take-drop
   (equal (append (fn-inj-take-n k x) (fn-inj-drop-n k x)) x)))

(local
 (defthm fn-inj-true-list-fix-of-a-true-list
   (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-inj-path-insert-is-a-true-list
   (true-listp (fn-inj-path-insert agent))))

; KEYSTONE (the splice inverse).  Inserting AGENT! where the source's Path
; content begins, then removing it again, gives back the source octet for
; octet.
(defthm fn-inj-unsplice-of-a-splice
  (implies (fn-inj-path-offset x)
           (equal (fn-inj-unsplice
                   (fn-inj-splice x (fn-inj-path-offset x)
                                  (fn-inj-path-insert agent))
                   agent)
                  (cons t x)))
  :hints (("Goal" :in-theory (disable fn-inj-path-scan)
           :use ((:instance fn-inj-path-scan-of-a-kept-prefix
                            (bol t)
                            (y (append (fn-inj-path-insert agent)
                                       (fn-inj-drop-n (fn-inj-path-scan x t) x))))))))

(defthm fn-inj-a-splice-is-a-cons
  (implies (fn-inj-path-offset x)
           (consp (fn-inj-splice x (fn-inj-path-offset x) ins)))
  :hints (("Goal" :in-theory (disable fn-inj-path-scan)
           :cases ((consp x))
           :use ((:instance fn-inj-path-scan-is-at-least-six (bol t))
                 (:instance fn-inj-take-n-of-a-cons-is-a-cons
                            (n (fn-inj-path-scan x t)))))))

(deftheory fn-inj-path-vocabulary
  '(fn-inj-alphap fn-inj-digitp fn-inj-alnump fn-inj-wspp fn-inj-nodot-octetp
    fn-inj-rev fn-inj-all-nodotp fn-inj-all-ldhp fn-inj-any-alpha-or-hyphenp fn-inj-last
    fn-inj-split-at fn-inj-drop-wsp fn-inj-trim-wsp-right fn-inj-path-nodotp
    fn-inj-labelp fn-inj-toplabelp fn-inj-labelsp fn-inj-path-identityp
    fn-inj-dec-octetp fn-inj-all-dec-octetsp fn-inj-ipv4p fn-inj-ipv6-octetsp
    fn-inj-has-colonp fn-inj-ipv6p fn-inj-all-alphap fn-inj-downcase fn-inj-diag-keyword fn-inj-after-keyword
    fn-inj-diag-otherp fn-inj-diag-postedp fn-inj-path-list-segmentsp
    fn-inj-but-last fn-inj-path-valuep fn-inj-any-postedp fn-inj-path-postedp
    fn-inj-path-openp fn-inj-path-scan fn-inj-path-offset fn-inj-take-n
    fn-inj-drop-n fn-inj-frontp fn-inj-splice fn-inj-path-insert
    fn-inj-unsplice))

(in-theory (disable fn-inj-path-vocabulary))
