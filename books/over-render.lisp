;; over-render.lisp -- OVER's quantum rendered as octets into one lease (Builder O, row O1,
;; landing 1, 2026-10-10).  Prefix `fn-ovr-'.
;;
;; The served OVER/XOVER cursor (books/over-window.lisp fn-ovw-step) builds a quantum's NOV
;; lines as octet lists.  Here the quantum is written octet by octet into one lease, an
;; abstract stobj congruent to `fn-octets' of capacity CAP (contract v2.1's pool buffer;
;; the host's lease is Builder A's), from the row's overview column: no octet list is
;; built on the column path (the payload-parse arm, for a row whose column is undecided
;; or a node without an Xref server name, appends the reference line, an octet list).
;;
;; KEYSTONES
;;   KO1  fn-ovr-put-probe-is-the-served-octets  one number's octets are fn-ovw-step's
;;   KO1b fn-ovr-probe-len-is-the-length         the length the fit test reads is written
;;   KO2  fn-ovr-quantum-is-the-step             a quantum is fn-ovw-step's window of N
;;   KO3  fn-ovr-quantum-within-the-lease        never more than CAP
;;   KO4  fn-ovr-quantum-window-at-most-w        never more than W numbers
;;   KO5  fn-ovr-quantum-is-the-largest-that-fits
;;   KO6  fn-ovr-run-is-the-windowed-reply       the quanta are the windowed reply
;;   KO7  fn-ovr-run-progresses                  every probe within L, CAP >= L + framing
;; The line bound L from the article's own header is books/over-render-bound.lisp's.

(in-package "ACL2")
(include-book "over-window")
(include-book "def-span-scan")
(local (include-book "arithmetic-5/top" :dir :system))

(def-buffer fn-ovr-lease :view t)

; ---------------------------------------------------------------------------
; The reference: one probe of the window, the octets fn-ovw-step writes for number J
; (zero or one stuffed, CRLF-terminated NOV line).
(defun fn-ovr-probe-octets (group j server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (natp j) (natp v)) :verify-guards nil))
  (fn-nntp-stuff-lines (fn-ovw-lines group j j server v fn-arena fn-cat)))

; Pieces of the zero-allocation renderer: strings and decimals written into the lease.

(def-span-scan fn-ovr-copy-string ()
  :shape :copy-string)

(defun fn-ovr-string-len (s)
  (declare (xargs :guard t))
  (if (stringp s) (length s) 0))

; A string's octets appended to the lease: the :copy-string instance, its capacity the
; lease's length plus the string's (the quantum's fit test is what holds CAP).
(defun fn-ovr-put-string (s fn-ovr-lease)
  (declare (xargs :stobjs fn-ovr-lease
                  :guard (unsigned-byte-p 59 (+ (fn-ovr-lease-len fn-ovr-lease) (fn-ovr-string-len s)))
                  :verify-guards nil))
  (if (stringp s)
      (mv-let (dss-st fn-ovr-lease)
        (fn-ovr-copy-string 0 (length s) (+ (fn-ovr-lease-len fn-ovr-lease) (length s)) s fn-ovr-lease)
        (declare (ignore dss-st))
        fn-ovr-lease)
    fn-ovr-lease))

(local
 (defthm fn-ovr-copy-string-list-identity
   (implies (true-listp xs) (equal (fn-ovr-copy-string-list xs) xs))
   :hints (("Goal" :in-theory (enable fn-ovr-copy-string-list)))))

(local
 (defthm fn-ovr-dss-string-octets-aux-is-nntp
   (equal (fn-dss-string-octets-aux cs) (fn-nntp-string-octets-aux cs))
   :hints (("Goal" :in-theory (enable fn-dss-string-octets-aux fn-nntp-string-octets-aux)))))

(defthm fn-ovr-dss-string-octets-is-nntp
  (equal (fn-dss-string-octets s) (fn-nntp-string-octets s))
  :hints (("Goal" :in-theory (enable fn-dss-string-octets fn-nntp-string-octets))))

(local
 (defthm fn-ovr-nntp-octets-true-listp
   (true-listp (fn-nntp-string-octets-aux cs))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-ovr-nntp-octets-aux-len
   (equal (len (fn-nntp-string-octets-aux cs)) (len cs))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-ovr-take-len-octets
   (equal (take (len cs) (fn-nntp-string-octets-aux cs)) (fn-nntp-string-octets-aux cs))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-ovr-len-zero-atom
   (implies (equal (len x) 0) (not (consp x)))))

(defthm fn-ovr-put-string-is-octets
  (implies (true-listp fn-ovr-lease)
           (equal (fn-ovr-put-string s fn-ovr-lease)
                  (append fn-ovr-lease (fn-nntp-string-octets s))))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets length))))



(local
 (defthm fn-ovr-nthcdr-open
   (implies (and (natp i) (< i (len l)))
            (equal (nthcdr i l) (cons (nth i l) (nthcdr (+ 1 i) l))))
   :hints (("Goal" :in-theory (enable nthcdr nth)))))
(local (defthm fn-ovr-append-assoc (equal (append (append a b) c) (append a (append b c)))))
(local (defthm fn-ovr-nthcdr-past (implies (and (natp i) (<= (len l) i) (true-listp l)) (equal (nthcdr i l) nil))))

; The decimal digits of N, most significant first.
(defun fn-ovr-put-digits (n fn-ovr-lease)
  (declare (xargs :stobjs fn-ovr-lease
                  :guard (and (natp n) (fn-ovr-lease-p fn-ovr-lease))
                  :measure (nfix n)))
  (if (and (natp n) (<= 10 n))
      (let ((fn-ovr-lease (fn-ovr-put-digits (floor n 10) fn-ovr-lease)))
        (fn-ovr-lease-append-octet (+ 48 (mod n 10)) fn-ovr-lease))
    (fn-ovr-lease-append-octet (+ 48 (nfix n)) fn-ovr-lease)))

(defun fn-ovr-digits-len (n)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (and (natp n) (<= 10 n)) (+ 1 (fn-ovr-digits-len (floor n 10))) 1))

;; explode-nonnegative-integer's accumulator: a non-empty one is appended.
(local
 (defthm fn-ovr-explode-append
   (implies (and (natp n) (consp a))
            (equal (explode-nonnegative-integer n 10 (append a b))
                   (append (explode-nonnegative-integer n 10 a) b)))
   :hints (("Goal" :induct (explode-nonnegative-integer n 10 a)
            :in-theory (enable explode-nonnegative-integer)))))

(local
 (defthm fn-ovr-explode-acc
   (implies (and (posp n) (syntaxp (not (equal acc ''nil))))
            (equal (explode-nonnegative-integer n 10 acc)
                   (append (explode-nonnegative-integer n 10 nil) acc)))
   :hints (("Goal" :expand ((explode-nonnegative-integer n 10 acc)
                            (explode-nonnegative-integer n 10 nil))
            :use ((:instance fn-ovr-explode-append (n (floor n 10))
                             (a (list (digit-to-char (mod n 10)))) (b acc)))
            :in-theory (disable fn-ovr-explode-append)))))

(local
 (defthm fn-ovr-explode-step
   (implies (and (natp n) (<= 10 n))
            (equal (explode-nonnegative-integer n 10 nil)
                   (append (explode-nonnegative-integer (floor n 10) 10 nil)
                           (list (digit-to-char (mod n 10))))))
   :hints (("Goal" :expand ((explode-nonnegative-integer n 10 nil))
            :use ((:instance fn-ovr-explode-acc (n (floor n 10)) (acc (list (digit-to-char (mod n 10))))))
            :in-theory (disable fn-ovr-explode-acc)))))

(local
 (defthm fn-ovr-explode-small
   (implies (and (natp n) (< n 10))
            (equal (explode-nonnegative-integer n 10 nil) (list (digit-to-char n))))
   :hints (("Goal" :expand ((explode-nonnegative-integer n 10 nil))))))

(local
 (defthm fn-ovr-string-octets-aux-append
   (equal (fn-nntp-string-octets-aux (append a b))
          (append (fn-nntp-string-octets-aux a) (fn-nntp-string-octets-aux b)))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(defthm fn-ovr-put-digits-is-decimal
  (implies (and (natp n) (true-listp fn-ovr-lease))
           (equal (fn-ovr-put-digits n fn-ovr-lease)
                  (append fn-ovr-lease (fn-nntp-decimal n))))
  :hints (("Goal" :induct (fn-ovr-put-digits n fn-ovr-lease)
           :in-theory (e/d (fn-ovr-lease-append-octet fn-oct-snoc fn-nntp-decimal fn-nntp-decimal-rev
                            fn-nntp-string-octets-aux digit-to-char)
                           ()))
))

(defthm fn-ovr-digits-len-is-decimal-len
  (implies (natp n)
           (equal (fn-ovr-digits-len n) (len (fn-nntp-decimal n))))
  :hints (("Goal" :induct (fn-ovr-digits-len n)
           :in-theory (enable fn-nntp-decimal fn-nntp-decimal-rev fn-nntp-string-octets-aux))))

; String predicates read in place (no octet list): the Message-ID test and the Xref word test.

; Every character of S from I is in [33, 126] and, when NOCOLON, not ':'; when NOGT, none
; before the last is '>'.
(defun fn-ovr-chars-okp (s i nocolon nogt)
  (declare (xargs :guard (and (stringp s) (natp i)) :measure (nfix (- (length s) (nfix i)))))
  (if (and (stringp s) (natp i) (< i (length s)))
      (let ((c (char-code (char s i))))
        (and (<= 33 c) (<= c 126)
             (not (and nocolon (equal c 58)))
             (not (and nogt (< (+ 1 i) (length s)) (equal c 62)))
             (fn-ovr-chars-okp s (+ 1 i) nocolon nogt)))
    t))

; fn-scat-msgid-idp, in place.
(defun fn-ovr-msgid-okp (s)
  (declare (xargs :guard t))
  (and (stringp s)
       (<= (length s) *fn-nntp-max-message-id-octets*)
       (<= 3 (length s)) (<= (length s) 250)
       (equal (char s 0) #\<)
       (equal (char s (- (length s) 1)) #\>)
       (fn-ovr-chars-okp s 1 nil t)))

; fn-xref-wordp of the name's octets, in place.
(defun fn-ovr-xref-wordp (s)
  (declare (xargs :guard t))
  (and (stringp s) (< 0 (length s)) (fn-ovr-chars-okp s 0 t nil)))

;; The list twin the proofs reason over.
(local
 (defun fn-ovr-l-okp (cs nocolon nogt)
   (if (consp cs)
       (let ((c (char-code (car cs))))
         (and (<= 33 c) (<= c 126)
              (not (and nocolon (equal c 58)))
              (not (and nogt (consp (cdr cs)) (equal c 62)))
              (fn-ovr-l-okp (cdr cs) nocolon nogt)))
     t)))

(local
 (defthm fn-ovr-nthcdr-open-2
   (implies (and (natp i) (< i (len l)))
            (equal (nthcdr i l) (cons (nth i l) (nthcdr (+ 1 i) l))))
   :hints (("Goal" :in-theory (enable nthcdr nth)))))

(local
 (defthm fn-ovr-chars-okp-is-list
   (implies (and (stringp s) (natp i))
            (equal (fn-ovr-chars-okp s i nocolon nogt)
                   (fn-ovr-l-okp (nthcdr i (coerce s 'list)) nocolon nogt)))
   :hints (("Goal" :induct (fn-ovr-chars-okp s i nocolon nogt)
            :in-theory (e/d (char) (nthcdr nth)))
           ("Subgoal *1/2" :cases ((< (len (coerce s 'list)) i) (= (len (coerce s 'list)) i))))))

(local
 (defthm fn-ovr-l-okp-printable
   (equal (fn-ovr-l-okp cs nil nil)
          (fn-nntp-printable-tokenp (fn-nntp-string-octets-aux cs)))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux fn-nntp-printable-tokenp)))))

(local
 (defthm fn-ovr-l-okp-xref
   (equal (fn-ovr-l-okp cs t nil)
          (fn-xref-octetsp (fn-nntp-string-octets-aux cs)))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux fn-xref-octetsp fn-xref-octetp)))))

(local
 (defthm fn-ovr-octets-aux-consp
   (equal (consp (fn-nntp-string-octets-aux cs)) (consp cs))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-ovr-octets-aux-iff
   (iff (fn-nntp-string-octets-aux cs) (consp cs))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-ovr-char-code-62
   (implies (characterp c) (equal (equal (char-code c) 62) (equal c #\>)))
   :hints (("Goal" :use ((:instance code-char-char-code-is-identity))
            :in-theory (disable code-char-char-code-is-identity)))))

(local
 (defthm fn-ovr-l-okp-tail
   (implies (character-listp cs)
   (equal (and (fn-ovr-l-okp cs nil t) (consp cs) (equal (car (last cs)) #\>))
          (and (fn-nntp-printable-tokenp (fn-nntp-string-octets-aux cs))
               (fn-nntp-message-id-tailp (fn-nntp-string-octets-aux cs)))))
   :hints (("Goal" :induct (fn-ovr-l-okp cs nil t)
            :in-theory (enable fn-nntp-string-octets-aux fn-nntp-printable-tokenp
                               fn-nntp-message-id-tailp)))))

(local
 (defthm fn-ovr-nth-last
   (implies (consp l) (equal (nth (+ -1 (len l)) l) (car (last l))))
   :hints (("Goal" :in-theory (enable nth last)))))

(local
 (defthm fn-ovr-last-cdr
   (implies (consp (cdr l)) (equal (last l) (last (cdr l))))))

(local
 (defthm fn-ovr-nth-len-cdr
   (implies (consp l) (equal (nth (len (cdr l)) l) (car (last l))))
   :hints (("Goal" :in-theory (enable nth last)))))

(local (defthm fn-ovr-nthcdr-1 (equal (nthcdr 1 x) (cdr x))))
(local (defthm fn-ovr-char-listp-cdr-coerce (character-listp (cdr (coerce s 'list))) :hints (("Goal" :use ((:instance character-listp-coerce (str s))) :in-theory (disable character-listp-coerce)))))

(local
 (defthm fn-ovr-octets-aux-len
   (equal (len (fn-nntp-string-octets-aux cs)) (len cs))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-ovr-char-code-60
   (implies (characterp c) (equal (equal (char-code c) 60) (equal c #\<)))
   :hints (("Goal" :use ((:instance code-char-char-code-is-identity))
            :in-theory (disable code-char-char-code-is-identity)))))

(local (defthm fn-ovr-car-coerce-char
         (implies (consp (coerce s 'list)) (characterp (car (coerce s 'list))))
         :hints (("Goal" :use ((:instance character-listp-coerce (str s)))
                  :in-theory (disable character-listp-coerce)))))

(defthm fn-ovr-msgid-okp-is-idp
  (equal (fn-ovr-msgid-okp s) (fn-scat-msgid-idp s))
  :hints (("Goal" :in-theory (e/d (fn-scat-msgid-idp fn-nntp-string-octets fn-nntp-message-id-tokenp char)
                                  (fn-ovr-l-okp-tail fn-ovr-chars-okp fn-ovr-nth-last))
           :expand ((fn-nntp-string-octets-aux (coerce s 'list))
                    (fn-nntp-printable-tokenp (cons 60 (fn-nntp-string-octets-aux (cdr (coerce s 'list))))))
           :use ((:instance fn-ovr-l-okp-tail (cs (cdr (coerce s 'list))))))))

(defthm fn-ovr-xref-wordp-is-wordp
  (implies (stringp s)
           (equal (fn-ovr-xref-wordp s) (fn-xref-wordp (fn-nntp-string-octets s))))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets fn-xref-wordp)
           :expand ((fn-nntp-string-octets-aux (coerce s 'list))))))


; The article number of GROUP in MS for an article whose Message-ID test is IDP.
(defun fn-ovr-article-number (group ms idp)
  (declare (xargs :guard t))
  (let ((number (fn-nntp-membership-number group ms)))
    (if (and (posp number) (<= number *fn-nntp-max-article-number*) idp) number 0)))

(defthm fn-nntp-article-idp-is-msgid-idp
  (equal (fn-nntp-article-idp article) (fn-scat-msgid-idp (fn-article-msgid article)))
  :hints (("Goal" :in-theory (enable fn-nntp-article-idp fn-scat-msgid-idp))))

(defthm fn-ovr-article-number-is-number
  (equal (fn-ovr-article-number group (fn-article-memberships article)
                                (fn-scat-msgid-idp (fn-article-msgid article)))
         (fn-nntp-article-number group article))
  :hints (("Goal" :in-theory (enable fn-nntp-article-number))))

; fn-scat-available-article with the Message-ID tested in place.
(defun fn-ovr-available-article (group n v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (natp v) :verify-guards nil))
  (if (and (posp n) (<= n *fn-nntp-max-article-number*))
      (let ((article (fn-scat-number-article group n v fn-arena fn-cat)))
        (if (and article (fn-ovr-msgid-okp (fn-article-msgid article))) article nil))
    nil))

(defthm fn-ovr-available-article-is-available
  (equal (fn-ovr-available-article group n v fn-arena fn-cat)
         (fn-scat-available-article group n v fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-scat-available-article) (fn-scat-number-article fn-ovr-msgid-okp)))))

; The lengths the fit test reads, computed as the writers write, with no octet list.

(defun fn-ovr-decimal-field-len (n)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (natp n) (<= (fn-ovr-digits-len n) *fn-nntp-max-decimal-octets*)) (fn-ovr-digits-len n) 1))


(defun fn-ovr-decimal-len (n)
  (declare (xargs :guard t :verify-guards nil))
  (if (natp n) (fn-ovr-digits-len n) 0))

(defun fn-ovr-xref-len (ms all idp)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ms)
      (let ((m (car ms)))
        (+ (if (and (consp m) (stringp (car m)) (fn-ovr-xref-wordp (car m)) (posp (cdr m))
                    (equal (fn-ovr-article-number (car m) all idp) (cdr m)))
               (+ 2 (fn-ovr-string-len (car m)) (fn-ovr-decimal-field-len (cdr m)))
             0)
           (fn-ovr-xref-len (cdr ms) all idp)))
    0))

(defun fn-ovr-column-line-len (n nov octets body server ms idp)
  (declare (xargs :guard t :verify-guards nil))
  (+ (fn-ovr-decimal-field-len n)
     (fn-ovr-string-len (fn-hnov-subject nov)) (fn-ovr-string-len (fn-hnov-from nov))
     (fn-ovr-string-len (fn-hnov-date nov)) (fn-ovr-string-len (fn-hnov-msgid nov))
     (fn-ovr-string-len (fn-hnov-references nov))
     (fn-ovr-decimal-len octets) (fn-ovr-decimal-len body)
     7
     (if server
         (+ 1 (len *fn-xref-name*) (len (if (true-listp server) server nil)) (fn-ovr-xref-len ms ms idp))
       0)
     2))

(defun fn-ovr-number-len (group n server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (natp v) :verify-guards nil))
  (let ((article (fn-ovr-available-article group n v fn-arena fn-cat)))
    (if (not (consp article))
        0
      (if server
          (let ((facts (fn-scol-facts article fn-cat)))
            (if facts
                (let ((nov (fn-hf-nov facts)))
                  (if (or (fn-hnov-tomb nov) (not (fn-hnov-ok nov)))
                      0
                    (fn-ovr-column-line-len n nov (fn-nntp-article-length article fn-arena)
                                            (fn-hf-body-lines facts) server
                                            (fn-article-memberships article)
                                            (fn-ovr-msgid-okp (fn-article-msgid article)))))
              (if (fn-nntp-article-tombstonep article fn-arena)
                  0
                (let ((over (fn-nov-overview article fn-arena)))
                  (if (fn-nov-okp over)
                      (len (fn-nntp-crlf (fn-nov-served-line n over server article)))
                    0)))))
        (if (fn-nntp-article-tombstonep article fn-arena)
            0
          (let ((over (fn-nov-overview article fn-arena)))
            (if (fn-nov-okp over) (len (fn-nntp-crlf (fn-nov-line n over))) 0)))))))

(defun fn-ovr-probe-len (group j server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (natp j) (natp v)) :verify-guards nil))
  (let ((s (and (natp j) (fn-cnx-view-seq group j v fn-cat))))
    (if (and s (natp s) (< s (fn-cat-count fn-cat)))
        (let* ((h (fn-cat-at s fn-cat)) (n (fn-held-number-in group h)))
          (if (and (posp n) (<= n *fn-nntp-max-article-number*) (fn-ovr-msgid-okp (fn-record-msgid h)))
              (fn-ovr-number-len group n server v fn-arena fn-cat)
            0))
      0)))

;; Each length is the length its writer appends.
; The decimal field and the Xref locations, written in place.

(defthm fn-ovr-true-listp-append
  (equal (true-listp (append a b)) (true-listp b)))

(defun fn-ovr-put-decimal-field (n fn-ovr-lease)
  (declare (xargs :stobjs fn-ovr-lease :guard (fn-ovr-lease-p fn-ovr-lease) :verify-guards nil))
  (if (and (natp n) (<= (fn-ovr-digits-len n) *fn-nntp-max-decimal-octets*))
      (fn-ovr-put-digits n fn-ovr-lease)
    (fn-ovr-lease-append-octet 48 fn-ovr-lease)))

(local
 (defthm fn-ovr-decimal-tokenp-append
   (equal (fn-nntp-decimal-tokenp (append a b))
          (and (fn-nntp-decimal-tokenp a) (fn-nntp-decimal-tokenp b)))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal-tokenp)))))

(local
 (defthm fn-ovr-put-digits-token
   (implies (natp n)
            (and (consp (fn-ovr-put-digits n nil))
                 (fn-nntp-decimal-tokenp (fn-ovr-put-digits n nil))))
   :hints (("Goal" :induct (fn-ovr-put-digits n nil)
            :in-theory (e/d (fn-ovr-lease-append-octet fn-oct-snoc fn-nntp-decimal-tokenp
                             fn-nntp-decimal-digitp)
                            (fn-ovr-put-digits-is-decimal))))))

(local
 (defthm fn-ovr-decimal-token
   (implies (natp n)
            (and (consp (fn-nntp-decimal n))
                 (fn-nntp-decimal-tokenp (fn-nntp-decimal n))))
   :hints (("Goal" :use ((:instance fn-ovr-put-digits-token)
                         (:instance fn-ovr-put-digits-is-decimal (fn-ovr-lease nil)))
            :in-theory (disable fn-ovr-put-digits-token fn-ovr-put-digits-is-decimal fn-ovr-put-digits
                                fn-nntp-decimal)))))

(local
 (defthm fn-ovr-decimal-of-non-natural
   (implies (not (natp n)) (equal (fn-nntp-decimal n) nil))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal)))))

(defthm fn-ovr-put-decimal-field-is-field
  (implies (true-listp fn-ovr-lease)
           (equal (fn-ovr-put-decimal-field n fn-ovr-lease)
                  (append fn-ovr-lease (fn-nntp-decimal-field n))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-decimal-field fn-ovr-lease-append-octet fn-oct-snoc)
                                  (fn-nntp-decimal fn-ovr-put-digits fn-ovr-digits-len))
           :use ((:instance fn-ovr-digits-len-is-decimal-len)))))

; The Xref locations of the pairs of MS that name ALL's numbers.
(defun fn-ovr-put-xref (ms all idp fn-ovr-lease)
  (declare (xargs :stobjs fn-ovr-lease
                  :guard (unsigned-byte-p 59 (+ (fn-ovr-lease-len fn-ovr-lease) (fn-ovr-xref-len ms all idp)))
                  :verify-guards nil))
  (if (consp ms)
      (let ((m (car ms)))
        (if (and (consp m) (stringp (car m)) (fn-ovr-xref-wordp (car m)) (posp (cdr m))
                 (equal (fn-ovr-article-number (car m) all idp) (cdr m)))
            (let* ((fn-ovr-lease (fn-ovr-lease-append-octet 32 fn-ovr-lease))
                   (fn-ovr-lease (fn-ovr-put-string (car m) fn-ovr-lease))
                   (fn-ovr-lease (fn-ovr-lease-append-octet 58 fn-ovr-lease))
                   (fn-ovr-lease (fn-ovr-put-decimal-field (cdr m) fn-ovr-lease)))
              (fn-ovr-put-xref (cdr ms) all idp fn-ovr-lease))
          (fn-ovr-put-xref (cdr ms) all idp fn-ovr-lease)))
    fn-ovr-lease))

(defthm fn-ovr-put-xref-is-locations
  (implies (true-listp fn-ovr-lease)
           (equal (fn-ovr-put-xref ms (fn-article-memberships article)
                                   (fn-scat-msgid-idp (fn-article-msgid article)) fn-ovr-lease)
                  (append fn-ovr-lease (fn-xref-locations (fn-xref-pairs-of ms article)))))
  :hints (("Goal" :induct (fn-ovr-put-xref ms (fn-article-memberships article)
                                           (fn-scat-msgid-idp (fn-article-msgid article)) fn-ovr-lease)
           :in-theory (e/d (fn-xref-locations fn-xref-pairs-of fn-ovr-lease-append-octet fn-oct-snoc
                            fn-ag-car fn-ag-cdr)
                           (fn-ovr-article-number fn-nntp-article-number fn-ovr-xref-wordp
                            fn-ovr-put-string fn-ovr-put-decimal-field fn-nntp-string-octets
                            fn-xref-wordp fn-nntp-decimal-field fn-ovr-msgid-okp)))))

; One NOV line written from the row's column; the probe.

; fn-nntp-decimal, in place: the digits of a natural, nothing otherwise.
(defun fn-ovr-put-decimal (n fn-ovr-lease)
  (declare (xargs :stobjs fn-ovr-lease :guard (fn-ovr-lease-p fn-ovr-lease) :verify-guards nil))
  (if (natp n) (fn-ovr-put-digits n fn-ovr-lease) fn-ovr-lease))

(defthm fn-ovr-put-decimal-is-decimal
  (implies (true-listp fn-ovr-lease)
           (equal (fn-ovr-put-decimal n fn-ovr-lease)
                  (append fn-ovr-lease (fn-nntp-decimal n))))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal))))

; The served line of number N from the row's decided column NOV (fn-hnov-ok), the
; payload's octet count OCTETS and body lines BODY, then CRLF.  SERVER, ALL, IDP and MS:
; the Xref field (MS the memberships, ALL the same, IDP the article's Message-ID test).
(defun fn-ovr-put-column-line (n nov octets body server ms idp fn-ovr-lease)
  (declare (xargs :stobjs fn-ovr-lease
                  :guard (and (fn-cbor-octet-listp server)
                              (unsigned-byte-p 59 (+ (fn-ovr-lease-len fn-ovr-lease)
                                                     (fn-ovr-column-line-len n nov octets body server ms idp))))
                  :verify-guards nil))
  (let* ((fn-ovr-lease (fn-ovr-put-decimal-field n fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-lease-append-octet 9 fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-put-string (fn-hnov-subject nov) fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-lease-append-octet 9 fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-put-string (fn-hnov-from nov) fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-lease-append-octet 9 fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-put-string (fn-hnov-date nov) fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-lease-append-octet 9 fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-put-string (fn-hnov-msgid nov) fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-lease-append-octet 9 fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-put-string (fn-hnov-references nov) fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-lease-append-octet 9 fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-put-decimal octets fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-lease-append-octet 9 fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-put-decimal body fn-ovr-lease))
         (fn-ovr-lease (if server
                           (let* ((fn-ovr-lease (fn-ovr-lease-append-octet 9 fn-ovr-lease))
                                  (fn-ovr-lease (fn-ovr-lease-append-list *fn-xref-name* fn-ovr-lease))
                                  (fn-ovr-lease (fn-ovr-lease-append-list
                                                 (if (true-listp server) server nil) fn-ovr-lease)))
                             (fn-ovr-put-xref ms ms idp fn-ovr-lease))
                         fn-ovr-lease))
         (fn-ovr-lease (fn-ovr-lease-append-octet 13 fn-ovr-lease)))
    (fn-ovr-lease-append-octet 10 fn-ovr-lease)))

; The octets of the line of number N, written: the column when the row's is decided, the
; payload's parse otherwise (the cold arm, an octet list), nothing for an absent or
; tombstoned article or one whose overview does not parse.
(defun fn-ovr-put-number (group n server v fn-ovr-lease fn-arena fn-cat)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat)
                  :guard (and (natp v) (fn-cbor-octet-listp server)
                              (unsigned-byte-p 59 (+ (fn-ovr-lease-len fn-ovr-lease)
                                                     (fn-ovr-number-len group n server v fn-arena fn-cat))))
                  :verify-guards nil))
  (let ((article (fn-ovr-available-article group n v fn-arena fn-cat)))
    (if (not (consp article))
        fn-ovr-lease
      (if server
          (let ((facts (fn-scol-facts article fn-cat)))
            (if facts
                (let ((nov (fn-hf-nov facts)))
                  (if (or (fn-hnov-tomb nov) (not (fn-hnov-ok nov)))
                      fn-ovr-lease
                    (fn-ovr-put-column-line n nov (fn-nntp-article-length article fn-arena)
                                            (fn-hf-body-lines facts) server
                                            (fn-article-memberships article)
                                            (fn-ovr-msgid-okp (fn-article-msgid article))
                                            fn-ovr-lease)))
              (if (fn-nntp-article-tombstonep article fn-arena)
                  fn-ovr-lease
                (let ((over (fn-nov-overview article fn-arena)))
                  (if (fn-nov-okp over)
                      (fn-ovr-lease-append-list
                       (fn-nntp-crlf (fn-nov-served-line n over server article)) fn-ovr-lease)
                    fn-ovr-lease)))))
        (if (fn-nntp-article-tombstonep article fn-arena)
            fn-ovr-lease
          (let ((over (fn-nov-overview article fn-arena)))
            (if (fn-nov-okp over)
                (fn-ovr-lease-append-list (fn-nntp-crlf (fn-nov-line n over)) fn-ovr-lease)
              fn-ovr-lease)))))))

; The probe of number J: the row the view binds to J, kept as fn-scat-range-keep keeps it.
(defun fn-ovr-put-probe (group j server v fn-ovr-lease fn-arena fn-cat)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat)
                  :guard (and (natp j) (natp v) (fn-cbor-octet-listp server)
                              (unsigned-byte-p 59 (+ (fn-ovr-lease-len fn-ovr-lease)
                                                     (fn-ovr-probe-len group j server v fn-arena fn-cat))))
                  :verify-guards nil))
  (let ((s (and (natp j) (fn-cnx-view-seq group j v fn-cat))))
    (if (and s (natp s) (< s (fn-cat-count fn-cat)))
        (let* ((h (fn-cat-at s fn-cat)) (n (fn-held-number-in group h)))
          (if (and (posp n) (<= n *fn-nntp-max-article-number*) (fn-ovr-msgid-okp (fn-record-msgid h)))
              (fn-ovr-put-number group n server v fn-ovr-lease fn-arena fn-cat)
            fn-ovr-lease))
      fn-ovr-lease)))


(defun fn-ovr-column-over (nov octets body)
  (declare (xargs :guard t :verify-guards nil))
  (list :ok
        (fn-record-string-octets (fn-hnov-subject nov))
        (fn-record-string-octets (fn-hnov-from nov))
        (fn-record-string-octets (fn-hnov-date nov))
        (fn-record-string-octets (fn-hnov-msgid nov))
        (fn-record-string-octets (fn-hnov-references nov))
        octets body))

(local (defthm fn-ovr-append-assoc-5 (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-ovr-record-aux-is-nntp-aux
   (equal (fn-record-string-octets-aux chars) (fn-nntp-string-octets-aux chars))
   :hints (("Goal" :in-theory (enable fn-record-string-octets-aux fn-nntp-string-octets-aux)))))

(defthm fn-ovr-record-octets-is-nntp-octets
  (equal (fn-record-string-octets s) (fn-nntp-string-octets s))
  :hints (("Goal" :in-theory (enable fn-record-string-octets fn-nntp-string-octets))))

; The third char-code map is a twin (fn-dss-string-octets beside fn-nntp-string-octets and
; fn-record-string-octets); its retirement is C's: one definition below def-span-scan's
; includes that the other two are proved equal to.
(defthm fn-ovr-dss-string-octets-is-record
  (equal (fn-dss-string-octets s) (fn-record-string-octets s))
  :hints (("Goal" :in-theory (disable fn-dss-string-octets fn-record-string-octets fn-nntp-string-octets))))

(defthm fn-ovr-put-column-line-is-the-line
  (implies (true-listp fn-ovr-lease)
           (equal (fn-ovr-put-column-line n nov octets body server
                                          (fn-article-memberships article)
                                          (fn-scat-msgid-idp (fn-article-msgid article)) fn-ovr-lease)
                  (append fn-ovr-lease
                          (fn-nntp-crlf (fn-nov-served-line n (fn-ovr-column-over nov octets body)
                                                            server article)))))
  :hints (("Goal" :in-theory (e/d (fn-nov-served-line fn-nov-line fn-xref-field fn-xref-pairs fn-nntp-crlf
                                   fn-ovr-lease-append-octet fn-oct-snoc fn-ovr-lease-append-list
                                   fn-octets$a-append-list fn-ovr-column-over
                                   fn-nov-subject fn-nov-from fn-nov-date fn-nov-msgid fn-nov-references
                                   fn-nov-bytes fn-nov-lines fn-nntp-append-pieces)
                                  (fn-ovr-put-string fn-ovr-put-decimal fn-ovr-put-decimal-field fn-ovr-put-xref
                                   fn-nntp-decimal fn-nntp-decimal-field fn-record-string-octets
                                   fn-xref-locations fn-xref-pairs-of)))))

(local
 (defthm fn-ovr-decimal-field-not-dot
   (not (equal (car (fn-nntp-decimal-field n)) 46))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal-field fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)))))

(local
 (defthm fn-ovr-decimal-field-consp
   (consp (fn-nntp-decimal-field n))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal-field)))))

(local
 (defthm fn-ovr-car-append-consp
   (implies (consp a) (equal (car (append a b)) (car a)))))

(local
 (defthm fn-ovr-nov-line-not-dot
   (not (equal (car (fn-nov-line n over)) 46))
   :hints (("Goal" :in-theory (e/d (fn-nov-line fn-nntp-append-pieces) (fn-nntp-decimal-field))))))

(local
 (defthm fn-ovr-served-line-not-dot
   (not (equal (car (fn-nov-served-line n over server article)) 46))
   :hints (("Goal" :in-theory (e/d (fn-nov-served-line) (fn-nov-line))
            :cases ((consp (fn-nov-line n over)))))))

(local
 (defthm fn-ovr-stuff-one
   (implies (not (equal (car line) 46))
            (equal (fn-nntp-stuff-lines (list line)) (fn-nntp-crlf line)))
   :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines fn-wire-stuff-line)))))

(local
 (defthm fn-ovr-scol-overview-of-facts
   (implies (fn-scol-facts article fn-cat)
            (equal (fn-scol-overview-of article fn-arena fn-cat)
                   (let ((facts (fn-scol-facts article fn-cat)))
                     (if (fn-hnov-ok (fn-hf-nov facts))
                         (fn-ovr-column-over (fn-hf-nov facts) (fn-nntp-article-length article fn-arena)
                                             (fn-hf-body-lines facts))
                       (list :error)))))
   :hints (("Goal" :in-theory (enable fn-scol-overview-of fn-scol-nov-overview fn-ovr-column-over)))))

(local
 (defthm fn-ovr-scol-overview-of-no-facts
   (implies (not (fn-scol-facts article fn-cat))
            (equal (fn-scol-overview-of article fn-arena fn-cat)
                   (fn-nov-overview article fn-arena)))
   :hints (("Goal" :in-theory (enable fn-scol-overview-of)))))

(local
 (defthm fn-ovr-column-over-okp
   (fn-nov-okp (fn-ovr-column-over nov octets body))
   :hints (("Goal" :in-theory (enable fn-nov-okp fn-ovr-column-over)))))

(defthm fn-ovr-put-number-is-the-lines
  (implies (and (true-listp fn-ovr-lease) (natp v))
           (equal (fn-ovr-put-number group n server v fn-ovr-lease fn-arena fn-cat)
                  (append fn-ovr-lease
                          (fn-nntp-stuff-lines
                           (if server
                               (fn-nov-served-lines-for-numbers-cat group (list n) server v fn-arena fn-cat)
                             (fn-nov-lines-for-numbers-cat group (list n) v fn-arena fn-cat))))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-put-number fn-nov-served-lines-for-numbers-cat
                                   fn-nov-lines-for-numbers-cat fn-scol-tombstonep
                                   fn-ovr-lease-append-list fn-octets$a-append-list)
                                  (fn-ovr-put-column-line fn-nov-served-line fn-nov-line fn-nov-overview fn-hf-nov
                                   fn-scol-facts fn-scat-available-article fn-ovr-available-article
                                   fn-nntp-article-tombstonep fn-nntp-stuff-lines fn-nntp-crlf
                                   fn-scol-overview-of fn-ovr-column-over fn-nntp-article-length
                                   fn-ovr-msgid-okp)))))

(local (defthm fn-ovr-served-lines-nil
  (equal (fn-nov-served-lines-for-numbers-cat group nil server v fn-arena fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-nov-served-lines-for-numbers-cat)))))
(local (defthm fn-ovr-lines-nil
  (equal (fn-nov-lines-for-numbers-cat group nil v fn-arena fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-nov-lines-for-numbers-cat)))))
(local (defthm fn-ovr-stuff-nil
  (equal (fn-nntp-stuff-lines nil) nil)
  :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines)))))
(local (defthm fn-ovr-append-nil-tl (implies (true-listp x) (equal (append x nil) x))))

; KO1: the renderer writes exactly the octets the window step writes for that number.
(defthm fn-ovr-put-probe-is-the-served-octets
  (implies (and (natp v) (true-listp fn-ovr-lease))
           (equal (fn-ovr-put-probe group j server v fn-ovr-lease fn-arena fn-cat)
                  (append fn-ovr-lease (fn-ovr-probe-octets group j server v fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-put-probe fn-ovr-probe-octets fn-ovw-lines fn-scat-range-keep
                                   fn-ovr-msgid-okp-is-idp)
                                  (fn-ovr-put-number fn-nov-served-lines-for-numbers-cat
                                   fn-nov-lines-for-numbers-cat fn-cnx-view-seq fn-held-number-in
                                   fn-scat-msgid-idp fn-ovr-msgid-okp fn-nntp-stuff-lines))
           :expand ((fn-cnx-range-aux group j j v fn-cat)
                    (fn-cnx-range-aux group (+ 1 j) j v fn-cat)))))

(local (defthm fn-ovr-len-append (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-ovr-decimal-field-len-is-len
  (equal (fn-ovr-decimal-field-len n) (len (fn-nntp-decimal-field n)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-decimal-field) (fn-ovr-digits-len))
           :use ((:instance fn-ovr-digits-len-is-decimal-len)))))

(defthm fn-ovr-decimal-len-is-len
  (equal (fn-ovr-decimal-len n) (len (fn-nntp-decimal n)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-decimal) (fn-ovr-digits-len)))))

(defthm fn-ovr-string-len-is-len
  (equal (fn-ovr-string-len s) (len (fn-nntp-string-octets s)))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets length))))

(defthm fn-ovr-xref-len-is-len
  (equal (fn-ovr-xref-len ms (fn-article-memberships article) (fn-scat-msgid-idp (fn-article-msgid article)))
         (len (fn-xref-locations (fn-xref-pairs-of ms article))))
  :hints (("Goal" :induct (fn-ovr-xref-len ms (fn-article-memberships article)
                                           (fn-scat-msgid-idp (fn-article-msgid article)))
           :in-theory (e/d (fn-xref-locations fn-xref-pairs-of fn-ag-car fn-ag-cdr)
                           (fn-ovr-article-number fn-nntp-article-number fn-ovr-xref-wordp
                            fn-ovr-decimal-field-len fn-nntp-string-octets fn-xref-wordp
                            fn-nntp-decimal-field fn-ovr-msgid-okp fn-ovr-string-len)))))

(local (defthm fn-ovr-len-append-9 (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-ovr-column-line-len-is-len
  (equal (fn-ovr-column-line-len n nov octets body server (fn-article-memberships article)
                                 (fn-scat-msgid-idp (fn-article-msgid article)))
         (len (fn-nntp-crlf (fn-nov-served-line n (fn-ovr-column-over nov octets body) server article))))
  :hints (("Goal" :in-theory (e/d (fn-nov-served-line fn-nov-line fn-xref-field fn-xref-pairs fn-nntp-crlf
                                   fn-ovr-column-over fn-nntp-append-pieces
                                   fn-nov-subject fn-nov-from fn-nov-date fn-nov-msgid fn-nov-references
                                   fn-nov-bytes fn-nov-lines)
                                  (fn-ovr-decimal-field-len fn-ovr-decimal-len fn-ovr-string-len fn-ovr-xref-len
                                   fn-nntp-decimal fn-nntp-decimal-field fn-nntp-string-octets
                                   fn-xref-locations fn-xref-pairs-of)))))

(defthm fn-ovr-number-len-is-len
  (implies (natp v)
           (equal (fn-ovr-number-len group n server v fn-arena fn-cat)
                  (len (fn-nntp-stuff-lines
                        (if server
                            (fn-nov-served-lines-for-numbers-cat group (list n) server v fn-arena fn-cat)
                          (fn-nov-lines-for-numbers-cat group (list n) v fn-arena fn-cat))))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-number-len fn-nov-served-lines-for-numbers-cat
                                   fn-nov-lines-for-numbers-cat fn-scol-tombstonep)
                                  (fn-ovr-column-line-len fn-nov-served-line fn-nov-line fn-nov-overview
                                   fn-hf-nov fn-scol-facts fn-scat-available-article fn-ovr-available-article
                                   fn-nntp-article-tombstonep fn-nntp-stuff-lines fn-nntp-crlf
                                   fn-scol-overview-of fn-ovr-column-over fn-nntp-article-length
                                   fn-ovr-msgid-okp)))))

; KO1b: the length the fit test reads is the length written.
(defthm fn-ovr-probe-len-is-the-length
  (implies (natp v)
           (equal (fn-ovr-probe-len group j server v fn-arena fn-cat)
                  (len (fn-ovr-probe-octets group j server v fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-probe-len fn-ovr-probe-octets fn-ovw-lines fn-scat-range-keep
                                   fn-ovr-msgid-okp-is-idp)
                                  (fn-ovr-number-len fn-nov-served-lines-for-numbers-cat
                                   fn-nov-lines-for-numbers-cat fn-cnx-view-seq fn-held-number-in
                                   fn-scat-msgid-idp fn-ovr-msgid-okp fn-nntp-stuff-lines))
           :expand ((fn-cnx-range-aux group j j v fn-cat)
                    (fn-cnx-range-aux group (+ 1 j) j v fn-cat)))))

;; ---------------------------------------------------------------------------
;; Guards.  Each writer's guard is that the lease's length plus what it writes is a
;; 59-bit fixnum (the :copy-string instance's index type); the quantum's capacity test
;; discharges it at the entry.

(in-theory (disable fn-ovr-string-len-is-len fn-ovr-decimal-field-len-is-len fn-ovr-decimal-len-is-len
                    fn-ovr-xref-len-is-len))

(verify-guards fn-ovr-put-string)
(verify-guards fn-ovr-put-digits)
(verify-guards fn-ovr-digits-len)
(verify-guards fn-ovr-decimal-field-len)
(verify-guards fn-ovr-decimal-len)
(verify-guards fn-ovr-xref-len)
(verify-guards fn-ovr-put-decimal-field)
(verify-guards fn-ovr-put-decimal)
(verify-guards fn-ovr-column-line-len)
(verify-guards fn-ovr-available-article)
(verify-guards fn-ovr-number-len)
(verify-guards fn-ovr-probe-len)
(local (defthm fn-ovr-g-len-append (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm fn-ovr-g-octet-listp-true-listp (implies (fn-cbor-octet-listp x) (true-listp x))
         :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(local (defthm fn-ovr-g-lease-true-listp (implies (fn-ovr-lease-p x) (true-listp x))))
(defthm fn-ovr-len-put-string
  (implies (true-listp fn-ovr-lease)
           (equal (len (fn-ovr-put-string s fn-ovr-lease)) (+ (len fn-ovr-lease) (fn-ovr-string-len s))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-string-len-is-len) (fn-ovr-put-string)))))
(defthm fn-ovr-len-put-decimal-field
  (implies (true-listp fn-ovr-lease)
           (equal (len (fn-ovr-put-decimal-field n fn-ovr-lease)) (+ (len fn-ovr-lease) (fn-ovr-decimal-field-len n))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-decimal-field-len-is-len) (fn-ovr-put-decimal-field fn-ovr-decimal-field-len)))))
(defthm fn-ovr-true-listp-put-string
  (implies (true-listp fn-ovr-lease) (true-listp (fn-ovr-put-string s fn-ovr-lease)))
  :hints (("Goal" :in-theory (disable fn-ovr-put-string))))
(defthm fn-ovr-true-listp-put-decimal-field
  (implies (true-listp fn-ovr-lease) (true-listp (fn-ovr-put-decimal-field n fn-ovr-lease)))
  :hints (("Goal" :in-theory (disable fn-ovr-put-decimal-field))))
(defthm fn-ovr-xref-len-natp (natp (fn-ovr-xref-len ms all idp)) :rule-classes :type-prescription)
(defthm fn-ovr-decimal-field-len-natp (natp (fn-ovr-decimal-field-len n)) :rule-classes :type-prescription)
(defthm fn-ovr-len-string-octets
  (equal (len (fn-nntp-string-octets s)) (fn-ovr-string-len s))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets fn-ovr-string-len length))))
(verify-guards fn-ovr-put-xref
  :hints (("Goal" :expand ((fn-ovr-xref-len ms all idp))
           :in-theory (e/d (fn-ovr-lease-append-octet fn-oct-snoc)
                           (fn-ovr-put-string fn-ovr-put-decimal-field fn-ovr-xref-len fn-ovr-string-len-is-len
                            fn-ovr-decimal-field-len fn-ovr-article-number fn-ovr-xref-wordp
                            fn-ovr-put-string-is-octets fn-ovr-put-decimal-field-is-field)))))

(defthm fn-ovr-len-put-xref
  (implies (true-listp fn-ovr-lease)
           (equal (len (fn-ovr-put-xref ms all idp fn-ovr-lease))
                  (+ (len fn-ovr-lease) (fn-ovr-xref-len ms all idp))))
  :hints (("Goal" :induct (fn-ovr-put-xref ms all idp fn-ovr-lease)
           :in-theory (e/d (fn-ovr-lease-append-octet fn-oct-snoc fn-ovr-string-len-is-len
                            fn-ovr-decimal-field-len-is-len)
                           (fn-ovr-put-string fn-ovr-put-decimal-field fn-ovr-len-string-octets
                            fn-ovr-article-number fn-ovr-xref-wordp
                            fn-ovr-decimal-field-len fn-ovr-string-len)))))
(defthm fn-ovr-true-listp-put-xref
  (implies (true-listp fn-ovr-lease) (true-listp (fn-ovr-put-xref ms all idp fn-ovr-lease)))
  :hints (("Goal" :induct (fn-ovr-put-xref ms all idp fn-ovr-lease)
           :in-theory (e/d (fn-ovr-lease-append-octet fn-oct-snoc)
                           (fn-ovr-put-string fn-ovr-put-decimal-field fn-ovr-article-number fn-ovr-xref-wordp)))))
(defthm fn-ovr-len-put-decimal
  (implies (true-listp fn-ovr-lease)
           (equal (len (fn-ovr-put-decimal n fn-ovr-lease)) (+ (len fn-ovr-lease) (fn-ovr-decimal-len n))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-decimal-len-is-len) (fn-ovr-put-decimal fn-ovr-decimal-len)))))
(defthm fn-ovr-true-listp-put-decimal
  (implies (true-listp fn-ovr-lease) (true-listp (fn-ovr-put-decimal n fn-ovr-lease)))
  :hints (("Goal" :in-theory (disable fn-ovr-put-decimal))))
(defthm fn-ovr-decimal-len-natp (natp (fn-ovr-decimal-len n)) :rule-classes :type-prescription)
(defthm fn-ovr-string-len-natp (natp (fn-ovr-string-len n)) :rule-classes :type-prescription)
(verify-guards fn-ovr-put-column-line
  :hints (("Goal" :expand ((fn-ovr-column-line-len n nov octets body server ms idp))
           :in-theory (e/d (fn-ovr-lease-append-octet fn-oct-snoc fn-ovr-lease-append-list fn-octets$a-append-list)
                           (fn-ovr-put-string fn-ovr-put-decimal-field fn-ovr-put-decimal fn-ovr-put-xref
                            fn-ovr-string-len-is-len fn-ovr-decimal-field-len-is-len fn-ovr-decimal-len-is-len
                            fn-ovr-xref-len-is-len fn-ovr-len-string-octets
                            fn-ovr-put-string-is-octets fn-ovr-put-decimal-field-is-field
                            fn-ovr-put-decimal-is-decimal fn-ovr-put-xref-is-locations
                            fn-ovr-xref-len fn-ovr-decimal-field-len fn-ovr-decimal-len fn-ovr-string-len)))))

(defthm fn-ovr-len-put-column-line
  (implies (true-listp fn-ovr-lease)
           (equal (len (fn-ovr-put-column-line n nov octets body server ms idp fn-ovr-lease))
                  (+ (len fn-ovr-lease) (fn-ovr-column-line-len n nov octets body server ms idp))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-put-column-line fn-ovr-column-line-len fn-ovr-lease-append-octet
                                   fn-oct-snoc fn-ovr-lease-append-list fn-octets$a-append-list)
                                  (fn-ovr-put-string fn-ovr-put-decimal-field fn-ovr-put-decimal fn-ovr-put-xref
                                   fn-ovr-put-string-is-octets fn-ovr-put-decimal-field-is-field
                                   fn-ovr-put-decimal-is-decimal fn-ovr-put-xref-is-locations
                                   fn-ovr-xref-len fn-ovr-decimal-field-len fn-ovr-decimal-len fn-ovr-string-len)))))

(local (defthm fn-ovr-g-octets-append
  (equal (fn-cbor-octet-listp (append a b))
         (and (fn-cbor-octet-listp (true-list-fix a)) (fn-cbor-octet-listp b)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(local (defthm fn-ovr-g-octets-string-aux
  (fn-cbor-octet-listp (fn-nntp-string-octets-aux cs))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-nntp-string-octets-aux)))))
(local (defthm fn-ovr-g-octets-string
  (fn-cbor-octet-listp (fn-nntp-string-octets s))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets)))))
(local (defthm fn-ovr-g-octets-decimal
  (fn-cbor-octet-listp (fn-nntp-decimal n))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal fn-nntp-decimal-rev)))))
(local (defthm fn-ovr-g-octets-decimal-field
  (fn-cbor-octet-listp (fn-nntp-decimal-field n))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-field)))))
(local (defthm fn-ovr-g-octets-xref-locations
  (fn-cbor-octet-listp (fn-xref-locations pairs))
  :hints (("Goal" :in-theory (e/d (fn-xref-locations) (fn-nntp-string-octets fn-nntp-decimal-field))))))
(local (defthm fn-ovr-g-tlf-octets (implies (fn-cbor-octet-listp x) (fn-cbor-octet-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(defthm fn-ovr-nov-overview-line-octets
  (implies (fn-cbor-octet-listp server)
           (and (fn-cbor-octet-listp (fn-nntp-crlf (fn-nov-line n (fn-nov-overview article fn-arena))))
                (fn-cbor-octet-listp (fn-nntp-crlf (fn-nov-served-line n (fn-nov-overview article fn-arena)
                                                                       server article)))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-crlf fn-nov-served-line fn-nov-line fn-nntp-append-pieces fn-xref-field
                                   fn-nov-overview fn-nov-subject fn-nov-from fn-nov-date fn-nov-msgid
                                   fn-nov-references fn-nov-bytes fn-nov-lines)
                                  (fn-nntp-decimal fn-nntp-decimal-field fn-nntp-string-octets fn-xref-locations
                                   fn-nov-header-content fn-xref-pairs fn-article-parse fn-nntp-article-length
                                   fn-nov-body-line-count)))))

(defthm fn-ovr-column-line-len-natp (natp (fn-ovr-column-line-len n nov octets body server ms idp))
  :rule-classes :type-prescription)
(defthm fn-ovr-number-len-natp (natp (fn-ovr-number-len group n server v fn-arena fn-cat))
  :rule-classes :type-prescription)
(verify-guards fn-ovr-put-number
  :hints (("Goal" :in-theory (e/d (fn-ovr-number-len fn-ovr-lease-append-list fn-octets$a-append-list)
                                  (fn-ovr-put-column-line fn-ovr-column-line-len fn-nov-served-line fn-nov-line
                                   fn-nov-overview fn-scol-facts fn-ovr-available-article fn-nntp-crlf
                                   fn-nntp-article-tombstonep fn-nntp-article-length fn-hf-nov fn-ovr-msgid-okp
                                   fn-ovr-put-column-line-is-the-line fn-ovr-available-article-is-available
                                   fn-scat-available-article fn-scol-tombstonep fn-scol-overview-of
                                   fn-ovr-column-line-len-is-len fn-ovr-number-len-is-len)))))
(defthm fn-ovr-len-put-number
  (implies (true-listp fn-ovr-lease)
           (equal (len (fn-ovr-put-number group n server v fn-ovr-lease fn-arena fn-cat))
                  (+ (len fn-ovr-lease) (fn-ovr-number-len group n server v fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-put-number fn-ovr-number-len fn-ovr-lease-append-list fn-octets$a-append-list)
                                  (fn-ovr-put-column-line fn-ovr-column-line-len fn-nov-served-line fn-nov-line
                                   fn-nov-overview fn-scol-facts fn-ovr-available-article fn-nntp-crlf
                                   fn-nntp-article-tombstonep fn-nntp-article-length fn-hf-nov fn-ovr-msgid-okp
                                   fn-ovr-put-column-line-is-the-line fn-ovr-available-article-is-available
                                   fn-scat-available-article fn-scol-tombstonep fn-scol-overview-of
                                   fn-ovr-column-line-len-is-len fn-ovr-number-len-is-len)))))
(verify-guards fn-ovr-put-probe
  :hints (("Goal" :in-theory (e/d (fn-ovr-probe-len)
                                  (fn-ovr-put-number fn-ovr-number-len fn-cnx-view-seq fn-held-number-in
                                   fn-ovr-msgid-okp fn-ovr-put-number-is-the-lines fn-ovr-number-len-is-len
                                   fn-ovr-probe-len-is-the-length fn-ovr-put-probe-is-the-served-octets)))))

; The two framing texts of a window.
(defun fn-ovr-status-octets ()
  (declare (xargs :guard t))
  (fn-ovw-status (fn-proto-text * :overview)))
(defun fn-ovr-close-octets (owed2 legacyp)
  (declare (xargs :guard t))
  (if owed2 (fn-ovw-status (fn-ovw-empty-text legacyp)) '(46 13 10)))

;; One pass over the probes J..LAST: each probe's length is read, and the probe is
;; written (after the status, while owed) only when the window through it, closed if
;; J is the range's last number, fits ROOM.  (mv HI OWED LEASE'): HI the last number
;; written (J-1 when none), OWED the status still owed.
(defun fn-ovr-fill (group j last top owedp legacyp room server v fn-ovr-lease fn-arena fn-cat)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (+ 1 (nfix last)) (nfix j)))))
  (if (and (natp j) (<= j (nfix last)))
      (let* ((p (fn-ovr-probe-len group j server v fn-arena fn-cat))
             (s (if (and owedp (posp p)) (len (fn-ovr-status-octets)) 0))
             (owed2 (and owedp (zp p)))
             (close (if (<= (nfix top) j) (len (fn-ovr-close-octets owed2 legacyp)) 0)))
        (if (<= (+ (fn-ovr-lease-len fn-ovr-lease) s p close) (nfix room))
            (let* ((fn-ovr-lease (if (posp s)
                                     (fn-ovr-lease-append-list (fn-ovr-status-octets) fn-ovr-lease)
                                   fn-ovr-lease))
                   (fn-ovr-lease (fn-ovr-put-probe group j server v fn-ovr-lease fn-arena fn-cat)))
              (fn-ovr-fill group (+ 1 j) last top owed2 legacyp room server v fn-ovr-lease fn-arena fn-cat))
          (mv (- j 1) owedp fn-ovr-lease)))
    (mv (- (nfix j) 1) owedp fn-ovr-lease)))

; ONE QUANTUM.  (mv N NEXT LEASE'): N numbers taken (0: not even one number's window
; fits the lease's remaining room under CAP; nothing written, the cursor unchanged),
; NEXT the cursor after them (nil when the range is exhausted), LEASE' the lease with
; the window's octets appended.  A header cursor (nth 7) is not this landing's: N = 0.
; A server name that is not an octet list cannot be written into an octet lease: N = 0
; (the served arm's server is fn-xref-serverp or nil, fn-nntp-xref-server-is-a-server).
(defun fn-ovr-quantum (cur w cap fn-ovr-lease fn-arena fn-cat)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil))
  (if (or (not (consp cur)) (nth 7 cur) (not (fn-cbor-octet-listp (nth 6 cur)))
          (not (unsigned-byte-p 59 cap)) (< cap (fn-ovr-lease-len fn-ovr-lease)))
      (mv 0 cur fn-ovr-lease)
    (let* ((group (nth 0 cur)) (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
           (v (nfix (nth 3 cur))) (legacyp (nth 4 cur)) (owedp (nth 5 cur)) (server (nth 6 cur)))
      (mv-let (hi owed2 fn-ovr-lease)
        (fn-ovr-fill group k (fn-ovw-hi k top w) top owedp legacyp cap server v fn-ovr-lease fn-arena fn-cat)
        (if (< hi k)
            (mv 0 cur fn-ovr-lease)
          (let* ((donep (<= top hi))
                 (fn-ovr-lease (if donep
                                   (fn-ovr-lease-append-list (fn-ovr-close-octets owed2 legacyp)
                                                             fn-ovr-lease)
                                 fn-ovr-lease)))
            (mv (+ 1 (- hi k))
                (if donep nil (fn-ovw-cursor group (+ 1 hi) top v legacyp owed2 server))
                fn-ovr-lease)))))))

; The run: quanta into the lease, cleared before each, until the cursor is nil;
; OKP nil when a quantum takes no number.
(defun fn-ovr-run (cur w cap fn-ovr-lease fn-arena fn-cat)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil
                  :measure (fn-ovw-remaining cur)
                  :hints (("Goal" :in-theory (disable fn-ovr-quantum)))))
  (if (consp cur)
      (let ((fn-ovr-lease (fn-ovr-lease-clear fn-ovr-lease)))
        (mv-let (n next fn-ovr-lease) (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)
          (cond ((not (posp n)) (mv nil nil fn-ovr-lease))
                ((null next) (mv t (fn-ovr-lease-list fn-ovr-lease) fn-ovr-lease))
                ((< (fn-ovw-remaining next) (fn-ovw-remaining cur))
                 (let ((octets (fn-ovr-lease-list fn-ovr-lease)))
                   (mv-let (okp rest fn-ovr-lease) (fn-ovr-run next w cap fn-ovr-lease fn-arena fn-cat)
                     (mv okp (append octets rest) fn-ovr-lease))))
                (t (mv nil nil fn-ovr-lease)))))
    (mv t nil fn-ovr-lease)))

; Every probe of K..TOP renders within L octets.
(defun fn-ovr-probes-within (group k top server v l fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (<= k (nfix top)))
      (and (<= (fn-ovr-probe-len group k server v fn-arena fn-cat) (nfix l))
           (fn-ovr-probes-within group (+ 1 k) top server v l fn-arena fn-cat))
    t))

; The framing a window may add beyond its lines: the status and the longer close.
(defun fn-ovr-frame-max ()
  (declare (xargs :guard t))
  (+ (len (fn-ovr-status-octets))
     (max (len (fn-ovr-close-octets t t)) (max (len (fn-ovr-close-octets t nil)) 3))))

