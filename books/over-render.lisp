;; OVER rendered directly into a runtime-contract pool window.
;; Concrete pool writers and their byte-count model.

(in-package "ACL2")

(include-book "over-window")

(include-book "def-span-scan-window")


(include-book "decimal-text")

(local (include-book "arithmetic-5/top" :dir :system))
; Pool rules come from C20; these helpers express OVER's absolute budget.
(local (in-theory (union-theories (theory 'fn-dsw-pool-theory) (current-theory :here))))
; Keep splice as the state refinement; opt into puts equalities only in hints.
(local (in-theory (disable fn-dsw-splice-is-puts fn-dsw-puts-is-splice
                           fn-dsw-append-loop-is-puts)))
(defthm fn-ovrqp-pool-length
 (implies (fn-rtc-st$ap s) (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s))))
 :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$ap fn-rtc-shapep) (theory 'minimal-theory)))))
(defthm fn-ovrqp-splice-preserves-ap
 (implies (fn-rtc-st$ap s) (fn-rtc-st$ap (fn-rtc-st$a-splice h j data s)))
 :hints (("Goal" :use ((:instance fn-rtc-st-splice{preserved} (fn-rtc-st s) (off j)))
          :in-theory (theory 'minimal-theory))))
(defun fn-ovrqp-roomp (h j limit s)
 (declare (xargs :verify-guards nil))
 (and (fn-rtc-st$ap s) (natp j) (natp limit) (<= j limit)
      (<= limit (fn-rtc-buf-cap h (fn-rtc-config s))) (fn-rtc-splice-okp h j nil s)))
(defthm fn-ovrqp-splice-frames
 (implies (and (fn-rtc-st$ap s) (fn-rtc-splice-okp h j data s))
   (and (equal (fn-rtc-config (fn-rtc-st$a-splice h j data s)) (fn-rtc-config s))
        (equal (fn-rtc-uses (fn-rtc-st$a-splice h j data s)) (fn-rtc-uses s))
        (equal (fn-rtc-b-owner (fn-rtc-buffer h (fn-rtc-st$a-splice h j data s)))
               (fn-rtc-b-owner (fn-rtc-buffer h s)))
        (equal (fn-rtc-b-bytes (fn-rtc-buffer h (fn-rtc-st$a-splice h j data s)))
               (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h s)) j data))))
 :hints (("Goal" :in-theory
  (union-theories '(fn-rtc-st$a-splice fn-rtc-splice-okp fn-rtc-b-owner fn-rtc-b-bytes fn-rtc-get
                   fn-dsw-with-buffer-accessors fn-ovrqp-pool-length fn-dsw-state-buffer-shape
                   natp nfix zp car-cons cdr-cons len)
                  (theory 'minimal-theory)))))
(defthm fn-ovrqp-room-after-splice
 (implies (and (fn-ovrqp-roomp h j limit s) (fn-cbor-octet-listp data) (<= (+ j (len data)) limit))
   (and (fn-rtc-splice-okp h j data s)
        (fn-ovrqp-roomp h (+ j (len data)) limit (fn-rtc-st$a-splice h j data s))))
 :hints (("Goal" :do-not-induct t :in-theory
   (union-theories '(fn-ovrqp-roomp fn-rtc-splice-okp
      fn-ovrqp-splice-frames fn-ovrqp-splice-preserves-ap fn-dsw-state-buffer-shape
      fn-rtc-c-l-splice-length fn-cbor-octet-listp-implies-true-listp
      natp nfix max len zp car-cons cdr-cons (:type-prescription len)
      (:executable-counterpart fn-cbor-octet-listp))
      (theory 'minimal-theory)))))
(local (defthm fn-ovrqp-nfix-natural (implies (natp x) (equal (nfix x) x))))
(local (defthm fn-ovrqp-natural-nfix (natp (nfix x)) :rule-classes :type-prescription))
(local (defthm fn-ovrqp-len-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (append a b) :in-theory (enable binary-append len)))))
(defthm fn-ovrqp-puts-compose
 (implies (natp j)
  (equal (fn-rtc-st$a-puts h (+ j (len a)) b (fn-rtc-st$a-puts h j a s))
         (fn-rtc-st$a-puts h j (append a b) s)))
 :hints (("Goal" :induct (fn-rtc-st$a-puts h j a s)
    :in-theory (e/d (fn-rtc-st$a-puts binary-append) (fn-rtc-st$a-put fn-rtc-st$a-splice fn-rtc-splice)))))
(defthm fn-ovrqp-room-properties
 (implies (fn-ovrqp-roomp h j limit s)
   (and (fn-rtc-st$ap s) (natp j) (natp limit)))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory (union-theories '(fn-ovrqp-roomp) (theory 'minimal-theory)))))
(defthm fn-ovrqp-splice-compose
 (implies (and (fn-ovrqp-roomp h j limit s) (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
               (<= (+ j (len a) (len b)) limit))
   (equal (fn-rtc-st$a-splice h (+ j (len a)) b (fn-rtc-st$a-splice h j a s))
          (fn-rtc-st$a-splice h j (append a b) s)))
 :hints (("Goal" :do-not-induct t
   :use ((:instance fn-ovrqp-room-after-splice (data a))
         (:instance fn-ovrqp-room-after-splice (data b) (j (+ j (len a)))
                    (s (fn-rtc-st$a-splice h j a s)))
         (:instance fn-dsw-splice-is-puts (data a))
         (:instance fn-dsw-splice-is-puts (data b) (j (+ j (len a)))
                    (s (fn-rtc-st$a-splice h j a s)))
         (:instance fn-dsw-splice-is-puts (data (append a b))))
   :in-theory (union-theories '(fn-ovrqp-room-properties fn-ovrqp-room-after-splice
                  fn-ovrqp-splice-preserves-ap fn-ovrqp-len-append fn-ovrqp-puts-compose
                  fn-rtc-c-l-octets-append natp nfix (:type-prescription len))
                 (theory 'minimal-theory)))))
(defthm fn-ovrqp-empty-append-keeps-state
 (equal (mv-nth 2 (fn-dsw-append h j nil st)) st)
 :hints (("Goal" :in-theory (union-theories '(fn-dsw-append fn-dsw-append-loop mv-nth car-cons cdr-cons
                (:executable-counterpart fn-cbor-octet-listp) len) (theory 'minimal-theory)))))
(defthm fn-ovrqp-empty-append-position
 (implies (natp j) (equal (mv-nth 1 (fn-dsw-append h j nil st)) j))
 :hints (("Goal" :in-theory (union-theories '(fn-dsw-append fn-dsw-append-loop mv-nth car-cons cdr-cons
                (:executable-counterpart fn-cbor-octet-listp) len default-+-1 default-+-2)
                (fn-dss-measure-theory)))))
(defthm fn-ovrqp-empty-splice
 (implies (and (fn-rtc-st$ap st) (fn-rtc-splice-okp h j nil st))
   (equal (fn-rtc-st$a-splice h j nil st) st))
 :hints (("Goal" :use ((:instance fn-dsw-append-is-splice (data nil) (s st))
                      fn-ovrqp-empty-append-keeps-state)
    :in-theory (union-theories '(mv-nth car-cons cdr-cons zp len) (theory 'minimal-theory)))))
(defthm fn-ovrqp-room-at-splice-position
 (implies (and (fn-ovrqp-roomp h j limit s) (fn-cbor-octet-listp data)
               (equal j2 (+ j (len data))) (<= j2 limit))
  (fn-ovrqp-roomp h j2 limit (fn-rtc-st$a-splice h j data s)))
 :hints (("Goal" :use fn-ovrqp-room-after-splice :in-theory (theory 'minimal-theory))))
(defthm fn-ovrqp-compose-at-splice-position
 (implies (and (fn-ovrqp-roomp h j limit s) (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
               (equal j2 (+ j (len a))) (<= (+ j2 (len b)) limit))
   (equal (fn-rtc-st$a-splice h j2 b (fn-rtc-st$a-splice h j a s))
          (fn-rtc-st$a-splice h j (append a b) s)))
 :hints (("Goal" :use fn-ovrqp-splice-compose :in-theory
    (union-theories '(associativity-of-+) (theory 'minimal-theory)))))
(local (defthm fn-ovrqp-append-associates
 (equal (append (append a b) c) (append a (append b c)))
 :hints (("Goal" :induct (append a b) :in-theory (enable binary-append)))))
(local (defthm fn-ovrqp-fold-sums
 (implies (syntaxp (and (quotep a) (quotep b)))
  (equal (+ a b x) (+ (+ a b) x)))
 :hints (("Goal" :use ((:instance associativity-of-+ (x a) (y b) (z x)))
  :in-theory (theory 'minimal-theory)))))
(defthm fn-ovrqp-room-bounds
 (implies (fn-ovrqp-roomp h j limit s)
  (and (<= j limit) (<= limit (fn-rtc-buf-cap h (fn-rtc-config s))) (fn-rtc-splice-okp h j nil s)))
 :hints (("Goal" :in-theory (union-theories '(fn-ovrqp-roomp) (theory 'minimal-theory)))))
(local (defthm fn-ovrqp-octets-append
 (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
  (fn-cbor-octet-listp (append a b)))
 :hints (("Goal" :induct (append a b)
   :in-theory (union-theories '(fn-cbor-octet-listp binary-append car-cons cdr-cons) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-octets-cons
 (equal (fn-cbor-octet-listp (cons x xs))
        (and (fn-cbor-octetp x) (fn-cbor-octet-listp xs)))
 :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))


(defun fn-ovr-probe-octets (group j server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (natp j) (natp v)) :verify-guards nil))
  (fn-nntp-stuff-lines (fn-ovw-lines group j j server v fn-arena fn-cat)))

(defun fn-ovr-string-len (s)
  (declare (xargs :guard t))
  (if (stringp s) (length s) 0))

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

(local
 (defthm fn-ovr-nthcdr-open
   (implies (and (natp i) (< i (len l)))
            (equal (nthcdr i l) (cons (nth i l) (nthcdr (+ 1 i) l))))
   :hints (("Goal" :in-theory (enable nthcdr nth)))))

(local (defthm fn-ovr-append-assoc (equal (append (append a b) c) (append a (append b c)))))

(local (defthm fn-ovr-nthcdr-past (implies (and (natp i) (<= (len l) i) (true-listp l)) (equal (nthcdr i l) nil))))

(local
 (defthm fn-ovr-explode-characters
   (implies (and (natp n) (character-listp acc))
            (character-listp (explode-nonnegative-integer n 10 acc)))))

(local
 (defthm fn-ovr-decimal-text-octets
   (implies (natp n)
            (equal (fn-nntp-string-octets (fn-decimal-text n)) (fn-nntp-decimal n)))
   :hints (("Goal" :in-theory (enable fn-decimal-text fn-nntp-string-octets fn-nntp-decimal
                                      fn-nntp-decimal-rev)))))

(local
 (defthm fn-ovr-decimal-text-len
   (implies (natp n)
            (equal (len (coerce (fn-decimal-text n) 'list)) (len (fn-nntp-decimal n))))
   :hints (("Goal" :in-theory (enable fn-decimal-text fn-nntp-decimal fn-nntp-decimal-rev)))))

(local
 (defun fn-ovr-digit-charsp (cs)
   (if (consp cs)
       (and (member (car cs) '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
            (fn-ovr-digit-charsp (cdr cs)))
     t)))

(local
 (defthm fn-ovr-explode-digits
   (implies (and (natp n) (fn-ovr-digit-charsp acc))
            (fn-ovr-digit-charsp (explode-nonnegative-integer n 10 acc)))
   :hints (("Goal" :in-theory (enable explode-nonnegative-integer digit-to-char)))))

(local
 (defthm fn-ovr-explode-consp
   (implies (natp n) (consp (explode-nonnegative-integer n 10 nil)))
   :hints (("Goal" :expand ((explode-nonnegative-integer n 10 nil))))))

(local
 (defthm fn-ovr-digit-chars-token
   (implies (and (fn-ovr-digit-charsp cs) (consp cs))
            (and (consp (fn-nntp-string-octets-aux cs))
                 (fn-nntp-decimal-tokenp (fn-nntp-string-octets-aux cs))))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux fn-nntp-decimal-tokenp
                                      fn-nntp-decimal-digitp)))))

(local
 (defthm fn-ovr-decimal-token
   (implies (natp n)
            (and (consp (fn-nntp-decimal n))
                 (fn-nntp-decimal-tokenp (fn-nntp-decimal n))))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal fn-nntp-decimal-rev)))))

(defun fn-ovr-chars-okp (s i nocolon nogt)
  (declare (xargs :guard (and (stringp s) (natp i)) :measure (nfix (- (length s) (nfix i)))))
  (if (and (stringp s) (natp i) (< i (length s)))
      (let ((c (char-code (char s i))))
        (and (<= 33 c) (<= c 126)
             (not (and nocolon (equal c 58)))
             (not (and nogt (< (+ 1 i) (length s)) (equal c 62)))
             (fn-ovr-chars-okp s (+ 1 i) nocolon nogt)))
    t))

(defun fn-ovr-msgid-okp (s)
  (declare (xargs :guard t))
  (and (stringp s)
       (<= (length s) *fn-nntp-max-message-id-octets*)
       (<= 3 (length s)) (<= (length s) 250)
       (equal (char s 0) #\<)
       (equal (char s (- (length s) 1)) #\>)
       (fn-ovr-chars-okp s 1 nil t)))

(defun fn-ovr-xref-wordp (s)
  (declare (xargs :guard t))
  (and (stringp s) (< 0 (length s)) (fn-ovr-chars-okp s 0 t nil)))

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

(defun fn-ovr-decimal-field-len (n)
  (declare (xargs :guard t :verify-guards nil))
  (if (natp n)
      (let ((d (length (fn-decimal-text n))))
        (if (<= d *fn-nntp-max-decimal-octets*) d 1))
    1))

(defun fn-ovr-decimal-len (n)
  (declare (xargs :guard t :verify-guards nil))
  (if (natp n) (length (fn-decimal-text n)) 0))

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

(defthm fn-ovr-true-listp-append
  (equal (true-listp (append a b)) (true-listp b)))

(local
 (defthm fn-ovr-decimal-tokenp-append
   (equal (fn-nntp-decimal-tokenp (append a b))
          (and (fn-nntp-decimal-tokenp a) (fn-nntp-decimal-tokenp b)))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal-tokenp)))))

(local
 (defthm fn-ovr-decimal-of-non-natural
   (implies (not (natp n)) (equal (fn-nntp-decimal n) nil))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal)))))

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

(local (defthm fn-ovr-len-append (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-ovr-decimal-field-len-is-len
  (equal (fn-ovr-decimal-field-len n) (len (fn-nntp-decimal-field n)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-decimal-field length) (fn-decimal-text fn-nntp-decimal))
           :use ((:instance fn-ovr-decimal-text-octets)))))

(defthm fn-ovr-decimal-len-is-len
  (equal (fn-ovr-decimal-len n) (len (fn-nntp-decimal n)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-decimal length) (fn-decimal-text))
           :use ((:instance fn-ovr-decimal-text-octets)))))

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

(in-theory (disable fn-ovr-string-len-is-len fn-ovr-decimal-field-len-is-len fn-ovr-decimal-len-is-len
                    fn-ovr-xref-len-is-len))

(verify-guards fn-ovr-decimal-field-len)

(verify-guards fn-ovr-decimal-len)

(verify-guards fn-ovr-xref-len)

(verify-guards fn-ovr-column-line-len)

(verify-guards fn-ovr-available-article)

(verify-guards fn-ovr-number-len)

(verify-guards fn-ovr-probe-len)

(local (defthm fn-ovr-g-len-append (equal (len (append a b)) (+ (len a) (len b)))))

(local (defthm fn-ovr-g-octet-listp-true-listp (implies (fn-cbor-octet-listp x) (true-listp x))
         :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(defthm fn-ovr-xref-len-natp (natp (fn-ovr-xref-len ms all idp)) :rule-classes :type-prescription)

(defthm fn-ovr-decimal-field-len-natp (natp (fn-ovr-decimal-field-len n)) :rule-classes :type-prescription)

(defthm fn-ovr-len-string-octets
  (equal (len (fn-nntp-string-octets s)) (fn-ovr-string-len s))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets fn-ovr-string-len length))))

(defthm fn-ovr-decimal-len-natp (natp (fn-ovr-decimal-len n)) :rule-classes :type-prescription)

(defthm fn-ovr-string-len-natp (natp (fn-ovr-string-len n)) :rule-classes :type-prescription)

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

(def-span-scan-window fn-ovr-wcopy-string () :shape :copy-string)

(defun fn-ovr-put-octets (octets h j limit fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (if (<= (+ (nfix j) (len octets)) (nfix limit))
      (fn-dsw-append h j octets fn-rtc-st)
    (mv :refused j fn-rtc-st)))

(defun fn-ovr-put-string (s h j limit fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (if (<= (+ (nfix j) (fn-ovr-string-len s)) (nfix limit))
      (if (stringp s)
          (fn-ovr-wcopy-string h 0 (length s) j s fn-rtc-st)
        (fn-dsw-append h j nil fn-rtc-st))
    (mv :refused j fn-rtc-st)))

(defun fn-ovr-put-decimal-field (n h j limit fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (if (<= (+ (nfix j) (fn-ovr-decimal-field-len n)) (nfix limit))
      (if (and (natp n) (<= (fn-dsw-decimal-count n) *fn-nntp-max-decimal-octets*))
          (fn-dsw-decimal h j n fn-rtc-st)
        (fn-dsw-append h j '(48) fn-rtc-st))
    (mv :refused j fn-rtc-st)))

(defun fn-ovr-put-decimal (n h j limit fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (if (<= (+ (nfix j) (fn-dsw-decimal-count n)) (nfix limit))
      (fn-dsw-decimal h j n fn-rtc-st)
    (mv :refused j fn-rtc-st)))

(defun fn-ovr-put-xref (ms all idp h j limit fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (if (< (nfix limit) (+ (nfix j) (fn-ovr-xref-len ms all idp)))
      (mv :refused j fn-rtc-st)
    (if (consp ms)
    (let ((m (car ms)))
      (if (and (consp m)
               (stringp (car m))
               (fn-ovr-xref-wordp (car m))
               (posp (cdr m))
               (equal (fn-ovr-article-number (car m) all idp) (cdr m)))
          (mv-let (sig j fn-rtc-st) (fn-ovr-put-octets (list 32) h j limit fn-rtc-st)
            (declare (ignore sig))
            (mv-let (sig j fn-rtc-st) (fn-ovr-put-string (car m) h j limit fn-rtc-st)
              (declare (ignore sig))
              (mv-let (sig j fn-rtc-st) (fn-ovr-put-octets (list 58) h j limit fn-rtc-st)
                (declare (ignore sig))
                (mv-let (sig j fn-rtc-st) (fn-ovr-put-decimal-field (cdr m) h j limit fn-rtc-st)
                  (declare (ignore sig))
                  (fn-ovr-put-xref (cdr ms) all idp h j limit fn-rtc-st)))))
        (fn-ovr-put-xref (cdr ms) all idp h j limit fn-rtc-st)))
  (mv :done j fn-rtc-st))))

(defun fn-ovr-put-decimal-field-tab (n h j limit fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (mv-let (sig j fn-rtc-st) (fn-ovr-put-decimal-field n h j limit fn-rtc-st) (declare (ignore sig)) (fn-ovr-put-octets '(9) h j limit fn-rtc-st)))
(defun fn-ovr-put-decimal-tab (n h j limit fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (mv-let (sig j fn-rtc-st) (fn-ovr-put-decimal n h j limit fn-rtc-st) (declare (ignore sig)) (fn-ovr-put-octets '(9) h j limit fn-rtc-st)))
(defun fn-ovr-put-fields (fields h j limit fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (if (consp fields)
      (mv-let (sig j fn-rtc-st) (fn-ovr-put-string (car fields) h j limit fn-rtc-st) (declare (ignore sig)) (mv-let (sig j fn-rtc-st) (fn-ovr-put-octets '(9) h j limit fn-rtc-st) (declare (ignore sig)) (fn-ovr-put-fields (cdr fields) h j limit fn-rtc-st)))
    (mv :done j fn-rtc-st)))
(defun fn-ovr-put-served-xref (server ms idp h j limit fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (if server
      (mv-let (sig j fn-rtc-st) (fn-ovr-put-octets '(9) h j limit fn-rtc-st) (declare (ignore sig)) (mv-let (sig j fn-rtc-st) (fn-ovr-put-octets *fn-xref-name* h j limit fn-rtc-st) (declare (ignore sig)) (mv-let (sig j fn-rtc-st) (fn-ovr-put-octets (if (true-listp server) server nil) h j limit fn-rtc-st) (declare (ignore sig)) (fn-ovr-put-xref ms ms idp h j limit fn-rtc-st))))
    (mv :done j fn-rtc-st)))

(defun fn-ovr-put-column-line (n nov octets body server ms idp h j limit fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (if (< (nfix limit) (+ (nfix j) (fn-ovr-column-line-len n nov octets body server ms idp)))
      (mv :refused j fn-rtc-st)
    (mv-let (sig j fn-rtc-st) (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st) (declare (ignore sig)) (mv-let (sig j fn-rtc-st) (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h j limit fn-rtc-st) (declare (ignore sig)) (mv-let (sig j fn-rtc-st) (fn-ovr-put-decimal-tab octets h j limit fn-rtc-st) (declare (ignore sig)) (mv-let (sig j fn-rtc-st) (fn-ovr-put-decimal body h j limit fn-rtc-st) (declare (ignore sig)) (mv-let (sig j fn-rtc-st) (fn-ovr-put-served-xref server ms idp h j limit fn-rtc-st) (declare (ignore sig)) (fn-ovr-put-octets '(13 10) h j limit fn-rtc-st))))))))


(defun fn-ovr-put-number (group n server v h j limit fn-rtc-st fn-arena fn-cat)
  (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (let ((v (nfix v))) (if (< (nfix limit) (+ (nfix j) (fn-ovr-number-len group n server v fn-arena fn-cat)))
      (mv :refused j fn-rtc-st)
    (let ((article (fn-ovr-available-article group n v fn-arena fn-cat)))
  (if (not (consp article))
      (mv :done j fn-rtc-st)
    (if server
        (let ((facts (fn-scol-facts article fn-cat)))
          (if facts
              (let ((nov (fn-hf-nov facts)))
                (if (or (fn-hnov-tomb nov) (not (fn-hnov-ok nov)))
                    (mv :done j fn-rtc-st)
                  (fn-ovr-put-column-line n
                                          nov
                                          (fn-nntp-article-length article fn-arena)
                                          (fn-hf-body-lines facts)
                                          server
                                          (fn-article-memberships article)
                                          (fn-ovr-msgid-okp (fn-article-msgid article))
                                          h
                                          j
                                          limit
                                          fn-rtc-st)))
            (if (fn-nntp-article-tombstonep article fn-arena)
                (mv :done j fn-rtc-st)
              (let ((over (fn-nov-overview article fn-arena)))
                (if (fn-nov-okp over)
                    (fn-ovr-put-octets (fn-nntp-crlf (fn-nov-served-line n over server article))
                                       h
                                       j
                                       limit
                                       fn-rtc-st)
                  (mv :done j fn-rtc-st))))))
      (if (fn-nntp-article-tombstonep article fn-arena)
          (mv :done j fn-rtc-st)
        (let ((over (fn-nov-overview article fn-arena)))
          (if (fn-nov-okp over)
              (fn-ovr-put-octets (fn-nntp-crlf (fn-nov-line n over)) h j limit fn-rtc-st)
            (mv :done j fn-rtc-st))))))))))

(defun fn-ovr-put-probe (group number server v h j limit fn-rtc-st fn-arena fn-cat)
  (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 limit) (<= j limit))))
  (let ((v (nfix v))) (if (natp number) (if (< (nfix limit) (+ (nfix j) (fn-ovr-probe-len group number server v fn-arena fn-cat)))
      (mv :refused j fn-rtc-st)
    (let ((s (and (natp number) (fn-cnx-view-seq group number v fn-cat))))
  (if (and s (natp s) (< s (fn-cat-count fn-cat)))
      (let ((row (fn-cat-at s fn-cat)))
        (let ((n (fn-held-number-in group row)))
          (if (and (posp n) (<= n *fn-nntp-max-article-number*) (fn-ovr-msgid-okp (fn-record-msgid row)))
              (fn-ovr-put-number group n server v h j limit fn-rtc-st fn-arena fn-cat)
            (mv :done j fn-rtc-st))))
    (mv :done j fn-rtc-st)))) (mv :done j fn-rtc-st))))


; Position and guards for primitive in-place writers.
(local (defthm fn-ovrwp-octets-position
  (implies (and (natp j) (<= j (nfix limit)))
           (let ((j2 (mv-nth 1 (fn-ovr-put-octets octets h j limit s))))
             (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-ovr-put-octets fn-dsw-append nfix natp len car-cons cdr-cons)
             (fn-dss-measure-theory))))))

(verify-guards fn-ovr-put-octets
  :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p))))

(verify-guards fn-ovr-put-string
  :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p fn-ovr-string-len length))))

(verify-guards fn-ovr-put-decimal-field
  :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p fn-ovr-decimal-field-len-natp (:type-prescription fn-dsw-decimal-count)))))

(verify-guards fn-ovr-put-decimal
  :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p (:type-prescription fn-dsw-decimal-count)))))

(local (defthm fn-ovrwp-nthcdr-zero
  (equal (nthcdr 0 xs) xs)
  :hints (("Goal" :in-theory (enable nthcdr)))))

; In-place writer preservation and position facts; only the probe contract
; is exported to the quantum book. Smaller field pipelines keep proofs bounded.
(local (defthm fn-ovrwp-explode-append
  (implies (and (posp n) (true-listp acc))
    (equal (explode-nonnegative-integer n 10 (append acc tail))
           (append (explode-nonnegative-integer n 10 acc) tail)))
  :hints (("Goal" :induct (explode-nonnegative-integer n 10 acc)
           :in-theory (e/d (explode-nonnegative-integer) (digit-to-char floor mod fn-rtc-st$ap fn-rtc-shapep))))))

(local (defthm fn-ovrwp-string-aux-append
  (equal (fn-nntp-string-octets-aux (append a b))
         (append (fn-nntp-string-octets-aux a) (fn-nntp-string-octets-aux b)))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local (defthm fn-ovrwp-digit-code
  (implies (and (natp d) (< d 10)) (equal (char-code (digit-to-char d)) (+ 48 d)))
  :hints (("Goal" :in-theory (enable digit-to-char) :cases ((equal d 0) (equal d 1) (equal d 2)
                      (equal d 3) (equal d 4) (equal d 5) (equal d 6) (equal d 7) (equal d 8) (equal d 9))))))

(local (defthm fn-ovrwp-decimal-small
  (implies (and (natp n) (< n 10)) (equal (fn-nntp-decimal n) (list (+ 48 n))))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal fn-nntp-decimal-rev explode-nonnegative-integer
                                    fn-nntp-string-octets-aux)))))

(local (defthm fn-ovrwp-decimal-step
  (implies (and (natp n) (<= 10 n))
    (equal (fn-nntp-decimal n) (append (fn-nntp-decimal (floor n 10)) (list (+ 48 (mod n 10))))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-decimal fn-nntp-decimal-rev fn-nntp-string-octets-aux)
                                    (explode-nonnegative-integer fn-rtc-st$ap fn-rtc-shapep))
           :expand ((explode-nonnegative-integer n 10 nil))
           :use ((:instance fn-ovrwp-explode-append (n (floor n 10)) (acc nil) (tail (list (digit-to-char (mod n 10))))))))))

(local (defthm fn-ovrwp-decimal-non-natural
  (implies (not (natp n)) (equal (fn-nntp-decimal n) nil))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal)))))

(local (defthm fn-ovrwp-decimal-count-is-length
  (equal (fn-dsw-decimal-count n) (len (fn-nntp-decimal n)))
  :hints (("Goal" :induct (fn-dsw-decimal-count n)
           :in-theory (e/d () (fn-nntp-decimal fn-nntp-decimal-rev fn-rtc-st$ap fn-rtc-shapep))
           :expand ((fn-dsw-decimal-count n)))
          ("Subgoal *1/2" :in-theory (enable fn-nntp-decimal)))))

(local (defthm fn-ovrwp-splice-preserves-ap
  (implies (fn-rtc-st$ap s) (fn-rtc-st$ap (fn-rtc-st$a-splice h j data s)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-rtc-st-splice{preserved} (fn-rtc-st s) (off j)))))))

(local (defthm fn-ovrwp-octets-preserves-ap
  (implies (fn-rtc-st$ap s)
           (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-octets octets h j limit s))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-put-octets)
          (fn-rtc-st$ap fn-rtc-shapep fn-rtc-st$a-splice fn-rtc-splice-okp fn-dsw-append fn-dsw-decimal fn-ovr-wcopy-string
           fn-ovr-probe-len fn-ovr-number-len fn-ovr-column-line-len fn-ovr-xref-len)))) ))

(local (defthm fn-ovrwp-string-preserves-ap
  (implies (fn-rtc-st$ap s)
           (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-string text h j limit s))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-put-string)
          (fn-rtc-st$ap fn-rtc-shapep fn-rtc-st$a-splice fn-rtc-splice-okp fn-dsw-append fn-dsw-decimal fn-ovr-wcopy-string
           fn-ovr-probe-len fn-ovr-number-len fn-ovr-column-line-len fn-ovr-xref-len)))) ))

(local (defthm fn-ovrwp-decimal-field-preserves-ap
  (implies (fn-rtc-st$ap s)
           (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-decimal-field n h j limit s))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-put-decimal-field)
          (fn-rtc-st$ap fn-rtc-shapep fn-rtc-st$a-splice fn-rtc-splice-okp fn-dsw-append fn-dsw-decimal fn-ovr-wcopy-string
           fn-ovr-probe-len fn-ovr-number-len fn-ovr-column-line-len fn-ovr-xref-len)))) ))

(local (defthm fn-ovrwp-decimal-preserves-ap
  (implies (fn-rtc-st$ap s)
           (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-decimal n h j limit s))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-put-decimal)
          (fn-rtc-st$ap fn-rtc-shapep fn-rtc-st$a-splice fn-rtc-splice-okp fn-dsw-append fn-dsw-decimal fn-ovr-wcopy-string
           fn-ovr-probe-len fn-ovr-number-len fn-ovr-column-line-len fn-ovr-xref-len)))) ))

(local (defthm fn-ovrwp-xref-preserves-ap
  (implies (fn-rtc-st$ap s)
           (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-xref ms all idp h j limit s))))
  :hints (("Goal" :induct (fn-ovr-put-xref ms all idp h j limit s)
    :in-theory (union-theories '(fn-ovr-put-xref
         fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap)
       (fn-dss-measure-theory))))))

(local (defthm fn-ovrwp-decimal-field-position
  (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
           (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field n h j limit s))))
             (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
  :hints (("Goal" :in-theory
            (e/d (fn-ovr-put-decimal-field fn-ovr-decimal-field-len-is-len fn-nntp-decimal-field)
                 (fn-rtc-st$ap fn-rtc-shapep fn-dsw-decimal fn-dsw-append fn-rtc-splice-okp fn-rtc-st$a-splice
                  fn-ovr-decimal-field-len fn-nntp-decimal fn-dsw-decimal-count))))))

(local (defthm fn-ovrwp-decimal-position
  (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
           (let ((j2 (mv-nth 1 (fn-ovr-put-decimal n h j limit s))))
             (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-put-decimal)
                 (fn-rtc-st$ap fn-rtc-shapep fn-dsw-decimal fn-dsw-append fn-rtc-splice-okp fn-rtc-st$a-splice
                  fn-nntp-decimal fn-dsw-decimal-count))))))

(local (defthm fn-ovrwp-string-position
  (implies (and (fn-rtc-st$ap st) (natp j) (<= j (nfix limit)))
           (let ((j2 (mv-nth 1 (fn-ovr-put-string s h j limit st))))
             (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
  :hints (("Goal" :in-theory (e/d (fn-ovr-put-string fn-oct-slice-list-is-take-nthcdr fn-ovr-string-len length)
                 (fn-rtc-st$ap fn-rtc-shapep fn-ovr-wcopy-string fn-dsw-append fn-rtc-splice-okp fn-rtc-st$a-splice
                  fn-nntp-string-octets))))))

(local (defthm fn-ovrwp-decimal-field-tab-preserves-ap
 (implies (fn-rtc-st$ap s) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovr-put-decimal-field-tab fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap) (fn-dss-measure-theory))))))

(local (defthm fn-ovrwp-decimal-tab-preserves-ap
 (implies (fn-rtc-st$ap s) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-decimal-tab n h j limit s))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovr-put-decimal-tab fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap) (fn-dss-measure-theory))))))

(local (defthm fn-ovrwp-fields-preserves-ap
 (implies (fn-rtc-st$ap s) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-fields fields h j limit s))))
 :hints (("Goal" :induct (fn-ovr-put-fields fields h j limit s)
    :in-theory (union-theories '(fn-ovr-put-fields fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap) (fn-dss-measure-theory))))))

(local (defthm fn-ovrwp-served-xref-preserves-ap
 (implies (fn-rtc-st$ap s) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-served-xref server ms idp h j limit s))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovr-put-served-xref fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap) (fn-dss-measure-theory))))))

(local (defthm fn-ovrwp-column-line-preserves-ap
 (implies (fn-rtc-st$ap s) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-column-line n nov octets body server ms idp h j limit s))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovr-put-column-line fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap) (fn-dss-measure-theory))))))

(local (defthm fn-ovrwp-number-preserves-ap
 (implies (fn-rtc-st$ap s) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-number group n server v h j limit s fn-arena fn-cat))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovr-put-number fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap fn-ovrwp-column-line-preserves-ap) (fn-dss-measure-theory))))))

(defthm fn-ovrwp-probe-preserves-ap
 (implies (fn-rtc-st$ap s) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-probe group number server v h j limit s fn-arena fn-cat))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovr-put-probe fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap fn-ovrwp-column-line-preserves-ap fn-ovrwp-number-preserves-ap) (fn-dss-measure-theory)))))

(local (defthm fn-ovrwp-nfix-natural (implies (natp x) (equal (nfix x) x))))

(local (defthm fn-ovrwp-natural-nfix (natp (nfix x)) :rule-classes :type-prescription))

(local (defthm fn-ovrwp-octets-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-octets octets h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory)
          :use fn-ovrwp-octets-position))))

(local (defthm fn-ovrwp-string-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-string text h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory)
          :use ((:instance fn-ovrwp-string-position (s text) (st s)))))))

(local (defthm fn-ovrwp-decimal-field-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field n h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory)
          :use fn-ovrwp-decimal-field-position))))

(local (defthm fn-ovrwp-decimal-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal n h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory)
          :use fn-ovrwp-decimal-position))))

(local (defthm fn-ovrwp-xref-position
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-xref ms all idp h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :induct (fn-ovr-put-xref ms all idp h j limit s)
    :in-theory (union-theories '(fn-ovrwp-octets-position-linear fn-ovrwp-string-position-linear fn-ovrwp-decimal-field-position-linear fn-ovrwp-decimal-position-linear natp-compound-recognizer fn-ovrwp-nfix-natural fn-ovrwp-natural-nfix fn-ovr-put-xref fn-ovrwp-octets-position fn-ovrwp-string-position fn-ovrwp-decimal-field-position fn-ovrwp-decimal-position fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap fn-ovrwp-column-line-preserves-ap fn-ovrwp-number-preserves-ap fn-ovrwp-probe-preserves-ap) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))

(local (defthm fn-ovrwp-xref-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-xref ms all idp h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-xref-position))))

(local (defthm fn-ovrwp-decimal-field-tab-position
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrwp-octets-position-linear fn-ovrwp-string-position-linear fn-ovrwp-decimal-field-position-linear fn-ovrwp-decimal-position-linear fn-ovrwp-xref-position-linear natp-compound-recognizer fn-ovrwp-nfix-natural fn-ovrwp-natural-nfix fn-ovr-put-decimal-field-tab fn-ovrwp-octets-position fn-ovrwp-string-position fn-ovrwp-decimal-field-position fn-ovrwp-decimal-position fn-ovrwp-xref-position fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap fn-ovrwp-column-line-preserves-ap fn-ovrwp-number-preserves-ap fn-ovrwp-probe-preserves-ap) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))

(local (defthm fn-ovrwp-decimal-field-tab-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-decimal-field-tab-position))))

(local (defthm fn-ovrwp-decimal-tab-position
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-tab n h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrwp-octets-position-linear fn-ovrwp-string-position-linear fn-ovrwp-decimal-field-position-linear fn-ovrwp-decimal-position-linear fn-ovrwp-xref-position-linear fn-ovrwp-decimal-field-tab-position-linear natp-compound-recognizer fn-ovrwp-nfix-natural fn-ovrwp-natural-nfix fn-ovr-put-decimal-tab fn-ovrwp-octets-position fn-ovrwp-string-position fn-ovrwp-decimal-field-position fn-ovrwp-decimal-position fn-ovrwp-xref-position fn-ovrwp-decimal-field-tab-position fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap fn-ovrwp-column-line-preserves-ap fn-ovrwp-number-preserves-ap fn-ovrwp-probe-preserves-ap) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))

(local (defthm fn-ovrwp-decimal-tab-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-tab n h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-decimal-tab-position))))

(local (defthm fn-ovrwp-fields-position
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-fields fields h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :induct (fn-ovr-put-fields fields h j limit s)
    :in-theory (union-theories '(fn-ovrwp-octets-position-linear fn-ovrwp-string-position-linear fn-ovrwp-decimal-field-position-linear fn-ovrwp-decimal-position-linear fn-ovrwp-xref-position-linear fn-ovrwp-decimal-field-tab-position-linear fn-ovrwp-decimal-tab-position-linear natp-compound-recognizer fn-ovrwp-nfix-natural fn-ovrwp-natural-nfix fn-ovr-put-fields fn-ovrwp-octets-position fn-ovrwp-string-position fn-ovrwp-decimal-field-position fn-ovrwp-decimal-position fn-ovrwp-xref-position fn-ovrwp-decimal-field-tab-position fn-ovrwp-decimal-tab-position fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap fn-ovrwp-column-line-preserves-ap fn-ovrwp-number-preserves-ap fn-ovrwp-probe-preserves-ap) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))

(local (defthm fn-ovrwp-fields-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-fields fields h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-fields-position))))

(local (defthm fn-ovrwp-served-xref-position
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-served-xref server ms idp h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrwp-octets-position-linear fn-ovrwp-string-position-linear fn-ovrwp-decimal-field-position-linear fn-ovrwp-decimal-position-linear fn-ovrwp-xref-position-linear fn-ovrwp-decimal-field-tab-position-linear fn-ovrwp-decimal-tab-position-linear fn-ovrwp-fields-position-linear natp-compound-recognizer fn-ovrwp-nfix-natural fn-ovrwp-natural-nfix fn-ovr-put-served-xref fn-ovrwp-octets-position fn-ovrwp-string-position fn-ovrwp-decimal-field-position fn-ovrwp-decimal-position fn-ovrwp-xref-position fn-ovrwp-decimal-field-tab-position fn-ovrwp-decimal-tab-position fn-ovrwp-fields-position fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap fn-ovrwp-column-line-preserves-ap fn-ovrwp-number-preserves-ap fn-ovrwp-probe-preserves-ap) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))

(local (defthm fn-ovrwp-served-xref-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-served-xref server ms idp h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-served-xref-position))))

(local (defthm fn-ovrwp-column-line-position
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-column-line n nov octets body server ms idp h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrwp-octets-position-linear fn-ovrwp-string-position-linear fn-ovrwp-decimal-field-position-linear fn-ovrwp-decimal-position-linear fn-ovrwp-xref-position-linear fn-ovrwp-decimal-field-tab-position-linear fn-ovrwp-decimal-tab-position-linear fn-ovrwp-fields-position-linear fn-ovrwp-served-xref-position-linear natp-compound-recognizer fn-ovrwp-nfix-natural fn-ovrwp-natural-nfix fn-ovr-put-column-line fn-ovrwp-octets-position fn-ovrwp-string-position fn-ovrwp-decimal-field-position fn-ovrwp-decimal-position fn-ovrwp-xref-position fn-ovrwp-decimal-field-tab-position fn-ovrwp-decimal-tab-position fn-ovrwp-fields-position fn-ovrwp-served-xref-position fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap fn-ovrwp-column-line-preserves-ap fn-ovrwp-number-preserves-ap fn-ovrwp-probe-preserves-ap) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))

(local (defthm fn-ovrwp-column-line-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-column-line n nov octets body server ms idp h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-column-line-position))))

(local (defthm fn-ovrwp-number-position
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-number group n server v h j limit s fn-arena fn-cat))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrwp-octets-position-linear fn-ovrwp-string-position-linear fn-ovrwp-decimal-field-position-linear fn-ovrwp-decimal-position-linear fn-ovrwp-xref-position-linear fn-ovrwp-decimal-field-tab-position-linear fn-ovrwp-decimal-tab-position-linear fn-ovrwp-fields-position-linear fn-ovrwp-served-xref-position-linear fn-ovrwp-column-line-position-linear natp-compound-recognizer fn-ovrwp-nfix-natural fn-ovrwp-natural-nfix fn-ovr-put-number fn-ovrwp-octets-position fn-ovrwp-string-position fn-ovrwp-decimal-field-position fn-ovrwp-decimal-position fn-ovrwp-xref-position fn-ovrwp-decimal-field-tab-position fn-ovrwp-decimal-tab-position fn-ovrwp-fields-position fn-ovrwp-served-xref-position fn-ovrwp-column-line-position fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap fn-ovrwp-column-line-preserves-ap fn-ovrwp-number-preserves-ap fn-ovrwp-probe-preserves-ap) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))

(local (defthm fn-ovrwp-number-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-number group n server v h j limit s fn-arena fn-cat))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-number-position))))

(defthm fn-ovrwp-probe-position
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-probe group number server v h j limit s fn-arena fn-cat))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrwp-octets-position-linear fn-ovrwp-string-position-linear fn-ovrwp-decimal-field-position-linear fn-ovrwp-decimal-position-linear fn-ovrwp-xref-position-linear fn-ovrwp-decimal-field-tab-position-linear fn-ovrwp-decimal-tab-position-linear fn-ovrwp-fields-position-linear fn-ovrwp-served-xref-position-linear fn-ovrwp-column-line-position-linear fn-ovrwp-number-position-linear natp-compound-recognizer fn-ovrwp-nfix-natural fn-ovrwp-natural-nfix fn-ovr-put-probe fn-ovrwp-octets-position fn-ovrwp-string-position fn-ovrwp-decimal-field-position fn-ovrwp-decimal-position fn-ovrwp-xref-position fn-ovrwp-decimal-field-tab-position fn-ovrwp-decimal-tab-position fn-ovrwp-fields-position fn-ovrwp-served-xref-position fn-ovrwp-column-line-position fn-ovrwp-number-position fn-ovrwp-octets-preserves-ap fn-ovrwp-string-preserves-ap fn-ovrwp-decimal-field-preserves-ap fn-ovrwp-decimal-preserves-ap fn-ovrwp-xref-preserves-ap fn-ovrwp-decimal-field-tab-preserves-ap fn-ovrwp-decimal-tab-preserves-ap fn-ovrwp-fields-preserves-ap fn-ovrwp-served-xref-preserves-ap fn-ovrwp-column-line-preserves-ap fn-ovrwp-number-preserves-ap fn-ovrwp-probe-preserves-ap) (set-difference-theories (fn-dss-measure-theory) '(natp nfix))))))

(defthm fn-ovrwp-probe-position-linear
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-probe group number server v h j limit s fn-arena fn-cat))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-probe-position)))

(local (defthm fn-ovrwp-octets-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-octets octets h j limit s))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-octets-position))))

(local (defthm fn-ovrwp-string-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-string text h j limit s))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use ((:instance fn-ovrwp-string-position (s text) (st s)))))))

(local (defthm fn-ovrwp-decimal-field-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-decimal-field n h j limit s))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-decimal-field-position))))

(local (defthm fn-ovrwp-decimal-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-decimal n h j limit s))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-decimal-position))))

(local (defthm fn-ovrwp-xref-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-xref ms all idp h j limit s))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-xref-position))))

(local (defthm fn-ovrwp-decimal-field-tab-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-decimal-field-tab-position))))

(local (defthm fn-ovrwp-decimal-tab-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-decimal-tab n h j limit s))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-decimal-tab-position))))

(local (defthm fn-ovrwp-fields-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-fields fields h j limit s))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-fields-position))))

(local (defthm fn-ovrwp-served-xref-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-served-xref server ms idp h j limit s))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-served-xref-position))))

(local (defthm fn-ovrwp-column-line-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-column-line n nov octets body server ms idp h j limit s))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-column-line-position))))

(local (defthm fn-ovrwp-number-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-number group n server v h j limit s fn-arena fn-cat))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-number-position))))

(defthm fn-ovrwp-probe-position-natural
 (implies (and (fn-rtc-st$ap s) (natp j) (<= j (nfix limit)))
   (natp (mv-nth 1 (fn-ovr-put-probe group number server v h j limit s fn-arena fn-cat))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrwp-probe-position)))

(defthm fn-ovrwp-octets-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-octets octets h j limit s))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-octets octets h j limit s))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-octets octets h j limit s))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-octets-position fn-ovrwp-octets-preserves-ap))))

(local (defthm fn-ovrwp-string-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-string text h j limit s))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-string text h j limit s))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-string text h j limit s))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use ((:instance fn-ovrwp-string-position (s text) (st s)) fn-ovrwp-string-preserves-ap)))))

(local (defthm fn-ovrwp-decimal-field-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field n h j limit s))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-decimal-field n h j limit s))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-decimal-field n h j limit s))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-decimal-field-position fn-ovrwp-decimal-field-preserves-ap)))))

(local (defthm fn-ovrwp-decimal-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal n h j limit s))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-decimal n h j limit s))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-decimal n h j limit s))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-decimal-position fn-ovrwp-decimal-preserves-ap)))))

(local (defthm fn-ovrwp-xref-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-xref ms all idp h j limit s))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-xref ms all idp h j limit s))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-xref ms all idp h j limit s))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-xref-position fn-ovrwp-xref-preserves-ap)))))

(local (defthm fn-ovrwp-decimal-field-tab-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-decimal-field-tab n h j limit s))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-decimal-field-tab-position fn-ovrwp-decimal-field-tab-preserves-ap)))))

(local (defthm fn-ovrwp-decimal-tab-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-tab n h j limit s))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-decimal-tab n h j limit s))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-decimal-tab n h j limit s))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-decimal-tab-position fn-ovrwp-decimal-tab-preserves-ap)))))

(local (defthm fn-ovrwp-fields-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-fields fields h j limit s))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-fields fields h j limit s))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-fields fields h j limit s))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-fields-position fn-ovrwp-fields-preserves-ap)))))

(local (defthm fn-ovrwp-served-xref-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-served-xref server ms idp h j limit s))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-served-xref server ms idp h j limit s))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-served-xref server ms idp h j limit s))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-served-xref-position fn-ovrwp-served-xref-preserves-ap)))))

(local (defthm fn-ovrwp-column-line-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-column-line n nov octets body server ms idp h j limit s))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-column-line n nov octets body server ms idp h j limit s))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-column-line n nov octets body server ms idp h j limit s))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-column-line-position fn-ovrwp-column-line-preserves-ap)))))

(local (defthm fn-ovrwp-number-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-number group n server v h j limit s fn-arena fn-cat))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-number group n server v h j limit s fn-arena fn-cat))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-number group n server v h j limit s fn-arena fn-cat))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-number-position fn-ovrwp-number-preserves-ap)))))

(defthm fn-ovrwp-probe-guard-output
 (implies (and (fn-rtc-st$ap s) (natp j) (unsigned-byte-p 59 limit) (<= j limit))
   (let ((j2 (mv-nth 1 (fn-ovr-put-probe group number server v h j limit s fn-arena fn-cat))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2)
          (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-probe group number server v h j limit s fn-arena fn-cat))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-put-probe group number server v h j limit s fn-arena fn-cat))))
 :hints (("Goal" :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p)
                                         (theory 'minimal-theory))
          :use (fn-ovrwp-probe-position fn-ovrwp-probe-preserves-ap))))

(verify-guards fn-ovr-put-xref
 :hints (("Goal" :do-not '(preprocess)
   :use ((:instance fn-ovrwp-octets-guard-output (octets '(32)) (j j) (s fn-rtc-st)) (:instance fn-ovrwp-string-guard-output (text (car (car ms))) (j (mv-nth 1 (fn-ovr-put-octets '(32) h j limit fn-rtc-st))) (s (mv-nth 2 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)))) (:instance fn-ovrwp-octets-guard-output (octets '(58)) (j (mv-nth 1 (fn-ovr-put-string (car (car ms)) h (mv-nth 1 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(32) h j limit fn-rtc-st))))) (s (mv-nth 2 (fn-ovr-put-string (car (car ms)) h (mv-nth 1 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)))))) (:instance fn-ovrwp-decimal-field-guard-output (n (cdr (car ms))) (j (mv-nth 1 (fn-ovr-put-octets '(58) h (mv-nth 1 (fn-ovr-put-string (car (car ms)) h (mv-nth 1 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-string (car (car ms)) h (mv-nth 1 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(32) h j limit fn-rtc-st))))))) (s (mv-nth 2 (fn-ovr-put-octets '(58) h (mv-nth 1 (fn-ovr-put-string (car (car ms)) h (mv-nth 1 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-string (car (car ms)) h (mv-nth 1 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(32) h j limit fn-rtc-st)))))))))
   :in-theory (union-theories '(fn-dsw-st-p-is-abstract-recognizer
                 unsigned-byte-p integer-range-p natp nfix fn-ovr-xref-len-natp
                 (:type-prescription fn-ovr-xref-len) natp-compound-recognizer)
                (theory 'minimal-theory)))))

(verify-guards fn-ovr-put-decimal-field-tab
 :hints (("Goal" :do-not '(preprocess) :use ((:instance fn-ovrwp-decimal-field-guard-output (n n) (j j) (s fn-rtc-st)) (:instance fn-ovrwp-octets-guard-output (octets '(9)) (j (mv-nth 1 (fn-ovr-put-decimal-field n h j limit fn-rtc-st))) (s (mv-nth 2 (fn-ovr-put-decimal-field n h j limit fn-rtc-st)))))
   :in-theory (union-theories '(fn-dsw-st-p-is-abstract-recognizer
     unsigned-byte-p integer-range-p natp nfix natp-compound-recognizer
     fn-ovr-column-line-len-natp (:type-prescription fn-ovr-column-line-len))
       (theory 'minimal-theory)))))

(verify-guards fn-ovr-put-decimal-tab
 :hints (("Goal" :do-not '(preprocess) :use ((:instance fn-ovrwp-decimal-guard-output (n n) (j j) (s fn-rtc-st)) (:instance fn-ovrwp-octets-guard-output (octets '(9)) (j (mv-nth 1 (fn-ovr-put-decimal n h j limit fn-rtc-st))) (s (mv-nth 2 (fn-ovr-put-decimal n h j limit fn-rtc-st)))))
   :in-theory (union-theories '(fn-dsw-st-p-is-abstract-recognizer
     unsigned-byte-p integer-range-p natp nfix natp-compound-recognizer
     fn-ovr-column-line-len-natp (:type-prescription fn-ovr-column-line-len))
       (theory 'minimal-theory)))))

(verify-guards fn-ovr-put-fields
 :hints (("Goal" :do-not '(preprocess) :use ((:instance fn-ovrwp-string-guard-output (text (car fields)) (j j) (s fn-rtc-st)) (:instance fn-ovrwp-octets-guard-output (octets '(9)) (j (mv-nth 1 (fn-ovr-put-string (car fields) h j limit fn-rtc-st))) (s (mv-nth 2 (fn-ovr-put-string (car fields) h j limit fn-rtc-st)))))
   :in-theory (union-theories '(fn-dsw-st-p-is-abstract-recognizer
     unsigned-byte-p integer-range-p natp nfix natp-compound-recognizer
     fn-ovr-column-line-len-natp (:type-prescription fn-ovr-column-line-len))
       (theory 'minimal-theory)))))

(verify-guards fn-ovr-put-served-xref
 :hints (("Goal" :do-not '(preprocess) :use ((:instance fn-ovrwp-octets-guard-output (octets '(9)) (j j) (s fn-rtc-st)) (:instance fn-ovrwp-octets-guard-output (octets *fn-xref-name*) (j (mv-nth 1 (fn-ovr-put-octets '(9) h j limit fn-rtc-st))) (s (mv-nth 2 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)))) (:instance fn-ovrwp-octets-guard-output (octets (if (true-listp server) server nil)) (j (mv-nth 1 (fn-ovr-put-octets *fn-xref-name* h (mv-nth 1 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(9) h j limit fn-rtc-st))))) (s (mv-nth 2 (fn-ovr-put-octets *fn-xref-name* h (mv-nth 1 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)))))) (:instance fn-ovrwp-xref-guard-output (ms ms) (all ms) (idp idp) (j (mv-nth 1 (fn-ovr-put-octets (if (true-listp server) server nil) h (mv-nth 1 (fn-ovr-put-octets *fn-xref-name* h (mv-nth 1 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-octets *fn-xref-name* h (mv-nth 1 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(9) h j limit fn-rtc-st))))))) (s (mv-nth 2 (fn-ovr-put-octets (if (true-listp server) server nil) h (mv-nth 1 (fn-ovr-put-octets *fn-xref-name* h (mv-nth 1 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-octets *fn-xref-name* h (mv-nth 1 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-octets '(9) h j limit fn-rtc-st)))))))))
   :in-theory (union-theories '(fn-dsw-st-p-is-abstract-recognizer
     unsigned-byte-p integer-range-p natp nfix natp-compound-recognizer
     fn-ovr-column-line-len-natp (:type-prescription fn-ovr-column-line-len))
       (theory 'minimal-theory)))))

(verify-guards fn-ovr-put-column-line
 :hints (("Goal" :do-not '(preprocess) :use ((:instance fn-ovrwp-decimal-field-tab-guard-output (n n) (j j) (s fn-rtc-st)) (:instance fn-ovrwp-fields-guard-output (fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov))) (j (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st))) (s (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) (:instance fn-ovrwp-decimal-tab-guard-output (n octets) (j (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st))))) (s (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))) (:instance fn-ovrwp-decimal-guard-output (n body) (j (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st))))))) (s (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))))) (:instance fn-ovrwp-served-xref-guard-output (server server) (ms ms) (idp idp) (j (mv-nth 1 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st))))))))) (s (mv-nth 2 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))))))) (:instance fn-ovrwp-octets-guard-output (octets '(13 10)) (j (mv-nth 1 (fn-ovr-put-served-xref server ms idp h (mv-nth 1 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))))) limit (mv-nth 2 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st))))))))))) (s (mv-nth 2 (fn-ovr-put-served-xref server ms idp h (mv-nth 1 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))))) limit (mv-nth 2 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))))))))))))
   :in-theory (union-theories '(fn-dsw-st-p-is-abstract-recognizer
     unsigned-byte-p integer-range-p natp nfix natp-compound-recognizer
     fn-ovr-column-line-len-natp (:type-prescription fn-ovr-column-line-len))
       (theory 'minimal-theory)))))

(verify-guards fn-ovr-put-number
 :hints (("Goal" :in-theory
  (e/d (natp nfix unsigned-byte-p integer-range-p fn-dsw-st-p-is-abstract-recognizer)
       (fn-ovr-put-column-line fn-ovr-put-octets fn-ovr-number-len fn-ovr-available-article
        fn-scat-available-article fn-nov-served-line fn-nov-line fn-nov-overview fn-nntp-crlf
        fn-scol-facts fn-hf-nov fn-ovr-msgid-okp fn-nntp-article-length fn-nntp-article-tombstonep
        fn-ovr-number-len-is-len fn-ovr-available-article-is-available)))))

(verify-guards fn-ovr-put-probe
 :hints (("Goal" :in-theory
  (e/d (natp nfix unsigned-byte-p integer-range-p fn-dsw-st-p-is-abstract-recognizer)
       (fn-ovr-put-number fn-ovr-number-len fn-ovr-probe-len fn-ovr-probe-len-is-the-length
        fn-cnx-view-seq fn-cat-at fn-held-number-in fn-record-msgid fn-ovr-msgid-okp
        fn-ovr-msgid-okp-is-idp)))))


; Writer refinements compose C20 splices at their returned positions.
; The quantum uses only the probe refinement and position/octet contracts.
(defthm fn-ovrqp-octets-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (fn-cbor-octet-listp data) (<= (+ j (len data)) limit))
  (equal (fn-ovr-put-octets data h j limit st)
         (mv :done (+ j (len data)) (fn-rtc-st$a-splice h j data st))))
 :hints (("Goal" :use ((:instance fn-ovrqp-room-after-splice (s st)))
   :in-theory (union-theories '(fn-ovr-put-octets fn-dsw-append-is-splice fn-ovrqp-room-properties
           fn-ovrqp-nfix-natural) (theory 'minimal-theory)))))
(local (defthm fn-ovrqp-slice-whole
 (implies (true-listp data) (equal (fn-oct-slice-list 0 (len data) data) data))
 :hints (("Goal" :use ((:instance fn-oct-slice-list-is-take-nthcdr (i 0) (n (len data)) (fn-octets data)))
    :in-theory (e/d (take nthcdr) (fn-oct-slice-list fn-oct-slice-list-is-take-nthcdr))))))
(local (defthm fn-ovrqp-string-aux-octets
 (fn-cbor-octet-listp (fn-nntp-string-octets-aux cs))
 :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux fn-cbor-octet-listp fn-cbor-octetp)))))
(local (defthm fn-ovrqp-string-octets
 (and (true-listp (fn-nntp-string-octets text)) (fn-cbor-octet-listp (fn-nntp-string-octets text)))
 :hints (("Goal" :in-theory (enable fn-nntp-string-octets fn-nntp-string-octets-aux fn-cbor-octet-listp fn-cbor-octetp)))))
(local (defthm fn-ovrqp-string-length
 (implies (stringp text) (equal (length text) (len (fn-nntp-string-octets text))))
 :hints (("Goal" :use ((:instance fn-ovr-len-string-octets (s text)))
    :in-theory (union-theories '(fn-ovr-string-len) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-string-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (<= (+ j (len (fn-nntp-string-octets text))) limit))
  (equal (fn-ovr-put-string text h j limit st)
         (mv :done (+ j (len (fn-nntp-string-octets text)))
                   (fn-rtc-st$a-splice h j (fn-nntp-string-octets text) st))))
 :hints (("Goal" :use ((:instance fn-ovrqp-room-after-splice (data (fn-nntp-string-octets text)) (s st)))
    :in-theory (union-theories '(fn-ovr-put-string fn-ovr-wcopy-string-is-the-source-splice
       fn-ovrqp-slice-whole fn-ovrqp-string-octets fn-ovrqp-string-aux-octets fn-cbor-octet-listp-implies-true-listp fn-ovrqp-room-properties fn-ovrqp-nfix-natural
       fn-ovr-string-len-is-len fn-ovrqp-string-length fn-dsw-append-is-splice
       fn-nntp-string-octets (:type-prescription len) (:type-prescription natp))
      (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-explode-append
  (implies (and (posp n) (true-listp acc))
    (equal (explode-nonnegative-integer n 10 (append acc tail))
           (append (explode-nonnegative-integer n 10 acc) tail)))
  :hints (("Goal" :induct (explode-nonnegative-integer n 10 acc)
           :in-theory (e/d (explode-nonnegative-integer) (digit-to-char floor mod fn-rtc-st$ap fn-rtc-shapep))))))
(local (defthm fn-ovrqp-string-aux-append
  (equal (fn-nntp-string-octets-aux (append a b))
         (append (fn-nntp-string-octets-aux a) (fn-nntp-string-octets-aux b)))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))
(local (defthm fn-ovrqp-digit-code
  (implies (and (natp d) (< d 10)) (equal (char-code (digit-to-char d)) (+ 48 d)))
  :hints (("Goal" :in-theory (enable digit-to-char) :cases ((equal d 0) (equal d 1) (equal d 2)
                      (equal d 3) (equal d 4) (equal d 5) (equal d 6) (equal d 7) (equal d 8) (equal d 9))))))
(local (defthm fn-ovrqp-decimal-small
  (implies (and (natp n) (< n 10)) (equal (fn-nntp-decimal n) (list (+ 48 n))))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal fn-nntp-decimal-rev explode-nonnegative-integer
                                    fn-nntp-string-octets-aux)))))
(local (defthm fn-ovrqp-decimal-step
  (implies (and (natp n) (<= 10 n))
    (equal (fn-nntp-decimal n) (append (fn-nntp-decimal (floor n 10)) (list (+ 48 (mod n 10))))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-decimal fn-nntp-decimal-rev fn-nntp-string-octets-aux)
                                    (explode-nonnegative-integer fn-rtc-st$ap fn-rtc-shapep))
           :expand ((explode-nonnegative-integer n 10 nil))
           :use ((:instance fn-ovrqp-explode-append (n (floor n 10)) (acc nil) (tail (list (digit-to-char (mod n 10))))))))))
(local (defthm fn-ovrqp-decimal-non-natural
  (implies (not (natp n)) (equal (fn-nntp-decimal n) nil))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal)))))
(local (defthm fn-ovrqp-decimal-count-is-length
  (equal (fn-dsw-decimal-count n) (len (fn-nntp-decimal n)))
  :hints (("Goal" :induct (fn-dsw-decimal-count n)
           :in-theory (e/d () (fn-nntp-decimal fn-nntp-decimal-rev fn-rtc-st$ap fn-rtc-shapep))
           :expand ((fn-dsw-decimal-count n)))
          ("Subgoal *1/2" :in-theory (enable fn-nntp-decimal)))))
(local (defthm fn-ovrqp-decimal-octets
 (fn-cbor-octet-listp (fn-nntp-decimal n))
 :hints (("Goal" :in-theory (enable fn-nntp-decimal fn-nntp-decimal-rev fn-ovrqp-string-aux-octets)))))
(local (defthm fn-ovrqp-decimal-field-octets
 (fn-cbor-octet-listp (fn-nntp-decimal-field n))
 :hints (("Goal" :in-theory (e/d (fn-nntp-decimal-field) (fn-nntp-decimal))))))
(local (defthm fn-ovrqp-decimal-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (<= (+ j (len (fn-nntp-decimal n))) limit))
  (equal (fn-ovr-put-decimal n h j limit st)
         (mv :done (+ j (len (fn-nntp-decimal n))) (fn-rtc-st$a-splice h j (fn-nntp-decimal n) st))))
 :hints (("Goal" :use ((:instance fn-ovrqp-room-after-splice (data (fn-nntp-decimal n)) (s st)))
  :in-theory (union-theories '(fn-ovr-put-decimal fn-dsw-decimal-is-splice fn-ovrqp-decimal-count-is-length
      fn-ovrqp-decimal-octets fn-ovrqp-decimal-field-octets fn-ovrqp-room-properties fn-ovrqp-nfix-natural) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-decimal-token-append
 (equal (fn-nntp-decimal-tokenp (append a b))
        (and (fn-nntp-decimal-tokenp a) (fn-nntp-decimal-tokenp b)))
 :hints (("Goal" :induct (append a b) :in-theory (enable fn-nntp-decimal-tokenp)))))
(local (defthm fn-ovrqp-decimal-token
 (implies (natp n) (and (consp (fn-nntp-decimal n)) (fn-nntp-decimal-tokenp (fn-nntp-decimal n))))
 :hints (("Goal" :induct (fn-dsw-decimal-count n)
   :in-theory (e/d (fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)
       (fn-nntp-decimal fn-nntp-decimal-rev fn-rtc-st$ap fn-rtc-shapep))
    :expand ((fn-dsw-decimal-count n))))))
(local (defthm fn-ovrqp-decimal-field-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (<= (+ j (len (fn-nntp-decimal-field n))) limit))
  (equal (fn-ovr-put-decimal-field n h j limit st)
         (mv :done (+ j (len (fn-nntp-decimal-field n))) (fn-rtc-st$a-splice h j (fn-nntp-decimal-field n) st))))
 :hints (("Goal" :use ((:instance fn-ovrqp-room-after-splice (data (fn-nntp-decimal-field n)) (s st)))
  :in-theory (union-theories '(fn-ovr-put-decimal-field fn-nntp-decimal-field fn-ovrqp-decimal-token fn-ovrqp-decimal-non-natural fn-dsw-decimal-is-splice
       fn-dsw-append-is-splice fn-ovrqp-decimal-count-is-length fn-ovr-decimal-field-len-is-len
       fn-ovrqp-decimal-octets fn-ovrqp-decimal-field-octets fn-ovrqp-room-properties fn-ovrqp-nfix-natural natp len car-cons cdr-cons
       (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-decimal-field-tab-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (<= (+ j (len (append (fn-nntp-decimal-field n) '(9)))) limit))
  (equal (fn-ovr-put-decimal-field-tab n h j limit st)
         (mv :done (+ j (len (append (fn-nntp-decimal-field n) '(9))))
            (fn-rtc-st$a-splice h j (append (fn-nntp-decimal-field n) '(9)) st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
   '(fn-ovr-put-decimal-field-tab fn-ovrqp-decimal-field-is-splice fn-ovrqp-octets-is-splice
     fn-ovrqp-room-after-splice fn-ovrqp-room-properties fn-ovrqp-splice-compose
     fn-ovrqp-decimal-octets fn-ovrqp-decimal-field-octets
     fn-ovrqp-len-append fn-ovrqp-nfix-natural
     associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2 mv-nth zp car-cons cdr-cons len (:type-prescription len)
     (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-decimal-tab-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (<= (+ j (len (append (fn-nntp-decimal n) '(9)))) limit))
  (equal (fn-ovr-put-decimal-tab n h j limit st)
         (mv :done (+ j (len (append (fn-nntp-decimal n) '(9))))
            (fn-rtc-st$a-splice h j (append (fn-nntp-decimal n) '(9)) st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
   '(fn-ovr-put-decimal-tab fn-ovrqp-decimal-is-splice fn-ovrqp-octets-is-splice
     fn-ovrqp-room-after-splice fn-ovrqp-room-properties fn-ovrqp-splice-compose
     fn-ovrqp-decimal-octets fn-ovrqp-decimal-field-octets
     fn-ovrqp-len-append fn-ovrqp-nfix-natural
     associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2 mv-nth zp car-cons cdr-cons len (:type-prescription len)
     (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defun fn-ovrqp-fields-octets (fields)
 (if (consp fields) (append (fn-nntp-string-octets (car fields)) '(9) (fn-ovrqp-fields-octets (cdr fields))) nil)))
(local (defthm fn-ovrqp-fields-octets-type
 (and (fn-cbor-octet-listp (fn-ovrqp-fields-octets fields)) (true-listp (fn-ovrqp-fields-octets fields)))
 :hints (("Goal" :induct (fn-ovrqp-fields-octets fields)
    :in-theory (union-theories '(fn-ovrqp-fields-octets fn-ovrqp-string-octets
      fn-ovrqp-octets-append fn-ovrqp-octets-cons (:executable-counterpart fn-cbor-octetp) binary-append car-cons cdr-cons
      (:type-prescription fn-ovrqp-fields-octets) (:type-prescription true-listp-append)
      (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-fields-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (<= (+ j (len (fn-ovrqp-fields-octets fields))) limit))
  (equal (fn-ovr-put-fields fields h j limit st)
    (mv :done (+ j (len (fn-ovrqp-fields-octets fields)))
        (fn-rtc-st$a-splice h j (fn-ovrqp-fields-octets fields) st))))
 :hints (("Goal" :induct (fn-ovr-put-fields fields h j limit st)
    :in-theory (union-theories '(fn-ovr-put-fields fn-ovrqp-fields-octets fn-ovrqp-fields-octets-type
      fn-ovrqp-string-is-splice fn-ovrqp-string-octets fn-ovrqp-octets-is-splice fn-ovrqp-empty-splice
      fn-ovrqp-room-properties fn-ovrqp-room-after-splice fn-ovrqp-compose-at-splice-position fn-ovrqp-room-at-splice-position fn-ovrqp-append-associates natp-compound-recognizer fix fn-ovrqp-len-append
      fn-ovrqp-nfix-natural fn-cbor-octet-listp-implies-true-listp fn-rtc-c-l-octets-append
      associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2
      mv-nth zp car-cons cdr-cons len binary-append (:type-prescription len)
      (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-xref-octets
 (fn-cbor-octet-listp (fn-xref-locations pairs))
 :hints (("Goal" :in-theory (e/d (fn-xref-locations)
    (fn-nntp-string-octets fn-nntp-decimal-field fn-rtc-st$ap fn-rtc-shapep))))))
(local (defthm fn-ovrqp-xref-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st)
               (<= (+ j (len (fn-xref-locations (fn-xref-pairs-of ms article)))) limit))
  (equal (fn-ovr-put-xref ms (fn-article-memberships article)
                            (fn-scat-msgid-idp (fn-article-msgid article)) h j limit st)
   (mv :done (+ j (len (fn-xref-locations (fn-xref-pairs-of ms article))))
       (fn-rtc-st$a-splice h j (fn-xref-locations (fn-xref-pairs-of ms article)) st))))
 :hints (("Goal" :induct (fn-ovr-put-xref ms (fn-article-memberships article)
                           (fn-scat-msgid-idp (fn-article-msgid article)) h j limit st)
  :in-theory (union-theories '(fn-ovr-put-xref fn-xref-pairs-of fn-xref-locations fn-ag-car fn-ag-cdr
      fn-ovr-xref-wordp-is-wordp fn-ovr-article-number-is-number fn-ovr-xref-len-is-len
      fn-ovrqp-octets-is-splice fn-ovrqp-string-is-splice fn-ovrqp-decimal-field-is-splice
      fn-ovrqp-string-octets fn-ovrqp-decimal-field-octets fn-ovrqp-xref-octets fn-ovrqp-empty-splice
      fn-ovrqp-room-properties fn-ovrqp-room-after-splice fn-ovrqp-room-at-splice-position
      fn-ovrqp-compose-at-splice-position fn-ovrqp-append-associates fn-ovrqp-len-append
      fn-ovrqp-nfix-natural fn-ovrqp-octets-cons (:executable-counterpart fn-cbor-octetp) fn-cbor-octet-listp-implies-true-listp fn-rtc-c-l-octets-append
      associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2
      natp-compound-recognizer fix mv-nth zp car-cons cdr-cons len binary-append (:type-prescription len)
      (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-served-xref-octets
 (implies (fn-cbor-octet-listp server)
  (fn-cbor-octet-listp (if server (cons 9 (fn-xref-field server (fn-xref-pairs article))) nil)))
 :hints (("Goal" :in-theory (union-theories '(fn-xref-field fn-xref-pairs fn-ovrqp-xref-octets
      fn-ovrqp-octets-cons fn-cbor-octet-listp-implies-true-listp fn-rtc-c-l-octets-append
      (:executable-counterpart fn-cbor-octetp) (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-served-xref-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (fn-cbor-octet-listp server)
  (<= (+ j (len (if server (cons 9 (fn-xref-field server (fn-xref-pairs article))) nil))) limit))
  (equal (fn-ovr-put-served-xref server (fn-article-memberships article)
             (fn-scat-msgid-idp (fn-article-msgid article)) h j limit st)
   (mv :done (+ j (len (if server (cons 9 (fn-xref-field server (fn-xref-pairs article))) nil)))
    (fn-rtc-st$a-splice h j (if server (cons 9 (fn-xref-field server (fn-xref-pairs article))) nil) st))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories '(fn-ovr-put-served-xref fn-xref-field fn-xref-pairs
      fn-ovrqp-octets-is-splice fn-ovrqp-xref-is-splice fn-ovrqp-xref-octets fn-ovrqp-empty-splice
      fn-ovrqp-room-properties fn-ovrqp-room-after-splice fn-ovrqp-room-at-splice-position
      fn-ovrqp-compose-at-splice-position fn-ovrqp-append-associates fn-ovrqp-len-append
      fn-ovrqp-nfix-natural fn-ovrqp-octets-cons fn-cbor-octet-listp-implies-true-listp fn-rtc-c-l-octets-append
      fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2
      natp-compound-recognizer fix mv-nth zp car-cons cdr-cons len binary-append (:type-prescription len)
      (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-cbor-octetp))
     (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-column-octets
 (implies (fn-cbor-octet-listp server)
  (fn-cbor-octet-listp (fn-nntp-crlf (fn-nov-served-line n (fn-ovr-column-over nov octets body) server article))))
 :hints (("Goal" :in-theory (e/d (fn-nntp-crlf fn-nov-served-line fn-nov-line fn-ovr-column-over
       fn-nov-subject fn-nov-from fn-nov-date fn-nov-msgid fn-nov-references fn-nov-bytes fn-nov-lines
       fn-nntp-append-pieces fn-xref-field fn-xref-pairs)
    (fn-nntp-string-octets fn-nntp-decimal fn-nntp-decimal-field fn-xref-locations
      fn-xref-pairs-of fn-rtc-st$ap fn-rtc-shapep))))))
(local (defthm fn-ovrqp-xref-field-octets
 (implies (fn-cbor-octet-listp server) (fn-cbor-octet-listp (fn-xref-field server pairs)))
 :hints (("Goal" :in-theory (union-theories '(fn-xref-field fn-ovrqp-xref-octets
   fn-ovrqp-octets-cons fn-cbor-octet-listp-implies-true-listp fn-rtc-c-l-octets-append
   binary-append car-cons cdr-cons (:executable-counterpart fn-cbor-octetp)
   (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-column-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (fn-cbor-octet-listp server)
   (<= (+ j (len (fn-nntp-crlf (fn-nov-served-line n (fn-ovr-column-over nov octets body) server article)))) limit))
  (equal (fn-ovr-put-column-line n nov octets body server
                   (fn-article-memberships article) (fn-scat-msgid-idp (fn-article-msgid article)) h j limit st)
    (mv :done (+ j (len (fn-nntp-crlf (fn-nov-served-line n (fn-ovr-column-over nov octets body) server article))))
      (fn-rtc-st$a-splice h j (fn-nntp-crlf (fn-nov-served-line n (fn-ovr-column-over nov octets body) server article)) st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
  '(fn-ovr-put-column-line fn-ovr-column-line-len-is-len fn-ovrqp-column-octets fn-ovr-record-octets-is-nntp-octets
    fn-ovrqp-decimal-field-tab-is-splice fn-ovrqp-fields-is-splice fn-ovrqp-fields-octets
    fn-ovrqp-decimal-tab-is-splice fn-ovrqp-decimal-is-splice fn-ovrqp-served-xref-is-splice
    fn-ovrqp-octets-is-splice fn-ovrqp-string-octets fn-ovrqp-decimal-octets fn-ovrqp-decimal-field-octets
    fn-ovrqp-fields-octets-type fn-ovrqp-served-xref-octets fn-ovrqp-xref-octets fn-ovrqp-xref-field-octets
    fn-nntp-crlf fn-nov-served-line fn-nov-line fn-ovr-column-over
    fn-nov-subject fn-nov-from fn-nov-date fn-nov-msgid fn-nov-references fn-nov-bytes fn-nov-lines
    fn-nntp-append-pieces
    fn-ovrqp-room-properties fn-ovrqp-room-after-splice fn-ovrqp-room-at-splice-position
    fn-ovrqp-compose-at-splice-position fn-ovrqp-append-associates fn-ovrqp-len-append
    fn-ovrqp-nfix-natural fn-ovrqp-octets-cons fn-cbor-octet-listp-implies-true-listp fn-rtc-c-l-octets-append
    fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2
    natp-compound-recognizer fix mv-nth zp car-cons cdr-cons len binary-append (:type-prescription len)
    (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-cbor-octetp))
    (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-decimal-field-not-dot
   (not (equal (car (fn-nntp-decimal-field n)) 46))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal-field fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)))))
(local (defthm fn-ovrqp-decimal-field-consp
   (consp (fn-nntp-decimal-field n))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal-field)))))
(local (defthm fn-ovrqp-car-append-consp
   (implies (consp a) (equal (car (append a b)) (car a)))))
(local (defthm fn-ovrqp-nov-line-not-dot
   (not (equal (car (fn-nov-line n over)) 46))
   :hints (("Goal" :in-theory (e/d (fn-nov-line fn-nntp-append-pieces) (fn-nntp-decimal-field))))))
(local (defthm fn-ovrqp-served-line-not-dot
   (not (equal (car (fn-nov-served-line n over server article)) 46))
   :hints (("Goal" :in-theory (e/d (fn-nov-served-line) (fn-nov-line))
            :cases ((consp (fn-nov-line n over)))))))
(local (defthm fn-ovrqp-stuff-one
   (implies (not (equal (car line) 46))
            (equal (fn-nntp-stuff-lines (list line)) (fn-nntp-crlf line)))
   :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines fn-wire-stuff-line)))))
(local (defthm fn-ovrqp-scol-overview-of-facts
   (implies (fn-scol-facts article fn-cat)
            (equal (fn-scol-overview-of article fn-arena fn-cat)
                   (let ((facts (fn-scol-facts article fn-cat)))
                     (if (fn-hnov-ok (fn-hf-nov facts))
                         (fn-ovr-column-over (fn-hf-nov facts) (fn-nntp-article-length article fn-arena)
                                             (fn-hf-body-lines facts))
                       (list :error)))))
   :hints (("Goal" :in-theory (enable fn-scol-overview-of fn-scol-nov-overview fn-ovr-column-over)))))
(local (defthm fn-ovrqp-scol-overview-of-no-facts
   (implies (not (fn-scol-facts article fn-cat))
            (equal (fn-scol-overview-of article fn-arena fn-cat)
                   (fn-nov-overview article fn-arena)))
   :hints (("Goal" :in-theory (enable fn-scol-overview-of)))))
(local (defthm fn-ovrqp-column-over-okp
   (fn-nov-okp (fn-ovr-column-over nov octets body))
   :hints (("Goal" :in-theory (enable fn-nov-okp fn-ovr-column-over)))))
(local (defthm fn-ovrqp-served-lines-nil
  (equal (fn-nov-served-lines-for-numbers-cat group nil server v fn-arena fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-nov-served-lines-for-numbers-cat)))))
(local (defthm fn-ovrqp-lines-nil
  (equal (fn-nov-lines-for-numbers-cat group nil v fn-arena fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-nov-lines-for-numbers-cat)))))
(local (defthm fn-ovrqp-stuff-nil
  (equal (fn-nntp-stuff-lines nil) nil)
  :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines)))))
(local (defthm fn-ovrqp-number-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (natp v) (fn-cbor-octet-listp server)
  (<= (+ j (len (fn-nntp-stuff-lines
      (if server (fn-nov-served-lines-for-numbers-cat group (list n) server v fn-arena fn-cat)
        (fn-nov-lines-for-numbers-cat group (list n) v fn-arena fn-cat))))) limit))
  (equal (fn-ovr-put-number group n server v h j limit st fn-arena fn-cat)
   (mv :done (+ j (len (fn-nntp-stuff-lines
      (if server (fn-nov-served-lines-for-numbers-cat group (list n) server v fn-arena fn-cat)
        (fn-nov-lines-for-numbers-cat group (list n) v fn-arena fn-cat)))))
     (fn-rtc-st$a-splice h j (fn-nntp-stuff-lines
      (if server (fn-nov-served-lines-for-numbers-cat group (list n) server v fn-arena fn-cat)
        (fn-nov-lines-for-numbers-cat group (list n) v fn-arena fn-cat))) st))))
 :hints (("Goal" :in-theory (e/d (fn-ovr-put-number fn-nov-served-lines-for-numbers-cat
       fn-nov-lines-for-numbers-cat fn-scol-tombstonep fn-ovr-number-len-is-len)
    (fn-ovr-put-column-line fn-ovr-put-octets fn-nov-served-line fn-nov-line fn-nov-overview fn-hf-nov
      fn-scol-facts fn-scat-available-article fn-ovr-available-article fn-nntp-article-tombstonep
      fn-nntp-stuff-lines fn-nntp-crlf fn-scol-overview-of fn-ovr-column-over fn-nntp-article-length
      fn-ovr-msgid-okp fn-ovr-number-len fn-rtc-st$ap fn-rtc-shapep fn-rtc-st$a-splice
      fn-rtc-splice-okp fn-ovrqp-roomp))))))
(defthm fn-ovrqp-probe-is-splice
 (implies (and (fn-ovrqp-roomp h j limit st) (natp v) (natp number) (fn-cbor-octet-listp server)
              (<= (+ j (len (fn-ovr-probe-octets group number server v fn-arena fn-cat))) limit))
  (equal (fn-ovr-put-probe group number server v h j limit st fn-arena fn-cat)
   (mv :done (+ j (len (fn-ovr-probe-octets group number server v fn-arena fn-cat)))
    (fn-rtc-st$a-splice h j (fn-ovr-probe-octets group number server v fn-arena fn-cat) st))))
 :hints (("Goal" :in-theory (e/d (fn-ovr-put-probe fn-ovr-probe-octets fn-ovw-lines fn-scat-range-keep
                                  fn-ovr-msgid-okp-is-idp fn-ovr-probe-len-is-the-length)
      (fn-ovr-put-number fn-nov-served-lines-for-numbers-cat fn-nov-lines-for-numbers-cat
       fn-cnx-view-seq fn-held-number-in fn-scat-msgid-idp fn-ovr-msgid-okp fn-nntp-stuff-lines
       fn-ovr-probe-len fn-ovr-number-len fn-rtc-st$ap fn-rtc-shapep fn-rtc-st$a-splice fn-rtc-splice-okp fn-ovrqp-roomp))
  :expand ((fn-cnx-range-aux group number number v fn-cat)
           (fn-cnx-range-aux group (+ 1 number) number v fn-cat)))))
(local (defthm fn-ovrqp-number-octets
 (implies (and (natp v) (fn-cbor-octet-listp server))
   (fn-cbor-octet-listp (fn-nntp-stuff-lines
     (if server (fn-nov-served-lines-for-numbers-cat group (list n) server v fn-arena fn-cat)
       (fn-nov-lines-for-numbers-cat group (list n) v fn-arena fn-cat)))))
 :hints (("Goal" :in-theory (e/d (fn-nov-served-lines-for-numbers-cat fn-nov-lines-for-numbers-cat fn-scol-tombstonep)
    (fn-nov-served-line fn-nov-line fn-nov-overview fn-hf-nov fn-scol-facts fn-scat-available-article
     fn-nntp-article-tombstonep fn-nntp-stuff-lines fn-nntp-crlf fn-scol-overview-of fn-ovr-column-over
     fn-nntp-article-length fn-rtc-st$ap fn-rtc-shapep))))))
(defthm fn-ovrqp-probe-octets
 (implies (and (natp v) (natp number) (fn-cbor-octet-listp server))
   (fn-cbor-octet-listp (fn-ovr-probe-octets group number server v fn-arena fn-cat)))
 :hints (("Goal" :in-theory (e/d (fn-ovr-probe-octets fn-ovw-lines fn-scat-range-keep)
      (fn-nov-served-lines-for-numbers-cat fn-nov-lines-for-numbers-cat
       fn-cnx-view-seq fn-held-number-in fn-scat-msgid-idp fn-nntp-stuff-lines fn-rtc-st$ap fn-rtc-shapep))
   :expand ((fn-cnx-range-aux group number number v fn-cat)
           (fn-cnx-range-aux group (+ 1 number) number v fn-cat)))))
(local (defthm fn-ovrqp-octets-position
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-octets octets h j limit st))))
     (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :in-theory (union-theories '(fn-ovr-put-octets fn-dsw-append nfix natp len car-cons cdr-cons)
                   (fn-dss-measure-theory))))))
(local (defthm fn-ovrqp-octets-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-octets octets h j limit st))))
     (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :use fn-ovrqp-octets-position :in-theory (theory 'minimal-theory)))))
(local (defthm fn-ovrup-string-position
 (implies (and (natp j) (<= j (nfix limit)))
  (let ((j2 (mv-nth 1 (fn-ovr-put-string text h j limit st))))
   (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
   '(fn-ovr-put-string fn-ovr-wcopy-string fn-ovr-wcopy-string-list-is-identity fn-dsw-append fn-ovrqp-slice-whole fn-ovrqp-string-length fn-ovrqp-string-octets fn-ovrqp-string-aux-octets fn-cbor-octet-listp-implies-true-listp fn-ovr-string-len-is-len fn-nntp-string-octets fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix natp nfix len car-cons cdr-cons
     (:type-prescription len) (:type-prescription fn-nntp-string-octets) (:type-prescription natp))
   (fn-dss-measure-theory))))))
(local (defthm fn-ovrup-string-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
  (let ((j2 (mv-nth 1 (fn-ovr-put-string text h j limit st))))
   (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :use fn-ovrup-string-position :in-theory (theory 'minimal-theory)))))
(local (defthm fn-ovrup-decimal-position
 (implies (and (natp j) (<= j (nfix limit)))
  (let ((j2 (mv-nth 1 (fn-ovr-put-decimal n h j limit st))))
   (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
   '(fn-ovr-put-decimal fn-dsw-decimal fn-dsw-append fn-ovrqp-decimal-count-is-length fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix natp nfix len car-cons cdr-cons
     (:type-prescription len) (:type-prescription fn-nntp-string-octets) (:type-prescription natp))
   (fn-dss-measure-theory))))))
(local (defthm fn-ovrup-decimal-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
  (let ((j2 (mv-nth 1 (fn-ovr-put-decimal n h j limit st))))
   (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :use fn-ovrup-decimal-position :in-theory (theory 'minimal-theory)))))
(local (defthm fn-ovrup-decimal-field-position
 (implies (and (natp j) (<= j (nfix limit)))
  (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field n h j limit st))))
   (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
   '(fn-ovr-put-decimal-field fn-dsw-decimal fn-dsw-append fn-ovrqp-decimal-count-is-length fn-ovr-decimal-field-len-is-len fn-nntp-decimal-field fn-ovrqp-decimal-token fn-ovrqp-decimal-non-natural fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix natp nfix len car-cons cdr-cons
     (:type-prescription len) (:type-prescription fn-nntp-string-octets) (:type-prescription natp))
   (fn-dss-measure-theory))))))
(local (defthm fn-ovrup-decimal-field-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
  (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field n h j limit st))))
   (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :use fn-ovrup-decimal-field-position :in-theory (theory 'minimal-theory)))))
(local (defthm fn-ovrup-xref-position
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-xref ms all idp h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :induct (fn-ovr-put-xref ms all idp h j limit s)
    :in-theory (union-theories '(fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-xref fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-xref-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-xref ms all idp h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrup-xref-position))))
(local (defthm fn-ovrup-decimal-field-tab-position
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-decimal-field-tab fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-decimal-field-tab-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrup-decimal-field-tab-position))))
(local (defthm fn-ovrup-decimal-tab-position
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-tab n h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-decimal-tab fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-decimal-tab-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-tab n h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrup-decimal-tab-position))))
(local (defthm fn-ovrup-fields-position
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-fields fields h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :induct (fn-ovr-put-fields fields h j limit s)
    :in-theory (union-theories '(fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear fn-ovrup-decimal-tab-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-fields fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position fn-ovrup-decimal-tab-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-fields-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-fields fields h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrup-fields-position))))
(local (defthm fn-ovrup-served-xref-position
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-served-xref server ms idp h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear fn-ovrup-decimal-tab-position-linear fn-ovrup-fields-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-served-xref fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position fn-ovrup-decimal-tab-position fn-ovrup-fields-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-served-xref-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-served-xref server ms idp h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrup-served-xref-position))))
(local (defthm fn-ovrup-column-line-position
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-column-line n nov octets body server ms idp h j limit s))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear fn-ovrup-decimal-tab-position-linear fn-ovrup-fields-position-linear fn-ovrup-served-xref-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-column-line fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position fn-ovrup-decimal-tab-position fn-ovrup-fields-position fn-ovrup-served-xref-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-column-line-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-column-line n nov octets body server ms idp h j limit s))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrup-column-line-position))))
(local (defthm fn-ovrup-number-position
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-number group n server v h j limit s fn-arena fn-cat))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear fn-ovrup-decimal-tab-position-linear fn-ovrup-fields-position-linear fn-ovrup-served-xref-position-linear fn-ovrup-column-line-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-number fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position fn-ovrup-decimal-tab-position fn-ovrup-fields-position fn-ovrup-served-xref-position fn-ovrup-column-line-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-number-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-number group n server v h j limit s fn-arena fn-cat))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrup-number-position))))
(defthm fn-ovrup-probe-position
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-probe group number server v h j limit s fn-arena fn-cat))))
      (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear fn-ovrup-decimal-tab-position-linear fn-ovrup-fields-position-linear fn-ovrup-served-xref-position-linear fn-ovrup-column-line-position-linear fn-ovrup-number-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-probe fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position fn-ovrup-decimal-tab-position fn-ovrup-fields-position fn-ovrup-served-xref-position fn-ovrup-column-line-position fn-ovrup-number-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix))))))
(defthm fn-ovrup-probe-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-probe group number server v h j limit s fn-arena fn-cat))))
      (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-ovrup-probe-position)))

; Guard-independent position advances are needed by KL2 on logical states.
(defthm fn-ovrup-octets-advance
 (implies (and (natp j) (<= j (nfix limit)))
  (<= (mv-nth 1 (fn-ovr-put-octets octets h j limit st)) (+ j (len octets))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :in-theory (union-theories '(fn-ovr-put-octets fn-dsw-append natp nfix len car-cons cdr-cons)
  (fn-dss-measure-theory)))))
(local (defthm fn-ovrup-string-advance
 (implies (and (natp j) (<= j (nfix limit)))
  (let ((j2 (mv-nth 1 (fn-ovr-put-string text h j limit st))))
   (<= j2 (+ j (fn-ovr-string-len text)))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
   '(fn-ovr-put-string fn-ovr-wcopy-string fn-ovr-wcopy-string-list-is-identity fn-dsw-append fn-ovrqp-slice-whole fn-ovrqp-string-length fn-ovrqp-string-octets fn-ovrqp-string-aux-octets fn-cbor-octet-listp-implies-true-listp fn-ovr-string-len-is-len fn-nntp-string-octets fn-ovr-decimal-len-is-len fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix natp nfix len car-cons cdr-cons
     (:type-prescription len) (:type-prescription fn-nntp-string-octets) (:type-prescription natp))
   (fn-dss-measure-theory))))))
(local (defthm fn-ovrup-decimal-advance
 (implies (and (natp j) (<= j (nfix limit)))
  (let ((j2 (mv-nth 1 (fn-ovr-put-decimal n h j limit st))))
   (<= j2 (+ j (fn-ovr-decimal-len n)))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
   '(fn-ovr-put-decimal fn-dsw-decimal fn-dsw-append fn-ovrqp-decimal-count-is-length fn-ovr-decimal-len-is-len fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix natp nfix len car-cons cdr-cons
     (:type-prescription len) (:type-prescription fn-nntp-string-octets) (:type-prescription natp))
   (fn-dss-measure-theory))))))
(local (defthm fn-ovrup-decimal-field-advance
 (implies (and (natp j) (<= j (nfix limit)))
  (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field n h j limit st))))
   (<= j2 (+ j (fn-ovr-decimal-field-len n)))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
   '(fn-ovr-put-decimal-field fn-dsw-decimal fn-dsw-append fn-ovrqp-decimal-count-is-length fn-ovr-decimal-field-len-is-len fn-nntp-decimal-field fn-ovrqp-decimal-token fn-ovrqp-decimal-non-natural fn-ovr-decimal-len-is-len fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix natp nfix len car-cons cdr-cons
     (:type-prescription len) (:type-prescription fn-nntp-string-octets) (:type-prescription natp))
   (fn-dss-measure-theory))))))
(local (defthm fn-ovrup-xref-advance
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-xref ms all idp h j limit s))))
      (<= j2 (+ j (fn-ovr-xref-len ms all idp)))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :induct (fn-ovr-put-xref ms all idp h j limit s)
    :in-theory (union-theories '(fn-ovrup-octets-advance fn-ovrup-string-advance fn-ovrup-decimal-advance fn-ovrup-decimal-field-advance fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ fix fn-ovr-xref-len-natp fn-ovr-string-len-natp fn-ovr-decimal-field-len-natp fn-ovr-decimal-len-natp unicity-of-0 default-+-1 default-+-2 fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-xref fn-ovr-xref-len fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-decimal-field-tab-advance
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s))))
      (<= j2 (+ j (+ 1 (fn-ovr-decimal-field-len n))))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrup-octets-advance fn-ovrup-string-advance fn-ovrup-decimal-advance fn-ovrup-decimal-field-advance fn-ovrup-xref-advance fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ fix fn-ovr-xref-len-natp fn-ovr-string-len-natp fn-ovr-decimal-field-len-natp fn-ovr-decimal-len-natp unicity-of-0 default-+-1 default-+-2 fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-decimal-field-tab fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-decimal-tab-advance
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-decimal-tab n h j limit s))))
      (<= j2 (+ j (+ 1 (fn-ovr-decimal-len n))))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrup-octets-advance fn-ovrup-string-advance fn-ovrup-decimal-advance fn-ovrup-decimal-field-advance fn-ovrup-xref-advance fn-ovrup-decimal-field-tab-advance fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ fix fn-ovr-xref-len-natp fn-ovr-string-len-natp fn-ovr-decimal-field-len-natp fn-ovr-decimal-len-natp unicity-of-0 default-+-1 default-+-2 fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-decimal-tab fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-fields-advance
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-fields fields h j limit s))))
      (<= j2 (+ j (len (fn-ovrqp-fields-octets fields))))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :induct (fn-ovr-put-fields fields h j limit s)
    :in-theory (union-theories '(fn-ovrup-octets-advance fn-ovrup-string-advance fn-ovrup-decimal-advance fn-ovrup-decimal-field-advance fn-ovrup-xref-advance fn-ovrup-decimal-field-tab-advance fn-ovrup-decimal-tab-advance fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ fix fn-ovr-xref-len-natp fn-ovr-string-len-natp fn-ovr-decimal-field-len-natp fn-ovr-decimal-len-natp unicity-of-0 default-+-1 default-+-2 fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear fn-ovrup-decimal-tab-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-fields fn-ovrqp-fields-octets fn-ovr-string-len-is-len fn-ovrqp-len-append fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position fn-ovrup-decimal-tab-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-served-xref-advance
 (implies (and (natp j) (<= j (nfix limit)) (fn-cbor-octet-listp server))
   (let ((j2 (mv-nth 1 (fn-ovr-put-served-xref server ms idp h j limit s))))
      (<= j2 (+ j (if server (+ 1 (len *fn-xref-name*) (len (if (true-listp server) server nil)) (fn-ovr-xref-len ms ms idp)) 0)))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrup-octets-advance fn-ovrup-string-advance fn-ovrup-decimal-advance fn-ovrup-decimal-field-advance fn-ovrup-xref-advance fn-ovrup-decimal-field-tab-advance fn-ovrup-decimal-tab-advance fn-ovrup-fields-advance fn-cbor-octet-listp-implies-true-listp fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ fix fn-ovr-xref-len-natp fn-ovr-string-len-natp fn-ovr-decimal-field-len-natp fn-ovr-decimal-len-natp unicity-of-0 default-+-1 default-+-2 fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear fn-ovrup-decimal-tab-position-linear fn-ovrup-fields-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-served-xref fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position fn-ovrup-decimal-tab-position fn-ovrup-fields-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-column-line-advance
 (implies (and (natp j) (<= j (nfix limit)) (fn-cbor-octet-listp server))
   (let ((j2 (mv-nth 1 (fn-ovr-put-column-line n nov octets body server ms idp h j limit s))))
      (<= j2 (+ j (fn-ovr-column-line-len n nov octets body server ms idp)))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :do-not-induct t :use ((:instance fn-ovrup-decimal-field-tab-advance (n n) (j j) (s s))
(:instance fn-ovrup-decimal-field-tab-position (n n) (j j) (s s))
(:instance fn-ovrup-fields-advance (fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov))) (j (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s))) (s (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))
(:instance fn-ovrup-fields-position (fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov))) (j (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s))) (s (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))
(:instance fn-ovrup-decimal-tab-advance (n octets) (j (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))) (s (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))
(:instance fn-ovrup-decimal-tab-position (n octets) (j (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))) (s (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))
(:instance fn-ovrup-decimal-advance (n body) (j (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))) (st (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))))
(:instance fn-ovrup-decimal-position (n body) (j (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))) (st (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))))
(:instance fn-ovrup-served-xref-advance (server server) (ms ms) (idp idp) (j (mv-nth 1 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))))) (s (mv-nth 2 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))))))
(:instance fn-ovrup-served-xref-position (server server) (ms ms) (idp idp) (j (mv-nth 1 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))))) (s (mv-nth 2 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))))))
(:instance fn-ovrup-octets-advance (octets '(13 10)) (j (mv-nth 1 (fn-ovr-put-served-xref server ms idp h (mv-nth 1 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))))) limit (mv-nth 2 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))))))) (st (mv-nth 2 (fn-ovr-put-served-xref server ms idp h (mv-nth 1 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))))) limit (mv-nth 2 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))))))))
(:instance fn-ovrqp-octets-position (octets '(13 10)) (j (mv-nth 1 (fn-ovr-put-served-xref server ms idp h (mv-nth 1 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))))) limit (mv-nth 2 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s))))))))))) (st (mv-nth 2 (fn-ovr-put-served-xref server ms idp h (mv-nth 1 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))))) limit (mv-nth 2 (fn-ovr-put-decimal body h (mv-nth 1 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))) limit (mv-nth 2 (fn-ovr-put-decimal-tab octets h (mv-nth 1 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))) limit (mv-nth 2 (fn-ovr-put-fields (list (fn-hnov-subject nov) (fn-hnov-from nov) (fn-hnov-date nov) (fn-hnov-msgid nov) (fn-hnov-references nov)) h (mv-nth 1 (fn-ovr-put-decimal-field-tab n h j limit s)) limit (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit s)))))))))))))
    :in-theory (union-theories '(fn-ovrup-octets-advance fn-ovrup-string-advance fn-ovrup-decimal-advance fn-ovrup-decimal-field-advance fn-ovrup-xref-advance fn-ovrup-decimal-field-tab-advance fn-ovrup-decimal-tab-advance fn-ovrup-fields-advance fn-ovrup-served-xref-advance fn-cbor-octet-listp-implies-true-listp (:type-prescription len) mv-nth car-cons cdr-cons zp fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ fix fn-ovr-xref-len-natp fn-ovr-string-len-natp fn-ovr-decimal-field-len-natp fn-ovr-decimal-len-natp unicity-of-0 default-+-1 default-+-2 fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear fn-ovrup-decimal-tab-position-linear fn-ovrup-fields-position-linear fn-ovrup-served-xref-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-column-line fn-ovr-column-line-len fn-ovrqp-fields-octets fn-ovr-string-len-is-len fn-ovrqp-len-append fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position fn-ovrup-decimal-tab-position fn-ovrup-fields-position fn-ovrup-served-xref-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(local (defthm fn-ovrup-number-advance
 (implies (and (natp j) (<= j (nfix limit)) (fn-cbor-octet-listp server))
   (let ((j2 (mv-nth 1 (fn-ovr-put-number group n server v h j limit s fn-arena fn-cat))))
      (<= j2 (+ j (fn-ovr-number-len group n server (nfix v) fn-arena fn-cat)))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrup-octets-advance fn-ovrup-string-advance fn-ovrup-decimal-advance fn-ovrup-decimal-field-advance fn-ovrup-xref-advance fn-ovrup-decimal-field-tab-advance fn-ovrup-decimal-tab-advance fn-ovrup-fields-advance fn-ovrup-served-xref-advance fn-ovrup-column-line-advance fn-cbor-octet-listp-implies-true-listp (:type-prescription len) mv-nth car-cons cdr-cons zp fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ fix fn-ovr-xref-len-natp fn-ovr-string-len-natp fn-ovr-decimal-field-len-natp fn-ovr-decimal-len-natp unicity-of-0 default-+-1 default-+-2 fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear fn-ovrup-decimal-tab-position-linear fn-ovrup-fields-position-linear fn-ovrup-served-xref-position-linear fn-ovrup-column-line-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-number fn-ovr-number-len fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position fn-ovrup-decimal-tab-position fn-ovrup-fields-position fn-ovrup-served-xref-position fn-ovrup-column-line-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))
(defthm fn-ovrup-probe-advance
 (implies (and (natp j) (<= j (nfix limit)) (fn-cbor-octet-listp server))
   (let ((j2 (mv-nth 1 (fn-ovr-put-probe group number server v h j limit s fn-arena fn-cat))))
      (<= j2 (+ j (fn-ovr-probe-len group number server (nfix v) fn-arena fn-cat)))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :do-not-induct t
    :in-theory (union-theories '(fn-ovrup-octets-advance fn-ovrup-string-advance fn-ovrup-decimal-advance fn-ovrup-decimal-field-advance fn-ovrup-xref-advance fn-ovrup-decimal-field-tab-advance fn-ovrup-decimal-tab-advance fn-ovrup-fields-advance fn-ovrup-served-xref-advance fn-ovrup-column-line-advance fn-ovrup-number-advance fn-cbor-octet-listp-implies-true-listp (:type-prescription len) mv-nth car-cons cdr-cons zp fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ fix fn-ovr-xref-len-natp fn-ovr-string-len-natp fn-ovr-decimal-field-len-natp fn-ovr-decimal-len-natp unicity-of-0 default-+-1 default-+-2 fn-ovrqp-octets-position-linear fn-ovrup-string-position-linear fn-ovrup-decimal-field-position-linear fn-ovrup-decimal-position-linear fn-ovrup-xref-position-linear fn-ovrup-decimal-field-tab-position-linear fn-ovrup-decimal-tab-position-linear fn-ovrup-fields-position-linear fn-ovrup-served-xref-position-linear fn-ovrup-column-line-position-linear fn-ovrup-number-position-linear natp-compound-recognizer fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovr-put-probe fn-ovr-probe-len fn-ovrqp-octets-position fn-ovrup-string-position fn-ovrup-decimal-field-position fn-ovrup-decimal-position fn-ovrup-xref-position fn-ovrup-decimal-field-tab-position fn-ovrup-decimal-tab-position fn-ovrup-fields-position fn-ovrup-served-xref-position fn-ovrup-column-line-position fn-ovrup-number-position ) (set-difference-theories (fn-dss-measure-theory) '(natp nfix))))))

; Scalar workspace refinement also covers logical states before correspondence.
(local (include-book "runtime-contract-host-lease-run"))
(defun fn-ovra-roomp (h j limit s)
 (declare (xargs :verify-guards nil))
 (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s))) (< h (len (fn-rtc-pool s)))
      (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :workspace)
      (natp j) (natp limit) (<= j limit) (<= j (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))
      (<= limit (fn-rtc-buf-cap h (fn-rtc-config s)))))
(defthm fn-ovra-room-properties
 (implies (fn-ovra-roomp h j limit s)
          (and (natp h) (natp j) (natp limit) (<= j limit)
               (<= limit (fn-rtc-buf-cap h (fn-rtc-config s)))))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory (union-theories '(fn-ovra-roomp) (theory 'minimal-theory)))))
(defthm fn-ovra-room-after-puts
 (implies (and (fn-ovra-roomp h j limit s) (fn-cbor-octet-listp data)
               (<= (+ j (len data)) limit))
          (fn-ovra-roomp h (+ j (len data)) limit (fn-rtc-st$a-puts h j data s)))
 :hints (("Goal" :use ((:instance fn-hlr-puts-frame (off j) (w data) (k h))
                      (:instance fn-hlr-puts-len2 (off j) (w data)))
 :in-theory (union-theories '(fn-ovra-roomp natp nfix (:type-prescription len))
 (fn-dss-measure-theory)))))
(defthm fn-ovra-append-is-puts
 (implies (and (fn-ovra-roomp h j limit s) (fn-cbor-octet-listp data)
               (<= (+ j (len data)) limit))
          (equal (fn-dsw-append h j data s)
                 (mv :done (+ j (len data)) (fn-rtc-st$a-puts h j data s))))
 :hints (("Goal" :in-theory (union-theories '(fn-dsw-append fn-dsw-roomp
 fn-rtc-st-config fn-rtc-st$a-config fn-rtc-st-owner fn-rtc-st$a-owner
 fn-rtc-st-uses fn-rtc-st$a-uses fn-rtc-st-fill fn-rtc-st$a-fill fn-rtc-bytes
 fn-rtc-splice-target-p fn-ovra-roomp fn-dsw-append-loop-is-puts
 fn-rtc-get fn-rtc-b-owner natp nfix len car-cons cdr-cons
 (:executable-counterpart fn-rtc-get)) (fn-dss-measure-theory)))))
(defthm fn-ovra-room-at-puts-position
 (implies (and (fn-ovra-roomp h j limit s) (fn-cbor-octet-listp data)
               (equal j2 (+ j (len data))) (<= j2 limit))
          (fn-ovra-roomp h j2 limit (fn-rtc-st$a-puts h j data s)))
 :hints (("Goal" :use fn-ovra-room-after-puts :in-theory (theory 'minimal-theory))))
(defthm fn-ovra-compose-at-puts-position
 (implies (and (fn-ovra-roomp h j limit s) (equal j2 (+ j (len a))))
  (equal (fn-rtc-st$a-puts h j2 b (fn-rtc-st$a-puts h j a s))
         (fn-rtc-st$a-puts h j (append a b) s)))
 :hints (("Goal" :use fn-ovrqp-puts-compose
  :in-theory (union-theories '(fn-ovra-room-properties) (theory 'minimal-theory)))))
(defthm fn-ovra-octets-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (fn-cbor-octet-listp data) (<= (+ j (len data)) limit))
  (equal (fn-ovr-put-octets data h j limit st)
         (mv :done (+ j (len data)) (fn-rtc-st$a-puts h j data st))))
 :hints (("Goal" :use ((:instance fn-ovra-room-after-puts (s st)))
   :in-theory (union-theories '(fn-ovr-put-octets fn-ovra-append-is-puts fn-ovra-room-properties
           fn-ovrqp-nfix-natural) (theory 'minimal-theory)))))
(local (defthm fn-ovra-string-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (<= (+ j (len (fn-nntp-string-octets text))) limit))
  (equal (fn-ovr-put-string text h j limit st)
         (mv :done (+ j (len (fn-nntp-string-octets text)))
                   (fn-rtc-st$a-puts h j (fn-nntp-string-octets text) st))))
 :hints (("Goal" :use ((:instance fn-ovra-room-after-puts (data (fn-nntp-string-octets text)) (s st)))
    :in-theory (union-theories '(fn-ovr-put-string fn-ovr-wcopy-string fn-ovr-wcopy-string-list-is-identity
       fn-ovrqp-slice-whole fn-ovrqp-string-octets fn-ovrqp-string-aux-octets fn-cbor-octet-listp-implies-true-listp fn-ovra-room-properties fn-ovrqp-nfix-natural
       fn-ovr-string-len-is-len fn-ovrqp-string-length fn-ovra-append-is-puts
       fn-nntp-string-octets (:type-prescription len) (:type-prescription natp) (:executable-counterpart len) (:executable-counterpart fn-cbor-octet-listp) unicity-of-0)
      (theory 'minimal-theory))))))
(local (defthm fn-ovra-decimal-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (<= (+ j (len (fn-nntp-decimal n))) limit))
  (equal (fn-ovr-put-decimal n h j limit st)
         (mv :done (+ j (len (fn-nntp-decimal n))) (fn-rtc-st$a-puts h j (fn-nntp-decimal n) st))))
 :hints (("Goal" :use ((:instance fn-ovra-room-after-puts (data (fn-nntp-decimal n)) (s st)))
  :in-theory (union-theories '(fn-ovr-put-decimal fn-dsw-decimal fn-ovra-append-is-puts fn-ovrqp-decimal-count-is-length
      fn-ovrqp-decimal-octets fn-ovrqp-decimal-field-octets fn-ovra-room-properties fn-ovrqp-nfix-natural) (theory 'minimal-theory))))))
(local (defthm fn-ovra-decimal-field-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (<= (+ j (len (fn-nntp-decimal-field n))) limit))
  (equal (fn-ovr-put-decimal-field n h j limit st)
         (mv :done (+ j (len (fn-nntp-decimal-field n))) (fn-rtc-st$a-puts h j (fn-nntp-decimal-field n) st))))
 :hints (("Goal" :use ((:instance fn-ovra-room-after-puts (data (fn-nntp-decimal-field n)) (s st)))
  :in-theory (union-theories '(fn-ovr-put-decimal-field fn-nntp-decimal-field fn-ovrqp-decimal-token fn-ovrqp-decimal-non-natural fn-dsw-decimal
       fn-ovra-append-is-puts fn-ovrqp-decimal-count-is-length fn-ovr-decimal-field-len-is-len
       fn-ovrqp-decimal-octets fn-ovrqp-decimal-field-octets fn-ovra-room-properties fn-ovrqp-nfix-natural natp len car-cons cdr-cons
       (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovra-decimal-field-tab-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (<= (+ j (len (append (fn-nntp-decimal-field n) '(9)))) limit))
  (equal (fn-ovr-put-decimal-field-tab n h j limit st)
         (mv :done (+ j (len (append (fn-nntp-decimal-field n) '(9))))
            (fn-rtc-st$a-puts h j (append (fn-nntp-decimal-field n) '(9)) st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
   '(fn-ovr-put-decimal-field-tab fn-ovra-decimal-field-is-puts fn-ovra-octets-is-puts
     fn-ovra-room-after-puts fn-ovra-room-properties fn-ovrqp-puts-compose
     fn-ovrqp-decimal-octets fn-ovrqp-decimal-field-octets
     fn-ovrqp-len-append fn-ovrqp-nfix-natural
     associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2 mv-nth zp car-cons cdr-cons len (:type-prescription len)
     (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovra-decimal-tab-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (<= (+ j (len (append (fn-nntp-decimal n) '(9)))) limit))
  (equal (fn-ovr-put-decimal-tab n h j limit st)
         (mv :done (+ j (len (append (fn-nntp-decimal n) '(9))))
            (fn-rtc-st$a-puts h j (append (fn-nntp-decimal n) '(9)) st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
   '(fn-ovr-put-decimal-tab fn-ovra-decimal-is-puts fn-ovra-octets-is-puts
     fn-ovra-room-after-puts fn-ovra-room-properties fn-ovrqp-puts-compose
     fn-ovrqp-decimal-octets fn-ovrqp-decimal-field-octets
     fn-ovrqp-len-append fn-ovrqp-nfix-natural
     associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2 mv-nth zp car-cons cdr-cons len (:type-prescription len)
     (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(defthm fn-ovra-empty-puts (equal (fn-rtc-st$a-puts h j nil s) s)
 :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$a-puts) (theory 'minimal-theory)))))
(local (defthm fn-ovra-fields-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (<= (+ j (len (fn-ovrqp-fields-octets fields))) limit))
  (equal (fn-ovr-put-fields fields h j limit st)
    (mv :done (+ j (len (fn-ovrqp-fields-octets fields)))
        (fn-rtc-st$a-puts h j (fn-ovrqp-fields-octets fields) st))))
 :hints (("Goal" :induct (fn-ovr-put-fields fields h j limit st)
    :in-theory (union-theories '(fn-ovr-put-fields fn-ovrqp-fields-octets fn-ovrqp-fields-octets-type
      fn-ovra-string-is-puts fn-ovrqp-string-octets fn-ovra-octets-is-puts fn-ovrqp-empty-splice
      fn-ovra-room-properties fn-ovra-empty-puts fn-ovra-room-after-puts fn-ovra-compose-at-puts-position fn-ovra-room-at-puts-position fn-ovrqp-append-associates natp-compound-recognizer fix fn-ovrqp-len-append
      fn-ovrqp-nfix-natural fn-cbor-octet-listp-implies-true-listp fn-rtc-c-l-octets-append
      associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2
      mv-nth zp car-cons cdr-cons len binary-append (:type-prescription len)
      (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovra-xref-is-puts
 (implies (and (fn-ovra-roomp h j limit st)
               (<= (+ j (len (fn-xref-locations (fn-xref-pairs-of ms article)))) limit))
  (equal (fn-ovr-put-xref ms (fn-article-memberships article)
                            (fn-scat-msgid-idp (fn-article-msgid article)) h j limit st)
   (mv :done (+ j (len (fn-xref-locations (fn-xref-pairs-of ms article))))
       (fn-rtc-st$a-puts h j (fn-xref-locations (fn-xref-pairs-of ms article)) st))))
 :hints (("Goal" :induct (fn-ovr-put-xref ms (fn-article-memberships article)
                           (fn-scat-msgid-idp (fn-article-msgid article)) h j limit st)
  :in-theory (union-theories '(fn-ovr-put-xref fn-xref-pairs-of fn-xref-locations fn-ag-car fn-ag-cdr
      fn-ovr-xref-wordp-is-wordp fn-ovr-article-number-is-number fn-ovr-xref-len-is-len
      fn-ovra-octets-is-puts fn-ovra-string-is-puts fn-ovra-decimal-field-is-puts
      fn-ovrqp-string-octets fn-ovrqp-decimal-field-octets fn-ovrqp-xref-octets fn-ovrqp-empty-splice
      fn-ovra-room-properties fn-ovra-empty-puts fn-ovra-room-after-puts fn-ovra-room-at-puts-position
      fn-ovra-compose-at-puts-position fn-ovrqp-append-associates fn-ovrqp-len-append
      fn-ovrqp-nfix-natural fn-ovrqp-octets-cons (:executable-counterpart fn-cbor-octetp) fn-cbor-octet-listp-implies-true-listp fn-rtc-c-l-octets-append
      associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2
      natp-compound-recognizer fix mv-nth zp car-cons cdr-cons len binary-append (:type-prescription len)
      (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))
(local (defthm fn-ovra-served-xref-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (fn-cbor-octet-listp server)
  (<= (+ j (len (if server (cons 9 (fn-xref-field server (fn-xref-pairs article))) nil))) limit))
  (equal (fn-ovr-put-served-xref server (fn-article-memberships article)
             (fn-scat-msgid-idp (fn-article-msgid article)) h j limit st)
   (mv :done (+ j (len (if server (cons 9 (fn-xref-field server (fn-xref-pairs article))) nil)))
    (fn-rtc-st$a-puts h j (if server (cons 9 (fn-xref-field server (fn-xref-pairs article))) nil) st))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories '(fn-ovr-put-served-xref fn-xref-field fn-xref-pairs
      fn-ovra-octets-is-puts fn-ovra-xref-is-puts fn-ovrqp-xref-octets fn-ovrqp-empty-splice
      fn-ovra-room-properties fn-ovra-empty-puts fn-ovra-room-after-puts fn-ovra-room-at-puts-position
      fn-ovra-compose-at-puts-position fn-ovrqp-append-associates fn-ovrqp-len-append
      fn-ovrqp-nfix-natural fn-ovrqp-octets-cons fn-cbor-octet-listp-implies-true-listp fn-rtc-c-l-octets-append
      fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2
      natp-compound-recognizer fix mv-nth zp car-cons cdr-cons len binary-append (:type-prescription len)
      (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-cbor-octetp))
     (theory 'minimal-theory))))))
(local (defthm fn-ovra-column-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (fn-cbor-octet-listp server)
   (<= (+ j (len (fn-nntp-crlf (fn-nov-served-line n (fn-ovr-column-over nov octets body) server article)))) limit))
  (equal (fn-ovr-put-column-line n nov octets body server
                   (fn-article-memberships article) (fn-scat-msgid-idp (fn-article-msgid article)) h j limit st)
    (mv :done (+ j (len (fn-nntp-crlf (fn-nov-served-line n (fn-ovr-column-over nov octets body) server article))))
      (fn-rtc-st$a-puts h j (fn-nntp-crlf (fn-nov-served-line n (fn-ovr-column-over nov octets body) server article)) st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
  '(fn-ovr-put-column-line fn-ovr-column-line-len-is-len fn-ovrqp-column-octets fn-ovr-record-octets-is-nntp-octets
    fn-ovra-decimal-field-tab-is-puts fn-ovra-fields-is-puts fn-ovrqp-fields-octets
    fn-ovra-decimal-tab-is-puts fn-ovra-decimal-is-puts fn-ovra-served-xref-is-puts
    fn-ovra-octets-is-puts fn-ovrqp-string-octets fn-ovrqp-decimal-octets fn-ovrqp-decimal-field-octets
    fn-ovrqp-fields-octets-type fn-ovrqp-served-xref-octets fn-ovrqp-xref-octets fn-ovrqp-xref-field-octets
    fn-nntp-crlf fn-nov-served-line fn-nov-line fn-ovr-column-over
    fn-nov-subject fn-nov-from fn-nov-date fn-nov-msgid fn-nov-references fn-nov-bytes fn-nov-lines
    fn-nntp-append-pieces
    fn-ovra-room-properties fn-ovra-empty-puts fn-ovra-room-after-puts fn-ovra-room-at-puts-position
    fn-ovra-compose-at-puts-position fn-ovrqp-append-associates fn-ovrqp-len-append
    fn-ovrqp-nfix-natural fn-ovrqp-octets-cons fn-cbor-octet-listp-implies-true-listp fn-rtc-c-l-octets-append
    fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2
    natp-compound-recognizer fix mv-nth zp car-cons cdr-cons len binary-append (:type-prescription len)
    (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart fn-cbor-octetp))
    (theory 'minimal-theory))))))
(local (defthm fn-ovra-number-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (natp v) (fn-cbor-octet-listp server)
  (<= (+ j (len (fn-nntp-stuff-lines
      (if server (fn-nov-served-lines-for-numbers-cat group (list n) server v fn-arena fn-cat)
        (fn-nov-lines-for-numbers-cat group (list n) v fn-arena fn-cat))))) limit))
  (equal (fn-ovr-put-number group n server v h j limit st fn-arena fn-cat)
   (mv :done (+ j (len (fn-nntp-stuff-lines
      (if server (fn-nov-served-lines-for-numbers-cat group (list n) server v fn-arena fn-cat)
        (fn-nov-lines-for-numbers-cat group (list n) v fn-arena fn-cat)))))
     (fn-rtc-st$a-puts h j (fn-nntp-stuff-lines
      (if server (fn-nov-served-lines-for-numbers-cat group (list n) server v fn-arena fn-cat)
        (fn-nov-lines-for-numbers-cat group (list n) v fn-arena fn-cat))) st))))
 :hints (("Goal" :in-theory (e/d (fn-ovra-room-properties fn-ovra-room-after-puts fn-ovra-empty-puts fn-ovr-put-number fn-nov-served-lines-for-numbers-cat
       fn-nov-lines-for-numbers-cat fn-scol-tombstonep fn-ovr-number-len-is-len)
    (fn-ovr-put-column-line fn-ovr-put-octets fn-nov-served-line fn-nov-line fn-nov-overview fn-hf-nov
      fn-scol-facts fn-scat-available-article fn-ovr-available-article fn-nntp-article-tombstonep
      fn-nntp-stuff-lines fn-nntp-crlf fn-scol-overview-of fn-ovr-column-over fn-nntp-article-length
      fn-ovr-msgid-okp fn-ovr-number-len fn-rtc-st$ap fn-rtc-shapep fn-rtc-st$a-puts
      fn-rtc-splice-okp fn-ovra-roomp))))))
(defthm fn-ovra-probe-is-puts
 (implies (and (fn-ovra-roomp h j limit st) (natp v) (natp number) (fn-cbor-octet-listp server)
              (<= (+ j (len (fn-ovr-probe-octets group number server v fn-arena fn-cat))) limit))
  (equal (fn-ovr-put-probe group number server v h j limit st fn-arena fn-cat)
   (mv :done (+ j (len (fn-ovr-probe-octets group number server v fn-arena fn-cat)))
    (fn-rtc-st$a-puts h j (fn-ovr-probe-octets group number server v fn-arena fn-cat) st))))
 :hints (("Goal" :in-theory (e/d (fn-ovra-room-properties fn-ovra-room-after-puts fn-ovra-empty-puts fn-ovr-put-probe fn-ovr-probe-octets fn-ovw-lines fn-scat-range-keep
                                  fn-ovr-msgid-okp-is-idp fn-ovr-probe-len-is-the-length)
      (fn-ovr-put-number fn-nov-served-lines-for-numbers-cat fn-nov-lines-for-numbers-cat
       fn-cnx-view-seq fn-held-number-in fn-scat-msgid-idp fn-ovr-msgid-okp fn-nntp-stuff-lines
       fn-ovr-probe-len fn-ovr-number-len fn-rtc-st$ap fn-rtc-shapep fn-rtc-st$a-puts fn-rtc-splice-okp fn-ovra-roomp))
  :expand ((fn-cnx-range-aux group number number v fn-cat)
           (fn-cnx-range-aux group (+ 1 number) number v fn-cat)))))
