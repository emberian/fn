; fn: a served POST's stored bytes parse under the profile's header limits
; widened by the injected block's bound (O1 packet 3, P3-5; DECISIONS-
; 20261010 item 5, option (c): no behaviour change, the ingress census stays
; on the source, books/injection.lisp fn-inj-decide).  The stored bytes are
; the Cancel-Lock lines before the injected octets with the Injection-Info
; parameters (FN-O1-POST-STORED-OCTETS); when they parse at the ceiling (the
; commit gate, books/peer-authored-accept.lisp fn-pa-carrier-kind) they parse
; under the configuration's header limits plus seven fields, seven lines and
; 2236 + 2 len(agent) octets (FN-O1-STORED-POST-WITHIN-THE-WIDENED-LIMITS):
; at most 2492 octets past the profile's header limit, the figure OVER's
; header bound takes.  The proof is census-only: every added line is one
; physical line, at most 998 + 2 octets in an article that parses, and the
; supplied-Path splice adds AGENT "!" to an existing line.

(in-package "ACL2")
(include-book "filed-groups")
(include-book "injection-info-params")
(include-book "cancel-lock")
(local (include-book "injection-invariants"))
(local (include-book "injection-info-params-invariants"))

; What a served POST stores (books/owner-served-invariants.lisp:76, local
; arm): Cancel-Lock lines (books/cancel-lock.lisp:144) before the injected
; octets with the Injection-Info parameters (books/injection-info-params.lisp
; :126) of the decision of fn-inj-decide (books/injection.lisp:966).
(defun fn-o1-post-stored-octets (source config obs secret account cfg)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-inj-decide source config obs)))
    (fn-cl-served-payload secret account (fn-inj-decision-msgid d)
                          (fn-ipp-injected-octets d secret account cfg))))

; The injected block's bound: at most seven single-line fields the source
; did not carry (Cancel-Lock, Cancel-Key, Path, Injection-Date, Message-ID,
; Date, Injection-Info), or six and AGENT "!" spliced into the supplied Path
; line.  Octets: Path AGENT+21 (or the splice AGENT+1), Injection-Date 49,
; generated Message-ID AGENT+61, Date 39, Cancel-Lock 66; Injection-Info
; (parameters: the posting account and the operator's complaints address,
; no fixed cap, D27) and Cancel-Key (one key per retained epoch) are each one
; physical line, so at most 998 + 2 in an article that parses.
(defun fn-o1-injected-block-octets (agent)
  (declare (xargs :guard t))
  (+ 2236 (* 2 (len agent))))

(defun fn-o1-stored-header-limits (limits agent)
  (declare (xargs :guard t))
  (fn-article-limits (+ 7 (fn-article-limit-fields limits))
                     (+ 7 (fn-article-limit-lines limits))
                     (+ (fn-article-limit-octets limits)
                        (fn-o1-injected-block-octets agent))))

; Census of the stored octets: every lemma below is local (prefix o1s-).
; The stored octets are at most seven single-line fields in front of the
; source (a splice adds no line), so their header census is the source
; census plus (7, 7, 2236 + 2*len(agent)); the ceiling parse and
; fn-article-parse-under-admits-exactly-the-limits then give the widened parse.

(local
 (defthm o1s-next-line-aux-of-a-line
  (implies (and (fn-ipp-no-crlfp a) (true-listp a) (natp left) (true-listp acc))
           (equal (fn-article-next-line-aux (append a (list* 13 10 r)) acc left)
                  (if (<= (len a) left)
                      (list :ok (append (reverse acc) a) r)
                    (list :error :limit))))
  :hints (("Goal" :induct (fn-article-next-line-aux a acc left)
           :in-theory (enable fn-article-next-line-aux fn-ipp-no-crlfp)))))

(local
 (defthm o1s-next-line-of-a-line
  (implies (and (fn-ipp-no-crlfp a) (true-listp a))
           (equal (fn-article-next-line (append a (list* 13 10 r)))
                  (if (<= (len a) 998)
                      (list :ok a r)
                    (list :error :limit))))
  :hints (("Goal" :in-theory (e/d (fn-article-next-line) (o1s-next-line-aux-of-a-line))
           :use ((:instance o1s-next-line-aux-of-a-line (acc nil) (left *fn-article-max-line-octets*)))))))
(local
 (defthm o1s-census-of-a-line
  (implies (and (fn-ipp-no-crlfp a) (true-listp a) (consp a))
           (and (<= (fn-article-header-field-count (append a (list* 13 10 r)))
                    (+ 1 (fn-article-header-field-count r)))
                (<= (fn-article-header-line-count (append a (list* 13 10 r)))
                    (+ 1 (fn-article-header-line-count r)))
                (<= (fn-article-header-octet-count (append a (list* 13 10 r)))
                    (+ 1000 (fn-article-header-octet-count r)))
                (<= (fn-article-header-octet-count (append a (list* 13 10 r)))
                    (+ 2 (len a) (fn-article-header-octet-count r)))))
  :hints (("Goal" :do-not-induct t
           :cases ((<= (len a) 998))
           :in-theory (disable fn-article-next-line o1s-next-line-aux-of-a-line)
           :expand ((fn-article-header-field-count (append a (list* 13 10 r)))
                    (fn-article-header-line-count (append a (list* 13 10 r)))
                    (fn-article-header-octet-count (append a (list* 13 10 r))))))))
(local
 (encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm o1s-big-hi2 (<= 48 (fn-inj-hi2 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-hi2))))
  (defthm o1s-big-lo2 (<= 48 (fn-inj-lo2 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-lo2))))
  (defthm o1s-big-r1 (<= 0 (fn-inj-r1 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-r1))))
  (defthm o1s-big-r2 (<= 0 (fn-inj-r2 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-r2 fn-inj-r1))))
  (defthm o1s-big-yth (<= 48 (fn-inj-y-th n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-y-th))))
  (defthm o1s-big-yhu (<= 48 (fn-inj-y-hu n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-y-hu))))
  (defthm o1s-big-yte (<= 48 (fn-inj-y-te n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-y-te))))
  (defthm o1s-big-yun (<= 48 (fn-inj-y-un n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-y-un))))))
(local (defthm o1s-big-d1 (<= 63 (fn-inj-dow-c1 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-dow-c1)))))
(local (defthm o1s-big-d2 (<= 63 (fn-inj-dow-c2 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-dow-c2)))))
(local (defthm o1s-big-d3 (<= 63 (fn-inj-dow-c3 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-dow-c3)))))
(local (defthm o1s-big-m1 (<= 63 (fn-inj-month-c1 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-month-c1)))))
(local (defthm o1s-big-m2 (<= 63 (fn-inj-month-c2 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-month-c2)))))
(local (defthm o1s-big-m3 (<= 63 (fn-inj-month-c3 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-month-c3)))))
(local
 (defthm o1s-date-no-crlf
  (fn-ipp-no-crlfp (fn-inj-date-octets inst))
  :hints (("Goal" :in-theory (e/d (fn-inj-date-octets fn-ipp-no-crlfp)
                                  (fn-inj-hi2 fn-inj-lo2 fn-inj-y-th fn-inj-y-hu fn-inj-y-te fn-inj-y-un
                                   fn-inj-dow-c1 fn-inj-dow-c2 fn-inj-dow-c3 fn-inj-month-c1 fn-inj-month-c2
                                   fn-inj-month-c3 fn-inj-instant-year fn-inj-instant-month fn-inj-instant-day
                                   fn-inj-instant-hour fn-inj-instant-minute fn-inj-instant-second fn-inj-instant-dow))))))
(local
 (defthm o1s-dot-atom-no-crlf
  (implies (and (true-listp bytes) (fn-af-dot-atom-text-aux bytes want-atext))
           (fn-ipp-no-crlfp bytes))
  :hints (("Goal" :induct (fn-af-dot-atom-text-aux bytes want-atext)
           :in-theory (enable fn-af-dot-atom-text-aux fn-af-atextp fn-ipp-no-crlfp)))))

(local
 (defthm o1s-config-agent-facts
  (implies (fn-inj-configp config)
           (and (fn-ipp-no-crlfp (fn-inj-config-agent config))
                (consp (fn-inj-config-agent config))
                (true-listp (fn-inj-config-agent config))))
  :hints (("Goal" :in-theory (e/d (fn-inj-configp fn-af-dot-atom-textp)
                                  (fn-af-dot-atom-text-aux fn-inj-config-agent))
           :use ((:instance o1s-dot-atom-no-crlf
                            (bytes (fn-inj-config-agent config)) (want-atext t))
                 (:instance fn-article-octet-list-true-listp
                            (octets (fn-inj-config-agent config))))))))

(local
 (encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm o1s-digits-rev-facts
    (and (fn-ipp-no-crlfp (fn-inj-digits-rev n w))
         (true-listp (fn-inj-digits-rev n w))
         (equal (len (fn-inj-digits-rev n w)) (nfix w)))
    :hints (("Goal" :in-theory (enable fn-inj-digits-rev fn-ipp-no-crlfp))))))
(local
 (defthm o1s-rev-append-facts
  (implies (and (fn-ipp-no-crlfp xs) (fn-ipp-no-crlfp acc) (true-listp acc))
           (and (fn-ipp-no-crlfp (fn-inj-rev-append xs acc))
                (true-listp (fn-inj-rev-append xs acc))
                (equal (len (fn-inj-rev-append xs acc)) (+ (len xs) (len acc)))))
  :hints (("Goal" :in-theory (enable fn-inj-rev-append fn-ipp-no-crlfp)))))
(local
 (defthm o1s-digits-facts
    (and (fn-ipp-no-crlfp (fn-inj-digits n w))
         (true-listp (fn-inj-digits n w))
         (equal (len (fn-inj-digits n w)) (nfix w)))
    :hints (("Goal" :in-theory (e/d (fn-inj-digits fn-ipp-no-crlfp) (o1s-rev-append-facts o1s-digits-rev-facts))
             :use ((:instance o1s-rev-append-facts (xs (fn-inj-digits-rev n w)) (acc nil))
                   (:instance o1s-digits-rev-facts))))))
(local
 (defun o1s-linesp (ls)
  (declare (xargs :verify-guards nil))
  (if (consp ls)
      (and (true-listp (car ls)) (consp (car ls)) (fn-ipp-no-crlfp (car ls))
           (o1s-linesp (cdr ls)))
    (null ls))))

(local
 (defun o1s-octets (ls)
  (declare (xargs :verify-guards nil))
  (if (consp ls)
      (append (car ls) (list* 13 10 (o1s-octets (cdr ls))))
    nil)))

(local
 (defun o1s-cost (ls)
  (declare (xargs :verify-guards nil))
  (if (consp ls)
      (+ (if (< 1000 (+ 2 (len (car ls)))) 1000 (+ 2 (len (car ls))))
         (o1s-cost (cdr ls)))
    0)))

(local
 (defthm o1s-census-of-lines
  (implies (o1s-linesp ls)
           (and (<= (fn-article-header-field-count (append (o1s-octets ls) r))
                    (+ (len ls) (fn-article-header-field-count r)))
                (<= (fn-article-header-line-count (append (o1s-octets ls) r))
                    (+ (len ls) (fn-article-header-line-count r)))
                (<= (fn-article-header-octet-count (append (o1s-octets ls) r))
                    (+ (o1s-cost ls) (fn-article-header-octet-count r)))))
  :hints (("Goal" :induct (o1s-octets ls)
           :in-theory (disable o1s-census-of-a-line)
           :do-not '(generalize))
          ("Subgoal *1/1" :use ((:instance o1s-census-of-a-line (a (car ls))
                                           (r (append (o1s-octets (cdr ls)) r))))))))
(local
 (defthm o1s-inj-append
  (equal (fn-inj-append a b) (append a b))
  :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defun o1s-block-ls (date msgid agent gid gdate params)
  (declare (xargs :verify-guards nil))
  (append (if (or gid gdate) (list (append *fn-inj-injection-date-field* date)) nil)
   (append (if gid (list (append *fn-inj-message-id-field* msgid)) nil)
    (append (if gdate (list (append *fn-inj-date-field* date)) nil)
            (list (append *fn-inj-injection-info-field* (append agent params))))))))

(local
 (defthm o1s-block-with-is-lines
  (equal (fn-ipp-block-with date msgid agent gid gdate params)
         (o1s-octets (o1s-block-ls date msgid agent gid gdate params)))
  :hints (("Goal" :in-theory (enable fn-ipp-block-with fn-inj-injection-date-line fn-inj-message-id-line
                                     fn-inj-date-line fn-inj-injection-info-line-with
                                     o1s-block-ls o1s-octets o1s-inj-append)))))

(local
 (defthm o1s-no-crlf-append
  (equal (fn-ipp-no-crlfp (append a b))
         (and (fn-ipp-no-crlfp a) (fn-ipp-no-crlfp b)))
  :hints (("Goal" :in-theory (enable fn-ipp-no-crlfp)))))

(local
 (defthm o1s-no-crlf-cons
  (equal (fn-ipp-no-crlfp (cons x y))
         (and (not (equal x 13)) (not (equal x 10)) (fn-ipp-no-crlfp y)))
  :hints (("Goal" :in-theory (enable fn-ipp-no-crlfp)))))

(local
 (defthm o1s-block-facts
  (implies (and (true-listp date) (fn-ipp-no-crlfp date) (equal (len date) 31)
                (implies gid (and (true-listp msgid) (fn-ipp-no-crlfp msgid)
                                  (equal (len msgid) (+ 47 (len agent)))))
                (true-listp agent) (fn-ipp-no-crlfp agent)
                (true-listp params) (fn-ipp-no-crlfp params))
           (and (o1s-linesp (o1s-block-ls date msgid agent gid gdate params))
                (<= (len (o1s-block-ls date msgid agent gid gdate params)) 4)
                (<= (o1s-cost (o1s-block-ls date msgid agent gid gdate params))
                    (+ 1149 (len agent)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1s-block-ls o1s-linesp o1s-cost) (fn-ipp-no-crlfp))))))
(local
 (defthm o1s-prefix-with-is-lines
  (equal (fn-ipp-prefix-with date msgid agent gid gdate params)
         (o1s-octets (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
                           (o1s-block-ls date msgid agent gid gdate params))))
  :hints (("Goal" :in-theory (enable fn-ipp-prefix-with fn-inj-path-line o1s-octets o1s-inj-append
                                     o1s-block-with-is-lines)))))

(local
 (defthm o1s-census-of-a-block
  (implies (and (true-listp date) (fn-ipp-no-crlfp date) (equal (len date) 31)
                (implies gid (and (true-listp msgid) (fn-ipp-no-crlfp msgid)
                                  (equal (len msgid) (+ 47 (len agent)))))
                (true-listp agent) (fn-ipp-no-crlfp agent)
                (true-listp params) (fn-ipp-no-crlfp params))
           (and (<= (fn-article-header-field-count (append (fn-ipp-block-with date msgid agent gid gdate params) r))
                    (+ 4 (fn-article-header-field-count r)))
                (<= (fn-article-header-line-count (append (fn-ipp-block-with date msgid agent gid gdate params) r))
                    (+ 4 (fn-article-header-line-count r)))
                (<= (fn-article-header-octet-count (append (fn-ipp-block-with date msgid agent gid gdate params) r))
                    (+ 1149 (len agent) (fn-article-header-octet-count r)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable o1s-census-of-lines o1s-block-facts)
           :use ((:instance o1s-census-of-lines (ls (o1s-block-ls date msgid agent gid gdate params)))
                 (:instance o1s-block-facts))))))

(local
 (defthm o1s-census-of-a-prefix
  (implies (and (true-listp date) (fn-ipp-no-crlfp date) (equal (len date) 31)
                (implies gid (and (true-listp msgid) (fn-ipp-no-crlfp msgid)
                                  (equal (len msgid) (+ 47 (len agent)))))
                (true-listp agent) (consp agent) (fn-ipp-no-crlfp agent)
                (true-listp params) (fn-ipp-no-crlfp params))
           (and (<= (fn-article-header-field-count (append (fn-ipp-prefix-with date msgid agent gid gdate params) r))
                    (+ 5 (fn-article-header-field-count r)))
                (<= (fn-article-header-line-count (append (fn-ipp-prefix-with date msgid agent gid gdate params) r))
                    (+ 5 (fn-article-header-line-count r)))
                (<= (fn-article-header-octet-count (append (fn-ipp-prefix-with date msgid agent gid gdate params) r))
                    (+ 1170 (* 2 (len agent)) (fn-article-header-octet-count r)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1s-linesp o1s-cost) (o1s-census-of-lines o1s-block-facts fn-ipp-no-crlfp))
           :use ((:instance o1s-census-of-lines
                            (ls (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
                                      (o1s-block-ls date msgid agent gid gdate params))))
                 (:instance o1s-block-facts))))))
(local
 (defthm o1s-valuep-facts
  (implies (fn-cll-valuep v)
           (and (fn-ipp-no-crlfp v) (true-listp v)))
  :hints (("Goal" :in-theory (enable fn-cll-valuep fn-cll-b64-charp fn-ipp-no-crlfp)))))

(local
 (defthm o1s-key-values-facts
  (implies (fn-cll-values-p keys)
           (and (fn-ipp-no-crlfp (fn-cll-key-values keys))
                (true-listp (fn-cll-key-values keys))))
  :hints (("Goal" :in-theory (enable fn-cll-values-p fn-cll-key-values fn-cll-append-is-append)
           :induct (fn-cll-values-p keys)))))
(local
 (defun o1s-cl-ls (lock keys)
  (declare (xargs :verify-guards nil))
  (append (if lock (list (append *fn-cll-lock-head* lock)) nil)
          (if (consp keys) (list (append *fn-cll-key-field* (fn-cll-key-values keys))) nil))))

(local
 (defthm o1s-cl-lines-are-lines
  (equal (fn-cll-lines lock keys) (o1s-octets (o1s-cl-ls lock keys)))
  :hints (("Goal" :in-theory (enable fn-cll-lines fn-cll-line fn-cll-key-line o1s-cl-ls o1s-octets
                                     fn-cll-append-is-append)))))

(local
 (defthm o1s-census-of-cl-lines
  (implies (and (fn-cll-valuep lock) (<= (len lock) 44) (fn-cll-values-p keys))
           (and (<= (fn-article-header-field-count (append (fn-cll-lines lock keys) r))
                    (+ 2 (fn-article-header-field-count r)))
                (<= (fn-article-header-line-count (append (fn-cll-lines lock keys) r))
                    (+ 2 (fn-article-header-line-count r)))
                (<= (fn-article-header-octet-count (append (fn-cll-lines lock keys) r))
                    (+ 1066 (fn-article-header-octet-count r)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1s-cl-ls o1s-linesp o1s-cost) (o1s-census-of-lines fn-ipp-no-crlfp fn-cll-lines))
           :use ((:instance o1s-census-of-lines (ls (o1s-cl-ls lock keys))))))))
(local
 (defun o1s-split (x)
  (declare (xargs :verify-guards nil))
  (cond ((atom x) :none)
        ((and (equal (car x) 13) (consp (cdr x)) (equal (cadr x) 10))
         (cons nil (cddr x)))
        (t (let ((r (o1s-split (cdr x))))
             (if (consp r) (cons (cons (car x) (car r)) (cdr r)) :none))))))

(local
 (defthm o1s-split-true-listp
  (implies (consp (o1s-split x)) (true-listp (car (o1s-split x))))
  :hints (("Goal" :in-theory (enable o1s-split)))))

(local
 (defthm o1s-split-reassembles
  (implies (consp (o1s-split x))
           (equal (append (car (o1s-split x)) (list* 13 10 (cdr (o1s-split x))))
                  x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable o1s-split)))))

(local
 (defthm o1s-split-shorter
  (implies (consp (o1s-split x))
           (< (len (cdr (o1s-split x))) (len x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable o1s-split)))))

(local
 (defthm o1s-aux-good
  (implies (and (true-listp acc) (natp left)
                (consp (o1s-split x))
                (fn-ipp-no-crlfp (car (o1s-split x)))
                (<= (len (car (o1s-split x))) left))
           (equal (fn-article-next-line-aux x acc left)
                  (list :ok (append (reverse acc) (car (o1s-split x)))
                        (cdr (o1s-split x)))))
  :hints (("Goal" :induct (fn-article-next-line-aux x acc left)
           :in-theory (enable fn-article-next-line-aux o1s-split fn-ipp-no-crlfp)))))

(local
 (defthm o1s-aux-bad
  (implies (and (true-listp acc) (natp left)
                (not (and (consp (o1s-split x))
                          (fn-ipp-no-crlfp (car (o1s-split x)))
                          (<= (len (car (o1s-split x))) left))))
           (equal (car (fn-article-next-line-aux x acc left)) :error))
  :hints (("Goal" :induct (fn-article-next-line-aux x acc left)
           :in-theory (enable fn-article-next-line-aux o1s-split fn-ipp-no-crlfp)))))
(local
 (defun o1s-goodp (s)
  (declare (xargs :verify-guards nil))
  (and (consp s) (consp (car s)) (fn-ipp-no-crlfp (car s)) (<= (len (car s)) 998))))

(local
 (defthm o1s-next-line-char-good
  (implies (o1s-goodp (o1s-split x))
           (equal (fn-article-next-line x)
                  (list :ok (car (o1s-split x)) (cdr (o1s-split x)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-article-next-line o1s-goodp) (o1s-aux-good o1s-aux-bad))
           :use ((:instance o1s-aux-good (acc nil) (left 998)))))))

(local
 (defthm o1s-split-car-atom
  (implies (and (consp (o1s-split x)) (not (consp (car (o1s-split x)))))
           (equal (car (o1s-split x)) nil))
  :hints (("Goal" :in-theory (enable o1s-split)))))

(local
 (defthm o1s-next-line-char-bad
  (implies (not (o1s-goodp (o1s-split x)))
           (or (not (fn-article-line-okp (fn-article-next-line x)))
               (null (fn-article-line-value (fn-article-next-line x)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-article-next-line fn-article-line-okp fn-article-line-value o1s-goodp)
                           (o1s-aux-good o1s-aux-bad))
           :use ((:instance o1s-aux-bad (acc nil) (left 998))
                 (:instance o1s-aux-good (acc nil) (left 998))
                 (:instance o1s-split-true-listp))))))

(local
 (defthm o1s-field-count-char
  (equal (fn-article-header-field-count x)
         (if (o1s-goodp (o1s-split x))
             (+ (if (fn-article-wspp (car (car (o1s-split x)))) 0 1)
                (fn-article-header-field-count (cdr (o1s-split x))))
           0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-next-line o1s-split o1s-next-line-char-good o1s-next-line-char-bad
                               fn-ahl-no-lines-no-fields-no-octets)
           :use (o1s-next-line-char-good o1s-next-line-char-bad)
           :expand ((fn-article-header-field-count x))))))

(local
 (defthm o1s-line-count-char
  (equal (fn-article-header-line-count x)
         (if (o1s-goodp (o1s-split x))
             (+ 1 (fn-article-header-line-count (cdr (o1s-split x))))
           0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-next-line o1s-split o1s-next-line-char-good o1s-next-line-char-bad
                               fn-ahl-no-lines-no-fields-no-octets)
           :use (o1s-next-line-char-good o1s-next-line-char-bad)
           :expand ((fn-article-header-line-count x))))))

(local
 (defthm o1s-octet-count-char
  (equal (fn-article-header-octet-count x)
         (if (o1s-goodp (o1s-split x))
             (+ 2 (len (car (o1s-split x)))
                (fn-article-header-octet-count (cdr (o1s-split x))))
           0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-next-line o1s-split o1s-next-line-char-good o1s-next-line-char-bad
                               fn-ahl-no-lines-no-fields-no-octets)
           :use (o1s-next-line-char-good o1s-next-line-char-bad)
           :expand ((fn-article-header-octet-count x))))))
(local
 (defun o1s-ins (x k ins)
  (declare (xargs :verify-guards nil))
  (if (zp k)
      (append ins x)
    (cons (car x) (o1s-ins (cdr x) (1- k) ins)))))

(local
 (defthm o1s-split-none
  (implies (not (consp (o1s-split x))) (equal (o1s-split x) :none))
  :hints (("Goal" :in-theory (enable o1s-split)))))

(local
 (defthm o1s-split-of-append-ins
  (implies (fn-ipp-no-crlfp ins)
           (equal (o1s-split (append ins y))
                  (let ((s (o1s-split y)))
                    (if (consp s)
                        (cons (append ins (car s)) (cdr s))
                      :none))))
  :hints (("Goal" :induct (fn-ipp-no-crlfp ins)
           :in-theory (enable o1s-split fn-ipp-no-crlfp)))))

(local
 (defun o1s-ind (x k)
  (declare (xargs :verify-guards nil))
  (cond ((atom x) k)
        ((and (equal (car x) 13) (consp (cdr x)) (equal (cadr x) 10)) k)
        (t (o1s-ind (cdr x) (1- k))))))

(local
 (defthm o1s-car-ins
  (implies (posp k) (equal (car (o1s-ins x k ins)) (car x)))
  :hints (("Goal" :expand ((o1s-ins x k ins))))))

(local
 (defthm o1s-cdr-ins
  (implies (posp k) (equal (cdr (o1s-ins x k ins)) (o1s-ins (cdr x) (1- k) ins)))
  :hints (("Goal" :expand ((o1s-ins x k ins))))))

(local
 (defthm o1s-consp-ins
  (implies (posp k) (consp (o1s-ins x k ins)))
  :hints (("Goal" :expand ((o1s-ins x k ins))))))

(local
 (defthm o1s-ins-zero
  (equal (o1s-ins x 0 ins) (append ins x))
  :hints (("Goal" :expand ((o1s-ins x 0 ins))))))

(local
 (defthm o1s-ins-one
  (equal (o1s-ins x 1 ins) (cons (car x) (append ins (cdr x))))
  :hints (("Goal" :expand ((o1s-ins x 1 ins))))))

(local
 (defthm o1s-split-of-ins
  (implies (and (fn-ipp-no-crlfp ins) (natp k) (<= 1 k) (<= k (len x))
                (not (equal (nth (1- k) x) 13)) (not (equal (nth (1- k) x) 10)))
           (equal (o1s-split (o1s-ins x k ins))
                  (let ((s (o1s-split x)))
                    (if (consp s)
                        (if (<= k (len (car s)))
                            (cons (o1s-ins (car s) k ins) (cdr s))
                          (cons (car s) (o1s-ins (cdr s) (- k (+ 2 (len (car s)))) ins)))
                      :none))))
  :hints (("Goal" :induct (o1s-ind x k)
           :in-theory (e/d (o1s-split) (o1s-ins))
           :do-not-induct nil)
          ("Subgoal *1/3" :cases ((equal k 1))))))
(local
 (defthm o1s-nocrlf-of-ins
  (implies (and (fn-ipp-no-crlfp ins) (natp k) (<= k (len a)))
           (equal (fn-ipp-no-crlfp (o1s-ins a k ins)) (fn-ipp-no-crlfp a)))
  :hints (("Goal" :induct (o1s-ins a k ins)
           :in-theory (enable o1s-ins fn-ipp-no-crlfp)))))

(local
 (defthm o1s-len-of-ins
  (implies (and (true-listp ins) (natp k) (<= k (len a)))
           (equal (len (o1s-ins a k ins)) (+ (len a) (len ins))))
  :hints (("Goal" :induct (o1s-ins a k ins)
           :in-theory (enable o1s-ins)))))

(local
 (defthm o1s-nth-of-append
  (implies (and (true-listp a) (natp j))
           (equal (nth (+ (len a) j) (append a b)) (nth j b)))
  :hints (("Goal" :induct (len a)))))

(local
 (defthm o1s-nth-of-split
  (implies (and (consp (o1s-split x)) (natp j))
           (equal (nth (+ (len (car (o1s-split x))) j) x)
                  (nth j (list* 13 10 (cdr (o1s-split x))))))
  :hints (("Goal" :in-theory (disable o1s-nth-of-append)
           :use ((:instance o1s-split-reassembles)
                 (:instance o1s-nth-of-append (a (car (o1s-split x))) (b (list* 13 10 (cdr (o1s-split x))))))))))

(local
 (defthm o1s-len-of-split
  (implies (consp (o1s-split x))
           (equal (len x) (+ 2 (len (car (o1s-split x))) (len (cdr (o1s-split x))))))
  :hints (("Goal" :use ((:instance o1s-split-reassembles))))))

(local
 (defun o1s-ind2 (x k)
  (declare (xargs :verify-guards nil :measure (len x)))
  (let ((s (o1s-split x)))
    (if (and (consp s) (< (len (car s)) k))
        (o1s-ind2 (cdr s) (- k (+ 2 (len (car s)))))
      k))))
(local
 (defun o1s-nf (x)
  (declare (xargs :verify-guards nil :measure (len x)))
  (let ((s (o1s-split x)))
    (if (o1s-goodp s)
        (+ (if (fn-article-wspp (car (car s))) 0 1) (o1s-nf (cdr s)))
      0))))
(local
 (defun o1s-nl (x)
  (declare (xargs :verify-guards nil :measure (len x)))
  (let ((s (o1s-split x)))
    (if (o1s-goodp s) (+ 1 (o1s-nl (cdr s))) 0))))
(local
 (defun o1s-no (x)
  (declare (xargs :verify-guards nil :measure (len x)))
  (let ((s (o1s-split x)))
    (if (o1s-goodp s) (+ 2 (len (car s)) (o1s-no (cdr s))) 0))))

(local
 (defthm o1s-goodp-shorter
  (implies (o1s-goodp (o1s-split x)) (< (len (cdr (o1s-split x))) (len x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable o1s-goodp)))))

(local
 (defthm o1s-counts-are-recursions
  (and (equal (fn-article-header-field-count x) (o1s-nf x))
       (equal (fn-article-header-line-count x) (o1s-nl x))
       (equal (fn-article-header-octet-count x) (o1s-no x)))
  :hints (("Goal" :induct (o1s-nf x)
           :in-theory (disable fn-article-header-field-count fn-article-header-line-count
                               fn-article-header-octet-count o1s-split))
          ("Subgoal *1/2" :use (o1s-field-count-char o1s-line-count-char o1s-octet-count-char)
                          :in-theory (disable fn-article-header-field-count fn-article-header-line-count
                               fn-article-header-octet-count o1s-split))
          ("Subgoal *1/1" :use (o1s-field-count-char o1s-line-count-char o1s-octet-count-char)
                          :in-theory (disable fn-article-header-field-count fn-article-header-line-count
                               fn-article-header-octet-count o1s-split)))))
(local
 (defun o1s-ok (x k)
  (declare (xargs :verify-guards nil :measure (len x)))
  (let ((s (o1s-split x)))
    (if (and (consp s) (< (len (car s)) k))
        (and (< (+ 2 (len (car s))) k)
             (o1s-ok (cdr s) (- k (+ 2 (len (car s))))))
      (and (not (equal (nth (1- k) x) 13)) (not (equal (nth (1- k) x) 10)))))))

(local
 (defthm o1s-nth-of-list*
  (implies (and (natp j) (<= 2 j))
           (equal (nth j (list* 13 10 r)) (nth (- j 2) r)))
  :hints (("Goal" :expand ((nth j (list* 13 10 r)) (nth (+ -1 j) (cons 10 r)))))))

(local
 (defthm o1s-nth-after-line
  (implies (and (consp (o1s-split x)) (natp k) (< (+ 2 (len (car (o1s-split x)))) k))
           (equal (nth (+ -1 k) x)
                  (nth (+ -1 (- k (+ 2 (len (car (o1s-split x)))))) (cdr (o1s-split x)))))
  :hints (("Goal" :use ((:instance o1s-nth-of-split
                                   (j (+ -1 (- k (len (car (o1s-split x))))))))
           :in-theory (disable o1s-nth-of-split nth)))))

(local
 (defthm o1s-ok-from-nth
  (implies (and (natp k) (<= 1 k) (<= k (len x))
                (not (equal (nth (1- k) x) 13)) (not (equal (nth (1- k) x) 10)))
           (o1s-ok x k))
  :hints (("Goal" :induct (o1s-ind2 x k)
           :in-theory (disable nth o1s-nth-of-split o1s-nth-after-line)
           :do-not-induct nil)
          ("Subgoal *1/1" :cases ((equal k (+ 1 (len (car (o1s-split x)))))
                                  (equal k (+ 2 (len (car (o1s-split x))))))
                          :use ((:instance o1s-nth-of-split (j 0))
                                (:instance o1s-nth-of-split (j 1))
                                o1s-nth-after-line o1s-len-of-split))
          ("Subgoal *1/2" :use ((:instance o1s-nth-of-split (j 0))
                                (:instance o1s-nth-of-split (j 1))
                                o1s-nth-after-line o1s-len-of-split)))))

(local
 (defthm o1s-ok-nth
  (implies (and (natp k) (<= 1 k) (<= k (len x)) (o1s-ok x k))
           (and (not (equal (nth (1- k) x) 13)) (not (equal (nth (1- k) x) 10))))
  :hints (("Goal" :induct (o1s-ind2 x k)
           :in-theory (disable nth o1s-nth-of-split o1s-nth-after-line)
           :do-not-induct nil)
          ("Subgoal *1/1" :use (o1s-nth-after-line o1s-len-of-split))
          ("Subgoal *1/2" :use (o1s-nth-after-line o1s-len-of-split)))))
(local
 (defthm o1s-goodp-of-ins
  (implies (and (fn-ipp-no-crlfp ins) (true-listp ins) (natp k) (<= 1 k) (<= k (len a))
                (o1s-goodp (cons (o1s-ins a k ins) r)))
           (and (o1s-goodp (cons a r))
                (equal (car (o1s-ins a k ins)) (car a))
                (equal (len (o1s-ins a k ins)) (+ (len a) (len ins)))))
  :hints (("Goal" :in-theory (e/d (o1s-goodp) (o1s-ins))))))

(local
 (defthm o1s-census-of-ins
  (implies (and (fn-ipp-no-crlfp ins) (true-listp ins) (natp k) (<= 1 k) (<= k (len x))
                (o1s-ok x k))
           (and (<= (o1s-nf (o1s-ins x k ins)) (o1s-nf x))
                (<= (o1s-nl (o1s-ins x k ins)) (o1s-nl x))
                (<= (o1s-no (o1s-ins x k ins)) (+ (len ins) (o1s-no x)))))
  :hints (("Goal" :induct (o1s-ind2 x k)
           :in-theory (e/d (o1s-goodp) (o1s-ins o1s-split nth o1s-nf o1s-nl o1s-no))
           :expand ((o1s-nf x) (o1s-nl x) (o1s-no x)
                    (o1s-nf (o1s-ins x k ins)) (o1s-nl (o1s-ins x k ins)) (o1s-no (o1s-ins x k ins)))))))
(local
 (defthm o1s-take-drop-zero
  (and (equal (fn-inj-take-n 0 x) nil) (equal (fn-inj-drop-n 0 x) x))
  :hints (("Goal" :expand ((fn-inj-take-n 0 x) (fn-inj-drop-n 0 x))))))

(local
 (defthm o1s-splice-is-ins
  (implies (and (natp k) (<= k (len x)) (true-listp ins))
           (equal (fn-inj-splice x k ins) (o1s-ins x k ins)))
  :hints (("Goal" :induct (o1s-ins x k ins)
           :in-theory (e/d (fn-inj-splice o1s-ins) ())
           :expand ((fn-inj-take-n k x) (fn-inj-drop-n k x))))))

(local
 (defthm o1s-take-n-len
  (implies (and (natp n) (equal (len (fn-inj-take-n n x)) n))
           (<= n (len x)))
  :hints (("Goal" :induct (fn-inj-take-n n x)
           :in-theory (enable fn-inj-take-n)))))

(local
 (defthm o1s-take-n-car
  (implies (and (posp n) (consp x))
           (equal (car (fn-inj-take-n n x)) (car x)))
  :hints (("Goal" :expand ((fn-inj-take-n n x))))))

(local
 (defun o1s-ind3 (n i x)
  (declare (xargs :verify-guards nil))
  (if (or (zp i) (zp n) (atom x)) nil (o1s-ind3 (1- n) (1- i) (cdr x)))))

(local
 (defthm o1s-take-n-nth
  (implies (and (natp n) (natp i) (< i n))
           (equal (nth i (fn-inj-take-n n x)) (nth i x)))
  :hints (("Goal" :induct (o1s-ind3 n i x)
           :in-theory (enable fn-inj-take-n)))))

(local
 (defthm o1s-openp-facts
  (implies (fn-inj-path-openp x)
           (and (<= 6 (len x)) (equal (nth 5 x) 32)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-inj-path-openp) (o1s-take-n-len o1s-take-n-nth))
           :use ((:instance o1s-take-n-len (n 6)) (:instance o1s-take-n-nth (n 6) (i 5)))))))

(local
 (defthm o1s-scan-ge1
  (implies (fn-inj-path-scan x bol)
           (and (natp (fn-inj-path-scan x bol))
                (<= 1 (fn-inj-path-scan x bol))))
  :rule-classes ((:linear :corollary (implies (fn-inj-path-scan x bol) (<= 1 (fn-inj-path-scan x bol))))
                 (:rewrite :corollary (implies (fn-inj-path-scan x bol) (natp (fn-inj-path-scan x bol)))))
  :hints (("Goal" :induct (fn-inj-path-scan x bol)
           :in-theory (e/d (fn-inj-path-scan) (fn-inj-path-openp nth))))))

(local
 (defthm o1s-nth-cons-pos
  (implies (posp s) (equal (nth s (cons a d)) (nth (1- s) d)))
  :hints (("Goal" :expand ((nth s (cons a d)))))))

(local
 (defthm o1s-scan-facts
  (implies (fn-inj-path-scan x bol)
           (and (<= (fn-inj-path-scan x bol) (len x))
                (equal (nth (1- (fn-inj-path-scan x bol)) x) 32)))
  :hints (("Goal" :induct (fn-inj-path-scan x bol)
           :in-theory (e/d (fn-inj-path-scan) (fn-inj-path-openp nth))))))
(local
 (defthm o1s-census-of-splice
  (implies (and (fn-inj-path-offset x) (fn-ipp-no-crlfp ins) (true-listp ins))
           (and (<= (fn-article-header-field-count (fn-inj-splice x (fn-inj-path-offset x) ins))
                    (fn-article-header-field-count x))
                (<= (fn-article-header-line-count (fn-inj-splice x (fn-inj-path-offset x) ins))
                    (fn-article-header-line-count x))
                (<= (fn-article-header-octet-count (fn-inj-splice x (fn-inj-path-offset x) ins))
                    (+ (len ins) (fn-article-header-octet-count x)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-inj-path-offset) (o1s-census-of-ins o1s-ok-from-nth o1s-scan-facts o1s-scan-ge1
                                                 o1s-splice-is-ins fn-inj-splice))
           :use ((:instance o1s-census-of-ins (k (fn-inj-path-scan x t)))
                 (:instance o1s-ok-from-nth (k (fn-inj-path-scan x t)))
                 (:instance o1s-scan-facts (bol t))
                 (:instance o1s-scan-ge1 (bol t))
                 (:instance o1s-splice-is-ins (k (fn-inj-path-scan x t))))))))
(local
 (defthm o1s-injected-facts
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (and (fn-inj-configp config)
                (not (fn-article-census-refusal (fn-article-header-census source)
                                                (fn-inj-config-header-limits config)))))
  :hints (("Goal" :in-theory (e/d (fn-inj-decide fn-inj-injectedp fn-inj-refuse)
                                  (fn-inj-configp fn-inj-mandatory-reason
                                   fn-inj-groups-admissiblep fn-inj-absentp
                                   fn-inj-prefix fn-inj-date-octets
                                   fn-inj-instant-of fn-inj-generated-message-id
                                   fn-inj-append floor fn-article-parse
                                   fn-af-proto-article-check fn-article-result-okp
                                   fn-article-result-article fn-article-syntax-p
                                   fn-clock-observationp fn-clock-has-wall
                                   fn-clock-wall fn-clock-monotonic fn-article-census-refusal
                                   fn-article-header-census fn-inj-block fn-inj-splice
                                   fn-inj-path-reason fn-inj-other-reason fn-inj-path-offset
                                   fn-inj-path-insert))))))
(local
 (defthm o1s-lock-value-len
  (<= (len (fn-cl-lock-value ring account msgid fields)) 44)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-cl-lock-value)
           :use ((:instance fn-cl-lock-shape (entry (fn-ns-current ring))))))))

(local
 (defthm o1s-served-is
  (equal (fn-cl-served-payload ring account msgid payload)
         (append (fn-cll-lines (fn-cl-lock-value ring account msgid (fn-ctl-received-fields payload))
                               (fn-cl-key-values ring account (fn-ctl-received-fields payload)))
                 payload))
  :hints (("Goal" :in-theory (enable fn-cl-served-payload fn-cll-append-is-append)))))

(local
 (defthm o1s-served-census
  (and (<= (fn-article-header-field-count (fn-cl-served-payload ring account msgid payload))
           (+ 2 (fn-article-header-field-count payload)))
       (<= (fn-article-header-line-count (fn-cl-served-payload ring account msgid payload))
           (+ 2 (fn-article-header-line-count payload)))
       (<= (fn-article-header-octet-count (fn-cl-served-payload ring account msgid payload))
           (+ 1066 (fn-article-header-octet-count payload))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(o1s-served-is) (theory 'minimal-theory))
           :use (o1s-served-is
                 (:instance o1s-census-of-cl-lines
                            (lock (fn-cl-lock-value ring account msgid (fn-ctl-received-fields payload)))
                            (keys (fn-cl-key-values ring account (fn-ctl-received-fields payload)))
                            (r payload))
                 (:instance fn-cl-lock-value-is-a-value
                            (fields (fn-ctl-received-fields payload)))
                 (:instance fn-cl-key-values-are-values
                            (fields (fn-ctl-received-fields payload)))
                 (:instance o1s-lock-value-len
                            (fields (fn-ctl-received-fields payload))))))))
(local
 (defthm o1s-date-shape
  (and (true-listp (fn-inj-date-octets inst)) (equal (len (fn-inj-date-octets inst)) 31))
  :hints (("Goal" :in-theory (enable fn-inj-date-octets)))))

(local
 (defthm o1s-generated-id-facts
  (implies (fn-inj-configp config)
           (let ((id (fn-inj-generated-message-id obs config)))
             (and (true-listp id) (fn-ipp-no-crlfp id)
                  (equal (len id) (+ 47 (len (fn-inj-config-agent config)))))))
  :hints (("Goal" :in-theory (e/d (fn-inj-generated-message-id o1s-inj-append) (fn-inj-configp))
           :use (o1s-config-agent-facts)))))

(local
 (defthm o1s-params-true-listp
  (true-listp (fn-ipp-params secret login addr))
  :hints (("Goal" :in-theory (e/d (fn-ipp-params fn-ipp-account-param fn-ipp-complaints-param
                                   o1s-inj-append fn-ipp-accountp)
                                  ())))))

(local
 (defthm o1s-params-okp-no-crlf
  (implies (fn-ipp-params-okp p) (fn-ipp-no-crlfp p))
  :hints (("Goal" :in-theory (enable fn-ipp-params-okp)))))

(local
 (defthm o1s-params-facts
  (and (true-listp (fn-ipp-params secret login (fn-ipp-complaints cfg)))
       (fn-ipp-no-crlfp (fn-ipp-params secret login (fn-ipp-complaints cfg))))
  :hints (("Goal" :cases ((consp (fn-ipp-params secret login (fn-ipp-complaints cfg))))
           :in-theory (disable fn-ipp-params fn-ipp-complaints fn-ipp-params-okp)
           :use (fn-ipp-params-are-a-parameter-run
                 (:instance o1s-params-true-listp (addr (fn-ipp-complaints cfg))))))))

(local
 (defthm o1s-path-insert-facts
  (implies (fn-ipp-no-crlfp agent)
           (and (true-listp (fn-inj-path-insert agent))
                (fn-ipp-no-crlfp (fn-inj-path-insert agent))
                (equal (len (fn-inj-path-insert agent)) (+ 1 (len agent)))))
  :hints (("Goal" :in-theory (enable fn-inj-path-insert)))))
(local
 (defthm o1s-injected-core
  (implies (and (equal x (if sp
                             (append (fn-ipp-block-with date msgid agent gid gdate params)
                                     (fn-inj-splice source off (fn-inj-path-insert agent)))
                           (append (fn-ipp-prefix-with date msgid agent gid gdate params) source)))
                (true-listp date) (fn-ipp-no-crlfp date) (equal (len date) 31)
                (implies gid (and (true-listp msgid) (fn-ipp-no-crlfp msgid)
                                  (equal (len msgid) (+ 47 (len agent)))))
                (true-listp agent) (consp agent) (fn-ipp-no-crlfp agent)
                (true-listp params) (fn-ipp-no-crlfp params)
                (implies sp (equal off (fn-inj-path-offset source))) (implies sp off))
           (and (<= (fn-article-header-field-count x) (+ 5 (fn-article-header-field-count source)))
                (<= (fn-article-header-line-count x) (+ 5 (fn-article-header-line-count source)))
                (<= (fn-article-header-octet-count x)
                    (+ 1170 (* 2 (len agent)) (fn-article-header-octet-count source)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable o1s-counts-are-recursions o1s-nf o1s-nl o1s-no o1s-split
                               o1s-census-of-a-prefix o1s-census-of-a-block o1s-census-of-splice
                               fn-ipp-block-with fn-ipp-prefix-with fn-inj-splice fn-inj-path-insert
                               fn-inj-path-offset o1s-path-insert-facts)
           :use ((:instance o1s-census-of-a-prefix (r source))
                 (:instance o1s-census-of-a-block
                            (r (fn-inj-splice source off (fn-inj-path-insert agent))))
                 (:instance o1s-census-of-splice (x source) (ins (fn-inj-path-insert agent)))
                 (:instance o1s-path-insert-facts))))))
(local
 (defthm o1s-injected-census
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (let ((x (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg)))
             (and (<= (fn-article-header-field-count x) (+ 5 (fn-article-header-field-count source)))
                  (<= (fn-article-header-line-count x) (+ 5 (fn-article-header-line-count source)))
                  (<= (fn-article-header-octet-count x)
                      (+ 1170 (* 2 (len (fn-inj-config-agent config)))
                         (fn-article-header-octet-count source))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable o1s-injected-core fn-ipp-injected-octets-carry-the-parameters
                               o1s-injected-facts fn-ipp-injected-octets fn-inj-decide
                               fn-ipp-block-with fn-ipp-prefix-with fn-ipp-params fn-ipp-complaints
                               fn-inj-generated-identity-is-the-clock-identity
                               o1s-generated-id-facts fn-article-parse fn-af-proto-article-check
                               fn-article-result-okp fn-article-result-article fn-inj-nth
                               o1s-params-facts o1s-date-shape o1s-date-no-crlf o1s-config-agent-facts
                               o1s-counts-are-recursions)
           :use ((:instance fn-ipp-injected-octets-carry-the-parameters (login account))
                 o1s-injected-facts
                 (:instance fn-inj-generated-identity-is-the-clock-identity (observation obs))
                 (:instance o1s-generated-id-facts)
                 (:instance o1s-params-facts (login account))
                 (:instance o1s-date-shape (inst (fn-inj-instant-of (fn-clock-wall obs))))
                 (:instance o1s-date-no-crlf (inst (fn-inj-instant-of (fn-clock-wall obs))))
                 (:instance o1s-config-agent-facts)
                 (:instance fn-inj-an-injected-supplied-path-has-an-offset)
                 (:instance o1s-injected-core
                            (x (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg))
                            (sp (fn-inj-supplies-pathp source))
                            (off (fn-inj-path-offset source))
                            (date (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall obs))))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (agent (fn-inj-config-agent config))
                            (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source))
                            (params (fn-ipp-params secret account (fn-ipp-complaints cfg)))))))))
(local
 (defthm o1s-strip-of-nil
  (implies (consp p) (equal (fn-inj-strip p nil) :no))
  :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm o1s-lines-consp
  (and (consp (fn-inj-path-line agent))
       (consp (fn-inj-injection-info-line agent))
       (consp (fn-inj-message-id-line msgid)))
  :hints (("Goal" :in-theory (enable fn-inj-path-line fn-inj-injection-info-line
                                     fn-inj-message-id-line o1s-inj-append)))))

(local
 (defthm o1s-with-params-of-nil
  (equal (fn-ipp-with-params nil msgid params) nil)
  :hints (("Goal" :in-theory (e/d (fn-ipp-with-params fn-ipp-at-stamp fn-ipp-at-msgid fn-ipp-at-date
                                   fn-ipp-at-info fn-pb-opensp)
                                  (fn-pb-path-agent))))))

(local
 (defthm o1s-counts-of-nil
  (and (equal (fn-article-header-field-count nil) 0)
       (equal (fn-article-header-line-count nil) 0)
       (equal (fn-article-header-octet-count nil) 0))))

(local
 (defthm o1s-refused-injected-octets
  (implies (not (fn-inj-injectedp (fn-inj-decide source config obs)))
           (equal (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg) nil))
  :hints (("Goal" :in-theory (e/d (fn-ipp-injected-octets) (fn-inj-decide fn-ipp-with-params fn-inj-injectedp))
           :use (fn-inj-refusal-produces-no-octets)))))

(local
 (defthm o1s-stored-census-refused
  (implies (not (fn-inj-injectedp (fn-inj-decide source config obs)))
           (let ((stored (fn-o1-post-stored-octets source config obs secret account cfg)))
             (and (<= (fn-article-header-field-count stored) 2)
                  (<= (fn-article-header-line-count stored) 2)
                  (<= (fn-article-header-octet-count stored) 1066))))
  :hints (("Goal" :in-theory (union-theories '(fn-o1-post-stored-octets o1s-refused-injected-octets
                                                       o1s-counts-of-nil)
                                             (theory 'minimal-theory))
           :use ((:instance o1s-served-census (ring secret)
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (payload (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg)))
                 o1s-refused-injected-octets o1s-counts-of-nil)))))

(local
 (defthm o1s-stored-census-injected
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (let ((stored (fn-o1-post-stored-octets source config obs secret account cfg)))
             (and (<= (fn-article-header-field-count stored) (+ 7 (fn-article-header-field-count source)))
                  (<= (fn-article-header-line-count stored) (+ 7 (fn-article-header-line-count source)))
                  (<= (fn-article-header-octet-count stored)
                      (+ 2236 (* 2 (len (fn-inj-config-agent config)))
                         (fn-article-header-octet-count source))))))
  :hints (("Goal" :in-theory (union-theories '(fn-o1-post-stored-octets)
                                             (theory 'minimal-theory))
           :use ((:instance o1s-served-census (ring secret)
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (payload (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg)))
                 o1s-injected-census)))))
(local
 (defthm o1s-counts-natp
  (and (natp (fn-article-header-field-count x))
       (natp (fn-article-header-line-count x))
       (natp (fn-article-header-octet-count x)))
  :hints (("Goal" :use ((:instance fn-article-header-field-count (octets x)))))))

(local
 (defthm o1s-len-nonneg (<= 0 (len x)) :rule-classes :linear))

(local
 (defthm o1s-limits-natp
  (and (natp (fn-article-limit-fields l)) (natp (fn-article-limit-lines l))
       (natp (fn-article-limit-octets l)))
  :hints (("Goal" :in-theory (enable fn-article-limit-fields fn-article-limit-lines fn-article-limit-octets)))))

(local
 (defthm o1s-census-within-from-no-refusal
  (implies (not (fn-article-census-refusal (fn-article-header-census src) limits))
           (and (<= (fn-article-header-field-count src) (fn-article-limit-fields limits))
                (<= (fn-article-header-line-count src) (fn-article-limit-lines limits))
                (<= (fn-article-header-octet-count src) (fn-article-limit-octets limits))))
  :hints (("Goal" :in-theory (enable fn-article-census-refusal fn-article-header-census
                                     fn-article-census-fields fn-article-census-lines
                                     fn-article-census-octets)))))

(local
 (defthm o1s-widened-within
  (implies (and (<= f (+ 7 (fn-article-limit-fields limits)))
                (<= l (+ 7 (fn-article-limit-lines limits)))
                (<= o (+ (fn-article-limit-octets limits) (fn-o1-injected-block-octets agent)))
                (natp f) (natp l) (natp o))
           (fn-article-census-within (list f l o) (fn-o1-stored-header-limits limits agent)))
  :hints (("Goal" :in-theory (enable fn-article-census-within fn-article-census-fields
                                     fn-article-census-lines fn-article-census-octets
                                     fn-o1-stored-header-limits fn-article-limits
                                     fn-article-limit-fields fn-article-limit-lines
                                     fn-article-limit-octets)))))

(local
 (defthm o1s-stored-within
  (let ((stored (fn-o1-post-stored-octets source config obs secret account cfg)))
    (fn-article-census-within
     (fn-article-header-census stored)
     (fn-o1-stored-header-limits (fn-inj-config-header-limits config) (fn-inj-config-agent config))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-article-header-census fn-o1-injected-block-octets
                                        o1s-counts-natp natp)
                                      (theory 'minimal-theory))
           :use ((:instance o1s-widened-within
                            (f (fn-article-header-field-count (fn-o1-post-stored-octets source config obs secret account cfg)))
                            (l (fn-article-header-line-count (fn-o1-post-stored-octets source config obs secret account cfg)))
                            (o (fn-article-header-octet-count (fn-o1-post-stored-octets source config obs secret account cfg)))
                            (limits (fn-inj-config-header-limits config))
                            (agent (fn-inj-config-agent config)))
                 o1s-stored-census-refused o1s-stored-census-injected o1s-injected-facts
                 (:instance o1s-limits-natp (l (fn-inj-config-header-limits config)))
                 (:instance o1s-len-nonneg (x (fn-inj-config-agent config)))
                 (:instance o1s-counts-natp
                            (x (fn-o1-post-stored-octets source config obs secret account cfg)))
                 (:instance o1s-census-within-from-no-refusal (src source)
                            (limits (fn-inj-config-header-limits config))))))))

(defthm fn-o1-stored-post-within-the-widened-limits
  (let ((stored (fn-o1-post-stored-octets source config obs secret account cfg)))
    (implies (fn-article-result-okp (fn-article-parse stored))
             (fn-article-result-okp
              (fn-article-parse-under
               stored
               (fn-o1-stored-header-limits (fn-inj-config-header-limits config)
                                           (fn-inj-config-agent config))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-article-parse-under-admits-exactly-the-limits
                            (octets (fn-o1-post-stored-octets source config obs secret account cfg))
                            (wider *fn-article-ceiling-limits*)
                            (limits (fn-o1-stored-header-limits (fn-inj-config-header-limits config)
                                                                (fn-inj-config-agent config))))
                 (:instance fn-article-parse-is-the-ceiling-limits-by-definition
                            (octets (fn-o1-post-stored-octets source config obs secret account cfg)))
                 o1s-stored-within)))
  :rule-classes nil)

; P4-1 support (all local, o1t- prefix): the stored parse keeps the source's Newsgroups, Control and
; Supersedes fields, so the decision's groups are filed within the stored bytes.

(local
 (defun o1t-line-ind (l acc left)
  (declare (xargs :measure (len l)))
  (if (consp l)
      (o1t-line-ind (cdr l) (cons (car l) acc) (1- left))
    (list acc left))))

(local
 (defthm o1t-next-line-aux-of-a-line
  (implies (and (fn-article-crlf-freep l) (true-listp l)
                (<= (len l) (nfix left)) (true-listp acc))
           (equal (fn-article-next-line-aux (append l (list* 13 10 r)) acc left)
                  (list :ok (append (reverse acc) l) r)))
  :hints (("Goal" :induct (o1t-line-ind l acc left)
           :in-theory (enable fn-article-next-line-aux)))))

(local
 (defthm o1t-next-line-of-a-line
  (implies (and (fn-article-crlf-freep l) (true-listp l) (<= (len l) 998))
           (equal (fn-article-next-line (append l (list* 13 10 r)))
                  (list :ok l r)))
  :hints (("Goal" :in-theory (enable fn-article-next-line)
           :use ((:instance o1t-next-line-aux-of-a-line (acc nil) (left 998)))))))

(local
 (defthm o1t-next-line-of-blank
  (equal (fn-article-next-line (list* 13 10 r)) (list :ok nil r))
  :hints (("Goal" :in-theory (enable fn-article-next-line fn-article-next-line-aux)))))

(local
 (defthm o1t-next-line-aux-len
  (implies (and (true-listp line-rev)
                (fn-article-line-okp (fn-article-next-line-aux octets line-rev left)))
           (<= (len (fn-article-line-value (fn-article-next-line-aux octets line-rev left)))
               (+ (len line-rev) (nfix left))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left)
           :in-theory (enable fn-article-next-line-aux)))))

(local
 (defthm o1t-next-line-len
  (implies (fn-article-line-okp (fn-article-next-line octets))
           (<= (len (fn-article-line-value (fn-article-next-line octets))) 998))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-article-next-line)
           :use ((:instance o1t-next-line-aux-len (line-rev nil) (left 998)))))))

(local
 (defun o1t-line-okp (l)
  (declare (xargs :guard t))
  (and (true-listp l) (consp l) (fn-article-crlf-freep l) (<= (len l) 998))))

(local
 (defun o1t-folds-okp (ls)
  (declare (xargs :guard t))
  (if (consp ls)
      (and (o1t-line-okp (car ls)) (fn-article-fold-linep (car ls))
           (o1t-folds-okp (cdr ls)))
    (null ls))))

(local
 (defun o1t-fold-up (f ls)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ls)
      (o1t-fold-up (fn-article-add-fold f (car ls)) (cdr ls))
    f)))

(local
 (defun o1t-fieldvp (f)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp f) (consp (car f))
       (o1t-line-okp (car (car f)))
       (not (fn-article-wspp (car (car (car f)))))
       (fn-article-line-okp (fn-article-new-field (car (car f))))
       (o1t-folds-okp (cdr (car f)))
       (equal f (o1t-fold-up (fn-article-line-value (fn-article-new-field (car (car f))))
                             (cdr (car f)))))))

(local
 (defun o1t-closedp (f)
  (declare (xargs :guard t :verify-guards nil))
  (fn-article-has-vcharp (fn-article-field-unfolded-value f))))

(local
 (defun o1t-fieldsvp (fs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (and (o1t-fieldvp (car fs)) (o1t-closedp (car fs)) (o1t-fieldsvp (cdr fs)))
    (null fs))))

(local
 (defthm o1t-fold-up-append
  (equal (o1t-fold-up f (append a b)) (o1t-fold-up (o1t-fold-up f a) b))))

(local
 (defthm o1t-folds-okp-true-listp
  (implies (o1t-folds-okp a) (true-listp a))
  :rule-classes :forward-chaining))

(local
 (defthm o1t-folds-okp-append
  (implies (true-listp a)
           (equal (o1t-folds-okp (append a b)) (and (o1t-folds-okp a) (o1t-folds-okp b))))
  :hints (("Goal" :induct (o1t-folds-okp a)))))

(local
 (defthm o1t-new-field-raw
  (implies (fn-article-line-okp (fn-article-new-field line))
           (equal (car (fn-article-line-value (fn-article-new-field line)))
                  (list line)))
  :hints (("Goal" :in-theory (enable fn-article-new-field)))))

(local
 (defthm o1t-new-field-true-listp
  (implies (fn-article-line-okp (fn-article-new-field line))
           (true-listp (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal" :in-theory (enable fn-article-new-field)))))

(local
 (defthm o1t-new-field-is-v
  (implies (and (o1t-line-okp line) (not (fn-article-wspp (car line)))
                (fn-article-line-okp (fn-article-new-field line)))
           (o1t-fieldvp (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal" :in-theory (e/d (o1t-fieldvp) (fn-article-new-field fn-article-line-value))))))

(local
 (defthm o1t-add-fold-is-v
  (implies (and (o1t-fieldvp f) (o1t-line-okp l) (fn-article-fold-linep l))
           (o1t-fieldvp (fn-article-add-fold f l)))
  :hints (("Goal" :in-theory (e/d (o1t-fieldvp fn-article-add-fold)
                                  (fn-article-new-field fn-article-line-value fn-article-fold-linep))
           :use ((:instance o1t-fold-up-append
                            (f (fn-article-line-value (fn-article-new-field (car (car f)))))
                            (a (cdr (car f))) (b (list l))))))))

(local
 (in-theory (disable o1t-fieldvp o1t-closedp)))

(local
 (defthm o1t-fieldsvp-true-listp
  (implies (o1t-fieldsvp fs) (true-listp fs))
  :rule-classes :forward-chaining))

(local
 (defthm o1t-fieldsvp-append
  (implies (true-listp a)
           (equal (o1t-fieldsvp (append a b)) (and (o1t-fieldsvp a) (o1t-fieldsvp b))))
  :hints (("Goal" :induct (o1t-fieldsvp a)))))

(local
 (defthm o1t-fieldsvp-rev
  (implies (o1t-fieldsvp a) (o1t-fieldsvp (rev a)))
  :hints (("Goal" :induct (o1t-fieldsvp a)
           :in-theory (enable rev)))))

(local
 (defthm o1t-fieldsvp-revappend
  (implies (and (o1t-fieldsvp a) (o1t-fieldsvp b))
           (o1t-fieldsvp (revappend a b)))))

(local
 (defthm o1t-fieldsvp-finish-fields
  (implies (and (o1t-fieldsvp fr)
                (or (null cur) (and (o1t-fieldvp cur) (o1t-closedp cur))))
           (o1t-fieldsvp (fn-article-finish-fields fr cur)))
  :hints (("Goal" :in-theory (enable fn-article-finish-fields)))))

(local
 (defthm o1t-true-list-nonnil-is-consp
  (implies (and (true-listp x) x) (consp x))
  :rule-classes nil))

(local
 (defthm o1t-next-line-value-consp
  (implies (and (fn-article-line-okp (fn-article-next-line octets))
                (fn-article-line-value (fn-article-next-line octets)))
           (consp (fn-article-line-value (fn-article-next-line octets))))
  :hints (("Goal" :in-theory (disable fn-article-next-line fn-article-line-value)
           :use (fn-article-next-line-value-is-list
                 (:instance o1t-true-list-nonnil-is-consp
                            (x (fn-article-line-value (fn-article-next-line octets)))))))))

(local
 (defthm o1t-next-line-value-is-a-line
  (implies (and (fn-article-line-okp (fn-article-next-line octets))
                (fn-article-line-value (fn-article-next-line octets)))
           (o1t-line-okp (fn-article-line-value (fn-article-next-line octets))))
  :hints (("Goal" :in-theory (e/d (o1t-line-okp)
                                  (fn-article-next-line fn-article-line-value))
           :use (fn-article-next-line-value-is-list
                 fn-article-next-line-value-crlf-free
                 o1t-next-line-value-consp
                 o1t-next-line-len)))))

(local
 (defthm o1t-parse-lines-fields-v
  (implies (and (true-listp octets)
                (o1t-fieldsvp fields-rev)
                (or (null current) (o1t-fieldvp current))
                (fn-article-result-okp
                 (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                         fields-rev current header-rev)))
           (o1t-fieldsvp
            (fn-article-fields
             (fn-article-result-article
              (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                      fields-rev current header-rev)))))
  :hints (("Goal"
           :induct (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                           fields-rev current header-rev)
           :in-theory (e/d (fn-article-parse-lines fn-article-ok fn-article-make
                            fn-article-fields fn-article-result-okp fn-article-result-article
                            fn-article-field-closedp o1t-closedp)
                           (fn-article-next-line fn-article-next-line-aux
                            fn-article-new-field fn-article-add-fold
                            fn-article-finish-fields fn-article-body-crlfp
                            fn-article-header-rev-add-line
                            fn-article-line-value fn-article-line-rest
                            o1t-fieldvp))))))

(local
 (defthm o1t-parse-fields-v
  (implies (fn-article-result-okp (fn-article-parse octets))
           (o1t-fieldsvp (fn-article-fields (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance o1t-parse-lines-fields-v
                  (limits *fn-article-ceiling-limits*) (lines-left (1+ *fn-article-max-octets*))
                  (header-bytes 0) (nfields 0) (fields-rev nil) (current nil)
                  (header-rev nil)))
           :in-theory (e/d (fn-article-parse fn-article-parse-under
                            fn-article-octets-are-proper-list)
                           (fn-article-parse-lines fn-cbor-at-mostp
                            o1t-parse-lines-fields-v))))))

(local
 (defun o1t-nlines (fs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (+ (len (car (car fs))) (o1t-nlines (cdr fs)))
    0)))

(local
 (defun o1t-hr-lines (hr lines)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp lines)
      (o1t-hr-lines (fn-article-header-rev-add-line hr (car lines)) (cdr lines))
    hr)))

(local
 (defun o1t-run-fr (fs fr cur)
  (declare (xargs :guard t))
  (if (consp fs)
      (o1t-run-fr (cdr fs) (if cur (cons cur fr) fr) (car fs))
    fr)))

(local
 (defun o1t-run-cur (fs cur)
  (declare (xargs :guard t))
  (if (consp fs) (o1t-run-cur (cdr fs) (car fs)) cur)))

(local
 (defun o1t-run-nf (fs nf cur)
  (declare (xargs :guard t))
  (if (consp fs)
      (o1t-run-nf (cdr fs) (if cur (+ 1 (nfix nf)) nf) (car fs))
    nf)))

(local
 (defun o1t-run-hr (fs hr)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (o1t-run-hr (cdr fs) (o1t-hr-lines hr (car (car fs))))
    hr)))

(local
 (defthm o1t-new-field-consp
  (implies (fn-article-line-okp (fn-article-new-field line))
           (consp (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal" :in-theory (enable fn-article-new-field)))))

(local
 (defthm o1t-parse-lines-of-a-fold
  (implies (and (o1t-line-okp l) (fn-article-fold-linep l) cur
                (posp nl) (natp hb)
                (<= (+ hb (len l) 2) (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines (append l (list* 13 10 rest))
                                          limits nl hb nf fr cur hr)
                  (fn-article-parse-lines rest limits (1- nl) (+ hb (len l) 2) nf fr
                                          (fn-article-add-fold cur l)
                                          (fn-article-header-rev-add-line hr l))))
  :hints (("Goal"
           :expand ((:free (cur hr nf fr)
                     (fn-article-parse-lines (append l (list* 13 10 rest))
                                             limits nl hb nf fr cur hr)))
           :in-theory (e/d (o1t-line-okp fn-article-fold-linep fn-article-wspp)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-header-bytes-p fn-article-has-vcharp
                            binary-append))
           :do-not-induct t))))

(local
 (defun o1t-folds-ind (ls cur nl hb hr)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ls)
      (o1t-folds-ind (cdr ls) (fn-article-add-fold cur (car ls)) (1- nl)
                     (+ hb (len (car ls)) 2)
                     (fn-article-header-rev-add-line hr (car ls)))
    (list cur nl hb hr))))

(local
 (defthm o1t-parse-lines-of-folds
  (implies (and (o1t-folds-okp ls) cur (natp nl) (natp hb)
                (<= (len ls) nl)
                (<= (+ hb (len (fn-article-lines-octets ls))) (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines (append (fn-article-lines-octets ls) rest)
                                          limits nl hb nf fr cur hr)
                  (fn-article-parse-lines rest limits (- nl (len ls))
                                          (+ hb (len (fn-article-lines-octets ls)))
                                          nf fr (o1t-fold-up cur ls) (o1t-hr-lines hr ls))))
  :hints (("Goal"
           :induct (o1t-folds-ind ls cur nl hb hr)
           :in-theory (e/d (fn-article-lines-octets)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-fold-linep))))))

(local
 (defthm o1t-parse-lines-of-a-new-field-line
  (implies (and (o1t-line-okp l) (not (fn-article-wspp (car l)))
                (fn-article-line-okp (fn-article-new-field l))
                (posp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (+ hb (len l) 2) (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines (append l (list* 13 10 rest))
                                          limits nl hb nf fr cur hr)
                  (fn-article-parse-lines rest limits (1- nl) (+ hb (len l) 2)
                                          (if cur (+ 1 nf) nf)
                                          (if cur (cons cur fr) fr)
                                          (fn-article-line-value (fn-article-new-field l))
                                          (fn-article-header-rev-add-line hr l))))
  :hints (("Goal"
           :expand ((:free (cur hr nf fr)
                     (fn-article-parse-lines (append l (list* 13 10 rest))
                                             limits nl hb nf fr cur hr)))
           :in-theory (e/d (o1t-line-okp fn-article-field-closedp)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-limit-fields fn-article-new-field
                            fn-article-header-bytes-p fn-article-has-vcharp
                            binary-append))
           :do-not-induct t))))

(local
 (defthm o1t-parse-lines-of-a-built-field
  (implies (and (o1t-line-okp l1) (not (fn-article-wspp (car l1)))
                (fn-article-line-okp (fn-article-new-field l1))
                (o1t-folds-okp folds)
                (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (+ 1 (len folds)) nl)
                (<= (+ hb (len l1) 2 (len (fn-article-lines-octets folds)))
                    (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-lines-octets (cons l1 folds)) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (+ 1 (len folds)))
                   (+ hb (len l1) 2 (len (fn-article-lines-octets folds)))
                   (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr)
                   (o1t-fold-up (fn-article-line-value (fn-article-new-field l1)) folds)
                   (o1t-hr-lines hr (cons l1 folds)))))
  :hints (("Goal"
           :in-theory (e/d (fn-article-lines-octets)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-limit-fields fn-article-new-field
                            fn-article-has-vcharp fn-article-line-value
                            o1t-parse-lines-of-a-new-field-line
                            o1t-parse-lines-of-folds))
           :do-not-induct t
           :use ((:instance o1t-parse-lines-of-a-new-field-line
                            (l l1) (rest (append (fn-article-lines-octets folds) rest)))
                 (:instance o1t-parse-lines-of-folds
                            (ls folds) (cur (fn-article-line-value (fn-article-new-field l1)))
                            (nl (1- nl)) (hb (+ hb (len l1) 2))
                            (nf (if cur (+ 1 nf) nf)) (fr (if cur (cons cur fr) fr))
                            (hr (fn-article-header-rev-add-line hr l1))))))))

(local
 (defthm o1t-cons-car-cdr
  (implies (consp x) (equal (cons (car x) (cdr x)) x))))

(local
 (defthm o1t-parse-lines-of-a-built-field-ls
  (implies (and (consp ls) (o1t-line-okp (car ls)) (not (fn-article-wspp (car (car ls))))
                (fn-article-line-okp (fn-article-new-field (car ls)))
                (o1t-folds-okp (cdr ls))
                (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (len ls) nl)
                (<= (+ hb (len (fn-article-lines-octets ls))) (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-lines-octets ls) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (len ls))
                   (+ hb (len (fn-article-lines-octets ls)))
                   (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr)
                   (o1t-fold-up (fn-article-line-value (fn-article-new-field (car ls))) (cdr ls))
                   (o1t-hr-lines hr ls))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-article-parse-lines fn-article-limit-octets fn-article-limit-fields
                               fn-article-new-field fn-article-line-value o1t-hr-lines
                               o1t-parse-lines-of-a-built-field)
           :expand ((len ls) (fn-article-lines-octets ls))
           :use ((:instance o1t-parse-lines-of-a-built-field
                            (l1 (car ls)) (folds (cdr ls))))))))

(local
 (defthm o1t-parse-lines-of-a-field
  (implies (and (o1t-fieldvp f)
                (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (len (car f)) nl)
                (<= (+ hb (len (fn-article-lines-octets (car f))))
                    (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-lines-octets (car f)) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (len (car f)))
                   (+ hb (len (fn-article-lines-octets (car f))))
                   (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr)
                   f (o1t-hr-lines hr (car f)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (o1t-fieldvp)
                           (fn-article-parse-lines fn-article-lines-octets
                            fn-article-limit-octets fn-article-limit-fields
                            fn-article-new-field fn-article-line-value
                            o1t-parse-lines-of-a-built-field-ls o1t-hr-lines))
           :use ((:instance o1t-parse-lines-of-a-built-field-ls (ls (car f))))))))

(local
 (defun o1t-fields-ind (fs nl hb nf fr cur hr)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (o1t-fields-ind (cdr fs) (- nl (len (car (car fs))))
                      (+ hb (len (fn-article-lines-octets (car (car fs)))))
                      (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr) (car fs)
                      (o1t-hr-lines hr (car (car fs))))
    (list nl hb nf fr cur hr))))

(local
 (defthm o1t-parse-lines-of-fields
  (implies (and (o1t-fieldsvp fs) (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (o1t-nlines fs) nl)
                (<= (+ hb (len (fn-article-fields-octets fs))) (fn-article-limit-octets limits))
                (<= (+ nf (if cur 1 0) (len fs)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-fields-octets fs) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (o1t-nlines fs))
                   (+ hb (len (fn-article-fields-octets fs)))
                   (o1t-run-nf fs nf cur) (o1t-run-fr fs fr cur)
                   (o1t-run-cur fs cur) (o1t-run-hr fs hr))))
  :hints (("Goal"
           :induct (o1t-fields-ind fs nl hb nf fr cur hr)
           :in-theory (e/d (o1t-closedp)
                           (fn-article-parse-lines fn-article-limit-octets
                            fn-article-limit-fields fn-article-lines-octets
                            o1t-hr-lines))))))

(local
 (defthm o1t-parse-lines-of-the-blank-line
  (implies (and (posp nl) (fn-article-body-crlfp body)
                (fn-article-field-closedp cur) (true-listp hr))
           (equal (fn-article-parse-lines (cons 13 (cons 10 body))
                                          limits nl hb nf fr cur hr)
                  (fn-article-ok
                   (fn-article-make (rev hr) body (fn-article-finish-fields fr cur)))))
  :hints (("Goal"
           :expand ((fn-article-parse-lines (cons 13 (cons 10 body))
                                            limits nl hb nf fr cur hr))
           :in-theory (disable fn-article-parse-lines fn-article-field-closedp
                               fn-article-body-crlfp fn-article-finish-fields)
           :use ((:instance fn-article-blank-line-partitions-input (octets (cons 13 (cons 10 body)))))))))

(local
 (defthm o1t-hr-lines-true-listp
  (implies (true-listp hr) (true-listp (o1t-hr-lines hr lines)))
  :hints (("Goal" :in-theory (enable fn-article-header-rev-add-line)))))

(local
 (defthm o1t-run-hr-true-listp
  (implies (true-listp hr) (true-listp (o1t-run-hr fs hr)))
  :hints (("Goal" :in-theory (disable o1t-hr-lines)))))

(local
 (defthm o1t-run-cur-closed
  (implies (and (o1t-fieldsvp fs)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur))))
           (fn-article-field-closedp (o1t-run-cur fs cur)))
  :hints (("Goal" :in-theory (enable fn-article-field-closedp o1t-closedp)))))

(local
 (defthm o1t-parse-lines-of-fields-and-body
  (implies (and (o1t-fieldsvp fs) (natp nl) (natp hb) (natp nf) (true-listp hr)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (< (o1t-nlines fs) nl)
                (<= (+ hb (len (fn-article-fields-octets fs))) (fn-article-limit-octets limits))
                (<= (+ nf (if cur 1 0) (len fs)) (fn-article-limit-fields limits))
                (fn-article-body-crlfp body))
           (equal (fn-article-parse-lines
                   (append (fn-article-fields-octets fs) (cons 13 (cons 10 body)))
                   limits nl hb nf fr cur hr)
                  (fn-article-ok
                   (fn-article-make (rev (o1t-run-hr fs hr)) body
                                    (fn-article-finish-fields (o1t-run-fr fs fr cur)
                                                              (o1t-run-cur fs cur))))))
  :hints (("Goal"
           :in-theory (disable fn-article-parse-lines fn-article-limit-octets
                               fn-article-limit-fields o1t-run-hr o1t-run-fr o1t-run-cur
                               o1t-run-nf fn-article-field-closedp o1t-nlines
                               fn-article-finish-fields fn-article-body-crlfp)
           :use ((:instance o1t-parse-lines-of-fields (rest (cons 13 (cons 10 body))))
                 (:instance o1t-parse-lines-of-the-blank-line
                            (nl (- nl (o1t-nlines fs)))
                            (hb (+ hb (len (fn-article-fields-octets fs))))
                            (nf (o1t-run-nf fs nf cur)) (fr (o1t-run-fr fs fr cur))
                            (cur (o1t-run-cur fs cur)) (hr (o1t-run-hr fs hr))))))))

(local
 (defthm o1t-reverse-is-rev
  (implies (true-listp x) (equal (reverse x) (rev x)))
  :hints (("Goal" :in-theory (enable rev)))))

(local
 (defthm o1t-finish-fields-of-the-run
  (implies (and (o1t-fieldsvp fs) (true-listp fr))
           (equal (fn-article-finish-fields (o1t-run-fr fs fr cur) (o1t-run-cur fs cur))
                  (append (fn-article-finish-fields fr cur) fs)))
  :hints (("Goal" :induct (o1t-fields-ind fs nl hb nf fr cur hr)
           :in-theory (e/d (fn-article-finish-fields) (o1t-hr-lines))))))

(local
 (defun o1t-tl-linesp (ls)
  (declare (xargs :guard t))
  (if (consp ls) (and (true-listp (car ls)) (o1t-tl-linesp (cdr ls))) t)))

(local
 (defthm o1t-folds-okp-tl-linesp
  (implies (o1t-folds-okp ls) (o1t-tl-linesp ls))))

(local
 (defthm o1t-fieldvp-tl-lines
  (implies (o1t-fieldvp f) (o1t-tl-linesp (car f)))
  :hints (("Goal" :in-theory (enable o1t-fieldvp)
           :use ((:instance o1t-cons-car-cdr (x (car f))))))))

(local
 (defthm o1t-hr-lines-recompose
  (implies (and (true-listp hr) (o1t-tl-linesp ls))
           (equal (rev (o1t-hr-lines hr ls))
                  (append (rev hr) (fn-article-lines-octets ls))))
  :hints (("Goal" :induct (o1t-hr-lines hr ls)
           :in-theory (e/d (fn-article-lines-octets)
                           (fn-article-header-rev-add-line fn-article-header-rev-add-line-recomposes))
           :do-not-induct t)
          ("Subgoal *1/1" :use ((:instance fn-article-header-rev-add-line-recomposes
                                           (header-rev hr) (line (car ls)))
                                (:instance fn-article-extended-header-is-list
                                           (header-rev hr) (line (car ls))))))))

(local
 (defthm o1t-run-hr-recompose
  (implies (and (o1t-fieldsvp fs) (true-listp hr))
           (equal (rev (o1t-run-hr fs hr))
                  (append (rev hr) (fn-article-fields-octets fs))))
  :hints (("Goal" :induct (o1t-fields-ind fs nl hb nf fr cur hr)
           :in-theory (e/d () (o1t-hr-lines fn-article-lines-octets))))))

(local
 (defthm o1t-len-le-len-append
  (<= (len b) (len (append a b)))
  :rule-classes :linear))

(local
 (defthm o1t-lines-le-octets
  (<= (len ls) (len (fn-article-lines-octets ls)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-article-lines-octets)))))

(local
 (defthm o1t-nlines-le-octets
  (implies (o1t-fieldsvp fs)
           (<= (o1t-nlines fs) (len (fn-article-fields-octets fs))))
  :rule-classes :linear
  :hints (("Goal" :induct (o1t-nlines fs)
           :in-theory (e/d () (fn-article-lines-octets))))))

(local
 (defthm o1t-fields-le-nlines
  (implies (o1t-fieldsvp fs)
           (<= (len fs) (o1t-nlines fs)))
  :rule-classes :linear
  :hints (("Goal" :induct (o1t-nlines fs)
           :in-theory (enable o1t-fieldvp)))))

(local
 (defthm o1t-parse-of-fields
  (implies (and (o1t-fieldsvp fs) (fn-article-body-crlfp body)
                (fn-cbor-octet-listp (append (fn-article-fields-octets fs)
                                             (cons 13 (cons 10 body))))
                (<= (len (append (fn-article-fields-octets fs) (cons 13 (cons 10 body))))
                    *fn-article-max-octets*))
           (equal (fn-article-parse (append (fn-article-fields-octets fs)
                                            (cons 13 (cons 10 body))))
                  (fn-article-ok (fn-article-make (fn-article-fields-octets fs) body fs))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-article-parse fn-article-parse-under fn-ap-at-most-is-length-bound)
                           (fn-article-parse-lines o1t-run-hr o1t-run-fr o1t-run-cur
                            o1t-nlines fn-article-fields-octets fn-article-finish-fields
                            fn-article-body-crlfp o1t-parse-lines-of-fields-and-body))
           :use ((:instance o1t-parse-lines-of-fields-and-body
                            (limits *fn-article-ceiling-limits*)
                            (nl (1+ *fn-article-max-octets*))
                            (hb 0) (nf 0) (fr nil) (cur nil) (hr nil))
                 (:instance o1t-finish-fields-of-the-run (fr nil) (cur nil))
                 (:instance o1t-run-hr-recompose (hr nil))
                 (:instance o1t-nlines-le-octets)
                 (:instance o1t-fields-le-nlines))))))

(local
 (defthm o1t-parse-lines-body-crlfp
  (implies (fn-article-result-okp
            (fn-article-parse-lines octets limits nl hb nf fr cur hr))
           (fn-article-body-crlfp
            (fn-article-body
             (fn-article-result-article
              (fn-article-parse-lines octets limits nl hb nf fr cur hr)))))
  :hints (("Goal"
           :induct (fn-article-parse-lines octets limits nl hb nf fr cur hr)
           :in-theory (e/d (fn-article-parse-lines fn-article-ok fn-article-make
                            fn-article-body fn-article-result-okp fn-article-result-article)
                           (fn-article-next-line fn-article-next-line-aux
                            fn-article-new-field fn-article-add-fold
                            fn-article-finish-fields fn-article-body-crlfp
                            fn-article-header-rev-add-line
                            fn-article-line-value fn-article-line-rest))))))

(local
 (defthm o1t-parse-body-crlfp
  (implies (fn-article-result-okp (fn-article-parse octets))
           (fn-article-body-crlfp
            (fn-article-body (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance o1t-parse-lines-body-crlfp
                  (limits *fn-article-ceiling-limits*) (nl (1+ *fn-article-max-octets*))
                  (hb 0) (nf 0) (fr nil) (cur nil) (hr nil)))
           :in-theory (e/d (fn-article-parse fn-article-parse-under)
                           (fn-article-parse-lines fn-cbor-at-mostp
                            o1t-parse-lines-body-crlfp))))))

(local
 (defthm o1t-parse-reconstructs
  (implies (fn-article-result-okp (fn-article-parse y))
           (let ((article (fn-article-result-article (fn-article-parse y))))
             (and (true-listp article)
                  (o1t-fieldsvp (fn-article-fields article))
                  (fn-article-body-crlfp (fn-article-body article))
                  (true-listp (fn-article-body article))
                  (equal y (append (fn-article-fields-octets (fn-article-fields article))
                                   (cons 13 (cons 10 (fn-article-body article))))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories '(fn-article-syntax-p fn-article-source
                                        fn-article-octet-list-true-listp
                                        fn-article-append-associative (:e binary-append)
                                        binary-append car-cons cdr-cons)
                                      (theory 'minimal-theory))
           :use ((:instance fn-article-successful-parse-syntax-p (octets y))
                 (:instance fn-article-successful-parse-preserves-source (octets y))
                 (:instance fn-article-successful-parse-fields-recompose-header (octets y))
                 (:instance o1t-parse-fields-v (octets y))
                 (:instance o1t-parse-body-crlfp (octets y)))))))

(local
 (defthm o1t-parse-article-true-listp
  (implies (fn-article-result-okp (fn-article-parse y))
           (true-listp (fn-article-result-article (fn-article-parse y))))
  :hints (("Goal" :use ((:instance fn-article-successful-parse-syntax-p (octets y)))
           :in-theory (e/d (fn-article-syntax-p) (fn-article-parse fn-article-result-article))))))

(local
 (defthm o1t-agree-source-newsgroups
  (implies (and (fn-article-result-okp (fn-article-parse s))
                (fn-article-result-okp (fn-article-parse r))
                (equal (fn-article-get-headers-aux
                        (fn-article-fields (fn-article-result-article (fn-article-parse s)))
                        *fn-af-newsgroups-name*)
                       (fn-article-get-headers-aux
                        (fn-article-fields (fn-article-result-article (fn-article-parse r)))
                        *fn-af-newsgroups-name*)))
           (equal (fn-o1-source-newsgroups s) (fn-o1-source-newsgroups r)))
  :hints (("Goal" :in-theory (e/d (fn-o1-source-newsgroups fn-af-newsgroups-status
                                   fn-article-get-headers)
                                  (fn-article-parse fn-article-get-headers-aux))))))

(local
 (defthm o1t-classify-fields-by-named
  (implies (and (equal (fn-ctl-fields-named *fn-ctl-control-name* fs)
                       (fn-ctl-fields-named *fn-ctl-control-name* gs))
                (equal (fn-ctl-fields-named *fn-ctl-supersedes-name* fs)
                       (fn-ctl-fields-named *fn-ctl-supersedes-name* gs)))
           (equal (fn-ctl-classify-fields fs) (fn-ctl-classify-fields gs)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ctl-classify-fields)
                                  (fn-ctl-fields-named fn-ctl-parse-command))))))

(local
 (defthm o1t-agree-classify
  (implies (and (fn-article-result-okp (fn-article-parse s))
                (fn-article-result-okp (fn-article-parse r))
                (equal (fn-ctl-fields-named
                        *fn-ctl-control-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse s))))
                       (fn-ctl-fields-named
                        *fn-ctl-control-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse r)))))
                (equal (fn-ctl-fields-named
                        *fn-ctl-supersedes-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse s))))
                       (fn-ctl-fields-named
                        *fn-ctl-supersedes-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse r))))))
           (equal (fn-ctl-classify-octets s) (fn-ctl-classify-octets r)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-classify-octets fn-ctl-classify)
                                  (fn-article-parse fn-ctl-fields-named fn-ctl-parse-command
                                   fn-ctl-classify-fields fn-article-fields
                                   fn-article-result-article))
           :use (o1t-parse-article-true-listp
                 (:instance o1t-parse-article-true-listp (y r))
                 (:instance o1t-classify-fields-by-named
                            (fs (fn-article-fields (fn-article-result-article (fn-article-parse s))))
                            (gs (fn-article-fields (fn-article-result-article (fn-article-parse r))))))))))

(local
 (defthm o1t-car-of-fold-up
  (implies (and (true-listp (car f)) (true-listp ls))
           (equal (car (o1t-fold-up f ls)) (append (car f) ls)))
  :hints (("Goal" :induct (o1t-fold-up f ls) :in-theory (enable fn-article-add-fold)))))

(local
 (defthm o1t-cadr-of-fold-up
  (equal (cadr (o1t-fold-up f ls)) (cadr f))
  :hints (("Goal" :induct (o1t-fold-up f ls) :in-theory (enable fn-article-add-fold)))))

(local
 (defthm o1t-closed-of-fold-up
  (implies (fn-article-has-vcharp (caddr f))
           (fn-article-has-vcharp (caddr (o1t-fold-up f ls))))
  :hints (("Goal" :induct (o1t-fold-up f ls) :in-theory (enable fn-article-add-fold)))))

(local
 (defthm o1t-fold-up-true-listp
  (implies (true-listp f) (true-listp (o1t-fold-up f ls)))
  :hints (("Goal" :induct (o1t-fold-up f ls) :in-theory (enable fn-article-add-fold)))))

(local (in-theory (disable o1t-fieldvp o1t-closedp)))

(local
 (defthm o1t-octet-listp-suffix
  (implies (fn-cbor-octet-listp (append a b)) (fn-cbor-octet-listp b))
  :hints (("Goal" :induct (append a b)))))

(local
 (defthm o1t-len-suffix
  (<= (len b) (len (append a b)))
  :rule-classes :linear))

(local
 (defthm o1t-reparse
  (implies (and (o1t-fieldsvp g) (fn-article-body-crlfp body)
                (fn-cbor-octet-listp tl) (<= (len tl) *fn-article-max-octets*)
                (equal tl (append (fn-article-fields-octets g) (cons 13 (cons 10 body)))))
           (and (fn-article-result-okp (fn-article-parse tl))
                (equal (fn-article-fields (fn-article-result-article (fn-article-parse tl))) g)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-article-ok fn-article-make fn-article-fields
                            fn-article-result-article fn-article-result-okp)
                           (fn-article-parse o1t-parse-of-fields fn-article-fields-octets))
           :use ((:instance o1t-parse-of-fields (fs g)))))))

(local
 (defun o1t-ind2 (a b)
  (declare (xargs :verify-guards nil))
  (if (and (consp a) (consp b)) (o1t-ind2 (cdr a) (cdr b)) nil)))

(local
 (defthm o1t-lu1
  (implies (and (fn-article-crlf-freep la) (fn-article-crlf-freep lb)
                (true-listp la) (true-listp lb)
                (equal (append la (list* 13 10 x)) (append lb (list* 13 10 y))))
           (and (equal la lb) (equal x y)))
  :rule-classes nil
  :hints (("Goal" :induct (o1t-ind2 la lb)))))

(local
 (defthm o1t-lu1-rw
  (implies (and (fn-article-crlf-freep la) (fn-article-crlf-freep lb)
                (true-listp la) (true-listp lb))
           (equal (equal (append la (list* 13 10 x)) (append lb (list* 13 10 y)))
                  (and (equal la lb) (equal x y))))
  :hints (("Goal" :cases ((equal (append la (list* 13 10 x)) (append lb (list* 13 10 y))))
           :use ((:instance o1t-lu1))))))

(local
 (defthm o1t-car-folds
  (implies (and (o1t-folds-okp b) b)
           (fn-article-wspp (car (append (fn-article-lines-octets b) v))))
  :hints (("Goal" :in-theory (enable o1t-folds-okp o1t-line-okp fn-article-lines-octets fn-article-fold-linep)))))

(local
 (defthm o1t-lu2
  (implies (and (o1t-folds-okp a) (o1t-folds-okp b)
                (not (fn-article-wspp (car u))) (not (fn-article-wspp (car v)))
                (equal (append (fn-article-lines-octets a) u)
                       (append (fn-article-lines-octets b) v)))
           (and (equal a b) (equal u v)))
  :rule-classes nil
  :hints (("Goal" :induct (o1t-ind2 a b)
           :in-theory (e/d (o1t-folds-okp o1t-line-okp fn-article-lines-octets fn-article-fold-linep)
                           (fn-article-wspp)))
          ("Subgoal *1/2" :cases ((consp b) (consp a)))
          ("Subgoal *1/1" :cases ((consp a))))))

(local
 (defun o1t-line0 (l)
  (declare (xargs :verify-guards nil))
  (and (true-listp l) (consp l) (fn-article-crlf-freep l))))

(local
 (defun o1t-rawp0 (r)
  (declare (xargs :verify-guards nil))
  (and (consp r) (o1t-line0 (car r))
       (not (fn-article-wspp (car (car r))))
       (o1t-folds-okp (cdr r)))))

(local
 (defun o1t-mkfield (r)
  (declare (xargs :verify-guards nil))
  (o1t-fold-up (fn-article-line-value (fn-article-new-field (car r))) (cdr r))))

(local
 (defthm o1t-fieldvp-facts
  (implies (o1t-fieldvp g)
           (and (true-listp g) (o1t-rawp0 (car g))
                (fn-article-line-okp (fn-article-new-field (car (car g))))
                (equal g (o1t-mkfield (car g)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (o1t-fieldvp o1t-rawp0 o1t-line0 o1t-line-okp o1t-mkfield) ())))))

(local
 (defthm o1t-lu-raw
  (implies (and (o1t-rawp0 r) (o1t-rawp0 r2)
                (not (fn-article-wspp (car u))) (not (fn-article-wspp (car v)))
                (equal (append (fn-article-lines-octets r) u)
                       (append (fn-article-lines-octets r2) v)))
           (and (equal r r2) (equal u v)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (o1t-rawp0 o1t-line0 o1t-line-okp fn-article-lines-octets) (fn-article-wspp))
           :use ((:instance o1t-lu1 (la (car r)) (lb (car r2))
                            (x (fn-article-lines-octets (cdr r))) (y (fn-article-lines-octets (cdr r2))))
                 (:instance o1t-lu2 (a (cdr r)) (b (cdr r2))))))))

(local
 (defthm o1t-car-of-field-octets
  (implies (and (o1t-fieldsvp gs) (not (fn-article-wspp (car u))))
           (not (fn-article-wspp (car (append (fn-article-fields-octets gs) u)))))
  :hints (("Goal" :in-theory (e/d (o1t-fieldsvp fn-article-fields-octets fn-article-lines-octets o1t-fieldvp
                                   o1t-line-okp) (fn-article-wspp))))))

(local
 (defthm o1t-peel-core
  (implies (and (o1t-rawp0 r) (not (fn-article-wspp (car tl)))
                (o1t-fieldsvp fs)
                (equal (append (fn-article-lines-octets r) tl)
                       (append (fn-article-fields-octets fs) (cons 13 (cons 10 body)))))
           (and (consp fs) (equal (car (car fs)) r)
                (equal tl (append (fn-article-fields-octets (cdr fs)) (cons 13 (cons 10 body))))
                (fn-article-line-okp (fn-article-new-field (car r)))
                (equal (car fs) (o1t-mkfield r))
                (o1t-fieldsvp (cdr fs))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-rawp0 o1t-line0 o1t-line-okp fn-article-lines-octets) (fn-article-wspp o1t-car-of-field-octets))
           :cases ((consp fs))
           :use ((:instance o1t-fieldvp-facts (g (car fs)))
                 (:instance o1t-car-of-field-octets (gs (cdr fs)) (u (cons 13 (cons 10 body))))
                 (:instance o1t-lu-raw (r2 (car (car fs)))
                            (u tl)
                            (v (append (fn-article-fields-octets (cdr fs)) (cons 13 (cons 10 body))))))))))

(local
 (defthm o1t-peel-field
  (implies (and (o1t-rawp0 r) (not (fn-article-wspp (car tl)))
                (fn-article-result-okp (fn-article-parse (append (fn-article-lines-octets r) tl))))
           (and (fn-article-line-okp (fn-article-new-field (car r)))
                (fn-article-result-okp (fn-article-parse tl))
                (equal (fn-article-fields
                        (fn-article-result-article (fn-article-parse (append (fn-article-lines-octets r) tl))))
                       (cons (o1t-mkfield r)
                             (fn-article-fields (fn-article-result-article (fn-article-parse tl)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-parse fn-article-wspp o1t-reparse
                               fn-article-lines-octets fn-article-fields-octets o1t-rawp0 o1t-mkfield
                               fn-article-successful-parse-input-octets fn-article-successful-parse-input-bound
                               o1t-octet-listp-suffix o1t-len-suffix)
           :use ((:instance o1t-parse-reconstructs (y (append (fn-article-lines-octets r) tl)))
                 (:instance o1t-peel-core
                            (fs (fn-article-fields (fn-article-result-article
                                                    (fn-article-parse (append (fn-article-lines-octets r) tl)))))
                            (body (fn-article-body (fn-article-result-article
                                                    (fn-article-parse (append (fn-article-lines-octets r) tl))))))
                 (:instance o1t-reparse
                            (g (cdr (fn-article-fields (fn-article-result-article
                                                        (fn-article-parse (append (fn-article-lines-octets r) tl))))))
                            (body (fn-article-body (fn-article-result-article
                                                    (fn-article-parse (append (fn-article-lines-octets r) tl))))))
                 (:instance fn-article-successful-parse-input-octets
                            (octets (append (fn-article-lines-octets r) tl)))
                 (:instance fn-article-successful-parse-input-bound
                            (octets (append (fn-article-lines-octets r) tl)))
                 (:instance o1t-octet-listp-suffix (a (fn-article-lines-octets r)) (b tl))
                 (:instance o1t-len-suffix (a (fn-article-lines-octets r)) (b tl)))))))

(local
 (defun o1t-rawsp (rs)
  (declare (xargs :verify-guards nil))
  (if (consp rs) (and (o1t-rawp0 (car rs)) (o1t-rawsp (cdr rs))) (null rs))))

(local
 (defun o1t-rocts (rs)
  (declare (xargs :verify-guards nil))
  (if (consp rs)
      (append (fn-article-lines-octets (car rs)) (o1t-rocts (cdr rs)))
    nil)))

(local
 (defun o1t-mkfields (rs)
  (declare (xargs :verify-guards nil))
  (if (consp rs) (cons (o1t-mkfield (car rs)) (o1t-mkfields (cdr rs))) nil)))

(local
 (defun o1t-newoks (rs)
  (declare (xargs :verify-guards nil))
  (if (consp rs)
      (and (fn-article-line-okp (fn-article-new-field (car (car rs)))) (o1t-newoks (cdr rs)))
    t)))

(local
 (defthm o1t-append-assoc
  (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm o1t-car-of-rocts
  (implies (and (o1t-rawsp rs) (not (fn-article-wspp (car tl))))
           (not (fn-article-wspp (car (append (o1t-rocts rs) tl)))))
  :hints (("Goal" :in-theory (e/d (o1t-rawp0 o1t-line0 fn-article-lines-octets) (fn-article-wspp))))))

(local
 (defthm o1t-peel-all
  (implies (and (o1t-rawsp rs) (not (fn-article-wspp (car tl)))
                (fn-article-result-okp (fn-article-parse (append (o1t-rocts rs) tl))))
           (and (fn-article-result-okp (fn-article-parse tl))
                (o1t-newoks rs)
                (equal (fn-article-fields (fn-article-result-article (fn-article-parse (append (o1t-rocts rs) tl))))
                       (append (o1t-mkfields rs)
                               (fn-article-fields (fn-article-result-article (fn-article-parse tl)))))))
  :hints (("Goal" :induct (o1t-rocts rs)
           :in-theory (disable fn-article-parse fn-article-wspp o1t-rawp0 o1t-mkfield
                               fn-article-lines-octets o1t-car-of-rocts))
          ("Subgoal *1/1" :use ((:instance o1t-peel-field (r (car rs)) (tl (append (o1t-rocts (cdr rs)) tl)))
                                (:instance o1t-car-of-rocts (rs (cdr rs)))))
          )))

(local
 (defun o1t-fields-agree (fs gs)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-article-get-headers-aux fs *fn-af-newsgroups-name*)
              (fn-article-get-headers-aux gs *fn-af-newsgroups-name*))
       (equal (fn-ctl-fields-named *fn-ctl-control-name* fs)
              (fn-ctl-fields-named *fn-ctl-control-name* gs))
       (equal (fn-ctl-fields-named *fn-ctl-supersedes-name* fs)
              (fn-ctl-fields-named *fn-ctl-supersedes-name* gs)))))

(local
 (defthm o1t-split-colon-of-a-name
  (implies (and (fn-article-ftext-listp name) (true-listp acc))
           (equal (fn-article-split-colon-aux (append name (cons 58 rest)) acc)
                  (list :ok (append (reverse acc) name) rest)))
  :hints (("Goal" :induct (o1t-line-ind name acc 0)
           :in-theory (enable fn-article-split-colon-aux fn-article-ftextp)))))

(local
 (defthm o1t-get-headers-aux-skip
  (implies (not (equal (fn-article-field-name g) (fn-article-ascii-downcase name)))
           (equal (fn-article-get-headers-aux (cons g fs) name)
                  (fn-article-get-headers-aux fs name)))
  :hints (("Goal" :expand ((fn-article-get-headers-aux (cons g fs) name))
           :in-theory (enable fn-article-field-name-equalp)))))

(local
 (defun o1t-prefix-clearp (pre)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pre)
      (and (true-listp (car pre))
           (not (equal (cadr (car pre)) *fn-af-newsgroups-name*))
           (not (equal (cadr (car pre)) *fn-ctl-control-name*))
           (not (equal (cadr (car pre)) *fn-ctl-supersedes-name*))
           (o1t-prefix-clearp (cdr pre)))
    t)))

(local
 (defthm o1t-prefix-agrees
  (implies (o1t-prefix-clearp pre)
           (o1t-fields-agree (append pre fs) fs))
  :hints (("Goal" :induct (o1t-prefix-clearp pre)
           :in-theory (e/d (o1t-fields-agree fn-ctl-fields-named fn-ctl-field-name
                            fn-article-get-headers-aux fn-article-field-name-equalp)
                           ())))))

(local
 (defun o1t-nameok (l)
  (declare (xargs :verify-guards nil))
  (let ((nm (fn-article-line-value (fn-article-split-colon-aux l nil))))
    (and (not (equal (fn-article-ascii-downcase nm) *fn-af-newsgroups-name*))
         (not (equal (fn-article-ascii-downcase nm) *fn-ctl-control-name*))
         (not (equal (fn-article-ascii-downcase nm) *fn-ctl-supersedes-name*))))))

(local
 (defun o1t-plinep (l)
  (declare (xargs :verify-guards nil))
  (and (true-listp l) (consp l) (fn-ipp-no-crlfp l)
       (not (fn-article-wspp (car l))) (o1t-nameok l))))

(local
 (defun o1t-plinesp (ls)
  (declare (xargs :verify-guards nil))
  (if (consp ls) (and (o1t-plinep (car ls)) (o1t-plinesp (cdr ls))) (null ls))))

(local
 (defun o1t-singles (ls)
  (declare (xargs :verify-guards nil))
  (if (consp ls) (cons (list (car ls)) (o1t-singles (cdr ls))) nil)))

(local
 (defthm o1t-crlf-free-is-no-crlf
  (equal (fn-article-crlf-freep x) (fn-ipp-no-crlfp x))
  :hints (("Goal" :in-theory (enable fn-article-crlf-freep fn-ipp-no-crlfp)))))

(local
 (defthm o1t-rocts-singles
  (equal (o1t-rocts (o1t-singles ls)) (o1s-octets ls))
  :hints (("Goal" :in-theory (enable o1t-rocts o1t-singles o1s-octets fn-article-lines-octets)))))

(local
 (defthm o1t-rawsp-singles
  (implies (o1t-plinesp ls) (o1t-rawsp (o1t-singles ls)))
  :hints (("Goal" :in-theory (enable o1t-rawsp o1t-singles o1t-plinesp o1t-plinep o1t-rawp0 o1t-line0
                                     o1t-folds-okp)))))

(local
 (defthm o1t-cadr-of-new-field
  (implies (fn-article-line-okp (fn-article-new-field l))
           (equal (cadr (fn-article-line-value (fn-article-new-field l)))
                  (fn-article-ascii-downcase (fn-article-line-value (fn-article-split-colon-aux l nil)))))
  :hints (("Goal" :in-theory (enable fn-article-new-field)))))

(local
 (defthm o1t-true-listp-of-new-field
  (implies (fn-article-line-okp (fn-article-new-field l))
           (true-listp (fn-article-line-value (fn-article-new-field l))))
  :hints (("Goal" :in-theory (enable fn-article-new-field)))))

(local
 (defthm o1t-cadr-mkfield
  (equal (cadr (o1t-mkfield r)) (cadr (fn-article-line-value (fn-article-new-field (car r)))))
  :hints (("Goal" :in-theory (union-theories '(o1t-mkfield o1t-cadr-of-fold-up) (theory 'minimal-theory))))))

(local
 (defthm o1t-true-listp-mkfield
  (implies (fn-article-line-okp (fn-article-new-field (car r)))
           (true-listp (o1t-mkfield r)))
  :hints (("Goal" :in-theory (e/d (o1t-mkfield) (fn-article-new-field))
           :use ((:instance o1t-true-listp-of-new-field (l (car r)))
                 (:instance o1t-fold-up-true-listp (f (fn-article-line-value (fn-article-new-field (car r)))) (ls (cdr r))))))))

(local
 (defthm o1t-mkfield-facts
  (implies (fn-article-line-okp (fn-article-new-field (car r)))
           (and (equal (cadr (o1t-mkfield r))
                       (fn-article-ascii-downcase
                        (fn-article-line-value (fn-article-split-colon-aux (car r) nil))))
                (true-listp (o1t-mkfield r))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable o1t-cadr-of-new-field)
           :use (o1t-cadr-of-new-field o1t-true-listp-mkfield (:instance o1t-cadr-mkfield) 
                 (:instance o1t-cadr-of-new-field (l (car r))))))))

(local
 (defthm o1t-clear-head
  (implies (and (o1t-plinep l) (fn-article-line-okp (fn-article-new-field l)))
           (let ((m (o1t-mkfield (list l))))
             (and (true-listp m)
                  (not (equal (cadr m) *fn-af-newsgroups-name*))
                  (not (equal (cadr m) *fn-ctl-control-name*))
                  (not (equal (cadr m) *fn-ctl-supersedes-name*)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (o1t-plinep o1t-nameok) (o1t-mkfield fn-article-new-field))
           :use ((:instance o1t-mkfield-facts (r (list l))))))))

(local
 (defthm o1t-clear-of-mkfields
  (implies (and (o1t-plinesp ls) (o1t-newoks (o1t-singles ls)))
           (o1t-prefix-clearp (o1t-mkfields (o1t-singles ls))))
  :hints (("Goal" :induct (o1t-singles ls)
           :in-theory (e/d (o1t-singles o1t-mkfields o1t-newoks o1t-plinesp o1t-prefix-clearp)
                           (o1t-mkfield o1t-plinep fn-article-new-field o1t-cadr-mkfield))
           :do-not-induct nil)
          ("Subgoal *1/1" :use ((:instance o1t-clear-head (l (car ls))))))))

(local
 (defthm o1t-peel-lines
  (implies (and (o1t-plinesp ls) (not (fn-article-wspp (car tl)))
                (fn-article-result-okp (fn-article-parse (append (o1s-octets ls) tl))))
           (and (fn-article-result-okp (fn-article-parse tl))
                (equal (fn-article-fields (fn-article-result-article (fn-article-parse (append (o1s-octets ls) tl))))
                       (append (o1t-mkfields (o1t-singles ls))
                               (fn-article-fields (fn-article-result-article (fn-article-parse tl)))))
                (o1t-prefix-clearp (o1t-mkfields (o1t-singles ls)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-parse fn-article-wspp o1t-rocts-singles o1t-rawsp-singles
                               o1t-clear-of-mkfields o1t-rocts o1t-rawsp o1t-mkfields o1t-newoks o1t-singles
                               o1t-plinesp)
           :use ((:instance o1t-peel-all (rs (o1t-singles ls)))
                 o1t-rocts-singles o1t-rawsp-singles
                 o1t-clear-of-mkfields)))))

(local
 (defthm o1t-source-start
  (implies (fn-article-result-okp (fn-article-parse src))
           (not (fn-article-wspp (car src))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-parse fn-article-wspp o1t-car-of-field-octets)
           :use ((:instance o1t-parse-reconstructs (y src))
                 (:instance o1t-car-of-field-octets
                            (gs (fn-article-fields (fn-article-result-article (fn-article-parse src))))
                            (u (cons 13 (cons 10 (fn-article-body (fn-article-result-article (fn-article-parse src))))))))))))

(local
 (defthm o1t-prefixed-agree
  (implies (and (o1t-plinesp ls)
                (fn-article-result-okp (fn-article-parse src))
                (fn-article-result-okp (fn-article-parse (append (o1s-octets ls) src))))
           (o1t-fields-agree
            (fn-article-fields (fn-article-result-article (fn-article-parse (append (o1s-octets ls) src))))
            (fn-article-fields (fn-article-result-article (fn-article-parse src)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-parse fn-article-wspp)
           :use ((:instance o1t-peel-lines (tl src))
                 (:instance o1t-source-start)
                 (:instance o1t-prefix-agrees
                            (pre (o1t-mkfields (o1t-singles ls)))
                            (fs (fn-article-fields (fn-article-result-article (fn-article-parse src))))))))))

(local
 (defthm o1t-downcase-is-ascii
  (equal (fn-inj-downcase x) (fn-article-ascii-downcase x))
  :hints (("Goal" :in-theory (enable fn-inj-downcase fn-article-ascii-downcase fn-article-ascii-downcase-byte)))))

(local
 (defthm o1t-take4
  (equal (fn-inj-take-n 4 (list* a b c d r)) (list a b c d))
  :hints (("Goal" :expand ((fn-inj-take-n 4 (list* a b c d r)) (fn-inj-take-n 3 (list* b c d r))
                           (fn-inj-take-n 2 (list* c d r)) (fn-inj-take-n 1 (list* d r)) (fn-inj-take-n 0 r))))))

(local
 (defthm o1t-openp-shape
  (implies (fn-inj-path-openp x)
           (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x))
                (equal (car (cddddr x)) 58) (equal (cadr (cddddr x)) 32)
                (consp (cddddr x)) (consp (cdr (cddddr x)))
                (equal (fn-article-ascii-downcase (list (car x) (cadr x) (caddr x) (cadddr x)))
                       '(112 97 116 104))))
  :hints (("Goal" :in-theory (e/d (fn-inj-path-openp) ())
           :expand ((fn-inj-take-n 6 x) (fn-inj-take-n 5 (cdr x)) (fn-inj-take-n 4 (cddr x))
                    (fn-inj-take-n 3 (cdddr x)) (fn-inj-take-n 2 (cddddr x)) (fn-inj-take-n 1 (cdr (cddddr x))))))))

(local
 (defthm o1t-openp-letters
  (implies (fn-inj-path-openp x)
           (and (or (equal (car x) 80) (equal (car x) 112))
                (or (equal (cadr x) 65) (equal (cadr x) 97))
                (or (equal (caddr x) 84) (equal (caddr x) 116))
                (or (equal (cadddr x) 72) (equal (cadddr x) 104))))
  :hints (("Goal" :in-theory (e/d (fn-article-ascii-downcase fn-article-ascii-downcase-byte)
                                  (o1t-openp-shape))
           :use (o1t-openp-shape)))))

(local
 (defthm o1t-openp-not-lead
  (implies (fn-inj-path-openp x)
           (and (not (equal (car x) 13)) (not (equal (car x) 10))
                (not (equal (car x) 32)) (not (equal (car x) 9))))
  :hints (("Goal" :use (o1t-openp-letters)))))

(local
 (defthm o1t-scan-line
  (implies (and (fn-article-crlf-freep l) (true-listp l))
           (equal (fn-inj-path-scan (append l (list* 13 10 x)) nil)
                  (let ((r (fn-inj-path-scan x t)))
                    (if r (+ (len l) 2 r) nil))))
  :hints (("Goal" :induct (len l)
           :in-theory (enable fn-inj-path-scan fn-article-crlf-freep)))))

(local
 (defthm o1t-scan-bol-line
  (implies (and (fn-article-crlf-freep l) (true-listp l) (consp l)
                (not (fn-inj-path-openp (append l (list* 13 10 x)))))
           (equal (fn-inj-path-scan (append l (list* 13 10 x)) t)
                  (let ((r (fn-inj-path-scan x t)))
                    (if r (+ (len l) 2 r) nil))))
  :hints (("Goal" :in-theory (e/d (fn-article-crlf-freep) (o1t-scan-line))
           :expand ((fn-inj-path-scan (append l (list* 13 10 x)) t)
                    (fn-inj-path-scan (cons (car l) (append (cdr l) (list* 13 10 x))) t))
           :use ((:instance o1t-scan-line (l (cdr l))))))))

(local
 (defun o1t-ind1 (fl) (declare (xargs :verify-guards nil)) (if (consp fl) (o1t-ind1 (cdr fl)) nil)))

(local
 (defthm o1t-scan-folds
  (implies (o1t-folds-okp fl)
           (equal (fn-inj-path-scan (append (fn-article-lines-octets fl) x) t)
                  (if (consp fl)
                      (let ((r (fn-inj-path-scan x t)))
                        (if r (+ (len (fn-article-lines-octets fl)) r) nil))
                    (fn-inj-path-scan x t))))
  :hints (("Goal" :induct (o1t-ind1 fl)
           :in-theory (e/d (o1t-folds-okp o1t-line-okp fn-article-fold-linep)
                           (fn-article-wspp o1t-scan-bol-line o1t-openp-not-lead)))
          ("Subgoal *1/1" :expand ((fn-article-lines-octets fl))
           :use ((:instance o1t-openp-not-lead
                            (x (append (car fl) (list* 13 10 (append (fn-article-lines-octets (cdr fl)) x)))))
                 (:instance o1t-scan-bol-line (l (car fl))
                            (x (append (fn-article-lines-octets (cdr fl)) x))))))))

(local
 (defthm o1t-scan-field
  (implies (and (o1t-rawp0 raw)
                (not (fn-inj-path-openp (append (fn-article-lines-octets raw) x))))
           (equal (fn-inj-path-scan (append (fn-article-lines-octets raw) x) t)
                  (let ((r (fn-inj-path-scan x t)))
                    (if r (+ (len (fn-article-lines-octets raw)) r) nil))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-rawp0 o1t-line0 fn-article-lines-octets)
                           (fn-inj-path-openp o1t-scan-bol-line o1t-scan-folds fn-inj-path-scan))
           :use ((:instance o1t-scan-bol-line (l (car raw))
                            (x (append (fn-article-lines-octets (cdr raw)) x)))
                 (:instance o1t-scan-folds (fl (cdr raw))))))))

(local
 (defun o1t-s1 (s tt)
  (declare (xargs :verify-guards nil))
  (if (and (consp s) (not (fn-inj-path-openp (append (fn-article-fields-octets s) tt))))
      (cons (car s) (o1t-s1 (cdr s) tt))
    nil)))

(local
 (defun o1t-s2 (s tt)
  (declare (xargs :verify-guards nil))
  (if (and (consp s) (not (fn-inj-path-openp (append (fn-article-fields-octets s) tt))))
      (o1t-s2 (cdr s) tt)
    s)))

(local
 (defthm o1t-scan-at-cr
  (implies (equal (car x) 13) (not (fn-inj-path-scan x t)))
  :hints (("Goal" :expand ((fn-inj-path-scan x t))
           :use (o1t-openp-not-lead)))))

(local
 (defthm o1t-scan-open
  (implies (fn-inj-path-openp x) (equal (fn-inj-path-scan x t) 6))
  :hints (("Goal" :expand ((fn-inj-path-scan x t))))))

(local
 (defthm o1t-scan-fields
  (implies (and (o1t-fieldsvp s) (equal (car tt) 13))
           (equal (fn-inj-path-scan (append (fn-article-fields-octets s) tt) t)
                  (if (fn-inj-path-openp (append (fn-article-fields-octets (o1t-s2 s tt)) tt))
                      (+ 6 (len (fn-article-fields-octets (o1t-s1 s tt))))
                    nil)))
  :hints (("Goal" :induct (o1t-s1 s tt)
           :in-theory (e/d (o1t-fieldsvp) (fn-inj-path-openp o1t-scan-field))
           :do-not-induct nil)
          ("Subgoal *1/2" :use ((:instance o1t-scan-at-cr (x tt)) (:instance o1t-openp-not-lead (x tt))
                               (:instance o1t-scan-open (x (append (fn-article-fields-octets s) tt)))))
          ("Subgoal *1/1" :expand ((fn-article-fields-octets s))
           :use ((:instance o1t-fieldvp-facts (g (car s)))
                 (:instance o1t-scan-field (raw (car (car s)))
                            (x (append (fn-article-fields-octets (cdr s)) tt))))))))

(local
 (defthm o1t-fields-octets-append
  (equal (fn-article-fields-octets (append a b))
         (append (fn-article-fields-octets a) (fn-article-fields-octets b)))
  :hints (("Goal" :induct (fn-article-fields-octets a)
           :in-theory (enable fn-article-fields-octets)))))

(local
 (defthm o1t-s1s2-facts
  (implies (o1t-fieldsvp s)
           (and (equal (append (o1t-s1 s tt) (o1t-s2 s tt)) s)
                (o1t-fieldsvp (o1t-s1 s tt))
                (o1t-fieldsvp (o1t-s2 s tt))))
  :hints (("Goal" :induct (o1t-s1 s tt)
           :in-theory (enable o1t-fieldsvp)))))

(local
 (defthm o1t-ins-of-append
  (implies (and (true-listp a) (natp j))
           (equal (o1s-ins (append a w) (+ (len a) j) ins)
                  (append a (o1s-ins w j ins))))
  :hints (("Goal" :induct (len a) :in-theory (enable o1s-ins)))))

(local
 (defthm o1t-split-of-line
  (implies (and (fn-ipp-no-crlfp l) (true-listp l))
           (equal (o1s-split (append l (list* 13 10 r))) (cons l r)))
  :hints (("Goal" :induct (fn-ipp-no-crlfp l) :in-theory (enable o1s-split fn-ipp-no-crlfp)))))

(local
 (defthm o1t-openp-ftext
  (implies (fn-inj-path-openp x)
           (fn-article-ftext-listp (list (car x) (cadr x) (caddr x) (cadddr x))))
  :hints (("Goal" :in-theory (enable fn-article-ftext-listp fn-article-ftextp)
           :use (o1t-openp-letters)))))

(local
 (defthm o1t-list6
  (implies (and (consp w) (consp (cdr w)) (consp (cddr w)) (consp (cdddr w))
                (consp (cddddr w)) (consp (cdr (cddddr w))))
           (equal (list* (car w) (cadr w) (caddr w) (cadddr w) (car (cddddr w)) (cadr (cddddr w))
                         (cddr (cddddr w)))
                  w))))

(local
 (defthm o1t-w-shape
  (implies (fn-inj-path-openp w)
           (equal w (list* (car w) (cadr w) (caddr w) (cadddr w) 58 32 (cddr (cddddr w)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable o1t-list6)
           :use ((:instance o1t-openp-shape (x w)) (:instance o1t-list6))))))

(local
 (defthm o1t-p6-nocrlf
  (implies (fn-inj-path-openp w)
           (fn-ipp-no-crlfp (list (car w) (cadr w) (caddr w) (cadddr w) 58 32)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ipp-no-crlfp) :use ((:instance o1t-openp-letters (x w)))))))

(local
 (defthm o1t-ins-at-six
  (implies (fn-inj-path-openp w)
           (equal (o1s-ins w 6 ins)
                  (append (list (car w) (cadr w) (caddr w) (cadddr w) 58 32)
                          (append ins (cddr (cddddr w))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (o1s-ins) ())
           :use (o1t-w-shape)
           :do-not-induct t))))

(local
 (defthm o1t-b3-split
  (implies (and (fn-inj-path-openp w)
                (equal (o1s-split w) (cons l1 rw))
                (fn-ipp-no-crlfp l1) (true-listp l1)
                (fn-ipp-no-crlfp ins) (true-listp ins))
           (and (consp (o1s-split (cddr (cddddr w))))
                (equal l1 (append (list (car w) (cadr w) (caddr w) (cadddr w) 58 32)
                                  (car (o1s-split (cddr (cddddr w))))))
                (equal rw (cdr (o1s-split (cddr (cddddr w)))))
                (fn-ipp-no-crlfp (car (o1s-split (cddr (cddddr w)))))
                (true-listp (car (o1s-split (cddr (cddddr w)))))
                (equal (o1s-ins w 6 ins)
                       (append (append (list (car w) (cadr w) (caddr w) (cadddr w) 58 32)
                                       (append ins (car (o1s-split (cddr (cddddr w))))))
                               (list* 13 10 rw)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable o1s-split o1s-ins fn-inj-path-openp
                               o1s-split-of-append-ins o1t-split-of-line
                               o1s-split-true-listp o1s-no-crlf-append)
           :use (o1t-w-shape o1t-p6-nocrlf o1t-ins-at-six
                 (:instance o1s-split-of-append-ins
                            (ins (list (car w) (cadr w) (caddr w) (cadddr w) 58 32))
                            (y (cddr (cddddr w))))
                 (:instance o1s-split-reassembles (x (cddr (cddddr w))))
                 (:instance o1s-split-true-listp (x (cddr (cddddr w))))
                 (:instance o1s-no-crlf-append
                            (a (list (car w) (cadr w) (caddr w) (cadddr w) 58 32))
                            (b (car (o1s-split (cddr (cddddr w)))))))))))

(local
 (defun o1t-w (p s2t sb)
  (declare (xargs :verify-guards nil))
  (append (fn-article-fields-octets (cons p s2t)) (list* 13 10 sb))))
(local
 (defun o1t-l1 (p) (declare (xargs :verify-guards nil)) (car (car p))))
(local
 (defun o1t-rw (p s2t sb)
  (declare (xargs :verify-guards nil))
  (append (fn-article-lines-octets (cdr (car p)))
          (append (fn-article-fields-octets s2t) (list* 13 10 sb)))))

(local
 (defthm o1t-w-is-line
  (implies (o1t-fieldsvp (cons p s2t))
           (equal (o1t-w p s2t sb)
                  (append (o1t-l1 p) (list* 13 10 (o1t-rw p s2t sb)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-w o1t-l1 o1t-rw fn-article-fields-octets fn-article-lines-octets o1t-fieldsvp)
                           ())
           :use ((:instance o1t-fieldvp-facts (g p)))))))

(local
 (defthm o1t-l1-line
  (implies (o1t-fieldsvp (cons p s2t))
           (and (fn-ipp-no-crlfp (o1t-l1 p)) (true-listp (o1t-l1 p)) (consp (o1t-l1 p))
                (not (fn-article-wspp (car (o1t-l1 p))))
                (o1t-folds-okp (cdr (car p)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-fieldsvp o1t-l1 o1t-rawp0 o1t-line0 o1t-crlf-free-is-no-crlf) (fn-article-wspp))
           :use ((:instance o1t-fieldvp-facts (g p)))))))

(local
 (defthm o1t-l1-facts
  (implies (o1t-fieldsvp (cons p s2t))
           (equal (o1s-split (o1t-w p s2t sb)) (cons (o1t-l1 p) (o1t-rw p s2t sb))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable o1t-w o1t-l1 o1t-rw o1t-w-is-line o1t-split-of-line o1t-l1-line)
           :use (o1t-w-is-line o1t-l1-line
                 (:instance o1t-split-of-line (l (o1t-l1 p)) (r (o1t-rw p s2t sb))))))))

(local
 (defthm o1t-suffix-ok
  (implies (and (fn-article-result-okp (fn-article-parse y3))
                (equal y3 (append m1 (list* 13 10 (append x u)))))
           (and (fn-cbor-octet-listp u) (<= (len u) *fn-article-max-octets*)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-parse o1t-octet-listp-suffix o1t-len-suffix
                               fn-article-successful-parse-input-octets fn-article-successful-parse-input-bound)
           :use ((:instance fn-article-successful-parse-input-octets (octets y3))
                 (:instance fn-article-successful-parse-input-bound (octets y3))
                 (:instance o1t-octet-listp-suffix (a m1) (b (list* 13 10 (append x u))))
                 (:instance o1t-octet-listp-suffix (a x) (b u))
                 (:instance o1t-len-suffix (a m1) (b (list* 13 10 (append x u))))
                 (:instance o1t-len-suffix (a x) (b u))))))) 

(local
 (defun o1t-y3 (m1 pf s2t sb)
  (declare (xargs :verify-guards nil))
  (append m1 (list* 13 10 (append (fn-article-lines-octets pf)
                                  (append (fn-article-fields-octets s2t) (list* 13 10 sb)))))))

(local
 (defthm o1t-y3-def
  (equal (o1t-y3 m1 pf s2t sb)
         (append m1 (list* 13 10 (append (fn-article-lines-octets pf)
                                         (append (fn-article-fields-octets s2t) (list* 13 10 sb))))))
  :rule-classes nil))

(local
 (defthm o1t-lo-cons
  (equal (fn-article-lines-octets (cons m1 pf))
         (append m1 (list* 13 10 (fn-article-lines-octets pf))))
  :hints (("Goal" :in-theory (enable fn-article-lines-octets)))))

(local
 (defthm o1t-b3-abs
  (implies (and (o1t-rawp0 (cons m1 pf)) (o1t-fieldsvp s2t) (fn-article-body-crlfp sb)
                (o1t-fieldsvp fs) (fn-article-body-crlfp body)
                (equal (append (fn-article-fields-octets fs) (list* 13 10 body))
                       (append m1 (list* 13 10 (append (fn-article-lines-octets pf)
                                                       (append (fn-article-fields-octets s2t)
                                                               (list* 13 10 sb))))))
                (fn-cbor-octet-listp (append (fn-article-fields-octets s2t) (list* 13 10 sb)))
                (<= (len (append (fn-article-fields-octets s2t) (list* 13 10 sb))) *fn-article-max-octets*))
           (and (consp fs)
                (equal (cdr fs) s2t)
                (fn-article-line-okp (fn-article-new-field m1))
                (equal (car fs) (o1t-mkfield (cons m1 pf)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-rawp0 o1t-line0)
                           (fn-article-parse fn-article-wspp o1t-reparse
                            fn-article-lines-octets fn-article-fields-octets o1t-mkfield
                            o1t-car-of-field-octets))
           :use ((:instance o1t-car-of-field-octets (gs s2t) (u (list* 13 10 sb)))
                 (:instance o1t-peel-core (r (cons m1 pf))
                            (tl (append (fn-article-fields-octets s2t) (list* 13 10 sb))))
                 (:instance o1t-reparse (g (cdr fs))
                            (tl (append (fn-article-fields-octets s2t) (list* 13 10 sb))))
                 (:instance o1t-reparse (g s2t) (body sb)
                            (tl (append (fn-article-fields-octets s2t) (list* 13 10 sb)))))))))

(local
 (defthm o1t-b3-uniq
  (implies (and (o1t-rawp0 (cons m1 pf)) (o1t-fieldsvp s2t) (fn-article-body-crlfp sb)
                (fn-article-result-okp (fn-article-parse (o1t-y3 m1 pf s2t sb))))
           (let ((fy (fn-article-fields (fn-article-result-article (fn-article-parse (o1t-y3 m1 pf s2t sb))))))
             (and (consp fy)
                  (equal (cdr fy) s2t)
                  (fn-article-line-okp (fn-article-new-field m1))
                  (equal (car fy) (o1t-mkfield (cons m1 pf))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-parse fn-article-successful-parse-is-parse-lines
                               fn-article-successful-parse-lines-okp o1t-rawp0 o1t-y3)
           :use ((:instance o1t-parse-reconstructs (y (o1t-y3 m1 pf s2t sb)))
                 (:instance o1t-suffix-ok (y3 (o1t-y3 m1 pf s2t sb)) (x (fn-article-lines-octets pf))
                            (u (append (fn-article-fields-octets s2t) (list* 13 10 sb))))
                 (:instance o1t-b3-abs
                            (fs (fn-article-fields (fn-article-result-article (fn-article-parse (o1t-y3 m1 pf s2t sb)))))
                            (body (fn-article-body (fn-article-result-article (fn-article-parse (o1t-y3 m1 pf s2t sb))))))
                 (:instance o1t-y3-def))))))

(local
 (defthm o1t-name-of-line
  (implies (and (fn-article-ftext-listp nm)
                (fn-article-line-okp (fn-article-new-field (append nm (cons 58 r)))))
           (equal (cadr (o1t-mkfield (list* (append nm (cons 58 r)) pf)))
                  (fn-article-ascii-downcase nm)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable o1t-mkfield o1t-cadr-of-new-field fn-article-new-field)
           :use ((:instance o1t-cadr-mkfield (r (cons (append nm (cons 58 r)) pf)))
                 (:instance o1t-cadr-of-new-field (l (append nm (cons 58 r))))
                 (:instance o1t-split-colon-of-a-name (name nm) (acc nil) (rest r)))))))

(local
 (defun o1t-m1 (w ins)
  (declare (xargs :verify-guards nil))
  (append (list (car w) (cadr w) (caddr w) (cadddr w) 58 32)
          (append ins (car (o1s-split (cddr (cddddr w))))))))

(local
 (defthm o1t-b3-y3
  (implies (and (o1t-fieldsvp (cons p s2t))
                (fn-inj-path-openp (o1t-w p s2t sb))
                (fn-ipp-no-crlfp ins) (true-listp ins))
           (and (equal (o1s-ins (o1t-w p s2t sb) 6 ins)
                       (o1t-y3 (o1t-m1 (o1t-w p s2t sb) ins) (cdr (car p)) s2t sb))
                (equal (o1t-l1 p)
                       (append (list (car (o1t-w p s2t sb)) (cadr (o1t-w p s2t sb))
                                     (caddr (o1t-w p s2t sb)) (cadddr (o1t-w p s2t sb)) 58 32)
                               (car (o1s-split (cddr (cddddr (o1t-w p s2t sb)))))))
                (fn-ipp-no-crlfp (car (o1s-split (cddr (cddddr (o1t-w p s2t sb))))))
                (true-listp (car (o1s-split (cddr (cddddr (o1t-w p s2t sb))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-rw o1t-m1) (o1s-ins o1t-w o1t-l1 fn-inj-path-openp o1t-y3 o1s-split o1t-w-is-line o1t-l1-facts o1t-l1-line
                               fn-article-lines-octets fn-article-fields-octets))
           :use (o1t-l1-line o1t-l1-facts
                 (:instance o1t-b3-split (w (o1t-w p s2t sb)) (l1 (o1t-l1 p)) (rw (o1t-rw p s2t sb)))
                 (:instance o1t-y3-def (m1 (o1t-m1 (o1t-w p s2t sb) ins)) (pf (cdr (car p)))))))))

(local
 (defthm o1t-b3-m1-raw
  (implies (and (o1t-fieldsvp (cons p s2t))
                (fn-inj-path-openp (o1t-w p s2t sb))
                (fn-ipp-no-crlfp ins) (true-listp ins))
           (o1t-rawp0 (cons (o1t-m1 (o1t-w p s2t sb) ins) (cdr (car p)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-rawp0 o1t-line0 o1t-m1 o1t-crlf-free-is-no-crlf)
                           (o1s-ins o1t-w o1t-l1 fn-inj-path-openp o1t-y3 o1s-split fn-article-wspp
                            o1t-b3-y3 o1t-l1-line))
           :use (o1t-b3-y3 o1t-l1-line
                 (:instance o1t-p6-nocrlf (w (o1t-w p s2t sb)))
                 (:instance o1t-openp-letters (x (o1t-w p s2t sb)))
                 (:instance o1s-no-crlf-append
                            (a (list (car (o1t-w p s2t sb)) (cadr (o1t-w p s2t sb))
                                     (caddr (o1t-w p s2t sb)) (cadddr (o1t-w p s2t sb)) 58 32))
                            (b (append ins (car (o1s-split (cddr (cddddr (o1t-w p s2t sb))))))))
                 (:instance o1s-no-crlf-append
                            (a ins) (b (car (o1s-split (cddr (cddddr (o1t-w p s2t sb)))))))
                 )))))

(local
 (defthm o1t-name-of-m1
  (implies (and (fn-inj-path-openp w)
                (fn-article-line-okp (fn-article-new-field (o1t-m1 w ins))))
           (equal (cadr (o1t-mkfield (cons (o1t-m1 w ins) pf))) '(112 97 116 104)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-m1) (o1t-name-of-line fn-inj-path-openp o1s-split o1t-mkfield fn-article-new-field))
           :use ((:instance o1t-name-of-line
                            (nm (list (car w) (cadr w) (caddr w) (cadddr w)))
                            (r (cons 32 (append ins (car (o1s-split (cddr (cddddr w)))))))
                            (pf pf))
                 (:instance o1t-openp-ftext (x w))
                 (:instance o1t-openp-shape (x w)))))))

(local
 (defthm o1t-name-of-l1
  (implies (and (fn-inj-path-openp w)
                (equal l1 (append (list (car w) (cadr w) (caddr w) (cadddr w) 58 32) c1))
                (fn-article-line-okp (fn-article-new-field l1)))
           (equal (cadr (o1t-mkfield (cons l1 pf))) '(112 97 116 104)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (o1t-name-of-line fn-inj-path-openp o1s-split o1t-mkfield fn-article-new-field))
           :use ((:instance o1t-name-of-line
                            (nm (list (car w) (cadr w) (caddr w) (cadddr w)))
                            (r (cons 32 c1))
                            (pf pf))
                 (:instance o1t-openp-ftext (x w))
                 (:instance o1t-openp-shape (x w)))))))

(local
 (defthm o1t-cadr-of-field
  (implies (o1t-fieldvp p)
           (equal (cadr p) (cadr (fn-article-line-value (fn-article-new-field (car (car p)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-new-field o1t-mkfield o1t-cadr-mkfield)
           :use ((:instance o1t-fieldvp-facts (g p))
                 (:instance o1t-cadr-mkfield (r (car p))))))))

(local
 (defthm o1t-b3
  (implies (and (o1t-fieldsvp (cons p s2t)) (fn-article-body-crlfp sb)
                (fn-inj-path-openp (o1t-w p s2t sb))
                (fn-ipp-no-crlfp ins) (true-listp ins)
                (fn-article-result-okp (fn-article-parse (o1s-ins (o1t-w p s2t sb) 6 ins))))
           (let ((fy (fn-article-fields (fn-article-result-article
                                         (fn-article-parse (o1s-ins (o1t-w p s2t sb) 6 ins))))))
             (and (consp fy)
                  (equal (cdr fy) s2t)
                  (equal (cadr (car fy)) '(112 97 116 104))
                  (equal (cadr p) '(112 97 116 104)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-l1) (fn-article-parse o1s-ins o1t-w fn-inj-path-openp o1s-split
                               fn-article-successful-parse-is-parse-lines fn-article-successful-parse-lines-okp
                               o1t-y3 o1t-mkfield o1t-rawp0 o1t-name-of-line o1t-b3-y3 o1t-b3-m1-raw
                               o1t-l1-line o1t-m1 o1t-name-of-m1 o1t-name-of-l1 o1t-w-is-line o1t-l1-facts))
           :use (o1t-b3-y3 o1t-b3-m1-raw
                 (:instance o1t-b3-uniq (m1 (o1t-m1 (o1t-w p s2t sb) ins)) (pf (cdr (car p))))
                 (:instance o1t-name-of-m1 (w (o1t-w p s2t sb)) (pf (cdr (car p))))
                 (:instance o1t-name-of-l1 (w (o1t-w p s2t sb)) (l1 (o1t-l1 p)) (pf (cdr (car p)))
                            (c1 (car (o1s-split (cddr (cddddr (o1t-w p s2t sb)))))))
                 (:instance o1t-fieldvp-facts (g p))
                 (:instance o1t-cadr-of-field))))))

(local
 (defthm o1t-true-listp-lines-octets
  (true-listp (fn-article-lines-octets x))
  :hints (("Goal" :in-theory (enable fn-article-lines-octets)))))

(local
 (defthm o1t-true-listp-fields-octets
  (true-listp (fn-article-fields-octets x))
  :hints (("Goal" :in-theory (enable fn-article-fields-octets)))))

(local
 (defun o1t-raws (s)
  (declare (xargs :verify-guards nil))
  (if (consp s) (cons (car (car s)) (o1t-raws (cdr s))) nil)))

(local
 (defthm o1t-raws-facts
  (implies (o1t-fieldsvp s)
           (and (o1t-rawsp (o1t-raws s))
                (equal (o1t-rocts (o1t-raws s)) (fn-article-fields-octets s))
                (equal (o1t-mkfields (o1t-raws s)) s)))
  :hints (("Goal" :induct (o1t-raws s)
           :in-theory (e/d (o1t-raws o1t-rawsp o1t-rocts o1t-mkfields o1t-fieldsvp fn-article-fields-octets)
                           ())
           :do-not-induct nil)
          ("Subgoal *1/1" :use ((:instance o1t-fieldvp-facts (g (car s))))))))

(local
 (defthm o1t-agree-trans
  (implies (and (o1t-fields-agree a b) (o1t-fields-agree b c))
           (o1t-fields-agree a c))
  :hints (("Goal" :in-theory (enable o1t-fields-agree)))))

(local
 (defthm o1t-replace-agree
  (implies (and (equal (cadr g) '(112 97 116 104)) (equal (cadr p) '(112 97 116 104)))
           (o1t-fields-agree (append s1 (cons g r)) (append s1 (cons p r))))
  :hints (("Goal" :induct (len s1)
           :in-theory (e/d (o1t-fields-agree fn-ctl-fields-named fn-ctl-field-name
                            fn-article-get-headers-aux fn-article-field-name-equalp)
                           ())))))

(local
 (defun o1t-fs (x)
  (declare (xargs :verify-guards nil))
  (fn-article-fields (fn-article-result-article (fn-article-parse x)))))

(local
 (defun o1t-sbody (x)
  (declare (xargs :verify-guards nil))
  (fn-article-body (fn-article-result-article (fn-article-parse x)))))

(local
 (defthm o1t-b-decomp
  (implies (and (fn-article-result-okp (fn-article-parse x))
                (fn-inj-path-offset x))
           (let* ((s (o1t-fs x)) (sb (o1t-sbody x)) (tt (list* 13 10 sb))
                  (s1 (o1t-s1 s tt)) (s2 (o1t-s2 s tt)))
             (and (o1t-fieldsvp s1) (consp s2) (o1t-fieldsvp s2)
                  (fn-inj-path-openp (o1t-w (car s2) (cdr s2) sb))
                  (equal x (append (fn-article-fields-octets s1) (o1t-w (car s2) (cdr s2) sb)))
                  (equal (fn-inj-path-offset x) (+ 6 (len (fn-article-fields-octets s1))))
                  (equal s (append s1 s2))
                  (fn-article-body-crlfp sb))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-inj-path-offset o1t-w)
                           (fn-article-parse fn-inj-path-scan fn-inj-path-openp o1t-s1 o1t-s2
                            fn-article-fields-octets o1t-scan-fields
                            o1t-s1s2-facts o1t-scan-at-cr))
           :use ((:instance o1t-parse-reconstructs (y x))
                 (:instance o1t-scan-fields (s (o1t-fs x)) (tt (list* 13 10 (o1t-sbody x))))
                 (:instance o1t-s1s2-facts (s (o1t-fs x)) (tt (list* 13 10 (o1t-sbody x))))
                 (:instance o1t-scan-at-cr (x (list* 13 10 (o1t-sbody x))))
                 (:instance o1t-openp-not-lead (x (list* 13 10 (o1t-sbody x))))
                 (:instance o1t-fields-octets-append (a (o1t-s1 (o1t-fs x) (list* 13 10 (o1t-sbody x))))
                            (b (o1t-s2 (o1t-fs x) (list* 13 10 (o1t-sbody x))))))))))

(local
 (defthm o1t-abs
  (implies (and (o1t-plinesp ls)
                (not (fn-article-wspp (car y2)))
                (fn-article-result-okp (fn-article-parse (append (o1s-octets ls) y2)))
                (o1t-fieldsvp s1)
                (equal y2 (append (fn-article-fields-octets s1) y3))
                (not (fn-article-wspp (car y3)))
                (implies (fn-article-result-okp (fn-article-parse y3))
                         (and (consp (fn-article-fields (fn-article-result-article (fn-article-parse y3))))
                              (equal (cdr (fn-article-fields (fn-article-result-article (fn-article-parse y3)))) s2t)
                              (equal (cadr (car (fn-article-fields (fn-article-result-article (fn-article-parse y3)))))
                                     '(112 97 116 104))
                              (equal (cadr p) '(112 97 116 104))))
                (equal sfields (append s1 (cons p s2t))))
           (o1t-fields-agree
            (fn-article-fields (fn-article-result-article (fn-article-parse (append (o1s-octets ls) y2))))
            sfields))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-parse fn-article-wspp o1t-rocts o1t-rawsp o1t-mkfields o1t-newoks
                               o1t-singles o1t-plinesp fn-article-fields-octets o1t-prefix-agrees
                               o1t-replace-agree o1t-agree-trans o1t-raws o1t-raws-facts
                               o1t-source-start)
           :use ((:instance o1t-peel-lines (tl y2))
                 (:instance o1t-raws-facts (s s1))
                 (:instance o1t-peel-all (rs (o1t-raws s1)) (tl y3))
                 (:instance o1t-prefix-agrees
                            (pre (o1t-mkfields (o1t-singles ls)))
                            (fs (fn-article-fields (fn-article-result-article (fn-article-parse y2)))))
                 (:instance o1t-prefix-agrees
                            (pre (o1t-mkfields (o1t-singles ls)))
                            (fs (append s1 (cons (car (fn-article-fields (fn-article-result-article (fn-article-parse y3)))) s2t))))
                 (:instance o1t-replace-agree
                            (g (car (fn-article-fields (fn-article-result-article (fn-article-parse y3)))))
                            (r s2t))
                 (:instance o1t-agree-trans
                            (a (append (o1t-mkfields (o1t-singles ls))
                                       (append s1 (cons (car (fn-article-fields (fn-article-result-article (fn-article-parse y3)))) s2t))))
                            (b (append s1 (cons (car (fn-article-fields (fn-article-result-article (fn-article-parse y3)))) s2t)))
                            (c sfields)))))))

(local
 (defthm o1t-y2-is
  (implies (and (fn-article-result-okp (fn-article-parse x))
                (fn-inj-path-offset x)
                (true-listp ins))
           (let* ((s (o1t-fs x)) (sb (o1t-sbody x)) (tt (list* 13 10 sb))
                  (s1 (o1t-s1 s tt)) (s2 (o1t-s2 s tt)))
             (and (equal (fn-inj-splice x (fn-inj-path-offset x) ins)
                         (append (fn-article-fields-octets s1)
                                 (o1s-ins (o1t-w (car s2) (cdr s2) sb) 6 ins)))
                  (equal (fn-inj-splice x (fn-inj-path-offset x) ins)
                         (o1s-ins x (fn-inj-path-offset x) ins)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-parse fn-inj-path-openp o1t-s1 o1t-s2 fn-article-fields-octets
                               o1t-w fn-inj-splice o1s-ins o1t-ins-of-append o1s-splice-is-ins
                               fn-inj-path-offset)
           :use (o1t-b-decomp
                 (:instance o1s-splice-is-ins (x x) (k (fn-inj-path-offset x)) (ins ins))
                 (:instance o1t-ins-of-append
                            (a (fn-article-fields-octets (o1t-s1 (o1t-fs x) (list* 13 10 (o1t-sbody x)))))
                            (w (o1t-w (car (o1t-s2 (o1t-fs x) (list* 13 10 (o1t-sbody x))))
                                      (cdr (o1t-s2 (o1t-fs x) (list* 13 10 (o1t-sbody x))))
                                      (o1t-sbody x)))
                            (j 6))
                 (:instance o1s-openp-facts
                            (x (o1t-w (car (o1t-s2 (o1t-fs x) (list* 13 10 (o1t-sbody x))))
                                      (cdr (o1t-s2 (o1t-fs x) (list* 13 10 (o1t-sbody x))))
                                      (o1t-sbody x)))))))))

(local (defun o1t-s1x (x) (declare (xargs :verify-guards nil))
  (o1t-s1 (o1t-fs x) (list* 13 10 (o1t-sbody x)))))
(local (defun o1t-s2x (x) (declare (xargs :verify-guards nil))
  (o1t-s2 (o1t-fs x) (list* 13 10 (o1t-sbody x)))))
(local (defun o1t-wx (x) (declare (xargs :verify-guards nil))
  (o1t-w (car (o1t-s2x x)) (cdr (o1t-s2x x)) (o1t-sbody x))))
(local (defun o1t-y3x (x ins) (declare (xargs :verify-guards nil))
  (o1s-ins (o1t-wx x) 6 ins)))

(local
 (defthm o1t-fx-1
  (implies (and (fn-article-result-okp (fn-article-parse x)) (fn-inj-path-offset x) (true-listp ins))
           (and (o1t-fieldsvp (o1t-s1x x))
                (equal (fn-inj-splice x (fn-inj-path-offset x) ins)
                       (append (fn-article-fields-octets (o1t-s1x x)) (o1t-y3x x ins)))
                (equal (o1t-fs x) (append (o1t-s1x x) (cons (car (o1t-s2x x)) (cdr (o1t-s2x x)))))
                (not (fn-article-wspp (car (o1t-y3x x ins))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-s1x o1t-s2x o1t-wx o1t-y3x)
                           (fn-article-parse fn-inj-path-openp o1t-s1 o1t-s2 fn-article-fields-octets
                            o1t-w fn-inj-splice o1s-ins fn-inj-path-offset o1t-fs o1t-sbody fn-article-wspp))
           :use ((:instance o1t-b-decomp) (:instance o1t-y2-is)
                 (:instance o1s-car-ins (k 6) (x (o1t-w (car (o1t-s2 (o1t-fs x) (list* 13 10 (o1t-sbody x))))
                                                        (cdr (o1t-s2 (o1t-fs x) (list* 13 10 (o1t-sbody x))))
                                                        (o1t-sbody x))))
                 (:instance o1t-openp-not-lead
                            (x (o1t-w (car (o1t-s2 (o1t-fs x) (list* 13 10 (o1t-sbody x))))
                                      (cdr (o1t-s2 (o1t-fs x) (list* 13 10 (o1t-sbody x))))
                                      (o1t-sbody x)))))))))

(local
 (defthm o1t-fx-2
  (implies (and (fn-article-result-okp (fn-article-parse x)) (fn-inj-path-offset x) (true-listp ins))
           (not (fn-article-wspp (car (fn-inj-splice x (fn-inj-path-offset x) ins)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-article-parse fn-inj-splice o1s-ins fn-inj-path-offset o1t-source-start
                               fn-article-wspp)
           :use ((:instance o1t-y2-is)
                 (:instance o1t-source-start (src x))
                 (:instance o1s-car-ins (x x) (k (fn-inj-path-offset x)))
                 (:instance o1t-b-decomp))))))

(local
 (defthm o1t-cons-car-cdr
  (implies (consp x) (equal (cons (car x) (cdr x)) x))))

(local
 (defthm o1t-fx-4
  (implies (and (fn-article-result-okp (fn-article-parse x)) (fn-inj-path-offset x))
           (and (consp (o1t-s2x x)) (o1t-fieldsvp (o1t-s2x x))
                (fn-inj-path-openp (o1t-wx x))
                (fn-article-body-crlfp (o1t-sbody x))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(o1t-s2x o1t-wx) (theory 'minimal-theory))
           :use ((:instance o1t-b-decomp))))))

(local
 (defthm o1t-fx-3
  (implies (and (fn-article-result-okp (fn-article-parse x)) (fn-inj-path-offset x)
                (fn-ipp-no-crlfp ins) (true-listp ins)
                (fn-article-result-okp (fn-article-parse (o1t-y3x x ins))))
           (let ((fy (fn-article-fields (fn-article-result-article (fn-article-parse (o1t-y3x x ins))))))
             (and (consp fy)
                  (equal (cdr fy) (cdr (o1t-s2x x)))
                  (equal (cadr (car fy)) '(112 97 116 104))
                  (equal (cadr (car (o1t-s2x x))) '(112 97 116 104)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(o1t-y3x o1t-wx o1t-cons-car-cdr) (theory 'minimal-theory))
           :use ((:instance o1t-fx-4)
                 (:instance o1t-b3 (p (car (o1t-s2x x))) (s2t (cdr (o1t-s2x x))) (sb (o1t-sbody x))))))))

(local
 (defthm o1t-splice-agree
  (implies (and (o1t-plinesp ls)
                (fn-article-result-okp (fn-article-parse src))
                (fn-inj-path-offset src)
                (fn-ipp-no-crlfp ins) (true-listp ins)
                (fn-article-result-okp
                 (fn-article-parse (append (o1s-octets ls) (fn-inj-splice src (fn-inj-path-offset src) ins)))))
           (o1t-fields-agree
            (fn-article-fields (fn-article-result-article
                                (fn-article-parse (append (o1s-octets ls)
                                                          (fn-inj-splice src (fn-inj-path-offset src) ins)))))
            (fn-article-fields (fn-article-result-article (fn-article-parse src)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(o1t-fs o1t-cons-car-cdr) (theory 'minimal-theory))
           :use ((:instance o1t-fx-1 (x src))
                 (:instance o1t-fx-2 (x src))
                 (:instance o1t-fx-3 (x src))
                 (:instance o1t-fx-4 (x src))
                 (:instance o1t-abs
                            (y2 (fn-inj-splice src (fn-inj-path-offset src) ins))
                            (s1 (o1t-s1x src))
                            (y3 (o1t-y3x src ins))
                            (p (car (o1t-s2x src)))
                            (s2t (cdr (o1t-s2x src)))
                            (sfields (fn-article-fields (fn-article-result-article (fn-article-parse src))))))))))

(local
 (defthm o1t-plinep-of-head
  (implies (and (member-equal head (list *fn-cll-lock-head* *fn-cll-key-field* *fn-inj-path-field*
                                          *fn-inj-injection-date-field* *fn-inj-message-id-field*
                                          *fn-inj-date-field* *fn-inj-injection-info-field*))
                (true-listp x) (fn-ipp-no-crlfp x))
           (o1t-plinep (append head x)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-plinep o1t-nameok) (fn-article-wspp))
           :cases ((equal head *fn-cll-lock-head*) (equal head *fn-cll-key-field*)
                   (equal head *fn-inj-path-field*) (equal head *fn-inj-injection-date-field*)
                   (equal head *fn-inj-message-id-field*) (equal head *fn-inj-date-field*)
                   (equal head *fn-inj-injection-info-field*))))))

(local
 (defthm o1t-plinesp-append
  (implies (true-listp a)
           (equal (o1t-plinesp (append a b)) (and (o1t-plinesp a) (o1t-plinesp b))))
  :hints (("Goal" :induct (o1t-plinesp a)))))

(local
 (defthm o1t-plinesp-cl
  (implies (and (fn-cll-valuep lock) (fn-cll-values-p keys))
           (o1t-plinesp (o1s-cl-ls lock keys)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1s-cl-ls o1t-plinesp) (o1t-plinep-of-head))
           :use ((:instance o1t-plinep-of-head (head *fn-cll-lock-head*) (x lock))
                 (:instance o1t-plinep-of-head (head *fn-cll-key-field*) (x (fn-cll-key-values keys)))
                 (:instance o1s-valuep-facts (v lock))
                 (:instance o1s-key-values-facts))))))

(local
 (defthm o1t-plinesp-block
  (implies (and (true-listp date) (fn-ipp-no-crlfp date)
                (implies gid (and (true-listp msgid) (fn-ipp-no-crlfp msgid)))
                (true-listp agent) (fn-ipp-no-crlfp agent)
                (true-listp params) (fn-ipp-no-crlfp params))
           (o1t-plinesp (o1s-block-ls date msgid agent gid gdate params)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1s-block-ls o1t-plinesp) (o1t-plinep-of-head))
           :cases (gid)
           :use ((:instance o1t-plinep-of-head (head *fn-inj-injection-date-field*) (x date))
                 (:instance o1t-plinep-of-head (head *fn-inj-message-id-field*) (x msgid))
                 (:instance o1t-plinep-of-head (head *fn-inj-date-field*) (x date))
                 (:instance o1t-plinep-of-head (head *fn-inj-injection-info-field*) (x (append agent params))))))))

(local
 (defthm o1t-plinep-path
  (implies (and (true-listp agent) (fn-ipp-no-crlfp agent))
           (o1t-plinep (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable o1t-plinep-of-head)
           :use ((:instance o1t-plinep-of-head (head *fn-inj-path-field*) (x (append agent *fn-inj-path-tail*))))))))

(local
 (defthm o1t-octets-append
  (equal (o1s-octets (append a b)) (append (o1s-octets a) (o1s-octets b)))
  :hints (("Goal" :in-theory (enable o1s-octets)))))

(local
 (defun o1t-ls (source config obs secret account cfg)
  (declare (xargs :verify-guards nil))
  (let* ((d (fn-inj-decide source config obs))
         (msgid (fn-inj-decision-msgid d))
         (payload (fn-ipp-injected-octets d secret account cfg))
         (fields (fn-ctl-received-fields payload))
         (lock (fn-cl-lock-value secret account msgid fields))
         (keys (fn-cl-key-values secret account fields))
         (agent (fn-inj-config-agent config))
         (params (fn-ipp-params secret account (fn-ipp-complaints cfg)))
         (blk (o1s-block-ls (fn-ipp-date obs) msgid agent (fn-ipp-gid source) (fn-ipp-gdate source) params)))
    (append (o1s-cl-ls lock keys)
            (if (fn-inj-supplies-pathp source)
                blk
              (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*)) blk))))))

(local
 (defun o1t-tl (source config)
  (declare (xargs :verify-guards nil))
  (if (fn-inj-supplies-pathp source)
      (fn-inj-splice source (fn-inj-path-offset source) (fn-inj-path-insert (fn-inj-config-agent config)))
    source)))

(local
 (defthm o1t-pre-plines
  (implies (and (fn-cll-valuep lock) (fn-cll-values-p keys)
                (true-listp date) (fn-ipp-no-crlfp date)
                (implies gid (and (true-listp msgid) (fn-ipp-no-crlfp msgid)))
                (true-listp agent) (fn-ipp-no-crlfp agent)
                (true-listp params) (fn-ipp-no-crlfp params))
           (o1t-plinesp (append (o1s-cl-ls lock keys)
                                (if sp
                                    (o1s-block-ls date msgid agent gid gdate params)
                                  (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
                                        (o1s-block-ls date msgid agent gid gdate params))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1s-cl-ls o1t-plinesp-append) (o1t-plinesp-cl o1t-plinesp-block o1t-plinep-path))
           :use (o1t-plinesp-cl o1t-plinesp-block o1t-plinep-path
                 (:instance o1t-plinesp-append (a (o1s-cl-ls lock keys))
                            (b (if sp
                                   (o1s-block-ls date msgid agent gid gdate params)
                                 (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
                                       (o1s-block-ls date msgid agent gid gdate params)))))
                 (:instance o1t-plinep-path))))))

(local
 (defthm o1t-pre-octets
  (implies (and (equal injected
                       (if sp
                           (append (fn-ipp-block-with date msgid agent gid gdate params) spl)
                         (append (fn-ipp-prefix-with date msgid agent gid gdate params) source))))
           (equal (append (fn-cll-lines lock keys) injected)
                  (append (o1s-octets (append (o1s-cl-ls lock keys)
                                              (if sp
                                                  (o1s-block-ls date msgid agent gid gdate params)
                                                (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
                                                      (o1s-block-ls date msgid agent gid gdate params)))))
                          (if sp spl source))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-octets-append) (fn-cll-lines fn-ipp-block-with fn-ipp-prefix-with))
           :use (o1s-cl-lines-are-lines o1s-block-with-is-lines o1s-prefix-with-is-lines)))))

(local
 (defthm o1t-stored-is
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (and (equal (fn-o1-post-stored-octets source config obs secret account cfg)
                       (append (o1s-octets (o1t-ls source config obs secret account cfg))
                               (o1t-tl source config)))
                (o1t-plinesp (o1t-ls source config obs secret account cfg))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1t-ls o1t-tl fn-o1-post-stored-octets)
                           (o1s-injected-core fn-ipp-injected-octets-carry-the-parameters
                            o1s-injected-facts fn-ipp-injected-octets fn-inj-decide
                            fn-ipp-block-with fn-ipp-prefix-with fn-ipp-params fn-ipp-complaints
                            fn-inj-generated-identity-is-the-clock-identity
                            o1s-generated-id-facts fn-article-parse fn-af-proto-article-check
                            fn-article-result-okp fn-article-result-article fn-inj-nth
                            o1s-params-facts o1s-date-shape o1s-date-no-crlf o1s-config-agent-facts
                            o1s-counts-are-recursions o1s-served-is o1s-cl-lines-are-lines
                            o1s-block-with-is-lines o1s-prefix-with-is-lines
                            o1t-pre-plines o1t-pre-octets
                            o1s-path-insert-facts fn-inj-splice fn-inj-path-insert fn-inj-path-offset
                            fn-inj-supplies-pathp
                            o1s-block-ls o1s-cl-ls o1s-octets o1t-plinesp fn-cll-lines
                            fn-cl-lock-value-is-a-value fn-cl-key-values-are-values
                            fn-cl-lock-value fn-cl-key-values fn-ctl-received-fields))
           :use ((:instance fn-ipp-injected-octets-carry-the-parameters (login account))
                 o1s-injected-facts
                 (:instance fn-inj-generated-identity-is-the-clock-identity (observation obs))
                 (:instance o1s-generated-id-facts)
                 (:instance o1s-params-facts (login account))
                 (:instance o1s-date-shape (inst (fn-inj-instant-of (fn-clock-wall obs))))
                 (:instance o1s-date-no-crlf (inst (fn-inj-instant-of (fn-clock-wall obs))))
                 (:instance o1s-config-agent-facts)
                 (:instance o1s-served-is (ring secret)
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (payload (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg)))
                 (:instance fn-cl-lock-value-is-a-value (ring secret)
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (fields (fn-ctl-received-fields
                                     (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg))))
                 (:instance fn-cl-key-values-are-values (ring secret)
                            (fields (fn-ctl-received-fields
                                     (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg))))
                 (:instance o1t-pre-plines
                            (lock (fn-cl-lock-value secret account (fn-inj-decision-msgid (fn-inj-decide source config obs))
                                                    (fn-ctl-received-fields
                                                     (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg))))
                            (keys (fn-cl-key-values secret account
                                                    (fn-ctl-received-fields
                                                     (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg))))
                            (date (fn-ipp-date obs))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (agent (fn-inj-config-agent config))
                            (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source))
                            (params (fn-ipp-params secret account (fn-ipp-complaints cfg)))
                            (sp (fn-inj-supplies-pathp source)))
                 (:instance o1t-pre-octets
                            (lock (fn-cl-lock-value secret account (fn-inj-decision-msgid (fn-inj-decide source config obs))
                                                    (fn-ctl-received-fields
                                                     (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg))))
                            (keys (fn-cl-key-values secret account
                                                    (fn-ctl-received-fields
                                                     (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg))))
                            (injected (fn-ipp-injected-octets (fn-inj-decide source config obs) secret account cfg))
                            (date (fn-ipp-date obs))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (agent (fn-inj-config-agent config))
                            (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source))
                            (params (fn-ipp-params secret account (fn-ipp-complaints cfg)))
                            (sp (fn-inj-supplies-pathp source))
                            (spl (fn-inj-splice source (fn-inj-path-offset source)
                                                (fn-inj-path-insert (fn-inj-config-agent config)))))
                 )))))

(local
 (defthm o1t-stored-sp
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (and (implies (fn-inj-supplies-pathp source) (fn-inj-path-offset source))
                (fn-ipp-no-crlfp (fn-inj-path-insert (fn-inj-config-agent config)))
                (true-listp (fn-inj-path-insert (fn-inj-config-agent config)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-inj-decide fn-inj-injectedp fn-inj-supplies-pathp fn-inj-path-offset
                               fn-inj-path-insert o1s-injected-facts o1s-config-agent-facts
                               o1s-path-insert-facts)
           :use (o1s-injected-facts o1s-config-agent-facts
                 (:instance o1s-path-insert-facts (agent (fn-inj-config-agent config)))
                 fn-inj-an-injected-supplied-path-has-an-offset)))))

(local
 (defthm o1t-agree-abs
  (implies (and (equal stored (append (o1s-octets ls) tl))
                (o1t-plinesp ls)
                (fn-article-result-okp (fn-article-parse source))
                (fn-article-result-okp (fn-article-parse stored))
                (implies sp (and (fn-inj-path-offset source)
                                 (fn-ipp-no-crlfp ins) (true-listp ins)))
                (equal tl (if sp (fn-inj-splice source (fn-inj-path-offset source) ins) source)))
           (o1t-fields-agree
            (fn-article-fields (fn-article-result-article (fn-article-parse stored)))
            (fn-article-fields (fn-article-result-article (fn-article-parse source)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :cases (sp)
           :use ((:instance o1t-splice-agree (src source))
                 (:instance o1t-prefixed-agree (src source)))))))

(local
 (defthm o1t-tl-def
  (equal (o1t-tl source config)
         (if (fn-inj-supplies-pathp source)
             (fn-inj-splice source (fn-inj-path-offset source) (fn-inj-path-insert (fn-inj-config-agent config)))
           source))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable o1t-tl)))))

(local
 (defthm o1t-stored-agrees
  (implies (and (fn-inj-injectedp (fn-inj-decide source config obs))
                (fn-article-result-okp (fn-article-parse source))
                (fn-article-result-okp
                 (fn-article-parse (fn-o1-post-stored-octets source config obs secret account cfg))))
           (o1t-fields-agree
            (fn-article-fields (fn-article-result-article
                                (fn-article-parse (fn-o1-post-stored-octets source config obs secret account cfg))))
            (fn-article-fields (fn-article-result-article (fn-article-parse source)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-inj-decide fn-inj-injectedp fn-inj-supplies-pathp fn-inj-path-offset
                               fn-inj-path-insert fn-article-parse fn-inj-splice o1t-ls
                               fn-o1-post-stored-octets o1s-octets o1t-agree-abs)
           :use (o1t-stored-is o1t-stored-sp o1t-tl-def
                 (:instance o1t-agree-abs
                            (stored (fn-o1-post-stored-octets source config obs secret account cfg))
                            (ls (o1t-ls source config obs secret account cfg))
                            (tl (o1t-tl source config))
                            (sp (fn-inj-supplies-pathp source))
                            (ins (fn-inj-path-insert (fn-inj-config-agent config)))))))))

(local
 (defthm o1t-ng-status-kind
  (or (equal (car (fn-af-newsgroups-status a)) :missing)
      (equal (car (fn-af-newsgroups-status a)) :duplicate)
      (equal (car (fn-af-newsgroups-status a)) :invalid)
      (equal (car (fn-af-newsgroups-status a)) :single))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-af-newsgroups-status) (fn-article-get-headers fn-af-newsgroups-field-value))))))

(local
 (defthm o1t-nth2-check
  (implies (consp (fn-inj-nth 2 (fn-af-proto-article-check a)))
           (and (equal (car (fn-af-newsgroups-status a)) :single)
                (equal (fn-inj-nth 2 (fn-af-proto-article-check a))
                       (cadr (fn-af-newsgroups-status a)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-af-proto-article-check fn-af-relayed-article-check
                            fn-af-status-kind fn-af-status-value fn-inj-nth fn-inj-car fn-inj-cdr)
                           (fn-af-newsgroups-status fn-af-message-id-status fn-article-get-headers))
           :use (o1t-ng-status-kind)))))

(local
 (defthm o1t-groups-cases
  (or (equal (fn-inj-decision-groups (fn-inj-decide source config obs)) nil)
      (and (fn-inj-injectedp (fn-inj-decide source config obs))
           (fn-article-result-okp (fn-article-parse source))
           (equal (fn-inj-decision-groups (fn-inj-decide source config obs))
                  (fn-inj-nth 2 (fn-af-proto-article-check
                                 (fn-article-result-article (fn-article-parse source)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-inj-decide fn-inj-injectedp fn-inj-refuse)
                                  (fn-inj-configp fn-inj-mandatory-reason
                                   fn-inj-groups-admissiblep fn-inj-absentp
                                   fn-inj-prefix fn-inj-date-octets
                                   fn-inj-instant-of fn-inj-generated-message-id
                                   fn-inj-append floor fn-article-parse
                                   fn-af-proto-article-check fn-article-result-okp
                                   fn-article-result-article fn-article-syntax-p
                                   fn-clock-observationp fn-clock-has-wall
                                   fn-clock-wall fn-clock-monotonic fn-article-census-refusal
                                   fn-article-header-census fn-inj-block fn-inj-splice
                                   fn-inj-path-reason fn-inj-other-reason fn-inj-path-offset
                                   fn-inj-path-insert fn-inj-nth fn-article-get-headers
                                   fn-article-successful-parse-is-parse-lines fn-article-successful-parse-lines-okp))))))

(local
 (defthm o1t-subseqp-refl
  (fn-o1-subseqp x x)
  :hints (("Goal" :induct (len x) :in-theory (enable fn-o1-subseqp)))))

(local
 (defthm o1t-plan-file
  (implies (and (equal (car (fn-pa-filing-plan received groups domain)) :file)
                (not (equal (car (fn-ctl-classify-octets received)) :control)))
           (equal (fn-pa-filing-plan received groups domain) (list :file groups)))
  :hints (("Goal" :in-theory (e/d (fn-pa-filing-plan) (fn-ctl-classify-octets))))))

(local
 (defthm o1t-sng-def
  (implies (fn-article-result-okp (fn-article-parse source))
           (equal (fn-o1-source-newsgroups source)
                  (if (equal (car (fn-af-newsgroups-status (fn-article-result-article (fn-article-parse source))))
                             :single)
                      (cadr (fn-af-newsgroups-status (fn-article-result-article (fn-article-parse source))))
                    nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-o1-source-newsgroups)))))

(local
 (defthm o1t-w2
  (implies (and (fn-article-result-okp (fn-article-parse source))
                (consp (fn-inj-nth 2 (fn-af-proto-article-check
                                      (fn-article-result-article (fn-article-parse source))))))
           (equal (fn-inj-nth 2 (fn-af-proto-article-check
                                 (fn-article-result-article (fn-article-parse source))))
                  (fn-o1-source-newsgroups source)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance o1t-nth2-check (a (fn-article-result-article (fn-article-parse source))))
                 o1t-sng-def)))))

(local
 (defthm o1t-subseqp-atom
  (implies (atom x) (fn-o1-subseqp x y))
  :hints (("Goal" :in-theory (enable fn-o1-subseqp)))))

(local
 (defthm o1t-w-lemma
  (implies (fn-article-result-okp (fn-article-parse source))
           (fn-o1-subseqp (fn-inj-nth 2 (fn-af-proto-article-check
                                         (fn-article-result-article (fn-article-parse source))))
                          (fn-o1-source-newsgroups source)))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :cases ((consp (fn-inj-nth 2 (fn-af-proto-article-check
                                         (fn-article-result-article (fn-article-parse source))))))
           :use (o1t-w2 (:instance o1t-subseqp-atom
                                   (x (fn-inj-nth 2 (fn-af-proto-article-check
                                                     (fn-article-result-article (fn-article-parse source)))))
                                   (y (fn-o1-source-newsgroups source)))
                 (:instance o1t-subseqp-refl (x (fn-o1-source-newsgroups source))))))))

(local
 (defthm o1t-sng-agree
  (implies (and (fn-article-result-okp (fn-article-parse source))
                (fn-article-result-okp (fn-article-parse stored))
                (o1t-fields-agree (fn-article-fields (fn-article-result-article (fn-article-parse stored)))
                                  (fn-article-fields (fn-article-result-article (fn-article-parse source)))))
           (equal (fn-o1-source-newsgroups source) (fn-o1-source-newsgroups stored)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance o1t-agree-source-newsgroups (s source) (r stored))
                 (:instance o1t-fields-agree
                            (fs (fn-article-fields (fn-article-result-article (fn-article-parse stored))))
                            (gs (fn-article-fields (fn-article-result-article (fn-article-parse source))))))
           :in-theory (e/d (o1t-fields-agree) (fn-article-parse fn-o1-source-newsgroups fn-article-result-article
                                              fn-article-result-okp o1t-agree-source-newsgroups))))))

(local
 (defthm o1t-groups-in-stored
  (implies (fn-article-result-okp
            (fn-article-parse (fn-o1-post-stored-octets source config obs secret account cfg)))
           (fn-o1-subseqp (fn-inj-decision-groups (fn-inj-decide source config obs))
                          (fn-o1-source-newsgroups
                           (fn-o1-post-stored-octets source config obs secret account cfg))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use (o1t-groups-cases o1t-stored-agrees
                 (:instance o1t-w-lemma)
                 (:instance o1t-sng-agree (stored (fn-o1-post-stored-octets source config obs secret account cfg)))
                 (:instance o1t-subseqp-atom
                            (x (fn-inj-decision-groups (fn-inj-decide source config obs)))
                            (y (fn-o1-source-newsgroups
                                (fn-o1-post-stored-octets source config obs secret account cfg)))))))))

(local
 (defthm o1t-ctl-case
  (implies (and (equal plan (fn-pa-filing-plan stored groups domain))
                (equal (car plan) :file)
                (equal (car (fn-ctl-classify-octets stored)) :control))
           (equal (cadr plan)
                  (list (fn-record-string-octets
                         (fn-ctl-filing-group (cadr (fn-ctl-classify-octets stored)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ctl-classify-octets fn-pa-filing-plan fn-record-string-octets)
           :use ((:instance fn-ctl-control-article-is-filed-only-in-control (received stored)))))))

(local
 (defthm o1t-other-case
  (implies (and (equal plan (fn-pa-filing-plan stored groups domain))
                (equal (car plan) :file)
                (not (equal (car (fn-ctl-classify-octets stored)) :control)))
           (equal (cadr plan) groups))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ctl-classify-octets fn-pa-filing-plan)
           :use (o1t-plan-file)))))

(local
 (defthm o1t-core-abs
  (implies (and (equal plan (fn-pa-filing-plan stored groups domain))
                (equal (car plan) :file)
                (fn-o1-subseqp groups (fn-o1-source-newsgroups stored)))
           (or (let ((c (fn-ctl-classify-octets stored)))
                 (and (consp c) (eq (car c) :control)
                      (equal (cadr plan)
                             (list (fn-record-string-octets (fn-ctl-filing-group (cadr c)))))))
               (fn-o1-subseqp (cadr plan) (fn-o1-source-newsgroups stored))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ctl-classify-octets fn-pa-filing-plan fn-record-string-octets
                               fn-o1-subseqp fn-o1-source-newsgroups)
           :cases ((equal (car (fn-ctl-classify-octets stored)) :control))
           :use (o1t-ctl-case o1t-other-case)))))

; P4-1 (O1 packet 4, the unsigned served POST arm): the groups the commit
; files (fn-pa-filing-plan over the STORED bytes, books/peer-authored-
; accept.lisp:659, of the decision's groups) are filed within the stored
; bytes, in the octet-group form the plan returns.
(defun fn-o1-filed-octets-within-sourcep (ogroups payload)
  (declare (xargs :guard t :verify-guards nil))
  (or (let ((c (fn-ctl-classify-octets payload)))
        (and (consp c) (eq (car c) :control)
             (equal ogroups (list (fn-record-string-octets (fn-ctl-filing-group (cadr c)))))))
      (fn-o1-subseqp ogroups (fn-o1-source-newsgroups payload))))

(defthm fn-o1-served-post-files-within-the-stored
  (let* ((d (fn-inj-decide source config obs))
         (stored (fn-o1-post-stored-octets source config obs secret account cfg))
         (plan (fn-pa-filing-plan stored (fn-inj-decision-groups d) domain)))
    (implies (and (fn-article-result-okp (fn-article-parse stored))
                  (equal (car plan) :file))
             (fn-o1-filed-octets-within-sourcep (cadr plan) stored)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-o1-filed-octets-within-sourcep) (theory 'minimal-theory))
           :use ((:instance o1t-core-abs
                            (stored (fn-o1-post-stored-octets source config obs secret account cfg))
                            (groups (fn-inj-decision-groups (fn-inj-decide source config obs)))
                            (plan (fn-pa-filing-plan (fn-o1-post-stored-octets source config obs secret account cfg)
                                                     (fn-inj-decision-groups (fn-inj-decide source config obs))
                                                     domain)))
                 o1t-groups-in-stored))))
