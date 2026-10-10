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
