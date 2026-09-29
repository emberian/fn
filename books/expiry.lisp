; fn: which stored articles the operator's expiry policy expires (Q14;
; RFC 5536 section 3.2.5; RFC 3977 sections 6.1.1, 6.2.1; D03, D13).
;
; The policy is the operator's (books/expiry-policy.lisp): per group, KEEP,
; DEFAULT and PURGE days and an OCTETS size window, or the "*" policy, or
; nothing (D03's default: keep forever).  This book decides, for every stored
; article at an instant NOW, whether the policy expires it, and hands the
; answer to the one reclaim path (books/store-reclaim-pack.lisp: the context's
; EXPIRED set, released through books/expiry-verdict.lisp, so every holder
; still keeps what it holds).  Nothing here reads a clock, a file or the
; network: NOW is the reclaim's recorded instant (books/reclaim-instant.lisp).
;
; Age (INN expire.ctl's semantics, per group):
;   the instant an article of the group asks to leave is its Expires: header's
;   date-time (RFC 5536 section 3.2.5; RFC 5322 section 3.3, read by
;   books/relay-checks.lisp `fn-rck-date-instant', moved to the stamp's
;   2000-01-01 epoch), or without a usable one its
;   acceptance stamp plus DEFAULT days, or never;
;   that instant is raised to the stamp plus KEEP days and lowered to the stamp
;   plus PURGE days (`fn-xpy-age-instant'), so a poster's Expires: is honoured
;   exactly within the operator's bounds (`fn-xpy-age-instant-honours-expires-
;   within-the-bounds') and never outside them (`fn-xpy-age-instant-is-within-
;   the-bounds').  An article accepted with no natural stamp (a :legacy stamp)
;   never expires by age, as under the store-wide rule.
; Size (fn's own):
;   an article is outside the group's window when the live payload octets of
;   the group's articles accepted at or after it exceed OCTETS
;   (`fn-xpy-size-outp'): the newest articles that fit stay.  A tombstone
;   counts no octets.
; Cross-posts:
;   an article expires only when EVERY group it is filed in expires it
;   (`fn-xpy-article-expiredp'): a group that keeps it keeps its payload.
;
; The walk (`fn-xpy-expired-set') reads the Store's article list once, newest
; first, carrying one running octet sum per group, and reads an article's
; payload header only when a group it is filed in has an age policy.
; KEYSTONE `fn-xpy-expired-set-is-the-spec': a Message-ID is in the set
; exactly when the specification (`fn-xpy-spec', which recomputes each
; window from the articles themselves) expires it.
(in-package "ACL2")
(include-book "expiry-policy")
(include-book "store-reclaim-pack")
(include-book "relay-checks")

;; The tau system is off in this book (docs/proof-style.md 9.1).
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The Expires: instant of an article's octets

(defconst *fn-xpy-expires-name* '(101 120 112 105 114 101 115)) ; "expires"

; The header block of an article's octets: everything up to and including
; the first empty line (CRLF CRLF), or every octet when there is none.  The
; walk stops there; the body is never read.
(defun fn-xpy-header-block (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (if (and (equal (car bytes) 13)
               (consp (cdr bytes)) (equal (cadr bytes) 10)
               (consp (cddr bytes)) (equal (caddr bytes) 13)
               (consp (cdddr bytes)) (equal (cadddr bytes) 10))
          (list 13 10 13 10)
        (cons (car bytes) (fn-xpy-header-block (cdr bytes))))
    nil))

; The Expires: header's instant on the acceptance stamp's clock -- seconds
; since 2000-01-01T00:00:00Z, the DTN epoch of books/clock.lisp and
; books/records-stamp.lisp -- or nil when the header block does not parse,
; the field is absent or repeated, or its value is not an RFC 5322
; date-time.  The date reader answers seconds since 1970, so the instant is
; moved by the 10,957 days between the epochs, as books/peer-inbound.lisp
; moves its clock (`fn-peer-clock-unix-seconds'); the first native run of
; this book compared them unconverted and honoured no Expires: at all.
(defun fn-xpy-expires-instant (bytes)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse (fn-xpy-header-block bytes))))
    (if (and (fn-article-result-okp parsed) (true-listp parsed)
             (fn-article-syntax-p (fn-article-result-article parsed)))
        (let* ((value (fn-path-single-field-value (fn-article-result-article parsed)
                                                  *fn-xpy-expires-name*))
               (unix (and value (fn-rck-date-instant value))))
          (if (integerp unix) (- unix *fn-rck-dtn-epoch-unix-seconds*) nil))
      nil)))

; -----------------------------------------------------------------------------
; Age

(defun fn-xpy-days (n)
  (declare (xargs :guard t))
  (* *fn-xpy-seconds-per-day* (nfix n)))

; The instant an article accepted at STAMP, with Expires: instant EXPIRES (an
; integer, or nil), leaves under policy P by age; nil for never.
(defun fn-xpy-age-instant (p stamp expires)
  (declare (xargs :guard t))
  (if (and (fn-xpy-agep p) (natp stamp))
      (let* ((asked (cond ((integerp expires) expires)
                          ((posp (fn-xpy-policy-default p))
                           (+ stamp (fn-xpy-days (fn-xpy-policy-default p))))
                          (t nil)))
             (lower (+ stamp (fn-xpy-days (fn-xpy-policy-keep p))))
             (upper (if (posp (fn-xpy-policy-purge p))
                        (+ stamp (fn-xpy-days (fn-xpy-policy-purge p)))
                      nil)))
        (cond ((null asked) upper)
              ((null upper) (max asked lower))
              (t (min (max asked lower) upper))))
    nil))

(defun fn-xpy-age-expiredp (p now stamp expires)
  (declare (xargs :guard t))
  (let ((at (fn-xpy-age-instant p stamp expires)))
    (and (integerp at) (natp now) (<= at now))))

;  KEYSTONE (the operator's bounds hold).  Under a policy whose KEEP is at
; most its PURGE, the instant an article leaves by age is never before its
; stamp plus KEEP days, and never after its stamp plus PURGE days when PURGE
; is set: whatever its Expires: header asks.
(defthm fn-xpy-age-instant-is-within-the-bounds
  (let ((at (fn-xpy-age-instant p stamp expires)))
    (implies (and (integerp at)
                  (fn-xpy-orderedp (fn-xpy-policy-keep p) (fn-xpy-policy-purge p)))
             (and (<= (+ stamp (fn-xpy-days (fn-xpy-policy-keep p))) at)
                  (implies (posp (fn-xpy-policy-purge p))
                           (<= at (+ stamp (fn-xpy-days (fn-xpy-policy-purge p))))))))
  :rule-classes nil)

;  KEYSTONE (RFC 5536 section 3.2.5, honoured within the bounds).  An
; article whose Expires: header names an instant at or after its stamp plus
; KEEP days, and at or before its stamp plus PURGE days (or PURGE unset),
; leaves by age at exactly that instant, under any policy with an age rule.
(defthm fn-xpy-age-instant-honours-expires-within-the-bounds
  (implies (and (fn-xpy-agep p) (natp stamp) (integerp expires)
                (<= (+ stamp (fn-xpy-days (fn-xpy-policy-keep p))) expires)
                (or (not (posp (fn-xpy-policy-purge p)))
                    (<= expires (+ stamp (fn-xpy-days (fn-xpy-policy-purge p))))))
           (equal (fn-xpy-age-instant p stamp expires) expires)))

;  KEYSTONE (no Expires: header).  Without a usable Expires: instant, an
; article leaves DEFAULT days after its stamp (held within KEEP and PURGE),
; or at its stamp plus PURGE days when DEFAULT is unset, or never.
(defthm fn-xpy-age-instant-without-expires
  (implies (and (fn-xpy-agep p) (natp stamp) (not (integerp expires)))
           (equal (fn-xpy-age-instant p stamp expires)
                  (let ((lower (+ stamp (fn-xpy-days (fn-xpy-policy-keep p))))
                        (upper (and (posp (fn-xpy-policy-purge p))
                                    (+ stamp (fn-xpy-days (fn-xpy-policy-purge p))))))
                    (if (posp (fn-xpy-policy-default p))
                        (let ((asked (+ stamp (fn-xpy-days (fn-xpy-policy-default p)))))
                          (if upper (min (max asked lower) upper) (max asked lower)))
                      upper)))))

;  KEYSTONE (D03 by default).  A policy with no age rule, or an article with
; no natural acceptance stamp, never expires by age.
(defthm fn-xpy-no-age-rule-never-expires-by-age
  (implies (or (not (fn-xpy-agep p)) (not (natp stamp)))
           (not (fn-xpy-age-expiredp p now stamp expires))))

; -----------------------------------------------------------------------------
; Size

; The live payload octets of GROUP's articles in ARTICLES: a tombstone counts
; nothing, an article not filed in GROUP counts nothing.
(defun fn-xpy-filed-in-p (group memberships)
  (declare (xargs :guard t))
  (if (consp memberships)
      (or (and (consp (car memberships)) (equal (car (car memberships)) group))
          (fn-xpy-filed-in-p group (cdr memberships)))
    nil))

(defun fn-xpy-live-octets (a fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (fn-rcl-payload-tombstonep (fn-article-payload a) fn-arena)
      0
    (fn-rcl-payload-len (fn-article-payload a) fn-arena)))

(defun fn-xpy-window-octets (group articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (+ (if (fn-xpy-filed-in-p group (fn-article-memberships (car articles)))
             (fn-xpy-live-octets (car articles) fn-arena)
           0)
         (fn-xpy-window-octets group (cdr articles) fn-arena))
    0))

; Whether an article is outside GROUP's window, WINDOW being the article
; itself and every article of the store accepted after it.
(defun fn-xpy-size-outp (p group window fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (fn-xpy-sizep p)
       (< (fn-xpy-policy-octets p) (fn-xpy-window-octets group window fn-arena))))

; -----------------------------------------------------------------------------
; One article

; Whether any group of MEMBERSHIPS has an age policy (so the Expires: header
; is worth reading).
(defun fn-xpy-any-agep (q memberships)
  (declare (xargs :guard t))
  (if (consp memberships)
      (or (and (consp (car memberships))
               (fn-xpy-agep (fn-xpy-group-policy-of q (car (car memberships)))))
          (fn-xpy-any-agep q (cdr memberships)))
    nil))

(defun fn-xpy-article-expires (q a fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (fn-xpy-any-agep q (fn-article-memberships a))
      (fn-xpy-expires-instant (fn-rcl-payload-bytes (fn-article-payload a) fn-arena))
    nil))

; Whether GROUP's policy expires the article (age or size).
(defun fn-xpy-group-expiresp (q now group stamp expires window fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((p (fn-xpy-group-policy-of q group)))
    (or (fn-xpy-age-expiredp p now stamp expires)
        (fn-xpy-size-outp p group window fn-arena))))

(defun fn-xpy-every-group-expiresp (q now memberships stamp expires window fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp memberships)
      (and (consp (car memberships))
           (fn-xpy-group-expiresp q now (car (car memberships)) stamp expires window
                                  fn-arena)
           (fn-xpy-every-group-expiresp q now (cdr memberships) stamp expires window
                                        fn-arena))
    t))

; THE ARTICLE: filed in at least one group, and every group it is filed in
; expires it.  WINDOW is the article and every article accepted after it.
(defun fn-xpy-article-expiredp (q now a window fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (consp (fn-article-memberships a))
       (fn-xpy-every-group-expiresp q now (fn-article-memberships a)
                                    (fn-article-stamp a)
                                    (fn-xpy-article-expires q a fn-arena)
                                    window fn-arena)))

(local
 (defthm fn-xpy-every-group-member
   (implies (and (fn-xpy-every-group-expiresp q now memberships stamp expires window
                                              fn-arena)
                 (member-equal m memberships))
            (and (consp m)
                 (fn-xpy-group-expiresp q now (car m) stamp expires window fn-arena)))
   :hints (("Goal" :in-theory (disable fn-xpy-group-expiresp)))))

;  KEYSTONE (cross-posts).  An article one of whose groups does not expire
; it is not expired: a group that keeps it keeps its payload.
(defthm fn-xpy-a-group-that-keeps-it-keeps-it
  (implies (and (member-equal m (fn-article-memberships a))
                (consp m)
                (not (fn-xpy-group-expiresp q now (car m) (fn-article-stamp a)
                                            (fn-xpy-article-expires q a fn-arena)
                                            window fn-arena)))
           (not (fn-xpy-article-expiredp q now a window fn-arena)))
  :hints (("Goal" :in-theory (disable fn-xpy-group-expiresp fn-xpy-article-expires)
                  :use ((:instance fn-xpy-every-group-member
                                   (memberships (fn-article-memberships a))
                                   (stamp (fn-article-stamp a))
                                   (expires (fn-xpy-article-expires q a fn-arena)))))))

; -----------------------------------------------------------------------------
; The specification over the store

; ARTICLES newest first (books/acceptance.lisp conses each accepted article
; onto the list); NEWER the articles already passed.  The Message-IDs the
; policy expires, in list order.
(defun fn-xpy-spec (q now articles newer fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (let ((window (cons (car articles) newer)))
        (if (fn-xpy-article-expiredp q now (car articles) window fn-arena)
            (cons (fn-article-msgid (car articles))
                  (fn-xpy-spec q now (cdr articles) window fn-arena))
          (fn-xpy-spec q now (cdr articles) window fn-arena)))
    nil))

; -----------------------------------------------------------------------------
; The executable walk: one running sum per group instead of a window

(defun fn-xpy-sum (group sums)
  (declare (xargs :guard t))
  (nfix (cdr (hons-get group sums))))

; Add O to the sum of each distinct group of MEMBERSHIPS (SEEN: the groups
; this article already added to).
(defun fn-xpy-add-octets (memberships seen o sums)
  (declare (xargs :guard (true-listp seen)))
  (if (consp memberships)
      (if (and (consp (car memberships))
               (not (member-equal (car (car memberships)) seen)))
          (fn-xpy-add-octets (cdr memberships) (cons (car (car memberships)) seen) o
                             (hons-acons (car (car memberships))
                                         (+ (nfix o) (fn-xpy-sum (car (car memberships)) sums))
                                         sums))
        (fn-xpy-add-octets (cdr memberships) seen o sums))
    sums))

; The sums of a window, oldest article added first.
(defun fn-xpy-sums-of (window fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp window)
      (fn-xpy-add-octets (fn-article-memberships (car window)) nil
                         (fn-xpy-live-octets (car window) fn-arena)
                         (fn-xpy-sums-of (cdr window) fn-arena))
    nil))

(defun fn-xpy-group-expiresp-sums (q now group stamp expires sums)
  (declare (xargs :guard t))
  (let ((p (fn-xpy-group-policy-of q group)))
    (or (fn-xpy-age-expiredp p now stamp expires)
        (and (fn-xpy-sizep p)
             (< (fn-xpy-policy-octets p) (fn-xpy-sum group sums))))))

(defun fn-xpy-every-group-expiresp-sums (q now memberships stamp expires sums)
  (declare (xargs :guard t))
  (if (consp memberships)
      (and (consp (car memberships))
           (fn-xpy-group-expiresp-sums q now (car (car memberships)) stamp expires sums)
           (fn-xpy-every-group-expiresp-sums q now (cdr memberships) stamp expires sums))
    t))

(defun fn-xpy-article-expiredp-sums (q now a sums fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (consp (fn-article-memberships a))
       (fn-xpy-every-group-expiresp-sums q now (fn-article-memberships a)
                                         (fn-article-stamp a)
                                         (fn-xpy-article-expires q a fn-arena)
                                         sums)))

; The walk: tail recursive (one frame at a time, however long the history),
; carrying the sums of the articles passed and the set so far.
(defun fn-xpy-walk (q now articles sums set fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (let ((sums (fn-xpy-add-octets (fn-article-memberships (car articles)) nil
                                     (fn-xpy-live-octets (car articles) fn-arena)
                                     sums)))
        (fn-xpy-walk q now (cdr articles) sums
                     (if (fn-xpy-article-expiredp-sums q now (car articles) sums fn-arena)
                         (hons-acons (fn-article-msgid (car articles)) t set)
                       set)
                     fn-arena))
    (prog2$ (fast-alist-free sums) set)))

; THE SET the reclaim's context carries: a fast alist (msgid . t) of the
; Message-IDs the policy expires at NOW among the Store's ARTICLES.
(defun fn-xpy-expired-set (q now articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-xpy-walk q now articles nil nil fn-arena))

; -----------------------------------------------------------------------------
; The walk is the specification

(local
 (defthm fn-xpy-sum-of-hons-acons
   (equal (fn-xpy-sum g (hons-acons k x sums))
          (if (equal g k) (nfix x) (fn-xpy-sum g sums)))))

(local
 (defthm fn-xpy-sum-of-add-octets
   (equal (fn-xpy-sum g (fn-xpy-add-octets memberships seen o sums))
          (+ (fn-xpy-sum g sums)
             (if (and (fn-xpy-filed-in-p g memberships)
                      (not (member-equal g seen)))
                 (nfix o)
               0)))
   :hints (("Goal" :induct (fn-xpy-add-octets memberships seen o sums)))))

(local
 (defthm fn-xpy-sum-of-nil
   (equal (fn-xpy-sum g nil) 0)
   :hints (("Goal" :in-theory (enable fn-xpy-sum)))))

(local (in-theory (disable fn-xpy-sum)))

(local
 (defthm fn-xpy-sum-of-sums-of
   (equal (fn-xpy-sum g (fn-xpy-sums-of window fn-arena))
          (fn-xpy-window-octets g window fn-arena))
   :hints (("Goal" :induct (fn-xpy-window-octets g window fn-arena)
                   :in-theory (enable fn-xpy-live-octets)))))

(local
 (defthm fn-xpy-group-sums-is-window
   (equal (fn-xpy-group-expiresp-sums q now group stamp expires
                                      (fn-xpy-sums-of window fn-arena))
          (fn-xpy-group-expiresp q now group stamp expires window fn-arena))
   :hints (("Goal" :in-theory (e/d (fn-xpy-size-outp)
                                   (fn-xpy-sums-of fn-xpy-window-octets
                                    fn-xpy-group-policy-of fn-xpy-age-expiredp))))))

(local
 (defthm fn-xpy-every-group-sums-is-window
   (equal (fn-xpy-every-group-expiresp-sums q now memberships stamp expires
                                            (fn-xpy-sums-of window fn-arena))
          (fn-xpy-every-group-expiresp q now memberships stamp expires window
                                       fn-arena))
   :hints (("Goal" :induct (fn-xpy-every-group-expiresp q now memberships stamp expires
                                                        window fn-arena)
                   :in-theory (disable fn-xpy-sums-of fn-xpy-group-expiresp-sums
                                       fn-xpy-group-expiresp)))))

(local
 (defthm fn-xpy-article-sums-is-window
   (equal (fn-xpy-article-expiredp-sums q now a (fn-xpy-sums-of window fn-arena) fn-arena)
          (fn-xpy-article-expiredp q now a window fn-arena))))

(local (in-theory (disable fn-xpy-article-expiredp-sums fn-xpy-article-expiredp)))

(local
 (defthm fn-xpy-add-octets-is-sums-of-cons
   (equal (fn-xpy-add-octets (fn-article-memberships a) nil (fn-xpy-live-octets a fn-arena)
                             (fn-xpy-sums-of newer fn-arena))
          (fn-xpy-sums-of (cons a newer) fn-arena))))

(local
 (defun fn-xpy-walk-ind (q now articles newer set fn-arena)
   (declare (xargs :stobjs fn-arena :verify-guards nil))
   (if (consp articles)
       (fn-xpy-walk-ind q now (cdr articles) (cons (car articles) newer)
                        (if (fn-xpy-article-expiredp q now (car articles)
                                                     (cons (car articles) newer) fn-arena)
                            (hons-acons (fn-article-msgid (car articles)) t set)
                          set)
                        fn-arena)
     (list q now newer set))))

(local
 (defthm fn-xpy-walk-is-spec
   (iff (hons-assoc-equal m (fn-xpy-walk q now articles (fn-xpy-sums-of newer fn-arena)
                                         set fn-arena))
        (or (member-equal m (fn-xpy-spec q now articles newer fn-arena))
            (hons-assoc-equal m set)))
   :hints (("Goal" :induct (fn-xpy-walk-ind q now articles newer set fn-arena)
                   :in-theory (disable fn-xpy-sums-of fn-xpy-add-octets
                                       fn-xpy-live-octets)))))

;  KEYSTONE.  A Message-ID is in the set the reclaim's context carries
; exactly when the specification expires it: some article of the store
; with that Message-ID is filed in at least one group, and every group it is
; filed in expires it at NOW -- by age (`fn-xpy-age-expiredp' of its stamp
; and Expires: header under the group's policy) or by size (the live octets
; of the group's articles accepted at or after it exceed the group's
; window).
(defthm fn-xpy-expired-set-is-the-spec
  (iff (fn-xpy-expiredp m (fn-xpy-expired-set q now articles fn-arena))
       (member-equal m (fn-xpy-spec q now articles nil fn-arena)))
  :hints (("Goal" :in-theory (enable fn-xpy-expiredp)
                  :use ((:instance fn-xpy-walk-is-spec (newer nil) (set nil))))))

; The context the reclaim reads (books/store-reclaim-pack.lisp): the rule's,
; with the set the policy of the configuration value V expires at NOW.
(defun fn-xpy-ctx (rule now s v fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-rclp-ctx-expiring rule now s
                        (fn-xpy-expired-set
                         (fn-cfg-quotas v) now
                         (fn-state-articles (fn-node-acceptance (fn-sn-node s)))
                         fn-arena)))

; -----------------------------------------------------------------------------
; The classes the verb reports and `status' prints under an expiry policy
;
; Every article is in exactly one class (`fn-xpy-classes-partition-the-
; articles'):
;   :reclaimed    its payload is a tombstone (reclaimed or expired earlier);
;   :signed       an authorship verdict needs its payload (STO-008);
;   :reclaimable  the retention rule releases it now;
;   :expired      the expiry policy releases it now (the rule would keep it);
;   :held         a holder keeps it;
;   :kept         neither the rule nor the policy releases it.

(defun fn-xpy-class-in (rule now h verdicts expired a fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((verdict (fn-xpy-standing-verdict rule now h verdicts expired a)))
    (cond ((fn-rcl-payload-tombstonep (fn-article-payload a) fn-arena) :reclaimed)
          ((fn-rcl-verdict-heldp (fn-article-msgid a) verdicts) :signed)
          ((equal verdict :reclaimable) :reclaimable)
          ((equal verdict :expired) :expired)
          ((fn-rcl-heldp verdict) :held)
          (t :kept))))

(defconst *fn-xpy-classes*
  '(:reclaimable :expired :held :reclaimed :signed :kept))

; The articles of class CLASS: the logical count, and the loop the host runs
; (tail recursive, one frame however long the history).
(defun fn-xpy-class-count-spec (class rule now h verdicts expired articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp articles)
      (+ (if (equal (fn-xpy-class-in rule now h verdicts expired (car articles) fn-arena)
                    class)
             1 0)
         (fn-xpy-class-count-spec class rule now h verdicts expired (cdr articles)
                                  fn-arena))
    0))

(defun fn-xpy-class-count (class rule now h verdicts expired articles acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard (natp acc)))
  (if (consp articles)
      (fn-xpy-class-count class rule now h verdicts expired (cdr articles)
                          (if (equal (fn-xpy-class-in rule now h verdicts expired
                                                      (car articles) fn-arena)
                                     class)
                              (+ 1 acc)
                            acc)
                          fn-arena)
    acc))

(local
 (defthm fn-xpy-class-count-is-spec
   (implies (acl2-numberp acc)
            (equal (fn-xpy-class-count class rule now h verdicts expired articles acc
                                       fn-arena)
                   (+ acc (fn-xpy-class-count-spec class rule now h verdicts expired
                                                   articles fn-arena))))
   :hints (("Goal" :in-theory (disable fn-xpy-class-in)))))

(defun fn-xpy-class-counts (rule now h verdicts expired articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (list (fn-xpy-class-count :reclaimable rule now h verdicts expired articles 0 fn-arena)
        (fn-xpy-class-count :expired rule now h verdicts expired articles 0 fn-arena)
        (fn-xpy-class-count :held rule now h verdicts expired articles 0 fn-arena)
        (fn-xpy-class-count :reclaimed rule now h verdicts expired articles 0 fn-arena)
        (fn-xpy-class-count :signed rule now h verdicts expired articles 0 fn-arena)
        (fn-xpy-class-count :kept rule now h verdicts expired articles 0 fn-arena)))

(defun fn-xpy-count-sum (counts)
  (declare (xargs :guard (true-listp counts)))
  (+ (nfix (nth 0 counts)) (nfix (nth 1 counts)) (nfix (nth 2 counts))
     (nfix (nth 3 counts)) (nfix (nth 4 counts)) (nfix (nth 5 counts))))

(local
 (defthm fn-xpy-class-in-is-a-class
   (member-equal (fn-xpy-class-in rule now h verdicts expired a fn-arena)
                 '(:reclaimable :expired :held :reclaimed :signed :kept))
   :hints (("Goal" :in-theory (disable fn-xpy-standing-verdict
                                       fn-rcl-payload-tombstonep)))))

(local
 (defthm fn-xpy-one-class
   (implies (member-equal x '(:reclaimable :expired :held :reclaimed :signed :kept))
            (equal (+ (if (equal x :reclaimable) 1 0) (if (equal x :expired) 1 0)
                      (if (equal x :held) 1 0) (if (equal x :reclaimed) 1 0)
                      (if (equal x :signed) 1 0) (if (equal x :kept) 1 0))
                   1))
   :rule-classes nil))

(local
 (defthm fn-xpy-class-count-specs-sum
   (equal (+ (fn-xpy-class-count-spec :reclaimable rule now h verdicts expired articles
                                      fn-arena)
             (fn-xpy-class-count-spec :expired rule now h verdicts expired articles
                                      fn-arena)
             (fn-xpy-class-count-spec :held rule now h verdicts expired articles
                                      fn-arena)
             (fn-xpy-class-count-spec :reclaimed rule now h verdicts expired articles
                                      fn-arena)
             (fn-xpy-class-count-spec :signed rule now h verdicts expired articles
                                      fn-arena)
             (fn-xpy-class-count-spec :kept rule now h verdicts expired articles
                                      fn-arena))
          (len articles))
   :hints (("Goal" :induct (len articles)
                   :in-theory (disable fn-xpy-class-in))
           ("Subgoal *1/1" :use ((:instance fn-xpy-one-class
                                            (x (fn-xpy-class-in rule now h verdicts expired
                                                                (car articles) fn-arena)))
                                 (:instance fn-xpy-class-in-is-a-class
                                            (a (car articles))))))))

;  KEYSTONE (every article in exactly one class).  The six counts sum to the
; number of stored articles.
(defthm fn-xpy-classes-partition-the-articles
  (equal (fn-xpy-count-sum (fn-xpy-class-counts rule now h verdicts expired articles
                                                fn-arena))
         (len articles))
  :hints (("Goal" :in-theory (disable fn-xpy-class-count-spec fn-xpy-class-count
                                      fn-xpy-class-count-specs-sum)
                  :use fn-xpy-class-count-specs-sum)))

; The classes of the Store S at NOW under the configuration value V: its
; rule, its holders and verdicts, and the set its expiry policy expires.
(defun fn-xpy-store-classes (rule now s v fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((ctx (fn-xpy-ctx rule now s v fn-arena)))
    (fn-xpy-class-counts rule now (fn-rcl-nth 2 ctx) (fn-rcl-held-verdicts (fn-rcl-nth 3 ctx))
                         (fn-rcl-nth 5 ctx) (fn-rcl-nth 4 ctx) fn-arena)))

; The classes over a reclaim context (books/store-reclaim-pack.lisp's
; (RULE NOW HOLDERS VERDICTS ARTICLES EXPIRED)): what the verb reports before
; it rewrites (host/checkpoint-host.lisp fn-store-reclaim-ctx-classes).
(defun fn-xpy-ctx-classes (ctx fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-xpy-class-counts (fn-rcl-nth 0 ctx) (fn-rcl-nth 1 ctx) (fn-rcl-nth 2 ctx)
                       (fn-rcl-held-verdicts (fn-rcl-nth 3 ctx))
                       (fn-rcl-nth 5 ctx) (fn-rcl-nth 4 ctx) fn-arena))
