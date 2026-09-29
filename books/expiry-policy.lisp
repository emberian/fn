; fn: the operator's per-group expiry policy, as configuration (Q14; RFC 5536
; section 3.2.5; D03, D13).
;
; D03 keeps a post until an explicit, authorized release.  A per-group expiry
; policy is such a release, set by the operator for a group (or for every
; group without its own), beside the store-wide retention rule
; (books/reclaim-rule.lisp).  The policy of a group is four numbers:
;
;   keep     KEEP days: no article leaves before KEEP days, whatever its
;            Expires: header asks (INN expire.ctl's `keep')
;   default  DEFAULT days: an article without a usable Expires: header
;            leaves DEFAULT days after it was accepted (INN's `default')
;   purge    PURGE days: no article stays longer than PURGE days, whatever
;            its Expires: header asks (INN's `purge')
;   octets   the group's size window: the newest articles of the group whose
;            live payload octets sum to at most OCTETS stay; an older one
;            leaves (fn's own; no INN equivalent)
;
; A number of 0 is "not set".  A group whose own rows are all unset takes the
; default policy (the rows named "*"); a store with no rows expires nothing
; (D03's default: `fn-xpy-config-policy-without-rows-keeps-forever').
;
; The policy is configuration QUOTA rows (books/config `:set-quota', delta
; code 4): scope `expire-keep', `expire-default', `expire-purge',
; `expire-octets' (the low 32 bits) or `expire-octets-hi' (the high 32 bits),
; and the group's name (or "*") as the row's second key.  A quota row is
; keyed on (scope, name) by `fn-cfg-row-upsert', so setting a group's policy
; twice replaces it.  No other reader of the configuration names these
; scopes, no store format changes, and every image admits the delta (a quota
; delta has no admission condition of its own).  The octets of a size window
; are two uint32 rows, so a window is any number below 2^64 (D27: the codec's
; uint32 is not a ceiling on the operator's number).
;
; Days are whole days of 86,400 seconds of the acceptance stamp's clock
; (books/records-stamp.lisp); a DAYS value is a row's uint32.
(in-package "ACL2")
(include-book "config")
(local (include-book "arithmetic-5/top" :dir :system))

(defconst *fn-xpy-keep-scope* "expire-keep")
(defconst *fn-xpy-default-scope* "expire-default")
(defconst *fn-xpy-purge-scope* "expire-purge")
(defconst *fn-xpy-octets-scope* "expire-octets")
(defconst *fn-xpy-octets-hi-scope* "expire-octets-hi")
(defconst *fn-xpy-every-group* "*")
(defconst *fn-xpy-seconds-per-day* 86400)
(defconst *fn-xpy-word* 4294967296) ; 2^32

; -----------------------------------------------------------------------------
; The rows

; The first quota row keyed (SCOPE, NAME), as `fn-cfg-row-upsert' keys it.
(defun fn-xpy-row (rows scope name)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (equal (fn-cfg-row-a (car rows)) scope)
               (equal (fn-cfg-row-b (car rows)) name))
          (car rows)
        (fn-xpy-row (cdr rows) scope name))
    nil))

; The row's number, or 0 when there is no row (0 is also "not set").
(defun fn-xpy-row-n (rows scope name)
  (declare (xargs :guard t))
  (nfix (fn-cfg-row-n (fn-xpy-row rows scope name))))

; A policy: (keep default purge octets), each a natural, 0 not set.
(defun fn-xpy-policy (keep default purge octets)
  (declare (xargs :guard t))
  (list (nfix keep) (nfix default) (nfix purge) (nfix octets)))

(defun fn-xpy-policy-keep (p) (declare (xargs :guard t)) (nfix (fn-cfg-ag-car p)))
(defun fn-xpy-policy-default (p)
  (declare (xargs :guard t))
  (nfix (fn-cfg-ag-car (fn-cfg-ag-cdr p))))
(defun fn-xpy-policy-purge (p)
  (declare (xargs :guard t))
  (nfix (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr p)))))
(defun fn-xpy-policy-octets (p)
  (declare (xargs :guard t))
  (nfix (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr p))))))

(defthm fn-xpy-policy-fields
  (let ((p (fn-xpy-policy keep default purge octets)))
    (and (equal (fn-xpy-policy-keep p) (nfix keep))
         (equal (fn-xpy-policy-default p) (nfix default))
         (equal (fn-xpy-policy-purge p) (nfix purge))
         (equal (fn-xpy-policy-octets p) (nfix octets))))
  :hints (("Goal" :in-theory (enable fn-cfg-ag-car fn-cfg-ag-cdr))))

(in-theory (disable fn-xpy-policy fn-xpy-policy-keep fn-xpy-policy-default
                    fn-xpy-policy-purge fn-xpy-policy-octets))

; Whether the policy expires anything by age, and by size.
(defun fn-xpy-agep (p)
  (declare (xargs :guard t))
  (or (posp (fn-xpy-policy-keep p))
      (posp (fn-xpy-policy-default p))
      (posp (fn-xpy-policy-purge p))))

(defun fn-xpy-sizep (p)
  (declare (xargs :guard t))
  (posp (fn-xpy-policy-octets p)))

(defun fn-xpy-setp (p)
  (declare (xargs :guard t))
  (or (fn-xpy-agep p) (fn-xpy-sizep p)))

(defconst *fn-xpy-keep-forever* (fn-xpy-policy 0 0 0 0))

; NAME's own rows, read as a policy.
(defun fn-xpy-rows-policy (rows name)
  (declare (xargs :guard t))
  (fn-xpy-policy (fn-xpy-row-n rows *fn-xpy-keep-scope* name)
                 (fn-xpy-row-n rows *fn-xpy-default-scope* name)
                 (fn-xpy-row-n rows *fn-xpy-purge-scope* name)
                 (+ (* *fn-xpy-word* (fn-xpy-row-n rows *fn-xpy-octets-hi-scope* name))
                    (fn-xpy-row-n rows *fn-xpy-octets-scope* name))))

; The policy GROUP is under in the quota rows Q (the configuration value's
; `fn-cfg-quotas'): its own rows when any is set, else the rows of "*".
(defun fn-xpy-group-policy-of (q group)
  (declare (xargs :guard t))
  (let ((own (fn-xpy-rows-policy q group)))
    (if (fn-xpy-setp own)
        own
      (fn-xpy-rows-policy q *fn-xpy-every-group*))))

(defun fn-xpy-group-policy (v group)
  (declare (xargs :guard t))
  (fn-xpy-group-policy-of (fn-cfg-quotas v) group))

; D03's default is preserved: without any expiry row every group keeps
; forever.
(defthm fn-xpy-group-policy-without-rows-keeps-forever
  (implies (and (null (fn-xpy-row (fn-cfg-quotas v) *fn-xpy-keep-scope* group))
                (null (fn-xpy-row (fn-cfg-quotas v) *fn-xpy-default-scope* group))
                (null (fn-xpy-row (fn-cfg-quotas v) *fn-xpy-purge-scope* group))
                (null (fn-xpy-row (fn-cfg-quotas v) *fn-xpy-octets-scope* group))
                (null (fn-xpy-row (fn-cfg-quotas v) *fn-xpy-octets-hi-scope* group))
                (null (fn-xpy-row (fn-cfg-quotas v) *fn-xpy-keep-scope* "*"))
                (null (fn-xpy-row (fn-cfg-quotas v) *fn-xpy-default-scope* "*"))
                (null (fn-xpy-row (fn-cfg-quotas v) *fn-xpy-purge-scope* "*"))
                (null (fn-xpy-row (fn-cfg-quotas v) *fn-xpy-octets-scope* "*"))
                (null (fn-xpy-row (fn-cfg-quotas v) *fn-xpy-octets-hi-scope* "*")))
           (equal (fn-xpy-group-policy v group) *fn-xpy-keep-forever*))
  :hints (("Goal" :in-theory (enable fn-xpy-policy fn-cfg-row-n fn-cfg-ag-car
                                     fn-cfg-ag-cdr))))

; -----------------------------------------------------------------------------
; The operator's words and the deltas they stage

; A policy the operator may set: days within a row's uint32, keep at most
; default and default at most purge where both are set (INN's order), the
; octets below 2^64.
(defun fn-xpy-days-okp (n)
  (declare (xargs :guard t))
  (and (natp n) (fn-record-uint32p n)))

(defun fn-xpy-orderedp (a b)
  (declare (xargs :guard t))
  (or (not (posp a)) (not (posp b)) (<= a b)))

(defun fn-xpy-policy-okp (p)
  (declare (xargs :guard t))
  (let ((k (fn-xpy-policy-keep p)) (d (fn-xpy-policy-default p))
        (u (fn-xpy-policy-purge p)) (o (fn-xpy-policy-octets p)))
    (and (fn-xpy-days-okp k) (fn-xpy-days-okp d) (fn-xpy-days-okp u)
         (< o (* *fn-xpy-word* *fn-xpy-word*))
         (fn-xpy-orderedp k d) (fn-xpy-orderedp d u) (fn-xpy-orderedp k u))))

; The target of `expire set': a group name the record codec admits, or "*".
(defun fn-xpy-targetp (name)
  (declare (xargs :guard t))
  (or (equal name *fn-xpy-every-group*)
      (fn-record-group-namep name)))

; The five quota deltas one `expire set' (or `expire clear': the policy of
; all zeros) stages: every row of the target, always, so no row survives from
; an earlier policy into a later one.
(defun fn-xpy-deltas (name p)
  (declare (xargs :guard t))
  (let ((o (fn-xpy-policy-octets p)))
    (list (fn-cfg-set-quota *fn-xpy-keep-scope* name (fn-xpy-policy-keep p))
          (fn-cfg-set-quota *fn-xpy-default-scope* name (fn-xpy-policy-default p))
          (fn-cfg-set-quota *fn-xpy-purge-scope* name (fn-xpy-policy-purge p))
          (fn-cfg-set-quota *fn-xpy-octets-scope* name (mod o *fn-xpy-word*))
          (fn-cfg-set-quota *fn-xpy-octets-hi-scope* name (floor o *fn-xpy-word*)))))

; The operator's words after the target of `retention expire TARGET ...':
; `clear', or pairs `keep DAYS', `default DAYS', `purge DAYS', `octets N' in
; any order, each at most once, the numbers decimal (no sign, no leading
; zero).  The policy, or nil when the words are not one (refused by name).
(defun fn-xpy-digit-charsp (chars)
  (declare (xargs :guard t))
  (if (consp chars)
      (and (characterp (car chars))
           (char<= #\0 (car chars)) (char<= (car chars) #\9)
           (fn-xpy-digit-charsp (cdr chars)))
    t))

(defun fn-xpy-chars-value (chars acc)
  (declare (xargs :guard (and (fn-xpy-digit-charsp chars) (natp acc))))
  (if (consp chars)
      (fn-xpy-chars-value (cdr chars)
                          (+ (* 10 acc) (- (char-code (car chars)) 48)))
    acc))

(defun fn-xpy-decimal (text)
  (declare (xargs :guard t))
  (if (stringp text)
      (let ((chars (coerce text 'list)))
        (if (and (consp chars) (fn-xpy-digit-charsp chars)
                 (not (and (consp (cdr chars)) (equal (car chars) #\0))))
            (fn-xpy-chars-value chars 0)
          nil))
    nil))

(defun fn-xpy-words-fields (words keep default purge octets)
  ; each field nil until its word is seen
  (declare (xargs :guard t :measure (len words)))
  (if (consp words)
      (let ((n (and (consp (cdr words)) (fn-xpy-decimal (cadr words)))))
        (cond ((null n) nil)
              ((and (equal (car words) "keep") (null keep))
               (fn-xpy-words-fields (cddr words) n default purge octets))
              ((and (equal (car words) "default") (null default))
               (fn-xpy-words-fields (cddr words) keep n purge octets))
              ((and (equal (car words) "purge") (null purge))
               (fn-xpy-words-fields (cddr words) keep default n octets))
              ((and (equal (car words) "octets") (null octets))
               (fn-xpy-words-fields (cddr words) keep default purge n))
              (t nil)))
    (fn-xpy-policy keep default purge octets)))

(defun fn-xpy-words-policy (words)
  (declare (xargs :guard t))
  (let ((p (if (equal words '("clear"))
               *fn-xpy-keep-forever*
             (and (consp words)
                  (fn-xpy-words-fields words nil nil nil nil)))))
    (if (and p (fn-xpy-policy-okp p)) p nil)))

(defthm fn-xpy-words-policy-is-an-admitted-policy
  (implies (fn-xpy-words-policy words)
           (fn-xpy-policy-okp (fn-xpy-words-policy words))))

; -----------------------------------------------------------------------------
; Lookup after upsert.

(local
 (defthm fn-xpy-row-of-upsert-same
   (implies (and (equal (fn-cfg-row-a row) scope)
                 (equal (fn-cfg-row-b row) name))
            (equal (fn-xpy-row (fn-cfg-row-upsert rows row) scope name) row))
   :hints (("Goal" :induct (fn-cfg-row-upsert rows row)
            :in-theory (enable fn-cfg-row-upsert)))))

(local
 (defthm fn-xpy-row-of-upsert-other
   (implies (not (and (equal (fn-cfg-row-a row) scope)
                      (equal (fn-cfg-row-b row) name)))
            (equal (fn-xpy-row (fn-cfg-row-upsert rows row) scope name)
                   (fn-xpy-row rows scope name)))
   :hints (("Goal" :induct (fn-cfg-row-upsert rows row)
            :in-theory (enable fn-cfg-row-upsert)))))

(local
 (defthm fn-cfg-quotas-of-set-quota
   (equal (fn-cfg-quotas (fn-cfg-apply-delta v gen stamp
                                             (list :set-quota scope name n nil)))
          (fn-cfg-row-upsert (fn-cfg-quotas v) (fn-cfg-row-make scope name "" n)))
   :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-delta-kind fn-cfg-delta-a
                                      fn-cfg-delta-b fn-cfg-delta-n fn-cfg-delta-rows
                                      fn-cfg-ag-car fn-cfg-ag-cdr)))))

(local (in-theory (disable fn-cfg-apply-delta fn-cfg-set-quota fn-cfg-quotas
                           fn-cfg-row-upsert)))

(local
 (defthm fn-xpy-row-n-of-row-make
   (equal (nfix (fn-cfg-row-n (fn-cfg-row-make a b c n))) (nfix n))))

;  KEYSTONE.  The policy the operator set for a target is the policy every
; later reader of the configuration sees for it: staging `fn-xpy-deltas'
; through the ordinary configuration fold, on ANY prior value, and reading
; the target's own rows gives the policy.  Replay applies the same
; `fn-cfg-apply' (books/config `fn-cfg-apply-record'), so this is what the
; next open reads.  Other targets' rows are untouched
; (`fn-xpy-rows-policy-of-other-target-after-expire-set').
(local
 (defthm fn-xpy-octets-split
   (implies (natp o)
            (equal (+ (* 4294967296 (floor o 4294967296)) (mod o 4294967296)) o))
   :hints (("Goal" :in-theory (enable mod)))))

(defthm fn-xpy-rows-policy-after-expire-set
  (equal (fn-xpy-rows-policy
          (fn-cfg-quotas (fn-cfg-apply v gen stamp (fn-xpy-deltas name p)))
          name)
         (fn-xpy-policy (fn-xpy-policy-keep p) (fn-xpy-policy-default p)
                        (fn-xpy-policy-purge p) (fn-xpy-policy-octets p)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply fn-cfg-set-quota fn-cfg-delta-make)
                                  (floor mod)))))

(defthm fn-xpy-rows-policy-of-other-target-after-expire-set
  (implies (not (equal other name))
           (equal (fn-xpy-rows-policy
                   (fn-cfg-quotas (fn-cfg-apply v gen stamp (fn-xpy-deltas name p)))
                   other)
                  (fn-xpy-rows-policy (fn-cfg-quotas v) other)))
  :hints (("Goal" :in-theory (enable fn-cfg-apply fn-cfg-set-quota
                                     fn-cfg-delta-make))))

; The deltas are typed configuration deltas: five, each a quota delta the
; configuration admits.
(defthm fn-xpy-deltas-are-deltas
  (implies (and (fn-xpy-targetp name) (fn-xpy-policy-okp p))
           (and (fn-cfg-delta-listp (fn-xpy-deltas name p))
                (equal (len (fn-xpy-deltas name p)) 5)))
  :hints (("Goal" :use ((:instance fn-cfg-labelp-of-record-group-name (s name)))
                  :in-theory (e/d (fn-cfg-set-quota fn-cfg-deltap fn-cfg-delta-listp
                                   fn-record-uint32p)
                                  (fn-record-group-namep)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-cfg-labelp fn-cfg-set-quota fn-cfg-deltap
                                  fn-cfg-delta-listp fn-record-uint32p)
                                 (fn-record-group-namep))))))
