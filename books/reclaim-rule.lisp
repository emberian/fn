; fn: the operator's content-retention rule (D03, D13), as configuration.
;
; D03 keeps a post until an explicit, authorized release and never expires it
; on its own.  The 2026-09-25 decisions review reads D03 as the DEFAULT, not
; as a requirement of unlimited retention: an operator may authorize a rule
; under which content bytes are released.  This book owns that rule.
;
;   retention keep-forever             the default; nothing is reclaimable
;   retention released-by-all-holders  reclaimable once no holder remains
;   retention release-after DAYS       and, in addition, accepted DAYS ago
;
; The rule is not a new configuration mechanism.  It is two `:set-limit'
; rows of the typed configuration value (books/config), written by the
; ordinary reconfiguration record, replayed by the ordinary configuration
; fold and staged live by the ordinary owner path:
;
;   limit "retention"       0 keep-forever, 1 released-by-all-holders,
;                           2 release-after
;   limit "retention-days"  DAYS, read only under code 2
;
; Limits and not policies, because `fn-cfg-row-upsert' keys a row on its
; (a, b) pair: a policy row is keyed by its id, so setting the policy twice
; with two ids would leave both rows and the first would win.  A limit row's
; b is always "", so a second `retention set' replaces the first.
;
; A configuration that carries no retention row is keep-forever
; (`fn-rcl-config-rule-without-a-row-keeps-forever'), so every store written
; before this book behaves exactly as it did.  A row this book does not
; recognise (a code above 2, or release-after with no positive day count)
; is refused by name, and a refused rule makes nothing reclaimable.
(in-package "ACL2")
(include-book "config")

(defconst *fn-rcl-rule-slot* "retention")
(defconst *fn-rcl-days-slot* "retention-days")
(defconst *fn-rcl-seconds-per-day* 86400)

; The first limit row keyed exactly as `:set-limit' keys it: slot and "".
(defun fn-rcl-limit-row (rows slot)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (equal (fn-cfg-row-a (car rows)) slot)
               (equal (fn-cfg-row-b (car rows)) ""))
          (car rows)
        (fn-rcl-limit-row (cdr rows) slot))
    nil))

(defun fn-rcl-rule-of-codes (code days)
  (declare (xargs :guard t))
  (cond ((equal code 0) '(:keep-forever))
        ((equal code 1) '(:released-by-all-holders))
        ((equal code 2)
         (if (and (posp days) (fn-record-uint32p days))
             (list :release-after days)
           '(:refused :retention-days)))
        (t '(:refused :retention-code))))

; The rule a configuration value carries.  Reads two rows; never the store.
(defun fn-rcl-config-rule (v)
  (declare (xargs :guard t))
  (let ((rule-row (fn-rcl-limit-row (fn-cfg-limits v) *fn-rcl-rule-slot*))
        (days-row (fn-rcl-limit-row (fn-cfg-limits v) *fn-rcl-days-slot*)))
    (if (null rule-row)
        '(:keep-forever)
      (fn-rcl-rule-of-codes (fn-cfg-row-n rule-row)
                            (and days-row (fn-cfg-row-n days-row))))))

(defun fn-rcl-rulep (rule)
  (declare (xargs :guard t))
  (or (equal rule '(:keep-forever))
      (equal rule '(:released-by-all-holders))
      (and (consp rule)
           (consp (cdr rule))
           (equal rule (list :release-after (cadr rule)))
           (posp (cadr rule))
           (fn-record-uint32p (cadr rule)))))

; The operator's words.  WORD is the second argument of `retention set';
; DAYS is the decimal the plan parsed, or nil.  Returns the rule or nil.
(defun fn-rcl-rule-of-words (word days)
  (declare (xargs :guard t))
  (cond ((and (equal word "keep-forever") (null days)) '(:keep-forever))
        ((and (equal word "released-by-all-holders") (null days))
         '(:released-by-all-holders))
        ((and (equal word "release-after") (posp days) (fn-record-uint32p days))
         (list :release-after days))
        (t nil)))

; The deltas one `retention set' stages: both rows, always, so the days row
; never survives from an earlier release-after into a later rule.
(defun fn-rcl-rule-deltas (rule)
  (declare (xargs :guard t))
  (cond ((equal rule '(:keep-forever))
         (list (fn-cfg-set-limit *fn-rcl-rule-slot* 0)
               (fn-cfg-set-limit *fn-rcl-days-slot* 0)))
        ((equal rule '(:released-by-all-holders))
         (list (fn-cfg-set-limit *fn-rcl-rule-slot* 1)
               (fn-cfg-set-limit *fn-rcl-days-slot* 0)))
        ((fn-rcl-rulep rule)
         (list (fn-cfg-set-limit *fn-rcl-rule-slot* 2)
               (fn-cfg-set-limit *fn-rcl-days-slot* (cadr rule))))
        (t nil)))

; The words the status line prints for a rule.
(defun fn-rcl-rule-word (rule)
  (declare (xargs :guard t))
  (cond ((equal rule '(:keep-forever)) "keep-forever")
        ((equal rule '(:released-by-all-holders)) "released-by-all-holders")
        ((and (consp rule) (equal (car rule) :release-after)) "release-after")
        (t "refused")))

; -----------------------------------------------------------------------------
; Lookup after upsert.

(local
 (defthm fn-rcl-limit-row-of-upsert-same
   (implies (and (equal (fn-cfg-row-a row) slot)
                 (equal (fn-cfg-row-b row) ""))
            (equal (fn-rcl-limit-row (fn-cfg-row-upsert rows row) slot) row))
   :hints (("Goal" :induct (fn-cfg-row-upsert rows row)
            :in-theory (enable fn-cfg-row-upsert)))))

(local
 (defthm fn-rcl-limit-row-of-upsert-other
   (implies (not (equal (fn-cfg-row-a row) slot))
            (equal (fn-rcl-limit-row (fn-cfg-row-upsert rows row) slot)
                   (fn-rcl-limit-row rows slot)))
   :hints (("Goal" :induct (fn-cfg-row-upsert rows row)
            :in-theory (enable fn-cfg-row-upsert)))))

(local
 (defthm fn-cfg-limits-of-set-limit
   (equal (fn-cfg-limits (fn-cfg-apply-delta v gen stamp
                                             (list :set-limit slot "" n nil)))
          (fn-cfg-row-upsert (fn-cfg-limits v) (fn-cfg-row-make slot "" "" n)))
   :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-delta-kind fn-cfg-delta-a fn-cfg-delta-b fn-cfg-delta-n fn-cfg-delta-rows fn-cfg-ag-car fn-cfg-ag-cdr)))))

(local (in-theory (disable fn-cfg-apply-delta fn-cfg-set-limit fn-cfg-limits
                           fn-cfg-row-upsert)))

;  KEYSTONE.  The rule the operator set is the rule every later reader of
; the configuration sees: staging `fn-rcl-rule-deltas' through the ordinary
; configuration fold, on ANY prior value, and reading the rule back gives the
; rule.  Replay applies the same `fn-cfg-apply' (books/config
; `fn-cfg-apply-record'), so this is also what the next open reads.
(defthm fn-rcl-config-rule-after-retention-set
  (implies (fn-rcl-rulep rule)
           (equal (fn-rcl-config-rule
                   (fn-cfg-apply v gen stamp (fn-rcl-rule-deltas rule)))
                  rule))
  :hints (("Goal" :in-theory (enable fn-cfg-apply fn-cfg-set-limit
                                     fn-cfg-delta-make))))

; D03's default is preserved: a value without a retention row keeps forever.
(defthm fn-rcl-config-rule-without-a-row-keeps-forever
  (implies (null (fn-rcl-limit-row (fn-cfg-limits v) *fn-rcl-rule-slot*))
           (equal (fn-rcl-config-rule v) '(:keep-forever))))

; The words and the rule agree: every rule the plan admits is a rule, and
; stages deltas the configuration admits.
(defthm fn-rcl-rule-of-words-is-a-rule
  (implies (fn-rcl-rule-of-words word days)
           (fn-rcl-rulep (fn-rcl-rule-of-words word days))))

(defthm fn-rcl-rule-deltas-are-deltas
  (implies (fn-rcl-rulep rule)
           (and (fn-cfg-delta-listp (fn-rcl-rule-deltas rule))
                (equal (len (fn-rcl-rule-deltas rule)) 2)))
  :hints (("Goal" :in-theory (enable fn-cfg-set-limit fn-cfg-deltap
                                     fn-cfg-delta-listp fn-cfg-labelp
                                     fn-record-uint32p))))
