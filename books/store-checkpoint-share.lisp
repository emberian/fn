; fn: one object per string content in a decoded state checkpoint (lane
; checkpoint-arena-3, 2026-09-27).
;
; The tables reader (books/store-checkpoint-tables-reader.lisp) makes a new
; string for every string it decodes.  The four R tables (the cpr, identity,
; consumer and topic indexes) repeat strings the E rows hold -- a record's
; Message-ID, its obligation and subject identities, its group name -- and
; the full replay builds those indexes from the rows' own strings, so an
; open from a checkpoint kept nine more strings per record than the replay
; (planning/evidence/checkpoint-arena-3-2026-09-27.md: the census by
; content at 10,000 records: the same 48,431 contents, 90,007 more objects).
;
; `fn-sshr-share' walks the decoded tables once with a local EQUAL hash
; table and answers the same value with each string content held by ONE
; object (the first seen).  KEYSTONE `fn-sshr-share-is-identity': it is
; the identity, for every value; so every theorem about the loaded tables
; holds of what it returns.  Host caller: books/store-checkpoint-arena-load
; `fn-scka-finish' (host/store-node-host.lisp fn-store-sco-decode-finish).
;
; Work is linear in the tables' conses and the stack depth is the value's
; nesting depth, not a list's length: a list's spine is walked by a loop
; that rebuilds it (`fn-sshr-list'), its elements by recursion.

(in-package "ACL2")

(defstobj fn-strshare (fn-strshare-tab :type (hash-table equal)))

; The table's logical model is an alist; the walk keeps every binding a
; string bound to itself.
(defun fn-sshr-invp (tab)
  (declare (xargs :guard t))
  (if (consp tab)
      (and (or (not (consp (car tab)))
               (equal (caar tab) (cdar tab)))
           (fn-sshr-invp (cdr tab)))
    t))

(defthm fn-sshr-invp-lookup
  (implies (fn-sshr-invp tab)
           (equal (cdr (hons-assoc-equal k tab))
                  (if (consp (hons-assoc-equal k tab)) k nil))))

(defthm fn-sshr-tab-of-put
  (equal (car (fn-strshare-tab-put k v fn-strshare))
         (cons (cons k v) (car fn-strshare))))

(defthm fn-sshr-tab-get-is-lookup
  (equal (fn-strshare-tab-get k fn-strshare)
         (cdr (hons-assoc-equal k (car fn-strshare)))))

(in-theory (disable fn-strshare-tab-put fn-strshare-tab-get))

; One string: the object already held for its content, or the string itself
; (then held).
(defun fn-sshr-string (x fn-strshare)
  (declare (xargs :stobjs fn-strshare :guard (stringp x)))
  (let ((hit (fn-strshare-tab-get x fn-strshare)))
    (if (stringp hit)
        (mv hit fn-strshare)
      (let ((fn-strshare (fn-strshare-tab-put x x fn-strshare)))
        (mv x fn-strshare)))))

(defthm fn-sshr-string-is-identity
  (implies (fn-sshr-invp (car fn-strshare))
           (and (equal (mv-nth 0 (fn-sshr-string x fn-strshare)) x)
                (fn-sshr-invp (car (mv-nth 1 (fn-sshr-string x fn-strshare))))))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
    (implies (fn-sshr-invp (car fn-strshare))
             (and (equal (car (fn-sshr-string x fn-strshare)) x)
                  (fn-sshr-invp (car (cadr (fn-sshr-string x fn-strshare))))))
    :hints (("Goal" :in-theory (enable mv-nth))))))

(in-theory (disable fn-sshr-string))

;; FLAG nil: X walked.  FLAG t: the spine of X, each element walked, onto
;; ACC (reversed), the final cdr walked last, the whole reversed back.
(defun fn-sshr-go (flag x acc fn-strshare)
  (declare (xargs :stobjs fn-strshare :guard (true-listp acc)
                  :measure (+ (* 2 (acl2-count x)) (if flag 0 1))))
  (if flag
      (if (consp x)
          (mv-let (a fn-strshare)
            (fn-sshr-go nil (car x) nil fn-strshare)
            (fn-sshr-go t (cdr x) (cons a acc) fn-strshare))
        (mv-let (tl fn-strshare)
          (if (stringp x) (fn-sshr-string x fn-strshare) (mv x fn-strshare))
          (mv (revappend acc tl) fn-strshare)))
    (cond ((stringp x) (fn-sshr-string x fn-strshare))
          ((consp x) (fn-sshr-go t x nil fn-strshare))
          (t (mv x fn-strshare)))))

(defthm fn-sshr-go-is-identity
  (implies (fn-sshr-invp (car fn-strshare))
           (and (equal (mv-nth 0 (fn-sshr-go flag x acc fn-strshare))
                       (if flag (revappend acc x) x))
                (fn-sshr-invp (car (mv-nth 1 (fn-sshr-go flag x acc fn-strshare))))))
  :hints (("Goal" :induct (fn-sshr-go flag x acc fn-strshare))))

(defun fn-sshr-share (x)
  (declare (xargs :guard t))
  (with-local-stobj fn-strshare
    (mv-let (y fn-strshare)
      (fn-sshr-go nil x nil fn-strshare)
      y)))

; KEYSTONE: sharing is the identity.
(defthm fn-sshr-share-is-identity
  (equal (fn-sshr-share x) x))

(in-theory (disable fn-sshr-share))
