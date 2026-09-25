; fn: a tombstone-shaped payload is never admitted (D13, STO-014, PRF-088).
;
; A reclaimed article's payload is a tombstone (books/reclaim-tombstone):
; NUL "FN-RCL1" and fixed fields.  The Store reads a payload that satisfies
; `fn-rcl-tombstonep' as "reclaimed" (430/423, the counts, the D25 digest
; comparison).  If a peer or a poster could submit such octets as an
; article, the Store would hold a live article that every reader and every
; count takes for a reclaimed one.  This book proves that cannot happen at
; the served ingresses: every one reaches the Store prepare only through
; `fn-pa-carrier-form' (books/peer-authored-accept), which the host calls as
; `fn-owner-peer-carrier-form' (host/owner-host.lisp) at
; host/native/owner.lisp `fnn-owner-attempt-transit' (the `form' binding,
; before any Store call; POST, IHAVE, TAKETHIS, peer and BP transit, and
; bound submissions all go through it), and it refuses a tombstone with
; (:refused :article), because an octet string whose first octet is NUL is
; not an article: the first header line's field name would open with NUL,
; which is not ftext (RFC 5536 section 3.2.1 via books/article
; `fn-article-ftextp').
;
; The same fact closes the index half of reclamation: a tombstone
; contributes nothing to the statement index any open re-derives
; (`fn-rcl-tombstone-contributes-nothing').
;
; Not covered: the developer image's `store post' (host/native/io.lisp
; `fnn-command-post'), which prepares a raw payload file with no article
; check; it is not a served ingress and is not in the release image.
;
; Keystone: `fn-rcl-tombstone-refused-at-carrier-form'.
(in-package "ACL2")
(include-book "reclaim-tombstone")
(include-book "peer-authored-accept")
(include-book "stx-lace")

(local
 (defthm fn-rca-car-revappend
   (implies (consp x)
            (equal (car (revappend x acc)) (car (last x))))))

(local
 (defthm fn-rca-car-append
   (equal (car (append a b)) (if (consp a) (car a) (car b)))))

(local
 (defthm fn-rca-consp-rev
   (equal (consp (rev x)) (consp x))
   :hints (("Goal" :in-theory (enable rev)))))

(local
 (defthm fn-rca-car-rev
   (implies (consp x)
            (equal (car (rev x)) (car (last x))))
   :hints (("Goal" :in-theory (enable rev)))))

; The line reader keeps the octets it has consumed: once it holds any, the
; line it returns opens with the first of them.
(local
 (defthm fn-rca-next-line-aux-first
   (implies (and (consp line-rev)
                 (fn-article-line-okp (fn-article-next-line-aux octets line-rev left)))
            (equal (car (fn-article-line-value
                         (fn-article-next-line-aux octets line-rev left)))
                   (car (last line-rev))))))

(local
 (defthm fn-rca-split-colon-aux-first
   (implies (and (consp name-rev)
                 (fn-article-line-okp (fn-article-split-colon-aux line name-rev)))
            (equal (car (fn-article-line-value
                         (fn-article-split-colon-aux line name-rev)))
                   (car (last name-rev))))))

(defthm fn-rca-nul-line-is-no-field
  ; A header line that opens with NUL is not a field.
  (implies (equal (car line) 0)
           (not (fn-article-line-okp (fn-article-new-field line))))
  :hints (("Goal" :in-theory (enable fn-article-namep fn-article-ftext-listp)
           :expand ((fn-article-split-colon-aux line nil))
           :use ((:instance fn-rca-split-colon-aux-first
                            (line (cdr line)) (name-rev (list (car line))))))))

(local
 (defthm fn-rca-result-okp-is-line-okp
   (equal (fn-article-result-okp x) (fn-article-line-okp x))
   :hints (("Goal" :in-theory (enable fn-article-result-okp fn-article-line-okp)))))

(defthm fn-rca-nul-line-first
  ; The first line of an octet string that opens with NUL opens with NUL.
  (implies (and (equal (car octets) 0)
                (fn-article-line-okp (fn-article-next-line octets)))
           (equal (car (fn-article-line-value (fn-article-next-line octets))) 0))
  :hints (("Goal" :in-theory (enable fn-article-next-line)
           :expand ((:free (n) (fn-article-next-line-aux octets nil n)))
           :use ((:instance fn-rca-next-line-aux-first
                            (octets (cdr octets)) (line-rev '(0))
                            (left (1- *fn-article-max-line-octets*)))))))

(defthm fn-rca-nul-first-octet-is-not-an-article
  ; An octet string that opens with NUL does not parse as an article.
  (implies (equal (car octets) 0)
           (not (fn-article-result-okp (fn-article-parse octets))))
  :hints (("Goal" :in-theory (e/d (fn-article-parse)
                                  (fn-article-new-field fn-article-next-line
                                   fn-article-line-okp fn-article-line-value
                                   fn-article-line-rest fn-article-result-okp))
           :expand ((:free (n) (fn-article-parse-lines octets n 0 nil nil nil)))
           :use fn-rca-nul-line-first)))

(local (in-theory (disable fn-rca-result-okp-is-line-okp)))

(defthm fn-rcl-tombstone-opens-with-nul
  (implies (fn-rcl-tombstonep payload)
           (equal (car payload) 0))
  :hints (("Goal" :in-theory (enable fn-rcl-tombstonep fn-rcl-prefixp))))

(defthm fn-rcl-tombstone-does-not-parse
  (implies (fn-rcl-tombstonep payload)
           (not (fn-article-result-okp (fn-article-parse payload))))
  :hints (("Goal" :in-theory (disable fn-article-result-okp fn-article-parse
                                      fn-rcl-tombstonep)
           :use (fn-rcl-tombstone-opens-with-nul
                 (:instance fn-rca-nul-first-octet-is-not-an-article
                            (octets payload))))))

;  KEYSTONE.  The function every served ingress calls before the Store
; prepare refuses a tombstone-shaped payload as not an article.
(defthm fn-rcl-tombstone-refused-at-carrier-form
  (implies (fn-rcl-tombstonep received)
           (equal (fn-pa-carrier-form received) '(:refused :article)))
  :hints (("Goal" :in-theory (e/d (fn-pa-carrier-form fn-pa-carrier-kind)
                                  (fn-rcl-tombstonep fn-article-parse
                                   fn-article-result-okp)))))

; A tombstone contributes nothing to the statement index any open derives.
(defthm fn-rcl-tombstone-contributes-nothing
  (implies (fn-rcl-tombstonep payload)
           (equal (fn-stx-delta payload keyring) nil))
  :hints (("Goal" :in-theory (e/d ((:d fn-stx-delta) (:d fn-stx-parse))
                                  (fn-rcl-tombstonep fn-article-parse
                                   fn-article-result-okp)))))
