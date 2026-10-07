; What `:pages t' of `def-representation' generates (books/def-representation.lisp
; `rep-pages-events'; the library is books/def-representation-pages.lisp,
; proved once over a schema variable), checked on a test instance:
;
; 1. The generated names, the unchanged `fn-generated' row for an instance
;    without :pages and the marked row for one with it.
; 2. Executed witnesses: the words of two rows, the round trip, and the dirty
;    set of an append, which does not grow with the sequence.
; 3. Teeth.  Each is a must-fail AND a concrete witness that its claim is
;    false for the right reason, so a stale or untranslatable body cannot
;    pass for a tooth:
;    a. an append-dirty that drops the pages a row's octets spill into;
;    b. a bound of one page;
;    c. a bound with a term in the length of the sequence is weaker, not a
;       tooth: the real bound is checked to hold at every length tried.
; 4. The expansion-time refusals.

(in-package "ACL2")
(include-book "../../books/def-representation-pages")
(include-book "../../books/def-representation")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(def-representation drt-pg (id :u64) (msgid :octets) (flag :bool) :pages t)
(def-representation drt-nopg (id :u64) (msgid :octets) (flag :bool))

; -----------------------------------------------------------------------------
; 1. Names and rows.

(assert-event (and (function-symbolp 'drt-pg-pages-of (w state))
                   (function-symbolp 'drt-pg-of-pages (w state))
                   (function-symbolp 'drt-pg-append-dirty (w state))
                   (function-symbolp 'drt-pg-rowp (w state))
                   (function-symbolp 'drt-pg-pool-pages-of-row (w state))
                   (not (function-symbolp 'drt-nopg-pages-of (w state)))))

(assert-event (equal (cdr (assoc-eq 'drt-nopg (table-alist 'fn-generated (w state))))
                     '(:def-representation :scalar nil :generic nil :implementation drt-nopg :invariant nil
                       :trees nil :write-once nil :paged t)))

(assert-event (equal (cdr (assoc-eq 'drt-pg (table-alist 'fn-generated (w state))))
                     '(:def-representation :scalar nil :generic nil :implementation drt-pg :invariant nil
                       :trees nil :write-once nil :paged t :pages t)))

; -----------------------------------------------------------------------------
; 2. Witnesses.

(defconst *drt-a2* '((7 (104 105) t) (9 (1 2 3 4 5 6 7 8 9) nil)))

; Tag 1; id; octet count, packed octets (little-endian, eight a word, zero
; padded); the bool.  The second row's nine octets take two words.
(assert-event
 (equal (adt-tp-seq-words *drt-pg-schema* *drt-a2*)
        (list 1 7 2 (+ 104 (* 256 105)) 1
              1 9 9 (+ 1 (* 256 2) (* 65536 3) (* 16777216 4) (* 4294967296 5)
                       (* 1099511627776 6) (* 281474976710656 7) (* 72057594037927936 8))
              9 0)))

(assert-event (equal (len (drt-pg-pages-of *drt-a2*)) 1))
(assert-event (equal (len (car (drt-pg-pages-of *drt-a2*))) 2048))
(assert-event (equal (drt-pg-of-pages (drt-pg-pages-of *drt-a2*)) *drt-a2*))
(assert-event (equal (drt-pg-of-pages nil) nil))

(defun drt-narrow (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil (cons (list n '(1 2 3) t) (drt-narrow (1- n)))))

; a row whose octets cross a pool page: 20000 octets, 2503 words
(defconst *drt-wide* (list 5 (make-list 20000 :initial-element 7) nil))

(assert-event (equal (adt-tp-npages (len (adt-tp-rw *drt-pg-schema* *drt-wide*))) 2))
(assert-event (equal (drt-pg-pool-pages-of-row *drt-wide*) 2))

; The dirty set of an append is one page for a narrow row after any prefix
; (the partial last page), and the wide row's two pages at most three, at
; every length tried; the applied dirty set is the appended sequence's image.
(assert-event
 (and (equal (len (drt-pg-append-dirty nil '(1 (2) t))) 1)
      (equal (len (drt-pg-append-dirty (drt-narrow 5) '(1 (2) t))) 1)
      (equal (len (drt-pg-append-dirty (drt-narrow 300) '(1 (2) t))) 1)
      (equal (len (drt-pg-append-dirty (drt-narrow 700) '(1 (2) t))) 1)
      (<= (len (drt-pg-append-dirty nil *drt-wide*)) 3)
      (<= (len (drt-pg-append-dirty (drt-narrow 300) *drt-wide*)) 3)
      (<= (len (drt-pg-append-dirty (drt-narrow 700) *drt-wide*)) 3)))

(assert-event
 (and (equal (pgs-apply-dirty (drt-pg-pages-of (drt-narrow 700))
                              (drt-pg-append-dirty (drt-narrow 700) *drt-wide*))
             (drt-pg-pages-of (append (drt-narrow 700) (list *drt-wide*))))
      (equal (drt-pg-of-pages (drt-pg-pages-of (append (drt-narrow 700) (list *drt-wide*))))
             (append (drt-narrow 700) (list *drt-wide*)))))

; 700 narrow rows are 3500 words, 1452 of them on page 1: an append rewrites page 1 only.
(assert-event (equal (strip-cars (drt-pg-append-dirty (drt-narrow 700) '(1 (2) t))) '(1)))

; -----------------------------------------------------------------------------
; 3a. An append-dirty that drops the pages the row's octets spill into.

(defun drt-pg-bad-dirty (a x)
  (declare (xargs :verify-guards nil))
  (take 1 (drt-pg-append-dirty a x)))

(must-fail-checked
 (defthm drt-pg-bad-dirty-is-apply-dirty
   (implies (and (drt-pg$ap a) (drt-pg-rowp x))
            (equal (pgs-apply-dirty (drt-pg-pages-of a) (drt-pg-bad-dirty a x))
                   (drt-pg-pages-of (drt-pg$a-append x a))))
   :hints (("Goal" :in-theory (enable drt-pg-pages-of drt-pg$ap drt-pg-rowp)))))

(assert-event
 (not (equal (pgs-apply-dirty (drt-pg-pages-of nil) (drt-pg-bad-dirty nil *drt-wide*))
             (drt-pg-pages-of (list *drt-wide*)))))

; -----------------------------------------------------------------------------
; 3b. A bound of one page.

(must-fail-checked
 (defthm drt-pg-append-dirty-bound-one
   (<= (len (drt-pg-append-dirty a x)) 1)))

(assert-event (not (<= (len (drt-pg-append-dirty nil *drt-wide*)) 1)))

; 4. Refusals.

(must-fail-checked
 (def-representation drt-pg-s (a :u64) :scalar t :pages t)
 :unchecked "refused at expansion: :pages is supported without :scalar and :generic")
(must-fail-checked
 (def-representation drt-pg-b (a :u64) :pages 3)
 :unchecked "refused at expansion: :pages takes t or nil")
(must-fail-checked
 (def-representation drt-pg-n (a (:nat 18446744073709551616)) :pages t)
 :unchecked "refused at expansion: a :nat bound of 2^64 is more than one word")

; -----------------------------------------------------------------------------
; 5. Setting a row in place (same width): the dirty pages are the row's own.

(defconst *drt-big* (append (drt-narrow 300) (list *drt-wide*) (drt-narrow 300)))
(defconst *drt-new* (list 5 (make-list 20000 :initial-element 9) t))

; the wide row sits at index 300, spans three pages; its set rewrites them and no other
(assert-event (<= (len (drt-pg-set-dirty *drt-big* 300 *drt-new*)) 4))
(assert-event (< 1 (len (drt-pg-set-dirty *drt-big* 300 *drt-new*))))
(assert-event (equal (pgs-apply-dirty (drt-pg-pages-of *drt-big*) (drt-pg-set-dirty *drt-big* 300 *drt-new*))
                     (drt-pg-pages-of (update-nth 300 *drt-new* *drt-big*))))
(assert-event (equal (len (drt-pg-set-dirty (drt-narrow 700) 3 '(9 (1 2 3) nil))) 1))

; A set-dirty that keeps only the first dirty page.
(defun drt-pg-bad-set (a i x)
  (declare (xargs :verify-guards nil))
  (take 1 (drt-pg-set-dirty a i x)))

(must-fail-checked
 (defthm drt-pg-bad-set-is-apply-dirty
   (implies (and (drt-pg$ap a) (natp i) (< i (len a)) (drt-pg-rowp x)
                 (equal (len (adt-tp-rw *drt-pg-schema* x)) (len (adt-tp-rw *drt-pg-schema* (nth i a)))))
            (equal (pgs-apply-dirty (drt-pg-pages-of a) (drt-pg-bad-set a i x))
                   (drt-pg-pages-of (update-nth i x a))))
   :hints (("Goal" :in-theory (enable drt-pg-pages-of drt-pg$ap drt-pg-rowp)))))

(assert-event (not (equal (pgs-apply-dirty (drt-pg-pages-of *drt-big*) (drt-pg-bad-set *drt-big* 300 *drt-new*))
                          (drt-pg-pages-of (update-nth 300 *drt-new* *drt-big*)))))

; A bound of one page.
(must-fail-checked
 (defthm drt-pg-set-dirty-bound-one
   (<= (len (drt-pg-set-dirty a i x)) 1)))
(assert-event (not (<= (len (drt-pg-set-dirty *drt-big* 300 *drt-new*)) 1)))

; The set must have the old row's width: a narrower row shifts every later word.
(must-fail-checked
 (defthm drt-pg-set-any-width
   (implies (and (drt-pg$ap a) (natp i) (< i (len a)) (drt-pg-rowp x))
            (equal (pgs-apply-dirty (drt-pg-pages-of a) (drt-pg-set-dirty a i x))
                   (drt-pg-pages-of (update-nth i x a))))
   :hints (("Goal" :in-theory (enable drt-pg-pages-of drt-pg$ap drt-pg-rowp)))))
(assert-event (not (equal (pgs-apply-dirty (drt-pg-pages-of *drt-big*)
                                           (drt-pg-set-dirty *drt-big* 0 '(1 nil nil)))
                          (drt-pg-pages-of (update-nth 0 '(1 nil nil) *drt-big*)))))
