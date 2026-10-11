; fn: the POST machine's head limit HMAX as a term of the sealed profile (D27),
; the figure books/post-transaction.lisp fn-ptx-hmax (lane/post, Builder P)
; reads at open.  The machine scans the poster's SOURCE octets, unmoved, for
; CR LF CR LF within min(len, HMAX) (fn-ptx-head-end: the least i with
; i + 3 < lim, answering i + 4); the injected block goes into the record's
; prefix, so it bounds the prefix, not the scan.
;
; A source the admission parses under the profile's header limits
; (books/article.lisp fn-article-parse-under at fn-bs-profile-header-limits)
; counts each header line with its CRLF and stops at the empty line; a line
; holds no CR and no LF (fn-article-next-line-aux), so with at least one
; header line the first CR LF CR LF in the source is the last line's CRLF
; and the empty line's, and the head through it is the counted octets plus
; 2, at most the profile's header octets plus 2.

(in-package "ACL2")
(include-book "article")
(include-book "byte-store-frame")

(defun fn-adm-head-limit (profile)
  (declare (xargs :guard t))
  (+ 2 (fn-article-limit-octets (fn-bs-profile-header-limits profile))))

; The head's end: I + 4 for the least I at or past START with CR LF CR LF at
; [I, I+4), or NIL when there is none (the pure form of fn-ptx-head-end with no
; scan limit).
(defun fn-adm-head-end (octets i)
  (declare (xargs :guard (natp i) :measure (len octets)))
  (if (and (consp octets) (consp (cdr octets)) (consp (cddr octets)) (consp (cdddr octets)))
      (if (and (equal (car octets) 13) (equal (cadr octets) 10)
               (equal (caddr octets) 13) (equal (cadddr octets) 10))
          (+ (nfix i) 4)
        (fn-adm-head-end (cdr octets) (+ 1 (nfix i))))
    nil))

; KEYSTONE (proved 2026-10-10): a source that parses under the profile's
; header limits with at least one header line has its head end, and within
; HMAX.  Proof: next-line splits the octets as line ++ CR LF ++ rest with a
; CR/LF-free line (fn-adm-hl-next-line-split); a nonempty line is skipped by
; head-end at its length (fn-adm-hl-head-end-skip-line); the invariant over
; fn-article-parse-lines (fn-adm-hl-lines): from header octets HB <= L with
; one CR LF behind, the head end of CR LF . octets, counted from HB - 2, is
; at most L + 2 (the empty line ends it at HB + 2; a nonempty line of length N
; moves to HB + N + 2, which the parse's own octet check keeps within L).

(defun fn-adm-hl-no-crlf (l)
  (declare (xargs :guard t))
  (if (consp l)
      (and (not (equal (car l) 13)) (not (equal (car l) 10)) (fn-adm-hl-no-crlf (cdr l)))
    t))
(defthm fn-adm-hl-no-crlf-append
  (equal (fn-adm-hl-no-crlf (append a b)) (and (fn-adm-hl-no-crlf a) (fn-adm-hl-no-crlf b))))
(defthm fn-adm-hl-no-crlf-rev
  (equal (fn-adm-hl-no-crlf (rev a)) (fn-adm-hl-no-crlf a))
  :hints (("Goal" :in-theory (enable rev))))
(defthm fn-adm-hl-append-assoc
  (equal (append (append a b) c) (append a (append b c))))
(defthm fn-adm-hl-rev-cons
  (equal (rev (cons a x)) (append (rev x) (list a)))
  :hints (("Goal" :in-theory (enable rev))))
(defthm fn-adm-hl-reverse-is-rev
  (implies (true-listp x) (equal (reverse x) (rev x)))
  :hints (("Goal" :in-theory (enable rev reverse))))
(defthm fn-adm-hl-next-line-aux-split
  (let ((r (fn-article-next-line-aux octets lrev left)))
    (implies (and (fn-article-line-okp r) (true-listp lrev) (fn-adm-hl-no-crlf lrev))
             (and (equal (append (fn-article-line-value r) (list 13 10) (fn-article-line-rest r))
                         (append (rev lrev) octets))
                  (fn-adm-hl-no-crlf (fn-article-line-value r)))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets lrev left)
           :in-theory (enable fn-article-line-okp fn-article-line-value fn-article-line-rest fn-article-error)
           :expand ((fn-article-next-line-aux octets lrev left)))))
(defthm fn-adm-hl-next-line-split
  (let ((r (fn-article-next-line octets)))
    (implies (fn-article-line-okp r)
             (and (equal (append (fn-article-line-value r) (list 13 10) (fn-article-line-rest r)) octets)
                  (fn-adm-hl-no-crlf (fn-article-line-value r)))))
  :hints (("Goal" :in-theory (e/d (fn-article-next-line) (fn-article-next-line-aux))
           :use ((:instance fn-adm-hl-next-line-aux-split (lrev nil) (left *fn-article-max-line-octets*))))))
(defthm fn-adm-hl-head-end-cons-not-cr
  (implies (not (equal c 13))
           (equal (fn-adm-head-end (cons c x) i) (fn-adm-head-end x (+ 1 (nfix i)))))
  :hints (("Goal" :expand ((fn-adm-head-end (cons c x) i)))))
(defun fn-adm-hl-ind (line i)
  (if (endp line) i (fn-adm-hl-ind (cdr line) (+ 1 (nfix i)))))
(defthm fn-adm-hl-head-end-skip-line
  (implies (and (fn-adm-hl-no-crlf line) (natp i))
           (equal (fn-adm-head-end (append line (cons 13 (cons 10 rest))) i)
                  (fn-adm-head-end (cons 13 (cons 10 rest)) (+ i (len line)))))
  :hints (("Goal" :induct (fn-adm-hl-ind line i) :in-theory (disable fn-adm-head-end))))
(defthm fn-adm-hl-head-end-crlf
  (equal (fn-adm-head-end (cons 13 (cons 10 rest)) j)
         (if (and (consp rest) (consp (cdr rest)) (equal (car rest) 13) (equal (cadr rest) 10))
             (+ (nfix j) 4)
           (fn-adm-head-end rest (+ 2 (nfix j)))))
  :hints (("Goal" :expand ((fn-adm-head-end (cons 13 (cons 10 rest)) j)))))
(defthm fn-adm-hl-step-empty
  (implies (and (natp hb) (<= 2 hb)
                (fn-article-line-okp (fn-article-next-line octets))
                (null (fn-article-line-value (fn-article-next-line octets))))
           (equal (fn-adm-head-end (cons 13 (cons 10 octets)) (- hb 2)) (+ hb 2)))
  :hints (("Goal" :in-theory (disable fn-adm-head-end fn-article-next-line fn-adm-hl-head-end-skip-line)
           :use fn-adm-hl-next-line-split)))
(defthm fn-adm-hl-step-line-gen
  (implies (and (fn-adm-hl-no-crlf line) (consp line) (natp hb) (<= 2 hb)
                (equal octets (append line (cons 13 (cons 10 rest)))))
           (equal (fn-adm-head-end (cons 13 (cons 10 octets)) (- hb 2))
                  (fn-adm-head-end (cons 13 (cons 10 rest)) (+ hb (len line)))))
  :hints (("Goal" :in-theory (disable fn-adm-head-end fn-adm-hl-head-end-skip-line fn-adm-hl-head-end-cons-not-cr)
           :use ((:instance fn-adm-hl-head-end-skip-line (i hb))
                 (:instance fn-adm-hl-head-end-cons-not-cr (c (car line)) (x (append (cdr line) (cons 13 (cons 10 rest)))) (i (- hb 1)))))))
(defthm fn-adm-hl-step-line
  (implies (and (natp hb) (<= 2 hb)
                (fn-article-line-okp (fn-article-next-line octets))
                (consp (fn-article-line-value (fn-article-next-line octets))))
           (equal (fn-adm-head-end (cons 13 (cons 10 octets)) (- hb 2))
                  (fn-adm-head-end (cons 13 (cons 10 (fn-article-line-rest (fn-article-next-line octets))))
                                   (+ hb (len (fn-article-line-value (fn-article-next-line octets)))))))
  :hints (("Goal" :in-theory (disable fn-adm-head-end fn-article-next-line fn-adm-hl-step-line-gen fn-adm-hl-next-line-split)
           :use (fn-adm-hl-next-line-split
                 (:instance fn-adm-hl-step-line-gen
                            (line (fn-article-line-value (fn-article-next-line octets)))
                            (rest (fn-article-line-rest (fn-article-next-line octets))))))))
(defthm fn-adm-hl-step-empty-ok
  (implies (and (natp hb) (<= 2 hb)
                (equal (car (fn-article-next-line octets)) :ok)
                (not (cadr (fn-article-next-line octets))))
           (equal (fn-adm-head-end (cons 13 (cons 10 octets)) (- hb 2)) (+ hb 2)))
  :hints (("Goal" :use fn-adm-hl-step-empty
           :in-theory (disable fn-adm-hl-step-empty fn-article-next-line fn-adm-head-end))))
(defthm fn-adm-hl-step-line-ok
  (implies (and (natp hb) (<= 2 hb)
                (equal (car (fn-article-next-line octets)) :ok)
                (consp (cadr (fn-article-next-line octets))))
           (equal (fn-adm-head-end (cons 13 (cons 10 octets)) (- hb 2))
                  (fn-adm-head-end (cons 13 (cons 10 (caddr (fn-article-next-line octets))))
                                   (+ hb (len (cadr (fn-article-next-line octets)))))))
  :hints (("Goal" :use fn-adm-hl-step-line
           :in-theory (disable fn-adm-hl-step-line fn-article-next-line fn-adm-head-end))))
(defthm fn-adm-hl-next-line-aux-line-true-listp
  (implies (and (equal (car (fn-article-next-line-aux octets lrev left)) :ok)
                (true-listp lrev))
           (true-listp (cadr (fn-article-next-line-aux octets lrev left))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets lrev left)
           :in-theory (enable fn-article-error)
           :expand ((fn-article-next-line-aux octets lrev left)))))
(defthm fn-adm-hl-next-line-line-true-listp
  (implies (equal (car (fn-article-next-line octets)) :ok)
           (true-listp (cadr (fn-article-next-line octets))))
  :hints (("Goal" :in-theory (e/d (fn-article-next-line) (fn-article-next-line-aux))
           :use (:instance fn-adm-hl-next-line-aux-line-true-listp (lrev nil) (left *fn-article-max-line-octets*)))))
(defthm fn-adm-hl-step-line-ok2
  (implies (and (natp hb) (<= 2 hb)
                (equal (car (fn-article-next-line octets)) :ok)
                (cadr (fn-article-next-line octets)))
           (equal (fn-adm-head-end (cons 13 (cons 10 octets)) (- hb 2))
                  (fn-adm-head-end (cons 13 (cons 10 (caddr (fn-article-next-line octets))))
                                   (+ hb (len (cadr (fn-article-next-line octets)))))))
  :hints (("Goal" :use (fn-adm-hl-step-line-ok fn-adm-hl-next-line-line-true-listp)
           :in-theory (disable fn-adm-hl-step-line-ok fn-adm-hl-next-line-line-true-listp fn-article-next-line fn-adm-head-end))))
(defun fn-adm-hl-calls (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((and (eq (car x) 'fn-article-parse-lines) (consp (cdr x)) (eq (cadr x) 'octets))
         (list x))
        (t (append (fn-adm-hl-calls (car x)) (fn-adm-hl-calls (cdr x))))))
(defthm fn-adm-hl-lines
  (implies (and (natp hb) (<= 2 hb) (<= hb (fn-article-limit-octets limits))
                (fn-article-result-okp
                 (fn-article-parse-lines octets limits ll hb nf fr cur hr)))
           (and (fn-adm-head-end (cons 13 (cons 10 octets)) (- hb 2))
                (<= (fn-adm-head-end (cons 13 (cons 10 octets)) (- hb 2))
                    (+ 2 (fn-article-limit-octets limits)))))
  :hints (("Goal" :induct (fn-article-parse-lines octets limits ll hb nf fr cur hr)
           :in-theory (disable fn-adm-head-end fn-article-next-line fn-article-new-field fn-adm-hl-head-end-crlf
                               (:definition fn-article-parse-lines)))
          (and stable-under-simplificationp
               (let ((calls (fn-adm-hl-calls clause)))
                 (and calls `(:expand ,calls)))))
  :rule-classes nil)
(defthm fn-adm-hl-top-line-gen
  (implies (and (fn-adm-hl-no-crlf line) (consp line)
                (equal octets (append line (cons 13 (cons 10 rest)))))
           (equal (fn-adm-head-end octets 0)
                  (fn-adm-head-end (cons 13 (cons 10 rest)) (len line))))
  :hints (("Goal" :in-theory (disable fn-adm-head-end fn-adm-hl-head-end-skip-line)
           :use ((:instance fn-adm-hl-head-end-skip-line (i 0))))))
(defthm fn-adm-hl-top-line
  (implies (and (equal (car (fn-article-next-line octets)) :ok)
                (cadr (fn-article-next-line octets)))
           (equal (fn-adm-head-end octets 0)
                  (fn-adm-head-end (cons 13 (cons 10 (caddr (fn-article-next-line octets))))
                                   (len (cadr (fn-article-next-line octets))))))
  :hints (("Goal" :use (fn-adm-hl-next-line-split fn-adm-hl-next-line-line-true-listp
                        (:instance fn-adm-hl-top-line-gen
                                   (line (cadr (fn-article-next-line octets)))
                                   (rest (caddr (fn-article-next-line octets)))))
           :in-theory (disable fn-adm-hl-next-line-split fn-adm-hl-next-line-line-true-listp
                               fn-adm-hl-top-line-gen fn-article-next-line fn-adm-head-end))))
(defthm fn-adm-hl-top
  (implies (and (equal (car (fn-article-parse-lines octets limits ll 0 0 nil nil nil)) :ok)
                (consp (fn-article-header
                        (cadr (fn-article-parse-lines octets limits ll 0 0 nil nil nil)))))
           (and (fn-adm-head-end octets 0)
                (<= (fn-adm-head-end octets 0) (+ 2 (fn-article-limit-octets limits)))))
  :hints (("Goal" :expand ((fn-article-parse-lines octets limits ll 0 0 nil nil nil))
           :in-theory (disable fn-adm-head-end fn-article-next-line fn-article-new-field))
          (and stable-under-simplificationp
               '(:use ((:instance fn-adm-hl-lines
                                  (octets (caddr (fn-article-next-line octets)))
                                  (ll (+ -1 ll))
                                  (hb (+ 2 (len (cadr (fn-article-next-line octets)))))
                                  (nf 0) (fr nil)
                                  (cur (cadr (fn-article-new-field (cadr (fn-article-next-line octets)))))
                                  (hr (fn-article-header-rev-add-line nil (cadr (fn-article-next-line octets)))))))))
  :rule-classes nil)
(defthm fn-adm-hl-under-ok
  (implies (fn-article-result-okp (fn-article-parse-under src limits))
           (equal (fn-article-parse-under src limits)
                  (fn-article-parse-lines src limits (+ 1 (fn-article-limit-lines limits))
                                          0 0 nil nil nil)))
  :hints (("Goal" :in-theory (e/d (fn-article-parse-under fn-article-result-okp fn-article-error)
                                  (fn-article-parse-lines fn-cbor-at-mostp fn-cbor-octet-listp))))
  :rule-classes nil)
(defthm fn-adm-hl-under
  (implies (and (fn-article-result-okp (fn-article-parse-under src limits))
                (consp (fn-article-header
                        (fn-article-result-article (fn-article-parse-under src limits)))))
           (and (fn-adm-head-end src 0)
                (<= (fn-adm-head-end src 0) (+ 2 (fn-article-limit-octets limits)))))
  :hints (("Goal" :use (fn-adm-hl-under-ok
                        (:instance fn-adm-hl-top (octets src)
                                   (ll (+ 1 (fn-article-limit-lines limits)))))
           :in-theory (e/d (fn-article-result-okp fn-article-result-article)
                           (fn-adm-head-end fn-article-parse-lines fn-article-parse-under
                            ))))
  :rule-classes nil)
(defthm fn-adm-source-head-within-the-head-limit
  (let ((r (fn-article-parse-under src (fn-bs-profile-header-limits profile))))
    (implies (and (fn-article-result-okp r)
                  (consp (fn-article-header (fn-article-result-article r))))
             (and (fn-adm-head-end src 0)
                  (<= (fn-adm-head-end src 0) (fn-adm-head-limit profile)))))
  :hints (("Goal" :use (:instance fn-adm-hl-under (limits (fn-bs-profile-header-limits profile)))
           :in-theory (e/d (fn-adm-head-limit)
                           (fn-adm-head-end fn-article-parse-under fn-bs-profile-header-limits
                            fn-article-result-okp fn-article-result-article)))))
