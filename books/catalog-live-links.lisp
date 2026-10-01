; fn: the live LINKS of the paged catalog (lane paged-catalog-5, Gate C of
; stage 3, planning/design-store-representation-2026-10-01.md; Codex r20 F2).
;
; A withdrawal of a group's least (greatest) live number must find the next
; (previous) live one.  The old executable scans the group's numbers for it
; (fn-cat$c-scan-up / -scan-down), one row decode a number: measured on
; hbox (10k rows, 2 groups, guards on) ONE withdrawal of the high after the
; 9,998 numbers below it were withdrawn consed 209 MB in 0.28 s.  The paged
; catalog keeps, per live (group . number), its neighbours: NEXT, the least
; live number above it, and PREV, the greatest live number below it, in two
; tables beside the rows.  This book states what an entry means over the
; logical rows (`fn-cpl-okp': every bound key is a live number and its
; value is that neighbour) and proves the tables' updates keep it: the
; commit links the new number after the group's live high
; (fn-cpl-okp-of-commit), the withdrawal unlinks its number
; (fn-cpl-okp-of-withdraw), a redecision changes no number's liveness
; (fn-cpl-okp-of-redecide).  A clear or a keyed clear empties the rows, so
; every number dies: the tables are cleared with them (fn-cpl-okp-nil).
; books/catalog-paged.lisp will carry `fn-cpl-okp' in its correspondence
; and answer a scan from the table (stage 3, gate C2).  An executable
; reading of `fn-cpl-okp' for the witnesses (tests/acl2/catalog-live-links-
; tests.lisp): fn-cpl-okp-is-all-goodp.

; The list-level lemmas about live numbers under an append and a withdrawal
; (section 1) are books/catalog-logic.lisp's own, local there; they are
; restated here, prefixed fn-cpl-, rather than exported from that book,
; whose closure is most of the tree.

(in-package "ACL2")
(include-book "catalog-logic")

(local (in-theory (disable (tau-system))))
(local (in-theory (disable fn-held-listp-implies-cat-rowsp)))

; -----------------------------------------------------------------------------
; 1. Live numbers under an append and a withdrawal (catalog-logic's, restated).

; -----------------------------------------------------------------------------
; The columns over an appended row, and over a row replaced with its keys
; kept (Message-ID, numbers, facts).

(local
 (defthm fn-cpl-seqs-for-append
   (implies (natp i)
            (equal (fn-cat-seqs-for m (append c (list h)) i)
                   (if (equal m (fn-record-msgid h))
                       (append (fn-cat-seqs-for m c i) (list (+ i (len c))))
                     (fn-cat-seqs-for m c i))))))

(local
 (defthm fn-cpl-number-seq-append
   (implies (natp i)
            (equal (fn-cat-number-seq g n (append c (list h)) i)
                   (if (fn-cat-number-seq g n c i)
                       (fn-cat-number-seq g n c i)
                     (if (and (fn-held-number-in g h) (equal n (fn-held-number-in g h)))
                         (+ i (len c))
                       nil))))))

(local
 (defthm fn-cpl-high-append
   (equal (fn-cat-group-high g (append c (list h)))
          (max (fn-cat-group-high g c) (nfix (fn-held-number-in g h))))))

(local
 (defthm fn-cpl-rows-append
   (equal (fn-cat-group-rows g (append c (list h)))
          (+ (fn-cat-group-rows g c) (if (fn-held-number-in g h) 1 0)))))

(local
 (defthm fn-cpl-octets-append
   (equal (fn-cat-octets-of (append c (list h)))
          (+ (fn-cat-octets-of c) (nfix (fn-hf-octets (fn-held-facts h)))))))

; A held row's number in a group is nil or a positive integer.
(local
 (defthm fn-cpl-assoc-of-numbersp
   (implies (fn-held-numbersp ns)
            (or (null (cdr (fn-cat-assoc g ns)))
                (posp (cdr (fn-cat-assoc g ns)))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-held-numbersp)))))

(local
 (defthm fn-cpl-number-in-type
   (implies (fn-held-p h)
            (or (null (fn-held-number-in g h))
                (posp (fn-held-number-in g h))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-held-number-in)
                   :use ((:instance fn-cpl-assoc-of-numbersp (ns (fn-held-numbers h))))))))

; The same fact as a rewrite: a present number is a positive integer.
(local
 (defthm fn-cpl-assoc-of-numbersp-rewrite
   (implies (and (fn-held-numbersp ns) (cdr (fn-cat-assoc g ns)))
            (and (integerp (cdr (fn-cat-assoc g ns)))
                 (< 0 (cdr (fn-cat-assoc g ns)))))
   :hints (("Goal" :use fn-cpl-assoc-of-numbersp))))

; A number above the group's high names no row.
(local
 (defthm fn-cpl-number-seq-above-high
   (implies (and (fn-cat-rowsp c) (rationalp n) (< (fn-cat-group-high g c) n))
            (equal (fn-cat-number-seq g n c i) nil))))

; A bound number is at most the high.
(local
 (defthm fn-cpl-number-seq-below-high
   (implies (and (fn-cat-rowsp c) (fn-cat-number-seq g n c i) (rationalp n))
            (<= n (fn-cat-group-high g c)))
   :rule-classes :linear))

; The keys of a row replaced with its keys kept.


(local
 (defthm fn-cpl-seqs-for-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-seqs-for m (update-nth k h c) i)
                   (fn-cat-seqs-for m c i)))))

(local
 (defthm fn-cpl-number-in-same-keys
   (implies (fn-cat-same-keysp h1 h2)
            (equal (fn-held-number-in g h1) (fn-held-number-in g h2)))
   :rule-classes nil))

(local
 (defthm fn-cpl-number-seq-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-number-seq g n (update-nth k h c) i)
                   (fn-cat-number-seq g n c i)))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-cpl-high-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-group-high g (update-nth k h c))
                   (fn-cat-group-high g c)))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-cpl-rows-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-group-rows g (update-nth k h c))
                   (fn-cat-group-rows g c)))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-cpl-octets-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-octets-of (update-nth k h c))
                   (fn-cat-octets-of c)))))

(local
 (defthm fn-cpl-with-withdrawn-same-keys
   (fn-cat-same-keysp (fn-held-with-withdrawn h w) h)))

(local
 (defthm fn-cpl-with-context-same-keys
   (fn-cat-same-keysp (fn-held-with-context h ctx) h)))

(local
 (defthm fn-cpl-assign-fields
   (and (equal (fn-record-msgid (fn-cat-assign h c)) (fn-record-msgid h))
        (equal (fn-held-numbers (fn-cat-assign h c))
               (fn-cat-assign-numbers (fn-record-groups h) c))
        (equal (fn-held-facts (fn-cat-assign h c)) (fn-held-facts h)))))

(local
 (defthm fn-cpl-assoc-of-assign-numbers
   (equal (fn-cat-assoc g (fn-cat-assign-numbers groups c))
          (if (member-equal g groups)
              (cons g (+ 1 (fn-cat-group-high g c)))
            nil))))

(local
 (defthm fn-cpl-number-in-of-assign
   (equal (fn-held-number-in g (fn-cat-assign h c))
          (if (member-equal g (fn-record-groups h))
              (+ 1 (fn-cat-group-high g c))
            nil))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

; -----------------------------------------------------------------------------
; The live summary over the list: the committed row and a withdrawal.

(local
 (defthm fn-cpl-withdrawn-of-assign
   (equal (fn-held-withdrawn (fn-cat-assign h c)) (fn-held-withdrawn h))
   :hints (("Goal" :in-theory (enable fn-cat-assign fn-held-with-numbers)))))

(local
 (defthm fn-cpl-nth-append-one-below
   (implies (and (natp i) (< i (len c)))
            (equal (nth i (append c (list h))) (nth i c)))))

(local
 (defthm fn-cpl-nth-append-one-at
   (implies (equal i (len c))
            (equal (nth i (append c (list h))) h))))

(local
 (defthm fn-cpl-len-append-one (equal (len (append c (list h))) (+ 1 (len c)))))

(local
 (defthm fn-cpl-number-seq-natp
   (implies (natp i)
            (or (equal (fn-cat-number-seq g n c i) nil)
                (natp (fn-cat-number-seq g n c i))))
   :rule-classes :type-prescription))

(local
 (defthm fn-cpl-number-seq-bounds
   (implies (and (natp i) (fn-cat-number-seq g n c i))
            (and (<= i (fn-cat-number-seq g n c i))
                 (< (fn-cat-number-seq g n c i) (+ i (len c)))))
   :rule-classes :linear))

(local
 (defthm fn-cpl-number-seq-names-number
   (implies (and (natp i) (fn-cat-number-seq g n c i))
            (equal (fn-held-number-in g (nth (- (fn-cat-number-seq g n c i) i) c)) n))
   :hints (("Goal" :induct (fn-cat-number-seq g n c i)))))

(local
 (defthm fn-cpl-number-seq-names-number-0
   (implies (fn-cat-number-seq g n c 0)
            (equal (fn-held-number-in g (nth (fn-cat-number-seq g n c 0) c)) n))
   :hints (("Goal" :use ((:instance fn-cpl-number-seq-names-number (i 0)))))))

(local
 (defthm fn-cpl-live-append-other
   (implies (and (fn-cat-rowsp c)
                 (not (and (member-equal g (fn-record-groups h))
                           (equal k (+ 1 (fn-cat-group-high g c))))))
            (equal (fn-cat-live-numberp g k (append c (list (fn-cat-assign h c))))
                   (fn-cat-live-numberp g k c)))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-numberp)
                                   (fn-cat-assign fn-cat-live-rowp fn-cat-rowsp fn-held-number-in
                                    nth fn-cat-number-seq len))))))

(local
 (defthm fn-cpl-live-append-new
   (implies (and (fn-cat-rowsp c) (member-equal g (fn-record-groups h))
                 (equal n (+ 1 (fn-cat-group-high g c))))
            (equal (fn-cat-live-numberp g n (append c (list (fn-cat-assign h c))))
                   (and (null (fn-held-withdrawn h))
                        (<= n *fn-nntp-max-article-number*)
                        (fn-scat-msgid-idp (fn-record-msgid h)))))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-numberp fn-cat-live-rowp)
                                   (fn-cat-assign fn-cat-rowsp fn-held-number-in fn-scat-msgid-idp
                                    nth fn-cat-number-seq len fn-cat-group-high))))))

(local
 (defthm fn-cpl-live-count-append
   (implies (and (fn-cat-rowsp c)
                 (or (not (member-equal g (fn-record-groups h)))
                     (<= top (fn-cat-group-high g c))))
            (equal (fn-cat-live-count-from g k top (append c (list (fn-cat-assign h c))))
                   (fn-cat-live-count-from g k top c)))
   :hints (("Goal" :induct (fn-cat-live-count-from g k top c)
            :in-theory (disable fn-cat-assign fn-cat-live-numberp)))))

(local
 (defthm fn-cpl-live-first-append
   (implies (and (fn-cat-rowsp c)
                 (or (not (member-equal g (fn-record-groups h)))
                     (<= top (fn-cat-group-high g c))))
            (equal (fn-cat-live-first g k top (append c (list (fn-cat-assign h c))))
                   (fn-cat-live-first g k top c)))
   :hints (("Goal" :induct (fn-cat-live-first g k top c)
            :in-theory (disable fn-cat-assign fn-cat-live-numberp)))))

(local
 (defthm fn-cpl-live-last-append
   (implies (and (fn-cat-rowsp c)
                 (or (not (member-equal g (fn-record-groups h)))
                     (<= k (fn-cat-group-high g c))))
            (equal (fn-cat-live-last g k (append c (list (fn-cat-assign h c))))
                   (fn-cat-live-last g k c)))
   :hints (("Goal" :induct (fn-cat-live-last g k c)
            :in-theory (disable fn-cat-assign fn-cat-live-numberp)))))

; One more number at the top of the range.
(local
 (defthm fn-cpl-live-empty-range
   (implies (< top k)
            (and (equal (fn-cat-live-count-from g k top c) 0)
                 (equal (fn-cat-live-first g k top c) 0)))))

(local
 (defthm fn-cpl-live-numberp-posp
   (implies (fn-cat-live-numberp g k c) (posp k))
   :rule-classes :forward-chaining))

(local
 (defthm fn-cpl-live-numberp-0
   (not (fn-cat-live-numberp g 0 c))))

(local
 (defthm fn-cpl-live-count-top
   (implies (and (natp k) (natp top) (<= k (+ 1 top)))
            (equal (fn-cat-live-count-from g k (+ 1 top) c)
                   (+ (fn-cat-live-count-from g k top c)
                      (if (fn-cat-live-numberp g (+ 1 top) c) 1 0))))
   :hints (("Goal" :induct (fn-cat-live-count-from g k top c)
            :in-theory (disable fn-cat-live-numberp)))))

(local
 (defthm fn-cpl-live-first-top
   (implies (and (natp k) (natp top) (<= k (+ 1 top)))
            (equal (fn-cat-live-first g k (+ 1 top) c)
                   (if (equal (fn-cat-live-first g k top c) 0)
                       (if (fn-cat-live-numberp g (+ 1 top) c) (+ 1 top) 0)
                     (fn-cat-live-first g k top c))))
   :hints (("Goal" :induct (fn-cat-live-first g k top c)
            :in-theory (disable fn-cat-live-numberp)))))

; The first live number is 0 or at least K and live; the last is at most K
; and live.
(local
 (defthm fn-cpl-live-first-bounds
   (implies (and (natp k) (not (equal (fn-cat-live-first g k top c) 0)))
            (and (<= k (fn-cat-live-first g k top c))
                 (<= (fn-cat-live-first g k top c) top)
                 (fn-cat-live-numberp g (fn-cat-live-first g k top c) c)))
   :hints (("Goal" :induct (fn-cat-live-first g k top c)
            :in-theory (disable fn-cat-live-numberp)))))

(local
 (defthm fn-cpl-live-last-bounds
   (implies (not (equal (fn-cat-live-last g k c) 0))
            (and (<= (fn-cat-live-last g k c) k)
                 (fn-cat-live-numberp g (fn-cat-live-last g k c) c)))
   :hints (("Goal" :induct (fn-cat-live-last g k c)
            :in-theory (disable fn-cat-live-numberp)))))

(local
 (defthm fn-cpl-live-types
   (and (natp (fn-cat-live-count-from g k top c))
        (natp (fn-cat-live-first g k top c))
        (natp (fn-cat-live-last g k c)))
   :rule-classes (:rewrite
                  (:type-prescription :corollary (natp (fn-cat-live-count-from g k top c)))
                  (:type-prescription :corollary (natp (fn-cat-live-first g k top c)))
                  (:type-prescription :corollary (natp (fn-cat-live-last g k c))))))

; A withdrawal: the one number of each group the withdrawn row is the
; column's answer for stops being live.


(local
 (defthm fn-cpl-live-rowp-of-withdrawn
   (not (fn-cat-live-rowp g k (fn-held-with-withdrawn h (cons v by))))
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn)))))

(local
 (defthm fn-cpl-mark-withdrawn-is-update
   (implies (and (< r (len c)) (null (fn-held-withdrawn (nth r c))))
            (equal (fn-cat-mark-withdrawn r v by c)
                   (update-nth r (fn-held-with-withdrawn (nth r c) (cons v by)) c)))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

(local
 (defthm fn-cpl-number-seq-withdrawn
   (implies (and (natp r) (< r (len c)))
            (equal (fn-cat-number-seq g n (update-nth r (fn-held-with-withdrawn (nth r c) w) c) i)
                   (fn-cat-number-seq g n c i)))
   :hints (("Goal" :in-theory (disable fn-cat-number-seq fn-held-with-withdrawn)
            :use ((:instance fn-cpl-number-seq-update-nth
                             (k r) (h (fn-held-with-withdrawn (nth r c) w))))))))

(local
 (defthm fn-cpl-live-rowp-number
   (implies (fn-cat-live-rowp g k h)
            (and (posp k) (equal (fn-held-number-in g h) k)))
   :rule-classes :forward-chaining))

(local
 (defthm fn-cpl-live-withdrawn
   (implies (and (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c))))
            (equal (fn-cat-live-numberp g j (fn-cat-mark-withdrawn r v by c))
                   (and (fn-cat-live-numberp g j c)
                        (not (equal j (fn-ctg-kstar g c r))))))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-numberp fn-ctg-kstar)
                                   (fn-held-with-withdrawn fn-cat-live-rowp fn-cat-number-seq
                                    fn-held-number-in fn-cat-mark-withdrawn nth update-nth))
            :cases ((equal (fn-cat-number-seq g j c 0) r))))))

(local
 (defthm fn-cpl-high-withdrawn
   (equal (fn-cat-group-high g (fn-cat-mark-withdrawn r v by c))
          (fn-cat-group-high g c))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

(local
 (defthm fn-cpl-live-count-withdrawn
   (implies (and (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c))) (natp top))
            (equal (fn-cat-live-count-from g j top (fn-cat-mark-withdrawn r v by c))
                   (- (fn-cat-live-count-from g j top c)
                      (if (and (natp j) (<= j (fn-ctg-kstar g c r))
                               (<= (fn-ctg-kstar g c r) top)
                               (fn-cat-live-numberp g (fn-ctg-kstar g c r) c))
                          1 0))))
   :hints (("Goal" :induct (fn-cat-live-count-from g j top c)
            :in-theory (disable fn-cat-live-numberp fn-ctg-kstar fn-cat-mark-withdrawn fn-cpl-mark-withdrawn-is-update)))))

(local
 (defthm fn-cpl-live-first-withdrawn
   (implies (and (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c))) (natp j) (natp top))
            (equal (fn-cat-live-first g j top (fn-cat-mark-withdrawn r v by c))
                   (if (and (not (equal (fn-ctg-kstar g c r) 0))
                            (equal (fn-cat-live-first g j top c) (fn-ctg-kstar g c r)))
                       (fn-cat-live-first g (+ 1 (fn-ctg-kstar g c r)) top c)
                     (fn-cat-live-first g j top c))))
   :hints (("Goal" :induct (fn-cat-live-count-from g j top c)
            :expand ((fn-cat-live-first g j top (fn-cat-mark-withdrawn r v by c))
                     (fn-cat-live-first g j top c))
            :in-theory (disable fn-cat-live-numberp fn-ctg-kstar fn-cat-mark-withdrawn fn-cpl-mark-withdrawn-is-update)))))

(local
 (defun fn-cpl-down-ind (j)
   (declare (xargs :guard t))
   (if (posp j) (fn-cpl-down-ind (- j 1)) t)))

(local
 (defthm fn-cpl-live-last-withdrawn
   (implies (and (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c))))
            (equal (fn-cat-live-last g j (fn-cat-mark-withdrawn r v by c))
                   (if (and (not (equal (fn-ctg-kstar g c r) 0))
                            (equal (fn-cat-live-last g j c) (fn-ctg-kstar g c r)))
                       (fn-cat-live-last g (- (fn-ctg-kstar g c r) 1) c)
                     (fn-cat-live-last g j c))))
   :hints (("Goal" :induct (fn-cpl-down-ind j)
            :expand ((fn-cat-live-last g j (fn-cat-mark-withdrawn r v by c))
                     (fn-cat-live-last g j c))
            :in-theory (disable fn-cat-live-numberp fn-ctg-kstar fn-cat-mark-withdrawn fn-cpl-mark-withdrawn-is-update)))))


; -----------------------------------------------------------------------------
; 2. The links.  An entry of the NEXT (DIR t) or PREV (DIR nil) table, keyed
; (g . k), is good when k is a live number of g and its value is the least
; live number above k (0: none up to the group's high) or the greatest below
; (0: none); `fn-cpl-okp' says every bound key is good.  The scan
; equalities first: over a correspondent old foundation the old executable's
; scans ARE live-first/live-last (catalog-logic proves these locally).

(defthm fn-cpl-numbers-okp-lookup
  (implies (and (fn-cat-numbers-okp keys tab c) (consp (hons-assoc-equal x keys)))
           (and (equal (cdr (hons-assoc-equal x tab)) (fn-cat-number-seq (car x) (cdr x) c 0))
                (fn-cat-number-seq (car x) (cdr x) c 0)))
  :hints (("Goal" :in-theory (disable fn-cat-number-seq))))

(defthm fn-cpl-cover-row-member
  (implies (and (fn-cat-numbers-cover-rowp numbers tab) (member-equal p numbers))
           (consp (hons-assoc-equal p tab))))

(defthm fn-cpl-row-number-bound
  (implies (and (fn-cat-numbers-cover-rowp numbers tab) (consp (fn-cat-assoc g numbers)))
           (consp (hons-assoc-equal (cons g (cdr (fn-cat-assoc g numbers))) tab)))
  :hints (("Goal" :in-theory (enable fn-cat-assoc))))

(defthm fn-cpl-number-seq-bound
  (implies (and (fn-cat-numbers-coverp c tab) (fn-cat-number-seq g k c i))
           (consp (hons-assoc-equal (cons g k) tab)))
  :hints (("Goal" :in-theory (e/d (fn-held-number-in) (fn-cat-assoc))
           :induct (fn-cat-number-seq g k c i))))

(defthm fn-cpl-rows-corr-nth
  (implies (and (fn-cat-rows-corr n c rows) (natp i) (< i (nfix n)))
           (equal (nth i rows) (nth i c)))
  :hints (("Goal" :induct (fn-cat-rows-corr n c rows) :in-theory (e/d (fn-cat-rows-corr) (nth)))
          ("Subgoal *1/2" :cases ((equal i (- n 1))))))

(defthm fn-cpl-live-at-p-is-live
   (implies (fn-cat$corr-base x c)
            (equal (fn-cat$c-live-at-p g k x) (fn-cat-live-numberp g k c)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-live-at-p fn-cat-live-numberp fn-cat$corr-base fn-cat$c-numbers-get fn-cat$c-rowsi)
                                   (fn-cat-live-rowp fn-cat-number-seq))
            :use ((:instance fn-cpl-numbers-okp-lookup (keys (nth 3 x)) (tab (nth 3 x)) (x (cons g k)))
                  (:instance fn-cpl-number-seq-bound (tab (nth 3 x)) (i 0))))))

(defthm fn-cpl-scan-up-is-first
   (implies (fn-cat$corr-base x c)
            (equal (fn-cat$c-scan-up g k top x) (fn-cat-live-first g k top c)))
   :hints (("Goal" :induct (fn-cat-live-first g k top c)
            :in-theory (e/d (fn-cat$c-scan-up) (fn-cat$corr-base fn-cat$c-live-at-p
                                                 fn-cat-live-numberp)))))

(defun fn-cpl-down-ind (j)
   (declare (xargs :guard t))
   (if (posp j) (fn-cpl-down-ind (- j 1)) t))

(defthm fn-cpl-scan-down-is-last
   (implies (fn-cat$corr-base x c)
            (equal (fn-cat$c-scan-down g k x) (fn-cat-live-last g k c)))
   :hints (("Goal" :induct (fn-cat-live-last g k c)
            :in-theory (e/d (fn-cat$c-scan-down) (fn-cat$corr-base fn-cat$c-live-at-p
                                                   fn-cat-live-numberp)))))

(defthm fn-cpl-first-skips
  (implies (and (natp a) (natp m) (natp top) (<= a m) (<= m top)
                (or (equal (fn-cat-live-first g a top c) 0)
                    (< m (fn-cat-live-first g a top c))))
           (not (fn-cat-live-numberp g m c)))
  :hints (("Goal" :induct (fn-cat-live-first g a top c)
           :in-theory (disable fn-cat-live-numberp))))

(defthm fn-cpl-last-from-gap
  (implies (and (fn-cat-live-numberp g j c) (natp j) (natp m) (<= j m)
                (natp top) (<= m top)
                (or (equal (fn-cat-live-first g (+ 1 j) top c) 0)
                    (< m (fn-cat-live-first g (+ 1 j) top c))))
           (equal (fn-cat-live-last g m c) j))
  :hints (("Goal" :induct (fn-cpl-down-ind m)
           :expand ((fn-cat-live-last g m c))
           :in-theory (disable fn-cat-live-numberp))
          ("Subgoal *1/1" :use ((:instance fn-cpl-first-skips (a (+ 1 j)))))))

(defthm fn-cpl-last-skips
  (implies (and (natp m) (natp b) (<= m b) (posp m)
                (or (equal (fn-cat-live-last g b c) 0)
                    (< (fn-cat-live-last g b c) m)))
           (not (fn-cat-live-numberp g m c)))
  :hints (("Goal" :induct (fn-cpl-down-ind b)
           :expand ((fn-cat-live-last g b c))
           :in-theory (disable fn-cat-live-numberp))))

(defthm fn-cpl-first-from-gap
  (implies (and (fn-cat-live-numberp g j c) (natp j) (natp m) (<= m j)
                (natp top) (<= j top)
                (or (equal (fn-cat-live-last g (- j 1) c) 0)
                    (< (fn-cat-live-last g (- j 1) c) m)))
           (equal (fn-cat-live-first g m top c) j))
  :hints (("Goal" :induct (fn-cat-live-first g m top c)
           :in-theory (disable fn-cat-live-numberp fn-cpl-last-from-gap))
          (and (consp (car id)) (equal (len (car id)) 2)
               '(:use ((:instance fn-cpl-last-skips (b (- j 1))))))))

(defun fn-cpl-next-of (g k c)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cat-live-first g (+ 1 (nfix k)) (fn-cat-group-high g c) c))

(defun fn-cpl-prev-of (g k c)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cat-live-last g (- (nfix k) 1) c))

(defun fn-cpl-goodp (dir x v c)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp x) (natp (cdr x))
       (fn-cat-live-numberp (car x) (cdr x) c)
       (equal v (if dir (fn-cpl-next-of (car x) (cdr x) c) (fn-cpl-prev-of (car x) (cdr x) c)))))

(defun-sk fn-cpl-okp (dir tab c)
  (forall x (implies (consp (hons-assoc-equal x tab))
                     (fn-cpl-goodp dir x (cdr (hons-assoc-equal x tab)) c))))

(in-theory (disable fn-cpl-okp fn-cpl-okp-necc))

(defthm fn-cpl-okp-nil (fn-cpl-okp dir nil c)
  :hints (("Goal" :in-theory (enable fn-cpl-okp))))

(defthm fn-cpl-lookup-of-remove
  (equal (hons-assoc-equal x (hons-remove-assoc k tab))
         (if (equal x k) nil (hons-assoc-equal x tab))))

(defun fn-cpl-cplan (groups livep c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (let* ((g (car groups)) (n (+ 1 (fn-cat-group-high g c))))
        (if (and livep (<= n *fn-nntp-max-article-number*))
            (cons (list g n (fn-cat-live-last g (fn-cat-group-high g c) c))
                  (fn-cpl-cplan (cdr groups) livep c))
          (fn-cpl-cplan (cdr groups) livep c)))
    nil))

(defun fn-cpl-link (dir plan tab)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp plan)
      (let* ((e (car plan)) (g (car e)) (n (cadr e)) (hi (caddr e))
             (tab (if dir
                      (let ((tab (if (posp hi) (cons (cons (cons g hi) n) tab) tab)))
                        (cons (cons (cons g n) 0) tab))
                    (cons (cons (cons g n) hi) tab))))
        (fn-cpl-link dir (cdr plan) tab))
    tab))

(defun fn-cpl-wplan (pairs r c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (let* ((p (car pairs)) (g (car p)) (k (cdr p)))
        (if (and (consp p) (equal (fn-cat-number-seq g k c 0) r)
                 (fn-cat-live-rowp g k (nth r c)))
            (cons (list g k (fn-cpl-prev-of g k c) (fn-cpl-next-of g k c))
                  (fn-cpl-wplan (cdr pairs) r c))
          (fn-cpl-wplan (cdr pairs) r c)))
    nil))

(defun fn-cpl-unlink (dir plan tab)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp plan)
      (let* ((e (car plan)) (g (car e)) (k (cadr e)) (p (caddr e)) (n (cadddr e))
             (tab (hons-remove-assoc (cons g k) tab))
             (tab (if dir
                      (if (posp p) (cons (cons (cons g p) n) tab) tab)
                    (if (posp n) (cons (cons (cons g n) p) tab) tab))))
        (fn-cpl-unlink dir (cdr plan) tab))
    tab))

(defun fn-cpl-bad (dir x plan)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp plan)
      (let* ((e (car plan)) (g (car e)) (k (cadr e)) (p (caddr e)) (n (cadddr e)))
        (or (equal x (cons g k))
            (and dir (posp p) (equal x (cons g p)))
            (and (not dir) (posp n) (equal x (cons g n)))
            (fn-cpl-bad dir x (cdr plan))))
    nil))

(defun-sk fn-cpl-winv (dir tab plan c c2)
  (forall x (implies (consp (hons-assoc-equal x tab))
                     (or (fn-cpl-goodp dir x (cdr (hons-assoc-equal x tab)) c2)
                         (and (fn-cpl-bad dir x plan)
                              (fn-cpl-goodp dir x (cdr (hons-assoc-equal x tab)) c))))))

(in-theory (disable fn-cpl-winv fn-cpl-winv-necc))

(defthm fn-cpl-winv-end
  (implies (fn-cpl-winv dir tab nil c c2) (fn-cpl-okp dir tab c2))
  :hints (("Goal" :in-theory (enable fn-cpl-okp)
           :use ((:instance fn-cpl-winv-necc (plan nil) (x (fn-cpl-okp-witness dir tab c2)))))))

(defthm fn-cpl-live-below-high
  (implies (and (fn-cat-rowsp c) (fn-cat-live-numberp g k c)) (<= k (fn-cat-group-high g c)))
  :rule-classes (:linear :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-cat-live-numberp)
           :use ((:instance fn-cpl-number-seq-above-high (n k) (i 0))))))

(defun fn-cpl-wentry-okp (e r c)
  (declare (xargs :guard t :verify-guards nil))
  (let ((g (car e)) (k (cadr e)))
    (and (true-listp e) (equal (len e) 4)
         (posp k) (fn-cat-live-numberp g k c)
         (equal (fn-ctg-kstar g c r) k)
         (equal (caddr e) (fn-cpl-prev-of g k c))
         (equal (cadddr e) (fn-cpl-next-of g k c)))))

(defun fn-cpl-wplan-okp (plan r c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp plan)
      (and (fn-cpl-wentry-okp (car plan) r c) (fn-cpl-wplan-okp (cdr plan) r c))
    t))

(defthm fn-cpl-wplan-okp-of-wplan
  (implies (and (natp r) (< r (len c)))
           (fn-cpl-wplan-okp (fn-cpl-wplan pairs r c) r c))
  :hints (("Goal" :in-theory (enable fn-ctg-kstar fn-cat-live-numberp))))

(defthm fn-cpl-g2-prev-of-next
  (implies (and (fn-cpl-wentry-okp e r c) (fn-cat-rowsp c) (natp r) (< r (len c))
                (null (fn-held-withdrawn (nth r c))) (posp (cadddr e)))
           (fn-cpl-goodp nil (cons (car e) (cadddr e)) (caddr e) (fn-cat-mark-withdrawn r v by c)))
  :hints (("Goal" :in-theory (disable fn-cat-live-numberp fn-cat-mark-withdrawn fn-cpl-mark-withdrawn-is-update
                                      fn-ctg-kstar fn-cpl-first-from-gap)
           :use ((:instance fn-cpl-live-first-bounds (g (car e)) (k (+ 1 (cadr e)))
                            (top (fn-cat-group-high (car e) c)))
                 (:instance fn-cpl-last-from-gap (g (car e)) (j (cadr e)) (m (- (cadddr e) 1))
                            (top (fn-cat-group-high (car e) c)))))))

(defthm fn-cpl-g1-next-of-prev
  (implies (and (fn-cat-rowsp c) (natp r) (< r (len c))
                (null (fn-held-withdrawn (nth r c)))
                (posp k) (fn-cat-live-numberp g k c) (equal (fn-ctg-kstar g c r) k)
                (posp (fn-cat-live-last g (- k 1) c)))
           (fn-cpl-goodp t (cons g (fn-cat-live-last g (- k 1) c)) (fn-cpl-next-of g k c)
                         (fn-cat-mark-withdrawn r v by c)))
  :hints (("Goal" :in-theory (union-theories '(fn-cpl-goodp fn-cpl-next-of natp posp nfix car-cons cdr-cons (:type-prescription fn-cat-group-high))
                                             (theory 'minimal-theory))
           :use ((:instance fn-cpl-live-last-bounds (k (- k 1)))
                 (:instance fn-cpl-live-withdrawn (j (fn-cat-live-last g (- k 1) c)))
                 (:instance fn-cpl-high-withdrawn)
                 (:instance fn-cpl-live-types (k (- k 1)) (top 0))
                 (:instance fn-cpl-live-first-withdrawn (j (+ 1 (fn-cat-live-last g (- k 1) c)))
                            (top (fn-cat-group-high g c)))
                 (:instance fn-cpl-live-below-high)
                 (:instance fn-cpl-first-from-gap (j k) (m (+ 1 (fn-cat-live-last g (- k 1) c)))
                            (top (fn-cat-group-high g c)))))))

(defthm fn-cpl-assoc-member-cons
  (implies (consp (fn-cat-assoc g xs)) (member-equal (cons g (cdr (fn-cat-assoc g xs))) xs))
  :hints (("Goal" :in-theory (enable fn-cat-assoc))))

(defthm fn-cpl-assoc-shape
  (implies (consp (fn-cat-assoc g xs)) (equal (car (fn-cat-assoc g xs)) g))
  :hints (("Goal" :in-theory (enable fn-cat-assoc))))

(defthm fn-cpl-bad-of-member
  (implies (and (member-equal (cons g k) pairs)
                (equal (fn-cat-number-seq g k c 0) r)
                (fn-cat-live-rowp g k (nth r c)))
           (and (fn-cpl-bad dir (cons g k) (fn-cpl-wplan pairs r c))
                (implies (and dir (posp (fn-cpl-prev-of g k c)))
                         (fn-cpl-bad dir (cons g (fn-cpl-prev-of g k c)) (fn-cpl-wplan pairs r c)))
                (implies (and (not dir) (posp (fn-cpl-next-of g k c)))
                         (fn-cpl-bad dir (cons g (fn-cpl-next-of g k c)) (fn-cpl-wplan pairs r c)))))
  :hints (("Goal" :in-theory (disable fn-cpl-prev-of fn-cpl-next-of fn-cat-live-rowp fn-cat-number-seq))))

(defthm fn-cpl-kstar-member
  (implies (posp (fn-ctg-kstar g c r))
           (and (member-equal (cons g (fn-ctg-kstar g c r)) (fn-held-numbers (nth r c)))
                (equal (fn-cat-number-seq g (fn-ctg-kstar g c r) c 0) r)))
  :hints (("Goal" :in-theory (e/d (fn-ctg-kstar fn-held-number-in) (fn-cat-assoc fn-cat-number-seq))
           :use ((:instance fn-cpl-assoc-member-cons (xs (fn-held-numbers (nth r c))))
                 (:instance fn-cpl-assoc-shape (xs (fn-held-numbers (nth r c))))))))

(defthm fn-cpl-kstar-live-rowp
  (implies (and (posp (fn-ctg-kstar g c r)) (fn-cat-live-numberp g (fn-ctg-kstar g c r) c))
           (fn-cat-live-rowp g (fn-ctg-kstar g c r) (nth r c)))
  :hints (("Goal" :in-theory (e/d (fn-cat-live-numberp) (fn-ctg-kstar fn-cat-live-rowp fn-cat-number-seq))
           :use fn-cpl-kstar-member)))

(defthm fn-cpl-changed-is-bad
  (implies (and (fn-cat-rowsp c) (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c)))
                (fn-cpl-goodp dir x v c)
                (not (fn-cpl-goodp dir x v (fn-cat-mark-withdrawn r w by c))))
           (fn-cpl-bad dir x (fn-cpl-wplan (fn-held-numbers (nth r c)) r c)))
  :hints (("Goal" :in-theory (e/d (fn-cpl-goodp fn-cpl-next-of fn-cpl-prev-of)
                                  (fn-cat-live-first fn-cat-live-last fn-cat-live-numberp fn-cat-live-rowp
                                   fn-cat-number-seq fn-ctg-kstar fn-cat-mark-withdrawn
                                   fn-cpl-mark-withdrawn-is-update fn-cpl-last-from-gap fn-cpl-first-from-gap
                                   fn-cpl-wplan fn-cpl-bad-of-member fn-cpl-live-first-withdrawn
                                   fn-cpl-live-last-withdrawn fn-cpl-live-withdrawn))
           :use ((:instance fn-cpl-live-withdrawn (j (cdr x)) (g (car x)) (v w))
                 (:instance fn-cpl-high-withdrawn (g (car x)) (v w))
                 (:instance fn-cpl-live-first-withdrawn (g (car x)) (v w) (j (+ 1 (cdr x)))
                            (top (fn-cat-group-high (car x) c)))
                 (:instance fn-cpl-live-last-withdrawn (g (car x)) (v w) (j (- (cdr x) 1)))
                 (:instance fn-cpl-kstar-member (g (car x)))
                 (:instance fn-cpl-kstar-live-rowp (g (car x)))
                 (:instance fn-cpl-bad-of-member (g (car x)) (k (fn-ctg-kstar (car x) c r))
                            (pairs (fn-held-numbers (nth r c))))
                 (:instance fn-cpl-live-first-bounds (g (car x)) (k (+ 1 (cdr x)))
                            (top (fn-cat-group-high (car x) c)))
                 (:instance fn-cpl-live-last-bounds (g (car x)) (k (- (cdr x) 1)))
                 (:instance fn-cpl-last-from-gap (g (car x)) (j (cdr x)) (m (- (fn-ctg-kstar (car x) c r) 1))
                            (top (fn-cat-group-high (car x) c)))
                 (:instance fn-cpl-first-from-gap (g (car x)) (j (cdr x)) (m (+ 1 (fn-ctg-kstar (car x) c r)))
                            (top (fn-cat-group-high (car x) c)))
                 (:instance fn-cpl-live-below-high (g (car x)) (k (cdr x)))))))

(defthm fn-cpl-goodp-dir
  (implies (syntaxp (not (quotep dir)))
           (equal (fn-cpl-goodp dir x v c)
                  (if dir (fn-cpl-goodp t x v c) (fn-cpl-goodp nil x v c))))
  :hints (("Goal" :in-theory (enable fn-cpl-goodp))))

(defthm fn-cpl-winv-init
  (implies (and (fn-cat-rowsp c) (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c)))
                (fn-cpl-okp dir tab c))
           (fn-cpl-winv dir tab (fn-cpl-wplan (fn-held-numbers (nth r c)) r c) c
                        (fn-cat-mark-withdrawn r w by c)))
  :hints (("Goal" :in-theory (union-theories '(fn-cpl-winv) (theory 'minimal-theory))
           :use ((:instance fn-cpl-changed-is-bad
                            (x (fn-cpl-winv-witness dir tab (fn-cpl-wplan (fn-held-numbers (nth r c)) r c) c
                                                    (fn-cat-mark-withdrawn r w by c)))
                            (v (cdr (hons-assoc-equal (fn-cpl-winv-witness dir tab (fn-cpl-wplan (fn-held-numbers (nth r c)) r c) c
                                                    (fn-cat-mark-withdrawn r w by c)) tab))))
                 (:instance fn-cpl-okp-necc
                            (x (fn-cpl-winv-witness dir tab (fn-cpl-wplan (fn-held-numbers (nth r c)) r c) c
                                                    (fn-cat-mark-withdrawn r w by c))))))))

(defthm fn-cpl-g2-prev-of-next-v
  (implies (and (fn-cat-rowsp c) (natp r) (< r (len c))
                (null (fn-held-withdrawn (nth r c)))
                (posp k) (fn-cat-live-numberp g k c) (equal (fn-ctg-kstar g c r) k)
                (posp (fn-cpl-next-of g k c)))
           (fn-cpl-goodp nil (cons g (fn-cpl-next-of g k c)) (fn-cat-live-last g (- k 1) c)
                         (fn-cat-mark-withdrawn r v by c)))
  :hints (("Goal" :use ((:instance fn-cpl-g2-prev-of-next (e (list g k (fn-cpl-prev-of g k c) (fn-cpl-next-of g k c)))))
           :in-theory (e/d (fn-cpl-wentry-okp) (fn-cpl-goodp fn-cpl-next-of fn-cat-live-numberp fn-ctg-kstar
                                                fn-cat-mark-withdrawn fn-cpl-mark-withdrawn-is-update)))))

(defun fn-cpl-wstep (dir g k p n tab)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tab (hons-remove-assoc (cons g k) tab)))
    (if dir
        (if (posp p) (cons (cons (cons g p) n) tab) tab)
      (if (posp n) (cons (cons (cons g n) p) tab) tab))))

(defthm fn-cpl-lookup-of-wstep
  (equal (hons-assoc-equal x (fn-cpl-wstep dir g k p n tab))
         (cond ((and dir (posp p) (equal x (cons g p))) (cons x n))
               ((and (not dir) (posp n) (equal x (cons g n))) (cons x p))
               ((equal x (cons g k)) nil)
               (t (hons-assoc-equal x tab)))))

(in-theory (disable fn-cpl-wstep))

(defthm fn-cpl-winv-step
  (implies (and (fn-cat-rowsp c) (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c)))
                (posp k) (fn-cat-live-numberp g k c) (equal (fn-ctg-kstar g c r) k)
                (equal p (fn-cpl-prev-of g k c)) (equal n (fn-cpl-next-of g k c))
                (fn-cpl-winv dir tab (cons (list g k p n) rest) c (fn-cat-mark-withdrawn r w by c)))
           (fn-cpl-winv dir (fn-cpl-wstep dir g k p n tab) rest c (fn-cat-mark-withdrawn r w by c)))
  :hints (("Goal" :in-theory (union-theories '(fn-cpl-goodp-dir fn-cpl-winv fn-cpl-lookup-of-wstep fn-cpl-bad posp
                                               car-cons cdr-cons fn-cpl-prev-of nfix)
                                             (theory 'minimal-theory))
           :use ((:instance fn-cpl-winv-necc (plan (cons (list g k p n) rest)) (c2 (fn-cat-mark-withdrawn r w by c))
                            (x (fn-cpl-winv-witness dir (fn-cpl-wstep dir g k p n tab) rest c
                                                    (fn-cat-mark-withdrawn r w by c))))
                 (:instance fn-cpl-g1-next-of-prev (v w))
                 (:instance fn-cpl-g2-prev-of-next-v (v w))))))

(defthm fn-cpl-unlink-is-wsteps
  (equal (fn-cpl-unlink dir plan tab)
         (if (consp plan)
             (fn-cpl-unlink dir (cdr plan)
                            (fn-cpl-wstep dir (car (car plan)) (cadr (car plan)) (caddr (car plan))
                                          (cadddr (car plan)) tab))
           tab))
  :rule-classes ((:definition :controller-alist ((fn-cpl-unlink nil t nil))))
  :hints (("Goal" :in-theory (enable fn-cpl-wstep))))

(defthm fn-cpl-list4
  (implies (and (true-listp e) (equal (len e) 4))
           (equal (list (car e) (cadr e) (caddr e) (cadddr e)) e))
  :hints (("Goal" :expand ((len e) (len (cdr e)) (len (cddr e)) (len (cdddr e)) (len (cddddr e))))))

(defthm fn-cpl-winv-end-atom
  (implies (and (not (consp plan)) (fn-cpl-winv dir tab plan c c2)) (fn-cpl-okp dir tab c2))
  :hints (("Goal" :in-theory (enable fn-cpl-okp)
           :use ((:instance fn-cpl-winv-necc (x (fn-cpl-okp-witness dir tab c2)))))))

(defun fn-cpl-unlink-ind (dir plan tab)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp plan)
      (fn-cpl-unlink-ind dir (cdr plan)
                         (fn-cpl-wstep dir (car (car plan)) (cadr (car plan)) (caddr (car plan))
                                       (cadddr (car plan)) tab))
    tab))

(defthm fn-cpl-unlink-okp
  (implies (and (fn-cat-rowsp c) (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c)))
                (fn-cpl-wplan-okp plan r c)
                (fn-cpl-winv dir tab plan c (fn-cat-mark-withdrawn r w by c)))
           (fn-cpl-okp dir (fn-cpl-unlink dir plan tab) (fn-cat-mark-withdrawn r w by c)))
  :hints (("Goal" :induct (fn-cpl-unlink-ind dir plan tab)
           :in-theory (union-theories '((:induction fn-cpl-unlink-ind) fn-cpl-unlink-is-wsteps fn-cpl-wplan-okp fn-cpl-wentry-okp fn-cpl-list4 cons-car-cdr fn-cpl-winv-end-atom
                                        car-cons cdr-cons)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/1" :use ((:instance fn-cpl-winv-step (g (car (car plan))) (k (cadr (car plan)))
                                           (p (caddr (car plan))) (n (cadddr (car plan))) (rest (cdr plan)))))))

(defthm fn-cpl-okp-of-withdraw
  (implies (and (fn-cat-rowsp c) (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c)))
                (fn-cpl-okp dir tab c))
           (fn-cpl-okp dir (fn-cpl-unlink dir (fn-cpl-wplan (fn-held-numbers (nth r c)) r c) tab)
                       (fn-cat-mark-withdrawn r w by c)))
  :hints (("Goal" :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-cpl-unlink-okp (plan (fn-cpl-wplan (fn-held-numbers (nth r c)) r c)))
                 (:instance fn-cpl-winv-init)
                 (:instance fn-cpl-wplan-okp-of-wplan (pairs (fn-held-numbers (nth r c))))))))

; KEYSTONE (withdrawal): unlinking the withdrawn row's live numbers --
; removing (g . k), pointing its PREV's NEXT past it and its NEXT's PREV
; below it -- keeps every entry good over the withdrawn rows.
; fn-cpl-okp-of-withdraw above.

; -----------------------------------------------------------------------------
; 3. The commit.  The plan (fn-cpl-cplan) names, per group of the committed
; row whose new number n = high + 1 is live, (g n hi) with hi the group's
; live high before the commit; the link puts (g . n) with no NEXT and hi
; as its PREV, and points hi's NEXT at n.  The loop invariant's bad set is
; the old live highs' NEXT entries (0 before, n after); PREV has none.

(defthm fn-cpl-high-of-commit
  (equal (fn-cat-group-high g (append c (list (fn-cat-assign h c))))
         (if (member-equal g (fn-record-groups h))
             (+ 1 (fn-cat-group-high g c))
           (fn-cat-group-high g c))))

(defthm fn-cpl-first-past-last
  (implies (natp top)
           (equal (fn-cat-live-first g (+ 1 (fn-cat-live-last g top c)) top c) 0))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-cat-live-numberp fn-cpl-first-from-gap fn-cpl-last-from-gap
                               fn-cat-live-first fn-cat-live-last fn-cpl-live-first-bounds fn-cpl-last-skips)
           :use ((:instance fn-cpl-live-first-bounds (k (+ 1 (fn-cat-live-last g top c))))
                 (:instance fn-cpl-last-skips (b top) (m (fn-cat-live-first g (+ 1 (fn-cat-live-last g top c)) top c)))))))

(defun fn-cpl-centry-okp (e h c)
  (declare (xargs :guard t :verify-guards nil))
  (let ((g (car e)) (n (cadr e)) (hi (caddr e)))
    (and (true-listp e) (equal (len e) 3)
         (member-equal g (fn-record-groups h))
         (equal n (+ 1 (fn-cat-group-high g c)))
         (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h))
         (<= n *fn-nntp-max-article-number*)
         (equal hi (fn-cat-live-last g (fn-cat-group-high g c) c)))))

(defun fn-cpl-cplan-okp (plan h c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp plan)
      (and (fn-cpl-centry-okp (car plan) h c) (fn-cpl-cplan-okp (cdr plan) h c))
    t))

(defthm fn-cpl-cplan-okp-of-cplan-gen
  (implies (and (subsetp-equal groups (fn-record-groups h))
                (equal livep (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h)))))
           (fn-cpl-cplan-okp (fn-cpl-cplan groups livep c) h c))
  :hints (("Goal" :in-theory (disable fn-cat-live-last fn-scat-msgid-idp))))

(defthm fn-cpl-cplan-okp-of-cplan
  (fn-cpl-cplan-okp (fn-cpl-cplan (fn-record-groups h)
                                  (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h)))
                                  c)
                    h c)
  :hints (("Goal" :use ((:instance fn-cpl-cplan-okp-of-cplan-gen (groups (fn-record-groups h))
                                   (livep (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h))))))
           :in-theory (disable fn-cpl-cplan-okp-of-cplan-gen fn-cpl-cplan fn-cpl-cplan-okp))))

(defthm fn-cpl-centry-new-live
  (implies (and (fn-cpl-centry-okp e h c) (fn-cat-rowsp c))
           (fn-cat-live-numberp (car e) (cadr e) (append c (list (fn-cat-assign h c)))))
  :hints (("Goal" :in-theory (disable fn-cat-live-numberp fn-cat-assign fn-scat-msgid-idp fn-cat-live-last))))

(defthm fn-cpl-cgood-new-next
  (implies (and (fn-cpl-centry-okp e h c) (fn-cat-rowsp c))
           (fn-cpl-goodp t (cons (car e) (cadr e)) 0 (append c (list (fn-cat-assign h c)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpl-next-of) (fn-cat-live-numberp fn-cat-assign fn-scat-msgid-idp fn-cat-live-last
                                             fn-cat-live-first fn-cpl-centry-okp))
           :use fn-cpl-centry-new-live
           :expand ((fn-cpl-centry-okp e h c)))))

(defthm fn-cpl-cgood-new-prev
  (implies (and (fn-cpl-centry-okp e h c) (fn-cat-rowsp c))
           (fn-cpl-goodp nil (cons (car e) (cadr e)) (caddr e) (append c (list (fn-cat-assign h c)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpl-prev-of) (fn-cat-live-numberp fn-cat-assign fn-scat-msgid-idp fn-cat-live-last
                                             fn-cat-live-first fn-cpl-centry-okp))
           :use fn-cpl-centry-new-live
           :expand ((fn-cpl-centry-okp e h c)))))

(defthm fn-cpl-cgood-hi-next
  (implies (and (fn-cpl-centry-okp e h c) (fn-cat-rowsp c) (posp (caddr e)))
           (fn-cpl-goodp t (cons (car e) (caddr e)) (cadr e) (append c (list (fn-cat-assign h c)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpl-next-of) (fn-cat-live-numberp fn-cat-assign fn-scat-msgid-idp fn-cat-live-last
                                             fn-cat-live-first fn-cpl-centry-okp))
           :use (fn-cpl-centry-new-live
                 (:instance fn-cpl-live-last-bounds (g (car e)) (k (fn-cat-group-high (car e) c)))
                 (:instance fn-cpl-live-below-high (g (car e)) (k (caddr e)))
                 (:instance fn-cpl-live-append-other (g (car e)) (k (caddr e)))
                 (:instance fn-cpl-live-first-top (g (car e)) (k (+ 1 (caddr e))) (top (fn-cat-group-high (car e) c))
                            (c (append c (list (fn-cat-assign h c)))))
                 (:instance fn-cpl-live-first-append (g (car e)) (k (+ 1 (caddr e))) (top (fn-cat-group-high (car e) c)))
                 (:instance fn-cpl-first-past-last (g (car e)) (top (fn-cat-group-high (car e) c))))
           :expand ((fn-cpl-centry-okp e h c)))))

(defun fn-cpl-cbad (x plan)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp plan)
      (let* ((e (car plan)) (g (car e)) (hi (caddr e)))
        (or (and (posp hi) (equal x (cons g hi)))
            (fn-cpl-cbad x (cdr plan))))
    nil))

(defthm fn-cpl-cbad-of-cplan
  (implies (and (member-equal g groups) livep
                (<= (+ 1 (fn-cat-group-high g c)) *fn-nntp-max-article-number*)
                (posp (fn-cat-live-last g (fn-cat-group-high g c) c)))
           (fn-cpl-cbad (cons g (fn-cat-live-last g (fn-cat-group-high g c) c)) (fn-cpl-cplan groups livep c)))
  :hints (("Goal" :in-theory (disable fn-cat-live-last))))

(defthm fn-cpl-cchanged-is-bad
  (implies (and (fn-cat-rowsp c)
                (fn-cpl-goodp dir x v c)
                (not (fn-cpl-goodp dir x v (append c (list (fn-cat-assign h c))))))
           (and dir
                (fn-cpl-cbad x (fn-cpl-cplan (fn-record-groups h)
                                             (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h)))
                                             c))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpl-goodp fn-cpl-next-of fn-cpl-prev-of)
                           (fn-cat-live-numberp fn-cat-assign fn-scat-msgid-idp fn-cat-live-last fn-cat-live-first
                            fn-cpl-cplan fn-cpl-cbad fn-cpl-live-append-other fn-cpl-live-append-new
                            fn-cpl-live-last-append fn-cpl-live-first-append fn-cpl-live-first-top
                            fn-cpl-last-from-gap fn-cpl-first-from-gap fn-cpl-cbad-of-cplan))
           :cases ((member-equal (car x) (fn-record-groups h)))
           :use ((:instance fn-cpl-live-below-high (g (car x)) (k (cdr x)))
                 (:instance fn-cpl-live-append-other (g (car x)) (k (cdr x)))
                 (:instance fn-cpl-live-last-append (g (car x)) (k (- (cdr x) 1)))
                 (:instance fn-cpl-live-first-append (g (car x)) (k (+ 1 (cdr x))) (top (fn-cat-group-high (car x) c)))
                 (:instance fn-cpl-live-first-top (g (car x)) (k (+ 1 (cdr x))) (top (fn-cat-group-high (car x) c))
                            (c (append c (list (fn-cat-assign h c)))))
                 (:instance fn-cpl-live-append-new (g (car x)) (n (+ 1 (fn-cat-group-high (car x) c))))
                 (:instance fn-cpl-last-from-gap (g (car x)) (j (cdr x)) (m (fn-cat-group-high (car x) c))
                            (top (fn-cat-group-high (car x) c)))
                 (:instance fn-cpl-cbad-of-cplan (g (car x)) (groups (fn-record-groups h))
                            (livep (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h)))))))))

(defun-sk fn-cpl-cinv (dir tab plan c c2)
  (forall x (implies (consp (hons-assoc-equal x tab))
                     (or (fn-cpl-goodp dir x (cdr (hons-assoc-equal x tab)) c2)
                         (and dir (fn-cpl-cbad x plan)
                              (fn-cpl-goodp dir x (cdr (hons-assoc-equal x tab)) c))))))

(in-theory (disable fn-cpl-cinv fn-cpl-cinv-necc))

(defthm fn-cpl-cinv-init
  (implies (and (fn-cat-rowsp c) (fn-cpl-okp dir tab c))
           (fn-cpl-cinv dir tab
                        (fn-cpl-cplan (fn-record-groups h)
                                      (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h)))
                                      c)
                        c (append c (list (fn-cat-assign h c)))))
  :hints (("Goal" :in-theory (union-theories '(fn-cpl-cinv) (theory 'minimal-theory))
           :use ((:instance fn-cpl-cchanged-is-bad
                            (x (fn-cpl-cinv-witness dir tab
                                                    (fn-cpl-cplan (fn-record-groups h)
                                                                  (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h)))
                                                                  c)
                                                    c (append c (list (fn-cat-assign h c)))))
                            (v (cdr (hons-assoc-equal
                                     (fn-cpl-cinv-witness dir tab
                                                          (fn-cpl-cplan (fn-record-groups h)
                                                                        (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h)))
                                                                        c)
                                                          c (append c (list (fn-cat-assign h c))))
                                     tab))))
                 (:instance fn-cpl-okp-necc
                            (x (fn-cpl-cinv-witness dir tab
                                                    (fn-cpl-cplan (fn-record-groups h)
                                                                  (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h)))
                                                                  c)
                                                    c (append c (list (fn-cat-assign h c))))))))))

(defun fn-cpl-lstep (dir g n hi tab)
  (declare (xargs :guard t :verify-guards nil))
  (if dir
      (cons (cons (cons g n) 0) (if (posp hi) (cons (cons (cons g hi) n) tab) tab))
    (cons (cons (cons g n) hi) tab)))

(defthm fn-cpl-lookup-of-lstep
  (equal (hons-assoc-equal x (fn-cpl-lstep dir g n hi tab))
         (cond ((equal x (cons g n)) (cons x (if dir 0 hi)))
               ((and dir (posp hi) (equal x (cons g hi))) (cons x n))
               (t (hons-assoc-equal x tab)))))

(in-theory (disable fn-cpl-lstep))

(defthm fn-cpl-cinv-step
  (implies (and (fn-cat-rowsp c) (fn-cpl-centry-okp (list g n hi) h c)
                (fn-cpl-cinv dir tab (cons (list g n hi) rest) c (append c (list (fn-cat-assign h c)))))
           (fn-cpl-cinv dir (fn-cpl-lstep dir g n hi tab) rest c (append c (list (fn-cat-assign h c)))))
  :hints (("Goal" :in-theory (union-theories '(fn-cpl-goodp-dir fn-cpl-cinv fn-cpl-lookup-of-lstep fn-cpl-cbad
                                               car-cons cdr-cons)
                                             (theory 'minimal-theory))
           :use ((:instance fn-cpl-cinv-necc (plan (cons (list g n hi) rest)) (c2 (append c (list (fn-cat-assign h c))))
                            (x (fn-cpl-cinv-witness dir (fn-cpl-lstep dir g n hi tab) rest c
                                                    (append c (list (fn-cat-assign h c))))))
                 (:instance fn-cpl-cgood-new-next (e (list g n hi)))
                 (:instance fn-cpl-cgood-new-prev (e (list g n hi)))
                 (:instance fn-cpl-cgood-hi-next (e (list g n hi)))))))

(defthm fn-cpl-link-is-lsteps
  (equal (fn-cpl-link dir plan tab)
         (if (consp plan)
             (fn-cpl-link dir (cdr plan)
                          (fn-cpl-lstep dir (car (car plan)) (cadr (car plan)) (caddr (car plan)) tab))
           tab))
  :rule-classes ((:definition :controller-alist ((fn-cpl-link nil t nil))))
  :hints (("Goal" :in-theory (enable fn-cpl-lstep))))

(defthm fn-cpl-list3
  (implies (and (true-listp e) (equal (len e) 3))
           (equal (list (car e) (cadr e) (caddr e)) e))
  :hints (("Goal" :expand ((len e) (len (cdr e)) (len (cddr e)) (len (cdddr e))))))

(defthm fn-cpl-cinv-end-atom
  (implies (and (not (consp plan)) (fn-cpl-cinv dir tab plan c c2)) (fn-cpl-okp dir tab c2))
  :hints (("Goal" :in-theory (enable fn-cpl-okp)
           :use ((:instance fn-cpl-cinv-necc (x (fn-cpl-okp-witness dir tab c2)))))))

(defun fn-cpl-link-ind (dir plan tab)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp plan)
      (fn-cpl-link-ind dir (cdr plan)
                       (fn-cpl-lstep dir (car (car plan)) (cadr (car plan)) (caddr (car plan)) tab))
    tab))

(defthm fn-cpl-link-okp
  (implies (and (fn-cat-rowsp c) (fn-cpl-cplan-okp plan h c)
                (fn-cpl-cinv dir tab plan c (append c (list (fn-cat-assign h c)))))
           (fn-cpl-okp dir (fn-cpl-link dir plan tab) (append c (list (fn-cat-assign h c)))))
  :hints (("Goal" :induct (fn-cpl-link-ind dir plan tab)
           :in-theory (union-theories '((:induction fn-cpl-link-ind) fn-cpl-link-is-lsteps fn-cpl-cplan-okp
                                        fn-cpl-centry-okp fn-cpl-list3 fn-cpl-cinv-end-atom car-cons cdr-cons cons-car-cdr)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/1" :use ((:instance fn-cpl-cinv-step (g (car (car plan))) (n (cadr (car plan)))
                                           (hi (caddr (car plan))) (rest (cdr plan)))))))

; KEYSTONE (commit): linking the committed row's new live numbers --
; (g . n) a live number with no NEXT and the group's live high as its
; PREV, the old live high's NEXT pointed at n -- keeps every entry good
; over the appended rows.
(defthm fn-cpl-okp-of-commit
  (implies (and (fn-cat-rowsp c) (fn-cpl-okp dir tab c))
           (fn-cpl-okp dir
                       (fn-cpl-link dir (fn-cpl-cplan (fn-record-groups h)
                                                      (and (null (fn-held-withdrawn h))
                                                           (fn-scat-msgid-idp (fn-record-msgid h)))
                                                      c)
                                    tab)
                       (append c (list (fn-cat-assign h c)))))
  :hints (("Goal" :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-cpl-link-okp
                            (plan (fn-cpl-cplan (fn-record-groups h)
                                                (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h)))
                                                c)))
                 fn-cpl-cinv-init
                 fn-cpl-cplan-okp-of-cplan))))

; -----------------------------------------------------------------------------
; 4. A redecision keeps every row's keys and withdrawal: no liveness moves.

(defthm fn-cpl-live-rowp-with-context
  (equal (fn-cat-live-rowp g k (fn-held-with-context h ctx))
         (fn-cat-live-rowp g k h))
  :hints (("Goal" :in-theory (e/d (fn-cat-live-rowp) (fn-scat-msgid-idp))
           :use ((:instance fn-cpl-number-in-same-keys (h1 (fn-held-with-context h ctx)) (h2 h))))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-held-with-context) (fn-scat-msgid-idp))))))

(defthm fn-cpl-live-recontext
  (implies (and (natp r) (< r (len c)))
           (equal (fn-cat-live-numberp g k (update-nth r (fn-held-with-context (nth r c) ctx) c))
                  (fn-cat-live-numberp g k c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat-live-numberp)
                           (fn-cat-number-seq fn-scat-msgid-idp fn-cat-live-rowp fn-held-with-context))
           :use ((:instance fn-cpl-number-seq-update-nth (k r) (n k) (i 0) (h (fn-held-with-context (nth r c) ctx))))
           :cases ((equal (fn-cat-number-seq g k c 0) r)))))

(defthm fn-cpl-live-first-recontext
  (implies (and (natp r) (< r (len c)))
           (equal (fn-cat-live-first g k top (update-nth r (fn-held-with-context (nth r c) ctx) c))
                  (fn-cat-live-first g k top c)))
  :hints (("Goal" :induct (fn-cat-live-first g k top c)
           :in-theory (disable fn-cat-live-numberp fn-held-with-context))))

(defthm fn-cpl-live-last-recontext
  (implies (and (natp r) (< r (len c)))
           (equal (fn-cat-live-last g k (update-nth r (fn-held-with-context (nth r c) ctx) c))
                  (fn-cat-live-last g k c)))
  :hints (("Goal" :induct (fn-cat-live-last g k c)
           :in-theory (disable fn-cat-live-numberp fn-held-with-context))))

(defthm fn-cpl-goodp-recontext
  (implies (and (natp r) (< r (len c)))
           (equal (fn-cpl-goodp dir x v (update-nth r (fn-held-with-context (nth r c) ctx) c))
                  (fn-cpl-goodp dir x v c)))
  :hints (("Goal" :in-theory (e/d (fn-cpl-next-of fn-cpl-prev-of)
                                  (fn-cat-live-numberp fn-cat-live-first fn-cat-live-last fn-held-with-context))
           :use ((:instance fn-cpl-high-update-nth (k r) (g (car x)) (h (fn-held-with-context (nth r c) ctx)))))))

; A redecision changes no number's liveness: every entry stays good.
(defthm fn-cpl-okp-of-redecide
  (implies (and (natp r) (< r (len c)) (fn-cpl-okp dir tab c))
           (fn-cpl-okp dir tab (update-nth r (fn-held-with-context (nth r c) ctx) c)))
  :hints (("Goal" :in-theory (e/d (fn-cpl-okp) (fn-cpl-goodp fn-held-with-context))
           :use ((:instance fn-cpl-okp-necc
                            (x (fn-cpl-okp-witness dir tab (update-nth r (fn-held-with-context (nth r c) ctx) c))))))))

; -----------------------------------------------------------------------------
; 5. `fn-cpl-okp' as a check over the table's own keys (executable: the
; witnesses evaluate it).

(defun fn-cpl-all-goodp (dir keys tab c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp keys)
      (and (let ((x (car (car keys))))
             (or (not (consp (hons-assoc-equal x tab)))
                 (fn-cpl-goodp dir x (cdr (hons-assoc-equal x tab)) c)))
           (fn-cpl-all-goodp dir (cdr keys) tab c))
    t))

(defthm fn-cpl-all-goodp-of-okp
  (implies (fn-cpl-okp dir tab c) (fn-cpl-all-goodp dir keys tab c))
  :hints (("Goal" :induct (fn-cpl-all-goodp dir keys tab c)
           :in-theory (disable fn-cpl-goodp))
          ("Subgoal *1/2" :use ((:instance fn-cpl-okp-necc (x (car (car keys))))))))

(defthm fn-cpl-all-goodp-lookup
  (implies (and (fn-cpl-all-goodp dir keys tab c) (consp (hons-assoc-equal x keys))
                (consp (hons-assoc-equal x tab)))
           (fn-cpl-goodp dir x (cdr (hons-assoc-equal x tab)) c))
  :hints (("Goal" :induct (fn-cpl-all-goodp dir keys tab c) :in-theory (disable fn-cpl-goodp))))

(defthm fn-cpl-okp-is-all-goodp
  (equal (fn-cpl-okp dir tab c) (fn-cpl-all-goodp dir tab tab c))
  :hints (("Goal" :in-theory (e/d (fn-cpl-okp) (fn-cpl-goodp))
           :cases ((fn-cpl-okp dir tab c)))
          ("Subgoal 2" :use ((:instance fn-cpl-all-goodp-lookup (keys tab) (x (fn-cpl-okp-witness dir tab c)))))))

(in-theory (disable fn-cpl-okp-is-all-goodp))

