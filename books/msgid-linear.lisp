; fn: the Message-ID index as a LINEAR-HASHING table on pages (lane
; msgid-linear-hash, 2026-10-01; stage 7, the index part, of
; planning/design-store-representation-2026-10-01.md; Litwin, "Linear
; hashing: a new tool for file and table addressing", VLDB 1980; the
; literature scholar's D3).  Prefix fn-mpxl-.  This is the LOGICAL side;
; books/msgid-linear-exec is its executable twin (typed words on pages).
;
; The table of books/msgid-pages (fn-mpx-: home page = TAG mod the page
; count, one overflow page, every candidate confirmed against the row's
; exact Message-ID) grows by a NEXT GENERATION BUILT BESIDE IT
; (books/msgid-pages-exec `fn-mpxt-grow': double the pages, re-place every
; entry): a whole-table rebuild at each doubling, twice the pages resident
; while it runs.  Linear hashing replaces the rebuild with ONE PAGE SPLIT
; PER STEP under a split pointer carried on the root (D27: bounded work per
; scheduling step, never a rebuild):
;
;   ROOT: the round modulus N (= N0 * 2^level, N0 = 1 here) and the split
;   pointer S, 0 <= S < N.  The table has N + S pages.
;   ADDRESS: h = TAG mod N; if h < S (its page was split this round) then
;   TAG mod 2N, which is h or h + N; else h.  Always below N + S.
;   SPLIT: of the entries on page S and on its overflow page S + 1, those
;   whose address under mod 2N is N + S (the MOVERS) go to the NEW page
;   N + S, appended; S advances; at S = N the round ends (N doubles, S = 0).
;   Nothing else moves, no other page changes.
;   LOOKUP: the home page and, when the home page's OVERFLOW FLAG is set,
;   the page after it -- at most two pages, as before.  The writer sets
;   the flag when it places an entry on the page after a full home page,
;   and nothing clears it, so a split -- which empties slots of a page --
;   never orphans an overflow entry.  (The reader of books/msgid-pages-exec
;   scans the next page only while the home page is FULL; a page a split
;   has taken movers from is not full, and that reader would lose the
;   overflow entries of its home.  The flag is the one representation
;   change linear hashing needs.)
;
; Two refusals, each named, never a false absence: a PUT whose home page
; and overflow page are both full (`fn-mpxl-saturatedp': nil placed, the
; table unchanged -- the served POST's :mpx-saturated) and a SPLIT whose
; movers exceed a page (nil ok, the table unchanged; the executable twin
; marks the table stuck, as the rebuild that could not be built did).  Both
; are Poisson tails under an unpredictable key (books/msgid-pages-exec,
; section 6); the capacity is the page's slot count, `*fn-mpxl-cap*'.
;
; Layers, as in books/msgid-pages:
;   A. THE INDEXED-ACCESS REFINEMENT is reused unchanged:
;      `fn-mpx-confirm-is-the-records-for' (an ascending, in-range,
;      complete candidate list confirmed against the rows IS
;      `fn-cei-article-records-for').
;   B. THE LINEAR TABLE specialises it: `fn-mpxl-cands' (the home page's
;      seqs and, under the flag, the next page's, inserted ascending) is
;      ascending by construction, below the length under `fn-mpxl-okp' and
;      complete under `fn-mpxl-faithful'.  KEYSTONE
;      `fn-mpxl-records-is-the-records-for'.
;   C. THE WRITER AND THE SPLIT keep every candidate
;      (`fn-mpxl-put-keeps-candidate', `fn-mpxl-split-keeps-candidate':
;      stated on candidate membership for every tag, so every row model --
;      the history's here, the catalog's in the executable twin -- inherits
;      them), the put finds what it placed (`fn-mpxl-put-finds'), and both
;      preserve the faithful relation (`fn-mpxl-put-preserves-faithful',
;      KEYSTONE `fn-mpxl-split-preserves-faithful').
;
; A page is (FLAG . ENTRIES), an entry (TAG . SEQ), in slot order (the
; executable twin's page-entries); a table is (PAGES N S).  Candidates are
; built by sorted insertion (`fn-mpxl-ins'), so a page's order is
; immaterial: `fn-mpxl-seqs-member' characterises membership by the entry.

(in-package "ACL2")
(include-book "msgid-pages")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
(local (in-theory (disable (tau-system))))

; The slots of one 16 KiB page (two columns of 1,024 words each).
(defconst *fn-mpxl-cap* 1024)

; -----------------------------------------------------------------------------
; 0. The address.

; The address of TAG under round modulus N and split pointer S.
(defun fn-mpxl-addr (tag n s)
  (declare (xargs :guard (and (natp tag) (posp n) (natp s))))
  (let ((h (mod tag n)))
    (if (< h s) (mod tag (* 2 n)) h)))

;; `mod' stays closed in this book: its facts are the three below.
(local (defthm fn-mpxl-mod-natp
  (implies (and (natp x) (posp y)) (natp (mod x y)))
  :rule-classes (:rewrite :type-prescription)))
(local (in-theory (disable mod)))
(local (defthm fn-mpxl-mod-2
  (implies (natp k) (or (equal (mod k 2) 0) (equal (mod k 2) 1)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance mod-bounded-by-modulus (x k) (y 2))
                        (:instance fn-mpxl-mod-natp (x k) (y 2)))))))

(defthm fn-mpxl-addr-natp
  (implies (and (natp tag) (posp n))
           (natp (fn-mpxl-addr tag n s)))
  :rule-classes :type-prescription)

; TAG mod 2N is TAG mod N, or N more.
(defthm fn-mpxl-mod-double
  (implies (and (natp tag) (posp n))
           (or (equal (mod tag (* 2 n)) (mod tag n))
               (equal (mod tag (* 2 n)) (+ n (mod tag n)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance mod-x-i*j-of-positives (x tag) (i n) (j 2))
                        (:instance fn-mpxl-mod-2 (k (floor tag n))))
           :in-theory (disable mod-x-i*j-of-positives))))

(defthm fn-mpxl-addr-below
  (implies (and (natp tag) (posp n) (natp s) (<= s n))
           (< (fn-mpxl-addr tag n s) (+ n s)))
  :rule-classes :linear
  :hints (("Goal" :use (fn-mpxl-mod-double
                        (:instance mod-bounded-by-modulus (x tag) (y n))))))

; A TAG whose address under mod 2N is N + S: a MOVER of the split of page S.
(defun fn-mpxl-moverp (tag n p)
  (declare (xargs :guard (and (natp tag) (posp n) (natp p))))
  (equal (mod tag (* 2 n)) p))

;; No rewriting of `mod' terms from here: the two facts above and the bound.
(local (in-theory (disable mod-x-i*j-of-positives simplify-mod-* mod-=-0 mod-x-y-=-x-for-rationals)))

; THE ADDRESS AFTER THE SPLIT of page S (the root advanced: S + 1 within
; the round, or N doubled and S = 0 at its end): the movers' address is the
; new page N + S; every other tag's address is unchanged.
(defthm fn-mpxl-addr-after-split-same-round
  (implies (and (natp tag) (posp n) (natp s) (< (+ 1 s) n))
           (equal (fn-mpxl-addr tag n (+ 1 s))
                  (if (fn-mpxl-moverp tag n (+ n s)) (+ n s) (fn-mpxl-addr tag n s))))
  :hints (("Goal" :in-theory (enable fn-mpxl-addr fn-mpxl-moverp)
           :cases ((equal (mod tag (* 2 n)) (mod tag n))
                   (equal (mod tag (* 2 n)) (+ n (mod tag n))))
           :use (fn-mpxl-mod-double
                 (:instance mod-bounded-by-modulus (x tag) (y n))
                 (:instance mod-bounded-by-modulus (x tag) (y (* 2 n)))))))

(defthm fn-mpxl-addr-after-split-next-round
  (implies (and (natp tag) (posp n) (natp s) (equal s (+ -1 n)))
           (equal (fn-mpxl-addr tag (* 2 n) 0)
                  (if (fn-mpxl-moverp tag n (+ n s)) (+ n s) (fn-mpxl-addr tag n s))))
  :hints (("Goal" :in-theory (enable fn-mpxl-addr fn-mpxl-moverp)
           :cases ((equal (mod tag (* 2 n)) (mod tag n))
                   (equal (mod tag (* 2 n)) (+ n (mod tag n))))
           :use (fn-mpxl-mod-double
                 (:instance mod-bounded-by-modulus (x tag) (y n))
                 (:instance mod-bounded-by-modulus (x tag) (y (* 2 n)))))))

; A mover's home is page S.
(defthm fn-mpxl-mover-home
  (implies (and (natp tag) (posp n) (natp s) (< s n) (fn-mpxl-moverp tag n (+ n s)))
           (equal (fn-mpxl-addr tag n s) s))
  :hints (("Goal" :in-theory (enable fn-mpxl-addr fn-mpxl-moverp)
           :use (fn-mpxl-mod-double
                 (:instance mod-bounded-by-modulus (x tag) (y n))))))

;; The same with N = S + 1 substituted, as the prover writes it (the split
;; theorem's case where the round ends).
(defthm fn-mpxl-addr-after-split-next-round-s
  (implies (and (natp tag) (natp s))
           (equal (fn-mpxl-addr tag (+ 2 (* 2 s)) 0)
                  (if (fn-mpxl-moverp tag (+ 1 s) (+ 1 s s)) (+ 1 s s) (fn-mpxl-addr tag (+ 1 s) s))))
  :hints (("Goal" :use ((:instance fn-mpxl-addr-after-split-next-round (n (+ 1 s)))))))

(in-theory (disable fn-mpxl-addr fn-mpxl-moverp))

; -----------------------------------------------------------------------------
; 1. Pages and tables.

; A page: (FLAG . ENTRIES), the entries (TAG . SEQ) in slot order.
(defun fn-mpxl-pagep (pg)
  (declare (xargs :guard t))
  (and (consp pg) (booleanp (car pg)) (fn-mpx-pagep (cdr pg))))

(defun fn-mpxl-pagesp (pgs)
  (declare (xargs :guard t))
  (if (consp pgs)
      (and (fn-mpxl-pagep (car pgs)) (fn-mpxl-pagesp (cdr pgs)))
    (null pgs)))

(defun fn-mpxl-flag (pg)
  (declare (xargs :guard t))
  (and (consp pg) (car pg) t))

(defun fn-mpxl-ents (pg)
  (declare (xargs :guard t))
  (if (consp pg) (cdr pg) nil))

(defun fn-mpxl-page (i pgs)
  (declare (xargs :guard (and (natp i) (true-listp pgs))))
  (if (< i (len pgs)) (nth i pgs) nil))

; The table: (PAGES N S) with N + S pages, 0 <= S < N.
(defun fn-mpxl-tabp (tab)
  (declare (xargs :guard t))
  (and (true-listp tab) (equal (len tab) 3)
       (fn-mpxl-pagesp (car tab))
       (posp (cadr tab)) (natp (caddr tab)) (< (caddr tab) (cadr tab))
       (equal (len (car tab)) (+ (cadr tab) (caddr tab)))))

(defun fn-mpxl-pages (tab)
  (declare (xargs :guard (fn-mpxl-tabp tab)))
  (car tab))
(defun fn-mpxl-n (tab)
  (declare (xargs :guard (fn-mpxl-tabp tab)))
  (cadr tab))
(defun fn-mpxl-s (tab)
  (declare (xargs :guard (fn-mpxl-tabp tab)))
  (caddr tab))
(defun fn-mpxl-make (pgs n s)
  (declare (xargs :guard t))
  (list pgs n s))

(defthm fn-mpxl-pagesp-true-listp
  (implies (fn-mpxl-pagesp pgs) (true-listp pgs)))

(defthm fn-mpxl-nth-pagep
  (implies (and (fn-mpxl-pagesp pgs) (natp i) (< i (len pgs)))
           (fn-mpxl-pagep (nth i pgs))))

(defthm fn-mpxl-ents-pagep
  (implies (fn-mpxl-pagesp pgs)
           (fn-mpx-pagep (fn-mpxl-ents (fn-mpxl-page i pgs)))))

(defthm fn-mpxl-ents-of-cons
  (equal (fn-mpxl-ents (cons f es)) es))
(defthm fn-mpxl-flag-of-cons
  (equal (fn-mpxl-flag (cons f es)) (and f t)))
(defthm fn-mpxl-page-nil
  (equal (fn-mpxl-page i nil) nil))
(defthm fn-mpxl-flag-booleanp
  (booleanp (fn-mpxl-flag pg))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-mpxl-len-update-nth
  (implies (and (natp i) (< i (len l)))
           (equal (len (update-nth i v l)) (len l))))
(local (defthm fn-mpxl-nth-update-nth
  (implies (and (natp i) (natp j))
           (equal (nth i (update-nth j v l))
                  (if (equal i j) v (nth i l))))))
(local (defthm fn-mpxl-len-append
  (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm fn-mpxl-nth-append
  (implies (natp i)
           (equal (nth i (append a b))
                  (if (< i (len a)) (nth i a) (nth (- i (len a)) b))))))

; The page at I of an updated list, and of a list with one page appended.
(defthm fn-mpxl-page-of-update-nth
  (implies (and (natp i) (natp j) (< j (len pgs)))
           (equal (fn-mpxl-page i (update-nth j pg pgs))
                  (if (equal i j) pg (fn-mpxl-page i pgs)))))
(defthm fn-mpxl-page-of-append-one
  (implies (natp i)
           (equal (fn-mpxl-page i (append pgs (list pg)))
                  (cond ((< i (len pgs)) (fn-mpxl-page i pgs))
                        ((equal i (len pgs)) pg)
                        (t nil)))))

;; A page is read through these from here on.
(in-theory (disable fn-mpxl-page fn-mpxl-ents fn-mpxl-flag))

(defthm fn-mpxl-pagesp-of-update-nth
  (implies (and (fn-mpxl-pagesp pgs) (natp i) (< i (len pgs)) (fn-mpxl-pagep pg))
           (fn-mpxl-pagesp (update-nth i pg pgs))))

(defthm fn-mpxl-pagesp-of-append
  (implies (and (fn-mpxl-pagesp a) (fn-mpxl-pagesp b))
           (fn-mpxl-pagesp (append a b))))

;; `nth' and `update-nth' stay closed from here: the lemmas above are their facts.
(local (in-theory (disable nth update-nth)))

(defthm fn-mpxl-tabp-make
  (equal (fn-mpxl-tabp (fn-mpxl-make pgs n s))
         (and (fn-mpxl-pagesp pgs) (posp n) (natp s) (< s n) (equal (len pgs) (+ n s)))))

(defthm fn-mpxl-tabp-facts
  (implies (fn-mpxl-tabp tab)
           (and (fn-mpxl-pagesp (fn-mpxl-pages tab))
                (true-listp (fn-mpxl-pages tab))
                (posp (fn-mpxl-n tab)) (natp (fn-mpxl-s tab))
                (< (fn-mpxl-s tab) (fn-mpxl-n tab))))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((fn-mpxl-tabp tab)))))

;; The page count is arithmetic, never a rewrite of `len' (a rewrite of it
;; made the simplifier specious under concrete equalities).
(defthm fn-mpxl-tabp-len
  (implies (fn-mpxl-tabp tab)
           (equal (len (fn-mpxl-pages tab)) (+ (fn-mpxl-n tab) (fn-mpxl-s tab))))
  :rule-classes ((:linear)
                 (:forward-chaining :trigger-terms ((fn-mpxl-tabp tab)))))

(defthm fn-mpxl-accessors-of-make
  (and (equal (fn-mpxl-pages (fn-mpxl-make pgs n s)) pgs)
       (equal (fn-mpxl-n (fn-mpxl-make pgs n s)) n)
       (equal (fn-mpxl-s (fn-mpxl-make pgs n s)) s)))

(local (defthm fn-mpxl-list-of-three
  (implies (and (true-listp x) (equal (len x) 3))
           (equal (list (car x) (cadr x) (caddr x)) x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable len)))))

(defthm fn-mpxl-make-of-accessors
  (implies (fn-mpxl-tabp tab)
           (equal (fn-mpxl-make (fn-mpxl-pages tab) (fn-mpxl-n tab) (fn-mpxl-s tab)) tab))
  :hints (("Goal" :in-theory (enable fn-mpxl-tabp fn-mpxl-pages fn-mpxl-n fn-mpxl-s fn-mpxl-make)
           :use ((:instance fn-mpxl-list-of-three (x tab))))))

(in-theory (disable fn-mpxl-tabp fn-mpxl-pages fn-mpxl-n fn-mpxl-s fn-mpxl-make))

; -----------------------------------------------------------------------------
; 2. The candidates.

; Insert S into an ascending list, once (books/msgid-pages-exec fn-mpxt-ins).
(defun fn-mpxl-ins (s seqs)
  (declare (xargs :guard (and (natp s) (nat-listp seqs))))
  (cond ((atom seqs) (list s))
        ((< s (car seqs)) (cons s seqs))
        ((equal s (car seqs)) seqs)
        (t (cons (car seqs) (fn-mpxl-ins s (cdr seqs))))))

(defthm fn-mpxl-ins-nat-listp
  (implies (and (natp s) (nat-listp seqs))
           (nat-listp (fn-mpxl-ins s seqs))))

(defthm fn-mpxl-ins-ascending
  (implies (and (natp s) (nat-listp seqs) (fn-mpx-ascendingp seqs))
           (fn-mpx-ascendingp (fn-mpxl-ins s seqs)))
  :hints (("Goal" :induct (fn-mpxl-ins s seqs))))

(defthm fn-mpxl-ins-member
  (implies (and (natp s) (nat-listp seqs))
           (iff (member-equal x (fn-mpxl-ins s seqs))
                (or (equal x s) (member-equal x seqs)))))

(defthm fn-mpxl-ins-below
  (implies (and (fn-mpx-below-p seqs n) (< s n))
           (fn-mpx-below-p (fn-mpxl-ins s seqs) n)))

; The seqs of the entries tagged TAG, inserted into ACC.
(defun fn-mpxl-seqs (tag ents acc)
  (declare (xargs :guard (and (fn-mpx-pagep ents) (nat-listp acc))))
  (if (consp ents)
      (let ((rest (fn-mpxl-seqs tag (cdr ents) acc)))
        (if (equal tag (car (car ents)))
            (fn-mpxl-ins (cdr (car ents)) rest)
          rest))
    acc))

(defthm fn-mpxl-seqs-nat-listp
  (implies (and (fn-mpx-pagep ents) (nat-listp acc))
           (nat-listp (fn-mpxl-seqs tag ents acc))))

(defthm fn-mpxl-seqs-ascending
  (implies (and (fn-mpx-pagep ents) (nat-listp acc) (fn-mpx-ascendingp acc))
           (fn-mpx-ascendingp (fn-mpxl-seqs tag ents acc))))

; Every seq of ENTS below N.
(defun fn-mpxl-ents-below (ents n)
  (declare (xargs :guard (and (fn-mpx-pagep ents) (natp n))))
  (if (consp ents)
      (and (< (cdr (car ents)) n) (fn-mpxl-ents-below (cdr ents) n))
    t))

(defthm fn-mpxl-seqs-below
  (implies (and (fn-mpxl-ents-below ents n) (fn-mpx-below-p acc n))
           (fn-mpx-below-p (fn-mpxl-seqs tag ents acc) n)))

; MEMBERSHIP: a seq is among the seqs exactly when it is in ACC or the
; entry (TAG . SEQ) is among the entries.
(defthm fn-mpxl-seqs-member
  (implies (and (fn-mpx-pagep ents) (nat-listp acc))
           (iff (member-equal q (fn-mpxl-seqs tag ents acc))
                (or (member-equal q acc) (member-equal (cons tag q) ents)))))

(in-theory (disable fn-mpxl-ins))

; THE CANDIDATES of TAG: its home page's seqs and, under the home page's
; flag, the next page's.
; (Written without a `let': the rewriter then sees every page read.)
(defun fn-mpxl-cands (tag tab)
  (declare (xargs :guard (and (natp tag) (fn-mpxl-tabp tab))))
  (if (and (fn-mpxl-flag (fn-mpxl-page (fn-mpxl-addr tag (fn-mpxl-n tab) (fn-mpxl-s tab)) (fn-mpxl-pages tab)))
           (< (+ 1 (fn-mpxl-addr tag (fn-mpxl-n tab) (fn-mpxl-s tab))) (len (fn-mpxl-pages tab))))
      (fn-mpxl-seqs tag
                    (fn-mpxl-ents (fn-mpxl-page (+ 1 (fn-mpxl-addr tag (fn-mpxl-n tab) (fn-mpxl-s tab)))
                                                (fn-mpxl-pages tab)))
                    (fn-mpxl-seqs tag
                                  (fn-mpxl-ents (fn-mpxl-page (fn-mpxl-addr tag (fn-mpxl-n tab) (fn-mpxl-s tab))
                                                              (fn-mpxl-pages tab)))
                                  nil))
    (fn-mpxl-seqs tag
                  (fn-mpxl-ents (fn-mpxl-page (fn-mpxl-addr tag (fn-mpxl-n tab) (fn-mpxl-s tab))
                                              (fn-mpxl-pages tab)))
                  nil)))

(defthm fn-mpxl-cands-nat-listp
  (implies (fn-mpxl-tabp tab)
           (nat-listp (fn-mpxl-cands tag tab))))

(defthm fn-mpxl-cands-ascending
  (implies (fn-mpxl-tabp tab)
           (fn-mpx-ascendingp (fn-mpxl-cands tag tab))))

(defthm fn-mpxl-cands-true-listp
  (implies (fn-mpxl-tabp tab)
           (true-listp (fn-mpxl-cands tag tab)))
  :hints (("Goal" :use fn-mpxl-cands-nat-listp
           :in-theory (disable fn-mpxl-cands-nat-listp fn-mpxl-cands))))

; Every page's seqs below N.
(defun fn-mpxl-pages-okp (pgs n)
  (declare (xargs :guard (and (fn-mpxl-pagesp pgs) (natp n))))
  (if (consp pgs)
      (and (fn-mpxl-ents-below (fn-mpxl-ents (car pgs)) n)
           (fn-mpxl-pages-okp (cdr pgs) n))
    t))

(defthm fn-mpxl-pages-okp-page
  (implies (fn-mpxl-pages-okp pgs n)
           (fn-mpxl-ents-below (fn-mpxl-ents (fn-mpxl-page i pgs)) n))
  :hints (("Goal" :in-theory (enable fn-mpxl-page nth) :induct (nth i pgs))))

(defun fn-mpxl-okp (tab n)
  (declare (xargs :guard (and (fn-mpxl-tabp tab) (natp n))))
  (fn-mpxl-pages-okp (fn-mpxl-pages tab) n))

(defthm fn-mpxl-cands-below
  (implies (fn-mpxl-okp tab n)
           (fn-mpx-below-p (fn-mpxl-cands tag tab) n)))

; -----------------------------------------------------------------------------
; 3. The reader, the faithful relation, the keystone.

; THE PAGED READER: the candidates of the Message-ID's tag, confirmed.
(defun fn-mpxl-records (msgid tab rows)
  (declare (xargs :guard (and (fn-mpxl-tabp tab) (true-listp rows))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxl-cands)))))
  (fn-mpx-confirm msgid (fn-mpxl-cands (fn-mpx-tag msgid) tab) rows))

; FAITHFUL from I: every held row's sequence at or after I is among its
; own tag's candidates.
(defun fn-mpxl-faithful-from (i tab rows)
  (declare (xargs :guard (and (natp i) (fn-mpxl-tabp tab) (true-listp rows))
                  :measure (nfix (- (len rows) (nfix i)))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxl-cands fn-cei-event-article)))))
  (if (>= (nfix i) (len rows))
      t
    (and (let ((rec (fn-cei-event-article (nth (nfix i) rows))))
           (or (not (fn-held-p rec))
               (member-equal (nfix i)
                             (fn-mpxl-cands (fn-mpx-tag (fn-record-msgid rec)) tab))))
         (fn-mpxl-faithful-from (1+ (nfix i)) tab rows))))

(defun fn-mpxl-faithful (tab rows)
  (declare (xargs :guard (and (fn-mpxl-tabp tab) (true-listp rows))))
  (and (fn-mpxl-okp tab (len rows))
       (fn-mpxl-faithful-from 0 tab rows)))

(local
 (defthm fn-mpxl-faithful-from-complete
   (implies (and (fn-mpxl-faithful-from i tab rows) (natp i))
            (fn-mpx-complete-from i msgid (fn-mpxl-cands (fn-mpx-tag msgid) tab) rows))
   :hints (("Goal" :induct (fn-mpxl-faithful-from i tab rows)
            :in-theory (e/d (fn-mpx-complete-from fn-mpx-hitp)
                            (fn-mpxl-cands fn-cei-event-article fn-held-p fn-record-msgid))))))

; KEYSTONE: the linear table's reader is the specification, under the
; faithful relation -- layer A (`fn-mpx-confirm-is-the-records-for') applied
; to the linear candidates.
(defthm fn-mpxl-records-is-the-records-for
  (implies (and (fn-mpxl-tabp tab)
                (fn-mpxl-faithful tab rows))
           (equal (fn-mpxl-records msgid tab rows)
                  (fn-cei-article-records-for msgid rows)))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-records fn-mpxl-faithful)
                                  (fn-mpxl-cands fn-mpx-confirm fn-mpxl-faithful-from
                                   fn-mpxl-okp fn-cei-article-records-for))
           :use ((:instance fn-mpx-confirm-is-the-records-for
                            (seqs (fn-mpxl-cands (fn-mpx-tag msgid) tab)))
                 (:instance fn-mpxl-faithful-from-complete (i 0))
                 (:instance fn-mpxl-cands-ascending (tag (fn-mpx-tag msgid)))
                 (:instance fn-mpxl-cands-below (tag (fn-mpx-tag msgid)) (n (len rows)))
                 (:instance fn-mpxl-cands-nat-listp (tag (fn-mpx-tag msgid)))))))

; The same against the history's abstract stobj logic function.
(defthm fn-mpxl-records-is-hist-msgid-records
  (implies (and (fn-mpxl-tabp tab)
                (fn-mpxl-faithful tab fn-hist$a))
           (equal (fn-mpxl-records msgid tab fn-hist$a)
                  (fn-hist$a-msgid-records msgid fn-hist$a)))
  :hints (("Goal" :in-theory (e/d (fn-hist$a-msgid-records)
                                  (fn-mpxl-records fn-mpxl-faithful fn-cei-article-records-for)))))

; -----------------------------------------------------------------------------
; 4. The writer: the entry onto its home page, else onto the next page with
; the home page's flag set, else NOT AT ALL (saturated: the table unchanged).

(defun fn-mpxl-saturatedp (tag tab)
  (declare (xargs :guard (and (natp tag) (fn-mpxl-tabp tab))))
  (let* ((pgs (fn-mpxl-pages tab))
         (h (fn-mpxl-addr tag (fn-mpxl-n tab) (fn-mpxl-s tab))))
    (and (>= (len (fn-mpxl-ents (fn-mpxl-page h pgs))) *fn-mpxl-cap*)
         (or (>= (+ 1 h) (len pgs))
             (>= (len (fn-mpxl-ents (fn-mpxl-page (+ 1 h) pgs))) *fn-mpxl-cap*)))))

; (mv placed tab)
(defun fn-mpxl-put (tag seq tab)
  (declare (xargs :guard (and (natp tag) (natp seq) (fn-mpxl-tabp tab))))
  (let* ((pgs (fn-mpxl-pages tab)) (n (fn-mpxl-n tab)) (s (fn-mpxl-s tab))
         (h (fn-mpxl-addr tag n s))
         (pg (fn-mpxl-page h pgs)))
    (cond ((< (len (fn-mpxl-ents pg)) *fn-mpxl-cap*)
           (mv t (fn-mpxl-make (update-nth h (cons (fn-mpxl-flag pg) (cons (cons tag seq) (fn-mpxl-ents pg))) pgs)
                               n s)))
          ((and (< (+ 1 h) (len pgs))
                (< (len (fn-mpxl-ents (fn-mpxl-page (+ 1 h) pgs))) *fn-mpxl-cap*))
           (let* ((pg1 (fn-mpxl-page (+ 1 h) pgs))
                  (pgs (update-nth h (cons t (fn-mpxl-ents pg)) pgs))
                  (pgs (update-nth (+ 1 h) (cons (fn-mpxl-flag pg1) (cons (cons tag seq) (fn-mpxl-ents pg1))) pgs)))
             (mv t (fn-mpxl-make pgs n s))))
          (t (mv nil tab)))))

; The outcome is the named refusal: placed exactly when not saturated, and
; an unplaced entry changes nothing.
(defthm fn-mpxl-put-places-iff-not-saturated
  (iff (mv-nth 0 (fn-mpxl-put tag seq tab))
       (not (fn-mpxl-saturatedp tag tab))))

(defthm fn-mpxl-put-unplaced-unchanged
  (implies (not (mv-nth 0 (fn-mpxl-put tag seq tab)))
           (equal (mv-nth 1 (fn-mpxl-put tag seq tab)) tab)))

(defthm fn-mpxl-put-tabp
  (implies (and (fn-mpxl-tabp tab) (natp tag) (natp seq))
           (fn-mpxl-tabp (mv-nth 1 (fn-mpxl-put tag seq tab))))
  :hints (("Goal" :in-theory (disable fn-mpxl-addr-below)
           :use ((:instance fn-mpxl-addr-below (n (fn-mpxl-n tab)) (s (fn-mpxl-s tab)))))))

(defthm fn-mpxl-put-root
  (implies (and (fn-mpxl-tabp tab) (natp tag))
           (and (equal (fn-mpxl-n (mv-nth 1 (fn-mpxl-put tag seq tab))) (fn-mpxl-n tab))
                (equal (fn-mpxl-s (mv-nth 1 (fn-mpxl-put tag seq tab))) (fn-mpxl-s tab))
                (equal (len (fn-mpxl-pages (mv-nth 1 (fn-mpxl-put tag seq tab)))) (len (fn-mpxl-pages tab)))))
  :hints (("Goal" :in-theory (disable fn-mpxl-addr-below)
           :use ((:instance fn-mpxl-addr-below (n (fn-mpxl-n tab)) (s (fn-mpxl-s tab)))))))

; The page at I after a placement: the entry consed onto the page it went
; to, the home page's flag set when it went to the next page, else unchanged.
(defthm fn-mpxl-page-of-put
  (implies (and (fn-mpxl-tabp tab) (natp tag) (natp i)
                (not (fn-mpxl-saturatedp tag tab)))
           (equal (fn-mpxl-page i (fn-mpxl-pages (mv-nth 1 (fn-mpxl-put tag seq tab))))
                  (let* ((pgs (fn-mpxl-pages tab))
                         (h (fn-mpxl-addr tag (fn-mpxl-n tab) (fn-mpxl-s tab)))
                         (home-has-room (< (len (fn-mpxl-ents (fn-mpxl-page h pgs))) *fn-mpxl-cap*)))
                    (cond ((and (equal i h) home-has-room)
                           (cons (fn-mpxl-flag (fn-mpxl-page h pgs))
                                 (cons (cons tag seq) (fn-mpxl-ents (fn-mpxl-page h pgs)))))
                          ((equal i h)
                           (cons t (fn-mpxl-ents (fn-mpxl-page h pgs))))
                          ((and (equal i (+ 1 h)) (not home-has-room))
                           (cons (fn-mpxl-flag (fn-mpxl-page i pgs))
                                 (cons (cons tag seq) (fn-mpxl-ents (fn-mpxl-page i pgs)))))
                          (t (fn-mpxl-page i pgs))))))
  :hints (("Goal" :in-theory (disable fn-mpxl-addr-below)
           :use ((:instance fn-mpxl-addr-below (n (fn-mpxl-n tab)) (s (fn-mpxl-s tab)))))))

(in-theory (disable fn-mpxl-put fn-mpxl-saturatedp))

; THE PUT FINDS WHAT IT PLACED.
(defthm fn-mpxl-put-finds
  (implies (and (fn-mpxl-tabp tab) (natp tag) (natp seq)
                (mv-nth 0 (fn-mpxl-put tag seq tab)))
           (member-equal seq (fn-mpxl-cands tag (mv-nth 1 (fn-mpxl-put tag seq tab)))))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-cands fn-mpxl-saturatedp) (fn-mpxl-page fn-mpxl-addr-below))
           :use ((:instance fn-mpxl-addr-below (n (fn-mpxl-n tab)) (s (fn-mpxl-s tab)))))))

; THE PUT KEEPS EVERY CANDIDATE of every tag.
(defthm fn-mpxl-put-keeps-candidate
  (implies (and (fn-mpxl-tabp tab) (natp tag) (natp wtag) (natp seq)
                (member-equal q (fn-mpxl-cands tag tab)))
           (member-equal q (fn-mpxl-cands tag (mv-nth 1 (fn-mpxl-put wtag seq tab)))))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-cands) (fn-mpxl-page fn-mpxl-addr-below))
           :cases ((fn-mpxl-saturatedp wtag tab))
           :use ((:instance fn-mpxl-addr-below (n (fn-mpxl-n tab)) (s (fn-mpxl-s tab)))
                 (:instance fn-mpxl-addr-below (tag wtag) (n (fn-mpxl-n tab)) (s (fn-mpxl-s tab)))))))

; The slot invariant under the put: the new seq below the new bound.
(defthm fn-mpxl-pages-okp-of-update-nth
  (implies (and (fn-mpxl-pages-okp pgs n) (natp i) (< i (len pgs))
                (fn-mpxl-ents-below (fn-mpxl-ents pg) n))
           (fn-mpxl-pages-okp (update-nth i pg pgs) n))
  :hints (("Goal" :in-theory (enable update-nth) :induct (update-nth i pg pgs))))

(defthm fn-mpxl-pages-okp-mono
  (implies (and (fn-mpxl-pages-okp pgs n) (natp n) (natp n2) (<= n n2))
           (fn-mpxl-pages-okp pgs n2)))

(defthm fn-mpxl-ents-below-mono
  (implies (and (fn-mpxl-ents-below ents n) (natp n) (natp n2) (<= n n2))
           (fn-mpxl-ents-below ents n2)))

(defthm fn-mpxl-put-okp
  (implies (and (fn-mpxl-tabp tab) (natp tag) (natp seq) (natp n) (natp n2)
                (<= n n2) (< seq n2)
                (fn-mpxl-okp tab n))
           (fn-mpxl-okp (mv-nth 1 (fn-mpxl-put tag seq tab)) n2))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-put) (fn-mpxl-addr-below))
           :use ((:instance fn-mpxl-addr-below (n (fn-mpxl-n tab)) (s (fn-mpxl-s tab)))))))

; -----------------------------------------------------------------------------
; 5. The split: the movers of page S and of its overflow page onto the new
; page N + S; the root advances.  (mv ok tab); not ok -- the movers exceed a
; page -- the table is unchanged.

(defun fn-mpxl-movers (ents n p)
  (declare (xargs :guard (and (fn-mpx-pagep ents) (posp n) (natp p))))
  (if (consp ents)
      (if (fn-mpxl-moverp (car (car ents)) n p)
          (cons (car ents) (fn-mpxl-movers (cdr ents) n p))
        (fn-mpxl-movers (cdr ents) n p))
    nil))

(defun fn-mpxl-stayers (ents n p)
  (declare (xargs :guard (and (fn-mpx-pagep ents) (posp n) (natp p))))
  (if (consp ents)
      (if (fn-mpxl-moverp (car (car ents)) n p)
          (fn-mpxl-stayers (cdr ents) n p)
        (cons (car ents) (fn-mpxl-stayers (cdr ents) n p)))
    nil))

(defthm fn-mpxl-movers-pagep
  (implies (fn-mpx-pagep ents) (fn-mpx-pagep (fn-mpxl-movers ents n p))))
(defthm fn-mpxl-stayers-pagep
  (implies (fn-mpx-pagep ents) (fn-mpx-pagep (fn-mpxl-stayers ents n p))))
(defthm fn-mpxl-movers-below
  (implies (fn-mpxl-ents-below ents m) (fn-mpxl-ents-below (fn-mpxl-movers ents n p) m)))
(defthm fn-mpxl-stayers-below
  (implies (fn-mpxl-ents-below ents m) (fn-mpxl-ents-below (fn-mpxl-stayers ents n p) m)))
(defthm fn-mpxl-ents-below-append
  (equal (fn-mpxl-ents-below (append a b) m)
         (and (fn-mpxl-ents-below a m) (fn-mpxl-ents-below b m))))
(defthm fn-mpx-pagep-append
  (implies (and (fn-mpx-pagep a) (fn-mpx-pagep b)) (fn-mpx-pagep (append a b))))

; An entry is among the movers exactly when it is among the entries and its
; tag moves; among the stayers when it does not.
(defthm fn-mpxl-movers-member
  (iff (member-equal e (fn-mpxl-movers ents n p))
       (and (member-equal e ents) (fn-mpxl-moverp (car e) n p))))
(defthm fn-mpxl-stayers-member
  (iff (member-equal e (fn-mpxl-stayers ents n p))
       (and (member-equal e ents) (not (fn-mpxl-moverp (car e) n p)))))

; The pages after the split of page S: S and S + 1 keep their stayers and
; their flags; the movers are the new last page, flag clear.
(defun fn-mpxl-split-pages (pgs n s)
  (declare (xargs :guard (and (fn-mpxl-pagesp pgs) (posp n) (natp s) (< s (len pgs)))))
  (let* ((p (len pgs))
         (pg (fn-mpxl-page s pgs))
         (pg1 (fn-mpxl-page (+ 1 s) pgs))
         (movers (append (fn-mpxl-movers (fn-mpxl-ents pg) n p)
                         (fn-mpxl-movers (fn-mpxl-ents pg1) n p)))
         (pgs (update-nth s (cons (fn-mpxl-flag pg) (fn-mpxl-stayers (fn-mpxl-ents pg) n p)) pgs))
         (pgs (if (< (+ 1 s) p)
                  (update-nth (+ 1 s) (cons (fn-mpxl-flag pg1) (fn-mpxl-stayers (fn-mpxl-ents pg1) n p)) pgs)
                pgs)))
    (append pgs (list (cons nil movers)))))

; The movers of the split of page S: those of its page and its overflow page.
(defun fn-mpxl-split-movers (tab)
  (declare (xargs :guard (fn-mpxl-tabp tab)))
  (let* ((pgs (fn-mpxl-pages tab)) (n (fn-mpxl-n tab)) (s (fn-mpxl-s tab)) (p (len pgs)))
    (append (fn-mpxl-movers (fn-mpxl-ents (fn-mpxl-page s pgs)) n p)
            (fn-mpxl-movers (fn-mpxl-ents (fn-mpxl-page (+ 1 s) pgs)) n p))))

(defun fn-mpxl-split (tab)
  (declare (xargs :guard (fn-mpxl-tabp tab)))
  (let ((n (fn-mpxl-n tab)) (s (fn-mpxl-s tab)))
    (if (< *fn-mpxl-cap* (len (fn-mpxl-split-movers tab)))
        (mv nil tab)
      (let ((pgs (fn-mpxl-split-pages (fn-mpxl-pages tab) n s)))
        (if (equal (+ 1 s) n)
            (mv t (fn-mpxl-make pgs (* 2 n) 0))
          (mv t (fn-mpxl-make pgs n (+ 1 s))))))))

(defthm fn-mpxl-split-refused-unchanged
  (implies (not (mv-nth 0 (fn-mpxl-split tab)))
           (equal (mv-nth 1 (fn-mpxl-split tab)) tab)))

(defthm fn-mpxl-split-pages-len
  (implies (and (natp s) (< s (len pgs)))
           (equal (len (fn-mpxl-split-pages pgs n s)) (+ 1 (len pgs)))))

(defthm fn-mpxl-split-pages-pagesp
  (implies (and (fn-mpxl-pagesp pgs) (natp s) (< s (len pgs)))
           (fn-mpxl-pagesp (fn-mpxl-split-pages pgs n s))))

(defthm fn-mpxl-page-beyond
  (implies (and (natp i) (<= (len pgs) i))
           (equal (fn-mpxl-page i pgs) nil))
  :hints (("Goal" :in-theory (enable fn-mpxl-page))))

; THE PAGE AT I AFTER THE SPLIT: only S, S + 1 and the new page differ.
(defthm fn-mpxl-page-of-split-pages
  (implies (and (fn-mpxl-pagesp pgs) (natp s) (< s (len pgs)) (natp i))
           (equal (fn-mpxl-page i (fn-mpxl-split-pages pgs n s))
                  (let ((p (len pgs)))
                    (cond ((equal i s)
                           (cons (fn-mpxl-flag (fn-mpxl-page s pgs))
                                 (fn-mpxl-stayers (fn-mpxl-ents (fn-mpxl-page s pgs)) n p)))
                          ((and (equal i (+ 1 s)) (< i p))
                           (cons (fn-mpxl-flag (fn-mpxl-page i pgs))
                                 (fn-mpxl-stayers (fn-mpxl-ents (fn-mpxl-page i pgs)) n p)))
                          ((equal i p)
                           (cons nil (append (fn-mpxl-movers (fn-mpxl-ents (fn-mpxl-page s pgs)) n p)
                                             (fn-mpxl-movers (fn-mpxl-ents (fn-mpxl-page (+ 1 s) pgs)) n p))))
                          (t (fn-mpxl-page i pgs))))))
  :hints (("Goal" :in-theory (enable fn-mpxl-split-pages) :do-not-induct t)))

(in-theory (disable fn-mpxl-split-pages fn-mpxl-split-movers))

(defthm fn-mpxl-split-tabp
  (implies (and (fn-mpxl-tabp tab) (mv-nth 0 (fn-mpxl-split tab)))
           (fn-mpxl-tabp (mv-nth 1 (fn-mpxl-split tab)))))

; The root after the split.
(defthm fn-mpxl-split-root
  (implies (and (fn-mpxl-tabp tab) (mv-nth 0 (fn-mpxl-split tab)))
           (and (equal (fn-mpxl-n (mv-nth 1 (fn-mpxl-split tab)))
                       (if (equal (+ 1 (fn-mpxl-s tab)) (fn-mpxl-n tab)) (* 2 (fn-mpxl-n tab)) (fn-mpxl-n tab)))
                (equal (fn-mpxl-s (mv-nth 1 (fn-mpxl-split tab)))
                       (if (equal (+ 1 (fn-mpxl-s tab)) (fn-mpxl-n tab)) 0 (+ 1 (fn-mpxl-s tab))))
                (equal (fn-mpxl-pages (mv-nth 1 (fn-mpxl-split tab)))
                       (fn-mpxl-split-pages (fn-mpxl-pages tab) (fn-mpxl-n tab) (fn-mpxl-s tab))))))

(in-theory (disable fn-mpxl-split))

; The split's effect on the seqs of one tag: a mover tag's seqs on the old
; pages are all on the new page; another tag's are where they were.
(defthm fn-mpxl-seqs-of-movers
  (implies (fn-mpxl-moverp tag n p)
           (equal (fn-mpxl-seqs tag (fn-mpxl-movers ents n p) acc)
                  (fn-mpxl-seqs tag ents acc))))
(defthm fn-mpxl-seqs-of-stayers
  (implies (not (fn-mpxl-moverp tag n p))
           (equal (fn-mpxl-seqs tag (fn-mpxl-stayers ents n p) acc)
                  (fn-mpxl-seqs tag ents acc))))
(defthm fn-mpxl-seqs-of-movers-other
  (implies (not (fn-mpxl-moverp tag n p))
           (equal (fn-mpxl-seqs tag (fn-mpxl-movers ents n p) acc) acc)))
(defthm fn-mpxl-seqs-of-stayers-mover
  (implies (fn-mpxl-moverp tag n p)
           (equal (fn-mpxl-seqs tag (fn-mpxl-stayers ents n p) acc) acc)))
(defthm fn-mpxl-seqs-of-append
  (equal (fn-mpxl-seqs tag (append a b) acc)
         (fn-mpxl-seqs tag a (fn-mpxl-seqs tag b acc))))

; Stated first over the root's variables (the prover then substitutes
; N = S + 1 at the round's end cleanly), then over the table.
(defthm fn-mpxl-split-pages-keeps-candidate
  (implies (and (fn-mpxl-pagesp pgs) (posp n) (natp s) (< s n) (equal (len pgs) (+ n s))
                (natp tag)
                (member-equal q (fn-mpxl-cands tag (fn-mpxl-make pgs n s))))
           (member-equal q (fn-mpxl-cands tag (fn-mpxl-make (fn-mpxl-split-pages pgs n s)
                                                            (if (equal (+ 1 s) n) (* 2 n) n)
                                                            (if (equal (+ 1 s) n) 0 (+ 1 s))))))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-cands) (fn-mpxl-page fn-mpxl-addr-below))
           :do-not-induct t
           :cases ((equal (+ 1 s) n))
           :use ((:instance fn-mpxl-addr-below)))))

; KEYSTONE (the split): every candidate of every tag survives the split.
(defthm fn-mpxl-split-keeps-candidate
  (implies (and (fn-mpxl-tabp tab) (natp tag)
                (mv-nth 0 (fn-mpxl-split tab))
                (member-equal q (fn-mpxl-cands tag tab)))
           (member-equal q (fn-mpxl-cands tag (mv-nth 1 (fn-mpxl-split tab)))))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-split) (fn-mpxl-split-pages-keeps-candidate fn-mpxl-cands))
           :use ((:instance fn-mpxl-split-pages-keeps-candidate
                            (pgs (fn-mpxl-pages tab)) (n (fn-mpxl-n tab)) (s (fn-mpxl-s tab)))))))

(defthm fn-mpxl-pages-okp-of-append
  (equal (fn-mpxl-pages-okp (append a b) n)
         (and (fn-mpxl-pages-okp a n) (fn-mpxl-pages-okp b n))))

(defthm fn-mpxl-split-okp
  (implies (and (fn-mpxl-tabp tab) (mv-nth 0 (fn-mpxl-split tab)) (fn-mpxl-okp tab n))
           (fn-mpxl-okp (mv-nth 1 (fn-mpxl-split tab)) n))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-split-pages) (fn-mpxl-page)) :do-not-induct t)))

(defthm fn-mpxl-okp-mono
  (implies (and (fn-mpxl-okp tab n) (natp n) (natp n2) (<= n n2))
           (fn-mpxl-okp tab n2)))

; -----------------------------------------------------------------------------
; 6. Preservation of the faithful relation.

(defthm fn-mpxl-faithful-from-of-split
  (implies (and (fn-mpxl-tabp tab) (mv-nth 0 (fn-mpxl-split tab))
                (fn-mpxl-faithful-from i tab rows))
           (fn-mpxl-faithful-from i (mv-nth 1 (fn-mpxl-split tab)) rows))
  :hints (("Goal" :induct (fn-mpxl-faithful-from i tab rows)
           :in-theory (disable fn-mpxl-cands fn-cei-event-article fn-held-p fn-record-msgid))))

; KEYSTONE: a split preserves the faithful relation -- the reader after the
; split is still the specification (with `fn-mpxl-records-is-the-records-for').
(defthm fn-mpxl-split-preserves-faithful
  (implies (and (fn-mpxl-tabp tab) (mv-nth 0 (fn-mpxl-split tab))
                (fn-mpxl-faithful tab rows))
           (fn-mpxl-faithful (mv-nth 1 (fn-mpxl-split tab)) rows))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-faithful) (fn-mpxl-okp fn-mpxl-faithful-from)))))

(defthm fn-mpxl-faithful-from-of-put
  (implies (and (fn-mpxl-tabp tab) (natp wtag) (natp seq)
                (fn-mpxl-faithful-from i tab rows))
           (fn-mpxl-faithful-from i (mv-nth 1 (fn-mpxl-put wtag seq tab)) rows))
  :hints (("Goal" :induct (fn-mpxl-faithful-from i tab rows)
           :in-theory (disable fn-mpxl-cands fn-cei-event-article fn-held-p fn-record-msgid))))

(local (defthm fn-mpxl-nth-of-append-one
  (implies (natp i)
           (equal (nth i (append rows (list h)))
                  (if (< i (len rows)) (nth i rows) (if (equal i (len rows)) h nil))))
  :hints (("Goal" :in-theory (enable nth) :induct (nth i rows)))))

(defthm fn-mpxl-faithful-from-beyond
  (implies (>= (nfix i) (len rows))
           (fn-mpxl-faithful-from i tab rows)))

(defthm fn-mpxl-faithful-from-append
  (implies (and (true-listp rows) (natp i)
                (fn-mpxl-faithful-from i tab rows)
                (or (not (fn-held-p (fn-cei-event-article h)))
                    (member-equal (len rows)
                                  (fn-mpxl-cands (fn-mpx-tag (fn-record-msgid (fn-cei-event-article h))) tab))))
           (fn-mpxl-faithful-from i tab (append rows (list h))))
  :hints (("Goal" :induct (fn-mpxl-faithful-from i tab (append rows (list h)))
           :in-theory (disable fn-mpxl-cands fn-cei-event-article fn-held-p fn-record-msgid))))

; The put of a held row's entry at its sequence keeps the table faithful to
; the rows with that row appended.
(defthm fn-mpxl-put-preserves-faithful
  (implies (and (fn-mpxl-tabp tab) (true-listp rows)
                (fn-mpxl-faithful tab rows)
                (fn-held-p (fn-cei-event-article h))
                (mv-nth 0 (fn-mpxl-put (fn-mpx-tag (fn-record-msgid (fn-cei-event-article h))) (len rows) tab)))
           (fn-mpxl-faithful (mv-nth 1 (fn-mpxl-put (fn-mpx-tag (fn-record-msgid (fn-cei-event-article h))) (len rows) tab))
                             (append rows (list h))))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-faithful)
                                  (fn-mpxl-okp fn-mpxl-faithful-from fn-mpxl-cands fn-held-p fn-record-msgid
                                   fn-cei-event-article fn-mpxl-put-finds fn-mpxl-faithful-from-append))
           :do-not-induct t
           :use ((:instance fn-mpxl-put-finds
                            (tag (fn-mpx-tag (fn-record-msgid (fn-cei-event-article h)))) (seq (len rows)))
                 (:instance fn-mpxl-faithful-from-append (i 0)
                            (tab (mv-nth 1 (fn-mpxl-put (fn-mpx-tag (fn-record-msgid (fn-cei-event-article h))) (len rows) tab))))
                 (:instance fn-mpxl-put-okp
                            (tag (fn-mpx-tag (fn-record-msgid (fn-cei-event-article h)))) (seq (len rows))
                            (n (len rows)) (n2 (+ 1 (len rows))))))))

; A row that is not a held article needs no entry.
(defthm fn-mpxl-faithful-append-not-held
  (implies (and (true-listp rows)
                (fn-mpxl-faithful tab rows)
                (not (fn-held-p (fn-cei-event-article h))))
           (fn-mpxl-faithful tab (append rows (list h))))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-faithful)
                                  (fn-mpxl-okp fn-mpxl-faithful-from fn-mpxl-cands fn-held-p
                                   fn-cei-event-article fn-mpxl-faithful-from-append))
           :use ((:instance fn-mpxl-faithful-from-append (i 0))
                 (:instance fn-mpxl-okp-mono (n (len rows)) (n2 (+ 1 (len rows))))))))
