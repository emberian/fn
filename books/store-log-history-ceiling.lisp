; fn: a log record's HISTORY at a ceiling the record itself decides
; (Builder L, landing 2a-host repair, 2026-10-11; prefix `fn-lgo-').
;
; The pre-open suffix scan (books/store-log-open-scan.lisp) charges each
; record's eight wire fields exactly; HISTORY (fn-ct-row-history, the padded
; SCC length of the interned ROW) also reads the arena handle and the
; statement context, which the open decides and the log past S does not
; carry (build/log-runs/l2/SEAM-history-field.md).  This book bounds HISTORY
; by a function of the record alone, over every handle, keyring and
; generation the intern can be given:
;   - a record or composite: 7 (the pad) + the tree ceiling of the row the
;     scan builds (handle 0, the empty keyring) + the handle's ceiling + the
;     context's ceiling over every keyring and generation;
;   - any other wire event: its own HISTORY, exactly (the intern keeps it).
; The tree ceiling counts every cons and every atom's octets and never
; packs a list of octets, so it bounds the encoding from above.  A number
; the codec can encode has at most 255 digits (fn-scc-nat-encodablep), so
; the handle and the generation cost at most 257 octets each; a row that is
; not encodable has HISTORY 0.
;
; It replaces the profile's per-row allowance (fn-adm-row-allowance, the
; widest row the profile admits, 34,996,915 octets under the development
; profile's 65,535 groups), which charged 64 small posts 2.24 GB of history
; and refused a read of a 72-article store (C4, test_native_checkpoint_auto
; kill-between-batches, 2026-10-11).
;
; KEYSTONE
;   L2H-5 fn-lgo-history-ceiling-bounds-the-intern
;                                        the row the intern builds from W at
;                                        any handle, keyring and generation
;                                        has HISTORY at most the ceiling of W

(in-package "ACL2")
(include-book "store-intern")
(include-book "charged-totals")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; 1. The row the scan builds.

; The held row the intern builds from wire record A (books/catalog-record.lisp
; fn-cat-intern-list) at handle 0, under the empty keyring and generation 0.
; The handle and the context are the two fields the scan cannot know; no
; total but HISTORY reads them.
(defun fn-lgo-held-of (a)
  (declare (xargs :guard (fn-record-p a) :verify-guards nil))
  (let ((bytes (fn-record-payload a)))
    (fn-held-make (fn-record-sequence a) (fn-record-txid a)
                  (fn-record-generation a) (fn-record-msgid a) 0
                  (fn-record-groups a) (fn-record-obligation-id a)
                  (fn-record-content-subject a) (fn-record-release-evidence a)
                  (fn-record-charge a) (fn-record-stamp a)
                  (fn-held-facts-of bytes)
                  (fn-held-context-of bytes nil 0)
                  nil nil)))

; The row the intern builds from wire event W, up to handle and context
; (books/store-intern.lisp fn-intern-event); :bad where the intern refuses.
(defun fn-lgo-wire-row (w)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-record-p w) (fn-lgo-held-of w))
        ((fn-stxa-p w)
         (let ((a (fn-replay-composite-record w)))
           (if (fn-record-p a) (fn-hstxa-make w (fn-lgo-held-of a)) :bad)))
        ((fn-wire-event-p w) w)
        (t :bad)))

; -----------------------------------------------------------------------------
; 2. The ceilings.

; Every cons one octet, every atom its octets: the encoding with no list of
; octets packed.
(defun fn-lgo-tree-ceiling (x)
  (declare (xargs :guard t))
  (if (consp x)
      (+ 1 (fn-lgo-tree-ceiling (car x)) (fn-lgo-tree-ceiling (cdr x)))
    (if (fn-scc-atomp x) (len (fn-scc-atom-octets x)) 0)))

; An encodable natural: its tag, its digit count, at most 255 digits.
(defconst *fn-lgo-nat-ceiling* 257)

(defun fn-lgo-max-ceiling (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (max (fn-lgo-tree-ceiling (car xs)) (fn-lgo-max-ceiling (cdr xs)))
    0))

; The verdict's token and its detail when the detail is a word
; (books/stx-verify.lisp fn-stx-verdict, fn-stx-verdict-of-octets).
(defconst *fn-lgo-verdict-words-ceiling*
  (+ (fn-lgo-max-ceiling '(:verified :unverified :absent))
     (fn-lgo-max-ceiling '(:no-field :malformed :ref-mismatch :signature))))

; The context of BYTES under any keyring and generation
; (fn-held-context-of): (VERDICT DELTA G), VERDICT = (TOKEN DETAIL G), the
; detail a word or the statement's creator, the delta empty or the
; statement, G a natural.
(defun fn-lgo-context-ceiling (bytes)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((a (fn-stx-parse bytes))
         (st (and a (ec-call (fn-stx-statement-of a)))))
    (+ 8 (* 2 *fn-lgo-nat-ceiling*) *fn-lgo-verdict-words-ceiling*
       (fn-lgo-tree-ceiling (and st (ec-call (fn-stmt-creator st))))
       (fn-lgo-tree-ceiling (list st)))))

; HISTORY of W's row at a ceiling W decides.
(defun fn-lgo-history-ceiling (w)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-record-p w)
         (+ 7 (fn-lgo-tree-ceiling (fn-lgo-wire-row w)) *fn-lgo-nat-ceiling*
            (fn-lgo-context-ceiling (fn-record-payload w))))
        ((fn-stxa-p w)
         (+ 7 (fn-lgo-tree-ceiling (fn-lgo-wire-row w)) *fn-lgo-nat-ceiling*
            (fn-lgo-context-ceiling (fn-record-payload (fn-replay-composite-record w)))))
        (t (fn-ct-row-history w))))

(verify-guards fn-lgo-held-of
  :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp fn-record-internals))))
(verify-guards fn-lgo-wire-row)
(verify-guards fn-lgo-context-ceiling)
(verify-guards fn-lgo-history-ceiling)

; -----------------------------------------------------------------------------
; 3. The ceiling bounds HISTORY.  The tree ceiling bounds the encoding (a
; packed list of N octets costs 2 + N + its count's digits, its tree 3N + 1);
; a member of an encodable tree is encodable, so the handle and the
; generation cost at most 257 octets each; the context's verdict is a word
; pair or (:verified CREATOR G), its delta empty or the statement.

(encapsulate ()
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-lgo-le-digits-len-le
    (implies (natp n) (<= (len (fn-scc-le-digits n)) n))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable fn-scc-le-digits)))))

(local
 (defthm fn-lgo-tree-ceiling-of-octets
    (implies (fn-scc-octet-listp x)
             (<= (+ 1 (* 3 (len x))) (fn-lgo-tree-ceiling x)))
    :rule-classes :linear
    :hints (("Goal" :induct (len x)
             :in-theory (enable fn-scc-octet-listp fn-scc-octetp fn-scc-atomp fn-scc-atom-octets
                                fn-scc-nat-encodablep fn-scc-nat-octets)))))

(local
 (defthm fn-lgo-tree-ceiling-of-octet
    (implies (fn-scc-octetp x) (<= 2 (fn-lgo-tree-ceiling x)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable fn-scc-octetp fn-scc-atomp fn-scc-atom-octets
                                       fn-scc-nat-encodablep fn-scc-nat-octets)))))

(local
 (defthm fn-lgo-program-len-within-tree-ceiling
   (implies (fn-sccb-treep x)
            (<= (fn-scc-program-len x acc) (+ acc (fn-lgo-tree-ceiling x))))
   :hints (("Goal" :induct (fn-scc-program-len x acc)
            :in-theory (enable fn-scc-nat-octets fn-scc-octets-valuep)
            :expand ((fn-sccb-treep x) (fn-lgo-tree-ceiling x) (fn-scc-program-len x acc)))
           ("Subgoal *1/1" :use ((:instance fn-lgo-le-digits-len-le (n (len x)))
                                 (:instance fn-lgo-tree-ceiling-of-octets (x (cdr x)))
                                 (:instance fn-lgo-tree-ceiling-of-octet (x (car x))))
            :in-theory (e/d (fn-scc-nat-octets fn-scc-octets-valuep fn-scc-octet-listp)
                            (fn-lgo-tree-ceiling))))))

(local
 (defthm fn-lgo-row-history-within-tree-ceiling
   (<= (fn-ct-row-history row) (+ 7 (fn-lgo-tree-ceiling row)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-ct-row-history fn-hp-x-rowlen fn-hp-pad8-count)
                                   (fn-lgo-tree-ceiling fn-scc-program-len fn-sccb-treep
                                    fn-lgo-program-len-within-tree-ceiling))
            :use ((:instance fn-lgo-program-len-within-tree-ceiling (x row) (acc 0)))))))

(local
 (defthm fn-lgo-octet-digits
    (implies (and (natp y) (< y 256))
             (fn-scc-octet-listp (fn-scc-atom-octets y)))
    :hints (("Goal" :in-theory (enable fn-scc-atom-octets fn-scc-nat-octets fn-scc-le-digits
                                       fn-scc-octet-listp fn-scc-octetp)
             :expand ((fn-scc-le-digits y) (fn-scc-le-digits (floor y 256)))))))

(local
 (defthm fn-lgo-nat-within-ceiling
   (implies (and (fn-sccb-treep n) (natp n))
            (<= (fn-lgo-tree-ceiling n) *fn-lgo-nat-ceiling*))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-sccb-treep fn-scc-atomp fn-scc-atom-octets fn-scc-nat-octets
                                      fn-scc-octet-listp fn-scc-octetp fn-scc-octets-valuep)))))

(local
 (defthm fn-lgo-member-within-max-ceiling
   (implies (member-equal x xs)
            (<= (fn-lgo-tree-ceiling x) (fn-lgo-max-ceiling xs)))
   :rule-classes nil))

(local
 (defthm fn-lgo-verdict-shape
   (let ((v (fn-stx-verdict-of-octets bytes keyring g))
         (st (fn-stx-statement-of (fn-stx-parse bytes))))
     (and (equal v (list (car v) (cadr v) g))
          (member-equal (car v) '(:verified :unverified :absent))
          (or (member-equal (cadr v) '(:no-field :malformed :ref-mismatch :signature))
              (and (fn-stx-parse bytes) st
                   (equal (cadr v) (fn-stmt-creator st))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-stx-verdict-of-octets (:d fn-stx-verdict) (:d fn-stx-statement-of)
                                      fn-stx-make-verdict)))))

(local
 (defthm fn-lgo-delta-shape
   (let ((d (fn-stx-delta bytes keyring)))
     (or (equal d nil)
         (equal d (list (fn-stx-statement-of (fn-stx-parse bytes))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable (:d fn-stx-delta))))))

(local
 (defthm fn-lgo-le-digits-octets
   (fn-scc-octet-listp (fn-scc-le-digits n))
   :hints (("Goal" :in-theory (enable fn-scc-le-digits fn-scc-octet-listp fn-scc-octetp)))))

(local
 (defun fn-lgo-digits-ind (m n)
   (declare (xargs :measure (nfix n) :hints (("Goal" :in-theory (enable zp)))))
   (if (or (zp m) (zp n)) (list m n)
     (fn-lgo-digits-ind (floor m 256) (floor n 256)))))

(local
 (defthm fn-lgo-floor-monotone
   (implies (and (natp m) (natp n) (<= m n)) (<= (floor m 256) (floor n 256)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable floor)
            :use ((:instance floor-bounded-by-/ (x m) (y 256)) (:instance floor-bounded-by-/ (x n) (y 256)))))))

(local
 (defthm fn-lgo-le-digits-len-monotone
   (implies (and (natp m) (natp n) (<= m n))
            (<= (len (fn-scc-le-digits m)) (len (fn-scc-le-digits n))))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-lgo-digits-ind m n) :in-theory (e/d (fn-scc-le-digits) (floor))
            :expand ((fn-scc-le-digits m) (fn-scc-le-digits n))))))

(local
 (defthm fn-lgo-treep-of-car-and-cdr
   (implies (and (fn-sccb-treep x) (consp x))
            (and (fn-sccb-treep (car x)) (fn-sccb-treep (cdr x))))
   :hints (("Goal" :in-theory (enable fn-scc-octets-valuep fn-scc-octet-listp fn-scc-octetp
                                      fn-scc-atomp fn-scc-nat-encodablep fn-scc-nat-octets)
            :expand ((fn-sccb-treep x) (fn-sccb-treep (car x)) (fn-sccb-treep (cdr x)))
            :use ((:instance fn-lgo-le-digits-len-monotone (m (len (cdr x))) (n (len x))))))))

(local
 (defthm fn-lgo-treep-of-cons
   (implies (fn-sccb-treep (cons a b))
            (and (fn-sccb-treep a) (fn-sccb-treep b)))
   :rule-classes :forward-chaining
   :hints (("Goal" :use ((:instance fn-lgo-treep-of-car-and-cdr (x (cons a b))))))))

(local
 (defthm fn-lgo-verdict-within-ceiling
   (let ((v (fn-stx-verdict-of-octets bytes keyring g))
         (st (fn-stx-statement-of (fn-stx-parse bytes))))
     (implies (and (natp g) (fn-sccb-treep g))
              (<= (fn-lgo-tree-ceiling v)
                  (+ 4 *fn-lgo-nat-ceiling* *fn-lgo-verdict-words-ceiling*
                     (fn-lgo-tree-ceiling (and (fn-stx-parse bytes) st (fn-stmt-creator st)))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d () (fn-stx-verdict-of-octets fn-stx-statement-of fn-stx-parse
                                       fn-stmt-creator fn-lgo-max-ceiling))
            :use (fn-lgo-verdict-shape
                  (:instance fn-lgo-member-within-max-ceiling
                             (x (car (fn-stx-verdict-of-octets bytes keyring g)))
                             (xs '(:verified :unverified :absent)))
                  (:instance fn-lgo-member-within-max-ceiling
                             (x (cadr (fn-stx-verdict-of-octets bytes keyring g)))
                             (xs '(:no-field :malformed :ref-mismatch :signature)))
                  (:instance fn-lgo-nat-within-ceiling (n g)))))))

(local
 (defthm fn-lgo-context-within-ceiling
   (let ((ctx (fn-held-context-of bytes keyring g)))
     (implies (and (natp g) (fn-sccb-treep ctx))
              (<= (fn-lgo-tree-ceiling ctx) (fn-lgo-context-ceiling bytes))))
   :hints (("Goal" :in-theory (e/d (fn-held-context-of fn-hc-make)
                                   (fn-stx-verdict-of-octets fn-stx-statement-of fn-stx-parse fn-stx-delta
                                    fn-stmt-creator fn-lgo-max-ceiling))
            :use (fn-lgo-verdict-within-ceiling
                  (:instance fn-lgo-delta-shape)
                  (:instance fn-lgo-nat-within-ceiling (n g)))))))

(local
 (defthm fn-lgo-held-intern-within-ceiling
   (let ((row (mv-nth 0 (fn-cat-intern-list a keyring generation fn-arena))))
     (implies (and (natp generation) (fn-sccb-treep row))
              (<= (fn-lgo-tree-ceiling row)
                  (+ (fn-lgo-tree-ceiling (fn-lgo-held-of a)) *fn-lgo-nat-ceiling*
                     (fn-lgo-context-ceiling (fn-record-payload a))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-cat-intern-list fn-held-make fn-lgo-held-of)
                                   (fn-held-context-of fn-held-facts-of fn-lgo-context-ceiling
                                    fn-lgo-tree-ceiling fn-arena-seal-list))
            :expand ((:free (x y) (fn-lgo-tree-ceiling (cons x y))))
            :use ((:instance fn-lgo-context-within-ceiling (bytes (fn-record-payload a)) (g generation))
                  (:instance fn-lgo-nat-within-ceiling (n (fn-arena-count fn-arena))))))))

(local
 (defthm fn-lgo-row-history-of-non-tree
   (implies (not (fn-sccb-treep row)) (equal (fn-ct-row-history row) 0))
   :hints (("Goal" :in-theory (enable fn-ct-row-history fn-hp-x-rowlen)))))

; KEYSTONE L2H-5.  The row the intern builds from W (books/store-intern.lisp
; fn-intern-event), at any handle the arena holds, under any keyring and
; natural generation, has HISTORY at most W's ceiling.
(defthm fn-lgo-history-ceiling-bounds-the-intern
  (let ((row (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))
    (implies (and (natp generation) (not (equal row :bad)))
             (<= (fn-ct-row-history row) (fn-lgo-history-ceiling w))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-lgo-history-ceiling fn-lgo-wire-row fn-hstxa-make)
                                  (fn-cat-intern-list fn-lgo-held-of fn-lgo-context-ceiling
                                   fn-lgo-tree-ceiling fn-ct-row-history fn-record-p fn-stxa-p
                                   fn-wire-event-p fn-replay-composite-record))
           :expand ((:free (x y) (fn-lgo-tree-ceiling (cons x y))))
           :cases ((fn-sccb-treep (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))
           :use ((:instance fn-lgo-held-intern-within-ceiling (a w))
                 (:instance fn-lgo-held-intern-within-ceiling (a (fn-replay-composite-record w)))
                 (:instance fn-lgo-row-history-within-tree-ceiling
                            (row (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))))))
)
