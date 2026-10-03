; fn: the committed event catalog, an attachable abstract stobj (wave 5,
; lane catalog-slice, 2026-09-26; D33; the consolidation design section 1.1).
;
; The LOGICAL value is the committed history as the theorems already know
; it: a true list of held records (books/catalog-record.lisp), oldest first,
; the sequence being the position.  The EXECUTABLE is the indexed tables:
; an array of rows by sequence, a LINEAR-HASHING Message-ID table (books/
; msgid-linear-exec, stage 7: a nested `fn-mlh' of keyed tags in page
; stobjs grown one page split per add, and the count of rows it could not
; place; the heap holds 16 octets an entry, never the Message-ID strings;
; lane catalog-commit-flat replaced the next-generation rebuild), a hash table
; from (group . number) to the sequence
; that number names, a hash table from group to its row count and its next
; number, and the scalar total of retained octets.  The abstraction
; relation `fn-cat$corr' states every cross-field invariant the tables must
; keep against that list, once; `defabsstobj' proves it established by the
; creator and preserved by every export; nothing on a served path evaluates
; it (no whole-state revalidation, AGENTS.md).
;
; Exports (logic over the list C / exec over the tables):
;   fn-cat-count               (len C)                             the count cell
;   fn-cat-at seq              (nth seq C)                         rows[seq]
;   fn-cat-msgid-seqs msgid    (fn-cat-seqs-for msgid C 0)         the table's candidates, confirmed
;                              the sequences of the rows carrying that Message-ID,
;                              ascending (fn-cei-article-records-for over sequences)
;   fn-cat-group-number g n    (fn-cat-number-seq g n C 0)         numbers[(g . n)]
;                              the first row whose numbers bind (g . n), or nil
;   fn-cat-group-next g        (1+ (fn-cat-group-high g C))        groups[g]'s cdr
;   fn-cat-group-count g       (fn-cat-group-rows g C)             groups[g]'s car
;   fn-cat-total-octets        (fn-cat-octets-of C)                the octets cell
;   fn-cat-visible-at seq v    (fn-cat-visiblep seq v C)           rows[seq]'s withdrawal
;                              a row below version V that is not withdrawn, or withdrawn
;                              at a version V does not exceed
;   fn-cat-commit h            (append C (list (fn-cat-assign h C)))  :protect t
;                              the numbers assigned from the groups' nexts, every
;                              table advanced, no walk of C
;   fn-cat-withdraw target by  (fn-cat-mark-withdrawn target (len C) by C)  :protect t
;                              the first cancel wins; its version is the count
;   fn-cat-redecide seq ctx    (update-nth seq (row with context ctx) C)     :protect t
;   fn-cat-clear               nil                                  :protect t
;   fn-cat-clear-keyed key     nil                                  :protect t
;                              the table emptied under KEY (the open's step; the
;                              tags of the entries a table holds are its key's)
;   fn-cat-msgid-saturatedp key msgid   (fn-mlh-build-saturatedp key msgid C)
;                              the fold over C could not place one more row carrying
;                              msgid: the served POST's refusal before durable acceptance
;   fn-cat-index-health key    (fn-mlh-build-health key C)        (pages count unplaced stuck)
;
; The numbers are assigned at commit and never reassigned: a group's next
; number is one past the highest it has bound, so the number table is
; append-only and a number names at most one row (fn-cat-number-seq finds
; the first, and the first is the only).  Visibility is a versioned fact: a
; view is a version (a count), and a row withdrawn at version W is visible
; to a reader at version V <= W.
;
; No book above this one names fn-cat$c; a second implementation of the
; same logical side is an `attach-stobj' in the image's include order
; (design section 3).  No skip-proofs.

(in-package "ACL2")
(include-book "catalog-record")
(include-book "catalog-availability")
(include-book "catalog-number-assignment")
(include-book "msgid-linear-exec")
(include-book "def-loop")

; The tau system is off in this book: it is time no prover step counts, and
; on these goals it was half the proof time (ACL2 time over the book's own
; forms 9.4 -> 4.9 s at the same 2.33M steps, persvati REPL 2026-09-28,
; lane d26-books-2).  The one proof that uses it turns it back on.
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; Held record helpers: a row's number in a group, and the three row updates
; that keep its keys (Message-ID, numbers, facts).





; fn-held-with-numbers, fn-held-with-withdrawn and fn-held-with-context are
; books/held-record.lisp (moved down for the store machine, records-flip).

; -----------------------------------------------------------------------------
; The catalog's row SHAPE: a held record whose context's delta is not
; examined (flip-L8-2, 2026-09-27).  The records flip made the held
; recognizer `fn-held-p' check the context's delta with `fn-lace-p', which
; checks each statement's content address (books/statement.lisp fn-stmt-p ->
; fn-stmt-payload-ref -> fn-digest).  A stobj recognizer and its
; correspondence may not have a supporter that is attached (ACL2 :doc
; stobj-attachment-restrictions), and books/crypto-attach attaches fn-digest:
; so with fn-held-listp as the catalog's recognizer no book could include
; both the catalog and crypto-attach.  The catalog reads a row's numbers,
; withdrawal, octets and keys, never the delta; its recognizer and
; correspondence are over this digest-free shape (`fn-cat-rowsp'), a held
; row is one (`fn-held-p-implies-cat-rowp'), and a book that needs the full
; held recognizer of the catalog's rows carries fn-held-listp beside
; fn-cat-p (commit, withdraw and redecide preserve it: fn-cat-commit-keeps-
; held-listp, fn-cat-withdraw-keeps-held-listp, fn-cat-redecide-keeps-held-
; listp).
(defun fn-cat-ctxp (x)
  (declare (xargs :guard t))
  (and (fn-hc-shapep x)
       (fn-hc-verdictp (fn-hc-verdict x))
       (natp (fn-hc-generation x))
       t))

(fn-payload-kind fn-cat-rowp :handle "the row's payload is a handle (natp)")
(defun fn-cat-rowp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-held-shapep x)
       (fn-record-uint64p (fn-held-sequence x))
       (fn-record-uint64p (fn-held-txid x))
       (fn-record-uint64p (fn-held-generation x))
       (fn-record-msgidp (fn-held-msgid x))
       (natp (fn-held-payload x))
       (fn-record-groups-validp (fn-held-groups x))
       (fn-record-metadata-bytes-p (fn-held-obligation-id x))
       (fn-record-metadata-bytes-p (fn-held-content-subject x))
       (fn-record-metadata-bytes-p (fn-held-release-evidence x))
       (fn-record-uint64p (fn-held-charge x))
       (fn-record-stampp (fn-held-stamp x))
       (fn-hf-p (fn-held-facts x))
       (fn-cat-ctxp (fn-held-context x))
       (fn-held-numbersp (fn-held-numbers x))
       (fn-held-withdrawnp (fn-held-withdrawn x))))

(verify-guards fn-cat-rowp)

(defun fn-cat-rowsp (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      (null xs)
    (and (fn-cat-rowp (car xs)) (fn-cat-rowsp (cdr xs)))))

(defthm fn-held-p-implies-cat-rowp
  (implies (fn-held-p x) (fn-cat-rowp x))
  :hints (("Goal" :in-theory (enable fn-held-p fn-hc-p))))

(defthm fn-cat-rowp-fields
  (implies (fn-cat-rowp h)
           (and (natp (fn-record-payload h))
                (fn-hf-p (fn-held-facts h))
                (fn-held-numbersp (fn-held-numbers h))
                (fn-held-withdrawnp (fn-held-withdrawn h))))
  :hints (("Goal" :in-theory (enable fn-held-accessors-are-the-wire-accessors))))

(in-theory (disable fn-cat-rowp fn-cat-ctxp))

(defthm fn-held-listp-implies-cat-rowsp
  (implies (fn-held-listp xs) (fn-cat-rowsp xs)))

; For includers.  In this book it fires on every row-list goal and never helps
; (86,238 frames, none useful; 2026-09-28).
(local (in-theory (disable fn-held-listp-implies-cat-rowsp)))

(defthm fn-cat-rowsp-forward-true-listp
  (implies (fn-cat-rowsp xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defthm fn-cat-rowp-of-nth-of-rowsp
  (implies (and (fn-cat-rowsp xs) (natp i) (< i (len xs)))
           (fn-cat-rowp (nth i xs))))

(defthm fn-cat-rowsp-of-update-nth
  (implies (and (fn-cat-rowsp xs) (fn-cat-rowp h) (natp i) (< i (len xs)))
           (fn-cat-rowsp (update-nth i h xs))))

(defthm fn-cat-rowsp-of-append-one
  (implies (and (fn-cat-rowsp xs) (fn-cat-rowp h))
           (fn-cat-rowsp (append xs (list h)))))


; -----------------------------------------------------------------------------
; The logical model: the columns as functions of the list.

; The sequences of the rows carrying MSGID, ascending, the first row being I.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cat-seqs-for-loop (msgid c i acc)
  (declare (xargs :guard (and (natp i) (true-listp acc)) :verify-guards nil))
  (if (consp c)
      (if (equal msgid (fn-record-msgid (car c)))
          (fn-cat-seqs-for-loop msgid (cdr c) (+ 1 i) (cons i acc))
        (fn-cat-seqs-for-loop msgid (cdr c) (+ 1 i) acc))
    (revappend acc nil)))

(defun fn-cat-seqs-for (msgid c i)
  (declare (xargs :verify-guards nil :guard (natp i)))
  (mbe :logic
       (if (consp c)
           (if (equal msgid (fn-record-msgid (car c)))
               (cons i (fn-cat-seqs-for msgid (cdr c) (+ 1 i)))
             (fn-cat-seqs-for msgid (cdr c) (+ 1 i)))
         nil)
       :exec (fn-cat-seqs-for-loop msgid c i nil)))

(local
 (defthm fn-cat-seqs-for-loop-is-revappend
   (equal (fn-cat-seqs-for-loop msgid c i acc)
          (revappend acc (fn-cat-seqs-for msgid c i)))
   :hints (("Goal" :induct (fn-cat-seqs-for-loop msgid c i acc)
                   :in-theory (union-theories '(fn-cat-seqs-for-loop fn-cat-seqs-for revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cat-seqs-for-loop)

(verify-guards fn-cat-seqs-for
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cat-seqs-for)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cat-seqs-for-loop-is-revappend (acc nil))))))


; The first row binding (GROUP . N), or nil; a row outside the group binds
; nothing, so no N matches it.


; The highest number bound in GROUP (0 when none).


; The rows bound in GROUP.
(defun fn-cat-group-rows (group c)
  (declare (xargs :guard t))
  (if (consp c)
      (+ (if (fn-held-number-in group (car c)) 1 0)
         (fn-cat-group-rows group (cdr c)))
    0))

; The retained octets: the sum of the rows' octet facts.
(defun fn-cat-octets-of (c)
  (declare (xargs :guard t))
  (if (consp c)
      (+ (nfix (fn-hf-octets (fn-held-facts (car c))))
         (fn-cat-octets-of (cdr c)))
    0))

; The numbers a commit assigns: one past each group's high.




; A row below version V, not withdrawn or withdrawn at a version V does
; not exceed.
;
; The one field fact the guards over a row's withdrawal need, without opening
; the closed held recognizer: a present withdrawal is an (at . by) pair of
; naturals.
(local
 (defthm fn-ctg-withdrawn-present-is-pair
   (implies (and (fn-held-withdrawnp w) w)
            (and (consp w) (natp (car w)) (natp (cdr w))))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn-held-withdrawnp)))))

; Its rewrite form fires on every consp and natp goal and relieves the
; recognizer each time (283,311 frames, 51 useful); the forward-chaining form
; supplies the same facts from the hypothesis once per goal.
(local (in-theory (disable (:rewrite fn-ctg-withdrawn-present-is-pair))))

; And the withdrawal a cancel writes, (at . by), is one.
(local
 (defthm fn-ctg-withdrawnp-of-pair
   (implies (and (natp at) (natp by))
            (fn-held-withdrawnp (cons at by)))
   :hints (("Goal" :in-theory (enable fn-held-withdrawnp)))))

(defun fn-cat-visiblep (seq v c)
  (declare (xargs :guard (and (natp seq) (natp v) (fn-cat-rowsp c) (< seq (len c)))
                  :guard-hints
                  (("Goal" :in-theory
                    (enable (:rewrite fn-ctg-withdrawn-present-is-pair)
                            (tau-system))))))
  (and (< seq v)
       (let ((w (fn-held-withdrawn (nth seq c))))
         (or (null w) (<= v (car w))))))

(defun fn-cat-mark-withdrawn (target v by c)
  (declare (xargs :guard (and (natp target) (natp v) (natp by) (fn-cat-rowsp c))))
  (if (and (< target (len c))
           (null (fn-held-withdrawn (nth target c))))
      (update-nth target (fn-held-with-withdrawn (nth target c) (cons v by)) c)
    c))

;; -----------------------------------------------------------------------------
;; The live summary of a group (lane sca-join-5, F2): the numbers a served
;; GROUP/LISTGROUP counts, over the rows no withdrawal has marked.
;;
;; A number K of GROUP is LIVE when the row the number table binds it to is
;; not withdrawn and K is a served number: positive, within RFC 3977's bound,
;; its row's Message-ID renderable (books/nntp-projection.lisp
;; fn-nntp-article-number's three tests; fn-scat-msgid-idp reads the third
;; from the row's Message-ID without its payload).  The summary is the count
;; of live numbers, the least and the greatest, over 1 .. the group's high:
;; stated number-wise over the number column, so it needs no uniqueness of
;; numbers (the column answers the first row binding K).  The catalog keeps
;; it in a table maintained by commit and withdraw (the exports
;; fn-cat-group-live-count/-low/-high below), so a served summary reads three
;; cells instead of probing every number.  A reader at version V sees the
;; same numbers when V is the count and no withdrawal is at or past V: the
;; HORIZON (one past the latest withdrawal's version, fn-cat-horizon-of) is
;; that bound, and books/served-catalog.lisp falls back to the probe pass
;; below it.

(defun fn-scat-msgid-idp (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (<= (length text) *fn-nntp-max-message-id-octets*)
       (fn-nntp-message-id-tokenp (fn-nntp-string-octets text))))

(defun fn-cat-live-candidatep (h)
  (declare (xargs :guard t))
  (and (fn-cat-row-availablep h)
       (null (fn-held-withdrawn h))
       (fn-scat-msgid-idp (fn-record-msgid h))))

(defun fn-cat-live-rowp (group k h)
  (declare (xargs :guard t))
  (and (fn-cat-row-availablep h)
       (null (fn-held-withdrawn h))
       (posp k) (<= k *fn-nntp-max-article-number*)
       (equal (fn-held-number-in group h) k)
       (fn-scat-msgid-idp (fn-record-msgid h))))

(defun fn-cat-live-numberp (group k c)
  (declare (xargs :guard (fn-cat-rowsp c)))
  (let ((s (fn-cat-number-seq group k c 0)))
    (and (natp s) (< s (len c))
         (fn-cat-live-rowp group k (nth s c)))))

(defun fn-cat-live-count-from (group k top c)
  (declare (xargs :guard (and (natp k) (natp top) (fn-cat-rowsp c))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (+ (if (fn-cat-live-numberp group k c) 1 0)
         (fn-cat-live-count-from group (+ 1 k) top c))
    0))

(defun fn-cat-live-first (group k top c)
  (declare (xargs :guard (and (natp k) (natp top) (fn-cat-rowsp c))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (if (fn-cat-live-numberp group k c)
          k
        (fn-cat-live-first group (+ 1 k) top c))
    0))

(defun fn-cat-live-last (group k c)
  (declare (xargs :guard (and (natp k) (fn-cat-rowsp c))))
  (if (posp k)
      (if (fn-cat-live-numberp group k c)
          k
        (fn-cat-live-last group (- k 1) c))
    0))

;; One past the latest withdrawal's version over the rows (0 when none).
(defun fn-cat-horizon-of (c)
  (declare (xargs :guard t))
  (if (consp c)
      (let ((w (fn-held-withdrawn (car c))))
        (max (if (consp w) (+ 1 (nfix (car w))) 0)
             (fn-cat-horizon-of (cdr c))))
    0))

; -----------------------------------------------------------------------------
; The logical side of the exports.

(defun fn-cat$ap (x)
  (declare (xargs :guard t))
  (fn-cat-rowsp x))

(defun create-fn-cat$a ()
  (declare (xargs :guard t))
  nil)

(defun fn-cat$a-count (fn-cat$a)
  (declare (xargs :guard t))
  (len fn-cat$a))

(defun fn-cat$a-at (seq fn-cat$a)
  (declare (xargs :guard (and (natp seq) (< seq (fn-cat$a-count fn-cat$a)) (fn-cat$ap fn-cat$a))))
  (nth seq fn-cat$a))

(defun fn-cat$a-msgid-seqs (msgid fn-cat$a)
  (declare (xargs :guard t))
  (fn-cat-seqs-for msgid fn-cat$a 0))

(defun fn-cat$a-group-number (group n fn-cat$a)
  (declare (xargs :guard t))
  (fn-cat-number-seq group n fn-cat$a 0))

(defun fn-cat$a-group-next (group fn-cat$a)
  (declare (xargs :guard t))
  (+ 1 (fn-cat-group-high group fn-cat$a)))

(defun fn-cat$a-group-count (group fn-cat$a)
  (declare (xargs :guard t))
  (fn-cat-group-rows group fn-cat$a))

(defun fn-cat$a-total-octets (fn-cat$a)
  (declare (xargs :guard t))
  (fn-cat-octets-of fn-cat$a))

(defun fn-cat$a-visible-at (seq v fn-cat$a)
  (declare (xargs :guard (and (natp seq) (< seq (fn-cat$a-count fn-cat$a)) (natp v)
                              (fn-cat$ap fn-cat$a))))
  (fn-cat-visiblep seq v fn-cat$a))

(defun fn-cat$a-commit (h fn-cat$a)
  (declare (xargs :guard (and (fn-held-p h) (fn-cat$ap fn-cat$a))))
  (append fn-cat$a (list (fn-cat-assign h fn-cat$a))))

(defun fn-cat$a-withdraw (target by fn-cat$a)
  (declare (xargs :guard (and (natp target) (< target (fn-cat$a-count fn-cat$a)) (natp by)
                              (fn-cat$ap fn-cat$a))))
  (fn-cat-mark-withdrawn target (len fn-cat$a) by fn-cat$a))

(defun fn-cat$a-redecide (seq context fn-cat$a)
  (declare (xargs :guard (and (natp seq) (< seq (fn-cat$a-count fn-cat$a)) (fn-hc-p context)
                              (fn-cat$ap fn-cat$a))))
  (update-nth seq (fn-held-with-context (nth seq fn-cat$a) context) fn-cat$a))

(defun fn-cat$a-clear (fn-cat$a)
  (declare (xargs :guard t) (ignore fn-cat$a))
  nil)

; The keyed clear: the same logical value; the key is the executable's.
(defun fn-cat$a-clear-keyed (key fn-cat$a)
  (declare (xargs :guard (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*)))
           (ignore key fn-cat$a))
  nil)

; The served refusal: the fold of the rows under KEY could not place one
; more row carrying MSGID (books/msgid-pages-exec 7j).
(defun fn-cat$a-msgid-saturatedp (key msgid fn-cat$a)
  (declare (xargs :guard (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*)
                              (fn-cat$ap fn-cat$a))))
  (fn-mlh-build-saturatedp key msgid fn-cat$a))

(defun fn-cat$a-index-health (key fn-cat$a)
  (declare (xargs :guard (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*)
                              (fn-cat$ap fn-cat$a))))
  (fn-mlh-build-health key fn-cat$a))

(defun fn-cat$a-group-live-count (group fn-cat$a)
  (declare (xargs :guard (fn-cat$ap fn-cat$a)))
  (fn-cat-live-count-from group 1 (fn-cat-group-high group fn-cat$a) fn-cat$a))

(defun fn-cat$a-group-live-low (group fn-cat$a)
  (declare (xargs :guard (fn-cat$ap fn-cat$a)))
  (fn-cat-live-first group 1 (fn-cat-group-high group fn-cat$a) fn-cat$a))

(defun fn-cat$a-group-live-high (group fn-cat$a)
  (declare (xargs :guard (fn-cat$ap fn-cat$a)))
  (fn-cat-live-last group (fn-cat-group-high group fn-cat$a) fn-cat$a))

;; Off the recognizer the horizon is past the count, so a reader that
;; takes the fast path when the horizon is at most the count learns that the
;; rows are well formed (books/served-catalog.lisp).
(defun fn-cat$a-horizon (fn-cat$a)
  (declare (xargs :guard t))
  (if (fn-cat-rowsp fn-cat$a) (fn-cat-horizon-of fn-cat$a) (+ 1 (len fn-cat$a))))

; -----------------------------------------------------------------------------
; The foundation.

(defstobj fn-cat$c
  (fn-cat$c-rows :type (array t (0)) :resizable t)
  (fn-cat$c-count :type (integer 0 *) :initially 0)
  ;; THE LINEAR-HASHING MESSAGE-ID TABLE (books/msgid-linear-exec, stage 7):
  ;; a nested table of keyed tags in page stobjs, grown one page split per
  ;; add (no next-generation rebuild); the rows it could not place are
  ;; counted (fn-cat$c-unplaced): 0 on the served path, where the refusal
  ;; fn-cat-msgid-saturatedp keeps it so.
  (fn-cat$c-mpx :type fn-mlh)
  (fn-cat$c-numbers :type (hash-table equal))
  (fn-cat$c-groups :type (hash-table equal))
  (fn-cat$c-octets :type (integer 0 *) :initially 0)
  ;; The live summary (sca-join-5): group -> (count low . high), and the
  ;; withdrawal horizon.
  (fn-cat$c-lives :type (hash-table equal))
  (fn-cat$c-hz :type (integer 0 *) :initially 0)
  ;; The withdrawals by version (lane scale-latency): version -> the rows
  ;; withdrawn at it, ascending.
  (fn-cat$c-wbv :type (hash-table equal))
  (fn-cat$c-unplaced :type (integer 0 *) :initially 0)
  :inline t)

(local
 (defthm fn-ctg-cells-are-naturals
   (implies (fn-cat$cp fn-cat$c)
            (and (natp (fn-cat$c-count fn-cat$c))
                 (natp (fn-cat$c-octets fn-cat$c))
                 (natp (fn-cat$c-hz fn-cat$c))))
   :rule-classes (:rewrite (:forward-chaining :trigger-terms ((fn-cat$cp fn-cat$c))))
   :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-countp fn-cat$c-octetsp
                                      fn-cat$c-hzp)))))

(local
 (defthm fn-ctg-rowsp-true-listp
   (implies (fn-cat$c-rowsp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cat$c-rowsp)))))

(local
 (defthm fn-ctg-rows-true-listp
   (implies (fn-cat$cp fn-cat$c)
            (true-listp (nth 0 fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$cp)))))

(local
 (defthm fn-ctg-len-of-resize-list
   (equal (len (resize-list l n d)) (nfix n))
   :hints (("Goal" :in-theory (enable resize-list)))))

; The recognizer through every writer, and the cells' types, so that the
; exec functions' guards and the obligations reason at the field level and
; never open the stobj into list structure (the arena's fn-arn-cp-* pattern).
(local
 (defthm fn-ctg-rowsp-of-update-nth
   (implies (and (fn-cat$c-rowsp x) (natp i) (< i (len x)))
            (fn-cat$c-rowsp (update-nth i v x)))
   :hints (("Goal" :in-theory (enable fn-cat$c-rowsp)))))

(local
 (defthm fn-ctg-rowsp-of-resize-list
   (implies (fn-cat$c-rowsp x)
            (fn-cat$c-rowsp (resize-list x n nil)))
   :hints (("Goal" :in-theory (enable fn-cat$c-rowsp resize-list)))))

(local
 (defthm fn-ctg-unplaced-is-natural
   (implies (fn-cat$cp fn-cat$c)
            (natp (fn-cat$c-unplaced fn-cat$c)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-unplaced fn-cat$c-unplacedp)))))

(local
 (defthm fn-ctg-cp-index-fields
   (implies (fn-cat$cp fn-cat$c)
            (and (fn-mlhp (nth *fn-cat$c-mpx* fn-cat$c))
                 (natp (nth *fn-cat$c-unplaced* fn-cat$c))))
   :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-unplacedp)))))

(local
 (defthm fn-ctg-unplaced-of-index-writes
   (and (equal (fn-cat$c-unplaced (update-fn-cat$c-mpx x fn-cat$c)) (fn-cat$c-unplaced fn-cat$c))
        (equal (fn-cat$c-unplaced (update-fn-cat$c-unplaced n fn-cat$c)) n))
   :hints (("Goal" :in-theory (enable fn-cat$c-unplaced update-fn-cat$c-mpx
                                      update-fn-cat$c-unplaced)))))

(local
 (defthm fn-ctg-cp-of-update-rowsi
   (implies (and (fn-cat$cp fn-cat$c) (natp i) (< i (fn-cat$c-rows-length fn-cat$c)))
            (fn-cat$cp (update-fn-cat$c-rowsi i v fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$cp update-nth-array)))))

(local
 (defthm fn-ctg-cp-of-resize
   (implies (fn-cat$cp fn-cat$c)
            (fn-cat$cp (resize-fn-cat$c-rows n fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$cp)))))

(local
 (defthm fn-ctg-cp-of-update-count
   (implies (and (fn-cat$cp fn-cat$c) (natp n))
            (fn-cat$cp (update-fn-cat$c-count n fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-countp)))))

(local
 (defthm fn-ctg-cp-of-update-octets
   (implies (and (fn-cat$cp fn-cat$c) (natp n))
            (fn-cat$cp (update-fn-cat$c-octets n fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-octetsp)))))

(local
 (defthm fn-ctg-cp-of-table-writes
   (implies (fn-cat$cp fn-cat$c)
            (and (fn-cat$cp (fn-cat$c-numbers-put k v fn-cat$c))
                 (fn-cat$cp (fn-cat$c-groups-put k v fn-cat$c))
                 (fn-cat$cp (fn-cat$c-lives-put k v fn-cat$c))
                 (fn-cat$cp (fn-cat$c-numbers-clear fn-cat$c))
                 (fn-cat$cp (fn-cat$c-groups-clear fn-cat$c))
                 (fn-cat$cp (fn-cat$c-lives-clear fn-cat$c))))
   :hints (("Goal" :in-theory (enable fn-cat$cp)))))

(local
 (defthm fn-ctg-cp-of-index-writes
   (implies (fn-cat$cp fn-cat$c)
            (and (implies (fn-mlhp x) (fn-cat$cp (update-fn-cat$c-mpx x fn-cat$c)))
                 (implies (natp n) (fn-cat$cp (update-fn-cat$c-unplaced n fn-cat$c)))))
   :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-unplacedp)))))

(local
 (defthm fn-ctg-cp-of-update-hz
   (implies (and (fn-cat$cp fn-cat$c) (natp n))
            (fn-cat$cp (update-fn-cat$c-hz n fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-hzp)))))

(local
 (defthm fn-ctg-rows-length-of-writes
   (and (equal (fn-cat$c-rows-length (resize-fn-cat$c-rows n fn-cat$c)) (nfix n))
        (equal (fn-cat$c-rows-length (update-fn-cat$c-rowsi i v fn-cat$c))
               (if (and (natp i) (< i (fn-cat$c-rows-length fn-cat$c)))
                   (fn-cat$c-rows-length fn-cat$c)
                 (max (1+ (nfix i)) (fn-cat$c-rows-length fn-cat$c))))
        (equal (fn-cat$c-rows-length (update-fn-cat$c-mpx x fn-cat$c))
               (fn-cat$c-rows-length fn-cat$c))
        (equal (fn-cat$c-rows-length (update-fn-cat$c-unplaced n fn-cat$c))
               (fn-cat$c-rows-length fn-cat$c))
        (equal (fn-cat$c-rows-length (fn-cat$c-numbers-put k v fn-cat$c))
               (fn-cat$c-rows-length fn-cat$c))
        (equal (fn-cat$c-rows-length (fn-cat$c-groups-put k v fn-cat$c))
               (fn-cat$c-rows-length fn-cat$c))
        (equal (fn-cat$c-rows-length (update-fn-cat$c-count n fn-cat$c))
               (fn-cat$c-rows-length fn-cat$c))
        (equal (fn-cat$c-rows-length (update-fn-cat$c-octets n fn-cat$c))
               (fn-cat$c-rows-length fn-cat$c)))
   :hints (("Goal" :in-theory (enable update-nth-array)))))

(defun fn-cat$c-wfp (fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (<= (fn-cat$c-count fn-cat$c) (fn-cat$c-rows-length fn-cat$c)))

(defun fn-cat$c-at (seq fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard (and (fn-cat$c-wfp fn-cat$c) (natp seq)
                              (< seq (fn-cat$c-count fn-cat$c)))))
  (fn-cat$c-rowsi seq fn-cat$c))

; THE PAGED READER (design B.6, the 5u method): the candidates for MSGID's
; tag from the nested table, confirmed against the rows array (the twin of
; fn-mpxt-confirm: a candidate at or past the count, or whose row carries
; another Message-ID, is dropped).  When a row could not be placed
; (unplaced > 0: a saturated table the operator has not rebuilt), the
; DEGRADED scan over the rows array answers, correct and O(count); the
; served path never reaches it (fn-cat-msgid-saturatedp refuses first).
(defun fn-cat$c-confirm (msgid seqs fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (nat-listp seqs)))
  (if (consp seqs)
      (let ((rest (fn-cat$c-confirm msgid (cdr seqs) fn-cat$c)))
        (if (and (< (car seqs) (fn-cat$c-count fn-cat$c))
                 (< (car seqs) (fn-cat$c-rows-length fn-cat$c))
                 (equal msgid (fn-record-msgid (fn-cat$c-rowsi (car seqs) fn-cat$c))))
            (cons (car seqs) rest)
          rest))
    nil))

(defun fn-cat$c-scan-msgid (msgid i acc fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (and (natp i) (true-listp acc))
                  :measure (nfix (- (nfix (fn-cat$c-count fn-cat$c)) (nfix i)))))
  (if (or (>= (nfix i) (nfix (fn-cat$c-count fn-cat$c)))
          (>= (nfix i) (fn-cat$c-rows-length fn-cat$c)))
      (revappend acc nil)
    (fn-cat$c-scan-msgid msgid (1+ (nfix i))
                         (if (equal msgid (fn-record-msgid (fn-cat$c-rowsi (nfix i) fn-cat$c)))
                             (cons (nfix i) acc)
                           acc)
                         fn-cat$c)))

(defun fn-cat$c-msgid-seqs (msgid fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard-hints (("Goal" :in-theory (disable fn-mlh-candidates)))))
  (if (eql 0 (fn-cat$c-unplaced fn-cat$c))
      (let ((seqs (stobj-let ((fn-mlh (fn-cat$c-mpx fn-cat$c)))
                             (seqs)
                             (if (fn-mlh-wfp fn-mlh)
                                 (fn-mlh-candidates (fn-mlh-tag-of msgid fn-mlh) fn-mlh)
                               nil)
                             seqs)))
        (fn-cat$c-confirm msgid seqs fn-cat$c))
    (fn-cat$c-scan-msgid msgid 0 nil fn-cat$c)))

(defun fn-cat$c-group-number (group n fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (fn-cat$c-numbers-get (cons group n) fn-cat$c))

(defun fn-cat$c-group-next (group fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let ((e (fn-cat$c-groups-get group fn-cat$c)))
    (if (consp e) (cdr e) 1)))

(defun fn-cat$c-group-count (group fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let ((e (fn-cat$c-groups-get group fn-cat$c)))
    (if (consp e) (car e) 0)))

(defun fn-cat$c-total-octets (fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (fn-cat$c-octets fn-cat$c))

(defun fn-cat$c-visible-at (seq v fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard (and (fn-cat$c-wfp fn-cat$c) (natp seq) (natp v)
                              (< seq (fn-cat$c-count fn-cat$c))
                              (fn-held-withdrawnp
                               (fn-held-withdrawn (fn-cat$c-rowsi seq fn-cat$c))))))
  (and (< seq v)
       (let ((w (fn-held-withdrawn (fn-cat$c-rowsi seq fn-cat$c))))
         (or (null w) (<= v (car w))))))

; The commit's plan: per group, its next number and its old row count, read
; from the tables BEFORE any write, so that a group listed twice gets the
; same number and is counted once (the logical assignment reads C once).
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cat$c-plan-loop (groups fn-cat$c acc)
  (declare (xargs :stobjs fn-cat$c :guard (true-listp acc) :verify-guards nil))
  (if (consp groups)
      (let ((e (fn-cat$c-groups-get (car groups) fn-cat$c)))
        (fn-cat$c-plan-loop (cdr groups)
                            fn-cat$c
                            (cons (list (car groups)
                                        (if (consp e) (nfix (cdr e)) 1)
                                        (if (consp e) (nfix (car e)) 0))
                                  acc)))
    (revappend acc nil)))

(defun fn-cat$c-plan (groups fn-cat$c)
  (declare (xargs :verify-guards nil :stobjs fn-cat$c))
  (mbe :logic
       (if (consp groups)
           (let ((e (fn-cat$c-groups-get (car groups) fn-cat$c)))
             (cons (list (car groups)
                         (if (consp e) (nfix (cdr e)) 1)
                         (if (consp e) (nfix (car e)) 0))
                   (fn-cat$c-plan (cdr groups) fn-cat$c)))
         nil)
       :exec (fn-cat$c-plan-loop groups fn-cat$c nil)))

(local
 (defthm fn-cat$c-plan-loop-is-revappend
   (equal (fn-cat$c-plan-loop groups fn-cat$c acc)
          (revappend acc (fn-cat$c-plan groups fn-cat$c)))
   :hints (("Goal" :induct (fn-cat$c-plan-loop groups fn-cat$c acc)
                   :in-theory (union-theories '(fn-cat$c-plan-loop fn-cat$c-plan revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cat$c-plan-loop)

(verify-guards fn-cat$c-plan
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cat$c-plan)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cat$c-plan-loop-is-revappend (acc nil))))))


; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(def-loop fn-cat-plan-numbers (plan)
  :shape :map
  :body (cons (fn-cbor-ag-car (car plan)) (fn-cbor-ag-car (fn-cbor-ag-cdr (car plan)))))


(defun fn-cat$c-apply-plan (plan seq fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (if (consp plan)
      (let* ((g (fn-cbor-ag-car (car plan)))
             (n (fn-cbor-ag-car (fn-cbor-ag-cdr (car plan))))
             (oc (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr (car plan)))))
             (fn-cat$c (fn-cat$c-numbers-put (cons g n) seq fn-cat$c))
             (fn-cat$c (fn-cat$c-groups-put g (cons (+ 1 (nfix oc)) (+ 1 (nfix n))) fn-cat$c)))
        (fn-cat$c-apply-plan (cdr plan) seq fn-cat$c))
    fn-cat$c))

(local
 (defthm fn-ctg-cells-over-writes
   (and (equal (fn-cat$c-octets (update-fn-cat$c-rowsi i v fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-octets (resize-fn-cat$c-rows n fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-octets (update-fn-cat$c-mpx x fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-octets (update-fn-cat$c-unplaced n fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-octets (fn-cat$c-numbers-put k v fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-octets (fn-cat$c-groups-put k v fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-octets (update-fn-cat$c-count n fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-count (update-fn-cat$c-rowsi i v fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (resize-fn-cat$c-rows n fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (update-fn-cat$c-mpx x fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (update-fn-cat$c-unplaced n fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (fn-cat$c-numbers-put k v fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (fn-cat$c-groups-put k v fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (update-fn-cat$c-octets n fn-cat$c)) (fn-cat$c-count fn-cat$c)))
   :hints (("Goal" :in-theory (enable update-nth-array fn-cat$c-octets fn-cat$c-count
                                      update-fn-cat$c-rowsi resize-fn-cat$c-rows
                                      update-fn-cat$c-mpx update-fn-cat$c-unplaced
                                      fn-cat$c-numbers-put
                                      fn-cat$c-groups-put update-fn-cat$c-count
                                      update-fn-cat$c-octets)))))

(local
 (defthm fn-ctg-cells-over-apply-plan
   (and (equal (fn-cat$c-octets (fn-cat$c-apply-plan plan seq fn-cat$c))
               (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-count (fn-cat$c-apply-plan plan seq fn-cat$c))
               (fn-cat$c-count fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-apply-plan)))))

(local
 (defthm fn-ctg-cp-of-apply-plan
   (implies (fn-cat$cp fn-cat$c)
            (and (fn-cat$cp (fn-cat$c-apply-plan plan seq fn-cat$c))
                 (equal (fn-cat$c-rows-length (fn-cat$c-apply-plan plan seq fn-cat$c))
                        (fn-cat$c-rows-length fn-cat$c))))))

(local
 (in-theory (disable fn-cat$cp fn-cat$c-count update-fn-cat$c-count
                     fn-cat$c-rowsi update-fn-cat$c-rowsi resize-fn-cat$c-rows
                     fn-cat$c-rows-length fn-cat$c-octets update-fn-cat$c-octets
                     fn-cat$c-mpx update-fn-cat$c-mpx
                     fn-cat$c-unplaced update-fn-cat$c-unplaced
                     fn-cat$c-numbers-get fn-cat$c-numbers-put fn-cat$c-numbers-clear
                     fn-cat$c-groups-get fn-cat$c-groups-put fn-cat$c-groups-clear
                     fn-cat$c-lives-get fn-cat$c-lives-put fn-cat$c-lives-clear
                     fn-cat$c-hz update-fn-cat$c-hz)))

; A total snoc: append on a true list, and on anything else the list of one.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cat-snoc-loop (xs x acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp xs)
      (fn-cat-snoc-loop (cdr xs) x (cons (car xs) acc))
    (revappend acc (list x))))

(defun fn-cat-snoc (xs x)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp xs) (cons (car xs) (fn-cat-snoc (cdr xs) x)) (list x))
       :exec (fn-cat-snoc-loop xs x nil)))

(local
 (defthm fn-cat-snoc-loop-is-revappend
   (equal (fn-cat-snoc-loop xs x acc)
          (revappend acc (fn-cat-snoc xs x)))
   :hints (("Goal" :induct (fn-cat-snoc-loop xs x acc)
                   :in-theory (union-theories '(fn-cat-snoc-loop fn-cat-snoc revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cat-snoc-loop)

(verify-guards fn-cat-snoc
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cat-snoc)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cat-snoc-loop-is-revappend (acc nil))))))


;; THE INDEX'S WRITES.  The add is the fold's step (fn-mlh-build-from,
;; books/msgid-pages-exec 7f) made on the live tables: below the word limit
;; the entry is placed (and the table grown at half the slots), or the row
;; is counted unplaced; at the limit it is counted unplaced without a write.
(defun fn-cat$c-index-add (msgid seq fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (natp seq)))
  (if (< (+ 2 seq) *fn-mlh-tag-limit*)
      (stobj-let ((fn-mlh (fn-cat$c-mpx fn-cat$c)))
                 (r fn-mlh)
                 (if (fn-mlh-wfp fn-mlh)
                     (fn-mlh-add (fn-mlh-tag-of msgid fn-mlh) seq fn-mlh)
                   (mv :mpx-unplaced fn-mlh))
                 (if (eq r :placed)
                     fn-cat$c
                   (update-fn-cat$c-unplaced (+ 1 (fn-cat$c-unplaced fn-cat$c)) fn-cat$c)))
    (update-fn-cat$c-unplaced (+ 1 (fn-cat$c-unplaced fn-cat$c)) fn-cat$c)))

;; The clear keeps the key (fn-mlh-clear); nothing is unplaced.
(defun fn-cat$c-index-clear (fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let ((fn-cat$c (update-fn-cat$c-unplaced 0 fn-cat$c)))
    (stobj-let ((fn-mlh (fn-cat$c-mpx fn-cat$c)))
               (fn-mlh)
               (fn-mlh-clear fn-mlh)
               fn-cat$c)))

;; The keyed clear: the open installs the ring's key into an emptied table.
(defun fn-cat$c-index-set-key (key fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let ((fn-cat$c (update-fn-cat$c-unplaced 0 fn-cat$c)))
    (stobj-let ((fn-mlh (fn-cat$c-mpx fn-cat$c)))
               (fn-mlh)
               (fn-mlh-set-key key fn-mlh)
               fn-cat$c)))

(defun fn-cat$c-commit-base (h fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (fn-cat$c-wfp fn-cat$c)))
  (let* ((seq (fn-cat$c-count fn-cat$c))
         (plan (fn-cat$c-plan (fn-record-groups h) fn-cat$c))
         (row (fn-held-with-numbers h (fn-cat-plan-numbers plan)))
         (fn-cat$c (fn-cat$c-index-add (fn-record-msgid h) seq fn-cat$c))
         (fn-cat$c (if (< seq (fn-cat$c-rows-length fn-cat$c))
                       fn-cat$c
                     (resize-fn-cat$c-rows (+ 1 (* 2 seq)) fn-cat$c)))
         (fn-cat$c (update-fn-cat$c-rowsi seq row fn-cat$c))
         (fn-cat$c (fn-cat$c-apply-plan plan seq fn-cat$c))
         (fn-cat$c (update-fn-cat$c-octets
                    (+ (fn-cat$c-octets fn-cat$c)
                       (nfix (fn-hf-octets (fn-held-facts h))))
                    fn-cat$c)))
    (update-fn-cat$c-count (+ 1 seq) fn-cat$c)))

(defun fn-cat$c-withdraw-base (target by fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard (and (fn-cat$c-wfp fn-cat$c) (natp target) (natp by)
                              (< target (fn-cat$c-count fn-cat$c)))))
  (let ((row (fn-cat$c-rowsi target fn-cat$c)))
    (if (null (fn-held-withdrawn row))
        (update-fn-cat$c-rowsi
         target (fn-held-with-withdrawn row (cons (fn-cat$c-count fn-cat$c) by))
         fn-cat$c)
      fn-cat$c)))

(defun fn-cat$c-redecide (seq context fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard (and (fn-cat$c-wfp fn-cat$c) (natp seq)
                              (< seq (fn-cat$c-count fn-cat$c)))))
  (update-fn-cat$c-rowsi
   seq (fn-held-with-context (fn-cat$c-rowsi seq fn-cat$c) context) fn-cat$c))

(defun fn-cat$c-clear-base (fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let* ((fn-cat$c (update-fn-cat$c-count 0 fn-cat$c))
         (fn-cat$c (update-fn-cat$c-octets 0 fn-cat$c))
         (fn-cat$c (fn-cat$c-index-clear fn-cat$c))
         (fn-cat$c (fn-cat$c-numbers-clear fn-cat$c)))
    (fn-cat$c-groups-clear fn-cat$c)))

;; -----------------------------------------------------------------------------
;; The live summary's cells (sca-join-5).  Readers: one probe each.

(defun fn-cat$c-group-live-count (group fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let ((e (fn-cat$c-lives-get group fn-cat$c)))
    (if (consp e) (nfix (car e)) 0)))

(defun fn-cat$c-group-live-low (group fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let ((e (fn-cat$c-lives-get group fn-cat$c)))
    (if (and (consp e) (consp (cdr e))) (nfix (car (cdr e))) 0)))

(defun fn-cat$c-group-live-high (group fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let ((e (fn-cat$c-lives-get group fn-cat$c)))
    (if (and (consp e) (consp (cdr e))) (nfix (cdr (cdr e))) 0)))

(defun fn-cat$c-horizon (fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (fn-cat$c-hz fn-cat$c))

;; Number K of GROUP is live in the tables: the number table's row, read.
(defun fn-cat$c-live-at-p (group k fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (fn-cat$c-wfp fn-cat$c)))
  (let ((s (fn-cat$c-numbers-get (cons group k) fn-cat$c)))
    (and (natp s) (< s (fn-cat$c-count fn-cat$c))
         (fn-cat-live-rowp group k (fn-cat$c-rowsi s fn-cat$c)))))

;; The scans a withdrawal of a group's low or high number runs: over
;; numbers, one probe each.  Their cost is amortized: a group's low only
;; rises (a commit's number is above every other), so the upward scans of a
;; group together cross each of its numbers once; the downward scan crosses
;; the withdrawn numbers at the group's top.
(defun fn-cat$c-scan-up (group k top fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (and (fn-cat$c-wfp fn-cat$c) (natp k) (natp top))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (if (fn-cat$c-live-at-p group k fn-cat$c)
          k
        (fn-cat$c-scan-up group (+ 1 k) top fn-cat$c))
    0))

(defun fn-cat$c-scan-down (group k fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (and (fn-cat$c-wfp fn-cat$c) (natp k))))
  (if (posp k)
      (if (fn-cat$c-live-at-p group k fn-cat$c)
          k
        (fn-cat$c-scan-down group (- k 1) fn-cat$c))
    0))

;; The commit's entries, read before any write: per group, the entry after
;; a row numbered N (the group's next) joins it, live or not.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cat$c-live-plan-loop (groups livep fn-cat$c acc)
  (declare (xargs :stobjs fn-cat$c :guard (true-listp acc) :verify-guards nil))
  (if (consp groups)
      (let* ((g (car groups))
             (ge (fn-cat$c-groups-get g fn-cat$c))
             (n (if (consp ge) (nfix (cdr ge)) 1))
             (count (fn-cat$c-group-live-count g fn-cat$c))
             (low (fn-cat$c-group-live-low g fn-cat$c))
             (high (fn-cat$c-group-live-high g fn-cat$c)))
        (fn-cat$c-live-plan-loop (cdr groups)
                                 livep
                                 fn-cat$c
                                 (cons (cons g
                                             (if (and livep
                                                      (posp n)
                                                      (<= n
                                                          *fn-nntp-max-article-number*))
                                                 (cons (+ 1 count)
                                                       (cons (if (equal low 0) n low) n))
                                               (cons count (cons low high))))
                                       acc)))
    (revappend acc nil)))

(defun fn-cat$c-live-plan (groups livep fn-cat$c)
  (declare (xargs :verify-guards nil :stobjs fn-cat$c))
  (mbe :logic
       (if (consp groups)
           (let* ((g (car groups))
                  (ge (fn-cat$c-groups-get g fn-cat$c))
                  (n (if (consp ge) (nfix (cdr ge)) 1))
                  (count (fn-cat$c-group-live-count g fn-cat$c))
                  (low (fn-cat$c-group-live-low g fn-cat$c))
                  (high (fn-cat$c-group-live-high g fn-cat$c)))
             (cons (cons g (if (and livep (posp n) (<= n *fn-nntp-max-article-number*))
                               (cons (+ 1 count) (cons (if (equal low 0) n low) n))
                             (cons count (cons low high))))
                   (fn-cat$c-live-plan (cdr groups) livep fn-cat$c)))
         nil)
       :exec (fn-cat$c-live-plan-loop groups livep fn-cat$c nil)))

(local
 (defthm fn-cat$c-live-plan-loop-is-revappend
   (equal (fn-cat$c-live-plan-loop groups livep fn-cat$c acc)
          (revappend acc (fn-cat$c-live-plan groups livep fn-cat$c)))
   :hints (("Goal" :induct (fn-cat$c-live-plan-loop groups livep fn-cat$c acc)
                   :in-theory (union-theories '(fn-cat$c-live-plan-loop fn-cat$c-live-plan revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cat$c-live-plan-loop)

(verify-guards fn-cat$c-live-plan
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cat$c-live-plan)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cat$c-live-plan-loop-is-revappend (acc nil))))))


(defun fn-cat$c-live-apply (plan fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (if (consp plan)
      (let ((fn-cat$c (fn-cat$c-lives-put (fn-cbor-ag-car (car plan))
                                          (fn-cbor-ag-cdr (car plan)) fn-cat$c)))
        (fn-cat$c-live-apply (cdr plan) fn-cat$c))
    fn-cat$c))

(defun fn-cat$c-commit (h fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (fn-cat$c-wfp fn-cat$c)))
  (let* ((lplan (fn-cat$c-live-plan (fn-record-groups h)
                                    (fn-cat-live-candidatep h)
                                    fn-cat$c))
         (w (fn-held-withdrawn h))
         (hz (max (fn-cat$c-hz fn-cat$c) (if (consp w) (+ 1 (nfix (car w))) 0)))
         (fn-cat$c (fn-cat$c-commit-base h fn-cat$c))
         (fn-cat$c (fn-cat$c-live-apply lplan fn-cat$c)))
    (update-fn-cat$c-hz hz fn-cat$c)))

;; A withdrawal's entry for GROUP, whose live number K stops being live.
(defun fn-cat$c-drop-entry (group k fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (and (fn-cat$c-wfp fn-cat$c) (posp k))))
  (let* ((ge (fn-cat$c-groups-get group fn-cat$c))
         (top (nfix (- (if (consp ge) (nfix (cdr ge)) 1) 1)))
         (count (fn-cat$c-group-live-count group fn-cat$c))
         (low (fn-cat$c-group-live-low group fn-cat$c))
         (high (fn-cat$c-group-live-high group fn-cat$c)))
    (cons (nfix (- count 1))
          (cons (if (equal low k) (fn-cat$c-scan-up group (+ 1 k) top fn-cat$c) low)
                (if (equal high k) (fn-cat$c-scan-down group (- k 1) fn-cat$c) high)))))

;; The withdrawal's entries, read before any write: for each binding
;; (g . k) of the row whose number the table answers with the row and which
;; is live; a repeated binding repeats the same entry.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cat$c-drop-plan-loop (pairs target row fn-cat$c acc)
  (declare (xargs :stobjs fn-cat$c :guard (and (fn-cat$c-wfp fn-cat$c) (true-listp acc)) :verify-guards nil))
  (if (consp pairs)
      (let* ((p (car pairs))
             (g (fn-cbor-ag-car p))
             (k (fn-cbor-ag-cdr p)))
        (if (and (consp p)
                 (equal (fn-cat$c-numbers-get (cons g k) fn-cat$c) target)
                 (fn-cat-live-rowp g k row))
            (fn-cat$c-drop-plan-loop (cdr pairs)
                                     target
                                     row
                                     fn-cat$c
                                     (cons (cons g (fn-cat$c-drop-entry g k fn-cat$c))
                                           acc))
          (fn-cat$c-drop-plan-loop (cdr pairs) target row fn-cat$c acc)))
    (revappend acc nil)))

(defun fn-cat$c-drop-plan (pairs target row fn-cat$c)
  (declare (xargs :verify-guards nil :stobjs fn-cat$c :guard (fn-cat$c-wfp fn-cat$c)))
  (mbe :logic
       (if (consp pairs)
           (let* ((p (car pairs))
                  (g (fn-cbor-ag-car p))
                  (k (fn-cbor-ag-cdr p)))
             (if (and (consp p)
                      (equal (fn-cat$c-numbers-get (cons g k) fn-cat$c) target)
                      (fn-cat-live-rowp g k row))
                 (cons (cons g (fn-cat$c-drop-entry g k fn-cat$c))
                       (fn-cat$c-drop-plan (cdr pairs) target row fn-cat$c))
               (fn-cat$c-drop-plan (cdr pairs) target row fn-cat$c)))
         nil)
       :exec (fn-cat$c-drop-plan-loop pairs target row fn-cat$c nil)))

(local
 (defthm fn-cat$c-drop-plan-loop-is-revappend
   (equal (fn-cat$c-drop-plan-loop pairs target row fn-cat$c acc)
          (revappend acc (fn-cat$c-drop-plan pairs target row fn-cat$c)))
   :hints (("Goal" :induct (fn-cat$c-drop-plan-loop pairs target row fn-cat$c acc)
                   :in-theory (union-theories '(fn-cat$c-drop-plan-loop fn-cat$c-drop-plan revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cat$c-drop-plan-loop)

(verify-guards fn-cat$c-drop-plan
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cat$c-drop-plan)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cat$c-drop-plan-loop-is-revappend (acc nil))))))


(defun fn-cat$c-withdraw (target by fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard (and (fn-cat$c-wfp fn-cat$c) (natp target) (natp by)
                              (< target (fn-cat$c-count fn-cat$c)))))
  (let ((row (fn-cat$c-rowsi target fn-cat$c)))
    (if (null (fn-held-withdrawn row))
        (let* ((dplan (fn-cat$c-drop-plan (fn-held-numbers row) target row fn-cat$c))
               (hz (max (fn-cat$c-hz fn-cat$c) (+ 1 (fn-cat$c-count fn-cat$c))))
               (fn-cat$c (fn-cat$c-withdraw-base target by fn-cat$c))
               (fn-cat$c (fn-cat$c-live-apply dplan fn-cat$c)))
          (update-fn-cat$c-hz hz fn-cat$c))
      fn-cat$c)))

;; The rows array is resized to nothing: a cleared catalog keeps no
;; reference to a row it held (PKT-733 (3)); the next append grows it.
(defun fn-cat$c-clear (fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let* ((fn-cat$c (fn-cat$c-clear-base fn-cat$c))
         (fn-cat$c (fn-cat$c-lives-clear fn-cat$c))
         (fn-cat$c (resize-fn-cat$c-rows 0 fn-cat$c)))
    (update-fn-cat$c-hz 0 fn-cat$c)))

; -----------------------------------------------------------------------------
; The abstraction relation.

; Rows 0 .. n-1 of the array (its logical list) are the first n elements of C.
(defun fn-cat-rows-corr (n c rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp n)
      t
    (and (< (- n 1) (len rows))
         (equal (nth (- n 1) rows) (nth (- n 1) c))
         (fn-cat-rows-corr (- n 1) c rows))))

; THE TABLE IS THE FOLD (books/msgid-linear-exec section 8): the nested
; table is `fn-mlh-build' of the rows under its own key and the unplaced
; cell the fold's count.  Equality, not a
; weaker relation: the served refusal's logic function is a function of the
; rows alone only because the table is determined by them.
(defun-nx fn-cat-key-of (fn-cat$c)
  (fn-mlh-key-octets (nth *fn-cat$c-mpx* fn-cat$c)))

; A bound (group . number) names a row, and the row it looks up to.
(defun fn-cat-numbers-okp (keys tab c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp keys)
      (and (fn-cat-number-seq (car (car (car keys))) (cdr (car (car keys))) c 0)
           (equal (cdr (hons-assoc-equal (car (car keys)) tab))
                  (fn-cat-number-seq (car (car (car keys))) (cdr (car (car keys))) c 0))
           (fn-cat-numbers-okp (cdr keys) tab c))
    t))

; Every (group . number) of a row's numbers is bound in TAB.
(defun fn-cat-numbers-cover-rowp (numbers tab)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (and (consp (hons-assoc-equal (car numbers) tab))
           (fn-cat-numbers-cover-rowp (cdr numbers) tab))
    t))

(defun fn-cat-numbers-coverp (c tab)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp c)
      (and (fn-cat-numbers-cover-rowp (fn-held-numbers (car c)) tab)
           (fn-cat-numbers-coverp (cdr c) tab))
    t))

(defun fn-cat-groups-okp (keys tab c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp keys)
      (and (equal (cdr (hons-assoc-equal (car (car keys)) tab))
                  (cons (fn-cat-group-rows (car (car keys)) c)
                        (+ 1 (fn-cat-group-high (car (car keys)) c))))
           (fn-cat-groups-okp (cdr keys) tab c))
    t))

; Every group of a row's numbers is bound in TAB.
(defun fn-cat-groups-cover-rowp (numbers tab)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (and (consp (hons-assoc-equal (car (car numbers)) tab))
           (fn-cat-groups-cover-rowp (cdr numbers) tab))
    t))

(defun fn-cat-groups-coverp (c tab)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp c)
      (and (fn-cat-groups-cover-rowp (fn-held-numbers (car c)) tab)
           (fn-cat-groups-coverp (cdr c) tab))
    t))

; The concrete object is well formed; the count is the length; the rows
; below the count are C; each table's bound keys look up to their columns
; and every row's keys are bound; the octets cell is the sum.  Stated over
; the stobj's logical fields (defun-nx: nothing executes it).
(defun-nx fn-cat$corr-base (fn-cat$c fn-cat$a)
  (and (fn-cat$cp fn-cat$c)
       (fn-cat-rowsp fn-cat$a)
       (equal (nth 1 fn-cat$c) (len fn-cat$a))
       (<= (nth 1 fn-cat$c) (len (nth 0 fn-cat$c)))
       (fn-cat-rows-corr (len fn-cat$a) fn-cat$a (nth 0 fn-cat$c))
       (equal (nth *fn-cat$c-mpx* fn-cat$c) (fn-mlh-build (fn-cat-key-of fn-cat$c) fn-cat$a))
       (equal (nth *fn-cat$c-unplaced* fn-cat$c) (fn-mlh-build-unplaced (fn-cat-key-of fn-cat$c) fn-cat$a))
       (fn-cat-numbers-okp (nth 3 fn-cat$c) (nth 3 fn-cat$c) fn-cat$a)
       (fn-cat-numbers-coverp fn-cat$a (nth 3 fn-cat$c))
       (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) fn-cat$a)
       (fn-cat-groups-coverp fn-cat$a (nth 4 fn-cat$c))
       (equal (nth 5 fn-cat$c) (fn-cat-octets-of fn-cat$a))))

; The live summary of a group as the logical side states it, and the live
; table's conjunct: every bound group's entry is its summary; every row's
; groups are bound (so an unbound group has no rows and the summary 0 0 0);
; the horizon cell is the rows' horizon.
(defun fn-cat-live-entry (g c)
  (declare (xargs :guard t :verify-guards nil))
  (cons (fn-cat-live-count-from g 1 (fn-cat-group-high g c) c)
        (cons (fn-cat-live-first g 1 (fn-cat-group-high g c) c)
              (fn-cat-live-last g (fn-cat-group-high g c) c))))

(defun fn-cat-live-okp (keys tab c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp keys)
      (and (equal (cdr (hons-assoc-equal (car (car keys)) tab))
                  (fn-cat-live-entry (car (car keys)) c))
           (fn-cat-live-okp (cdr keys) tab c))
    t))

(defun-nx fn-cat$corr-live (fn-cat$c fn-cat$a)
  (and (fn-cat-live-okp (nth 6 fn-cat$c) (nth 6 fn-cat$c) fn-cat$a)
       (fn-cat-groups-coverp fn-cat$a (nth 6 fn-cat$c))
       (equal (nth 7 fn-cat$c) (fn-cat-horizon-of fn-cat$a))))

(defun-nx fn-cat$corr (fn-cat$c fn-cat$a)
  (and (fn-cat$corr-base fn-cat$c fn-cat$a)
       (fn-cat$corr-live fn-cat$c fn-cat$a)))

; -----------------------------------------------------------------------------
; The columns over an appended row, and over a row replaced with its keys
; kept (Message-ID, numbers, facts).

(local
 (defthm fn-ctg-seqs-for-append
   (implies (natp i)
            (equal (fn-cat-seqs-for m (append c (list h)) i)
                   (if (equal m (fn-record-msgid h))
                       (append (fn-cat-seqs-for m c i) (list (+ i (len c))))
                     (fn-cat-seqs-for m c i))))))

(local
 (defthm fn-ctg-number-seq-append
   (implies (natp i)
            (equal (fn-cat-number-seq g n (append c (list h)) i)
                   (if (fn-cat-number-seq g n c i)
                       (fn-cat-number-seq g n c i)
                     (if (and (fn-held-number-in g h) (equal n (fn-held-number-in g h)))
                         (+ i (len c))
                       nil))))))

(local
 (defthm fn-ctg-high-append
   (equal (fn-cat-group-high g (append c (list h)))
          (max (fn-cat-group-high g c) (nfix (fn-held-number-in g h))))))

(local
 (defthm fn-ctg-rows-append
   (equal (fn-cat-group-rows g (append c (list h)))
          (+ (fn-cat-group-rows g c) (if (fn-held-number-in g h) 1 0)))))

(local
 (defthm fn-ctg-octets-append
   (equal (fn-cat-octets-of (append c (list h)))
          (+ (fn-cat-octets-of c) (nfix (fn-hf-octets (fn-held-facts h)))))))

; A held row's number in a group is nil or a positive integer.
(local
 (defthm fn-ctg-assoc-of-numbersp
   (implies (fn-held-numbersp ns)
            (or (null (cdr (fn-cat-assoc g ns)))
                (posp (cdr (fn-cat-assoc g ns)))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-held-numbersp)))))

(local
 (defthm fn-ctg-number-in-type
   (implies (fn-held-p h)
            (or (null (fn-held-number-in g h))
                (posp (fn-held-number-in g h))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-held-number-in)
                   :use ((:instance fn-ctg-assoc-of-numbersp (ns (fn-held-numbers h))))))))

; The same fact as a rewrite: a present number is a positive integer.
(local
 (defthm fn-ctg-assoc-of-numbersp-rewrite
   (implies (and (fn-held-numbersp ns) (cdr (fn-cat-assoc g ns)))
            (and (integerp (cdr (fn-cat-assoc g ns)))
                 (< 0 (cdr (fn-cat-assoc g ns)))))
   :hints (("Goal" :use fn-ctg-assoc-of-numbersp))))

; A number above the group's high names no row.
(local
 (defthm fn-ctg-number-seq-above-high
   (implies (and (fn-cat-rowsp c) (rationalp n) (< (fn-cat-group-high g c) n))
            (equal (fn-cat-number-seq g n c i) nil))))

; A bound number is at most the high.
(local
 (defthm fn-ctg-number-seq-below-high
   (implies (and (fn-cat-rowsp c) (fn-cat-number-seq g n c i) (rationalp n))
            (<= n (fn-cat-group-high g c)))
   :rule-classes :linear))

; The keys of a row replaced with its keys kept.
(defun fn-cat-same-keysp (h1 h2)
  (declare (xargs :guard t))
  (and (equal (fn-record-msgid h1) (fn-record-msgid h2))
       (equal (fn-held-numbers h1) (fn-held-numbers h2))
       (equal (fn-held-facts h1) (fn-held-facts h2))))

(local
 (defthm fn-ctg-seqs-for-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-seqs-for m (update-nth k h c) i)
                   (fn-cat-seqs-for m c i)))))

(local
 (defthm fn-ctg-number-in-same-keys
   (implies (fn-cat-same-keysp h1 h2)
            (equal (fn-held-number-in g h1) (fn-held-number-in g h2)))
   :rule-classes nil))

(local
 (defthm fn-ctg-number-seq-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-number-seq g n (update-nth k h c) i)
                   (fn-cat-number-seq g n c i)))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-ctg-high-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-group-high g (update-nth k h c))
                   (fn-cat-group-high g c)))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-ctg-rows-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-group-rows g (update-nth k h c))
                   (fn-cat-group-rows g c)))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-ctg-octets-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-octets-of (update-nth k h c))
                   (fn-cat-octets-of c)))))

(local
 (defthm fn-ctg-with-withdrawn-same-keys
   (fn-cat-same-keysp (fn-held-with-withdrawn h w) h)))

(local
 (defthm fn-ctg-with-context-same-keys
   (fn-cat-same-keysp (fn-held-with-context h ctx) h)))

(local
 (defthm fn-ctg-assign-fields
   (and (equal (fn-record-msgid (fn-cat-assign h c)) (fn-record-msgid h))
        (equal (fn-held-numbers (fn-cat-assign h c))
               (fn-cat-assign-numbers (fn-record-groups h) c))
        (equal (fn-held-facts (fn-cat-assign h c)) (fn-held-facts h)))))

(local
 (defthm fn-ctg-assoc-of-assign-numbers
   (equal (fn-cat-assoc g (fn-cat-assign-numbers groups c))
          (if (member-equal g groups)
              (cons g (+ 1 (fn-cat-group-high g c)))
            nil))))

(local
 (defthm fn-ctg-number-in-of-assign
   (equal (fn-held-number-in g (fn-cat-assign h c))
          (if (member-equal g (fn-record-groups h))
              (+ 1 (fn-cat-group-high g c))
            nil))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

; -----------------------------------------------------------------------------
; The live summary over the list: the committed row and a withdrawal.

(local
 (defthm fn-ctg-availability-of-assign
   (equal (fn-cat-row-availablep (fn-cat-assign h c))
          (fn-cat-row-availablep h))
   :hints (("Goal" :in-theory (e/d (fn-cat-assign) (fn-held-with-numbers))))))

(local
 (defthm fn-ctg-withdrawn-of-assign
   (equal (fn-held-withdrawn (fn-cat-assign h c)) (fn-held-withdrawn h))
   :hints (("Goal" :in-theory (enable fn-cat-assign fn-held-with-numbers)))))

(local
 (defthm fn-ctg-nth-append-one-below
   (implies (and (natp i) (< i (len c)))
            (equal (nth i (append c (list h))) (nth i c)))))

(local
 (defthm fn-ctg-nth-append-one-at
   (implies (equal i (len c))
            (equal (nth i (append c (list h))) h))))

(local
 (defthm fn-ctg-len-append-one (equal (len (append c (list h))) (+ 1 (len c)))))

(local
 (defthm fn-ctg-number-seq-natp
   (implies (natp i)
            (or (equal (fn-cat-number-seq g n c i) nil)
                (natp (fn-cat-number-seq g n c i))))
   :rule-classes :type-prescription))

(local
 (defthm fn-ctg-number-seq-bounds
   (implies (and (natp i) (fn-cat-number-seq g n c i))
            (and (<= i (fn-cat-number-seq g n c i))
                 (< (fn-cat-number-seq g n c i) (+ i (len c)))))
   :rule-classes :linear))

(local
 (defthm fn-ctg-number-seq-names-number
   (implies (and (natp i) (fn-cat-number-seq g n c i))
            (equal (fn-held-number-in g (nth (- (fn-cat-number-seq g n c i) i) c)) n))
   :hints (("Goal" :induct (fn-cat-number-seq g n c i)))))

(local
 (defthm fn-ctg-number-seq-names-number-0
   (implies (fn-cat-number-seq g n c 0)
            (equal (fn-held-number-in g (nth (fn-cat-number-seq g n c 0) c)) n))
   :hints (("Goal" :use ((:instance fn-ctg-number-seq-names-number (i 0)))))))

(local
 (defthm fn-ctg-live-append-other
   (implies (and (fn-cat-rowsp c)
                 (not (and (member-equal g (fn-record-groups h))
                           (equal k (+ 1 (fn-cat-group-high g c))))))
            (equal (fn-cat-live-numberp g k (append c (list (fn-cat-assign h c))))
                   (fn-cat-live-numberp g k c)))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-numberp)
                                   (fn-cat-assign fn-cat-live-rowp fn-cat-rowsp fn-held-number-in
                                    nth fn-cat-number-seq len))))))

(local
 (defthm fn-ctg-live-append-new
   (implies (and (fn-cat-rowsp c) (member-equal g (fn-record-groups h))
                 (equal n (+ 1 (fn-cat-group-high g c))))
            (equal (fn-cat-live-numberp g n (append c (list (fn-cat-assign h c))))
                   (and (fn-cat-live-candidatep h)
                        (<= n *fn-nntp-max-article-number*))))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-numberp fn-cat-live-rowp)
                                   (fn-cat-assign fn-cat-rowsp fn-held-number-in fn-scat-msgid-idp
                                    nth fn-cat-number-seq len fn-cat-group-high))))))

(local
 (defthm fn-ctg-live-count-append
   (implies (and (fn-cat-rowsp c)
                 (or (not (member-equal g (fn-record-groups h)))
                     (<= top (fn-cat-group-high g c))))
            (equal (fn-cat-live-count-from g k top (append c (list (fn-cat-assign h c))))
                   (fn-cat-live-count-from g k top c)))
   :hints (("Goal" :induct (fn-cat-live-count-from g k top c)
            :in-theory (disable fn-cat-assign fn-cat-live-numberp)))))

(local
 (defthm fn-ctg-live-first-append
   (implies (and (fn-cat-rowsp c)
                 (or (not (member-equal g (fn-record-groups h)))
                     (<= top (fn-cat-group-high g c))))
            (equal (fn-cat-live-first g k top (append c (list (fn-cat-assign h c))))
                   (fn-cat-live-first g k top c)))
   :hints (("Goal" :induct (fn-cat-live-first g k top c)
            :in-theory (disable fn-cat-assign fn-cat-live-numberp)))))

(local
 (defthm fn-ctg-live-last-append
   (implies (and (fn-cat-rowsp c)
                 (or (not (member-equal g (fn-record-groups h)))
                     (<= k (fn-cat-group-high g c))))
            (equal (fn-cat-live-last g k (append c (list (fn-cat-assign h c))))
                   (fn-cat-live-last g k c)))
   :hints (("Goal" :induct (fn-cat-live-last g k c)
            :in-theory (disable fn-cat-assign fn-cat-live-numberp)))))

; One more number at the top of the range.
(local
 (defthm fn-ctg-live-empty-range
   (implies (< top k)
            (and (equal (fn-cat-live-count-from g k top c) 0)
                 (equal (fn-cat-live-first g k top c) 0)))))

(local
 (defthm fn-ctg-live-numberp-posp
   (implies (fn-cat-live-numberp g k c) (posp k))
   :rule-classes :forward-chaining))

(local
 (defthm fn-ctg-live-numberp-0
   (not (fn-cat-live-numberp g 0 c))))

(local
 (defthm fn-ctg-live-count-top
   (implies (and (natp k) (natp top) (<= k (+ 1 top)))
            (equal (fn-cat-live-count-from g k (+ 1 top) c)
                   (+ (fn-cat-live-count-from g k top c)
                      (if (fn-cat-live-numberp g (+ 1 top) c) 1 0))))
   :hints (("Goal" :induct (fn-cat-live-count-from g k top c)
            :in-theory (disable fn-cat-live-numberp)))))

(local
 (defthm fn-ctg-live-first-top
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
 (defthm fn-ctg-live-first-bounds
   (implies (and (natp k) (not (equal (fn-cat-live-first g k top c) 0)))
            (and (<= k (fn-cat-live-first g k top c))
                 (<= (fn-cat-live-first g k top c) top)
                 (fn-cat-live-numberp g (fn-cat-live-first g k top c) c)))
   :hints (("Goal" :induct (fn-cat-live-first g k top c)
            :in-theory (disable fn-cat-live-numberp)))))

(local
 (defthm fn-ctg-live-last-bounds
   (implies (not (equal (fn-cat-live-last g k c) 0))
            (and (<= (fn-cat-live-last g k c) k)
                 (fn-cat-live-numberp g (fn-cat-live-last g k c) c)))
   :hints (("Goal" :induct (fn-cat-live-last g k c)
            :in-theory (disable fn-cat-live-numberp)))))

(local
 (defthm fn-ctg-live-types
   (and (natp (fn-cat-live-count-from g k top c))
        (natp (fn-cat-live-first g k top c))
        (natp (fn-cat-live-last g k c)))
   :rule-classes (:rewrite
                  (:type-prescription :corollary (natp (fn-cat-live-count-from g k top c)))
                  (:type-prescription :corollary (natp (fn-cat-live-first g k top c)))
                  (:type-prescription :corollary (natp (fn-cat-live-last g k c))))))

; A withdrawal: the one number of each group the withdrawn row is the
; column's answer for stops being live.
(defun fn-ctg-kstar (g c r)
  (declare (xargs :guard t :verify-guards nil))
  (let ((k (fn-held-number-in g (nth r c))))
    (if (and (posp k) (equal (fn-cat-number-seq g k c 0) r)) k 0)))

(local
 (defthm fn-ctg-live-rowp-of-withdrawn
   (not (fn-cat-live-rowp g k (fn-held-with-withdrawn h (cons v by))))
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn)))))

(local
 (defthm fn-ctg-mark-withdrawn-is-update
   (implies (and (< r (len c)) (null (fn-held-withdrawn (nth r c))))
            (equal (fn-cat-mark-withdrawn r v by c)
                   (update-nth r (fn-held-with-withdrawn (nth r c) (cons v by)) c)))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

(local
 (defthm fn-ctg-number-seq-withdrawn
   (implies (and (natp r) (< r (len c)))
            (equal (fn-cat-number-seq g n (update-nth r (fn-held-with-withdrawn (nth r c) w) c) i)
                   (fn-cat-number-seq g n c i)))
   :hints (("Goal" :in-theory (disable fn-cat-number-seq fn-held-with-withdrawn)
            :use ((:instance fn-ctg-number-seq-update-nth
                             (k r) (h (fn-held-with-withdrawn (nth r c) w))))))))

(local
 (defthm fn-ctg-live-rowp-number
   (implies (fn-cat-live-rowp g k h)
            (and (posp k) (equal (fn-held-number-in g h) k)))
   :rule-classes :forward-chaining))

(local
 (defthm fn-ctg-live-withdrawn
   (implies (and (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c))))
            (equal (fn-cat-live-numberp g j (fn-cat-mark-withdrawn r v by c))
                   (and (fn-cat-live-numberp g j c)
                        (not (equal j (fn-ctg-kstar g c r))))))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-numberp fn-ctg-kstar)
                                   (fn-held-with-withdrawn fn-cat-live-rowp fn-cat-number-seq
                                    fn-held-number-in fn-cat-mark-withdrawn nth update-nth))
            :cases ((equal (fn-cat-number-seq g j c 0) r))))))

(local
 (defthm fn-ctg-high-withdrawn
   (equal (fn-cat-group-high g (fn-cat-mark-withdrawn r v by c))
          (fn-cat-group-high g c))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

(local
 (defthm fn-ctg-live-count-withdrawn
   (implies (and (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c))) (natp top))
            (equal (fn-cat-live-count-from g j top (fn-cat-mark-withdrawn r v by c))
                   (- (fn-cat-live-count-from g j top c)
                      (if (and (natp j) (<= j (fn-ctg-kstar g c r))
                               (<= (fn-ctg-kstar g c r) top)
                               (fn-cat-live-numberp g (fn-ctg-kstar g c r) c))
                          1 0))))
   :hints (("Goal" :induct (fn-cat-live-count-from g j top c)
            :in-theory (disable fn-cat-live-numberp fn-ctg-kstar fn-cat-mark-withdrawn fn-ctg-mark-withdrawn-is-update)))))

(local
 (defthm fn-ctg-live-first-withdrawn
   (implies (and (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c))) (natp j) (natp top))
            (equal (fn-cat-live-first g j top (fn-cat-mark-withdrawn r v by c))
                   (if (and (not (equal (fn-ctg-kstar g c r) 0))
                            (equal (fn-cat-live-first g j top c) (fn-ctg-kstar g c r)))
                       (fn-cat-live-first g (+ 1 (fn-ctg-kstar g c r)) top c)
                     (fn-cat-live-first g j top c))))
   :hints (("Goal" :induct (fn-cat-live-count-from g j top c)
            :expand ((fn-cat-live-first g j top (fn-cat-mark-withdrawn r v by c))
                     (fn-cat-live-first g j top c))
            :in-theory (disable fn-cat-live-numberp fn-ctg-kstar fn-cat-mark-withdrawn fn-ctg-mark-withdrawn-is-update)))))

(local
 (defun fn-ctg-down-ind (j)
   (declare (xargs :guard t))
   (if (posp j) (fn-ctg-down-ind (- j 1)) t)))

(local
 (defthm fn-ctg-live-last-withdrawn
   (implies (and (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c))))
            (equal (fn-cat-live-last g j (fn-cat-mark-withdrawn r v by c))
                   (if (and (not (equal (fn-ctg-kstar g c r) 0))
                            (equal (fn-cat-live-last g j c) (fn-ctg-kstar g c r)))
                       (fn-cat-live-last g (- (fn-ctg-kstar g c r) 1) c)
                     (fn-cat-live-last g j c))))
   :hints (("Goal" :induct (fn-ctg-down-ind j)
            :expand ((fn-cat-live-last g j (fn-cat-mark-withdrawn r v by c))
                     (fn-cat-live-last g j c))
            :in-theory (disable fn-cat-live-numberp fn-ctg-kstar fn-cat-mark-withdrawn fn-ctg-mark-withdrawn-is-update)))))

; The horizon.
(local
 (defthm fn-ctg-horizon-append
   (equal (fn-cat-horizon-of (append c (list x)))
          (max (fn-cat-horizon-of c)
               (let ((w (fn-held-withdrawn x))) (if (consp w) (+ 1 (nfix (car w))) 0))))))

(local
 (defthm fn-ctg-horizon-update-nth
   (implies (and (natp r) (< r (len c)) (not (consp (fn-held-withdrawn (nth r c)))))
            (equal (fn-cat-horizon-of (update-nth r x c))
                   (max (fn-cat-horizon-of c)
                        (let ((w (fn-held-withdrawn x))) (if (consp w) (+ 1 (nfix (car w))) 0)))))
   :hints (("Goal" :induct (update-nth r x c) :in-theory (enable update-nth)))))

; -----------------------------------------------------------------------------
; The tables after the commit's writes.  A put conses the pair in front
; (the hash-table field's logical model), so a lookup finds the newest.

(local
 (defthm fn-ctg-snoc-is-append
   (implies (true-listp xs)
            (equal (fn-cat-snoc xs x) (append xs (list x))))))

(local
 (defthm fn-ctg-seqs-for-true-listp
   (true-listp (fn-cat-seqs-for m c i))))

; An unbound group binds no number in a covered row; an unbound
; (group . number) is not a covered row's binding.
(local
 (defthm fn-ctg-assoc-groups-unbound
   (implies (and (fn-cat-groups-cover-rowp ns tab)
                 (not (consp (hons-assoc-equal g tab))))
            (equal (fn-cat-assoc g ns) nil))))

(local
 (defthm fn-ctg-assoc-numbers-bound
   (implies (and (fn-cat-numbers-cover-rowp ns tab)
                 (consp (fn-cat-assoc g ns)))
            (consp (hons-assoc-equal (cons g (cdr (fn-cat-assoc g ns))) tab)))))

(local
 (defthm fn-ctg-numbers-unbound
   (implies (and (fn-cat-numbers-coverp c tab)
                 (not (consp (hons-assoc-equal (cons g n) tab))))
            (equal (fn-cat-number-seq g n c i) nil))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

; The numbers and groups tables after the plan.
(local
 (defthm fn-ctg-groups-unbound
   (implies (and (fn-cat-groups-coverp c tab)
                 (not (consp (hons-assoc-equal g tab))))
            (and (equal (fn-cat-group-high g c) 0)
                 (equal (fn-cat-group-rows g c) 0)))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-ctg-groups-okp-bound
   (implies (and (fn-cat-groups-okp keys tab c) (consp (hons-assoc-equal g keys)))
            (equal (cdr (hons-assoc-equal g tab))
                   (cons (fn-cat-group-rows g c) (+ 1 (fn-cat-group-high g c)))))))

(local
 (defthm fn-ctg-numbers-okp-bound
   (implies (and (fn-cat-numbers-okp keys tab c) (consp (hons-assoc-equal k keys)))
            (and (fn-cat-number-seq (car k) (cdr k) c 0)
                 (equal (cdr (hons-assoc-equal k tab))
                        (fn-cat-number-seq (car k) (cdr k) c 0))))))

; What the exec reads for a group: (rows . 1+high), from the table or by
; default when unbound.
(local
 (defthm fn-ctg-groups-lookup
   (implies (and (fn-cat-groups-okp tab tab c) (fn-cat-groups-coverp c tab))
            (and (equal (let ((e (cdr (hons-assoc-equal g tab)))) (if (consp e) (nfix (cdr e)) 1))
                        (+ 1 (fn-cat-group-high g c)))
                 (equal (let ((e (cdr (hons-assoc-equal g tab)))) (if (consp e) (nfix (car e)) 0))
                        (fn-cat-group-rows g c))))
   :hints (("Goal" :do-not-induct t
            :cases ((consp (hons-assoc-equal g tab)))))))

(local
 (defthm fn-ctg-numbers-lookup
   (implies (and (fn-cat-numbers-okp tab tab c) (fn-cat-numbers-coverp c tab))
            (equal (cdr (hons-assoc-equal (cons g n) tab)) (fn-cat-number-seq g n c 0)))
   :hints (("Goal" :do-not-induct t
            :cases ((consp (hons-assoc-equal (cons g n) tab)))))))
; -----------------------------------------------------------------------------
; The rows array against the list.

(local
 (defthm fn-ctg-rows-corr-nth
   (implies (and (fn-cat-rows-corr n c rows) (natp i) (< i (nfix n)))
            (equal (nth i rows) (nth i c)))
   :hints (("Goal" :induct (fn-cat-rows-corr n c rows)))))

(local
 (defthm fn-ctg-nth-of-resize-list
   (implies (and (natp i) (< i (len l)) (< i (nfix n)))
            (equal (nth i (resize-list l n d)) (nth i l)))
   :hints (("Goal" :in-theory (enable resize-list)))))

(local
 (defthm fn-ctg-rows-corr-of-resize
   (implies (and (fn-cat-rows-corr n c rows) (<= (nfix n) (nfix m)))
            (fn-cat-rows-corr n c (resize-list rows m d)))
   :hints (("Goal" :induct (fn-cat-rows-corr n c rows)))))

(local
 (defthm fn-ctg-rows-corr-of-update-above
   (implies (and (fn-cat-rows-corr n c rows) (natp k) (<= (nfix n) k)
                 (< k (len rows)))
            (fn-cat-rows-corr n c (update-nth k v rows)))
   :hints (("Goal" :induct (fn-cat-rows-corr n c rows)))))

(defthm fn-ctg-nth-of-append-below
   (implies (and (natp i) (< i (len c)))
            (equal (nth i (append c (list h))) (nth i c))))

(defthm fn-ctg-nth-of-append-at
   (implies (equal i (len c))
            (equal (nth i (append c (list h))) h)))

(local
 (defthm fn-ctg-rows-corr-of-append-and-update-above
   (implies (and (fn-cat-rows-corr n c rows) (natp k) (<= (nfix n) k)
                 (<= (nfix n) (len c)) (< k (len rows)))
            (fn-cat-rows-corr n (append c (list h)) (update-nth k v rows)))
   :hints (("Goal" :induct (fn-cat-rows-corr n c rows)))))

(local
 (defthm fn-ctg-rows-corr-extend
   (implies (and (fn-cat-rows-corr n c rows) (natp n) (equal n (len c))
                 (< n (len rows)))
            (fn-cat-rows-corr (+ 1 n) (append c (list h)) (update-nth n h rows)))
   :hints (("Goal" :expand ((fn-cat-rows-corr (+ 1 n) (append c (list h))
                                              (update-nth n h rows)))
            :do-not-induct t))))

(local
 (defthm fn-ctg-rows-corr-of-update-above-both
   (implies (and (fn-cat-rows-corr n c rows) (natp k) (<= (nfix n) k) (< k (len rows)))
            (fn-cat-rows-corr n (update-nth k v c) (update-nth k v rows)))
   :hints (("Goal" :induct (fn-cat-rows-corr n c rows)))))

(local
 (defthm fn-ctg-rows-corr-of-update-both
   (implies (and (fn-cat-rows-corr n c rows) (natp k) (< k (nfix n)) (< k (len rows)))
            (fn-cat-rows-corr n (update-nth k v c) (update-nth k v rows)))
   :hints (("Goal" :induct (fn-cat-rows-corr n c rows)))))

; -----------------------------------------------------------------------------
; The plan's writes as two put-folds, and their lookups.

(defun fn-cat-nputs (plan seq tab)
  (declare (xargs :guard t))
  (if (consp plan)
      (fn-cat-nputs (cdr plan) seq
                    (cons (cons (cons (fn-cbor-ag-car (car plan))
                                      (fn-cbor-ag-car (fn-cbor-ag-cdr (car plan))))
                                seq)
                          tab))
    tab))

(defun fn-cat-gputs (plan tab)
  (declare (xargs :guard t))
  (if (consp plan)
      (fn-cat-gputs (cdr plan)
                    (cons (cons (fn-cbor-ag-car (car plan))
                                (cons (+ 1 (nfix (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr (car plan))))))
                                      (+ 1 (nfix (fn-cbor-ag-car (fn-cbor-ag-cdr (car plan)))))))
                          tab))
    tab))

(local
 (defthm fn-ctg-apply-plan-fields
   (and (equal (nth 0 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 0 fn-cat$c))
        (equal (nth 1 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 1 fn-cat$c))
        (equal (nth 2 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 2 fn-cat$c))
        (equal (nth 3 (fn-cat$c-apply-plan plan seq fn-cat$c))
               (fn-cat-nputs plan seq (nth 3 fn-cat$c)))
        (equal (nth 4 (fn-cat$c-apply-plan plan seq fn-cat$c))
               (fn-cat-gputs plan (nth 4 fn-cat$c)))
        (equal (nth 5 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 5 fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-apply-plan fn-cat$c-numbers-put
                                      fn-cat$c-groups-put)))))

(local
 (defthm fn-ctg-nputs-lookup
   (equal (hons-assoc-equal k (fn-cat-nputs plan seq tab))
          (if (member-equal k (fn-cat-plan-numbers plan))
              (cons k seq)
            (hons-assoc-equal k tab)))))

; The group entry as the case split leaves it: a cons is the columns; a
; non-cons means the group is unbound, with no rows and high 0.
(local
 (defthm fn-ctg-groups-entry-bound
   (implies (and (fn-cat-groups-okp tab tab c)
                 (consp (cdr (hons-assoc-equal g tab))))
            (equal (cdr (hons-assoc-equal g tab))
                   (cons (fn-cat-group-rows g c) (+ 1 (fn-cat-group-high g c)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ctg-groups-okp-bound (keys tab)))))))

(local
 (defthm fn-ctg-groups-entry-unbound
   (implies (and (fn-cat-groups-okp tab tab c) (fn-cat-groups-coverp c tab)
                 (not (consp (cdr (hons-assoc-equal g tab)))))
            (and (equal (fn-cat-group-high g c) 0)
                 (equal (fn-cat-group-rows g c) 0)))
   :hints (("Goal" :do-not-induct t
            :cases ((consp (hons-assoc-equal g tab)))
            :use ((:instance fn-ctg-groups-okp-bound (keys tab)))))))

; The plan read from a state: its numbers are the assignment, its group
; entries the columns.
(local
 (defthm fn-ctg-plan-numbers-is-assign
   (implies (and (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c)))
            (equal (fn-cat-plan-numbers (fn-cat$c-plan groups fn-cat$c))
                   (fn-cat-assign-numbers groups c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-plan fn-cat$c-groups-get)))))

; The groups walked with the table extended at each step.
(local
 (defun fn-ctg-gputs-ind (groups tab fn-cat$c)
   (declare (xargs :stobjs fn-cat$c :verify-guards nil))
   (if (consp groups)
       (let ((e (fn-cat$c-groups-get (car groups) fn-cat$c)))
         (fn-ctg-gputs-ind (cdr groups)
                           (cons (cons (car groups)
                                       (cons (+ 1 (if (consp e) (nfix (car e)) 0))
                                             (+ 1 (if (consp e) (nfix (cdr e)) 1))))
                                 tab)
                           fn-cat$c))
     (list tab))))

(local
 (defthm fn-ctg-gputs-lookup
   (implies (and (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c)))
            (equal (hons-assoc-equal g (fn-cat-gputs (fn-cat$c-plan groups fn-cat$c) tab))
                   (if (member-equal g groups)
                       (cons g (cons (+ 1 (fn-cat-group-rows g c))
                                     (+ 2 (fn-cat-group-high g c))))
                     (hons-assoc-equal g tab))))
   :hints (("Goal" :in-theory (enable fn-cat$c-plan fn-cat$c-groups-get)
            :induct (fn-ctg-gputs-ind groups tab fn-cat$c)))))

; -----------------------------------------------------------------------------
; The assigned row is a held record; a member of the assignment carries the
; group's next number.

(local
 (defthm fn-ctg-numbersp-of-assign-numbers
   (fn-held-numbersp (fn-cat-assign-numbers groups c))
   :hints (("Goal" :in-theory (enable fn-held-numbersp)))))

(defthm fn-cat-held-p-of-assign
  (implies (fn-held-p h) (fn-held-p (fn-cat-assign h c)))
  :hints (("Goal" :in-theory (enable fn-held-p fn-cat-assign fn-held-with-numbers))))

(defthm fn-cat-held-p-of-with-withdrawn
  (implies (and (fn-held-p h) (fn-held-withdrawnp w))
           (fn-held-p (fn-held-with-withdrawn h w)))
  :hints (("Goal" :in-theory (enable fn-held-p fn-held-with-withdrawn))))

(defthm fn-cat-held-p-of-with-context
  (implies (and (fn-held-p h) (fn-hc-p ctx))
           (fn-held-p (fn-held-with-context h ctx)))
  :hints (("Goal" :in-theory (enable fn-held-p fn-held-with-context))))

(local
 (defthm fn-ctg-rowp-of-assign
   (implies (fn-cat-rowp h) (fn-cat-rowp (fn-cat-assign h c)))
   :hints (("Goal" :in-theory (enable fn-cat-rowp fn-cat-assign fn-held-with-numbers)))))

(local
 (defthm fn-ctg-rowp-of-with-withdrawn
   (implies (and (fn-cat-rowp h) (fn-held-withdrawnp w))
            (fn-cat-rowp (fn-held-with-withdrawn h w)))
   :hints (("Goal" :in-theory (enable fn-cat-rowp fn-held-with-withdrawn)))))

(local
 (defthm fn-ctg-rowp-of-with-context
   (implies (and (fn-cat-rowp h) (fn-hc-p ctx))
            (fn-cat-rowp (fn-held-with-context h ctx)))
   :hints (("Goal" :in-theory (enable fn-cat-rowp fn-cat-ctxp fn-hc-p fn-held-with-context)))))

(local
 (defthm fn-ctg-member-of-assign-numbers
   (implies (member-equal k (fn-cat-assign-numbers groups c))
            (and (consp k)
                 (member-equal (car k) groups)
                 (equal (cdr k) (+ 1 (fn-cat-group-high (car k) c)))))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; The numbers and groups tables' conjuncts after the commit.

; A key naming a row is never in a fresh assignment: its number is at most
; the group's high, and the assignment is one past it.
(local
 (defthm fn-ctg-named-key-not-assigned
   (implies (and (fn-cat-rowsp c)
                 (fn-cat-number-seq (car k) (cdr k) c 0)
                 (rationalp (cdr k)))
            (not (member-equal k (fn-cat-assign-numbers groups c))))))

; A number that names a row of a held list is a positive integer.
(local
 (defthm fn-ctg-number-seq-posp
   (implies (and (fn-cat-rowsp c) (fn-cat-number-seq g n c i))
            (posp n))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

; Old keys: a bound number names a row of C, so it is not in the
; assignment; its column is unchanged by the new row.
(local
 (defthm fn-ctg-numbers-okp-old-keys
   (implies (and (fn-cat-numbers-okp keys tab c) (fn-cat-rowsp c)
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c)))
            (fn-cat-numbers-okp keys
                                (fn-cat-nputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (len c) tab)
                                (append c (list (fn-cat-assign h c)))))
   :hints (("Goal" :induct (fn-cat-numbers-okp keys tab c)
            :in-theory (enable fn-held-number-in)))))

; -----------------------------------------------------------------------------
; The obligations, each as `defabsstobj-missing-events' states it.

(local
 (deftheory fn-ctg-open
   '(fn-cat$c-count update-fn-cat$c-count fn-cat$c-rowsi update-fn-cat$c-rowsi
     resize-fn-cat$c-rows fn-cat$c-rows-length fn-cat$c-octets update-fn-cat$c-octets
     fn-cat$c-mpx update-fn-cat$c-mpx
     fn-cat$c-unplaced update-fn-cat$c-unplaced
     fn-cat$c-numbers-get fn-cat$c-numbers-put fn-cat$c-numbers-clear
     fn-cat$c-groups-get fn-cat$c-groups-put fn-cat$c-groups-clear
     update-nth-array fn-cat$c-wfp fn-cat$c-at
     fn-cat$c-group-number fn-cat$c-group-next fn-cat$c-group-count
     fn-cat$c-total-octets fn-cat$c-visible-at
     fn-cat$c-lives-get fn-cat$c-lives-put fn-cat$c-lives-clear
     fn-cat$c-hz update-fn-cat$c-hz fn-cat$c-group-live-count
     fn-cat$c-group-live-low fn-cat$c-group-live-high fn-cat$c-horizon)))

(defthm create-fn-cat{correspondence-bl}
  (fn-cat$corr (create-fn-cat$c) (create-fn-cat$a))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cat$cp create-fn-cat$c)
                                  (fn-mlh-build-nil fn-mlh-set-key-is-a-list create-fn-mlh))
           :use (fn-mlh-create-is-build-nil
                 (:instance fn-mlh-build-nil (key (fn-mlh-key-octets (create-fn-mlh))))))))

(defthm create-fn-cat{preserved}
  (fn-cat$ap (create-fn-cat$a))
  :rule-classes nil)

(defthm fn-cat-count{correspondence-bl}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-count fn-cat$c) (fn-cat$a-count fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-at{correspondence-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-cat$ap fn-cat))
           (equal (fn-cat$c-at seq fn-cat$c) (fn-cat$a-at seq fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-at{guard-thm-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-cat$ap fn-cat))
           (and (fn-cat$c-wfp fn-cat$c) (natp seq) (< seq (fn-cat$c-count fn-cat$c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

; THE READER'S CORRESPONDENCE.  The nth-walk from I is the catalog's
; cdr-walk over the rows from I (PRF-970, folded in from the retired bridge
; book msgid-pages-catalog), so the paged reader is the column under the
; faithful relation; the fold with no unplaced row is faithful (PRF-1018);
; the confirmation over the rows array is the confirmation over the list;
; the degraded scan is the walk.
(local
 (defthm fn-ctg-nthcdr-cdr
   (implies (natp i) (equal (nthcdr (+ 1 i) l) (cdr (nthcdr i l))))))
(local
 (defthm fn-ctg-car-nthcdr
   (implies (natp i) (equal (car (nthcdr i l)) (nth i l)))))
(local
 (defthm fn-ctg-consp-nthcdr
   (implies (natp i) (iff (consp (nthcdr i l)) (< i (len l))))
   :hints (("Goal" :induct (nthcdr i l)))))

(defthm fn-mpxt-spec-from-is-cat-seqs-for
  (implies (natp i)
           (equal (fn-mpxt-spec-from i msgid rows)
                  (fn-cat-seqs-for msgid (nthcdr i rows) i)))
  :hints (("Goal" :induct (fn-mpxt-spec-from i msgid rows)
           :in-theory (enable fn-mpxt-spec-from fn-mpxt-hitp fn-cat-seqs-for))))

; KEYSTONE (PRF-970): the paged reader is the catalog's Message-ID column
; under the faithful relation.
(defthm fn-mlh-seqs-is-cat-msgid-seqs
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (fn-mlh-faithful fn-cat$a fn-mlh))
           (equal (fn-mlh-seqs msgid fn-cat$a fn-mlh)
                  (fn-cat$a-msgid-seqs msgid fn-cat$a)))
  :hints (("Goal" :in-theory (e/d (fn-cat$a-msgid-seqs nthcdr)
                                  (fn-mlh-seqs fn-mlh-faithful fn-cat-seqs-for
                                   fn-mpxt-spec-from fn-mpxt-spec-from-is-cat-seqs-for
                                   fn-mlh-seqs-is-spec-from))
           :use ((:instance fn-mlh-seqs-is-spec-from (rows fn-cat$a))
                 (:instance fn-mpxt-spec-from-is-cat-seqs-for (i 0) (rows fn-cat$a))))))

; The confirmation over the rows array is the confirmation over the list,
; for candidates below the count.
(local
 (defthm fn-ctg-confirm-is-confirm
   (implies (and (fn-cat-rows-corr n c (nth 0 fn-cat$c)) (equal (nth 1 fn-cat$c) n)
                 (natp n) (<= n (len (nth 0 fn-cat$c)))
                 (nat-listp seqs) (fn-mpx-below-p seqs n))
            (equal (fn-cat$c-confirm msgid seqs fn-cat$c)
                   (fn-mpxt-confirm msgid seqs c)))
   :hints (("Goal" :induct (fn-cat$c-confirm msgid seqs fn-cat$c)
            :in-theory (enable fn-cat$c-confirm fn-mpxt-confirm fn-mpxt-hitp fn-mpx-below-p
                               fn-cat$c-count fn-cat$c-rows-length fn-cat$c-rowsi)))))

; The degraded scan from I with ACC is the walk from I, reversed onto ACC.
(local
 (defthm fn-ctg-scan-is-seqs-for
   (implies (and (fn-cat-rows-corr n c (nth 0 fn-cat$c)) (equal (nth 1 fn-cat$c) n)
                 (natp n) (equal n (len c)) (true-listp c) (<= n (len (nth 0 fn-cat$c)))
                 (natp i) (true-listp acc))
            (equal (fn-cat$c-scan-msgid msgid i acc fn-cat$c)
                   (revappend acc (fn-cat-seqs-for msgid (nthcdr i c) i))))
   :hints (("Goal" :induct (fn-cat$c-scan-msgid msgid i acc fn-cat$c)
            :in-theory (e/d (fn-cat$c-scan-msgid fn-cat-seqs-for fn-cat$c-count fn-cat$c-rows-length
                             fn-cat$c-rowsi)
                            (nthcdr))
            :expand ((fn-cat-seqs-for msgid (nthcdr i c) i))))))

; The table that IS the fold with no unplaced row: well formed, its
; candidates below the count, its confirmed candidates the column.  Stated
; over a table variable, so the rewriter carries the relation's equality
; (an equation between a stobj field and the fold) into the reader's terms.
(local
 (defthm fn-ctg-fold-table-wfp
   (implies (equal tbl (fn-mlh-build key c))
            (fn-mlh-wfp tbl))
   :hints (("Goal" :in-theory (disable fn-mlh-wfp fn-mlh-build-nil fn-mlh-set-key-is-a-list)))))

(local
 (defthm fn-ctg-fold-candidates-below
   (implies (and (equal tbl (fn-mlh-build key c)) (true-listp c)
                 (equal (fn-mlh-build-unplaced key c) 0) (posp tag))
            (fn-mpx-below-p (fn-mlh-candidates tag tbl) (len c)))
   :hints (("Goal" :in-theory (e/d (fn-mlh-faithful)
                                   (fn-mlh-build-shape fn-mlh-build-nil fn-mlh-set-key-is-a-list
                                    fn-mlh-candidates fn-mlh-okp fn-mlh-faithful-from
                                    fn-mlh-build-faithful fn-mlh-candidates-below))
            :use ((:instance fn-mlh-build-faithful (rows c))
                  (:instance fn-mlh-build-shape (rows c))
                  (:instance fn-mlh-candidates-below (fn-mlh tbl) (n (len c))))))))

(local
 (defthm fn-ctg-fold-reader-is-the-column
   (implies (and (equal tbl (fn-mlh-build key c)) (true-listp c)
                 (equal (fn-mlh-build-unplaced key c) 0))
            (equal (fn-mpxt-confirm msgid (fn-mlh-candidates (fn-mlh-tag msgid (fn-mlh-key-octets tbl)) tbl) c)
                   (fn-cat-seqs-for msgid c 0)))
   :hints (("Goal" :in-theory (e/d (fn-mlh-seqs fn-cat$a-msgid-seqs)
                                   (fn-mlh-build-shape fn-mlh-build-nil fn-mlh-set-key-is-a-list
                                    fn-mlh-candidates fn-mpxt-confirm fn-mlh-faithful fn-cat-seqs-for
                                    fn-mlh-build-faithful fn-mlh-seqs-is-cat-msgid-seqs
                                    fn-mlh-seqs-is-spec-from fn-mpxt-spec-from-is-cat-seqs-for
                                    fn-mpxt-confirm-is-the-spec))
            :use ((:instance fn-mlh-build-faithful (rows c))
                  (:instance fn-mlh-build-shape (rows c))
                  (:instance fn-mlh-seqs-is-cat-msgid-seqs (fn-cat$a c) (fn-mlh (fn-mlh-build key c))))))))

(defthm fn-cat-msgid-seqs{correspondence-bl}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-msgid-seqs msgid fn-cat$c) (fn-cat$a-msgid-seqs msgid fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat$c-msgid-seqs fn-cat$c-unplaced fn-cat$c-mpx fn-cat$corr fn-cat$corr-base
                            fn-cat$a-msgid-seqs fn-cat-key-of)
                           (fn-cat$corr-live fn-mlh-candidates fn-mpxt-confirm fn-cat-rows-corr
                            fn-mlh-okp fn-mlh-faithful fn-mlh-faithful-from fn-cat-seqs-for
                            fn-mlh-build-nil fn-mlh-set-key-is-a-list fn-mlh-build-shape
                            fn-cat$c-confirm fn-cat$c-scan-msgid fn-mlh-wfp))
           :use ((:instance fn-ctg-confirm-is-confirm (n (len fn-cat)) (c fn-cat)
                            (seqs (fn-mlh-candidates
                                   (fn-mlh-tag msgid (fn-mlh-key-octets (nth *fn-cat$c-mpx* fn-cat$c)))
                                   (nth *fn-cat$c-mpx* fn-cat$c))))
                 (:instance fn-ctg-scan-is-seqs-for (n (len fn-cat)) (c fn-cat) (i 0) (acc nil))))))

(defthm fn-cat-group-number{correspondence-bl}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-group-number group n fn-cat$c)
                  (fn-cat$a-group-number group n fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-group-next{correspondence-bl}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-group-next group fn-cat$c) (fn-cat$a-group-next group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open)
           :cases ((consp (cdr (hons-assoc-equal group (nth 4 fn-cat$c))))))))

(defthm fn-cat-group-count{correspondence-bl}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-group-count group fn-cat$c) (fn-cat$a-group-count group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open)
           :cases ((consp (cdr (hons-assoc-equal group (nth 4 fn-cat$c))))))))

(defthm fn-cat-total-octets{correspondence-bl}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-total-octets fn-cat$c) (fn-cat$a-total-octets fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-visible-at{correspondence-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat)) (natp v)
                (fn-cat$ap fn-cat))
           (equal (fn-cat$c-visible-at seq v fn-cat$c) (fn-cat$a-visible-at seq v fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-visible-at{guard-thm-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat)) (natp v)
                (fn-cat$ap fn-cat))
           (and (fn-cat$c-wfp fn-cat$c) (natp seq) (natp v)
                (< seq (fn-cat$c-count fn-cat$c))
                (fn-held-withdrawnp (fn-held-withdrawn (fn-cat$c-rowsi seq fn-cat$c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

; The commit: the rows array gains the assigned row at the count, the
; Message-ID table its sequence, the numbers and groups tables the plan,
; the octets cell the row's octets, the count one.
; The groups walked with the numbers table extended at each step.
(local
 (defun fn-ctg-nputs-ind (groups seq tab fn-cat$c)
   (declare (xargs :stobjs fn-cat$c :verify-guards nil))
   (if (consp groups)
       (let ((e (fn-cat$c-groups-get (car groups) fn-cat$c)))
         (fn-ctg-nputs-ind (cdr groups) seq
                           (cons (cons (cons (car groups) (if (consp e) (nfix (cdr e)) 1)) seq)
                                 tab)
                           fn-cat$c))
     (list seq tab))))

; A listed group's assigned pair is in the assignment.
(local
 (defthm fn-ctg-assigned-member
   (implies (and (member-equal g groups) (equal n (+ 1 (fn-cat-group-high g c))))
            (member-equal (cons g n) (fn-cat-assign-numbers groups c)))))

; The new row's number in its own group is the assigned one; the column
; for it is the new row.
(defthm fn-ctg-number-seq-of-fresh
   (implies (and (fn-cat-rowsp c) (member-equal g (fn-record-groups h))
                 (equal n (+ 1 (fn-cat-group-high g c))))
            (equal (fn-cat-number-seq g n (append c (list (fn-cat-assign h c))) 0)
                   (len c))))

(local
 (defthm fn-ctg-commit-numbers-new-keys
   (implies (and (fn-cat-rowsp c)
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c))
                 (subsetp-equal groups (fn-record-groups h))
                 (fn-cat-numbers-okp tab2
                                     (fn-cat-nputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (len c) tab)
                                     (append c (list (fn-cat-assign h c)))))
            (fn-cat-numbers-okp
             (fn-cat-nputs (fn-cat$c-plan groups fn-cat$c) (len c) tab2)
             (fn-cat-nputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (len c) tab)
             (append c (list (fn-cat-assign h c)))))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-plan fn-cat$c-groups-get) (fn-cat-assign))
            :induct (fn-ctg-nputs-ind groups (len c) tab2 fn-cat$c)))))

(local
 (defthm fn-ctg-commit-numbers-cover-row-any
   (implies (and (subsetp-equal groups (fn-record-groups h))
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c)))
            (fn-cat-numbers-cover-rowp
             (fn-cat-assign-numbers groups c)
             (fn-cat-nputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) seq tab)))
   :hints (("Goal" :in-theory (enable fn-cat$c-plan fn-cat$c-groups-get)))))

(local
 (defthm fn-ctg-cover-rowp-monotone
   (implies (fn-cat-numbers-cover-rowp ns tab)
            (fn-cat-numbers-cover-rowp ns (fn-cat-nputs plan seq tab)))))

(local
 (defthm fn-ctg-numbers-coverp-monotone
   (implies (fn-cat-numbers-coverp c tab)
            (fn-cat-numbers-coverp c (fn-cat-nputs plan seq tab)))))

(local
 (defthm fn-ctg-numbers-coverp-append
   (equal (fn-cat-numbers-coverp (append c (list h)) tab)
          (and (fn-cat-numbers-coverp c tab)
               (fn-cat-numbers-cover-rowp (fn-held-numbers h) tab)))))

(local
 (defthm fn-ctg-subsetp-equal-of-cons-right
   (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(local
 (defthm fn-ctg-subsetp-equal-reflexive
   (subsetp-equal x x)))

(local
 (defthm fn-ctg-commit-numbers-coverp
   (implies (and (fn-cat-numbers-coverp c tab)
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c)))
            (fn-cat-numbers-coverp (append c (list (fn-cat-assign h c)))
                                   (fn-cat-nputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (len c) tab)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ctg-commit-numbers-cover-row-any
                             (groups (fn-record-groups h)) (seq (len c))))))))

(local
 (defthm fn-ctg-gputs-keeps-bound
   (implies (consp (hons-assoc-equal g tab))
            (consp (hons-assoc-equal g (fn-cat-gputs plan tab))))))

(local
 (defthm fn-ctg-groups-cover-rowp-monotone
   (implies (fn-cat-groups-cover-rowp ns tab)
            (fn-cat-groups-cover-rowp ns (fn-cat-gputs plan tab)))
   :hints (("Goal" :induct (fn-cat-groups-cover-rowp ns tab)
            :in-theory (disable fn-cat-gputs)))))

(local
 (defthm fn-ctg-groups-coverp-monotone
   (implies (fn-cat-groups-coverp c tab)
            (fn-cat-groups-coverp c (fn-cat-gputs plan tab)))
   :hints (("Goal" :induct (fn-cat-groups-coverp c tab)
            :in-theory (disable fn-cat-gputs fn-cat-groups-cover-rowp)))))

(local
 (defthm fn-ctg-groups-coverp-append
   (equal (fn-cat-groups-coverp (append c (list h)) tab)
          (and (fn-cat-groups-coverp c tab)
               (fn-cat-groups-cover-rowp (fn-held-numbers h) tab)))))

(local
 (defthm fn-ctg-commit-groups-cover-row
   (implies (and (subsetp-equal groups (fn-record-groups h))
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c)))
            (fn-cat-groups-cover-rowp
             (fn-cat-assign-numbers groups c)
             (fn-cat-gputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (nth 4 fn-cat$c))))))

(local
 (defthm fn-ctg-commit-groups-coverp
   (implies (and (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c)))
            (fn-cat-groups-coverp (append c (list (fn-cat-assign h c)))
                                  (fn-cat-gputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c)
                                                (nth 4 fn-cat$c))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-ctg-commit-groups-cover-row
                             (groups (fn-record-groups h))))))))

; The groups conjunct over every key of the new table: a key in the plan
; reads the advanced entry, an old key its old entry, and the column moved
; exactly when the group is the new row's.
(local
 (defthm fn-ctg-commit-groups-okp-keys
   (implies (and (fn-cat-rowsp c)
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c))
                 (fn-cat-groups-okp keys (nth 4 fn-cat$c) c))
            (fn-cat-groups-okp keys
                               (fn-cat-gputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (nth 4 fn-cat$c))
                               (append c (list (fn-cat-assign h c)))))
   :hints (("Goal" :induct (fn-cat-groups-okp keys (nth 4 fn-cat$c) c)))))

(local
 (defthm fn-ctg-commit-groups-okp-new-keys
   (implies (and (fn-cat-rowsp c)
                 (subsetp-equal groups (fn-record-groups h))
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c))
                 (fn-cat-groups-okp tab2
                                    (fn-cat-gputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (nth 4 fn-cat$c))
                                    (append c (list (fn-cat-assign h c)))))
            (fn-cat-groups-okp (fn-cat-gputs (fn-cat$c-plan groups fn-cat$c) tab2)
                               (fn-cat-gputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (nth 4 fn-cat$c))
                               (append c (list (fn-cat-assign h c)))))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-plan fn-cat$c-groups-get) (fn-cat-assign))
            :induct (fn-ctg-gputs-ind groups tab2 fn-cat$c)))))

; The committed state's fields, once, with the exec opened; the
; correspondence then reasons at the field level.
; The index's add: its two fields, the fold's step; every other field kept.
(local
 (defthm fn-ctg-index-add-fields
   (implies (fn-cat$cp fn-cat$c)
            (and (equal (nth 2 (fn-cat$c-index-add m seq fn-cat$c))
                        (if (and (< (+ 2 seq) *fn-mlh-tag-limit*) (fn-mlh-wfp (nth 2 fn-cat$c)))
                            (mv-nth 1 (fn-mlh-add (fn-mlh-tag m (fn-mlh-key-octets (nth 2 fn-cat$c)))
                                                   seq (nth 2 fn-cat$c)))
                          (nth 2 fn-cat$c)))
                 (equal (nth 9 (fn-cat$c-index-add m seq fn-cat$c))
                        (if (and (< (+ 2 seq) *fn-mlh-tag-limit*) (fn-mlh-wfp (nth 2 fn-cat$c))
                                 (equal (mv-nth 0 (fn-mlh-add (fn-mlh-tag m (fn-mlh-key-octets (nth 2 fn-cat$c)))
                                                               seq (nth 2 fn-cat$c)))
                                        :placed))
                            (nth 9 fn-cat$c)
                          (+ 1 (nth 9 fn-cat$c))))
                 (implies (and (natp k) (not (equal k 2)) (not (equal k 9)))
                          (equal (nth k (fn-cat$c-index-add m seq fn-cat$c)) (nth k fn-cat$c)))))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-index-add fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced)
                                   (fn-mlh-add))))))

(local
 (defthm fn-ctg-cp-of-index-add
   (implies (and (fn-cat$cp fn-cat$c) (natp seq))
            (fn-cat$cp (fn-cat$c-index-add m seq fn-cat$c)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-index-add fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced fn-cat$cp
                                    fn-cat$c-unplacedp)
                                   (fn-mlh-add))))))

(local
 (defthm fn-ctg-rows-length-of-index-add
   (equal (fn-cat$c-rows-length (fn-cat$c-index-add m seq fn-cat$c))
          (fn-cat$c-rows-length fn-cat$c))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-index-add fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced fn-cat$c-rows-length)
                                   (fn-mlh-add))))))

; The live layer and the rows array touch no index field.
(local
 (defthm fn-ctg-index-fields-of-writes
   (and (equal (nth 9 (update-fn-cat$c-rowsi i v x)) (nth 9 x))
        (equal (nth 9 (resize-fn-cat$c-rows n x)) (nth 9 x))
        (equal (nth 9 (update-fn-cat$c-count n x)) (nth 9 x))
        (equal (nth 9 (update-fn-cat$c-octets n x)) (nth 9 x))
        (equal (nth 9 (update-fn-cat$c-hz n x)) (nth 9 x))
        (equal (nth 9 (fn-cat$c-numbers-put key v x)) (nth 9 x))
        (equal (nth 9 (fn-cat$c-groups-put key v x)) (nth 9 x))
        (equal (nth 9 (fn-cat$c-lives-put key v x)) (nth 9 x))
        (equal (nth 9 (fn-cat$c-numbers-clear x)) (nth 9 x))
        (equal (nth 9 (fn-cat$c-groups-clear x)) (nth 9 x))
        (equal (nth 9 (fn-cat$c-lives-clear x)) (nth 9 x)))
   :hints (("Goal" :in-theory (enable update-fn-cat$c-rowsi resize-fn-cat$c-rows
                                      update-fn-cat$c-count update-fn-cat$c-octets
                                      update-fn-cat$c-hz fn-cat$c-numbers-put fn-cat$c-groups-put
                                      fn-cat$c-lives-put fn-cat$c-numbers-clear fn-cat$c-groups-clear
                                      fn-cat$c-lives-clear update-nth-array)))))

(local
 (defthm fn-ctg-apply-plan-fields-910
   (equal (nth 9 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 9 fn-cat$c))
   :hints (("Goal" :in-theory (enable fn-cat$c-apply-plan fn-cat$c-numbers-put
                                      fn-cat$c-groups-put)))))

(local
 (defthm fn-ctg-live-apply-fields-910
   (equal (nth 9 (fn-cat$c-live-apply plan x)) (nth 9 x))
   :hints (("Goal" :in-theory (enable fn-cat$c-live-apply fn-cat$c-lives-put)))))

(local
 (defthm fn-ctg-commit-fields
   (implies (fn-cat$cp fn-cat$c)
            (let ((plan (fn-cat$c-plan (fn-record-groups h) fn-cat$c))
                  (count (nth 1 fn-cat$c)))
              (and (equal (nth 0 (fn-cat$c-commit-base h fn-cat$c))
                          (update-nth count
                                      (fn-held-with-numbers h (fn-cat-plan-numbers plan))
                                      (if (< count (len (nth 0 fn-cat$c)))
                                          (nth 0 fn-cat$c)
                                        (resize-list (nth 0 fn-cat$c) (+ 1 (* 2 count)) nil))))
                   (equal (nth 1 (fn-cat$c-commit-base h fn-cat$c)) (+ 1 count))
                   (equal (nth 2 (fn-cat$c-commit-base h fn-cat$c))
                          (nth 2 (fn-cat$c-index-add (fn-record-msgid h) count fn-cat$c)))
                   (equal (nth 9 (fn-cat$c-commit-base h fn-cat$c))
                          (nth 9 (fn-cat$c-index-add (fn-record-msgid h) count fn-cat$c)))
                   (equal (nth 3 (fn-cat$c-commit-base h fn-cat$c))
                          (fn-cat-nputs plan count (nth 3 fn-cat$c)))
                   (equal (nth 4 (fn-cat$c-commit-base h fn-cat$c))
                          (fn-cat-gputs plan (nth 4 fn-cat$c)))
                   (equal (nth 5 (fn-cat$c-commit-base h fn-cat$c))
                          (+ (nth 5 fn-cat$c) (nfix (fn-hf-octets (fn-held-facts h))))))))
   :hints (("Goal" :in-theory (e/d (fn-ctg-open fn-cat$c-commit-base)
                                   (nth update-nth fn-cat$c-index-add))))))

(local
 (defthm fn-ctg-cells-of-index-add
   (and (equal (fn-cat$c-count (fn-cat$c-index-add m seq fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-octets (fn-cat$c-index-add m seq fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-hz (fn-cat$c-index-add m seq fn-cat$c)) (fn-cat$c-hz fn-cat$c))
        (equal (fn-cat$c-rowsi i (fn-cat$c-index-add m seq fn-cat$c)) (fn-cat$c-rowsi i fn-cat$c)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-index-add fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced
                                    fn-cat$c-count fn-cat$c-octets fn-cat$c-hz fn-cat$c-rowsi)
                                   (fn-mlh-add))))))

(local
 (defthm fn-ctg-cp-of-commit
   (implies (and (fn-cat$cp fn-cat$c) (fn-cat$c-wfp fn-cat$c))
            (fn-cat$cp (fn-cat$c-commit-base h fn-cat$c)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-commit-base fn-cat$c-wfp) (fn-cat$c-index-add))))))

; THE TABLE AFTER THE COMMIT IS THE FOLD OVER ONE MORE ROW.  Stated first
; over table variables (the rewriter carries their equations into the add),
; then instantiated with the stobj's own fields, whose equations are the
; relation's literal clauses.
(local
 (defthm fn-ctg-add-of-the-fold
   (implies (and (equal tbl (fn-mlh-build key c))
                 (equal u (fn-mlh-build-unplaced key c))
                 (equal seq (len c))
                 (equal m (fn-record-msgid h))
                 (< (+ 2 seq) *fn-mlh-tag-limit*))
            (and (equal (mv-nth 1 (fn-mlh-add (fn-mlh-tag m (fn-mlh-key-octets tbl)) seq tbl))
                        (fn-mlh-build key (append c (list h))))
                 (equal (if (equal (mv-nth 0 (fn-mlh-add (fn-mlh-tag m (fn-mlh-key-octets tbl)) seq tbl))
                                   :placed)
                            u
                          (+ 1 u))
                        (fn-mlh-build-unplaced key (append c (list h))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d () (fn-mlh-add fn-mlh-build-nil fn-mlh-set-key-is-a-list
                                       fn-mlh-build-shape))))))

(local
 (defthm fn-ctg-index-add-is-the-fold
   (implies (and (fn-cat$cp fn-cat$c)
                 (equal (nth 2 fn-cat$c) (fn-mlh-build key c))
                 (equal (nth 9 fn-cat$c) (fn-mlh-build-unplaced key c))
                 (equal seq (len c))
                 (equal m (fn-record-msgid h)))
            (and (equal (nth 2 (fn-cat$c-index-add m seq fn-cat$c))
                        (fn-mlh-build key (append c (list h))))
                 (equal (nth 9 (fn-cat$c-index-add m seq fn-cat$c))
                        (fn-mlh-build-unplaced key (append c (list h))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d () (fn-mlh-add fn-cat$c-index-add fn-mlh-build-append
                                       fn-mlh-build-nil fn-mlh-set-key-is-a-list fn-mlh-build-shape
                                       fn-ctg-fold-table-wfp))
            :use ((:instance fn-ctg-add-of-the-fold (tbl (nth 2 fn-cat$c))
                             (u (nth 9 fn-cat$c)))
                  (:instance fn-ctg-fold-table-wfp (tbl (nth 2 fn-cat$c)))
                  (:instance fn-mlh-build-append (rows c)))))))

; The key of the fold is the fold's key: the fixed point the corr states.
(local
 (defthm fn-ctg-key-of-index-add
   (implies (and (fn-cat$cp fn-cat$c) (natp seq))
            (equal (fn-cat-key-of (fn-cat$c-index-add m seq fn-cat$c))
                   (fn-cat-key-of fn-cat$c)))
   :hints (("Goal" :in-theory (e/d (fn-cat-key-of fn-cat$c-index-add fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced)
                                   (fn-mlh-add fn-mlh-add-shape fn-mlh-wfp))
            :use ((:instance fn-mlh-add-shape
                             (tag (fn-mlh-tag m (fn-mlh-key-octets (nth *fn-cat$c-mpx* fn-cat$c))))
                             (fn-mlh (nth *fn-cat$c-mpx* fn-cat$c))))))))

(defthm fn-ctg-len-of-append
   (equal (len (append a b)) (+ (len a) (len b))))

; Well-formedness in the corr's vocabulary.
(local
 (defthm fn-ctg-wfp-is-nth
   (implies (fn-cat$cp fn-cat$c)
            (equal (fn-cat$c-wfp fn-cat$c)
                   (<= (nth 1 fn-cat$c) (len (nth 0 fn-cat$c)))))
   :hints (("Goal" :in-theory (enable fn-cat$c-wfp fn-cat$c-count fn-cat$c-rows-length)))))

(local
 (defthm fn-ctg-wfp-from-corr
   (implies (fn-cat$corr-base fn-cat$c fn-cat)
            (fn-cat$c-wfp fn-cat$c))
   :hints (("Goal" :in-theory (enable fn-ctg-open)))))

; The committed row with its numbers replaced, as the commit's goals meet it
; (fn-cat-assign and fn-held-with-numbers opened): still a held row.
(local
 (defthm fn-ctg-held-p-of-renumbered-make
   (implies (and (fn-cat-rowp h) (fn-held-numbersp ns))
            (fn-cat-rowp (fn-held-make (fn-record-sequence h) (fn-record-txid h)
                                     (fn-record-generation h) (fn-record-msgid h)
                                     (fn-record-payload h) (fn-record-groups h)
                                     (fn-record-obligation-id h)
                                     (fn-record-content-subject h)
                                     (fn-record-release-evidence h)
                                     (fn-record-charge h) (fn-record-stamp h)
                                     (fn-held-facts h) (fn-held-context h)
                                     ns (fn-held-withdrawn h))))
   :hints (("Goal" :in-theory (enable fn-cat-rowp fn-record-internals fn-held-internals)))))

(local
 (defthm fn-ctg-cp-count-nth
   (implies (fn-cat$cp fn-cat$c)
            (natp (nth *fn-cat$c-count* fn-cat$c)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-countp)))))

(local
 (defthm fn-ctg-key-of-commit-base
   (implies (fn-cat$cp fn-cat$c)
            (equal (fn-cat-key-of (fn-cat$c-commit-base h fn-cat$c)) (fn-cat-key-of fn-cat$c)))
   :hints (("Goal" :in-theory (e/d (fn-cat-key-of)
                                   (fn-cat$c-commit-base fn-cat$c-index-add fn-ctg-index-add-fields
                                    fn-mlh-add fn-ctg-key-of-index-add))
            :use ((:instance fn-ctg-key-of-index-add (m (fn-record-msgid h)) (seq (nth 1 fn-cat$c))))))))

(local
 (defthm fn-ctg-commit-base-corr
   (implies (and (fn-cat$corr-base fn-cat$c fn-cat) (fn-held-p h) (fn-cat$ap fn-cat))
            (fn-cat$corr-base (fn-cat$c-commit-base h fn-cat$c) (fn-cat$a-commit h fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-assign)
                                   (fn-cat$c-commit-base fn-cat$c-plan fn-cat$c-groups-get resize-list
                                    fn-cat$c-index-add fn-ctg-index-add-fields fn-cat-key-of
                                    fn-mlh-build-shape fn-mlh-build-nil fn-mlh-set-key-is-a-list
                                    fn-mlh-add fn-ctg-fold-table-wfp fn-mlh-build-append))
            :do-not-induct t
            :use ((:instance fn-ctg-commit-numbers-new-keys
                             (groups (fn-record-groups h)) (tab2 (nth 3 fn-cat$c))
                             (tab (nth 3 fn-cat$c)) (c fn-cat))
                  (:instance fn-ctg-numbers-okp-old-keys
                             (keys (nth 3 fn-cat$c)) (tab (nth 3 fn-cat$c)) (c fn-cat))
                  (:instance fn-ctg-commit-groups-okp-new-keys
                             (groups (fn-record-groups h)) (tab2 (nth 4 fn-cat$c)) (c fn-cat))
                  (:instance fn-ctg-commit-groups-okp-keys
                             (keys (nth 4 fn-cat$c)) (c fn-cat))
                  (:instance fn-ctg-commit-numbers-coverp (tab (nth 3 fn-cat$c)) (c fn-cat))
                  (:instance fn-ctg-commit-groups-coverp (c fn-cat))
                  (:instance fn-ctg-index-add-is-the-fold
                             (key (fn-cat-key-of fn-cat$c)) (c fn-cat) (seq (nth 1 fn-cat$c))
                             (m (fn-record-msgid h)) (h (fn-cat-assign h fn-cat)))
                  (:instance fn-ctg-rows-corr-extend
                             (n (len fn-cat)) (c fn-cat)
                             (rows (if (< (len fn-cat) (len (nth 0 fn-cat$c)))
                                       (nth 0 fn-cat$c)
                                     (resize-list (nth 0 fn-cat$c) (+ 1 (* 2 (len fn-cat))) nil)))
                             (h (fn-cat-assign h fn-cat))))))))

(defthm fn-cat-commit{guard-thm-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (fn-held-p h) (fn-cat$ap fn-cat))
           (fn-cat$c-wfp fn-cat$c))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-commit{preserved}
  (implies (and (fn-held-p h) (fn-cat$ap fn-cat))
           (fn-cat$ap (fn-cat$a-commit h fn-cat)))
  :rule-classes nil)

; The table predicates under a same-key row replacement.
(local
 (defthm fn-ctg-build-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (and (equal (fn-mlh-build key (update-nth k h c)) (fn-mlh-build key c))
                 (equal (fn-mlh-build-unplaced key (update-nth k h c)) (fn-mlh-build-unplaced key c))))
   :hints (("Goal" :in-theory (enable fn-cat-same-keysp)))))

(local
 (defthm fn-ctg-numbers-okp-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-numbers-okp keys tab (update-nth k h c))
                   (fn-cat-numbers-okp keys tab c)))))

(local
 (defthm fn-ctg-groups-okp-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-groups-okp keys tab (update-nth k h c))
                   (fn-cat-groups-okp keys tab c)))))

(local
 (defthm fn-ctg-numbers-coverp-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-numbers-coverp (update-nth k h c) tab)
                   (fn-cat-numbers-coverp c tab)))))

(local
 (defthm fn-ctg-groups-coverp-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-groups-coverp (update-nth k h c) tab)
                   (fn-cat-groups-coverp c tab)))))

(local
 (defthm fn-ctg-withdraw-fields
   (implies (fn-cat$cp fn-cat$c)
            (let ((row (nth target (nth 0 fn-cat$c))))
              (and (equal (nth 0 (fn-cat$c-withdraw-base target by fn-cat$c))
                          (if (null (fn-held-withdrawn row))
                              (update-nth target
                                          (fn-held-with-withdrawn row (cons (nth 1 fn-cat$c) by))
                                          (nth 0 fn-cat$c))
                            (nth 0 fn-cat$c)))
                   (equal (nth 1 (fn-cat$c-withdraw-base target by fn-cat$c)) (nth 1 fn-cat$c))
                   (equal (nth 2 (fn-cat$c-withdraw-base target by fn-cat$c)) (nth 2 fn-cat$c))
                   (equal (nth 3 (fn-cat$c-withdraw-base target by fn-cat$c)) (nth 3 fn-cat$c))
                   (equal (nth 4 (fn-cat$c-withdraw-base target by fn-cat$c)) (nth 4 fn-cat$c))
                   (equal (nth 5 (fn-cat$c-withdraw-base target by fn-cat$c)) (nth 5 fn-cat$c)))))
   :hints (("Goal" :in-theory (e/d (fn-ctg-open fn-cat$c-withdraw-base) (nth update-nth))))))

(local
 (defthm fn-ctg-withdraw-fields-910
   (implies (fn-cat$cp fn-cat$c)
            (and (equal (nth 9 (fn-cat$c-withdraw-base target by fn-cat$c)) (nth 9 fn-cat$c))))
   :hints (("Goal" :in-theory (e/d (fn-ctg-open fn-cat$c-withdraw-base) (nth update-nth))))))

(local
 (defthm fn-ctg-cp-of-withdraw
   (implies (and (fn-cat$cp fn-cat$c) (natp target) (< target (len (nth 0 fn-cat$c))))
            (fn-cat$cp (fn-cat$c-withdraw-base target by fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-withdraw-base fn-cat$c-rows-length)))))

(local
 (defthm fn-ctg-withdraw-base-corr
   (implies (and (fn-cat$corr-base fn-cat$c fn-cat) (natp target) (< target (fn-cat$a-count fn-cat))
                 (natp by) (fn-cat$ap fn-cat))
            (fn-cat$corr-base (fn-cat$c-withdraw-base target by fn-cat$c)
                         (fn-cat$a-withdraw target by fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-mark-withdrawn)
                                   (fn-cat$c-withdraw-base fn-held-with-withdrawn))
            :do-not-induct t))))

(defthm fn-cat-withdraw{guard-thm-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp target) (< target (fn-cat$a-count fn-cat))
                (natp by) (fn-cat$ap fn-cat))
           (and (fn-cat$c-wfp fn-cat$c) (natp target) (natp by)
                (< target (fn-cat$c-count fn-cat$c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-withdraw{preserved}
  (implies (and (natp target) (< target (fn-cat$a-count fn-cat)) (natp by) (fn-cat$ap fn-cat))
           (fn-cat$ap (fn-cat$a-withdraw target by fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cat-mark-withdrawn) (fn-held-with-withdrawn))
           :do-not-induct t)))

(local
 (defthm fn-ctg-redecide-fields
   (implies (fn-cat$cp fn-cat$c)
            (and (equal (nth 0 (fn-cat$c-redecide seq context fn-cat$c))
                        (update-nth seq
                                    (fn-held-with-context (nth seq (nth 0 fn-cat$c)) context)
                                    (nth 0 fn-cat$c)))
                 (equal (nth 1 (fn-cat$c-redecide seq context fn-cat$c)) (nth 1 fn-cat$c))
                 (equal (nth 2 (fn-cat$c-redecide seq context fn-cat$c)) (nth 2 fn-cat$c))
                 (equal (nth 3 (fn-cat$c-redecide seq context fn-cat$c)) (nth 3 fn-cat$c))
                 (equal (nth 4 (fn-cat$c-redecide seq context fn-cat$c)) (nth 4 fn-cat$c))
                 (equal (nth 5 (fn-cat$c-redecide seq context fn-cat$c)) (nth 5 fn-cat$c))))
   :hints (("Goal" :in-theory (e/d (fn-ctg-open fn-cat$c-redecide) (nth update-nth))))))

(local
 (defthm fn-ctg-redecide-fields-910
   (implies (fn-cat$cp fn-cat$c)
            (and (equal (nth 9 (fn-cat$c-redecide seq context fn-cat$c)) (nth 9 fn-cat$c))))
   :hints (("Goal" :in-theory (e/d (fn-ctg-open fn-cat$c-redecide) (nth update-nth))))))

(local
 (defthm fn-ctg-cp-of-redecide
   (implies (and (fn-cat$cp fn-cat$c) (natp seq) (< seq (len (nth 0 fn-cat$c))))
            (fn-cat$cp (fn-cat$c-redecide seq context fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-redecide fn-cat$c-rows-length)))))

(local
 (defthm fn-ctg-redecide-base-corr
   (implies (and (fn-cat$corr-base fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                 (fn-hc-p context) (fn-cat$ap fn-cat))
            (fn-cat$corr-base (fn-cat$c-redecide seq context fn-cat$c)
                         (fn-cat$a-redecide seq context fn-cat)))
   :hints (("Goal" :in-theory (disable fn-cat$c-redecide fn-held-with-context)
            :do-not-induct t))))

(defthm fn-cat-redecide{guard-thm-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-hc-p context) (fn-cat$ap fn-cat))
           (and (fn-cat$c-wfp fn-cat$c) (natp seq) (< seq (fn-cat$c-count fn-cat$c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-redecide{preserved}
  (implies (and (natp seq) (< seq (fn-cat$a-count fn-cat)) (fn-hc-p context) (fn-cat$ap fn-cat))
           (fn-cat$ap (fn-cat$a-redecide seq context fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-held-with-context) :do-not-induct t)))

(local
 (defthm fn-ctg-index-clear-fields
   (implies (fn-cat$cp fn-cat$c)
            (and (equal (nth 2 (fn-cat$c-index-clear fn-cat$c)) (fn-mlh-clear (nth 2 fn-cat$c)))
                 (equal (nth 9 (fn-cat$c-index-clear fn-cat$c)) 0)
                 (implies (and (natp k) (not (equal k 2)) (not (equal k 9)))
                          (equal (nth k (fn-cat$c-index-clear fn-cat$c)) (nth k fn-cat$c)))
                 (fn-cat$cp (fn-cat$c-index-clear fn-cat$c))))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-index-clear fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced fn-cat$cp fn-cat$c-unplacedp)
                                   (fn-mlh-clear fn-mlh-set-key fn-mlh-set-key-is-a-list
                                    fn-mlh-clear-is-build-nil))))))

(local
 (defthm fn-ctg-index-clear-frame
   (implies (and (natp k) (not (equal k 2)) (not (equal k 9)))
            (equal (nth k (fn-cat$c-index-clear fn-cat$c)) (nth k fn-cat$c)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-index-clear fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced)
                                   (fn-mlh-clear fn-mlh-set-key fn-mlh-set-key-is-a-list
                                    fn-mlh-clear-is-build-nil))))))

(local
 (defthm fn-ctg-index-clear-fields-u
   (and (equal (nth 2 (fn-cat$c-index-clear fn-cat$c)) (fn-mlh-clear (nth 2 fn-cat$c)))
        (equal (nth 9 (fn-cat$c-index-clear fn-cat$c)) 0))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-index-clear fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced)
                                   (fn-mlh-clear fn-mlh-set-key fn-mlh-set-key-is-a-list
                                    fn-mlh-clear-is-build-nil))))))

(local
 (defthm fn-ctg-cp-of-clear
   (implies (fn-cat$cp fn-cat$c)
            (fn-cat$cp (fn-cat$c-clear-base fn-cat$c)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-clear-base) (fn-cat$c-index-clear))))))

(local
 (defthm fn-ctg-clear-fields
   (implies (fn-cat$cp fn-cat$c)
            (and (equal (nth 1 (fn-cat$c-clear-base fn-cat$c)) 0)
                 (equal (nth 2 (fn-cat$c-clear-base fn-cat$c)) (fn-mlh-clear (nth 2 fn-cat$c)))
                 (equal (nth 9 (fn-cat$c-clear-base fn-cat$c)) 0)
                 (equal (nth 3 (fn-cat$c-clear-base fn-cat$c)) nil)
                 (equal (nth 4 (fn-cat$c-clear-base fn-cat$c)) nil)
                 (equal (nth 5 (fn-cat$c-clear-base fn-cat$c)) 0)))
   :hints (("Goal" :in-theory (e/d (fn-ctg-open fn-cat$c-clear-base)
                                   (nth update-nth fn-cat$c-index-clear fn-mlh-clear fn-mlh-set-key
                                    fn-mlh-set-key-is-a-list fn-mlh-clear-is-build-nil))))))

;; The two tables' key recognizers are the same predicate.
(local
 (defthm fn-ctg-mlh-keyp-is-mpxt-keyp
   (implies (fn-mlh-keyp l) (fn-mpxt-keyp l))
   :hints (("Goal" :in-theory (enable fn-mlh-keyp fn-mpxt-keyp)))))

; A table's key is a 32-octet key (books/msgid-pages-exec 7h, off the
; recognizer), so writing it back reads back as itself.
(local
 (defthm fn-ctg-key-octets-is-a-key
   (implies (fn-mlhp x)
            (and (fn-mpxt-keyp (fn-mlh-key-octets x))
                 (equal (len (fn-mlh-key-octets x)) *fn-mpxt-key-octets*)))
   :hints (("Goal" :use ((:instance fn-mlh-key-from-is-nthcdr (i 0) (fn-mlh x)))
            :in-theory (e/d (fn-mlhp fn-mlh-key-octets) (fn-mlh-key-from))))))

(local
 (defthm fn-ctg-clear-base-corr
   (implies (fn-cat$corr-base fn-cat$c fn-cat)
            (fn-cat$corr-base (fn-cat$c-clear-base fn-cat$c) (fn-cat$a-clear fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-key-of)
                                   (fn-cat$c-clear-base fn-mlh-clear fn-mlh-set-key
                                    fn-mlh-set-key-is-a-list))
            :do-not-induct t))))

(defthm fn-cat-clear{preserved}
  (implies (fn-cat$ap fn-cat)
           (fn-cat$ap (fn-cat$a-clear fn-cat)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The live summary's obligations (sca-join-5).  The table and the horizon
; cell are written after the base tables, from entries read before any write;
; the base relation reads fields 0 .. 5 only.

(defun fn-ctg-lputs (plan tab)
  (declare (xargs :guard t))
  (if (consp plan)
      (fn-ctg-lputs (cdr plan) (cons (cons (fn-cbor-ag-car (car plan))
                                           (fn-cbor-ag-cdr (car plan)))
                                     tab))
    tab))

(local
 (defthm fn-ctg-live-apply-fields
   (and (equal (nth 0 (fn-cat$c-live-apply plan x)) (nth 0 x))
        (equal (nth 1 (fn-cat$c-live-apply plan x)) (nth 1 x))
        (equal (nth 2 (fn-cat$c-live-apply plan x)) (nth 2 x))
        (equal (nth 3 (fn-cat$c-live-apply plan x)) (nth 3 x))
        (equal (nth 4 (fn-cat$c-live-apply plan x)) (nth 4 x))
        (equal (nth 5 (fn-cat$c-live-apply plan x)) (nth 5 x))
        (equal (nth 6 (fn-cat$c-live-apply plan x)) (fn-ctg-lputs plan (nth 6 x)))
        (equal (nth 7 (fn-cat$c-live-apply plan x)) (nth 7 x)))
   :hints (("Goal" :in-theory (enable fn-cat$c-live-apply fn-cat$c-lives-put)))))

(local
 (defthm fn-ctg-cp-of-live-apply
   (implies (fn-cat$cp x) (fn-cat$cp (fn-cat$c-live-apply plan x)))
   :hints (("Goal" :in-theory (enable fn-cat$c-live-apply)))))

(local
 (defthm fn-ctg-update-hz-fields
   (and (equal (nth 0 (update-fn-cat$c-hz n x)) (nth 0 x))
        (equal (nth 1 (update-fn-cat$c-hz n x)) (nth 1 x))
        (equal (nth 2 (update-fn-cat$c-hz n x)) (nth 2 x))
        (equal (nth 3 (update-fn-cat$c-hz n x)) (nth 3 x))
        (equal (nth 4 (update-fn-cat$c-hz n x)) (nth 4 x))
        (equal (nth 5 (update-fn-cat$c-hz n x)) (nth 5 x))
        (equal (nth 6 (update-fn-cat$c-hz n x)) (nth 6 x))
        (equal (nth 7 (update-fn-cat$c-hz n x)) n))
   :hints (("Goal" :in-theory (enable update-fn-cat$c-hz)))))

(local
 (defthm fn-ctg-lives-clear-fields
   (and (equal (nth 0 (fn-cat$c-lives-clear x)) (nth 0 x))
        (equal (nth 1 (fn-cat$c-lives-clear x)) (nth 1 x))
        (equal (nth 2 (fn-cat$c-lives-clear x)) (nth 2 x))
        (equal (nth 3 (fn-cat$c-lives-clear x)) (nth 3 x))
        (equal (nth 4 (fn-cat$c-lives-clear x)) (nth 4 x))
        (equal (nth 5 (fn-cat$c-lives-clear x)) (nth 5 x))
        (equal (nth 6 (fn-cat$c-lives-clear x)) nil)
        (equal (nth 7 (fn-cat$c-lives-clear x)) (nth 7 x)))
   :hints (("Goal" :in-theory (enable fn-cat$c-lives-clear)))))

(local
 (defthm fn-ctg-apply-plan-fields-67
   (and (equal (nth 6 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 6 fn-cat$c))
        (equal (nth 7 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 7 fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-apply-plan fn-cat$c-numbers-put
                                      fn-cat$c-groups-put)))))

(local
 (defthm fn-ctg-base-fields-67
   (implies (fn-cat$cp fn-cat$c)
            (and (equal (nth 6 (fn-cat$c-commit-base h fn-cat$c)) (nth 6 fn-cat$c))
                 (equal (nth 7 (fn-cat$c-commit-base h fn-cat$c)) (nth 7 fn-cat$c))
                 (equal (nth 6 (fn-cat$c-withdraw-base target by fn-cat$c)) (nth 6 fn-cat$c))
                 (equal (nth 7 (fn-cat$c-withdraw-base target by fn-cat$c)) (nth 7 fn-cat$c))
                 (equal (nth 6 (fn-cat$c-redecide seq context fn-cat$c)) (nth 6 fn-cat$c))
                 (equal (nth 7 (fn-cat$c-redecide seq context fn-cat$c)) (nth 7 fn-cat$c))))
   :hints (("Goal" :in-theory (e/d (fn-ctg-open fn-cat$c-commit-base fn-cat$c-withdraw-base
                                    fn-cat$c-redecide)
                                   (nth update-nth fn-cat$c-apply-plan))))))

; The base relation reads the recognizer and fields 0 .. 5.
(local
 (defthm fn-ctg-corr-base-fields
   (implies (and (fn-cat$cp x) (fn-cat$cp y)
                 (equal (nth 0 y) (nth 0 x)) (equal (nth 1 y) (nth 1 x))
                 (equal (nth 2 y) (nth 2 x)) (equal (nth 3 y) (nth 3 x))
                 (equal (nth 4 y) (nth 4 x)) (equal (nth 5 y) (nth 5 x))
                 (equal (nth 9 y) (nth 9 x)))
            (iff (fn-cat$corr-base y a) (fn-cat$corr-base x a)))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-cat$corr-base fn-cat-key-of) (theory 'minimal-theory))))))

(local
 (defthm fn-ctg-live-okp-bound
   (implies (and (fn-cat-live-okp keys tab c) (consp (hons-assoc-equal g keys)))
            (equal (cdr (hons-assoc-equal g tab)) (fn-cat-live-entry g c)))))

(local
 (defthm fn-ctg-live-at-p-is-live
   (implies (fn-cat$corr-base x c)
            (equal (fn-cat$c-live-at-p g k x) (fn-cat-live-numberp g k c)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-live-at-p fn-cat-live-numberp fn-ctg-open)
                                   (fn-cat-live-rowp fn-cat-number-seq))))))

(local
 (defthm fn-ctg-scan-up-is-first
   (implies (fn-cat$corr-base x c)
            (equal (fn-cat$c-scan-up g k top x) (fn-cat-live-first g k top c)))
   :hints (("Goal" :induct (fn-cat-live-first g k top c)
            :in-theory (e/d (fn-cat$c-scan-up) (fn-cat$corr-base fn-cat$c-live-at-p
                                                 fn-cat-live-numberp))))))

(local
 (defthm fn-ctg-scan-down-is-last
   (implies (fn-cat$corr-base x c)
            (equal (fn-cat$c-scan-down g k x) (fn-cat-live-last g k c)))
   :hints (("Goal" :induct (fn-cat-live-last g k c)
            :in-theory (e/d (fn-cat$c-scan-down) (fn-cat$corr-base fn-cat$c-live-at-p
                                                   fn-cat-live-numberp))))))

(local
 (defthm fn-ctg-live-lookup
   (implies (and (fn-cat-live-okp tab tab c) (fn-cat-groups-coverp c tab))
            (equal (cdr (hons-assoc-equal g tab))
                   (if (consp (hons-assoc-equal g tab))
                       (fn-cat-live-entry g c)
                     nil)))
   :hints (("Goal" :in-theory (disable fn-cat-live-entry fn-cat-live-okp fn-cat-groups-coverp)
            :use ((:instance fn-ctg-live-okp-bound (keys tab)))))))

(local
 (defthm fn-ctg-live-unbound-high
   (implies (and (fn-cat-groups-coverp c tab) (not (consp (hons-assoc-equal g tab))))
            (equal (fn-cat-group-high g c) 0))
   :hints (("Goal" :use fn-ctg-groups-unbound
            :in-theory (disable fn-ctg-groups-unbound fn-cat-groups-coverp fn-cat-group-high)))))

(local
 (defthm fn-ctg-live-readers
   (implies (and (fn-cat-live-okp (nth 6 x) (nth 6 x) c)
                 (fn-cat-groups-coverp c (nth 6 x)))
            (and (equal (fn-cat$c-group-live-count g x)
                        (fn-cat-live-count-from g 1 (fn-cat-group-high g c) c))
                 (equal (fn-cat$c-group-live-low g x)
                        (fn-cat-live-first g 1 (fn-cat-group-high g c) c))
                 (equal (fn-cat$c-group-live-high g x)
                        (fn-cat-live-last g (fn-cat-group-high g c) c))))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-group-live-count fn-cat$c-group-live-low
                                    fn-cat$c-group-live-high fn-cat$c-lives-get
                                    fn-cat-live-entry)
                                   (fn-cat-live-count-from fn-cat-live-first fn-cat-live-last
                                    fn-cat-live-okp fn-cat-groups-coverp fn-cat-group-high
                                    hons-assoc-equal))
            :expand ((fn-cat-live-last g 0 c))
            :cases ((consp (hons-assoc-equal g (nth 6 x))))))))

; The commit.
(defun fn-ctg-commit-entry (g livep c)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((hi (fn-cat-group-high g c))
         (n (+ 1 hi))
         (count (fn-cat-live-count-from g 1 hi c))
         (low (fn-cat-live-first g 1 hi c))
         (high (fn-cat-live-last g hi c)))
    (if (and livep (<= n *fn-nntp-max-article-number*))
        (cons (+ 1 count) (cons (if (equal low 0) n low) n))
      (cons count (cons low high)))))

(local
 (defun fn-ctg-lplan-ind (groups livep tab fn-cat$c)
   (declare (xargs :stobjs fn-cat$c :verify-guards nil))
   (if (consp groups)
       (let ((e (car (fn-cat$c-live-plan groups livep fn-cat$c))))
         (fn-ctg-lplan-ind (cdr groups) livep
                           (cons (cons (fn-cbor-ag-car e) (fn-cbor-ag-cdr e)) tab)
                           fn-cat$c))
     (list tab livep))))

(local
 (defthm fn-ctg-lplan-lookup
   (implies (and (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c))
                 (fn-cat-live-okp (nth 6 fn-cat$c) (nth 6 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 6 fn-cat$c)))
            (equal (hons-assoc-equal g (fn-ctg-lputs (fn-cat$c-live-plan groups livep fn-cat$c) tab))
                   (if (member-equal g groups)
                       (cons g (fn-ctg-commit-entry g livep c))
                     (hons-assoc-equal g tab))))
   :hints (("Goal" :induct (fn-ctg-lplan-ind groups livep tab fn-cat$c)
            :in-theory (e/d (fn-cat$c-live-plan fn-cat$c-groups-get)
                            (fn-cat-live-count-from fn-cat-live-first fn-cat-live-last
                             fn-cat-live-okp fn-cat-groups-coverp fn-cat-groups-okp
                             fn-cat$c-group-live-count fn-cat$c-group-live-low
                             fn-cat$c-group-live-high))))))

(local
 (defthm fn-ctg-live-entry-append-member
   (implies (and (fn-cat-rowsp c) (member-equal g (fn-record-groups h)))
            (equal (fn-cat-live-entry g (append c (list (fn-cat-assign h c))))
                   (fn-ctg-commit-entry g (fn-cat-live-candidatep h)
                                        c)))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-entry)
                                   (fn-cat-assign fn-cat-live-count-from fn-cat-live-first
                                    fn-cat-live-numberp fn-scat-msgid-idp))
            :expand ((fn-cat-live-last g (+ 1 (fn-cat-group-high g c))
                                       (append c (list (fn-cat-assign h c)))))))))

(local
 (defthm fn-ctg-live-entry-append-other
   (implies (and (fn-cat-rowsp c) (not (member-equal g (fn-record-groups h))))
            (equal (fn-cat-live-entry g (append c (list (fn-cat-assign h c))))
                   (fn-cat-live-entry g c)))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-entry)
                                   (fn-cat-assign fn-cat-live-count-from fn-cat-live-first
                                    fn-cat-live-last fn-cat-live-numberp))))))

(local
 (defthm fn-ctg-commit-live-okp-old
   (implies (and (fn-cat-rowsp c)
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c))
                 (fn-cat-live-okp (nth 6 fn-cat$c) (nth 6 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 6 fn-cat$c))
                 (fn-cat-live-okp keys (nth 6 fn-cat$c) c))
            (fn-cat-live-okp keys
                             (fn-ctg-lputs (fn-cat$c-live-plan
                                            (fn-record-groups h)
                                            (fn-cat-live-candidatep h)
                                            fn-cat$c)
                                           (nth 6 fn-cat$c))
                             (append c (list (fn-cat-assign h c)))))
   :hints (("Goal" :induct (fn-cat-live-okp keys (nth 6 fn-cat$c) c)
            :in-theory (disable fn-cat-live-entry fn-ctg-commit-entry fn-cat-assign
                                fn-cat-groups-okp fn-cat-groups-coverp fn-scat-msgid-idp)))))

(defun fn-ctg-plan-keys-in (plan groups)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp plan)
      (and (member-equal (fn-cbor-ag-car (car plan)) groups)
           (fn-ctg-plan-keys-in (cdr plan) groups))
    t))

(local
 (defthm fn-ctg-live-plan-keys-in
   (fn-ctg-plan-keys-in (fn-cat$c-live-plan groups livep fn-cat$c) groups)
   :hints (("Goal" :in-theory (e/d (fn-cat$c-live-plan)
                                   (fn-cat$c-group-live-count fn-cat$c-group-live-low
                                    fn-cat$c-group-live-high fn-cat$c-groups-get))))))

(local
 (defthm fn-ctg-commit-lookup-member
   (implies (and (fn-cat-rowsp c)
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c))
                 (fn-cat-live-okp (nth 6 fn-cat$c) (nth 6 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 6 fn-cat$c))
                 (equal livep (fn-cat-live-candidatep h))
                 (member-equal g (fn-record-groups h)))
            (equal (cdr (hons-assoc-equal
                         g (fn-ctg-lputs (fn-cat$c-live-plan (fn-record-groups h) livep fn-cat$c)
                                         tab)))
                   (fn-cat-live-entry g (append c (list (fn-cat-assign h c))))))
   :hints (("Goal" :in-theory (disable fn-cat-live-entry fn-ctg-commit-entry fn-cat-assign
                                       fn-cat-groups-okp fn-cat-groups-coverp fn-cat-live-okp
                                       fn-scat-msgid-idp fn-cat$c-live-plan)))))

(local
 (defthm fn-ctg-commit-live-okp-new
   (implies (and (fn-cat-rowsp c)
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c))
                 (fn-cat-live-okp (nth 6 fn-cat$c) (nth 6 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 6 fn-cat$c))
                 (equal livep (fn-cat-live-candidatep h))
                 (fn-ctg-plan-keys-in plan (fn-record-groups h))
                 (fn-cat-live-okp tab2
                                  (fn-ctg-lputs (fn-cat$c-live-plan (fn-record-groups h) livep fn-cat$c)
                                                (nth 6 fn-cat$c))
                                  (append c (list (fn-cat-assign h c)))))
            (fn-cat-live-okp (fn-ctg-lputs plan tab2)
                             (fn-ctg-lputs (fn-cat$c-live-plan (fn-record-groups h) livep fn-cat$c)
                                           (nth 6 fn-cat$c))
                             (append c (list (fn-cat-assign h c)))))
   :hints (("Goal" :induct (fn-ctg-lputs plan tab2)
            :in-theory (disable fn-cat-live-entry fn-ctg-commit-entry fn-cat-assign
                                fn-cat-groups-okp fn-cat-groups-coverp fn-scat-msgid-idp
                                fn-cat$c-live-plan fn-ctg-lplan-lookup)))))

(local
 (defthm fn-ctg-lputs-keeps-bound
   (implies (consp (hons-assoc-equal g tab))
            (consp (hons-assoc-equal g (fn-ctg-lputs plan tab))))))

(local
 (defthm fn-ctg-cover-rowp-lputs
   (implies (fn-cat-groups-cover-rowp ns tab)
            (fn-cat-groups-cover-rowp ns (fn-ctg-lputs plan tab)))
   :hints (("Goal" :induct (fn-cat-groups-cover-rowp ns tab)
            :in-theory (disable fn-ctg-lputs)))))

(local
 (defthm fn-ctg-coverp-lputs
   (implies (fn-cat-groups-coverp c tab)
            (fn-cat-groups-coverp c (fn-ctg-lputs plan tab)))
   :hints (("Goal" :induct (fn-cat-groups-coverp c tab)
            :in-theory (disable fn-ctg-lputs fn-cat-groups-cover-rowp)))))

(local
 (defthm fn-ctg-commit-live-cover-row
   (implies (and (subsetp-equal groups (fn-record-groups h))
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c))
                 (fn-cat-live-okp (nth 6 fn-cat$c) (nth 6 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 6 fn-cat$c)))
            (fn-cat-groups-cover-rowp
             (fn-cat-assign-numbers groups c)
             (fn-ctg-lputs (fn-cat$c-live-plan (fn-record-groups h) livep fn-cat$c) tab)))
   :hints (("Goal" :induct (len groups)
            :in-theory (disable fn-ctg-commit-entry fn-cat-live-okp fn-cat-groups-okp
                                fn-cat-groups-coverp)))))

(local
 (defthm fn-ctg-commit-live-fields
   (implies (fn-cat$cp fn-cat$c)
            (and (equal (nth 6 (fn-cat$c-commit h fn-cat$c))
                        (fn-ctg-lputs (fn-cat$c-live-plan
                                       (fn-record-groups h)
                                       (fn-cat-live-candidatep h)
                                       fn-cat$c)
                                      (nth 6 fn-cat$c)))
                 (equal (nth 7 (fn-cat$c-commit h fn-cat$c))
                        (max (nth 7 fn-cat$c)
                             (let ((w (fn-held-withdrawn h)))
                               (if (consp w) (+ 1 (nfix (car w))) 0))))))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-commit fn-cat$c-hz)
                                   (fn-cat$c-live-plan fn-cat$c-commit-base
                                    fn-cat$c-live-apply fn-scat-msgid-idp))))))

(local
 (defthm fn-ctg-commit-live-corr
   (implies (and (fn-cat$corr fn-cat$c fn-cat) (fn-held-p h) (fn-cat$ap fn-cat))
            (fn-cat$corr-live (fn-cat$c-commit h fn-cat$c) (fn-cat$a-commit h fn-cat)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d ()
                            (fn-cat-assign fn-cat$c-commit fn-cat$c-live-plan fn-cat-live-okp
                             fn-cat-groups-okp fn-cat-groups-coverp fn-scat-msgid-idp
                             fn-cat-rows-corr
                             fn-cat-numbers-okp fn-cat-numbers-coverp fn-held-with-numbers))
            :use ((:instance fn-ctg-commit-live-okp-new
                             (c fn-cat)
                             (livep (fn-cat-live-candidatep h))
                             (plan (fn-cat$c-live-plan
                                    (fn-record-groups h)
                                    (fn-cat-live-candidatep h)
                                    fn-cat$c))
                             (tab2 (nth 6 fn-cat$c)))
                  (:instance fn-ctg-live-plan-keys-in
                             (groups (fn-record-groups h))
                             (livep (fn-cat-live-candidatep h)))
                  (:instance fn-ctg-commit-live-okp-old (c fn-cat) (keys (nth 6 fn-cat$c)))
                  (:instance fn-ctg-commit-live-cover-row
                             (c fn-cat) (groups (fn-record-groups h))
                             (livep (fn-cat-live-candidatep h))
                             (tab (nth 6 fn-cat$c))))))))

(local
 (defthm fn-ctg-corr-base-cp
   (implies (fn-cat$corr-base x a)
            (and (fn-cat$cp x) (fn-cat$c-wfp x)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-ctg-wfp-is-nth)))))

(local
 (defthm fn-ctg-commit-base-keeps-corr-base
   (implies (and (fn-cat$corr-base fn-cat$c fn-cat) (fn-held-p h) (fn-cat$ap fn-cat))
            (fn-cat$corr-base (fn-cat$c-commit h fn-cat$c) (fn-cat$a-commit h fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-commit)
                                   (fn-cat$corr-base fn-cat$c-commit-base fn-cat$c-live-apply
                                    fn-cat$c-live-plan fn-scat-msgid-idp fn-cat$a-commit))
            :use ((:instance fn-ctg-commit-base-corr)
                  (:instance fn-ctg-corr-base-fields
                             (x (fn-cat$c-commit-base h fn-cat$c))
                             (y (update-fn-cat$c-hz (max (fn-cat$c-hz fn-cat$c)
                                           (if (consp (fn-held-withdrawn h))
                                               (+ 1 (nfix (car (fn-held-withdrawn h)))) 0))
                                 (fn-cat$c-live-apply (fn-cat$c-live-plan (fn-record-groups h)
                                                        (fn-cat-live-candidatep h)
                                                        fn-cat$c)
                                  (fn-cat$c-commit-base h fn-cat$c))))
                             (a (fn-cat$a-commit h fn-cat))))))))

(defthm fn-cat-commit{correspondence-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (fn-held-p h) (fn-cat$ap fn-cat))
           (fn-cat$corr (fn-cat$c-commit h fn-cat$c) (fn-cat$a-commit h fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-cat$corr) (theory 'minimal-theory))
           :use ((:instance fn-ctg-commit-live-corr)
                 (:instance fn-ctg-commit-base-corr)
                 (:instance fn-ctg-commit-base-keeps-corr-base)))))

; The withdrawal.
(defun fn-ctg-drop-entry-l (g k c)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((hi (fn-cat-group-high g c))
         (count (fn-cat-live-count-from g 1 hi c))
         (low (fn-cat-live-first g 1 hi c))
         (high (fn-cat-live-last g hi c)))
    (cons (nfix (- count 1))
          (cons (if (equal low k) (fn-cat-live-first g (+ 1 k) hi c) low)
                (if (equal high k) (fn-cat-live-last g (- k 1) c) high)))))

(local
 (defthm fn-ctg-corr-base-facts
   (implies (fn-cat$corr-base x c)
            (and (fn-cat-rowsp c)
                 (equal (nth 1 x) (len c))
                 (fn-cat-rows-corr (len c) c (nth 0 x))
                 (fn-cat-numbers-okp (nth 3 x) (nth 3 x) c)
                 (fn-cat-numbers-coverp c (nth 3 x))
                 (fn-cat-groups-okp (nth 4 x) (nth 4 x) c)
                 (fn-cat-groups-coverp c (nth 4 x))))
   :rule-classes :forward-chaining))

(local
 (defthm fn-ctg-corr-live-facts
   (implies (fn-cat$corr-live x c)
            (and (fn-cat-live-okp (nth 6 x) (nth 6 x) c)
                 (fn-cat-groups-coverp c (nth 6 x))
                 (equal (nth 7 x) (fn-cat-horizon-of c))))
   :rule-classes :forward-chaining))

(local
 (defthm fn-ctg-drop-entry-is-l
   (implies (and (fn-cat$corr-base fn-cat$c c) (fn-cat$corr-live fn-cat$c c))
            (equal (fn-cat$c-drop-entry g k fn-cat$c) (fn-ctg-drop-entry-l g k c)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-drop-entry fn-cat$c-groups-get)
                                   (fn-cat$corr-base fn-cat$corr-live fn-cat-live-count-from fn-cat-live-first fn-cat-live-last
                                    fn-cat$c-scan-up fn-cat$c-scan-down
                                    fn-cat$c-group-live-count fn-cat$c-group-live-low
                                    fn-cat$c-group-live-high fn-cat-live-okp
                                    fn-cat-groups-coverp fn-cat-groups-okp
                                    fn-cat-rows-corr
                                    fn-cat-numbers-okp fn-cat-numbers-coverp))))))

(defun fn-ctg-dhit (g pairs r row c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (or (and (consp (car pairs))
               (equal (car (car pairs)) g)
               (equal (fn-cat-number-seq g (cdr (car pairs)) c 0) r)
               (fn-cat-live-rowp g (cdr (car pairs)) row))
          (fn-ctg-dhit g (cdr pairs) r row c))
    nil))

(local
 (defun fn-ctg-dplan-ind (pairs r row tab fn-cat$c)
   (declare (xargs :stobjs fn-cat$c :verify-guards nil))
   (if (consp pairs)
       (let* ((p (car pairs)) (g (fn-cbor-ag-car p)) (k (fn-cbor-ag-cdr p)))
         (if (and (consp p)
                  (equal (fn-cat$c-numbers-get (cons g k) fn-cat$c) r)
                  (fn-cat-live-rowp g k row))
             (fn-ctg-dplan-ind (cdr pairs) r row
                               (cons (cons g (fn-cat$c-drop-entry g k fn-cat$c)) tab)
                               fn-cat$c)
           (fn-ctg-dplan-ind (cdr pairs) r row tab fn-cat$c)))
     (list tab r row))))

(local
 (defthm fn-ctg-numbers-lookup-pair
   (implies (and (fn-cat-numbers-okp tab tab c) (fn-cat-numbers-coverp c tab) (consp key))
            (equal (cdr (hons-assoc-equal key tab))
                   (fn-cat-number-seq (car key) (cdr key) c 0)))
   :hints (("Goal" :use ((:instance fn-ctg-numbers-lookup (g (car key)) (n (cdr key))))
            :in-theory (disable fn-ctg-numbers-lookup fn-cat-numbers-okp fn-cat-numbers-coverp
                                fn-cat-number-seq)))))

(local
 (defthm fn-ctg-dplan-lookup
   (implies (and (fn-cat$corr-base fn-cat$c c) (fn-cat$corr-live fn-cat$c c))
            (equal (hons-assoc-equal g (fn-ctg-lputs (fn-cat$c-drop-plan pairs r row fn-cat$c) tab))
                   (if (fn-ctg-dhit g pairs r row c)
                       (cons g (fn-ctg-drop-entry-l g (fn-held-number-in g row) c))
                     (hons-assoc-equal g tab))))
   :hints (("Goal" :induct (fn-ctg-dplan-ind pairs r row tab fn-cat$c)
            :in-theory (e/d (fn-cat$c-drop-plan fn-cat$c-numbers-get)
                            (fn-cat$c-drop-entry fn-ctg-drop-entry-l fn-cat-live-rowp
                             fn-held-number-in fn-cat$corr-base fn-cat$corr-live fn-cat-number-seq
                             fn-cat-numbers-okp fn-cat-numbers-coverp))))))

(local
 (defthm fn-ctg-dhit-gives
   (implies (fn-ctg-dhit g pairs r row c)
            (and (posp (fn-held-number-in g row))
                 (equal (fn-cat-number-seq g (fn-held-number-in g row) c 0) r)
                 (fn-cat-live-rowp g (fn-held-number-in g row) row)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ctg-dhit g pairs r row c)
            :in-theory (disable fn-cat-live-rowp fn-cat-number-seq fn-held-number-in)))))

(local
 (defthm fn-ctg-dhit-of-member
   (implies (and (member-equal p pairs) (consp p) (equal (car p) g)
                 (equal (fn-cat-number-seq g (cdr p) c 0) r)
                 (fn-cat-live-rowp g (cdr p) row))
            (fn-ctg-dhit g pairs r row c))
   :hints (("Goal" :in-theory (disable fn-cat-live-rowp fn-cat-number-seq)))))

(local
 (defthm fn-ctg-assoc-member
   (implies (fn-cat-assoc g ns)
            (and (member-equal (fn-cat-assoc g ns) ns)
                 (consp (fn-cat-assoc g ns))
                 (equal (car (fn-cat-assoc g ns)) g)))))

(local
 (defthm fn-ctg-dhit-is-kstar
   (implies (and (natp r) (< r (len c)))
            (iff (fn-ctg-dhit g (fn-held-numbers (nth r c)) r (nth r c) c)
                 (and (not (equal (fn-ctg-kstar g c r) 0))
                      (fn-cat-live-numberp g (fn-ctg-kstar g c r) c))))
   :hints (("Goal" :in-theory (e/d (fn-ctg-kstar fn-cat-live-numberp fn-held-number-in)
                                   (fn-cat-live-rowp fn-cat-number-seq fn-ctg-dhit))
            :use ((:instance fn-ctg-dhit-gives (pairs (fn-held-numbers (nth r c))) (row (nth r c)))
                  (:instance fn-ctg-dhit-of-member
                             (pairs (fn-held-numbers (nth r c))) (row (nth r c))
                             (p (fn-cat-assoc g (fn-held-numbers (nth r c))))))))))

(local
 (defthm fn-ctg-kstar-facts
   (implies (not (equal (fn-ctg-kstar g c r) 0))
            (and (posp (fn-ctg-kstar g c r))
                 (equal (fn-ctg-kstar g c r) (fn-held-number-in g (nth r c)))
                 (equal (fn-cat-number-seq g (fn-ctg-kstar g c r) c 0) r)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-ctg-kstar)))))

(local
 (defthm fn-ctg-kstar-below-high
   (implies (and (fn-cat-rowsp c) (fn-cat-live-numberp g k c))
            (<= k (fn-cat-group-high g c)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-cat-live-numberp) (fn-cat-live-rowp))))))

(local
 (defthm fn-ctg-live-range-nonempty
   (implies (and (natp j) (natp top) (<= j k) (<= k top) (fn-cat-live-numberp g k c))
            (and (< 0 (fn-cat-live-count-from g j top c))
                 (not (equal (fn-cat-live-first g j top c) 0))))
   :hints (("Goal" :induct (fn-cat-live-count-from g j top c)
            :in-theory (disable fn-cat-live-numberp)))))

(local
 (defthm fn-ctg-live-last-nonempty
   (implies (and (natp k) (natp j) (<= k j) (fn-cat-live-numberp g k c))
            (not (equal (fn-cat-live-last g j c) 0)))
   :hints (("Goal" :induct (fn-ctg-down-ind j)
            :in-theory (disable fn-cat-live-numberp)))))

(local
 (defthm fn-ctg-drop-entry-hit
   (implies (and (natp r) (< r (len c)) (fn-cat-rowsp c)
                 (null (fn-held-withdrawn (nth r c)))
                 (not (equal (fn-ctg-kstar g c r) 0))
                 (fn-cat-live-numberp g (fn-ctg-kstar g c r) c))
            (equal (fn-cat-live-entry g (fn-cat-mark-withdrawn r v by c))
                   (fn-ctg-drop-entry-l g (fn-held-number-in g (nth r c)) c)))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-entry)
                                   (fn-cat-live-numberp fn-ctg-kstar fn-cat-mark-withdrawn
                                    fn-ctg-mark-withdrawn-is-update fn-held-number-in
                                    fn-cat-live-count-from fn-cat-live-first fn-cat-live-last))
            :use ((:instance fn-ctg-kstar-facts)
                  (:instance fn-ctg-kstar-below-high (k (fn-ctg-kstar g c r)))
                  (:instance fn-ctg-live-range-nonempty (j 1) (k (fn-ctg-kstar g c r))
                             (top (fn-cat-group-high g c)))
                  (:instance fn-ctg-live-last-nonempty (k (fn-ctg-kstar g c r))
                             (j (fn-cat-group-high g c)))
                  (:instance fn-ctg-live-first-bounds (k 1) (top (fn-cat-group-high g c)))
                  (:instance fn-ctg-live-last-bounds (k (fn-cat-group-high g c))))))))

(local
 (defthm fn-ctg-drop-entry-miss
   (implies (and (natp r) (< r (len c)) (fn-cat-rowsp c)
                 (null (fn-held-withdrawn (nth r c)))
                 (not (and (not (equal (fn-ctg-kstar g c r) 0))
                           (fn-cat-live-numberp g (fn-ctg-kstar g c r) c))))
            (equal (fn-cat-live-entry g (fn-cat-mark-withdrawn r v by c))
                   (fn-cat-live-entry g c)))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-entry)
                                   (fn-cat-live-numberp fn-ctg-kstar fn-cat-mark-withdrawn
                                    fn-ctg-mark-withdrawn-is-update fn-held-number-in
                                    fn-cat-live-count-from fn-cat-live-first fn-cat-live-last))
            :use ((:instance fn-ctg-live-first-bounds (k 1) (top (fn-cat-group-high g c)))
                  (:instance fn-ctg-live-last-bounds (k (fn-cat-group-high g c))))))))

(local
 (defthm fn-ctg-withdraw-live-okp-old
   (implies (and (fn-cat$corr-base fn-cat$c c) (fn-cat$corr-live fn-cat$c c)
                 (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c)))
                 (fn-cat-live-okp keys (nth 6 fn-cat$c) c))
            (fn-cat-live-okp keys
                             (fn-ctg-lputs (fn-cat$c-drop-plan (fn-held-numbers (nth r c)) r (nth r c)
                                                               fn-cat$c)
                                           (nth 6 fn-cat$c))
                             (fn-cat-mark-withdrawn r (len c) by c)))
   :hints (("Goal" :induct (fn-cat-live-okp keys (nth 6 fn-cat$c) c)
            :in-theory (disable fn-cat-live-entry fn-ctg-drop-entry-l fn-cat$corr-base
                                fn-cat$corr-live fn-cat-mark-withdrawn fn-ctg-mark-withdrawn-is-update
                                fn-ctg-dhit fn-ctg-kstar fn-cat-live-numberp fn-held-number-in)))))

(local
 (defthm fn-ctg-withdraw-live-okp-new
   (implies (and (fn-cat$corr-base fn-cat$c c) (fn-cat$corr-live fn-cat$c c)
                 (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c)))
                 (subsetp-equal pairs (fn-held-numbers (nth r c)))
                 (fn-cat-live-okp tab2
                                  (fn-ctg-lputs (fn-cat$c-drop-plan (fn-held-numbers (nth r c)) r
                                                                    (nth r c) fn-cat$c)
                                                (nth 6 fn-cat$c))
                                  (fn-cat-mark-withdrawn r (len c) by c)))
            (fn-cat-live-okp (fn-ctg-lputs (fn-cat$c-drop-plan pairs r (nth r c) fn-cat$c) tab2)
                             (fn-ctg-lputs (fn-cat$c-drop-plan (fn-held-numbers (nth r c)) r
                                                               (nth r c) fn-cat$c)
                                           (nth 6 fn-cat$c))
                             (fn-cat-mark-withdrawn r (len c) by c)))
   :hints (("Goal" :induct (fn-ctg-dplan-ind pairs r (nth r c) tab2 fn-cat$c)
            :in-theory (e/d (fn-cat$c-drop-plan fn-cat$c-numbers-get)
                            (fn-cat-live-entry fn-ctg-drop-entry-l fn-cat$corr-base
                             fn-cat$corr-live fn-cat-mark-withdrawn fn-ctg-mark-withdrawn-is-update
                             fn-ctg-dhit fn-ctg-kstar fn-cat-live-numberp fn-held-number-in
                             fn-cat$c-drop-entry fn-cat-live-rowp fn-cat-number-seq
                             fn-cat-numbers-okp fn-cat-numbers-coverp)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-ctg-dhit-of-member
                                   (g (car (car pairs))) (p (car pairs))
                                   (pairs (fn-held-numbers (nth r c))) (row (nth r c)))))))))

(local
 (defthm fn-ctg-withdraw-live-fields
   (implies (fn-cat$cp fn-cat$c)
            (and (implies (fn-held-withdrawn (fn-cat$c-rowsi target fn-cat$c))
                          (equal (fn-cat$c-withdraw target by fn-cat$c) fn-cat$c))
                 (implies (not (fn-held-withdrawn (fn-cat$c-rowsi target fn-cat$c)))
                          (and (equal (nth 6 (fn-cat$c-withdraw target by fn-cat$c))
                                      (fn-ctg-lputs (fn-cat$c-drop-plan
                                                     (fn-held-numbers (fn-cat$c-rowsi target fn-cat$c))
                                                     target (fn-cat$c-rowsi target fn-cat$c) fn-cat$c)
                                                    (nth 6 fn-cat$c)))
                               (equal (nth 7 (fn-cat$c-withdraw target by fn-cat$c))
                                      (max (nth 7 fn-cat$c) (+ 1 (nth 1 fn-cat$c))))))))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-withdraw fn-cat$c-hz fn-cat$c-count)
                                   (fn-cat$c-drop-plan fn-cat$c-withdraw-base
                                    fn-cat$c-live-apply))))))

(local
 (defthm fn-ctg-rowsi-is-nth
   (implies (and (fn-cat$corr-base fn-cat$c c) (natp r) (< r (len c)))
            (equal (fn-cat$c-rowsi r fn-cat$c) (nth r c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-rowsi)))))

(local
 (defthm fn-ctg-withdrawn-of-with-withdrawn
   (equal (fn-held-withdrawn (fn-held-with-withdrawn h w)) w)
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn)))))

(local
 (defthm fn-ctg-withdraw-live-corr
   (implies (and (fn-cat$corr fn-cat$c c) (natp r) (< r (fn-cat$a-count c)) (natp by)
                 (fn-cat$ap c))
            (fn-cat$corr-live (fn-cat$c-withdraw r by fn-cat$c) (fn-cat$a-withdraw r by c)))
   :hints (("Goal" :do-not-induct t
            :cases ((fn-held-withdrawn (nth r c)))
            :in-theory (e/d (fn-cat$corr fn-ctg-mark-withdrawn-is-update)
                            (fn-cat$c-withdraw fn-cat$corr-base fn-cat$c-drop-plan
                             fn-cat-live-okp fn-cat-groups-coverp fn-ctg-withdraw-live-okp-new
                             fn-ctg-withdraw-live-okp-old fn-held-with-withdrawn))
            :use ((:instance fn-ctg-withdraw-live-okp-new
                             (pairs (fn-held-numbers (nth r c))) (tab2 (nth 6 fn-cat$c)))
                  (:instance fn-ctg-withdraw-live-okp-old (keys (nth 6 fn-cat$c)))
                  (:instance fn-ctg-groups-coverp-update-nth
                             (k r) (h (fn-held-with-withdrawn (nth r c) (cons (len c) by)))
                             (tab (nth 6 fn-cat$c))))))))

(local
 (defthm fn-ctg-cp-of-withdraw-base-corr
   (implies (and (fn-cat$corr-base x c) (natp target) (< target (len c)))
            (fn-cat$cp (fn-cat$c-withdraw-base target by x)))
   :hints (("Goal" :in-theory (disable fn-cat$c-withdraw-base)))))

(local
 (defthm fn-ctg-withdraw-base-when-withdrawn
   (implies (fn-held-withdrawn (fn-cat$c-rowsi target x))
            (equal (fn-cat$c-withdraw-base target by x) x))
   :hints (("Goal" :in-theory (enable fn-cat$c-withdraw-base)))))

(local
 (defthm fn-ctg-withdraw-keeps-corr-base
   (implies (and (fn-cat$corr-base fn-cat$c fn-cat) (natp target)
                 (< target (fn-cat$a-count fn-cat)) (natp by) (fn-cat$ap fn-cat))
            (fn-cat$corr-base (fn-cat$c-withdraw target by fn-cat$c)
                              (fn-cat$a-withdraw target by fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-withdraw)
                                   (fn-cat$corr-base fn-cat$c-withdraw-base fn-cat$c-live-apply
                                    fn-cat$c-drop-plan fn-cat$a-withdraw))
            :cases ((fn-held-withdrawn (fn-cat$c-rowsi target fn-cat$c)))
            :use ((:instance fn-ctg-withdraw-base-corr)
                  (:instance fn-ctg-corr-base-fields
                             (x (fn-cat$c-withdraw-base target by fn-cat$c))
                             (y (update-fn-cat$c-hz
                                 (max (fn-cat$c-hz fn-cat$c) (+ 1 (fn-cat$c-count fn-cat$c)))
                                 (fn-cat$c-live-apply
                                  (fn-cat$c-drop-plan
                                   (fn-held-numbers (fn-cat$c-rowsi target fn-cat$c))
                                   target (fn-cat$c-rowsi target fn-cat$c) fn-cat$c)
                                  (fn-cat$c-withdraw-base target by fn-cat$c))))
                             (a (fn-cat$a-withdraw target by fn-cat))))))))

(defthm fn-cat-withdraw{correspondence-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp target) (< target (fn-cat$a-count fn-cat))
                (natp by) (fn-cat$ap fn-cat))
           (fn-cat$corr (fn-cat$c-withdraw target by fn-cat$c)
                        (fn-cat$a-withdraw target by fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-cat$corr) (theory 'minimal-theory))
           :use ((:instance fn-ctg-withdraw-live-corr (r target) (c fn-cat))
                 (:instance fn-ctg-withdraw-keeps-corr-base)))))

; The re-decision keeps every key, the withdrawal and the Message-ID.
(local
 (defthm fn-ctg-withdrawn-of-with-context
   (equal (fn-held-withdrawn (fn-held-with-context h ctx)) (fn-held-withdrawn h))
   :hints (("Goal" :in-theory (enable fn-held-with-context)))))

(local
 (defthm fn-ctg-live-numberp-recontext
   (implies (and (natp s) (< s (len c)))
            (equal (fn-cat-live-numberp g k (update-nth s (fn-held-with-context (nth s c) ctx) c))
                   (fn-cat-live-numberp g k c)))
   :hints (("Goal" :in-theory (e/d (fn-cat-live-numberp fn-cat-live-rowp)
                                   (fn-held-with-context fn-cat-number-seq fn-held-number-in))
            :use ((:instance fn-ctg-number-seq-update-nth
                             (k s) (n k) (i 0) (h (fn-held-with-context (nth s c) ctx)))
                  (:instance fn-ctg-number-in-same-keys
                             (h1 (fn-held-with-context (nth s c) ctx)) (h2 (nth s c))))))))

(local
 (defthm fn-ctg-live-sums-recontext
   (implies (and (natp s) (< s (len c)))
            (and (equal (fn-cat-live-count-from g j top (update-nth s (fn-held-with-context (nth s c) ctx) c))
                        (fn-cat-live-count-from g j top c))
                 (equal (fn-cat-live-first g j top (update-nth s (fn-held-with-context (nth s c) ctx) c))
                        (fn-cat-live-first g j top c))))
   :hints (("Goal" :induct (fn-cat-live-count-from g j top c)
            :in-theory (disable fn-cat-live-numberp fn-held-with-context)))))

(local
 (defthm fn-ctg-live-last-recontext
   (implies (and (natp s) (< s (len c)))
            (equal (fn-cat-live-last g j (update-nth s (fn-held-with-context (nth s c) ctx) c))
                   (fn-cat-live-last g j c)))
   :hints (("Goal" :induct (fn-cat-live-last g j c)
            :in-theory (disable fn-cat-live-numberp fn-held-with-context)))))

(local
 (defthm fn-ctg-live-okp-recontext
   (implies (and (natp s) (< s (len c)))
            (equal (fn-cat-live-okp keys tab (update-nth s (fn-held-with-context (nth s c) ctx) c))
                   (fn-cat-live-okp keys tab c)))
   :hints (("Goal" :induct (fn-cat-live-okp keys tab c)
            :in-theory (e/d (fn-cat-live-entry)
                            (fn-cat-live-count-from fn-cat-live-first fn-cat-live-last
                             fn-held-with-context))))))

(local
 (defthm fn-ctg-horizon-recontext
   (implies (and (natp s) (< s (len c)))
            (equal (fn-cat-horizon-of (update-nth s (fn-held-with-context (nth s c) ctx) c))
                   (fn-cat-horizon-of c)))
   :hints (("Goal" :induct (update-nth s x c)
            :in-theory (e/d (update-nth) (fn-held-with-context))))))

(defthm fn-cat-redecide{correspondence-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-hc-p context) (fn-cat$ap fn-cat))
           (fn-cat$corr (fn-cat$c-redecide seq context fn-cat$c)
                        (fn-cat$a-redecide seq context fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat$corr fn-cat$corr-live)
                           (fn-cat$c-redecide fn-cat$corr-base fn-held-with-context
                            fn-cat-live-okp fn-cat-groups-coverp))
           :use ((:instance fn-ctg-redecide-base-corr)
                 (:instance fn-ctg-groups-coverp-update-nth
                            (k seq) (c fn-cat)
                            (h (fn-held-with-context (nth seq fn-cat) context))
                            (tab (nth 6 fn-cat$c)))))))

(local
 (defthm fn-ctg-corr-base-nil-of-resize-rows
   (implies (and (fn-cat$corr-base x nil) (fn-cat$cp x))
            (fn-cat$corr-base (resize-fn-cat$c-rows 0 x) nil))
   :hints (("Goal" :in-theory (e/d (fn-cat$corr-base resize-fn-cat$c-rows) (fn-cat$cp))
            :use ((:instance fn-ctg-cp-of-resize (n 0) (fn-cat$c x)))))))

(local
 (defthm fn-ctg-nth-of-resize-rows
   (and (equal (nth *fn-cat$c-lives-get* (resize-fn-cat$c-rows n x))
               (nth *fn-cat$c-lives-get* x))
        (equal (nth *fn-cat$c-hz* (resize-fn-cat$c-rows n x))
               (nth *fn-cat$c-hz* x)))
   :hints (("Goal" :in-theory (enable resize-fn-cat$c-rows)))))

(defthm fn-cat-clear{correspondence-bl}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (fn-cat$corr (fn-cat$c-clear fn-cat$c) (fn-cat$a-clear fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat$corr fn-cat$corr-live fn-cat$c-clear)
                           (fn-cat$corr-base fn-cat$c-clear-base))
           :use ((:instance fn-ctg-clear-base-corr)
                 (:instance fn-ctg-corr-base-fields
                            (x (fn-cat$c-clear-base fn-cat$c))
                            (y (fn-cat$c-lives-clear (fn-cat$c-clear-base fn-cat$c)))
                            (a (fn-cat$a-clear fn-cat)))
                 (:instance fn-ctg-corr-base-nil-of-resize-rows
                            (x (fn-cat$c-lives-clear (fn-cat$c-clear-base fn-cat$c))))
                 (:instance fn-ctg-corr-base-fields
                            (x (resize-fn-cat$c-rows
                                0 (fn-cat$c-lives-clear (fn-cat$c-clear-base fn-cat$c))))
                            (y (update-fn-cat$c-hz
                                0 (resize-fn-cat$c-rows
                                   0 (fn-cat$c-lives-clear (fn-cat$c-clear-base fn-cat$c)))))
                            (a (fn-cat$a-clear fn-cat)))))))

(defthm fn-cat-group-live-count{correspondence-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (fn-cat$ap fn-cat))
           (equal (fn-cat$c-group-live-count group fn-cat$c)
                  (fn-cat$a-group-live-count group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cat$corr) (fn-cat$corr-base fn-cat$c-group-live-count)))))

(defthm fn-cat-group-live-low{correspondence-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (fn-cat$ap fn-cat))
           (equal (fn-cat$c-group-live-low group fn-cat$c)
                  (fn-cat$a-group-live-low group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cat$corr) (fn-cat$corr-base fn-cat$c-group-live-low)))))

(defthm fn-cat-group-live-high{correspondence-bl}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (fn-cat$ap fn-cat))
           (equal (fn-cat$c-group-live-high group fn-cat$c)
                  (fn-cat$a-group-live-high group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cat$corr) (fn-cat$corr-base fn-cat$c-group-live-high)))))

(defthm fn-cat-horizon{correspondence-bl}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-horizon fn-cat$c) (fn-cat$a-horizon fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cat$corr fn-cat$c-horizon fn-cat$c-hz)
                                  (fn-cat$corr-base)))))

; -----------------------------------------------------------------------------
; The withdrawals by version (lane scale-latency, PKT-870).  A reader's view V
; sees a withdrawn row exactly when its withdrawal's version is at least V
; (fn-cat-visiblep), so what a view below the count sees differs from the
; top's live summary by the rows appended at or after V and the rows
; withdrawn at or after V.  The first are the rows V .. count-1; the second
; the catalog keeps here: per version W, the rows withdrawn at W, ascending
; (`fn-cat-withdrawn-at', one probe; books/served-catalog-view.lisp reads it
; for W from V to the horizon).  Maintained by commit (a row committed
; already withdrawn) and withdraw (at the count); redecide keeps every
; withdrawal; clear empties it.

; The rows of C from index I withdrawn at version W, ascending.
(defun fn-cat-withdrawn-at-from (w c i)
  (declare (xargs :guard (natp i)))
  (if (consp c)
      (let ((x (fn-held-withdrawn (car c)))
            (rest (fn-cat-withdrawn-at-from w (cdr c) (+ 1 i))))
        (if (and (consp x) (equal (car x) w)) (cons i rest) rest))
    nil))

(defun fn-cat$a-withdrawn-at (w fn-cat$a)
  (declare (xargs :guard t))
  (fn-cat-withdrawn-at-from w fn-cat$a 0))

; S into the ascending list L (executed as a loop: tools/depth_check.py).
(defun fn-cat-insert-asc-loop (s l acc)
  (declare (xargs :guard (true-listp acc)))
  (if (and (consp l) (< (nfix (car l)) (nfix s)))
      (fn-cat-insert-asc-loop s (cdr l) (cons (car l) acc))
    (revappend acc (cons s l))))

(defun fn-cat-insert-asc (s l)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (and (consp l) (< (nfix (car l)) (nfix s)))
                  (cons (car l) (fn-cat-insert-asc s (cdr l)))
                (cons s l))
       :exec (fn-cat-insert-asc-loop s l nil)))

(local
 (defthm fn-cat-insert-asc-loop-is-revappend
   (equal (fn-cat-insert-asc-loop s l acc)
          (revappend acc (fn-cat-insert-asc s l)))))

(verify-guards fn-cat-insert-asc)

(defun fn-cat$c-withdrawn-at (w fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (fn-cat$c-wbv-get w fn-cat$c))

(defun fn-cat$c-commit-w (h fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (fn-cat$c-wfp fn-cat$c)))
  (let* ((seq (fn-cat$c-count fn-cat$c))
         (x (fn-held-withdrawn h))
         (fn-cat$c (fn-cat$c-commit h fn-cat$c)))
    (if (consp x)
        (fn-cat$c-wbv-put (car x) (fn-cat-insert-asc seq (fn-cat$c-wbv-get (car x) fn-cat$c))
                          fn-cat$c)
      fn-cat$c)))

(defun fn-cat$c-withdraw-w (target by fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard (and (fn-cat$c-wfp fn-cat$c) (natp target) (natp by)
                              (< target (fn-cat$c-count fn-cat$c)))))
  (if (null (fn-held-withdrawn (fn-cat$c-rowsi target fn-cat$c)))
      (let* ((v (fn-cat$c-count fn-cat$c))
             (fn-cat$c (fn-cat$c-withdraw target by fn-cat$c)))
        (fn-cat$c-wbv-put v (fn-cat-insert-asc target (fn-cat$c-wbv-get v fn-cat$c)) fn-cat$c))
    fn-cat$c))

(defun fn-cat$c-clear-w (fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let ((fn-cat$c (fn-cat$c-clear fn-cat$c)))
    (fn-cat$c-wbv-clear fn-cat$c)))

; THE KEYED CLEAR: the clear, then the ring's key installed into the
; emptied table (the open's step before the load).
(defun fn-cat$c-clear-keyed (key fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))))
  (let ((fn-cat$c (fn-cat$c-clear-w fn-cat$c)))
    (fn-cat$c-index-set-key key fn-cat$c)))

; The rows below the count as a list, ascending (a tail-recursive loop):
; the logic function's argument when the executable must not trust its own
; table -- a key that is not the table's, UNREACHABLE IN COMPOSITION (the
; host passes the ring's key the open installed) and O(count) when reached.
(defun fn-cat$c-rows-list (i acc fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard (and (natp i) (<= i (fn-cat$c-rows-length fn-cat$c)) (true-listp acc))))
  (if (zp i)
      acc
    (fn-cat$c-rows-list (1- i) (cons (fn-cat$c-rowsi (1- i) fn-cat$c) acc) fn-cat$c)))

(local
 (defthm fn-ctw-rows-list-true-listp
   (implies (true-listp acc)
            (true-listp (fn-cat$c-rows-list i acc fn-cat$c)))
   :hints (("Goal" :induct (fn-cat$c-rows-list i acc fn-cat$c)))))

(defun fn-cat$c-rows-below-count (fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (fn-cat$c-rows-list (min (fn-cat$c-count fn-cat$c) (fn-cat$c-rows-length fn-cat$c)) nil fn-cat$c))

; THE SERVED REFUSAL, executable: the table's own answer when KEY is its key
; (two page reads, no conses beyond the tag), else the fold over the rows.
(defun fn-cat$c-msgid-saturatedp (key msgid fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))
                  :guard-hints (("Goal" :in-theory (disable fn-mlh-saturatedp fn-mlh-key-samep
                                                            fn-cat$c-rows-list fn-mlh-key-samep-is-equal)
                                 :do-not-induct t))))
  (let ((own (stobj-let ((fn-mlh (fn-cat$c-mpx fn-cat$c)))
                        (own)
                        (if (and (fn-mlh-wfp fn-mlh) (fn-mlh-key-samep key fn-mlh))
                            (if (fn-mlh-saturatedp (fn-mlh-tag msgid key) fn-mlh) :saturated :open)
                          :other-key)
                        own)))
    (if (eq own :other-key)
        (fn-mlh-build-saturatedp key msgid (fn-cat$c-rows-below-count fn-cat$c))
      (or (>= (+ 2 (fn-cat$c-count fn-cat$c)) *fn-mlh-tag-limit*)
          (eq own :saturated)))))

(defun fn-cat$c-index-health (key fn-cat$c)
  (declare (xargs :stobjs fn-cat$c
                  :guard (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))
                  :guard-hints (("Goal" :in-theory (disable fn-mlh-key-samep fn-cat$c-rows-list
                                                            fn-mlh-key-samep-is-equal)
                                 :do-not-induct t))))
  (let ((own (stobj-let ((fn-mlh (fn-cat$c-mpx fn-cat$c)))
                        (own)
                        (if (and (fn-mlh-wfp fn-mlh) (fn-mlh-key-samep key fn-mlh))
                            (list (fn-mlh-pages fn-mlh) (fn-mlh-count fn-mlh) (fn-mlh-stuck fn-mlh))
                          nil)
                        own)))
    (if (consp own)
        (list (car own) (cadr own) (fn-cat$c-unplaced fn-cat$c) (caddr own))
      (fn-mlh-build-health key (fn-cat$c-rows-below-count fn-cat$c)))))

; The table's conjunct: every bound version's entry is its rows; every
; withdrawn row's version is bound.
(defun fn-cat-wbv-okp (keys tab c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp keys)
      (and (equal (cdr (hons-assoc-equal (car (car keys)) tab))
                  (fn-cat-withdrawn-at-from (car (car keys)) c 0))
           (fn-cat-wbv-okp (cdr keys) tab c))
    t))

(defun fn-cat-wbv-coverp (c tab)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp c)
      (and (let ((x (fn-held-withdrawn (car c))))
             (or (not (consp x)) (consp (hons-assoc-equal (car x) tab))))
           (fn-cat-wbv-coverp (cdr c) tab))
    t))

(defun-nx fn-cat$corr-wbv (fn-cat$c fn-cat$a)
  (and (fn-cat-wbv-okp (nth 8 fn-cat$c) (nth 8 fn-cat$c) fn-cat$a)
       (fn-cat-wbv-coverp fn-cat$a (nth 8 fn-cat$c))))

(defun-nx fn-cat$corr-w (fn-cat$c fn-cat$a)
  (and (fn-cat$corr fn-cat$c fn-cat$a)
       (fn-cat$corr-wbv fn-cat$c fn-cat$a)))

; --- the rows' side

(local
 (defthm fn-ctw-at-from-of-append
   (implies (natp i)
            (equal (fn-cat-withdrawn-at-from w (append c (list h)) i)
                   (if (and (consp (fn-held-withdrawn h)) (equal (car (fn-held-withdrawn h)) w))
                       (append (fn-cat-withdrawn-at-from w c i) (list (+ i (len c))))
                     (fn-cat-withdrawn-at-from w c i))))
   :hints (("Goal" :induct (fn-cat-withdrawn-at-from w c i)))))

(defun fn-ctw-all-below (l s)
  (declare (xargs :guard t))
  (if (consp l)
      (and (< (nfix (car l)) (nfix s)) (fn-ctw-all-below (cdr l) s))
    t))

(defun fn-ctw-all-above (l s)
  (declare (xargs :guard t))
  (if (consp l)
      (and (< (nfix s) (nfix (car l))) (fn-ctw-all-above (cdr l) s))
    t))

(local
 (defthm fn-ctw-at-from-below
   (implies (and (natp i) (natp s) (<= (+ i (len c)) s))
            (fn-ctw-all-below (fn-cat-withdrawn-at-from w c i) s))
   :hints (("Goal" :induct (fn-cat-withdrawn-at-from w c i)))))

(local
 (defthm fn-ctw-at-from-above
   (implies (and (natp i) (natp s) (< s i))
            (fn-ctw-all-above (fn-cat-withdrawn-at-from w c i) s))
   :hints (("Goal" :induct (fn-cat-withdrawn-at-from w c i)))))

(local
 (defthm fn-ctw-insert-past-all
   (implies (and (fn-ctw-all-below l s) (true-listp l))
            (equal (fn-cat-insert-asc s l) (append l (list s))))))

(local
 (defthm fn-ctw-at-from-true-listp
   (true-listp (fn-cat-withdrawn-at-from w c i))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm fn-ctw-insert-before-all
   (implies (and (fn-ctw-all-above l s) (natp s))
            (equal (fn-cat-insert-asc s l) (cons s l)))
   :hints (("Goal" :expand ((fn-cat-insert-asc s l))))))

(local
 (defun fn-ctw-ind (c k i)
   (if (consp c)
       (fn-ctw-ind (cdr c) (- k 1) (+ 1 i))
     (list k i))))

; A withdrawal of row K (not withdrawn before) at version V.
(local
 (defthm fn-ctw-at-from-of-withdraw
   (implies (and (natp k) (< k (len c)) (natp i) (null (fn-held-withdrawn (nth k c))))
            (equal (fn-cat-withdrawn-at-from
                    w (update-nth k (fn-held-with-withdrawn (nth k c) (cons v by)) c) i)
                   (if (equal w v)
                       (fn-cat-insert-asc (+ i k) (fn-cat-withdrawn-at-from w c i))
                     (fn-cat-withdrawn-at-from w c i))))
   :hints (("Goal" :induct (fn-ctw-ind c k i)
            :expand ((fn-cat-withdrawn-at-from
                      w (update-nth k (fn-held-with-withdrawn (nth k c) (cons v by)) c) i)
                     (fn-cat-withdrawn-at-from w c i)
                     (update-nth k (fn-held-with-withdrawn (nth k c) (cons v by)) c))
            :in-theory (e/d (fn-ctg-withdrawn-of-with-withdrawn) (fn-held-with-withdrawn))))))

(local
 (defthm fn-ctw-at-from-of-recontext
   (implies (and (natp k) (< k (len c)))
            (equal (fn-cat-withdrawn-at-from
                    w (update-nth k (fn-held-with-context (nth k c) ctx) c) i)
                   (fn-cat-withdrawn-at-from w c i)))
   :hints (("Goal" :induct (fn-ctw-ind c k i)
            :expand ((update-nth k (fn-held-with-context (nth k c) ctx) c))
            :in-theory (e/d (fn-ctg-withdrawn-of-with-context) (fn-held-with-context))))))

; --- the table's side

(local
 (defthm fn-ctw-okp-lookup
   (implies (and (fn-cat-wbv-okp keys tab c) (consp (hons-assoc-equal k keys)))
            (equal (cdr (hons-assoc-equal k tab)) (fn-cat-withdrawn-at-from k c 0)))
   :hints (("Goal" :induct (fn-cat-wbv-okp keys tab c)))))

(local
 (defthm fn-ctw-coverp-unbound
   (implies (and (fn-cat-wbv-coverp c tab) (not (consp (hons-assoc-equal k tab))))
            (equal (fn-cat-withdrawn-at-from k c i) nil))
   :hints (("Goal" :induct (fn-cat-withdrawn-at-from k c i)))))

(local
 (defthm fn-ctw-lookup
   (implies (and (fn-cat-wbv-okp tab tab c) (fn-cat-wbv-coverp c tab))
            (equal (cdr (hons-assoc-equal k tab)) (fn-cat-withdrawn-at-from k c 0)))
   :hints (("Goal" :cases ((consp (hons-assoc-equal k tab)))))))

; Every version other than K reads the same in C and C2.
(defun-nx fn-ctw-agree (keys k c c2)
  (if (consp keys)
      (and (or (equal (car (car keys)) k)
               (equal (fn-cat-withdrawn-at-from (car (car keys)) c 0)
                      (fn-cat-withdrawn-at-from (car (car keys)) c2 0)))
           (fn-ctw-agree (cdr keys) k c c2))
    t))

(local
 (defthm fn-ctw-okp-put
   (implies (and (fn-cat-wbv-okp keys tab c) (fn-ctw-agree keys k c c2)
                 (equal val (fn-cat-withdrawn-at-from k c2 0)))
            (fn-cat-wbv-okp keys (cons (cons k val) tab) c2))
   :hints (("Goal" :induct (fn-cat-wbv-okp keys tab c)))))

(local
 (defthm fn-ctw-okp-put-top
   (implies (and (fn-cat-wbv-okp tab tab c) (fn-ctw-agree tab k c c2)
                 (equal val (fn-cat-withdrawn-at-from k c2 0)))
            (fn-cat-wbv-okp (cons (cons k val) tab) (cons (cons k val) tab) c2))
   :hints (("Goal" :expand ((fn-cat-wbv-okp (cons (cons k val) tab) (cons (cons k val) tab) c2))))))

(local
 (defthm fn-ctw-agree-of-append-any
   (fn-ctw-agree keys (car (fn-held-withdrawn h)) c (append c (list h)))
   :hints (("Goal" :induct (fn-ctw-agree keys (car (fn-held-withdrawn h)) c (append c (list h)))
            :in-theory (disable fn-cat-withdrawn-at-from)))))

(local
 (defthm fn-ctw-agree-of-withdraw
   (implies (and (natp r) (< r (len c)) (null (fn-held-withdrawn (nth r c))))
            (fn-ctw-agree keys v c
                          (update-nth r (fn-held-with-withdrawn (nth r c) (cons v by)) c)))
   :hints (("Goal" :induct (fn-ctw-agree keys v c c)
            :in-theory (disable fn-cat-withdrawn-at-from fn-held-with-withdrawn)))))

(local
 (defthm fn-ctw-coverp-extend
   (implies (fn-cat-wbv-coverp c tab)
            (fn-cat-wbv-coverp c (cons pair tab)))
   :hints (("Goal" :induct (fn-cat-wbv-coverp c tab)))))

(local
 (defthm fn-ctw-coverp-append
   (implies (and (fn-cat-wbv-coverp c tab)
                 (or (not (consp (fn-held-withdrawn h)))
                     (consp (hons-assoc-equal (car (fn-held-withdrawn h)) tab))))
            (fn-cat-wbv-coverp (append c (list h)) tab))
   :hints (("Goal" :induct (fn-cat-wbv-coverp c tab)))))

(local
 (defthm fn-ctw-coverp-withdraw
   (implies (and (fn-cat-wbv-coverp c tab) (natp r) (< r (len c))
                 (consp (hons-assoc-equal v tab)))
            (fn-cat-wbv-coverp
             (update-nth r (fn-held-with-withdrawn (nth r c) (cons v by)) c) tab))
   :hints (("Goal" :induct (fn-ctw-ind c r 0)
            :expand ((update-nth r (fn-held-with-withdrawn (nth r c) (cons v by)) c))
            :in-theory (e/d (fn-ctg-withdrawn-of-with-withdrawn) (fn-held-with-withdrawn))))))

(local
 (defthm fn-ctw-coverp-recontext
   (implies (and (fn-cat-wbv-coverp c tab) (natp r) (< r (len c)))
            (fn-cat-wbv-coverp
             (update-nth r (fn-held-with-context (nth r c) ctx) c) tab))
   :hints (("Goal" :induct (fn-ctw-ind c r 0)
            :expand ((update-nth r (fn-held-with-context (nth r c) ctx) c))
            :in-theory (e/d (fn-ctg-withdrawn-of-with-context) (fn-held-with-context))))))

(local
 (defthm fn-ctw-okp-recontext
   (implies (and (fn-cat-wbv-okp keys tab c) (natp r) (< r (len c)))
            (fn-cat-wbv-okp keys tab (update-nth r (fn-held-with-context (nth r c) ctx) c)))
   :hints (("Goal" :induct (fn-cat-wbv-okp keys tab c)
            :in-theory (disable fn-cat-withdrawn-at-from fn-held-with-context)))))

; --- the concrete side: the old writers never touch the new field, and the
; new field's writes never touch the old fields.

(local
 (defthm fn-ctw-nth-of-wbv-writes
   (implies (not (equal n 8))
            (and (equal (nth n (fn-cat$c-wbv-put k v x)) (nth n x))
                 (equal (nth n (fn-cat$c-wbv-clear x)) (nth n x))))
   :hints (("Goal" :in-theory (enable fn-cat$c-wbv-put fn-cat$c-wbv-clear)))))

(local
 (defthm fn-ctw-wbv-fields
   (and (equal (nth 8 (fn-cat$c-wbv-put k v x)) (cons (cons k v) (nth 8 x)))
        (equal (nth 8 (fn-cat$c-wbv-clear x)) nil)
        (equal (fn-cat$c-wbv-get k x) (cdr (hons-assoc-equal k (nth 8 x)))))
   :hints (("Goal" :in-theory (enable fn-cat$c-wbv-put fn-cat$c-wbv-clear fn-cat$c-wbv-get)))))

(local
 (defthm fn-ctw-cp-of-wbv-writes
   (implies (fn-cat$cp x)
            (and (fn-cat$cp (fn-cat$c-wbv-put k v x))
                 (fn-cat$cp (fn-cat$c-wbv-clear x))))
   :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-wbv-put fn-cat$c-wbv-clear)))))

(local
 (defthm fn-ctw-corr-bl-of-wbv-writes
   (implies (fn-cat$corr x a)
            (and (fn-cat$corr (fn-cat$c-wbv-put k v x) a)
                 (fn-cat$corr (fn-cat$c-wbv-clear x) a)))
   :hints (("Goal" :in-theory (e/d (fn-cat$corr fn-cat$corr-base fn-cat$corr-live)
                                   (fn-cat$c-wbv-put fn-cat$c-wbv-clear))))))

(local
 (defthm fn-ctw-nth8-of-old-writes
   (and (equal (nth 8 (update-fn-cat$c-rowsi i v x)) (nth 8 x))
        (equal (nth 8 (resize-fn-cat$c-rows n x)) (nth 8 x))
        (equal (nth 8 (update-fn-cat$c-count n x)) (nth 8 x))
        (equal (nth 8 (update-fn-cat$c-octets n x)) (nth 8 x))
        (equal (nth 8 (update-fn-cat$c-hz n x)) (nth 8 x))
        (equal (nth 8 (update-fn-cat$c-mpx t2 x)) (nth 8 x))
        (equal (nth 8 (update-fn-cat$c-unplaced n x)) (nth 8 x))
        (equal (nth 8 (fn-cat$c-numbers-put k v x)) (nth 8 x))
        (equal (nth 8 (fn-cat$c-groups-put k v x)) (nth 8 x))
        (equal (nth 8 (fn-cat$c-lives-put k v x)) (nth 8 x))
        (equal (nth 8 (fn-cat$c-numbers-clear x)) (nth 8 x))
        (equal (nth 8 (fn-cat$c-groups-clear x)) (nth 8 x))
        (equal (nth 8 (fn-cat$c-lives-clear x)) (nth 8 x)))
   :hints (("Goal" :in-theory (enable update-fn-cat$c-rowsi resize-fn-cat$c-rows
                                      update-fn-cat$c-count update-fn-cat$c-octets
                                      update-fn-cat$c-hz update-fn-cat$c-mpx
                                      update-fn-cat$c-unplaced
                                      fn-cat$c-numbers-put fn-cat$c-groups-put
                                      fn-cat$c-lives-put
                                      fn-cat$c-numbers-clear fn-cat$c-groups-clear
                                      fn-cat$c-lives-clear update-nth-array)))))

(local
 (defthm fn-ctw-nth8-of-apply-plan
   (equal (nth 8 (fn-cat$c-apply-plan plan seq x)) (nth 8 x))
   :hints (("Goal" :in-theory (enable fn-cat$c-apply-plan)))))

(local
 (defthm fn-ctw-nth8-of-live-apply
   (equal (nth 8 (fn-cat$c-live-apply plan x)) (nth 8 x))
   :hints (("Goal" :in-theory (enable fn-cat$c-live-apply)))))

(local
 (defthm fn-ctw-nth8-of-writers
   (and (equal (nth 8 (fn-cat$c-commit h x)) (nth 8 x))
        (equal (nth 8 (fn-cat$c-withdraw r by x)) (nth 8 x))
        (equal (nth 8 (fn-cat$c-redecide r ctx x)) (nth 8 x)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-commit fn-cat$c-commit-base fn-cat$c-withdraw
                                    fn-cat$c-withdraw-base fn-cat$c-redecide)
                                   (fn-cat$c-live-plan fn-cat$c-drop-plan fn-cat$c-plan
                                    fn-cat$c-apply-plan fn-cat$c-live-apply))))))

(local
 (defthm fn-ctw-okp-of-append-unwithdrawn
   (implies (and (fn-cat-wbv-okp keys tab c) (not (consp (fn-held-withdrawn h))))
            (fn-cat-wbv-okp keys tab (append c (list h))))
   :hints (("Goal" :induct (fn-cat-wbv-okp keys tab c)))))

(local
 (defthm fn-ctw-count-is-len
   (implies (fn-cat$corr x a)
            (equal (fn-cat$c-count x) (len a)))
   :hints (("Goal" :in-theory (enable fn-cat$corr fn-cat$corr-base fn-cat$c-count)))))

(local
 (defthm fn-ctw-rowsi-is-nth
   (implies (and (fn-cat$corr x a) (fn-cat$ap a) (natp r) (< r (len a)))
            (equal (fn-cat$c-rowsi r x) (nth r a)))
   :hints (("Goal" :use ((:instance fn-cat-at{correspondence-bl}
                                    (fn-cat$c x) (fn-cat a) (seq r)))
            :in-theory (e/d (fn-cat$c-at) (fn-cat$corr))))))

(local
 (defthm fn-ctw-corr-wbv-parts
   (implies (fn-cat$corr-wbv x a)
            (and (fn-cat-wbv-okp (nth 8 x) (nth 8 x) a)
                 (fn-cat-wbv-coverp a (nth 8 x))))
   :hints (("Goal" :in-theory (enable fn-cat$corr-wbv)))))

(local (in-theory (disable fn-cat-withdrawn-at-from fn-cat-insert-asc fn-cat-wbv-okp
                           fn-cat-wbv-coverp fn-ctw-agree)))

; --- the obligations over the extended relation


(defthm create-fn-cat{correspondence}
  (fn-cat$corr-w (create-fn-cat$c) (create-fn-cat$a))
  :rule-classes nil
  :hints (("Goal" :use create-fn-cat{correspondence-bl}
           :in-theory (enable fn-cat$corr-w fn-cat$corr-wbv create-fn-cat$c create-fn-cat$a
                              fn-cat-wbv-okp fn-cat-wbv-coverp))))

(defthm fn-cat-withdrawn-at{correspondence}
  (implies (fn-cat$corr-w fn-cat$c fn-cat)
           (equal (fn-cat$c-withdrawn-at w fn-cat$c) (fn-cat$a-withdrawn-at w fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cat$corr-w fn-cat$c-withdrawn-at fn-cat$a-withdrawn-at)
                                  (fn-cat$corr fn-cat$corr-wbv))
           :use ((:instance fn-ctw-corr-wbv-parts (x fn-cat$c) (a fn-cat))
                 (:instance fn-ctw-lookup (k w) (tab (nth 8 fn-cat$c)) (c fn-cat))))))

(defthm fn-cat-commit{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (fn-held-p h) (fn-cat$ap fn-cat))
           (fn-cat$corr-w (fn-cat$c-commit-w h fn-cat$c) (fn-cat$a-commit h fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat$corr-w fn-cat$corr-wbv fn-cat$c-commit-w fn-cat$a-commit
                            fn-ctg-withdrawn-of-assign)
                           (fn-cat$corr fn-cat$c-commit fn-cat-assign fn-cat$c-wbv-put
                            fn-cat$c-wbv-get))
           :use ((:instance fn-cat-commit{correspondence-bl})
                 (:instance fn-ctw-corr-wbv-parts (x fn-cat$c) (a fn-cat))
                 (:instance fn-ctw-lookup (k (car (fn-held-withdrawn h)))
                            (tab (nth 8 fn-cat$c)) (c fn-cat))
                 (:instance fn-ctw-at-from-below (w (car (fn-held-withdrawn h))) (c fn-cat)
                            (i 0) (s (len fn-cat)))
                 (:instance fn-ctw-count-is-len (x fn-cat$c) (a fn-cat))
                 (:instance fn-ctw-agree-of-append-any (keys (nth 8 fn-cat$c))
                            (h (fn-cat-assign h fn-cat)) (c fn-cat))
                 (:instance fn-ctw-okp-put-top (tab (nth 8 fn-cat$c)) (c fn-cat)
                            (k (car (fn-held-withdrawn h)))
                            (c2 (append fn-cat (list (fn-cat-assign h fn-cat))))
                            (val (append (fn-cat-withdrawn-at-from (car (fn-held-withdrawn h))
                                                                   fn-cat 0)
                                         (list (len fn-cat)))))))))

(defthm fn-cat-withdraw{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (natp target) (< target (fn-cat$a-count fn-cat))
                (natp by) (fn-cat$ap fn-cat))
           (fn-cat$corr-w (fn-cat$c-withdraw-w target by fn-cat$c)
                        (fn-cat$a-withdraw target by fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat$corr-w fn-cat$corr-wbv fn-cat$c-withdraw-w fn-cat$a-withdraw
                            fn-cat-mark-withdrawn)
                           (fn-cat$corr fn-cat$c-withdraw fn-held-with-withdrawn
                            fn-cat$c-wbv-put fn-cat$c-wbv-get))
           :use ((:instance fn-cat-withdraw{correspondence-bl})
                 (:instance fn-ctw-corr-wbv-parts (x fn-cat$c) (a fn-cat))
                 (:instance fn-ctw-lookup (k (len fn-cat)) (tab (nth 8 fn-cat$c)) (c fn-cat))
                 (:instance fn-ctw-rowsi-is-nth (x fn-cat$c) (a fn-cat) (r target))
                 (:instance fn-ctw-count-is-len (x fn-cat$c) (a fn-cat))))))

(defthm fn-cat-redecide{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-hc-p context) (fn-cat$ap fn-cat))
           (fn-cat$corr-w (fn-cat$c-redecide seq context fn-cat$c)
                        (fn-cat$a-redecide seq context fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat$corr-w fn-cat$corr-wbv fn-cat$a-redecide)
                           (fn-cat$corr fn-cat$c-redecide fn-held-with-context))
           :use ((:instance fn-cat-redecide{correspondence-bl})
                 (:instance fn-ctw-corr-wbv-parts (x fn-cat$c) (a fn-cat))))))

(defthm fn-cat-clear{correspondence}
  (implies (fn-cat$corr-w fn-cat$c fn-cat)
           (fn-cat$corr-w (fn-cat$c-clear-w fn-cat$c) (fn-cat$a-clear fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat$corr-w fn-cat$corr-wbv fn-cat$c-clear-w fn-cat$a-clear
                            fn-cat-wbv-okp fn-cat-wbv-coverp)
                           (fn-cat$corr fn-cat$c-clear fn-cat$c-wbv-clear))
           :use ((:instance fn-cat-clear{correspondence-bl})))))

; The index's fields, off the full relation (the base clauses lifted).
(local
 (defthm fn-ctw-index-of-corr-w
   (implies (fn-cat$corr-w fn-cat$c fn-cat)
            (and (fn-cat$cp fn-cat$c)
                 (fn-cat-rowsp fn-cat)
                 (equal (nth 1 fn-cat$c) (len fn-cat))
                 (<= (nth 1 fn-cat$c) (len (nth 0 fn-cat$c)))
                 (fn-cat-rows-corr (len fn-cat) fn-cat (nth 0 fn-cat$c))
                 (equal (nth 2 fn-cat$c) (fn-mlh-build (fn-cat-key-of fn-cat$c) fn-cat))
                 (equal (nth 9 fn-cat$c) (fn-mlh-build-unplaced (fn-cat-key-of fn-cat$c) fn-cat))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-cat$corr-w fn-cat$corr fn-cat$corr-base)
                                              (theory 'minimal-theory))))))

; The rows below the count, as a list, are the rows.
(local
 (defthm fn-ctw-rows-list-is-prefix
   (implies (and (fn-cat-rows-corr n c (nth 0 fn-cat$c)) (natp i) (<= i (nfix n)) (true-listp c)
                 (<= (nfix n) (len c)))
            (equal (fn-cat$c-rows-list i acc fn-cat$c)
                   (append (fn-mpxt-prefix i c) acc)))
   :hints (("Goal" :induct (fn-cat$c-rows-list i acc fn-cat$c)
            :in-theory (e/d (fn-cat$c-rows-list fn-cat$c-rowsi) (fn-cat-rows-corr fn-ctg-rows-corr-nth)))
           ("Subgoal *1/2" :use ((:instance fn-ctg-rows-corr-nth (i (+ -1 i)) (rows (nth 0 fn-cat$c)))
                                 (:instance fn-mpxt-prefix-next (i (+ -1 i)) (rows c)))))))

(local
 (defthm fn-ctw-append-nil
   (implies (true-listp a) (equal (append a nil) a))))

(local
 (defthm fn-ctw-rows-below-count-is-the-rows
   (implies (fn-cat$corr-w fn-cat$c fn-cat)
            (equal (fn-cat$c-rows-below-count fn-cat$c) fn-cat))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-rows-below-count fn-cat$c-count fn-cat$c-rows-length)
                                   (fn-cat$c-rows-list fn-cat-rows-corr fn-ctw-rows-list-is-prefix
                                    fn-mpxt-prefix-all))
            :use ((:instance fn-ctw-index-of-corr-w)
                  (:instance fn-ctw-rows-list-is-prefix (n (len fn-cat)) (c fn-cat) (i (len fn-cat)) (acc nil))
                  (:instance fn-mpxt-prefix-all (rows fn-cat)))))))

; A 32-octet key that is the table's is the fold's key.
(local
 (defthm fn-ctw-same-key-is-the-fold-key
   (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (true-listp key)
                 (equal key (fn-mlh-key-octets (nth 2 fn-cat$c))))
            (equal (fn-cat-key-of fn-cat$c) key))
   :hints (("Goal" :in-theory (enable fn-cat-key-of)))))

(local
 (defthm fn-ctw-keyp-true-listp
   (implies (fn-mpxt-keyp l) (true-listp l))
   :hints (("Goal" :in-theory (enable fn-mpxt-keyp)))))

(defthm fn-cat-msgid-saturatedp{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat)
                (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*) (fn-cat$ap fn-cat))
           (equal (fn-cat$c-msgid-saturatedp key msgid fn-cat$c)
                  (fn-cat$a-msgid-saturatedp key msgid fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat$c-msgid-saturatedp fn-cat$a-msgid-saturatedp fn-cat$c-mpx
                            fn-cat$c-count fn-cat-key-of)
                           (fn-mlh-saturatedp fn-mlh-build-nil fn-mlh-set-key-is-a-list fn-mlh-set-key
                            fn-cat$c-rows-below-count fn-cat-rows-corr
                            fn-cat$corr-w fn-cat$corr fn-cat$corr-base fn-cat$corr-live fn-cat$corr-wbv
                            fn-ctw-rows-below-count-is-the-rows))
           :use ((:instance fn-ctw-index-of-corr-w)
                 (:instance fn-ctw-rows-below-count-is-the-rows)))))

(defthm fn-cat-msgid-saturatedp{guard-thm}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat)
                (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*) (fn-cat$ap fn-cat))
           (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*)))
  :rule-classes nil)

(defthm fn-cat-index-health{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat)
                (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*) (fn-cat$ap fn-cat))
           (equal (fn-cat$c-index-health key fn-cat$c)
                  (fn-cat$a-index-health key fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat$c-index-health fn-cat$a-index-health fn-cat$c-mpx
                            fn-cat$c-unplaced fn-cat-key-of)
                           (fn-mlh-build-nil fn-mlh-set-key-is-a-list fn-mlh-set-key
                            fn-cat$c-rows-below-count fn-cat-rows-corr
                            fn-cat$corr-w fn-cat$corr fn-cat$corr-base fn-cat$corr-live fn-cat$corr-wbv
                            fn-ctw-rows-below-count-is-the-rows))
           :use ((:instance fn-ctw-index-of-corr-w)
                 (:instance fn-ctw-rows-below-count-is-the-rows)))))

(defthm fn-cat-index-health{guard-thm}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat)
                (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*) (fn-cat$ap fn-cat))
           (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*)))
  :rule-classes nil)

; The keyed clear: the clear's relation with the rows nil, then the key
; installed into the emptied tables (fn-mlh-key-octets-of-set-key,
; fn-mlh-build-nil, fn-mlh-set-key-is-a-list).
(local
 (defthm fn-ctw-index-set-key-fields
   (implies (fn-cat$cp fn-cat$c)
            (and (equal (nth 2 (fn-cat$c-index-set-key key fn-cat$c)) (fn-mlh-set-key key (nth 2 fn-cat$c)))
                 (equal (nth 9 (fn-cat$c-index-set-key key fn-cat$c)) 0)
                 (implies (and (natp k) (not (equal k 2)) (not (equal k 9)))
                          (equal (nth k (fn-cat$c-index-set-key key fn-cat$c)) (nth k fn-cat$c)))
                 (fn-cat$cp (fn-cat$c-index-set-key key fn-cat$c))))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-index-set-key fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced fn-cat$cp fn-cat$c-unplacedp)
                                   (fn-mlh-set-key fn-mlh-set-key-is-a-list))))))

(local
 (defthm fn-ctw-index-set-key-frame
   (implies (and (natp k) (not (equal k 2)) (not (equal k 9)))
            (equal (nth k (fn-cat$c-index-set-key key fn-cat$c)) (nth k fn-cat$c)))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-index-set-key fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced)
                                   (fn-mlh-set-key fn-mlh-set-key-is-a-list))))))

(local
 (defthm fn-ctw-index-set-key-fields-u
   (and (equal (nth 2 (fn-cat$c-index-set-key key fn-cat$c)) (fn-mlh-set-key key (nth 2 fn-cat$c)))
        (equal (nth 9 (fn-cat$c-index-set-key key fn-cat$c)) 0))
   :hints (("Goal" :in-theory (e/d (fn-cat$c-index-set-key fn-cat$c-mpx update-fn-cat$c-mpx
                                    fn-cat$c-unplaced update-fn-cat$c-unplaced)
                                   (fn-mlh-set-key fn-mlh-set-key-is-a-list))))))

(local
 (defthm fn-ctw-corr-w-of-index-set-key
   (implies (and (fn-cat$corr-w fn-cat$c nil) (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))
            (fn-cat$corr-w (fn-cat$c-index-set-key key fn-cat$c) nil))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cat$corr-w fn-cat$corr fn-cat$corr-base fn-cat$corr-live fn-cat$corr-wbv
                             fn-cat-key-of fn-cat-live-okp fn-cat-groups-coverp fn-cat-wbv-okp fn-cat-wbv-coverp
                             fn-cat-numbers-okp fn-cat-numbers-coverp fn-cat-groups-okp fn-cat-rows-corr)
                            (fn-cat$c-index-set-key fn-mlh-set-key fn-mlh-clear-is-build-nil
                             fn-mlh-create-is-build-nil fn-mlh-clear create-fn-mlh
                             fn-mlh-set-key-is-a-list))
            :use ((:instance fn-mlh-set-key-canonical (fn-mlh (nth *fn-cat$c-mpx* fn-cat$c))))))))

(defthm fn-cat-clear-keyed{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat)
                (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))
           (fn-cat$corr-w (fn-cat$c-clear-keyed key fn-cat$c) (fn-cat$a-clear-keyed key fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat$c-clear-keyed fn-cat$a-clear-keyed)
                           (fn-cat$c-clear-w fn-cat$c-index-set-key fn-cat$corr-w))
           :use ((:instance fn-cat-clear{correspondence})))))

(defthm fn-cat-clear-keyed{guard-thm}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat)
                (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))
           (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*)))
  :rule-classes nil)

(defthm fn-cat-clear-keyed{preserved}
  (implies (and (fn-cat$ap fn-cat) (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))
           (fn-cat$ap (fn-cat$a-clear-keyed key fn-cat)))
  :rule-classes nil)

(defthm fn-cat-count{correspondence}
  (implies (fn-cat$corr-w fn-cat$c fn-cat)
           (equal (fn-cat$c-count fn-cat$c) (fn-cat$a-count fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-count{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-at{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-cat$ap fn-cat))
           (equal (fn-cat$c-at seq fn-cat$c) (fn-cat$a-at seq fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-at{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-at{guard-thm}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-cat$ap fn-cat))
           (and (fn-cat$c-wfp fn-cat$c) (natp seq) (< seq (fn-cat$c-count fn-cat$c))))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-at{guard-thm-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-msgid-seqs{correspondence}
  (implies (fn-cat$corr-w fn-cat$c fn-cat)
           (equal (fn-cat$c-msgid-seqs msgid fn-cat$c) (fn-cat$a-msgid-seqs msgid fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-msgid-seqs{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-group-number{correspondence}
  (implies (fn-cat$corr-w fn-cat$c fn-cat)
           (equal (fn-cat$c-group-number group n fn-cat$c)
                  (fn-cat$a-group-number group n fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-group-number{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-group-next{correspondence}
  (implies (fn-cat$corr-w fn-cat$c fn-cat)
           (equal (fn-cat$c-group-next group fn-cat$c) (fn-cat$a-group-next group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-group-next{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-group-count{correspondence}
  (implies (fn-cat$corr-w fn-cat$c fn-cat)
           (equal (fn-cat$c-group-count group fn-cat$c) (fn-cat$a-group-count group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-group-count{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-total-octets{correspondence}
  (implies (fn-cat$corr-w fn-cat$c fn-cat)
           (equal (fn-cat$c-total-octets fn-cat$c) (fn-cat$a-total-octets fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-total-octets{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-visible-at{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat)) (natp v)
                (fn-cat$ap fn-cat))
           (equal (fn-cat$c-visible-at seq v fn-cat$c) (fn-cat$a-visible-at seq v fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-visible-at{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-visible-at{guard-thm}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat)) (natp v)
                (fn-cat$ap fn-cat))
           (and (fn-cat$c-wfp fn-cat$c) (natp seq) (natp v)
                (< seq (fn-cat$c-count fn-cat$c))
                (fn-held-withdrawnp (fn-held-withdrawn (fn-cat$c-rowsi seq fn-cat$c)))))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-visible-at{guard-thm-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-commit{guard-thm}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (fn-held-p h) (fn-cat$ap fn-cat))
           (fn-cat$c-wfp fn-cat$c))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-commit{guard-thm-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-withdraw{guard-thm}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (natp target) (< target (fn-cat$a-count fn-cat))
                (natp by) (fn-cat$ap fn-cat))
           (and (fn-cat$c-wfp fn-cat$c) (natp target) (natp by)
                (< target (fn-cat$c-count fn-cat$c))))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-withdraw{guard-thm-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-redecide{guard-thm}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-hc-p context) (fn-cat$ap fn-cat))
           (and (fn-cat$c-wfp fn-cat$c) (natp seq) (< seq (fn-cat$c-count fn-cat$c))))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-redecide{guard-thm-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-group-live-count{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (fn-cat$ap fn-cat))
           (equal (fn-cat$c-group-live-count group fn-cat$c)
                  (fn-cat$a-group-live-count group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-group-live-count{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-group-live-low{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (fn-cat$ap fn-cat))
           (equal (fn-cat$c-group-live-low group fn-cat$c)
                  (fn-cat$a-group-live-low group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-group-live-low{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-group-live-high{correspondence}
  (implies (and (fn-cat$corr-w fn-cat$c fn-cat) (fn-cat$ap fn-cat))
           (equal (fn-cat$c-group-live-high group fn-cat$c)
                  (fn-cat$a-group-live-high group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-group-live-high{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

(defthm fn-cat-horizon{correspondence}
  (implies (fn-cat$corr-w fn-cat$c fn-cat)
           (equal (fn-cat$c-horizon fn-cat$c) (fn-cat$a-horizon fn-cat)))
  :rule-classes nil
  :hints (("Goal" :use fn-cat-horizon{correspondence-bl}
           :in-theory (union-theories '(fn-cat$corr-w) (theory 'minimal-theory)))))

;; Four of the catalog's lemmas, non-local so that books/catalog.lisp (the
;; generic, split from this book so that an implementation can be attached
;; before it: books/catalog-paged-attach.lisp) proves its keystones over the
;; opened view with them; disabled here, enabled where they are used.
(in-theory (disable fn-ctg-nth-of-append-below fn-ctg-nth-of-append-at fn-ctg-len-of-append fn-ctg-number-seq-of-fresh))
