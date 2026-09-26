; fn: the committed event catalog, an attachable abstract stobj (wave 5,
; lane catalog-slice, 2026-09-26; D33; the consolidation design section 1.1).
;
; The LOGICAL value is the committed history as the theorems already know
; it: a true list of held records (books/catalog-record.lisp), oldest first,
; the sequence being the position.  The EXECUTABLE is the indexed tables:
; an array of rows by sequence, a hash table from Message-ID to the
; sequences bound to it, a hash table from (group . number) to the sequence
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
;   fn-cat-msgid-seqs msgid    (fn-cat-seqs-for msgid C 0)         msgids[msgid]
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

; -----------------------------------------------------------------------------
; Held record helpers: a row's number in a group, and the three row updates
; that keep its keys (Message-ID, numbers, facts).

(defun fn-cat-assoc (k alist)
  (declare (xargs :guard t))
  (if (consp alist)
      (if (and (consp (car alist)) (equal k (car (car alist))))
          (car alist)
        (fn-cat-assoc k (cdr alist)))
    nil))

(defun fn-held-number-in (group h)
  (declare (xargs :guard t))
  (let ((pair (fn-cat-assoc group (fn-held-numbers h))))
    (if (consp pair) (cdr pair) nil)))

(defun fn-held-with-numbers (h numbers)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence h) (fn-record-txid h) (fn-record-generation h)
                (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) (fn-held-facts h) (fn-held-context h)
                numbers (fn-held-withdrawn h)))

(defun fn-held-with-withdrawn (h withdrawn)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence h) (fn-record-txid h) (fn-record-generation h)
                (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) (fn-held-facts h) (fn-held-context h)
                (fn-held-numbers h) withdrawn))

(defun fn-held-with-context (h context)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence h) (fn-record-txid h) (fn-record-generation h)
                (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) (fn-held-facts h) context
                (fn-held-numbers h) (fn-held-withdrawn h)))

; -----------------------------------------------------------------------------
; The logical model: the columns as functions of the list.

; The sequences of the rows carrying MSGID, ascending, the first row being I.
(defun fn-cat-seqs-for (msgid c i)
  (declare (xargs :guard (natp i)))
  (if (consp c)
      (if (equal msgid (fn-record-msgid (car c)))
          (cons i (fn-cat-seqs-for msgid (cdr c) (+ 1 i)))
        (fn-cat-seqs-for msgid (cdr c) (+ 1 i)))
    nil))

; The first row binding (GROUP . N), or nil; a row outside the group binds
; nothing, so no N matches it.
(defun fn-cat-number-seq (group n c i)
  (declare (xargs :guard (natp i)))
  (if (consp c)
      (let ((b (fn-held-number-in group (car c))))
        (if (and b (equal b n))
            i
          (fn-cat-number-seq group n (cdr c) (+ 1 i))))
    nil))

; The highest number bound in GROUP (0 when none).
(defun fn-cat-group-high (group c)
  (declare (xargs :guard t))
  (if (consp c)
      (max (nfix (fn-held-number-in group (car c)))
           (fn-cat-group-high group (cdr c)))
    0))

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
(defun fn-cat-assign-numbers (groups c)
  (declare (xargs :guard t))
  (if (consp groups)
      (cons (cons (car groups) (+ 1 (fn-cat-group-high (car groups) c)))
            (fn-cat-assign-numbers (cdr groups) c))
    nil))

(defun fn-cat-assign (h c)
  (declare (xargs :guard t))
  (fn-held-with-numbers h (fn-cat-assign-numbers (fn-record-groups h) c)))

; A row below version V, not withdrawn or withdrawn at a version V does
; not exceed.
(defun fn-cat-visiblep (seq v c)
  (declare (xargs :guard (and (natp seq) (natp v) (fn-held-listp c) (< seq (len c)))))
  (and (< seq v)
       (let ((w (fn-held-withdrawn (nth seq c))))
         (or (null w) (<= v (car w))))))

(defun fn-cat-mark-withdrawn (target v by c)
  (declare (xargs :guard (and (natp target) (natp v) (natp by) (fn-held-listp c))))
  (if (and (< target (len c))
           (null (fn-held-withdrawn (nth target c))))
      (update-nth target (fn-held-with-withdrawn (nth target c) (cons v by)) c)
    c))

; -----------------------------------------------------------------------------
; The logical side of the exports.

(defun fn-cat$ap (x)
  (declare (xargs :guard t))
  (fn-held-listp x))

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

; -----------------------------------------------------------------------------
; The foundation.

(defstobj fn-cat$c
  (fn-cat$c-rows :type (array t (0)) :resizable t)
  (fn-cat$c-count :type (integer 0 *) :initially 0)
  (fn-cat$c-msgids :type (hash-table equal))
  (fn-cat$c-numbers :type (hash-table equal))
  (fn-cat$c-groups :type (hash-table equal))
  (fn-cat$c-octets :type (integer 0 *) :initially 0)
  :inline t)

(local
 (defthm fn-ctg-cells-are-naturals
   (implies (fn-cat$cp fn-cat$c)
            (and (natp (fn-cat$c-count fn-cat$c))
                 (natp (fn-cat$c-octets fn-cat$c))))
   :rule-classes (:rewrite (:forward-chaining :trigger-terms ((fn-cat$cp fn-cat$c))))
   :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-countp fn-cat$c-octetsp)))))

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
            (and (fn-cat$cp (fn-cat$c-msgids-put k v fn-cat$c))
                 (fn-cat$cp (fn-cat$c-numbers-put k v fn-cat$c))
                 (fn-cat$cp (fn-cat$c-groups-put k v fn-cat$c))
                 (fn-cat$cp (fn-cat$c-msgids-clear fn-cat$c))
                 (fn-cat$cp (fn-cat$c-numbers-clear fn-cat$c))
                 (fn-cat$cp (fn-cat$c-groups-clear fn-cat$c))))
   :hints (("Goal" :in-theory (enable fn-cat$cp)))))

(local
 (defthm fn-ctg-rows-length-of-writes
   (and (equal (fn-cat$c-rows-length (resize-fn-cat$c-rows n fn-cat$c)) (nfix n))
        (equal (fn-cat$c-rows-length (update-fn-cat$c-rowsi i v fn-cat$c))
               (if (and (natp i) (< i (fn-cat$c-rows-length fn-cat$c)))
                   (fn-cat$c-rows-length fn-cat$c)
                 (max (1+ (nfix i)) (fn-cat$c-rows-length fn-cat$c))))
        (equal (fn-cat$c-rows-length (fn-cat$c-msgids-put k v fn-cat$c))
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

(defun fn-cat$c-msgid-seqs (msgid fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (fn-cat$c-msgids-get msgid fn-cat$c))

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
(defun fn-cat$c-plan (groups fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (if (consp groups)
      (let ((e (fn-cat$c-groups-get (car groups) fn-cat$c)))
        (cons (list (car groups)
                    (if (consp e) (nfix (cdr e)) 1)
                    (if (consp e) (nfix (car e)) 0))
              (fn-cat$c-plan (cdr groups) fn-cat$c)))
    nil))

(defun fn-cat-plan-numbers (plan)
  (declare (xargs :guard t))
  (if (consp plan)
      (cons (cons (fn-cbor-ag-car (car plan)) (fn-cbor-ag-car (fn-cbor-ag-cdr (car plan))))
            (fn-cat-plan-numbers (cdr plan)))
    nil))

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
        (equal (fn-cat$c-octets (fn-cat$c-msgids-put k v fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-octets (fn-cat$c-numbers-put k v fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-octets (fn-cat$c-groups-put k v fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-octets (update-fn-cat$c-count n fn-cat$c)) (fn-cat$c-octets fn-cat$c))
        (equal (fn-cat$c-count (update-fn-cat$c-rowsi i v fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (resize-fn-cat$c-rows n fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (fn-cat$c-msgids-put k v fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (fn-cat$c-numbers-put k v fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (fn-cat$c-groups-put k v fn-cat$c)) (fn-cat$c-count fn-cat$c))
        (equal (fn-cat$c-count (update-fn-cat$c-octets n fn-cat$c)) (fn-cat$c-count fn-cat$c)))
   :hints (("Goal" :in-theory (enable update-nth-array fn-cat$c-octets fn-cat$c-count
                                      update-fn-cat$c-rowsi resize-fn-cat$c-rows
                                      fn-cat$c-msgids-put fn-cat$c-numbers-put
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
                     fn-cat$c-msgids-get fn-cat$c-msgids-put fn-cat$c-msgids-clear
                     fn-cat$c-numbers-get fn-cat$c-numbers-put fn-cat$c-numbers-clear
                     fn-cat$c-groups-get fn-cat$c-groups-put fn-cat$c-groups-clear)))

; A total snoc: append on a true list, and on anything else the list of one.
(defun fn-cat-snoc (xs x)
  (declare (xargs :guard t))
  (if (consp xs) (cons (car xs) (fn-cat-snoc (cdr xs) x)) (list x)))

(defun fn-cat$c-commit (h fn-cat$c)
  (declare (xargs :stobjs fn-cat$c :guard (fn-cat$c-wfp fn-cat$c)))
  (let* ((seq (fn-cat$c-count fn-cat$c))
         (plan (fn-cat$c-plan (fn-record-groups h) fn-cat$c))
         (row (fn-held-with-numbers h (fn-cat-plan-numbers plan)))
         (fn-cat$c (if (< seq (fn-cat$c-rows-length fn-cat$c))
                       fn-cat$c
                     (resize-fn-cat$c-rows (+ 1 (* 2 seq)) fn-cat$c)))
         (fn-cat$c (update-fn-cat$c-rowsi seq row fn-cat$c))
         (fn-cat$c (fn-cat$c-msgids-put
                    (fn-record-msgid h)
                    (fn-cat-snoc (fn-cat$c-msgids-get (fn-record-msgid h) fn-cat$c) seq)
                    fn-cat$c))
         (fn-cat$c (fn-cat$c-apply-plan plan seq fn-cat$c))
         (fn-cat$c (update-fn-cat$c-octets
                    (+ (fn-cat$c-octets fn-cat$c)
                       (nfix (fn-hf-octets (fn-held-facts h))))
                    fn-cat$c)))
    (update-fn-cat$c-count (+ 1 seq) fn-cat$c)))

(defun fn-cat$c-withdraw (target by fn-cat$c)
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

(defun fn-cat$c-clear (fn-cat$c)
  (declare (xargs :stobjs fn-cat$c))
  (let* ((fn-cat$c (update-fn-cat$c-count 0 fn-cat$c))
         (fn-cat$c (update-fn-cat$c-octets 0 fn-cat$c))
         (fn-cat$c (fn-cat$c-msgids-clear fn-cat$c))
         (fn-cat$c (fn-cat$c-numbers-clear fn-cat$c)))
    (fn-cat$c-groups-clear fn-cat$c)))

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

; Every key of KEYS (an alist walked for its keys) looks up in TAB to the
; Message-ID column's value.
(defun fn-cat-msgids-okp (keys tab c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp keys)
      (and (equal (cdr (hons-assoc-equal (car (car keys)) tab))
                  (fn-cat-seqs-for (car (car keys)) c 0))
           (fn-cat-msgids-okp (cdr keys) tab c))
    t))

; Every row's Message-ID is bound in TAB.
(defun fn-cat-msgids-coverp (c tab)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp c)
      (and (consp (hons-assoc-equal (fn-record-msgid (car c)) tab))
           (fn-cat-msgids-coverp (cdr c) tab))
    t))

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
(defun-nx fn-cat$corr (fn-cat$c fn-cat$a)
  (and (fn-cat$cp fn-cat$c)
       (fn-held-listp fn-cat$a)
       (equal (nth 1 fn-cat$c) (len fn-cat$a))
       (<= (nth 1 fn-cat$c) (len (nth 0 fn-cat$c)))
       (fn-cat-rows-corr (len fn-cat$a) fn-cat$a (nth 0 fn-cat$c))
       (fn-cat-msgids-okp (nth 2 fn-cat$c) (nth 2 fn-cat$c) fn-cat$a)
       (fn-cat-msgids-coverp fn-cat$a (nth 2 fn-cat$c))
       (fn-cat-numbers-okp (nth 3 fn-cat$c) (nth 3 fn-cat$c) fn-cat$a)
       (fn-cat-numbers-coverp fn-cat$a (nth 3 fn-cat$c))
       (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) fn-cat$a)
       (fn-cat-groups-coverp fn-cat$a (nth 4 fn-cat$c))
       (equal (nth 5 fn-cat$c) (fn-cat-octets-of fn-cat$a))))

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
   :rule-classes :type-prescription))

(local
 (defthm fn-ctg-number-in-type
   (implies (fn-held-p h)
            (or (null (fn-held-number-in g h))
                (posp (fn-held-number-in g h))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

; A number above the group's high names no row.
(local
 (defthm fn-ctg-number-seq-above-high
   (implies (and (fn-held-listp c) (rationalp n) (< (fn-cat-group-high g c) n))
            (equal (fn-cat-number-seq g n c i) nil))))

; A bound number is at most the high.
(local
 (defthm fn-ctg-number-seq-below-high
   (implies (and (fn-held-listp c) (fn-cat-number-seq g n c i) (rationalp n))
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
; The tables after the commit's writes.  A put conses the pair in front
; (the hash-table field's logical model), so a lookup finds the newest.

; The Message-ID column of an unbound Message-ID is empty.
(local
 (defthm fn-ctg-seqs-for-unbound
   (implies (and (fn-cat-msgids-coverp c tab)
                 (not (consp (hons-assoc-equal m tab))))
            (equal (fn-cat-seqs-for m c i) nil))))

(local
 (defthm fn-ctg-msgids-okp-of-commit
   (implies (and (fn-cat-msgids-okp keys tab c)
                 (fn-cat-msgids-coverp c tab)
                 (equal m0 (fn-record-msgid h))
                 (equal v (append (fn-cat-seqs-for m0 c 0) (list (len c)))))
            (fn-cat-msgids-okp keys (cons (cons m0 v) tab) (append c (list h))))))

(local
 (defthm fn-ctg-msgids-coverp-of-commit
   (implies (and (fn-cat-msgids-coverp c tab) (equal m0 (fn-record-msgid h)))
            (fn-cat-msgids-coverp (append c (list h)) (cons (cons m0 v) tab)))))

(local
 (defthm fn-ctg-snoc-is-append
   (implies (true-listp xs)
            (equal (fn-cat-snoc xs x) (append xs (list x))))))

(local
 (defthm fn-ctg-seqs-for-true-listp
   (true-listp (fn-cat-seqs-for m c i))))

; A key bound in the table is one of the walked pairs, so its conjunct holds.
(local
 (defthm fn-ctg-msgids-okp-bound
   (implies (and (fn-cat-msgids-okp keys tab c) (consp (hons-assoc-equal m keys)))
            (equal (cdr (hons-assoc-equal m tab)) (fn-cat-seqs-for m c 0)))))

; The bound lookup of a Message-ID is its column (or nil when unbound).
(local
 (defthm fn-ctg-msgids-lookup
   (implies (and (fn-cat-msgids-okp tab tab c) (fn-cat-msgids-coverp c tab))
            (equal (cdr (hons-assoc-equal m tab)) (fn-cat-seqs-for m c 0)))
   :hints (("Goal" :do-not-induct t
            :cases ((consp (hons-assoc-equal m tab)))))))

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

(local
 (defthm fn-ctg-nth-of-append-below
   (implies (and (natp i) (< i (len c)))
            (equal (nth i (append c (list h))) (nth i c)))))

(local
 (defthm fn-ctg-nth-of-append-at
   (implies (equal i (len c))
            (equal (nth i (append c (list h))) h))))

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
   (fn-held-numbersp (fn-cat-assign-numbers groups c))))

(local
 (defthm fn-ctg-held-p-of-assign
   (implies (fn-held-p h) (fn-held-p (fn-cat-assign h c)))
   :hints (("Goal" :in-theory (enable fn-held-p fn-cat-assign fn-held-with-numbers)))))

(local
 (defthm fn-ctg-held-p-of-with-withdrawn
   (implies (and (fn-held-p h) (fn-held-withdrawnp w))
            (fn-held-p (fn-held-with-withdrawn h w)))
   :hints (("Goal" :in-theory (enable fn-held-p fn-held-with-withdrawn)))))

(local
 (defthm fn-ctg-held-p-of-with-context
   (implies (and (fn-held-p h) (fn-hc-p ctx))
            (fn-held-p (fn-held-with-context h ctx)))
   :hints (("Goal" :in-theory (enable fn-held-p fn-held-with-context)))))

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
   (implies (and (fn-held-listp c)
                 (fn-cat-number-seq (car k) (cdr k) c 0)
                 (rationalp (cdr k)))
            (not (member-equal k (fn-cat-assign-numbers groups c))))))

; A number that names a row of a held list is a positive integer.
(local
 (defthm fn-ctg-number-seq-posp
   (implies (and (fn-held-listp c) (fn-cat-number-seq g n c i))
            (posp n))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

; Old keys: a bound number names a row of C, so it is not in the
; assignment; its column is unchanged by the new row.
(local
 (defthm fn-ctg-numbers-okp-old-keys
   (implies (and (fn-cat-numbers-okp keys tab c) (fn-held-listp c)
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
     fn-cat$c-msgids-get fn-cat$c-msgids-put fn-cat$c-msgids-clear
     fn-cat$c-numbers-get fn-cat$c-numbers-put fn-cat$c-numbers-clear
     fn-cat$c-groups-get fn-cat$c-groups-put fn-cat$c-groups-clear
     update-nth-array fn-cat$c-wfp fn-cat$c-at fn-cat$c-msgid-seqs
     fn-cat$c-group-number fn-cat$c-group-next fn-cat$c-group-count
     fn-cat$c-total-octets fn-cat$c-visible-at)))

(defthm create-fn-cat{correspondence}
  (fn-cat$corr (create-fn-cat$c) (create-fn-cat$a))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cat$cp create-fn-cat$c))))

(defthm create-fn-cat{preserved}
  (fn-cat$ap (create-fn-cat$a))
  :rule-classes nil)

(defthm fn-cat-count{correspondence}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-count fn-cat$c) (fn-cat$a-count fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-at{correspondence}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-cat$ap fn-cat))
           (equal (fn-cat$c-at seq fn-cat$c) (fn-cat$a-at seq fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-at{guard-thm}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-cat$ap fn-cat))
           (and (fn-cat$c-wfp fn-cat$c) (natp seq) (< seq (fn-cat$c-count fn-cat$c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-msgid-seqs{correspondence}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-msgid-seqs msgid fn-cat$c) (fn-cat$a-msgid-seqs msgid fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-group-number{correspondence}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-group-number group n fn-cat$c)
                  (fn-cat$a-group-number group n fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-group-next{correspondence}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-group-next group fn-cat$c) (fn-cat$a-group-next group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open)
           :cases ((consp (cdr (hons-assoc-equal group (nth 4 fn-cat$c))))))))

(defthm fn-cat-group-count{correspondence}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-group-count group fn-cat$c) (fn-cat$a-group-count group fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open)
           :cases ((consp (cdr (hons-assoc-equal group (nth 4 fn-cat$c))))))))

(defthm fn-cat-total-octets{correspondence}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (equal (fn-cat$c-total-octets fn-cat$c) (fn-cat$a-total-octets fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-visible-at{correspondence}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat)) (natp v)
                (fn-cat$ap fn-cat))
           (equal (fn-cat$c-visible-at seq v fn-cat$c) (fn-cat$a-visible-at seq v fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctg-open))))

(defthm fn-cat-visible-at{guard-thm}
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
(local
 (defthm fn-ctg-commit-msgids-head
   (implies (and (fn-cat-msgids-okp tab tab c) (fn-cat-msgids-coverp c tab)
                 (equal m0 (fn-record-msgid h)))
            (equal (fn-cat-snoc (cdr (hons-assoc-equal m0 tab)) (len c))
                   (append (fn-cat-seqs-for m0 c 0) (list (len c)))))))

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
(local
 (defthm fn-ctg-number-seq-of-fresh
   (implies (and (fn-held-listp c) (member-equal g (fn-record-groups h))
                 (equal n (+ 1 (fn-cat-group-high g c))))
            (equal (fn-cat-number-seq g n (append c (list (fn-cat-assign h c))) 0)
                   (len c)))))

(local
 (defthm fn-ctg-commit-numbers-new-keys
   (implies (and (fn-held-listp c)
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
            (fn-cat-groups-cover-rowp ns (fn-cat-gputs plan tab)))))

(local
 (defthm fn-ctg-groups-coverp-monotone
   (implies (fn-cat-groups-coverp c tab)
            (fn-cat-groups-coverp c (fn-cat-gputs plan tab)))))

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
   (implies (and (fn-held-listp c)
                 (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c)
                 (fn-cat-groups-coverp c (nth 4 fn-cat$c))
                 (fn-cat-groups-okp keys (nth 4 fn-cat$c) c))
            (fn-cat-groups-okp keys
                               (fn-cat-gputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (nth 4 fn-cat$c))
                               (append c (list (fn-cat-assign h c)))))
   :hints (("Goal" :induct (fn-cat-groups-okp keys (nth 4 fn-cat$c) c)))))

(local
 (defthm fn-ctg-commit-groups-okp-new-keys
   (implies (and (fn-held-listp c)
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
(local
 (defthm fn-ctg-commit-fields
   (implies (fn-cat$cp fn-cat$c)
            (let ((plan (fn-cat$c-plan (fn-record-groups h) fn-cat$c))
                  (count (nth 1 fn-cat$c)))
              (and (equal (nth 0 (fn-cat$c-commit h fn-cat$c))
                          (update-nth count
                                      (fn-held-with-numbers h (fn-cat-plan-numbers plan))
                                      (if (< count (len (nth 0 fn-cat$c)))
                                          (nth 0 fn-cat$c)
                                        (resize-list (nth 0 fn-cat$c) (+ 1 (* 2 count)) nil))))
                   (equal (nth 1 (fn-cat$c-commit h fn-cat$c)) (+ 1 count))
                   (equal (nth 2 (fn-cat$c-commit h fn-cat$c))
                          (cons (cons (fn-record-msgid h)
                                      (fn-cat-snoc (cdr (hons-assoc-equal (fn-record-msgid h)
                                                                          (nth 2 fn-cat$c)))
                                                   count))
                                (nth 2 fn-cat$c)))
                   (equal (nth 3 (fn-cat$c-commit h fn-cat$c))
                          (fn-cat-nputs plan count (nth 3 fn-cat$c)))
                   (equal (nth 4 (fn-cat$c-commit h fn-cat$c))
                          (fn-cat-gputs plan (nth 4 fn-cat$c)))
                   (equal (nth 5 (fn-cat$c-commit h fn-cat$c))
                          (+ (nth 5 fn-cat$c) (nfix (fn-hf-octets (fn-held-facts h))))))))
   :hints (("Goal" :in-theory (e/d (fn-ctg-open fn-cat$c-commit) (nth update-nth))))))

(local
 (defthm fn-ctg-cp-of-commit
   (implies (and (fn-cat$cp fn-cat$c) (fn-cat$c-wfp fn-cat$c))
            (fn-cat$cp (fn-cat$c-commit h fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-commit fn-cat$c-wfp)))))

(local
 (defthm fn-ctg-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

; Well-formedness in the corr's vocabulary.
(local
 (defthm fn-ctg-wfp-is-nth
   (implies (fn-cat$cp fn-cat$c)
            (equal (fn-cat$c-wfp fn-cat$c)
                   (<= (nth 1 fn-cat$c) (len (nth 0 fn-cat$c)))))
   :hints (("Goal" :in-theory (enable fn-cat$c-wfp fn-cat$c-count fn-cat$c-rows-length)))))

(local
 (defthm fn-ctg-wfp-from-corr
   (implies (fn-cat$corr fn-cat$c fn-cat)
            (fn-cat$c-wfp fn-cat$c))
   :hints (("Goal" :in-theory (enable fn-ctg-open)))))

(defthm fn-cat-commit{correspondence}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (fn-held-p h) (fn-cat$ap fn-cat))
           (fn-cat$corr (fn-cat$c-commit h fn-cat$c) (fn-cat$a-commit h fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cat-assign)
                                  (fn-cat$c-commit fn-cat$c-plan fn-cat$c-groups-get resize-list))
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
                 (:instance fn-ctg-msgids-okp-of-commit
                            (keys (nth 2 fn-cat$c)) (tab (nth 2 fn-cat$c)) (c fn-cat)
                            (m0 (fn-record-msgid h))
                            (v (append (fn-cat-seqs-for (fn-record-msgid h) fn-cat 0)
                                       (list (len fn-cat)))))
                 (:instance fn-ctg-rows-corr-extend
                            (n (len fn-cat)) (c fn-cat)
                            (rows (if (< (len fn-cat) (len (nth 0 fn-cat$c)))
                                      (nth 0 fn-cat$c)
                                    (resize-list (nth 0 fn-cat$c) (+ 1 (* 2 (len fn-cat))) nil)))
                            (h (fn-cat-assign h fn-cat)))))))

(defthm fn-cat-commit{guard-thm}
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
 (defthm fn-ctg-msgids-okp-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-msgids-okp keys tab (update-nth k h c))
                   (fn-cat-msgids-okp keys tab c)))))

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
 (defthm fn-ctg-msgids-coverp-update-nth
   (implies (and (natp k) (< k (len c)) (fn-cat-same-keysp h (nth k c)))
            (equal (fn-cat-msgids-coverp (update-nth k h c) tab)
                   (fn-cat-msgids-coverp c tab)))))

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
              (and (equal (nth 0 (fn-cat$c-withdraw target by fn-cat$c))
                          (if (null (fn-held-withdrawn row))
                              (update-nth target
                                          (fn-held-with-withdrawn row (cons (nth 1 fn-cat$c) by))
                                          (nth 0 fn-cat$c))
                            (nth 0 fn-cat$c)))
                   (equal (nth 1 (fn-cat$c-withdraw target by fn-cat$c)) (nth 1 fn-cat$c))
                   (equal (nth 2 (fn-cat$c-withdraw target by fn-cat$c)) (nth 2 fn-cat$c))
                   (equal (nth 3 (fn-cat$c-withdraw target by fn-cat$c)) (nth 3 fn-cat$c))
                   (equal (nth 4 (fn-cat$c-withdraw target by fn-cat$c)) (nth 4 fn-cat$c))
                   (equal (nth 5 (fn-cat$c-withdraw target by fn-cat$c)) (nth 5 fn-cat$c)))))
   :hints (("Goal" :in-theory (e/d (fn-ctg-open fn-cat$c-withdraw) (nth update-nth))))))

(local
 (defthm fn-ctg-cp-of-withdraw
   (implies (and (fn-cat$cp fn-cat$c) (natp target) (< target (len (nth 0 fn-cat$c))))
            (fn-cat$cp (fn-cat$c-withdraw target by fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-withdraw fn-cat$c-rows-length)))))

(defthm fn-cat-withdraw{correspondence}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp target) (< target (fn-cat$a-count fn-cat))
                (natp by) (fn-cat$ap fn-cat))
           (fn-cat$corr (fn-cat$c-withdraw target by fn-cat$c)
                        (fn-cat$a-withdraw target by fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cat-mark-withdrawn)
                                  (fn-cat$c-withdraw fn-held-with-withdrawn))
           :do-not-induct t)))

(defthm fn-cat-withdraw{guard-thm}
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
 (defthm fn-ctg-cp-of-redecide
   (implies (and (fn-cat$cp fn-cat$c) (natp seq) (< seq (len (nth 0 fn-cat$c))))
            (fn-cat$cp (fn-cat$c-redecide seq context fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-redecide fn-cat$c-rows-length)))))

(defthm fn-cat-redecide{correspondence}
  (implies (and (fn-cat$corr fn-cat$c fn-cat) (natp seq) (< seq (fn-cat$a-count fn-cat))
                (fn-hc-p context) (fn-cat$ap fn-cat))
           (fn-cat$corr (fn-cat$c-redecide seq context fn-cat$c)
                        (fn-cat$a-redecide seq context fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-cat$c-redecide fn-held-with-context)
           :do-not-induct t)))

(defthm fn-cat-redecide{guard-thm}
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
 (defthm fn-ctg-cp-of-clear
   (implies (fn-cat$cp fn-cat$c)
            (fn-cat$cp (fn-cat$c-clear fn-cat$c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-clear)))))

(local
 (defthm fn-ctg-clear-fields
   (implies (fn-cat$cp fn-cat$c)
            (and (equal (nth 1 (fn-cat$c-clear fn-cat$c)) 0)
                 (equal (nth 2 (fn-cat$c-clear fn-cat$c)) nil)
                 (equal (nth 3 (fn-cat$c-clear fn-cat$c)) nil)
                 (equal (nth 4 (fn-cat$c-clear fn-cat$c)) nil)
                 (equal (nth 5 (fn-cat$c-clear fn-cat$c)) 0)))
   :hints (("Goal" :in-theory (e/d (fn-ctg-open fn-cat$c-clear) (nth update-nth))))))

(defthm fn-cat-clear{correspondence}
  (implies (fn-cat$corr fn-cat$c fn-cat)
           (fn-cat$corr (fn-cat$c-clear fn-cat$c) (fn-cat$a-clear fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-cat$c-clear) :do-not-induct t)))

(defthm fn-cat-clear{preserved}
  (implies (fn-cat$ap fn-cat)
           (fn-cat$ap (fn-cat$a-clear fn-cat)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The catalog.  The exports are stated over the list; `:attachable t' lets
; an image attach another implementation of the same logical side.

(defabsstobj fn-cat
  :foundation fn-cat$c
  :recognizer (fn-cat-p :logic fn-cat$ap :exec fn-cat$cp)
  :creator (create-fn-cat :logic create-fn-cat$a :exec create-fn-cat$c)
  :corr-fn fn-cat$corr
  :exports ((fn-cat-count :logic fn-cat$a-count :exec fn-cat$c-count)
            (fn-cat-at :logic fn-cat$a-at :exec fn-cat$c-at)
            (fn-cat-msgid-seqs :logic fn-cat$a-msgid-seqs :exec fn-cat$c-msgid-seqs)
            (fn-cat-group-number :logic fn-cat$a-group-number :exec fn-cat$c-group-number)
            (fn-cat-group-next :logic fn-cat$a-group-next :exec fn-cat$c-group-next)
            (fn-cat-group-count :logic fn-cat$a-group-count :exec fn-cat$c-group-count)
            (fn-cat-total-octets :logic fn-cat$a-total-octets :exec fn-cat$c-total-octets)
            (fn-cat-visible-at :logic fn-cat$a-visible-at :exec fn-cat$c-visible-at)
            (fn-cat-commit :logic fn-cat$a-commit :exec fn-cat$c-commit :protect t)
            (fn-cat-withdraw :logic fn-cat$a-withdraw :exec fn-cat$c-withdraw :protect t)
            (fn-cat-redecide :logic fn-cat$a-redecide :exec fn-cat$c-redecide :protect t)
            (fn-cat-clear :logic fn-cat$a-clear :exec fn-cat$c-clear :protect t))
  :attachable t)

; -----------------------------------------------------------------------------
; The logical view, opened: a theorem over `fn-cat' is a theorem over the
; list of held records.

(defthm fn-cat-p-is-held-listp
  (equal (fn-cat-p x) (fn-held-listp x)))

(defthm fn-cat-count-is-len
  (equal (fn-cat-count fn-cat) (len fn-cat)))

(defthm fn-cat-at-is-nth
  (equal (fn-cat-at seq fn-cat) (nth seq fn-cat)))

(defthm fn-cat-msgid-seqs-is-seqs-for
  (equal (fn-cat-msgid-seqs msgid fn-cat) (fn-cat-seqs-for msgid fn-cat 0)))

(defthm fn-cat-group-number-is-number-seq
  (equal (fn-cat-group-number group n fn-cat) (fn-cat-number-seq group n fn-cat 0)))

(defthm fn-cat-group-next-is-high
  (equal (fn-cat-group-next group fn-cat) (+ 1 (fn-cat-group-high group fn-cat))))

(defthm fn-cat-group-count-is-rows
  (equal (fn-cat-group-count group fn-cat) (fn-cat-group-rows group fn-cat)))

(defthm fn-cat-total-octets-is-octets-of
  (equal (fn-cat-total-octets fn-cat) (fn-cat-octets-of fn-cat)))

(defthm fn-cat-visible-at-is-visiblep
  (equal (fn-cat-visible-at seq v fn-cat) (fn-cat-visiblep seq v fn-cat)))

(defthm fn-cat-commit-is-append
  (equal (fn-cat-commit h fn-cat) (append fn-cat (list (fn-cat-assign h fn-cat)))))

(defthm fn-cat-withdraw-is-mark
  (equal (fn-cat-withdraw target by fn-cat)
         (fn-cat-mark-withdrawn target (len fn-cat) by fn-cat)))

(defthm fn-cat-redecide-is-update-nth
  (equal (fn-cat-redecide seq context fn-cat)
         (update-nth seq (fn-held-with-context (nth seq fn-cat) context) fn-cat)))

(defthm fn-cat-clear-is-nil
  (equal (fn-cat-clear fn-cat) nil))

(in-theory (disable fn-cat-p fn-cat-count fn-cat-at fn-cat-msgid-seqs
                    fn-cat-group-number fn-cat-group-next fn-cat-group-count
                    fn-cat-total-octets fn-cat-visible-at fn-cat-commit
                    fn-cat-withdraw fn-cat-redecide fn-cat-clear
                    fn-cat-p-is-held-listp fn-cat-assign fn-cat-visiblep
                    fn-cat-mark-withdrawn fn-held-with-numbers
                    fn-held-with-withdrawn fn-held-with-context))

; KEYSTONES over the opened view: a commit appends one row whose numbers
; are one past each of its groups' highs, and leaves every row below the
; old count as it was; a number is bound to at most one row (the first
; found is the only one); a row withdrawn at version W is visible to a
; version V exactly when V <= W.

(defthm fn-cat-commit-keeps-rows
  (implies (and (natp seq) (< seq (fn-cat-count fn-cat)))
           (equal (fn-cat-at seq (fn-cat-commit h fn-cat))
                  (fn-cat-at seq fn-cat)))
  :hints (("Goal" :in-theory (enable fn-ctg-nth-of-append-below))))

(defthm fn-cat-commit-new-row
  (equal (fn-cat-at (fn-cat-count fn-cat) (fn-cat-commit h fn-cat))
         (fn-cat-assign h fn-cat))
  :hints (("Goal" :in-theory (enable fn-ctg-nth-of-append-at))))

(defthm fn-cat-commit-count
  (equal (fn-cat-count (fn-cat-commit h fn-cat)) (+ 1 (fn-cat-count fn-cat)))
  :hints (("Goal" :in-theory (enable fn-ctg-len-of-append))))

(defthm fn-cat-commit-binds-fresh-numbers
  (implies (and (fn-cat-p fn-cat) (member-equal g (fn-record-groups h)))
           (equal (fn-cat-group-number g (fn-cat-group-next g fn-cat) (fn-cat-commit h fn-cat))
                  (fn-cat-count fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-p-is-held-listp fn-ctg-number-seq-of-fresh))))

(defthm fn-cat-visible-at-withdrawn
  (implies (and (natp seq) (natp v) (< seq (fn-cat-count fn-cat))
                (fn-held-withdrawn (fn-cat-at seq fn-cat)))
           (equal (fn-cat-visible-at seq v fn-cat)
                  (and (< seq v) (<= v (car (fn-held-withdrawn (fn-cat-at seq fn-cat)))))))
  :hints (("Goal" :in-theory (enable fn-cat-visiblep))))
