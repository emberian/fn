; fn: the PAGED implementation of the catalog's logical side (stage 3 of
; planning/design-store-representation-2026-10-01.md, lane paged-catalog,
; 2026-10-01).  The same logical value as books/catalog.lisp (the committed
; history: a list of held records, `fn-cat$ap'), the same :logic function
; behind every export, and a foundation whose rows are TYPED COLUMNS and a
; byte pool instead of an `(array t)' of held records: `fn-crow', one
; declaration of books/def-representation.lisp, whose correspondence and
; preservation the generator discharges.  Attached in the image's include
; order by books/catalog-paged-attach.lisp (`attach-stobj fn-cat
; fn-cat-paged'), so no book above the catalog recertifies -- the arena's
; precedent (books/payload-arena-attach.lisp).
;
; THE ROW.  A held record is sixteen positions; the columns carry the ones
; the executable reads without a decode and the brief names:
;   seq txid gen charge stamp   u64   (fn-record-uint64p: below 2^64)
;   payload                     u64   the arena handle
;   msgid                       octets  the Message-ID's octets in the pool
;   wpres wat wby               bool u64 u64  the withdrawal (at . by)
;   aux                         octets  the REMAINDER: groups, the three
;                                       identities, the facts, the context
;                                       and an empty slot (D43: the
;                                       acceptance binding's, reverted; its
;                                       relay-v1 return fills it) as ONE tree
;                                       in the pool (books/store-tree-codec.lisp,
;                                       KEYSTONE fn-scc-decode-tree-of-encode)
;   nums                        octets  the (group . number) bindings as a
;                                       tree of their own: the withdrawal
;                                       reads them without the remainder
; The logical side admits what no wire record carries (a handle or a
; withdrawal version past 2^64, a remainder outside the tree codec's
; domain: a symbol of another package, a natural past 2^2040), and the
; correspondence must be total over it.  Two escapes, each a branch the
; composed machine never reaches: a natural at or past the column's
; sentinel (2^64 - 1) is carried in the tree (`esc'); a row whose remainder
; is not a tree is kept WHOLE as an object in the overflow cell (the nested
; old foundation's rows array, nil for every row the columns carry).
;
; THE TABLES.  The index tables (the paged Message-ID table fn-mpxt, the
; (group . number), group, live and withdrawn-by-version tables) are stage
; 4's (dense per-group runs); here they are the old foundation `fn-cat$c'
; NESTED whole, its rows array repurposed as the overflow cells, and every
; table operation is the old executable called through `stobj-let'.
;
; THE PROOF is a refinement through the old implementation: the VIEW of a
; paged state is the old foundation with its rows array replaced by the
; decoded columns (`fn-cat$p-view'), the correspondence is the old one on
; the view (`fn-cat$pcorr' = `fn-cat$corr-w' of the view), each paged
; executable SIMULATES the old one on the view exactly (`fn-cat$p-X-sim':
; view of the paged step = the old step of the view), and every obligation
; `defabsstobj' states is the old obligation instantiated at the view.  No
; index theorem is reproved; the row codec's round trip
; (`fn-cp-row-held-of-row-of') is the one new keystone.  No skip-proofs.

(in-package "ACL2")
(include-book "catalog-logic")
;; The live links' meaning and the commit/withdrawal keystones (gate C).
(include-book "catalog-live-links")
(include-book "def-representation")
(include-book "def-representation-tree")
;; The withdrawals-by-version trie (its keystone fn-cpt-list-of-add).
(include-book "catalog-wbv-trie")
;; The tree codec's executables with their guards verified, and the tree
;; recognizer whose program is octets (fn-sccb-treep); its closure carries
;; the frame trailer and the digest attachments, which no recognizer or
;; correspondence below reaches (the catalog's digest-free row shape).
(include-book "store-checkpoint-buffer")
;; fn-record-ascii-string-implies-octet-string, fn-record-string-round-trip:
;; a Message-ID string comes back from its octets.
(include-book "records-invariants")

(local (in-theory (disable (tau-system))))
; D26: two included event-shape rules fire on every term and never help here.
(local (in-theory (disable fn-cne-event-shape fn-cae-event-shape)))

; The stobjs' logical lists stay as `nth' and `update-nth' terms in every
; proof: the old foundation's accessors open to them, and the facts below
; are stated over them (never over car/cdr chains).
(local (in-theory (disable nth update-nth)))

(local
 (defthm fn-cp-nth-of-cons
   (equal (nth i (cons a x)) (if (zp i) a (nth (- i 1) x)))
   :hints (("Goal" :in-theory (enable nth)))))

; -----------------------------------------------------------------------------
; 1. The row store: typed columns and the pool, from one declaration.

(def-representation fn-crow
  (seq :u64) (txid :u64) (gen :u64) (payload :u64) (charge :u64) (stamp :u64)
  (msgid :octets)
  (wpres :bool) (wat :u64) (wby :u64)
  (esc :bool)
  (aux :tree)
  (nums :tree)
  :write-once t)

; -----------------------------------------------------------------------------
; 2. The foundation: the row store beside the old foundation (its tables,
; and its rows array as the overflow cells).

(defstobj fn-cat$p
  (fn-cat$p-rows :type fn-crow)
  (fn-cat$p-tab :type fn-cat$c)
  ;; The live links (books/catalog-live-links.lisp): (group . number) -> the
  ;; least live number above it (NEXT) / the greatest below it (PREV), 0 for
  ;; none.  A withdrawal of a group's low or high reads its neighbour here
  ;; (one probe) instead of scanning the numbers.
  (fn-cat$p-lnext :type (hash-table equal))
  (fn-cat$p-lprev :type (hash-table equal))
  ;; The withdrawals by version: version -> the rows withdrawn at it as a
  ;; binary trie (books/catalog-wbv-trie.lisp): O(log N) a withdrawal, an
  ;; in-order walk allocating only the answer to read, in any arrival
  ;; order.  The nested foundation's own table (its position 8) is not
  ;; written.
  (fn-cat$p-wbv :type (hash-table equal))
  :inline t)

; -----------------------------------------------------------------------------
; 3. The row codec.

; A u64 stays a u64 in every proof below (the column facts are stated with
; it closed; the keystone opens it where the record's bounds are compared).
(local (in-theory (disable unsigned-byte-p)))

(defconst *fn-cp-sent* (1- (expt 2 64)))

; A natural below the sentinel is carried by its column.
(defun fn-cp-smallp (v)
  (declare (xargs :guard t))
  (and (natp v) (< v *fn-cp-sent*)))

; A u64 field (fn-record-uint64p on a well-formed row); anything else is
; clamped so that every column value is typed whatever the row.
(defun fn-cp-u64 (v)
  (declare (xargs :guard t))
  (if (unsigned-byte-p 64 v) v 0))

(defun fn-cp-escapedp (h)
  (declare (xargs :guard t))
  (let ((w (fn-held-withdrawn h)))
    (not (and (fn-cp-smallp (fn-held-payload h))
              (or (null w)
                  (and (consp w) (fn-cp-smallp (car w)) (fn-cp-smallp (cdr w))))))))

; The remainder: what the columns do not carry, as one tree (the numbers
; are a tree of their own, the `nums' column).
(defun fn-cp-tree-of (h)
  (declare (xargs :guard t))
  (list (fn-held-groups h) (fn-held-obligation-id h) (fn-held-content-subject h)
        (fn-held-release-evidence h) (fn-held-facts h) (fn-held-context h)
        nil   ; D43: the binding's slot, empty while the field is reverted
        (if (fn-cp-escapedp h) (list (fn-held-payload h) (fn-held-withdrawn h)) nil)))

(defthm fn-scc-octet-listp-is-adt-octetsp
  (equal (fn-scc-octet-listp x) (adt-octetsp x))
  :hints (("Goal" :in-theory (enable adt-octetsp fn-scc-octet-listp fn-scc-octetp unsigned-byte-p))))

(defthm fn-cbor-octet-listp-is-adt-octetsp
  (equal (fn-cbor-octet-listp x) (adt-octetsp x))
  :hints (("Goal" :in-theory (enable adt-octetsp fn-cbor-octet-listp fn-cbor-octetp unsigned-byte-p))))

; The Message-ID's octets (fn-record-string-octets of a Message-ID string
; is one; clamped so that any row's column is typed).
(defun fn-cp-msgid-octets (h)
  (declare (xargs :guard t))
  (let ((o (fn-record-string-octets (fn-held-msgid h))))
    (if (fn-cbor-octet-listp o) o nil)))

; The row's columns.  Total: every column value is typed for any H (the
; clamps), and a row the tree codec cannot carry (fn-sccb-treep,
; books/store-checkpoint-buffer.lisp: every leaf's octets octets) gets an
; empty remainder and is kept whole in its overflow cell
; (fn-cp-overflow-of).
(defun fn-cp-row-of (h)
  (declare (xargs :guard t))
  (let* ((w (fn-held-withdrawn h))
         (tree (fn-cp-tree-of h)))
    (list (fn-cp-u64 (fn-held-sequence h)) (fn-cp-u64 (fn-held-txid h))
          (fn-cp-u64 (fn-held-generation h))
          (if (fn-cp-smallp (fn-held-payload h)) (fn-held-payload h) 0)
          (fn-cp-u64 (fn-held-charge h)) (fn-cp-u64 (fn-held-stamp h))
          (fn-cp-msgid-octets h)
          (consp w)
          (if (and (consp w) (fn-cp-smallp (car w))) (car w) 0)
          (if (and (consp w) (fn-cp-smallp (cdr w))) (cdr w) 0)
          (fn-cp-escapedp h)
          (if (fn-sccb-treep tree) (fn-scc-program tree) nil)
          (if (fn-sccb-treep (fn-held-numbers h)) (fn-scc-program (fn-held-numbers h)) nil))))

; A row the columns carry exactly: a catalog row (fn-cat-rowp) whose
; remainder and whose numbers are trees; every other row is kept whole in
; its cell, so that the codec is exact for every row (fn-cp-row-held-of-row-of).
(defun fn-cp-overflow-of (h)
  (declare (xargs :guard t))
  (if (and (fn-cat-rowp h) (fn-sccb-treep (fn-cp-tree-of h)) (fn-sccb-treep (fn-held-numbers h)))
      nil
    h))

; A tree column decoded (nil for a program the codec refuses).
(defun fn-cp-decoded (octets)
  (declare (xargs :guard (fn-scc-octet-listp octets)))
  (let ((d (fn-scc-decode-tree octets)))
    (if (and (consp d) (eq (car d) :ok) (consp (cdr d))) (car (cdr d)) nil)))

; The row from its columns: the two trees decoded, the escape honoured.
(defun fn-cp-held (seq txid gen payload charge stamp msgid wpres wat wby esc aux nums)
  (declare (xargs :guard (and (fn-scc-octet-listp aux) (fn-scc-octet-listp nums))))
  (let* ((tree (fn-cp-decoded aux))
         (e (adt-l-nth 7 tree))
         (payload (if esc (adt-l-nth 0 e) payload))
         (w (if esc (adt-l-nth 1 e) (if wpres (cons wat wby) nil))))
    (fn-held-make seq txid gen (fn-record-octets-string msgid) payload
                  (adt-l-nth 0 tree) (adt-l-nth 1 tree) (adt-l-nth 2 tree) (adt-l-nth 3 tree)
                  charge stamp (adt-l-nth 4 tree) (adt-l-nth 5 tree) (fn-cp-decoded nums)
                  w)))

(defun fn-cp-row-held (r)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cp-held (adt-l-nth 0 r) (adt-l-nth 1 r) (adt-l-nth 2 r) (adt-l-nth 3 r) (adt-l-nth 4 r)
              (adt-l-nth 5 r) (adt-l-nth 6 r) (adt-l-nth 7 r) (adt-l-nth 8 r) (adt-l-nth 9 r)
              (adt-l-nth 10 r) (adt-l-nth 11 r) (adt-l-nth 12 r)))

; The columns of any row are a record of the schema.
(local
 (defthm fn-cp-rec-p-of-list
   (equal (adt-rec-p *fn-crow-schema* (list a b c d e f g h i j k l m))
          (and (unsigned-byte-p 64 a) (unsigned-byte-p 64 b) (unsigned-byte-p 64 c)
               (unsigned-byte-p 64 d) (unsigned-byte-p 64 e) (unsigned-byte-p 64 f)
               (adt-octetsp g) (booleanp h) (unsigned-byte-p 64 i) (unsigned-byte-p 64 j)
               (booleanp k) (adt-octetsp l) (adt-octetsp m)))
   :hints (("Goal" :in-theory (enable adt-rec-p adt-val-okp)))))

(local
 (defthm fn-cp-u64-is-u64
   (unsigned-byte-p 64 (fn-cp-u64 v))
   :hints (("Goal" :in-theory (enable fn-cp-u64)))))

(local
 (defthm fn-cp-smallp-is-u64
   (implies (fn-cp-smallp v) (unsigned-byte-p 64 v))
   :hints (("Goal" :in-theory (enable fn-cp-smallp unsigned-byte-p)))))

(local
 (defthm fn-cp-msgid-octets-are-octets
   (adt-octetsp (fn-cp-msgid-octets h))
   :hints (("Goal" :in-theory (enable fn-cp-msgid-octets)))))

(local
 (defthm fn-cp-program-octets
   (implies (fn-sccb-treep x) (adt-octetsp (fn-scc-program x)))
   :hints (("Goal" :use fn-sccb-treep-encodes-octets
            :in-theory (disable fn-sccb-treep-encodes-octets fn-sccb-treep)))))

(local
 (defthm fn-cp-escapedp-booleanp
   (booleanp (fn-cp-escapedp h))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-cp-escapedp)))))

; D26: the record of the 13 columns is fn-cp-rec-p-of-list and the column
; facts; the schema predicate and the codec stay closed (743,766 -> 11,135
; steps).
(defthm fn-cp-row-of-rec-p
  (adt-rec-p *fn-crow-schema* (fn-cp-row-of h))
  :hints (("Goal" :in-theory (e/d (fn-cp-row-of) (fn-cp-u64 fn-cp-smallp fn-cp-msgid-octets
                                                   fn-cp-escapedp fn-sccb-treep fn-scc-program
                                                   fn-cp-tree-of fn-held-numbers adt-rec-p)))))

; The decoder on a program (the keystone fn-scc-decode-tree-of-encode in
; the encoder's executable form).
(local
 (defthm fn-cp-decode-tree-of-program
   (implies (fn-scc-treep x)
            (equal (fn-scc-decode-tree (fn-scc-program x)) (list :ok x)))
   :hints (("Goal" :use fn-scc-decode-tree-of-encode
            :in-theory (e/d (fn-scc-encode-is-program) (fn-scc-decode-tree-of-encode))))))

; KEYSTONE: the row codec's round trip.  A well-formed row whose remainder
; the codec carries comes back from its columns.
(local
 (defthm fn-cp-msgidp-octet-string
   (implies (fn-record-msgidp x) (fn-record-octet-stringp x))
   :hints (("Goal" :in-theory (enable fn-record-msgidp)
            :use ((:instance fn-record-ascii-string-implies-octet-string (text x)))))))

(local
 (defthm fn-cp-msgid-octets-of-msgid
   (implies (fn-record-msgidp (fn-held-msgid h))
            (equal (fn-record-octets-string (fn-cp-msgid-octets h)) (fn-held-msgid h)))
   :hints (("Goal" :in-theory (e/d (fn-cp-msgid-octets fn-record-octet-stringp)
                                   (fn-record-string-octets fn-record-octets-string
                                    fn-record-string-round-trip fn-cp-msgidp-octet-string))
            :use ((:instance fn-record-string-round-trip (text (fn-held-msgid h)))
                  (:instance fn-cp-msgidp-octet-string (x (fn-held-msgid h))))))))

; The columns' row on a program: the tree decoded (fn-cp-decode-tree-of-program),
; the decoder kept closed.
(local
 (defthm fn-cp-decoded-of-program
   (implies (fn-sccb-treep x) (equal (fn-cp-decoded (fn-scc-program x)) x))
   :hints (("Goal" :in-theory (e/d (fn-cp-decoded) (fn-scc-decode-tree fn-scc-program fn-sccb-treep))))))

(local
 (defthm fn-cp-held-of-program
   (implies (and (fn-sccb-treep tree) (fn-sccb-treep nums))
            (equal (fn-cp-held s tx g p c st m wp wa wb e (fn-scc-program tree) (fn-scc-program nums))
                   (fn-held-make s tx g (fn-record-octets-string m)
                                 (if e (adt-l-nth 0 (adt-l-nth 7 tree)) p)
                                 (adt-l-nth 0 tree) (adt-l-nth 1 tree) (adt-l-nth 2 tree)
                                 (adt-l-nth 3 tree) c st (adt-l-nth 4 tree) (adt-l-nth 5 tree)
                                 nums
                                 (if e (adt-l-nth 1 (adt-l-nth 7 tree)) (if wp (cons wa wb) nil)))))
   :hints (("Goal" :in-theory (e/d (fn-cp-held) (fn-cp-decoded fn-scc-decode-tree fn-scc-program fn-sccb-treep))))))

(defthm fn-cp-row-held-of-row-of
  (implies (and (fn-cat-rowp h) (fn-sccb-treep (fn-cp-tree-of h)) (fn-sccb-treep (fn-held-numbers h)))
           (equal (fn-cp-row-held (fn-cp-row-of h)) h))
  :hints (("Goal" :do-not-induct t :use ((:instance fn-held-make-of-accessors (x h)))
           :in-theory (e/d (fn-cat-rowp fn-cp-row-held fn-cp-row-of fn-cp-tree-of
                            fn-cp-escapedp fn-cp-u64 fn-cp-smallp unsigned-byte-p
                            fn-record-uint64p fn-record-stampp fn-held-withdrawnp
                            adt-l-nth)
                           (fn-cp-held fn-sccb-treep fn-scc-decode-tree fn-scc-program
                            fn-cp-msgid-octets fn-record-string-octets
                            fn-record-octets-string
                            fn-held-accessors-are-the-wire-accessors fn-held-make-of-accessors)))))


; TEETH of the keystone.  A reachable positive witness (a plain article's
; row after its commit numbers it): every hypothesis and the conclusion.
; Hypothesis removal, one each: a row that is not a catalog row (its
; Message-ID is a number) with both trees; a catalog row whose remainder is
; not a tree (a payload past the codec's 2^2040, escaped into the
; remainder) with its numbers a tree; a catalog row whose numbers are not a
; tree (a number past 2^2040) with its remainder a tree.  Each keeps the other hypotheses, and the round trip
; fails for all three -- which is why fn-cp-overflow-of keeps exactly those
; rows whole in their cells (the mutation half of each witness).
(defconst *cp-w1*
  (fn-record-make 0 1 0 "<a@x>" (append (fn-record-string-octets "Subject: a") '(13 10 13 10 97 13 10))
                  '("fn.test") "o" "s" "e" 1 5
                  (fn-ab-for-received :post-d25
                                      (append (fn-record-string-octets "Subject: a") '(13 10 13 10 97 13 10)))))
(defconst *cp-h1* (fn-held-with-numbers (fn-held-plain *cp-w1* 0) '(("fn.test" . 1))))
(defconst *cp-h-badmsgid* (update-nth 3 5 *cp-h1*))
(defconst *cp-h-bignum* (fn-held-with-numbers *cp-h1* (list (cons "fn.test" (expt 2 3000)))))
(defconst *cp-h-bigpay* (update-nth 4 (expt 2 3000) *cp-h1*))

(assert-event (let ((h *cp-h1*))
                (and (fn-cat-rowp h) (fn-sccb-treep (fn-cp-tree-of h)) (fn-sccb-treep (fn-held-numbers h))
                     (equal (fn-cp-row-held (fn-cp-row-of h)) h)
                     (null (fn-cp-overflow-of h)))))

(assert-event (let ((h *cp-h-badmsgid*))
                (and (not (fn-cat-rowp h)) (fn-sccb-treep (fn-cp-tree-of h)) (fn-sccb-treep (fn-held-numbers h))
                     (not (equal (fn-cp-row-held (fn-cp-row-of h)) h))
                     (equal (fn-cp-overflow-of h) h))))

(assert-event (let ((h *cp-h-bigpay*))
                (and (fn-cat-rowp h) (not (fn-sccb-treep (fn-cp-tree-of h))) (fn-sccb-treep (fn-held-numbers h))
                     (not (equal (fn-cp-row-held (fn-cp-row-of h)) h))
                     (equal (fn-cp-overflow-of h) h))))

(assert-event (let ((h *cp-h-bignum*))
                (and (fn-cat-rowp h) (fn-sccb-treep (fn-cp-tree-of h)) (not (fn-sccb-treep (fn-held-numbers h)))
                     (not (equal (fn-cp-row-held (fn-cp-row-of h)) h))
                     (equal (fn-cp-overflow-of h) h))))

; -----------------------------------------------------------------------------
; 4. The view and the correspondence.

; The rows list of a paged state: for each overflow cell, the cell when it
; holds a row, else the decoded columns (the same length as the cells).
(defun fn-cp-merge (crow ovf)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ovf)
      nil
    (cons (if (and (consp crow) (null (car ovf))) (fn-cp-row-held (car crow)) (car ovf))
          (fn-cp-merge (cdr crow) (cdr ovf)))))

; The withdrawals by version: the old foundation keeps each version's rows
; ascending (fn-cat-insert-asc, one copy of the list a withdrawal: Theta(m)
; per step under a cancel storm of m).  The paged one keeps a binary trie
; per version (books/catalog-wbv-trie.lisp): the writer copies one path,
; O(log N); the reader walks it in order, allocating only the answer, for
; EVERY arrival order.  Its ascending list after an add is the old insert
; (fn-cpt-list-of-add), so the view's table is the old one exactly.
(defthm fn-cpt-insert-is-insert-asc
  (equal (fn-cpt-insert s l) (fn-cat-insert-asc s l)))


; The view's withdrawals-by-version table: each pushed entry sorted.
(defun fn-cp-wbv-view (al)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom al)
      nil
    (if (consp (car al))
        (cons (cons (car (car al)) (fn-cpt-list (cdr (car al)))) (fn-cp-wbv-view (cdr al)))
      (fn-cp-wbv-view (cdr al)))))

(defthm fn-cp-lookup-of-wbv-view
  (equal (hons-assoc-equal k (fn-cp-wbv-view al))
         (if (hons-assoc-equal k al)
             (cons k (fn-cpt-list (cdr (hons-assoc-equal k al))))
           nil)))

; The old foundation with its rows array and its withdrawals table replaced.
(defun fn-cp-frame (r wb c)
  (declare (xargs :guard t :verify-guards nil))
  (update-nth 0 r (update-nth 8 wb c)))

(defun-nx fn-cat$p-view (fn-cat$p)
  (fn-cp-frame (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p)))
               (fn-cp-wbv-view (nth 4 fn-cat$p))
               (nth 1 fn-cat$p)))

; The correspondence: the old one on the view, and both link tables good
; over the logical rows and binding every live number (so a withdrawal's
; neighbour read never scans: fn-cat$p-next-is-probe, -prev-is-probe).
(defun-nx fn-cat$pcorr (fn-cat$p fn-cat$a)
  (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
       (fn-cat$corr-w (fn-cat$p-view fn-cat$p) fn-cat$a)
       (fn-cpl-okp t (nth 2 fn-cat$p) fn-cat$a)
       (fn-cpl-okp nil (nth 3 fn-cat$p) fn-cat$a)
       (fn-cpl-coverp (nth 2 fn-cat$p) fn-cat$a)
       (fn-cpl-coverp (nth 3 fn-cat$p) fn-cat$a)))

; -----------------------------------------------------------------------------
; 5. The executables.  What their guards need of the nested stores, stated
; once; the recognizers stay closed in every guard proof.

(defthm fn-cp-pp-fields
  (implies (fn-cat$pp fn-cat$p)
           (and (fn-crowp (nth 0 fn-cat$p)) (fn-cat$cp (nth 1 fn-cat$p))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cat$pp))))

; The old foundation's cells, as its recognizer has them (the catalog's
; fn-ctg-cells-are-naturals and fn-ctg-rowsp-true-listp, local there).
(local
 (defthm fn-cp-rowsp-true-listp
   (implies (fn-cat$c-rowsp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cat$c-rowsp)))))

(defthm fn-cp-cp-fields
  (implies (fn-cat$cp c)
           (and (true-listp c) (equal (len c) 11)
                (true-listp (nth 0 c))
                (natp (nth 1 c)) (natp (nth 5 c)) (natp (nth 7 c)) (natp (nth 10 c))
                (fn-mpxtp (nth 2 c)) (fn-mpxtp (nth 9 c))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cat$cp fn-cat$c-countp fn-cat$c-octetsp fn-cat$c-hzp
                                     fn-cat$c-unplacedp fn-cat$c-rowsp))))

(defthm fn-cp-crow-row-rec-p
  (implies (and (fn-crowp a) (natp i) (< i (len a)))
           (adt-rec-p *fn-crow-schema* (nth i a)))
  :hints (("Goal" :in-theory (enable fn-crowp-is-seq-p))))

(defthm fn-cp-crow-aux-octets
  (implies (and (fn-crowp a) (natp i) (< i (len a)))
           (and (adt-octetsp (nth 11 (nth i a)))
                (adt-octetsp (nth 12 (nth i a)))))
  :hints (("Goal" :use fn-cp-crow-row-rec-p
           :in-theory (e/d (adt-rec-p adt-val-okp nth) (fn-cp-crow-row-rec-p fn-crowp)))))

(defthm fn-cp-crowp-of-set-column
  (implies (and (fn-crowp a) (natp i) (< i (len a)) (natp j) (< j 13)
                (adt-val-okp (nth j *fn-crow-schema*) v))
           (fn-crowp (update-nth i (update-nth j v (nth i a)) a)))
  :hints (("Goal" :in-theory (enable fn-crowp-is-seq-p))))

(defthm fn-cp-crowp-of-append-row
  (implies (fn-crowp a)
           (fn-crowp (append a (list (fn-cp-row-of h)))))
  :hints (("Goal" :in-theory (e/d (fn-crowp-is-seq-p) (fn-cp-row-of)))))

(defthm fn-cp-len-of-set-column
  (implies (and (natp i) (< i (len a)))
           (equal (len (update-nth i r a)) (len a))))

; The generated setters rewrite to adt-set-a: its length and the recognizer.
(defthm fn-cp-len-of-adt-set-a
  (implies (and (natp i) (< i (len a)))
           (equal (len (adt-set-a j i v a)) (len a)))
  :hints (("Goal" :in-theory (enable adt-set-a))))

(defthm fn-cp-crowp-of-adt-set-a
  (implies (and (fn-crowp a) (natp i) (< i (len a)) (natp j) (< j 13)
                (adt-val-okp (nth j *fn-crow-schema*) v))
           (fn-crowp (adt-set-a j i v a)))
  :hints (("Goal" :in-theory (e/d (adt-set-a) (fn-cp-crowp-of-set-column))
           :use fn-cp-crowp-of-set-column)))

(local (in-theory (disable fn-cat$pp fn-crowp fn-cat$cp fn-cp-row-of fn-cp-held fn-cp-tree-of
                           fn-cp-escapedp fn-cp-u64 fn-cp-smallp fn-cp-msgid-octets
                           fn-cp-overflow-of fn-cp-row-held)))

(local
 (defthm fn-cp-row-of-fields
   (and (unsigned-byte-p 64 (nth 0 (fn-cp-row-of h)))
        (unsigned-byte-p 64 (nth 1 (fn-cp-row-of h)))
        (unsigned-byte-p 64 (nth 2 (fn-cp-row-of h)))
        (unsigned-byte-p 64 (nth 3 (fn-cp-row-of h)))
        (unsigned-byte-p 64 (nth 4 (fn-cp-row-of h)))
        (unsigned-byte-p 64 (nth 5 (fn-cp-row-of h)))
        (adt-octetsp (nth 6 (fn-cp-row-of h)))
        (booleanp (nth 7 (fn-cp-row-of h)))
        (unsigned-byte-p 64 (nth 8 (fn-cp-row-of h)))
        (unsigned-byte-p 64 (nth 9 (fn-cp-row-of h)))
        (booleanp (nth 10 (fn-cp-row-of h)))
        (adt-octetsp (nth 11 (fn-cp-row-of h)))
        (adt-octetsp (nth 12 (fn-cp-row-of h))))
   :hints (("Goal" :in-theory (e/d (fn-cp-row-of) (fn-cp-u64 fn-cp-smallp fn-cp-msgid-octets
                                                    fn-cp-escapedp fn-sccb-treep))))))

(defun fn-cat$p-count (fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (n) (fn-cat$c-count fn-cat$c) n))

(defun fn-cat$p-wfp (fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (ok)
             (and (fn-cat$c-wfp fn-cat$c)
                  (<= (fn-cat$c-count fn-cat$c) (fn-crow-count fn-crow)))
             ok))

; The row at SEQ: its overflow cell, else its columns decoded.
(defun fn-cat$p-at (seq fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp seq) (< seq (fn-cat$p-count fn-cat$p)))
                  :guard-hints (("Goal" :do-not-induct t))))
  (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (h)
             (let ((o (fn-cat$c-rowsi seq fn-cat$c)))
               (if o
                   o
                 (fn-cp-held (fn-crow-get-seq seq fn-crow) (fn-crow-get-txid seq fn-crow)
                             (fn-crow-get-gen seq fn-crow) (fn-crow-get-payload seq fn-crow)
                             (fn-crow-get-charge seq fn-crow) (fn-crow-get-stamp seq fn-crow)
                             (fn-crow-get-msgid seq fn-crow) (fn-crow-get-wpres seq fn-crow)
                             (fn-crow-get-wat seq fn-crow) (fn-crow-get-wby seq fn-crow)
                             (fn-crow-get-esc seq fn-crow) (fn-crow-get-aux seq fn-crow)
                             (fn-crow-get-nums seq fn-crow))))
             h))

; The withdrawal of the row at SEQ from its three columns: no decode on the
; served reader's path unless the row is escaped or overflowed.
(defun fn-cat$p-withdrawn-of (seq fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp seq) (< seq (fn-cat$p-count fn-cat$p)))
                  :guard-hints (("Goal" :do-not-induct t))))
  (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (w)
             (let ((o (fn-cat$c-rowsi seq fn-cat$c)))
               (cond (o (fn-held-withdrawn o))
                     ((fn-crow-get-esc seq fn-crow)
                      (fn-held-withdrawn
                       (fn-cp-held (fn-crow-get-seq seq fn-crow) (fn-crow-get-txid seq fn-crow)
                                   (fn-crow-get-gen seq fn-crow) (fn-crow-get-payload seq fn-crow)
                                   (fn-crow-get-charge seq fn-crow) (fn-crow-get-stamp seq fn-crow)
                                   (fn-crow-get-msgid seq fn-crow) (fn-crow-get-wpres seq fn-crow)
                                   (fn-crow-get-wat seq fn-crow) (fn-crow-get-wby seq fn-crow)
                                   t (fn-crow-get-aux seq fn-crow) (fn-crow-get-nums seq fn-crow))))
                     ((fn-crow-get-wpres seq fn-crow)
                      (cons (fn-crow-get-wat seq fn-crow) (fn-crow-get-wby seq fn-crow)))
                     (t nil)))
             w))

; The (group . number) bindings of the row at SEQ: its cell's, else its
; numbers column decoded -- the remainder is never read.  The withdrawal's
; only row read beside the three withdrawal columns.
(defun fn-cat$p-numbers-of (seq fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp seq) (< seq (fn-cat$p-count fn-cat$p)))
                  :guard-hints (("Goal" :do-not-induct t))))
  (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (ns)
             (let ((o (fn-cat$c-rowsi seq fn-cat$c)))
               (if o (fn-held-numbers o) (fn-cp-decoded (fn-crow-get-nums seq fn-crow))))
             ns))

; The row at SEQ is carried by its columns (no cell) and not escaped: its
; withdrawal columns are the row's withdrawal.
(defun fn-cat$p-columns-p (seq fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp seq) (< seq (fn-cat$p-count fn-cat$p)))
                  :guard-hints (("Goal" :do-not-induct t))))
  (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (ok)
             (and (null (fn-cat$c-rowsi seq fn-cat$c)) (not (fn-crow-get-esc seq fn-crow)))
             ok))

; A redecided row (operator-rate: `keys redecide', one row a command) in its
; overflow cell: its remainder changed, and the pool is write-once.  The cell
; is replaced on each redecision, never accumulated.  GEN: an in-place
; rewrite of the remainder's extent when the new program fits (needs the
; extents' disjointness in the generator's correspondence).
(defun fn-cat$p-set-cell (seq h fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp seq) (< seq (fn-cat$p-count fn-cat$p)))))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (fn-cat$c)
             (update-fn-cat$c-rowsi seq h fn-cat$c)
             fn-cat$p))

; A withdrawal W written at SEQ (Codex r21 F1, D27).  A row on the columns
; that is not escaped and a withdrawal the columns carry: the three
; withdrawal columns, nothing else -- the row is not read.  Otherwise -- an
; overflowed or escaped row, or a version past the sentinel -- the row
; (decoded here, the only time the withdrawal decodes one) with its new
; withdrawal in its overflow cell.  The pool is never written: fn-crow is
; write-once (no set of an octets field exists), so its fill is its rows'
; octets (fn-crow$c-fill-is-load-of-*).
(defun fn-cat$p-set-withdrawn (seq w fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp seq) (< seq (fn-cat$p-count fn-cat$p)))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (enable adt-val-okp)))))
  (if (and (fn-cat$p-columns-p seq fn-cat$p)
           (consp w) (fn-cp-smallp (car w)) (fn-cp-smallp (cdr w)))
      (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)))
                 (fn-crow)
                 (let* ((fn-crow (fn-crow-set-wpres seq t fn-crow))
                        (fn-crow (fn-crow-set-wat seq (car w) fn-crow)))
                   (fn-crow-set-wby seq (cdr w) fn-crow))
                 fn-cat$p)
    (fn-cat$p-set-cell seq (fn-held-with-withdrawn (fn-cat$p-at seq fn-cat$p) w) fn-cat$p)))

;; The row with its remainder as the TREE (the record NAME-APPEND-T takes:
;; its executable walks the tree into the pool, books/def-representation-tree.lisp).
(defun fn-cp-row-t-of (h tree nums)
  (declare (xargs :guard t))
  (let ((w (fn-held-withdrawn h)))
    (list (fn-cp-u64 (fn-held-sequence h)) (fn-cp-u64 (fn-held-txid h))
          (fn-cp-u64 (fn-held-generation h))
          (if (fn-cp-smallp (fn-held-payload h)) (fn-held-payload h) 0)
          (fn-cp-u64 (fn-held-charge h)) (fn-cp-u64 (fn-held-stamp h))
          (fn-cp-msgid-octets h)
          (consp w)
          (if (and (consp w) (fn-cp-smallp (car w))) (car w) 0)
          (if (and (consp w) (fn-cp-smallp (cdr w))) (cdr w) 0)
          (fn-cp-escapedp h)
          tree
          nums)))

(defthm fn-cp-tree-enc-of-row-t-of
  (implies (and (fn-sccb-treep (fn-cp-tree-of h)) (fn-sccb-treep (fn-held-numbers h)))
           (equal (fn-crow-tree-enc (fn-cp-row-t-of h (fn-cp-tree-of h) (fn-held-numbers h)))
                  (fn-cp-row-of h)))
  :hints (("Goal" :in-theory (e/d (fn-cp-row-of) (fn-cp-tree-of fn-sccb-treep fn-scc-program)))))

(local
 (defthm fn-cp-row-t-of-shape
   (and (true-listp (fn-cp-row-t-of h tree nums))
        (equal (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (fn-cp-row-t-of h tree nums)))))))))))))
               tree)
        (equal (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (fn-cp-row-t-of h tree nums))))))))))))))
               nums))
   :hints (("Goal" :in-theory (enable fn-cp-row-t-of)))))

; A row appended at the count: the columns appended, the overflow cells
; grown as the old rows array was and the cell written.  Executed, the
; remainder is walked into the pool (NAME-APPEND-T) and its encodability
; checked without an octet list (adt-tree-okp): before it the commit
; consed the program by nested `append' and checked it twice, 38 KB a
; commit (lane paged-catalog-3's measurement in its LANEDUMP).
(defun fn-cat$p-append-row (h fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (fn-cat$p-wfp fn-cat$p)
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (e/d (fn-cp-overflow-of adt-tree-okp-is-sccb-treep)
                                                 (fn-cp-row-of fn-cp-row-t-of fn-cp-tree-of
                                                  fn-sccb-treep fn-cat-rowp))))))
  (let* ((tree (fn-cp-tree-of h))
         (nums (fn-held-numbers h))
         (ok (and (adt-tree-okp tree) (adt-tree-okp nums))))
    (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
               (fn-crow fn-cat$c)
               (let* ((seq (fn-cat$c-count fn-cat$c))
                      (fn-crow (mbe :logic (fn-crow-append (fn-cp-row-of h) fn-crow)
                                    :exec (if ok
                                              (fn-crow-append-t (fn-cp-row-t-of h tree nums) fn-crow)
                                            (fn-crow-append (fn-cp-row-of h) fn-crow))))
                      (fn-cat$c (if (< seq (fn-cat$c-rows-length fn-cat$c))
                                    fn-cat$c
                                  (resize-fn-cat$c-rows (+ 1 (* 2 seq)) fn-cat$c)))
                      (fn-cat$c (update-fn-cat$c-rowsi
                                 seq (mbe :logic (fn-cp-overflow-of h)
                                          :exec (if (and ok (fn-cat-rowp h)) nil h))
                                 fn-cat$c)))
                 (mv fn-crow fn-cat$c))
               fn-cat$p)))

; --- the Message-ID reader (the old fn-cat$c-confirm / -scan-msgid /
; -msgid-seqs over the paged rows)

(defun fn-cat$p-confirm (msgid seqs fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (and (fn-cat$p-wfp fn-cat$p) (nat-listp seqs))))
  (if (consp seqs)
      (let ((rest (fn-cat$p-confirm msgid (cdr seqs) fn-cat$p)))
        (if (and (< (car seqs) (fn-cat$p-count fn-cat$p))
                 (equal msgid (fn-record-msgid (fn-cat$p-at (car seqs) fn-cat$p))))
            (cons (car seqs) rest)
          rest))
    nil))

(defun fn-cat$p-scan-msgid (msgid i acc fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (and (fn-cat$p-wfp fn-cat$p) (natp i) (true-listp acc))
                  :measure (nfix (- (nfix (fn-cat$p-count fn-cat$p)) (nfix i)))))
  (if (>= (nfix i) (nfix (fn-cat$p-count fn-cat$p)))
      (revappend acc nil)
    (fn-cat$p-scan-msgid msgid (1+ (nfix i))
                         (if (equal msgid (fn-record-msgid (fn-cat$p-at (nfix i) fn-cat$p)))
                             (cons (nfix i) acc)
                           acc)
                         fn-cat$p)))

(defun fn-cat$p-msgid-seqs (msgid fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (fn-cat$p-wfp fn-cat$p)))
  (let ((seqs (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
                         (seqs)
                         (if (eql 0 (fn-cat$c-unplaced fn-cat$c))
                             (stobj-let ((fn-mpxt (fn-cat$c-mpx fn-cat$c)))
                                        (seqs)
                                        (if (fn-mpxt-wfp fn-mpxt)
                                            (fn-mpxt-candidates (fn-mpxt-tag msgid (fn-mpxt-key-octets fn-mpxt)) fn-mpxt)
                                          nil)
                                        seqs)
                           :scan)
                         seqs)))
    (if (eq seqs :scan)
        (fn-cat$p-scan-msgid msgid 0 nil fn-cat$p)
      (fn-cat$p-confirm msgid seqs fn-cat$p))))

; --- the table readers: the old executables on the nested tables

(defun fn-cat$p-group-number (group n fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (x) (fn-cat$c-group-number group n fn-cat$c) x))

(defun fn-cat$p-group-next (group fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (x) (fn-cat$c-group-next group fn-cat$c) x))

(defun fn-cat$p-group-count (group fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (x) (fn-cat$c-group-count group fn-cat$c) x))

(defun fn-cat$p-total-octets (fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (x) (fn-cat$c-total-octets fn-cat$c) x))

; A present withdrawal is an (at . by) pair of naturals (books/catalog.lisp's
; fn-ctg-withdrawn-present-is-pair, local there), forward only.
(local
 (defthm fn-cp-withdrawn-present-is-pair
   (implies (and (fn-held-withdrawnp w) w)
            (and (consp w) (natp (car w)) (natp (cdr w))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-held-withdrawnp)))))

(defun fn-cat$p-visible-at (seq v fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp seq) (natp v)
                              (< seq (fn-cat$p-count fn-cat$p))
                              (fn-held-withdrawnp (fn-cat$p-withdrawn-of seq fn-cat$p)))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable fn-cat$p-withdrawn-of)))))
  (and (< seq v)
       (let ((w (fn-cat$p-withdrawn-of seq fn-cat$p)))
         (or (null w) (<= v (car w))))))

(defun fn-cat$p-group-live-count (group fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (x) (fn-cat$c-group-live-count group fn-cat$c) x))

(defun fn-cat$p-group-live-low (group fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (x) (fn-cat$c-group-live-low group fn-cat$c) x))

(defun fn-cat$p-group-live-high (group fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (x) (fn-cat$c-group-live-high group fn-cat$c) x))

(defun fn-cat$p-horizon (fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (x) (fn-cat$c-horizon fn-cat$c) x))

(defun fn-cat$p-withdrawn-at (w fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (fn-cpt-list (fn-cat$p-wbv-get w fn-cat$p)))

; The rows below the count as a list (the logic function's argument when the
; executable must not trust its own table: the old fn-cat$c-rows-below-count).
(defun fn-cat$p-rows-list (i acc fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp i) (<= i (fn-cat$p-count fn-cat$p))
                              (true-listp acc))))
  (if (zp i)
      acc
    (fn-cat$p-rows-list (1- i) (cons (fn-cat$p-at (1- i) fn-cat$p) acc) fn-cat$p)))

(defun fn-cat$p-rows-below-count (fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (fn-cat$p-wfp fn-cat$p)))
  (fn-cat$p-rows-list (fn-cat$p-count fn-cat$p) nil fn-cat$p))

(local
 (defthm fn-cp-rows-list-true-listp
   (implies (true-listp acc)
            (true-listp (fn-cat$p-rows-list i acc fn-cat$p)))
   :hints (("Goal" :induct (fn-cat$p-rows-list i acc fn-cat$p)))))

(local
 (defthm fn-cp-rows-below-count-true-listp
   (true-listp (fn-cat$p-rows-below-count fn-cat$p))
   :hints (("Goal" :in-theory (enable fn-cat$p-rows-below-count)))))

(defun fn-cat$p-msgid-saturatedp (key msgid fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p)
                              (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-saturatedp fn-mpxt-key-samep
                                                            fn-cat$p-rows-list fn-mpxt-key-samep-is-equal
                                                            fn-cat$p-rows-below-count fn-mpxtp fn-crowp fn-cat$cp)
                                 :do-not-induct t))))
  (let ((own (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
                        (own)
                        (stobj-let ((fn-mpxt (fn-cat$c-mpx fn-cat$c)))
                                   (own)
                                   (if (and (fn-mpxt-wfp fn-mpxt) (fn-mpxt-key-samep key fn-mpxt))
                                       (if (fn-mpxt-saturatedp (fn-mpxt-tag msgid key) fn-mpxt) :saturated :open)
                                     :other-key)
                                   own)
                        own)))
    (if (eq own :other-key)
        (fn-mpxt-build-saturatedp key msgid (fn-cat$p-rows-below-count fn-cat$p))
      (or (>= (+ 2 (fn-cat$p-count fn-cat$p)) *fn-mpxt-word-limit*)
          (eq own :saturated)))))

(defun fn-cat$p-index-health (key fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p)
                              (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-saturatedp fn-mpxt-key-samep
                                                            fn-cat$p-rows-list fn-mpxt-key-samep-is-equal
                                                            fn-cat$p-rows-below-count fn-mpxtp fn-crowp fn-cat$cp)
                                 :do-not-induct t))))
  (let ((own (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
                        (own)
                        (stobj-let ((fn-mpxt (fn-cat$c-mpx fn-cat$c)))
                                   (own)
                                   (if (and (fn-mpxt-wfp fn-mpxt) (fn-mpxt-key-samep key fn-mpxt))
                                       (list (fn-mpxt-pages fn-mpxt) (fn-mpxt-count fn-mpxt) (fn-mpxt-stuck fn-mpxt))
                                     nil)
                                   own)
                        own)))
    (if (consp own)
        (list (car own) (cadr own)
              (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (u) (fn-cat$c-unplaced fn-cat$c) u)
              (caddr own))
      (fn-mpxt-build-health key (fn-cat$p-rows-below-count fn-cat$p)))))

; --- the writes

(local
 (defthm fn-cp-octets-of-apply-plan
   (equal (nth *fn-cat$c-octets* (fn-cat$c-apply-plan plan seq c))
          (nth *fn-cat$c-octets* c))
   :hints (("Goal" :in-theory (enable fn-cat$c-apply-plan fn-cat$c-numbers-put fn-cat$c-groups-put)))))

; The commit's table steps, each one stobj-let over the nested tables.
(defun fn-cat$p-tab-index-add (msgid seq fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (natp seq)))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (fn-cat$c)
             (fn-cat$c-index-add msgid seq fn-cat$c)
             fn-cat$p))

(defun fn-cat$p-tab-commit (plan lplan hz seq h fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (and (natp seq) (natp hz))))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (fn-cat$c)
             (let* ((fn-cat$c (fn-cat$c-apply-plan plan seq fn-cat$c))
                    (fn-cat$c (update-fn-cat$c-octets
                               (+ (fn-cat$c-octets fn-cat$c)
                                  (nfix (fn-hf-octets (fn-held-facts h))))
                               fn-cat$c))
                    (fn-cat$c (update-fn-cat$c-count (+ 1 seq) fn-cat$c))
                    (fn-cat$c (fn-cat$c-live-apply lplan fn-cat$c)))
               (update-fn-cat$c-hz hz fn-cat$c))
             fn-cat$p))

(local
 (defthm fn-cp-wfp-of-tab-index-add
   (implies (fn-cat$p-wfp fn-cat$p)
            (fn-cat$p-wfp (fn-cat$p-tab-index-add m s fn-cat$p)))
   :hints (("Goal" :in-theory (enable fn-cat$p-tab-index-add)))))

; The commit's live links (books/catalog-live-links.lisp fn-cpl-cplan,
; fn-cpl-link), read before any write: per group whose new number n is
; live, (g n hi) with hi the group's live high.
(defun fn-cat$p-cplan (groups livep fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (if (consp groups)
      (let* ((g (car groups)) (n (fn-cat$p-group-next g fn-cat$p)))
        (if (and livep (natp n) (<= n *fn-nntp-max-article-number*))
            (cons (list g n (fn-cat$p-group-live-high g fn-cat$p))
                  (fn-cat$p-cplan (cdr groups) livep fn-cat$p))
          (fn-cat$p-cplan (cdr groups) livep fn-cat$p)))
    nil))

(defun fn-cat$p-link (plan fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (true-list-listp plan)))
  (if (consp plan)
      (let* ((e (car plan)) (g (car e)) (n (cadr e)) (hi (caddr e))
             (fn-cat$p (if (posp hi) (fn-cat$p-lnext-put (cons g hi) n fn-cat$p) fn-cat$p))
             (fn-cat$p (fn-cat$p-lnext-put (cons g n) 0 fn-cat$p))
             (fn-cat$p (fn-cat$p-lprev-put (cons g n) hi fn-cat$p)))
        (fn-cat$p-link (cdr plan) fn-cat$p))
    fn-cat$p))

(defthm fn-cp-true-list-listp-of-cplan
  (true-list-listp (fn-cat$p-cplan groups livep fn-cat$p)))

(defun fn-cat$p-commit-w (h fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (fn-cat$p-wfp fn-cat$p)
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable fn-cat$p-tab-index-add fn-cat$p-tab-commit
                                                     fn-cat$p-append-row fn-cat$p-wfp
                                                     fn-cat$c-live-plan fn-cat$c-plan)))))
  (let* ((seq (fn-cat$p-count fn-cat$p))
         (x (fn-held-withdrawn h))
         (lplan (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
                           (lp)
                           (fn-cat$c-live-plan (fn-record-groups h)
                                               (and (null x) (fn-scat-msgid-idp (fn-record-msgid h)))
                                               fn-cat$c)
                           lp))
         (hz (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
                        (hz)
                        (max (fn-cat$c-hz fn-cat$c) (if (consp x) (+ 1 (nfix (car x))) 0))
                        hz))
         (plan (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
                          (plan)
                          (fn-cat$c-plan (fn-record-groups h) fn-cat$c)
                          plan))
         (row (fn-held-with-numbers h (fn-cat-plan-numbers plan)))
         (cplan (fn-cat$p-cplan (fn-record-groups h)
                                (and (null x) (fn-scat-msgid-idp (fn-record-msgid h)))
                                fn-cat$p))
         (fn-cat$p (fn-cat$p-tab-index-add (fn-record-msgid h) seq fn-cat$p))
         (fn-cat$p (fn-cat$p-append-row row fn-cat$p))
         (fn-cat$p (fn-cat$p-tab-commit plan lplan hz seq h fn-cat$p))
         (fn-cat$p (fn-cat$p-link cplan fn-cat$p)))
    (if (consp x)
        (fn-cat$p-wbv-put (car x) (fn-cpt-add seq (fn-cat$p-wbv-get (car x) fn-cat$p)) fn-cat$p)
      fn-cat$p)))

; The liveness probe and the neighbours, from the link tables
; (books/catalog-live-links.lisp): (group . number) is bound in NEXT exactly
; when it is live (fn-cpl-coverp: live => bound; fn-cpl-okp: bound => live),
; and a live number's entry is its neighbour -- both carried in
; fn-cat$pcorr, so no executable here scans the rows or decodes one
; (KEYSTONES fn-cat$p-livep-is-live, fn-cat$p-next-is-probe,
; fn-cat$p-prev-is-probe).  On a state that does not correspond the probes
; answer as the tables say; the correspondence is what makes them right.
(defun fn-cat$p-livep (group k fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (natp (fn-cat$p-lnext-get (cons group k) fn-cat$p)))

(defun fn-cat$p-next (group k fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (nfix (fn-cat$p-lnext-get (cons group k) fn-cat$p)))

(defun fn-cat$p-prev (group k fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (nfix (fn-cat$p-lprev-get (cons group k) fn-cat$p)))

(defun fn-cat$p-drop-entry (group k fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (let* ((count (fn-cat$p-group-live-count group fn-cat$p))
         (low (fn-cat$p-group-live-low group fn-cat$p))
         (high (fn-cat$p-group-live-high group fn-cat$p)))
    (cons (nfix (- count 1))
          (cons (if (equal low k) (fn-cat$p-next group k fn-cat$p) low)
                (if (equal high k) (fn-cat$p-prev group k fn-cat$p) high)))))

; The withdrawal's plans over the row's bindings PAIRS (its numbers column),
; read before any write: per binding (g . k) the numbers table answers with
; the row and that is live (the probe) -- the old fn-cat$c-drop-plan's
; filter, which read the row, decided on a corresponding state by two
; probes.  The drop plan feeds the live summary (fn-cat$c-live-apply), the
; link plan the unlink (books/catalog-live-links.lisp fn-cpl-wplan: (g k prev
; next)).
(defun fn-cat$p-drop-plan (pairs target fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (if (consp pairs)
      (let* ((p (car pairs))
             (g (fn-cbor-ag-car p))
             (k (fn-cbor-ag-cdr p)))
        (if (and (consp p)
                 (equal (fn-cat$p-group-number g k fn-cat$p) target)
                 (fn-cat$p-livep g k fn-cat$p))
            (cons (cons g (fn-cat$p-drop-entry g k fn-cat$p))
                  (fn-cat$p-drop-plan (cdr pairs) target fn-cat$p))
          (fn-cat$p-drop-plan (cdr pairs) target fn-cat$p)))
    nil))

(defun fn-cat$p-wplan (pairs target fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (if (consp pairs)
      (let* ((p (car pairs))
             (g (fn-cbor-ag-car p))
             (k (fn-cbor-ag-cdr p)))
        (if (and (consp p)
                 (equal (fn-cat$p-group-number g k fn-cat$p) target)
                 (fn-cat$p-livep g k fn-cat$p))
            (cons (list g k (fn-cat$p-prev g k fn-cat$p) (fn-cat$p-next g k fn-cat$p))
                  (fn-cat$p-wplan (cdr pairs) target fn-cat$p))
          (fn-cat$p-wplan (cdr pairs) target fn-cat$p)))
    nil))

(defthm fn-cp-true-list-listp-of-wplan
  (true-list-listp (fn-cat$p-wplan pairs target fn-cat$p)))

(defun fn-cat$p-unlink (plan fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (true-list-listp plan)))
  (if (consp plan)
      (let* ((e (car plan)) (g (car e)) (k (cadr e)) (pv (caddr e)) (n (cadddr e))
             (fn-cat$p (fn-cat$p-lnext-rem (cons g k) fn-cat$p))
             (fn-cat$p (if (posp pv) (fn-cat$p-lnext-put (cons g pv) n fn-cat$p) fn-cat$p))
             (fn-cat$p (fn-cat$p-lprev-rem (cons g k) fn-cat$p))
             (fn-cat$p (if (posp n) (fn-cat$p-lprev-put (cons g n) pv fn-cat$p) fn-cat$p)))
        (fn-cat$p-unlink (cdr plan) fn-cat$p))
    fn-cat$p))

; The withdrawal's table step (one stobj-let over the nested tables).
(defun fn-cat$p-tab-withdraw (dplan hz fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (natp hz)))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (fn-cat$c)
             (let ((fn-cat$c (fn-cat$c-live-apply dplan fn-cat$c)))
               (update-fn-cat$c-hz hz fn-cat$c))
             fn-cat$p))

; The withdrawal of row TARGET at version count, by BY.  Its row reads are
; the three withdrawal columns (fn-cat$p-withdrawn-of) and the numbers
; column (fn-cat$p-numbers-of); every liveness and neighbour question is a
; table probe; the remainder in the pool is never decoded (D27: the step's
; allocation is the plans and the trie path, not the row).
(defun fn-cat$p-withdraw-w (target by fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp target) (natp by)
                              (< target (fn-cat$p-count fn-cat$p)))))
  (if (null (fn-cat$p-withdrawn-of target fn-cat$p))
      (let* ((v (fn-cat$p-count fn-cat$p))
             (pairs (fn-cat$p-numbers-of target fn-cat$p))
             (dplan (fn-cat$p-drop-plan pairs target fn-cat$p))
             (hz (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
                            (hz)
                            (max (fn-cat$c-hz fn-cat$c) (+ 1 (fn-cat$c-count fn-cat$c)))
                            hz))
             (wplan (fn-cat$p-wplan pairs target fn-cat$p))
             (fn-cat$p (fn-cat$p-set-withdrawn target (cons v by) fn-cat$p))
             (fn-cat$p (fn-cat$p-tab-withdraw dplan hz fn-cat$p))
             (fn-cat$p (fn-cat$p-unlink wplan fn-cat$p)))
        (fn-cat$p-wbv-put v (fn-cpt-add target (fn-cat$p-wbv-get v fn-cat$p)) fn-cat$p))
    fn-cat$p))

(defun fn-cat$p-redecide (seq context fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp seq) (< seq (fn-cat$p-count fn-cat$p)))))
  (fn-cat$p-set-cell seq (fn-held-with-context (fn-cat$p-at seq fn-cat$p) context) fn-cat$p))

(defun fn-cat$p-clear-w (fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (let ((fn-cat$p
          (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
                     (fn-crow fn-cat$c)
                     (let* ((fn-crow (fn-crow-clear fn-crow))
                            (fn-cat$c (fn-cat$c-clear-w fn-cat$c)))
                       (mv fn-crow fn-cat$c))
                     fn-cat$p)))
    (let* ((fn-cat$p (fn-cat$p-lnext-clear fn-cat$p))
           (fn-cat$p (fn-cat$p-lprev-clear fn-cat$p)))
      (fn-cat$p-wbv-clear fn-cat$p))))

(defun fn-cat$p-clear-keyed (key fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))))
  (let ((fn-cat$p
          (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
                     (fn-crow fn-cat$c)
                     (let* ((fn-crow (fn-crow-clear fn-crow))
                            (fn-cat$c (fn-cat$c-clear-keyed key fn-cat$c)))
                       (mv fn-crow fn-cat$c))
                     fn-cat$p)))
    (let* ((fn-cat$p (fn-cat$p-lnext-clear fn-cat$p))
           (fn-cat$p (fn-cat$p-lprev-clear fn-cat$p)))
      (fn-cat$p-wbv-clear fn-cat$p))))


; -----------------------------------------------------------------------------
; 6. The simulation: each paged executable, through the view, is the old
; executable on the view.  First the old executables' blindness to the rows
; array (position 0 of the old foundation): a table operation on a state
; whose rows are replaced is the operation, then the replacement.

(local
 (defthm fn-cp-update-nth-0-commute
   (implies (and (natp k) (not (equal k 0)))
            (equal (update-nth k v (update-nth 0 r c))
                   (update-nth 0 r (update-nth k v c))))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-cp-update-nth-0-0
   (equal (update-nth 0 r (update-nth 0 r2 c)) (update-nth 0 r c))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-cp-nth-0-of-update-nth-0
   (equal (nth 0 (update-nth 0 r c)) r)))

; The frame: the view replaces positions 0 (rows) and 8 (withdrawals by
; version) of the old foundation; every old table operation but the
; withdrawals' commutes with it.
(local
 (defun fn-cp-un2-ind (i j c)
   (if (or (zp i) (zp j)) c (fn-cp-un2-ind (1- i) (1- j) (cdr c)))))

(local
 (defthm fn-cp-update-nth-commute-any
   (implies (and (natp i) (natp j) (not (equal i j)))
            (equal (update-nth i v (update-nth j w c))
                   (update-nth j w (update-nth i v c))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-cp-un2-ind i j c) :in-theory (enable update-nth)))))

(local
 (defthm fn-cp-update-nth-8-commute
   (implies (and (natp k) (not (equal k 0)) (not (equal k 8)))
            (equal (update-nth k v (update-nth 8 w c))
                   (update-nth 8 w (update-nth k v c))))
   :hints (("Goal" :use ((:instance fn-cp-update-nth-commute-any (i k) (j 8)))))))

(local
 (defthm fn-cp-update-nth-same
   (equal (update-nth i x (update-nth i y l)) (update-nth i x l))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local (in-theory (enable fn-cp-frame)))

; The old foundation's primitives, opened once here.
(local (in-theory (enable fn-cat$c-count update-fn-cat$c-count fn-cat$c-rowsi update-fn-cat$c-rowsi
                          fn-cat$c-rows-length resize-fn-cat$c-rows fn-cat$c-octets update-fn-cat$c-octets
                          fn-cat$c-mpx update-fn-cat$c-mpx fn-cat$c-mpx2 update-fn-cat$c-mpx2
                          fn-cat$c-unplaced update-fn-cat$c-unplaced fn-cat$c-hz update-fn-cat$c-hz
                          fn-cat$c-numbers-get fn-cat$c-numbers-put fn-cat$c-numbers-clear
                          fn-cat$c-groups-get fn-cat$c-groups-put fn-cat$c-groups-clear
                          fn-cat$c-lives-get fn-cat$c-lives-put fn-cat$c-lives-clear
                          fn-cat$c-wbv-get fn-cat$c-wbv-put fn-cat$c-wbv-clear)))

(local
 (defthm fn-cp-readers-blind
   (and (equal (fn-cat$c-count (fn-cp-frame r wb c)) (fn-cat$c-count c))
        (equal (fn-cat$c-octets (fn-cp-frame r wb c)) (fn-cat$c-octets c))
        (equal (fn-cat$c-mpx (fn-cp-frame r wb c)) (fn-cat$c-mpx c))
        (equal (fn-cat$c-mpx2 (fn-cp-frame r wb c)) (fn-cat$c-mpx2 c))
        (equal (fn-cat$c-unplaced (fn-cp-frame r wb c)) (fn-cat$c-unplaced c))
        (equal (fn-cat$c-hz (fn-cp-frame r wb c)) (fn-cat$c-hz c))
        (equal (fn-cat$c-numbers-get k (fn-cp-frame r wb c)) (fn-cat$c-numbers-get k c))
        (equal (fn-cat$c-groups-get k (fn-cp-frame r wb c)) (fn-cat$c-groups-get k c))
        (equal (fn-cat$c-lives-get k (fn-cp-frame r wb c)) (fn-cat$c-lives-get k c))
        (equal (fn-cat$c-wbv-get k (fn-cp-frame r wb c)) (cdr (hons-assoc-equal k wb)))
        (equal (fn-cat$c-rowsi i (fn-cp-frame r wb c)) (nth i r))
        (equal (fn-cat$c-rows-length (fn-cp-frame r wb c)) (len r)))))

(local
 (defthm fn-cp-writers-blind
   (and (equal (update-fn-cat$c-count n (fn-cp-frame r wb c)) (fn-cp-frame r wb (update-fn-cat$c-count n c)))
        (equal (update-fn-cat$c-octets n (fn-cp-frame r wb c)) (fn-cp-frame r wb (update-fn-cat$c-octets n c)))
        (equal (update-fn-cat$c-mpx x (fn-cp-frame r wb c)) (fn-cp-frame r wb (update-fn-cat$c-mpx x c)))
        (equal (update-fn-cat$c-mpx2 x (fn-cp-frame r wb c)) (fn-cp-frame r wb (update-fn-cat$c-mpx2 x c)))
        (equal (update-fn-cat$c-unplaced n (fn-cp-frame r wb c)) (fn-cp-frame r wb (update-fn-cat$c-unplaced n c)))
        (equal (update-fn-cat$c-hz n (fn-cp-frame r wb c)) (fn-cp-frame r wb (update-fn-cat$c-hz n c)))
        (equal (fn-cat$c-numbers-put k v (fn-cp-frame r wb c)) (fn-cp-frame r wb (fn-cat$c-numbers-put k v c)))
        (equal (fn-cat$c-groups-put k v (fn-cp-frame r wb c)) (fn-cp-frame r wb (fn-cat$c-groups-put k v c)))
        (equal (fn-cat$c-lives-put k v (fn-cp-frame r wb c)) (fn-cp-frame r wb (fn-cat$c-lives-put k v c)))
        (equal (fn-cat$c-wbv-put k v (fn-cp-frame r wb c)) (fn-cp-frame r (cons (cons k v) wb) c))
        (equal (fn-cat$c-numbers-clear (fn-cp-frame r wb c)) (fn-cp-frame r wb (fn-cat$c-numbers-clear c)))
        (equal (fn-cat$c-groups-clear (fn-cp-frame r wb c)) (fn-cp-frame r wb (fn-cat$c-groups-clear c)))
        (equal (fn-cat$c-lives-clear (fn-cp-frame r wb c)) (fn-cp-frame r wb (fn-cat$c-lives-clear c)))
        (equal (fn-cat$c-wbv-clear (fn-cp-frame r wb c)) (fn-cp-frame r nil c))
        (equal (update-fn-cat$c-rowsi i v (fn-cp-frame r wb c)) (fn-cp-frame (update-nth i v r) wb c))
        (equal (resize-fn-cat$c-rows n (fn-cp-frame r wb c)) (fn-cp-frame (resize-list r n nil) wb c)))))

; The derived readers and writers of books/catalog.lisp, each by its definition.
(local
 (defthm fn-cp-plan-blind
   (equal (fn-cat$c-plan groups (fn-cp-frame r wb c)) (fn-cat$c-plan groups c))
   :hints (("Goal" :in-theory (enable fn-cat$c-plan)))))

(local
 (defthm fn-cp-live-plan-blind
   (equal (fn-cat$c-live-plan groups livep (fn-cp-frame r wb c)) (fn-cat$c-live-plan groups livep c))
   :hints (("Goal" :in-theory (enable fn-cat$c-live-plan fn-cat$c-group-live-count
                                      fn-cat$c-group-live-low fn-cat$c-group-live-high)))))

(local
 (defthm fn-cp-apply-plan-blind
   (equal (fn-cat$c-apply-plan plan seq (fn-cp-frame r wb c))
          (fn-cp-frame r wb (fn-cat$c-apply-plan plan seq c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-apply-plan)))))

(local
 (defthm fn-cp-live-apply-blind
   (equal (fn-cat$c-live-apply plan (fn-cp-frame r wb c))
          (fn-cp-frame r wb (fn-cat$c-live-apply plan c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-live-apply)))))

(local
 (defthm fn-cp-index-add-blind
   (equal (fn-cat$c-index-add m seq (fn-cp-frame r wb c))
          (fn-cp-frame r wb (fn-cat$c-index-add m seq c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-index-add)))))

(local
 (defthm fn-cp-index-clear-blind
   (equal (fn-cat$c-index-clear (fn-cp-frame r wb c))
          (fn-cp-frame r wb (fn-cat$c-index-clear c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-index-clear)))))

(local
 (defthm fn-cp-index-set-key-blind
   (equal (fn-cat$c-index-set-key key (fn-cp-frame r wb c))
          (fn-cp-frame r wb (fn-cat$c-index-set-key key c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-index-set-key)))))

(local
 (defthm fn-cp-simple-readers-blind
   (and (equal (fn-cat$c-group-number g n (fn-cp-frame r wb c)) (fn-cat$c-group-number g n c))
        (equal (fn-cat$c-group-next g (fn-cp-frame r wb c)) (fn-cat$c-group-next g c))
        (equal (fn-cat$c-group-count g (fn-cp-frame r wb c)) (fn-cat$c-group-count g c))
        (equal (fn-cat$c-total-octets (fn-cp-frame r wb c)) (fn-cat$c-total-octets c))
        (equal (fn-cat$c-group-live-count g (fn-cp-frame r wb c)) (fn-cat$c-group-live-count g c))
        (equal (fn-cat$c-group-live-low g (fn-cp-frame r wb c)) (fn-cat$c-group-live-low g c))
        (equal (fn-cat$c-group-live-high g (fn-cp-frame r wb c)) (fn-cat$c-group-live-high g c))
        (equal (fn-cat$c-horizon (fn-cp-frame r wb c)) (fn-cat$c-horizon c))
        (equal (fn-cat$c-withdrawn-at w (fn-cp-frame r wb c)) (cdr (hons-assoc-equal w wb)))
        (equal (fn-cat$c-wfp (fn-cp-frame r wb c)) (<= (fn-cat$c-count c) (len r))))
   :hints (("Goal" :in-theory (enable fn-cat$c-group-number fn-cat$c-group-next fn-cat$c-group-count
                                      fn-cat$c-total-octets fn-cat$c-group-live-count
                                      fn-cat$c-group-live-low fn-cat$c-group-live-high
                                      fn-cat$c-horizon fn-cat$c-withdrawn-at fn-cat$c-wfp)))))


(local (in-theory (disable fn-cp-frame fn-cp-update-nth-8-commute)))

(local
 (defthm fn-cp-nth-of-frame
   (and (equal (nth 0 (fn-cp-frame r wb c)) r)
        (equal (nth 8 (fn-cp-frame r wb c)) wb)
        (implies (and (natp i) (not (equal i 0)) (not (equal i 8)))
                 (equal (nth i (fn-cp-frame r wb c)) (nth i c))))
   :hints (("Goal" :in-theory (enable fn-cp-frame)))))

(local
 (defthm fn-cp-frame-frame
   (equal (fn-cp-frame r wb (fn-cp-frame r2 wb2 c)) (fn-cp-frame r wb c))
   :hints (("Goal" :in-theory (enable fn-cp-frame)))))

(local
 (defthm fn-cp-update-nth-of-frame
   (implies (and (natp k) (not (equal k 0)) (not (equal k 8)))
            (equal (update-nth k v (fn-cp-frame r wb c))
                   (fn-cp-frame r wb (update-nth k v c))))
   :hints (("Goal" :in-theory (enable fn-cp-frame fn-cp-update-nth-8-commute)))))

(local
 (defthm fn-cp-frame-of-update-nth-0
   (equal (fn-cp-frame r wb (update-nth 0 x c)) (fn-cp-frame r wb c))
   :hints (("Goal" :in-theory (enable fn-cp-frame)))))

(local
 (defthm fn-cp-frame-of-update-nth-8
   (equal (fn-cp-frame r wb (update-nth 8 x c)) (fn-cp-frame r wb c))
   :hints (("Goal" :in-theory (enable fn-cp-frame)))))

(local
 (defthm fn-cp-update-nth-0-of-frame
   (equal (update-nth 0 r (fn-cp-frame r2 wb c)) (fn-cp-frame r wb c))
   :hints (("Goal" :in-theory (enable fn-cp-frame)))))

; --- the rows of the view

(local
 (defthm fn-cp-len-of-merge
   (equal (len (fn-cp-merge crow ovf)) (len ovf))
   :hints (("Goal" :in-theory (enable fn-cp-merge)))))

(local
 (defthm fn-cp-true-listp-of-merge
   (true-listp (fn-cp-merge crow ovf))
   :hints (("Goal" :in-theory (enable fn-cp-merge)))))

(local
 (defthm fn-cp-nth-of-merge
   (implies (and (natp i) (< i (len ovf)))
            (equal (nth i (fn-cp-merge crow ovf))
                   (if (and (< i (len crow)) (null (nth i ovf)))
                       (fn-cp-row-held (nth i crow))
                     (nth i ovf))))
   :hints (("Goal" :in-theory (enable fn-cp-merge nth)))))

; A row written at I below both lengths: the merge updated at I.
(local
 (defthm fn-cp-merge-of-put
   (implies (and (natp i) (< i (len crow)) (<= (len crow) (len ovf)) (true-listp ovf)
                 (if o (equal o row) (equal (fn-cp-row-held r) row)))
            (equal (fn-cp-merge (update-nth i r crow) (update-nth i o ovf))
                   (update-nth i row (fn-cp-merge crow ovf))))
   :hints (("Goal" :in-theory (enable fn-cp-merge update-nth)))))

; A row appended at the count (the length of CROW), the cells grown first.
(local
 (defun fn-cp-resize-ind (crow ovf n)
   (if (and (integerp n) (> n 0))
       (fn-cp-resize-ind (cdr crow) (if (atom ovf) ovf (cdr ovf)) (1- n))
     (list crow ovf))))

(local
 (defthm fn-cp-merge-of-nil-tail
   (implies (atom crow)
            (equal (fn-cp-merge crow (resize-list nil n nil)) (resize-list nil n nil)))
   :hints (("Goal" :in-theory (enable fn-cp-merge resize-list)))))

(local
 (defthm fn-cp-merge-of-resize
   (implies (and (<= (len crow) (len ovf)) (true-listp ovf))
            (equal (fn-cp-merge crow (resize-list ovf n nil))
                   (resize-list (fn-cp-merge crow ovf) n nil)))
   :hints (("Goal" :in-theory (enable fn-cp-merge resize-list)
            :induct (fn-cp-resize-ind crow ovf n)))))

(local
 (defthm fn-cp-merge-of-append
   (implies (and (equal (len crow) i) (natp i) (< i (len ovf)) (true-listp ovf)
                 (if o (equal o row) (equal (fn-cp-row-held r) row)))
            (equal (fn-cp-merge (append crow (list r)) (update-nth i o ovf))
                   (update-nth i row (fn-cp-merge crow ovf))))
   :hints (("Goal" :in-theory (enable fn-cp-merge update-nth)))))

; --- what the correspondence gives, once

(local
 (defthm fn-cp-rows-corr-nth
   (implies (and (fn-cat-rows-corr n a rows) (natp i) (< i (nfix n)))
            (equal (nth i rows) (nth i a)))
   :hints (("Goal" :in-theory (enable fn-cat-rows-corr)))))

(local
 (defthm fn-cp-corr-facts
   (implies (fn-cat$pcorr fn-cat$p fn-cat$a)
            (and (fn-cat$cp (fn-cat$p-view fn-cat$p))
                 (fn-cat-rowsp fn-cat$a)
                 (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (equal (nth 1 (nth 1 fn-cat$p)) (len fn-cat$a))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (fn-cat-rows-corr (len fn-cat$a) fn-cat$a
                                   (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p))))
                 (fn-cat$corr-w (fn-cat$p-view fn-cat$p) fn-cat$a)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cat$pcorr fn-cat$p-view fn-cat$corr-w fn-cat$corr
                                      fn-cat$corr-base)))))

; The row at SEQ of the view is the logical row.
(local
 (defthm fn-cp-view-row
   (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (natp seq) (< seq (len fn-cat$a)))
            (equal (nth seq (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p))))
                   (nth seq fn-cat$a)))
   :hints (("Goal" :use ((:instance fn-cp-rows-corr-nth (n (len fn-cat$a)) (a fn-cat$a) (i seq)
                                    (rows (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p))))))
            :in-theory (disable fn-cp-rows-corr-nth)))))

; The correspondence stays closed below: its facts come forward once (fn-cp-corr-facts).
(local (in-theory (disable fn-cat$pcorr fn-cat$corr-w fn-cat$corr fn-cat$corr-base fn-cat$corr-live
                           fn-cat$corr-wbv)))

; --- the readers

(local
 (defthm fn-cp-withdrawn-of-held
   (equal (fn-held-withdrawn (fn-cp-held s tx g p c st m wp wa wb e aux nums))
          (if e
              (adt-l-nth 1 (adt-l-nth 7 (fn-cp-decoded aux)))
            (if wp (cons wa wb) nil)))
   :hints (("Goal" :in-theory (e/d (fn-cp-held) (fn-cp-decoded fn-scc-decode-tree))))))

(local
 (defthm fn-cp-numbers-of-held
   (equal (fn-held-numbers (fn-cp-held s tx g p c st m wp wa wb e aux nums))
          (fn-cp-decoded nums))
   :hints (("Goal" :in-theory (e/d (fn-cp-held) (fn-cp-decoded fn-scc-decode-tree))))))

(local
 (defthm fn-cat$p-at-is-merge
   (implies (and (natp seq) (< seq (len (nth 0 fn-cat$p)))
                 (<= (len (nth 0 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-at seq fn-cat$p)
                   (nth seq (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p))))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-at fn-cp-row-held adt-l-nth-is-nth)
                                   (fn-cp-held fn-scc-decode-tree))))))

(local
 (defthm fn-cat$p-withdrawn-of-is-merge
   (implies (and (natp seq) (< seq (len (nth 0 fn-cat$p)))
                 (<= (len (nth 0 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-withdrawn-of seq fn-cat$p)
                   (fn-held-withdrawn (nth seq (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p)))))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-withdrawn-of fn-cp-row-held adt-l-nth-is-nth)
                                   (fn-cp-held fn-cp-decoded fn-scc-decode-tree))))))

(local
 (defthm fn-cat$p-numbers-of-is-merge
   (implies (and (natp seq) (< seq (len (nth 0 fn-cat$p)))
                 (<= (len (nth 0 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-numbers-of seq fn-cat$p)
                   (fn-held-numbers (nth seq (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p)))))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-numbers-of fn-cp-row-held adt-l-nth-is-nth)
                                   (fn-cp-held fn-cp-decoded fn-scc-decode-tree))))))

(local
 (defthm fn-cat$p-at-is-row
   (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (natp seq) (< seq (len fn-cat$a)))
            (equal (fn-cat$p-at seq fn-cat$p) (nth seq fn-cat$a)))
   :hints (("Goal" :in-theory (disable fn-cat$p-at fn-cat$p-withdrawn-of)))))

(local
 (defthm fn-cat$p-withdrawn-of-is-row
   (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (natp seq) (< seq (len fn-cat$a)))
            (equal (fn-cat$p-withdrawn-of seq fn-cat$p)
                   (fn-held-withdrawn (nth seq fn-cat$a))))
   :hints (("Goal" :in-theory (disable fn-cat$p-at fn-cat$p-withdrawn-of)))))

(local
 (defthm fn-cat$p-numbers-of-is-row
   (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (natp seq) (< seq (len fn-cat$a)))
            (equal (fn-cat$p-numbers-of seq fn-cat$p)
                   (fn-held-numbers (nth seq fn-cat$a))))
   :hints (("Goal" :in-theory (disable fn-cat$p-at fn-cat$p-withdrawn-of fn-cat$p-numbers-of)))))

(local
 (defthm fn-cp-nth-of-nfix
   (equal (nth (nfix i) x) (nth i x))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-cat$p-at-is-merge-any
   (implies (and (< (nfix seq) (len (nth 0 fn-cat$p)))
                 (<= (len (nth 0 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-at seq fn-cat$p)
                   (nth seq (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p))))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-at fn-cp-row-held adt-l-nth-is-nth)
                                   (fn-cp-held fn-scc-decode-tree fn-cp-nth-of-nfix fn-cat$p-at-is-merge))
            :use ((:instance fn-cat$p-at-is-merge (seq (nfix seq)))
                  (:instance fn-cp-nth-of-nfix (i seq) (x (nth 0 fn-cat$p)))
                  (:instance fn-cp-nth-of-nfix (i seq) (x (nth 0 (nth 1 fn-cat$p))))
                  (:instance fn-cp-nth-of-nfix (i seq) (x (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p)))))
                  (:instance fn-cp-nth-of-nfix (i seq) (x (nth (nfix seq) (nth 0 fn-cat$p))))
                  )))))

(local (in-theory (e/d (fn-cat$p-view) (fn-cat$p-at fn-cat$p-withdrawn-of fn-cat$p-numbers-of
                                          fn-cat$p-at-is-row fn-cat$p-withdrawn-of-is-row
                                          fn-cat$p-numbers-of-is-row fn-cp-view-row
                                          fn-cat$p-at-is-merge))))

(local
 (defthm fn-cat$p-count-sim
   (equal (fn-cat$p-count fn-cat$p) (fn-cat$c-count (fn-cat$p-view fn-cat$p)))
   :hints (("Goal" :in-theory (enable fn-cat$p-count)))))

(local
 (defthm fn-cat$p-visible-at-sim
   (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (natp seq) (< seq (len fn-cat$a)))
            (equal (fn-cat$p-visible-at seq v fn-cat$p)
                   (fn-cat$c-visible-at seq v (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-visible-at fn-cat$c-visible-at)))))

(local
 (defthm fn-cat$p-confirm-sim
   (implies (and (nat-listp seqs) (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-confirm msgid seqs fn-cat$p)
                   (fn-cat$c-confirm msgid seqs (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-confirm fn-cat$c-confirm)
            :induct (fn-cat$p-confirm msgid seqs fn-cat$p)))))


(local
 (defthm fn-cat$p-scan-msgid-sim-s
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-scan-msgid msgid i acc fn-cat$p)
                   (fn-cat$c-scan-msgid msgid i acc (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-scan-msgid fn-cat$c-scan-msgid)
            :induct (fn-cat$p-scan-msgid msgid i acc fn-cat$p)))))

(local
 (defthm fn-cat$p-msgid-seqs-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-msgid-seqs msgid fn-cat$p)
                   (fn-cat$c-msgid-seqs msgid (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-msgid-seqs fn-cat$c-msgid-seqs)
                                   (fn-cat$p-confirm fn-cat$c-confirm fn-cat$p-scan-msgid
                                    fn-cat$c-scan-msgid fn-mpxt-candidates))))))

(local
 (defthm fn-cat$p-rows-list-sim-s
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (natp i) (<= i (nth 1 (nth 1 fn-cat$p))))
            (equal (fn-cat$p-rows-list i acc fn-cat$p)
                   (fn-cat$c-rows-list i acc (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-rows-list fn-cat$c-rows-list)
            :induct (fn-cat$p-rows-list i acc fn-cat$p)))))

(local
 (defthm fn-cat$p-rows-below-count-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (natp (nth 1 (nth 1 fn-cat$p))))
            (equal (fn-cat$p-rows-below-count fn-cat$p)
                   (fn-cat$c-rows-below-count (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-rows-below-count fn-cat$c-rows-below-count)
                                   (fn-cat$p-rows-list fn-cat$c-rows-list))))))

(local
 (defthm fn-cat$p-msgid-saturatedp-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (natp (nth 1 (nth 1 fn-cat$p))))
            (equal (fn-cat$p-msgid-saturatedp key msgid fn-cat$p)
                   (fn-cat$c-msgid-saturatedp key msgid (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-msgid-saturatedp fn-cat$c-msgid-saturatedp)
                                   (fn-cat$p-rows-below-count fn-cat$c-rows-below-count
                                    fn-mpxt-saturatedp fn-mpxt-key-samep fn-mpxt-build-saturatedp))))))

(local
 (defthm fn-cat$p-index-health-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (natp (nth 1 (nth 1 fn-cat$p))))
            (equal (fn-cat$p-index-health key fn-cat$p)
                   (fn-cat$c-index-health key (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-index-health fn-cat$c-index-health)
                                   (fn-cat$p-rows-below-count fn-cat$c-rows-below-count
                                    fn-mpxt-key-samep fn-mpxt-build-health))))))

(local
 (defthm fn-cat$p-table-readers-sim
   (and (equal (fn-cat$p-group-number g n fn-cat$p) (fn-cat$c-group-number g n (fn-cat$p-view fn-cat$p)))
        (equal (fn-cat$p-group-next g fn-cat$p) (fn-cat$c-group-next g (fn-cat$p-view fn-cat$p)))
        (equal (fn-cat$p-group-count g fn-cat$p) (fn-cat$c-group-count g (fn-cat$p-view fn-cat$p)))
        (equal (fn-cat$p-total-octets fn-cat$p) (fn-cat$c-total-octets (fn-cat$p-view fn-cat$p)))
        (equal (fn-cat$p-group-live-count g fn-cat$p) (fn-cat$c-group-live-count g (fn-cat$p-view fn-cat$p)))
        (equal (fn-cat$p-group-live-low g fn-cat$p) (fn-cat$c-group-live-low g (fn-cat$p-view fn-cat$p)))
        (equal (fn-cat$p-group-live-high g fn-cat$p) (fn-cat$c-group-live-high g (fn-cat$p-view fn-cat$p)))
        (equal (fn-cat$p-horizon fn-cat$p) (fn-cat$c-horizon (fn-cat$p-view fn-cat$p)))
        (equal (fn-cat$p-withdrawn-at w fn-cat$p) (fn-cat$c-withdrawn-at w (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-group-number fn-cat$p-group-next fn-cat$p-group-count
                                      fn-cat$p-total-octets fn-cat$p-group-live-count
                                      fn-cat$p-group-live-low fn-cat$p-group-live-high
                                      fn-cat$p-horizon fn-cat$p-withdrawn-at)))))


; --- the liveness probe, the neighbours and the plans (gate C2)

(local
 (defthm fn-cp-corr-okp
   (implies (fn-cat$pcorr fn-cat$p fn-cat$a)
            (and (fn-cpl-okp t (nth 2 fn-cat$p) fn-cat$a)
                 (fn-cpl-okp nil (nth 3 fn-cat$p) fn-cat$a)
                 (fn-cpl-coverp (nth 2 fn-cat$p) fn-cat$a)
                 (fn-cpl-coverp (nth 3 fn-cat$p) fn-cat$a)
                 (fn-cat$corr-base (fn-cat$p-view fn-cat$p) fn-cat$a)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cat$pcorr fn-cat$corr-w fn-cat$corr)))))

; KEYSTONE: on a corresponding state the liveness probe IS liveness -- a
; bound key is live (fn-cpl-okp), a live number is bound (fn-cpl-coverp).
; Every row read the withdrawal's old filter made is this probe.
(defthm fn-cat$p-livep-is-live
  (implies (fn-cat$pcorr fn-cat$p fn-cat$a)
           (equal (fn-cat$p-livep g k fn-cat$p) (fn-cat-live-numberp g k fn-cat$a)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cp-corr-okp)
                 (:instance fn-cpl-probe-of-live (dir t) (tab (nth 2 fn-cat$p)) (c fn-cat$a))
                 (:instance fn-cpl-okp-necc (dir t) (tab (nth 2 fn-cat$p)) (c fn-cat$a) (x (cons g k))))
           :in-theory (e/d (fn-cat$p-livep fn-cpl-goodp fn-cpl-next-of)
                           (fn-cp-corr-okp fn-cpl-probe-of-live fn-cpl-okp-necc fn-cat-live-numberp
                            fn-cat-live-first fn-cat$p-view fn-cat$pcorr)))))

; KEYSTONES (Codex r30 F1): on a corresponding state a live number's
; neighbour read is its table entry -- bound, a natural, its true neighbour
; (coverage + okp carried in fn-cat$pcorr, books/catalog-live-links sec. 6).
; Every probe the withdrawal makes is of a live number of the row it
; withdraws (fn-cat$p-wplan, fn-cat$p-drop-entry, after the liveness probe).
(defthm fn-cat$p-next-is-probe
  (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (fn-cat-live-numberp g k fn-cat$a))
           (and (natp (fn-cat$p-lnext-get (cons g k) fn-cat$p))
                (equal (fn-cat$p-next g k fn-cat$p) (fn-cpl-next-of g k fn-cat$a))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cp-corr-okp)
                 (:instance fn-cpl-probe-of-live (dir t) (tab (nth 2 fn-cat$p)) (c fn-cat$a)))
           :in-theory (e/d (fn-cat$p-next fn-cpl-next-of)
                           (fn-cp-corr-okp fn-cpl-probe-of-live fn-cat-live-numberp fn-cat-live-first
                            fn-cat$p-view fn-cat$pcorr)))))

(defthm fn-cat$p-prev-is-probe
  (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (fn-cat-live-numberp g k fn-cat$a))
           (and (natp (fn-cat$p-lprev-get (cons g k) fn-cat$p))
                (equal (fn-cat$p-prev g k fn-cat$p) (fn-cpl-prev-of g k fn-cat$a))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cp-corr-okp)
                 (:instance fn-cpl-probe-of-live (dir nil) (tab (nth 3 fn-cat$p)) (c fn-cat$a)))
           :in-theory (e/d (fn-cat$p-prev fn-cpl-prev-of)
                           (fn-cp-corr-okp fn-cpl-probe-of-live fn-cat-live-numberp fn-cat-live-last
                            fn-cat$p-view fn-cat$pcorr)))))

; The view's group top (the old drop-entry's scan bound) is the group's high.
(local
 (defthm fn-cp-view-top-is-high
   (implies (fn-cat$pcorr fn-cat$p fn-cat$a)
            (equal (fn-cat$c-group-next g (fn-cat$p-view fn-cat$p))
                   (+ 1 (fn-cat-group-high g fn-cat$a))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-cat-group-next{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat$a)
                             (group g))
                  (:instance fn-cp-corr-facts))
            :in-theory (e/d (fn-cat$a-group-next) (fn-cp-corr-facts fn-cp-corr-okp fn-cat$p-view))))))

(local
 (defthm fn-cp-live-numberp-posp
   (implies (fn-cat-live-numberp g k c) (posp k))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cat-live-numberp)))))

(local
 (defthm fn-cat$p-drop-entry-sim
   (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (fn-cat-live-numberp g k fn-cat$a))
            (equal (fn-cat$p-drop-entry g k fn-cat$p)
                   (fn-cat$c-drop-entry g k (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-cp-view-top-is-high)
                  (:instance fn-cpl-scan-up-is-first (x (fn-cat$p-view fn-cat$p)) (c fn-cat$a)
                             (k (+ 1 k)) (top (fn-cat-group-high g fn-cat$a)))
                  (:instance fn-cpl-scan-down-is-last (x (fn-cat$p-view fn-cat$p)) (c fn-cat$a) (k (- k 1))))
            :in-theory (e/d (fn-cat$p-drop-entry fn-cat$c-drop-entry fn-cat$c-group-next fn-cpl-next-of fn-cpl-prev-of)
                            (fn-cat$p-next fn-cat$p-prev fn-cat$c-scan-up fn-cat$c-scan-down fn-cp-view-top-is-high
                             fn-cpl-scan-up-is-first fn-cpl-scan-down-is-last fn-cat-live-first fn-cat-live-last
                             fn-cat-live-numberp fn-cat$p-view fn-cat$pcorr))))))

(local
 (defthm fn-cp-group-number-is-seq
   (implies (fn-cat$pcorr fn-cat$p fn-cat$a)
            (equal (fn-cat$p-group-number g k fn-cat$p) (fn-cat-number-seq g k fn-cat$a 0)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-cat-group-number{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p))
                             (fn-cat fn-cat$a) (group g) (n k))
                  fn-cp-corr-facts)
            :in-theory (e/d (fn-cat$a-group-number) (fn-cp-corr-facts fn-cat-number-seq fn-cat$p-view))))))

; The numbers table of the view, at any key (the old plans probe it at the
; row's pair itself).
(local
 (defthm fn-cp-view-numbers-get-is-seq
   (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (consp x))
            (equal (fn-cat$c-numbers-get x (fn-cat$p-view fn-cat$p))
                   (fn-cat-number-seq (car x) (cdr x) fn-cat$a 0)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-cp-group-number-is-seq (g (car x)) (k (cdr x)))
                  (:instance fn-cat$p-table-readers-sim (g (car x)) (n (cdr x))))
            :in-theory (e/d (fn-cat$c-group-number)
                            (fn-cp-group-number-is-seq fn-cat$p-table-readers-sim fn-cat-number-seq
                             fn-cat$p-view fn-cat$pcorr fn-cat$p-group-number))))))

; The old filter (the numbers table answers TARGET and the row is live
; there) is the two probes, on a corresponding state at a row of the
; catalog: fn-cat$p-livep-is-live opens the liveness to the number's seq
; being TARGET and the row there live.
(local
 (defthm fn-cat$p-drop-plan-sim
   (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (natp target) (< target (len fn-cat$a))
                 (equal row (nth target fn-cat$a)))
            (equal (fn-cat$p-drop-plan pairs target fn-cat$p)
                   (fn-cat$c-drop-plan pairs target row (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-drop-plan fn-cat$c-drop-plan fn-cat-live-numberp)
                                   (fn-cat$p-drop-entry fn-cat$c-drop-entry fn-cat-live-rowp fn-cat-number-seq
                                    fn-cat$p-livep fn-cat$p-view fn-cat$pcorr fn-cat$p-group-number
                                    fn-cat$p-table-readers-sim fn-cat$c-group-number fn-cat$c-numbers-get))
            :induct (fn-cat$p-drop-plan pairs target fn-cat$p)))))

(local
 (defthm fn-cat$p-wplan-sim
   (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a) (natp r) (< r (len fn-cat$a)))
            (equal (fn-cat$p-wplan pairs r fn-cat$p)
                   (fn-cpl-wplan pairs r fn-cat$a)))
   :hints (("Goal" :induct (fn-cat$p-wplan pairs r fn-cat$p)
            :in-theory (e/d (fn-cat$p-wplan fn-cpl-wplan fn-cat-live-numberp)
                            (fn-cat$p-next fn-cat$p-prev fn-cat-live-rowp fn-cat-number-seq fn-cpl-next-of
                             fn-cpl-prev-of fn-cat$p-livep fn-cat$p-view fn-cat$pcorr fn-cat$p-group-number
                             fn-cat$p-table-readers-sim fn-cat$c-group-number fn-cat$c-numbers-get))))))

; --- the writes: the view of each paged write is the old write of the view

(local
 (defthm fn-cp-update-nth-update-nth-same
   (equal (update-nth i x (update-nth i y l)) (update-nth i x l))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-cp-row-held-of-row-of-any
   (implies (and h (not (fn-cp-overflow-of h)))
            (equal (fn-cp-row-held (fn-cp-row-of h)) h))
   :hints (("Goal" :in-theory (enable fn-cp-overflow-of)))))

(local
 (defthm fn-cp-merge-put-nil
   (implies (and (natp i) (< i (len crow)) (<= (len crow) (len ovf)))
            (equal (fn-cp-merge (update-nth i r crow) (update-nth i nil ovf))
                   (update-nth i (fn-cp-row-held r) (fn-cp-merge crow ovf))))
   :hints (("Goal" :in-theory (enable fn-cp-merge update-nth)))))

(local
 (defthm fn-cp-merge-put-cell
   (implies (and (natp i) (< i (len crow)) (<= (len crow) (len ovf)) o)
            (equal (fn-cp-merge (update-nth i r crow) (update-nth i o ovf))
                   (update-nth i o (fn-cp-merge crow ovf))))
   :hints (("Goal" :in-theory (enable fn-cp-merge update-nth)))))

(local
 (defthm fn-cp-held-of-row-of-nths
   (implies (and h (not (fn-cp-overflow-of h)))
            (equal (fn-cp-held (nth 0 (fn-cp-row-of h)) (nth 1 (fn-cp-row-of h)) (nth 2 (fn-cp-row-of h))
                               (nth 3 (fn-cp-row-of h)) (nth 4 (fn-cp-row-of h)) (nth 5 (fn-cp-row-of h))
                               (nth 6 (fn-cp-row-of h)) (nth 7 (fn-cp-row-of h)) (nth 8 (fn-cp-row-of h))
                               (nth 9 (fn-cp-row-of h)) (nth 10 (fn-cp-row-of h)) (nth 11 (fn-cp-row-of h))
                               (nth 12 (fn-cp-row-of h)))
                   h))
   :hints (("Goal" :use fn-cp-row-held-of-row-of-any
            :in-theory (e/d (fn-cp-row-held adt-l-nth-is-nth) (fn-cp-row-held-of-row-of-any fn-cp-held))))))

(local
 (defthm fn-cp-overflow-of-is-h
   (implies (fn-cp-overflow-of h) (equal (fn-cp-overflow-of h) h))
   :hints (("Goal" :in-theory (enable fn-cp-overflow-of)))))

; The withdrawal's three columns, written over a row that is not escaped:
; the decoded row with its withdrawal replaced.
(local
 (defthm fn-cp-row-held-of-withdrawal-columns
   (implies (not (nth 10 r))
            (equal (fn-cp-row-held (update-nth 9 b (update-nth 8 a (update-nth 7 t r))))
                   (fn-held-with-withdrawn (fn-cp-row-held r) (cons a b))))
   :hints (("Goal" :in-theory (e/d (fn-cp-row-held fn-cp-held adt-l-nth-is-nth fn-held-with-withdrawn)
                                   (fn-scc-decode-tree))))))

(local
 (defun fn-cp-cell-ind (i crow ovf)
   (if (zp i) (list crow ovf) (fn-cp-cell-ind (1- i) (cdr crow) (cdr ovf)))))

(local
 (defthm fn-cp-merge-set-cell
   (implies (and (natp i) (< i (len ovf)) o)
            (equal (fn-cp-merge crow (update-nth i o ovf))
                   (update-nth i o (fn-cp-merge crow ovf))))
   :hints (("Goal" :in-theory (enable fn-cp-merge update-nth)
            :induct (fn-cp-cell-ind i crow ovf)))))

(local
 (defthm fn-cp-merge-put-at-nil-cell
   (implies (and (natp i) (< i (len crow)) (<= (len crow) (len ovf)) (not (nth i ovf)))
            (equal (fn-cp-merge (update-nth i r crow) ovf)
                   (update-nth i (fn-cp-row-held r) (fn-cp-merge crow ovf))))
   :hints (("Goal" :in-theory (enable fn-cp-merge update-nth nth)
            :induct (fn-cp-cell-ind i crow ovf)))))

(local
 (defthm fn-cat$p-set-cell-view
   (implies (and (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (natp seq) (< seq (nth 1 (nth 1 fn-cat$p))) h)
            (equal (fn-cat$p-view (fn-cat$p-set-cell seq h fn-cat$p))
                   (update-fn-cat$c-rowsi seq h (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-set-cell)))))

(local
 (defthm fn-cp-with-withdrawn-nonnil
   (fn-held-with-withdrawn h w)
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn)))))

(local
 (defthm fn-cat$p-set-withdrawn-view
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (natp seq) (< seq (nth 1 (nth 1 fn-cat$p))))
            (equal (fn-cat$p-view (fn-cat$p-set-withdrawn seq w fn-cat$p))
                   (update-fn-cat$c-rowsi seq (fn-held-with-withdrawn
                                               (nth seq (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p))))
                                               w)
                                          (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-set-withdrawn fn-cat$p-columns-p adt-set-a fn-cat$p-at-is-merge)
                                   (fn-cp-row-held fn-cp-held fn-held-with-withdrawn fn-cat$p-set-cell))))))

(local
 (defthm fn-cp-merge-of-resize-any
   (implies (<= (len crow) (len ovf))
            (equal (fn-cp-merge crow (resize-list ovf n nil))
                   (resize-list (fn-cp-merge crow ovf) n nil)))
   :hints (("Goal" :in-theory (enable fn-cp-merge resize-list)
            :induct (fn-cp-resize-ind crow ovf n)))))

(local
 (defthm fn-cp-merge-append-nil-0
   (implies (< (len crow) (len ovf))
            (equal (fn-cp-merge (append crow (list r)) (update-nth (len crow) nil ovf))
                   (update-nth (len crow) (fn-cp-row-held r) (fn-cp-merge crow ovf))))
   :hints (("Goal" :in-theory (enable fn-cp-merge update-nth)
            :induct (fn-cp-merge crow ovf)))))

(local
 (defthm fn-cp-merge-append-nil
   (implies (and (equal (len crow) i) (< (len crow) (len ovf)))
            (equal (fn-cp-merge (append crow (list r)) (update-nth i nil ovf))
                   (update-nth i (fn-cp-row-held r) (fn-cp-merge crow ovf))))))

(local
 (defthm fn-cp-merge-append-cell-0
   (implies (and (< (len crow) (len ovf)) o)
            (equal (fn-cp-merge (append crow (list r)) (update-nth (len crow) o ovf))
                   (update-nth (len crow) o (fn-cp-merge crow ovf))))
   :hints (("Goal" :in-theory (enable fn-cp-merge update-nth)
            :induct (fn-cp-merge crow ovf)))))

(local
 (defthm fn-cp-merge-append-cell
   (implies (and (equal (len crow) i) (and (< (len crow) (len ovf)) o))
            (equal (fn-cp-merge (append crow (list r)) (update-nth i o ovf))
                   (update-nth i o (fn-cp-merge crow ovf))))))

(local (in-theory (disable fn-cp-merge)))

(local
 (defthm fn-cp-append-of-len-0
   (implies (equal (len x) 0) (equal (append x y) y))))

(local
 (defthm fn-cp-merge-singleton
   (and (equal (fn-cp-merge (list r) '(nil)) (list (fn-cp-row-held r)))
        (implies o (equal (fn-cp-merge (list r) (list o)) (list o))))
   :hints (("Goal" :in-theory (enable fn-cp-merge)))))

(local
 (defthm fn-cp-update-nth-0-singleton
   (equal (update-nth 0 v '(nil)) (list v))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-cat$p-append-row-view
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))) h)
            (equal (fn-cat$p-view (fn-cat$p-append-row h fn-cat$p))
                   (let ((c (fn-cat$p-view fn-cat$p)))
                     (update-fn-cat$c-rowsi (fn-cat$c-count c) h
                                            (if (< (fn-cat$c-count c) (fn-cat$c-rows-length c))
                                                c
                                              (resize-fn-cat$c-rows (+ 1 (* 2 (fn-cat$c-count c))) c))))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-append-row fn-cp-row-held adt-l-nth-is-nth)
                                   (fn-cp-row-of fn-cp-overflow-of fn-cp-held resize-list))
            :cases ((fn-cp-overflow-of h))))))

; The table writers leave the rows field (0) and the count (1) as they were.
(local
 (defthm fn-cp-index-add-frame
   (and (equal (nth 0 (fn-cat$c-index-add m s c)) (nth 0 c))
        (equal (nth 1 (fn-cat$c-index-add m s c)) (nth 1 c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-index-add)))))

(local
 (defthm fn-cp-apply-plan-frame
   (and (equal (nth 0 (fn-cat$c-apply-plan plan s c)) (nth 0 c))
        (equal (nth 1 (fn-cat$c-apply-plan plan s c)) (nth 1 c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-apply-plan)
            :induct (fn-cat$c-apply-plan plan s c)))))

(local
 (defthm fn-cp-live-apply-frame
   (and (equal (nth 0 (fn-cat$c-live-apply plan c)) (nth 0 c))
        (equal (nth 1 (fn-cat$c-live-apply plan c)) (nth 1 c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-live-apply)
            :induct (fn-cat$c-live-apply plan c)))))

(local
 (defthm fn-cp-wbv-put-frame
   (and (equal (nth 0 (fn-cat$c-wbv-put k v c)) (nth 0 c))
        (equal (nth 1 (fn-cat$c-wbv-put k v c)) (nth 1 c)))))

(local
 (defthm fn-cp-view-of-tab-index-add
   (equal (fn-cat$p-view (fn-cat$p-tab-index-add m s fn-cat$p))
          (fn-cat$c-index-add m s (fn-cat$p-view fn-cat$p)))
   :hints (("Goal" :in-theory (enable fn-cat$p-tab-index-add)))))

(local
 (defthm fn-cp-tab-index-add-shape
   (and (equal (nth 0 (fn-cat$p-tab-index-add m s fn-cat$p)) (nth 0 fn-cat$p))
        (equal (nth 1 (nth 1 (fn-cat$p-tab-index-add m s fn-cat$p))) (nth 1 (nth 1 fn-cat$p)))
        (equal (nth 0 (nth 1 (fn-cat$p-tab-index-add m s fn-cat$p))) (nth 0 (nth 1 fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-tab-index-add)))))

(local
 (defthm fn-cp-view-of-tab-commit
   (equal (fn-cat$p-view (fn-cat$p-tab-commit plan lplan hz seq h fn-cat$p))
          (let* ((c (fn-cat$p-view fn-cat$p))
                 (c (fn-cat$c-apply-plan plan seq c))
                 (c (update-fn-cat$c-octets (+ (fn-cat$c-octets c) (nfix (fn-hf-octets (fn-held-facts h)))) c))
                 (c (update-fn-cat$c-count (+ 1 seq) c))
                 (c (fn-cat$c-live-apply lplan c)))
            (update-fn-cat$c-hz hz c)))
   :hints (("Goal" :in-theory (enable fn-cat$p-tab-commit)))))

; The link tables and the withdrawals' pushes: the view reads positions 0,
; 1 and 4 only; the links write 2 and 3; a push is the old sorted insert at
; the view (the trie's ascending list after the add).
(local
 (defthm fn-cp-link-fields
   (and (equal (nth 0 (fn-cat$p-link plan fn-cat$p)) (nth 0 fn-cat$p))
        (equal (nth 1 (fn-cat$p-link plan fn-cat$p)) (nth 1 fn-cat$p))
        (equal (nth 4 (fn-cat$p-link plan fn-cat$p)) (nth 4 fn-cat$p))
        (equal (nth 2 (fn-cat$p-link plan fn-cat$p)) (fn-cpl-link t plan (nth 2 fn-cat$p)))
        (equal (nth 3 (fn-cat$p-link plan fn-cat$p)) (fn-cpl-link nil plan (nth 3 fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-link fn-cpl-link)
            :induct (fn-cat$p-link plan fn-cat$p)))))

(local
 (defthm fn-cp-unlink-fields
   (and (equal (nth 0 (fn-cat$p-unlink plan fn-cat$p)) (nth 0 fn-cat$p))
        (equal (nth 1 (fn-cat$p-unlink plan fn-cat$p)) (nth 1 fn-cat$p))
        (equal (nth 4 (fn-cat$p-unlink plan fn-cat$p)) (nth 4 fn-cat$p))
        (equal (nth 2 (fn-cat$p-unlink plan fn-cat$p)) (fn-cpl-unlink t plan (nth 2 fn-cat$p)))
        (equal (nth 3 (fn-cat$p-unlink plan fn-cat$p)) (fn-cpl-unlink nil plan (nth 3 fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-unlink fn-cpl-unlink)
            :induct (fn-cat$p-unlink plan fn-cat$p)))))

(local
 (defthm fn-cp-view-of-link
   (and (equal (fn-cat$p-view (fn-cat$p-link plan fn-cat$p)) (fn-cat$p-view fn-cat$p))
        (equal (fn-cat$p-view (fn-cat$p-unlink plan fn-cat$p)) (fn-cat$p-view fn-cat$p)))
   :hints (("Goal" :in-theory (enable fn-cat$p-view)))))

(local
 (defthm fn-cp-view-of-wbv-push
   (implies (natp s)
            (equal (fn-cat$p-view (fn-cat$p-wbv-put k (fn-cpt-add s (fn-cat$p-wbv-get k fn-cat$p)) fn-cat$p))
                   (fn-cat$c-wbv-put k (fn-cat-insert-asc s (fn-cat$c-wbv-get k (fn-cat$p-view fn-cat$p)))
                                     (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-view) (fn-cat-insert-asc))))))

(local
 (defthm fn-cp-wbv-push-fields
   (and (equal (nth 0 (fn-cat$p-wbv-put k v fn-cat$p)) (nth 0 fn-cat$p))
        (equal (nth 1 (fn-cat$p-wbv-put k v fn-cat$p)) (nth 1 fn-cat$p))
        (equal (nth 2 (fn-cat$p-wbv-put k v fn-cat$p)) (nth 2 fn-cat$p))
        (equal (nth 3 (fn-cat$p-wbv-put k v fn-cat$p)) (nth 3 fn-cat$p)))))

(local (in-theory (disable fn-cat$p-link fn-cat$p-unlink fn-cat$p-wbv-put fn-cat$p-wbv-get)))

(local
 (defthm fn-cp-with-numbers-nonnil
   (fn-held-with-numbers h n)
   :hints (("Goal" :in-theory (enable fn-held-with-numbers)))))

(local
 (defthm fn-cat$p-commit-w-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-view (fn-cat$p-commit-w h fn-cat$p))
                   (fn-cat$c-commit-w h (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :do-not-induct t
            ;; D26: max and the Message-ID test stay closed (they split
            ;; the goal 60 ways; 896k -> 173k steps).
            :in-theory (e/d (fn-cat$p-commit-w fn-cat$c-commit-w fn-cat$c-commit fn-cat$c-commit-base)
                            (max fn-scat-msgid-idp fn-cat$p-append-row fn-cat$p-tab-index-add fn-cat$p-tab-commit
                             fn-cat$c-live-plan fn-cat$c-plan fn-cat$c-apply-plan fn-cat$c-live-apply
                             fn-cat$c-index-add fn-cat$c-wbv-put fn-cat$c-wbv-get fn-held-with-numbers
                             fn-cat-plan-numbers fn-cat-insert-asc fn-cpt-list fn-cp-wbv-view))))))

(local
 (defthm fn-cp-with-context-nonnil
   (fn-held-with-context h x)
   :hints (("Goal" :in-theory (enable fn-held-with-context)))))

(local
 (defthm fn-cat$p-redecide-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (natp seq) (< seq (nth 1 (nth 1 fn-cat$p))))
            (equal (fn-cat$p-view (fn-cat$p-redecide seq context fn-cat$p))
                   (fn-cat$c-redecide seq context (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cat$p-redecide fn-cat$c-redecide)
                            (fn-cat$p-set-cell fn-held-with-context))))))

(local
 (defthm fn-cp-view-of-tab-withdraw
   (equal (fn-cat$p-view (fn-cat$p-tab-withdraw dplan hz fn-cat$p))
          (update-fn-cat$c-hz hz (fn-cat$c-live-apply dplan (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-tab-withdraw)))))

(local
 (defthm fn-cp-set-withdrawn-shape
   (implies (and (natp seq) (< seq (len (nth 0 fn-cat$p)))
                 (<= (len (nth 0 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (and (equal (len (nth 0 (fn-cat$p-set-withdrawn seq w fn-cat$p))) (len (nth 0 fn-cat$p)))
                 (equal (nth 1 (nth 1 (fn-cat$p-set-withdrawn seq w fn-cat$p))) (nth 1 (nth 1 fn-cat$p)))
                 (equal (len (nth 0 (nth 1 (fn-cat$p-set-withdrawn seq w fn-cat$p))))
                        (len (nth 0 (nth 1 fn-cat$p))))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-set-withdrawn fn-cat$p-columns-p adt-set-a) (fn-cat$p-at))))))

(local
 (defthm fn-cp-set-cell-shape
   (implies (and (natp seq) (< seq (len (nth 0 (nth 1 fn-cat$p)))))
            (and (equal (nth 0 (fn-cat$p-set-cell seq h fn-cat$p)) (nth 0 fn-cat$p))
                 (equal (nth 1 (nth 1 (fn-cat$p-set-cell seq h fn-cat$p))) (nth 1 (nth 1 fn-cat$p)))
                 (equal (len (nth 0 (nth 1 (fn-cat$p-set-cell seq h fn-cat$p))))
                        (len (nth 0 (nth 1 fn-cat$p))))))
   :hints (("Goal" :in-theory (enable fn-cat$p-set-cell)))))

(local
 (defthm fn-cat$p-withdraw-w-sim
   (implies (and (fn-cat$pcorr fn-cat$p fn-cat$a)
                 (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (natp target) (< target (nth 1 (nth 1 fn-cat$p))))
            (equal (fn-cat$p-view (fn-cat$p-withdraw-w target by fn-cat$p))
                   (fn-cat$c-withdraw-w target by (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-cp-view-row (seq target)))
            :in-theory (e/d (fn-cat$p-withdraw-w fn-cat$c-withdraw-w fn-cat$c-withdraw
                             fn-cat$c-withdraw-base)
                            (fn-cat$p-set-withdrawn fn-cat$p-tab-withdraw fn-cat$p-drop-plan fn-cat$c-drop-plan
                             fn-cat$c-live-apply fn-cat$c-wbv-put fn-cat$c-wbv-get fn-cat$p-wplan
                             fn-held-with-withdrawn fn-cat-insert-asc))))))

(local
 (defthm fn-cat$p-clear-w-sim
   (equal (fn-cat$p-view (fn-cat$p-clear-w fn-cat$p))
          (fn-cat$c-clear-w (fn-cat$p-view fn-cat$p)))
   :hints (("Goal" :in-theory (enable fn-cat$p-clear-w fn-cat$c-clear-w fn-cat$c-clear
                                      fn-cat$c-clear-base fn-cp-merge)))))

; D26: the keyed clear IS the clear with the ring's key installed into the
; emptied table, and installing a key moves no field the view replaces, so
; the keyed clear's simulation is the clear's (4.9 s at 4,308 steps of
; clausification before; one unfolding now).
(local
 (defthm fn-cp-clear-keyed-unfolds
   (equal (fn-cat$p-clear-keyed key fn-cat$p)
          (update-nth 1 (fn-cat$c-index-set-key key (nth 1 (fn-cat$p-clear-w fn-cat$p)))
                      (fn-cat$p-clear-w fn-cat$p)))
   :hints (("Goal" :in-theory (enable fn-cat$p-clear-keyed fn-cat$p-clear-w fn-cat$c-clear-keyed)))))

(local
 (defthm fn-cp-view-of-set-key
   (equal (fn-cat$p-view (update-nth 1 (fn-cat$c-index-set-key key (nth 1 fn-cat$p)) fn-cat$p))
          (fn-cat$c-index-set-key key (fn-cat$p-view fn-cat$p)))
   :hints (("Goal" :in-theory (enable fn-cat$p-view fn-cp-frame fn-cat$c-index-set-key)))))

(local
 (defthm fn-cat$p-clear-keyed-sim
   (equal (fn-cat$p-view (fn-cat$p-clear-keyed key fn-cat$p))
          (fn-cat$c-clear-keyed key (fn-cat$p-view fn-cat$p)))
   :hints (("Goal" :in-theory (union-theories '(fn-cp-clear-keyed-unfolds fn-cp-view-of-set-key
                                                fn-cat$p-clear-w-sim fn-cat$c-clear-keyed nth-update-nth)
                                              (theory 'minimal-theory))))))

(local (in-theory (disable fn-cp-clear-keyed-unfolds)))

; -----------------------------------------------------------------------------
; 7. The obligations: each the old catalog's (books/catalog-logic.lisp), at the view.

(local
 (defthm fn-cp-corr-count-natp
   (implies (fn-cat$pcorr fn-cat$p fn-cat$a)
            (natp (nth 1 (nth 1 fn-cat$p))))
   :rule-classes :forward-chaining
   :hints (("Goal" :use fn-cp-corr-facts :in-theory (disable fn-cp-corr-facts)))))

;  --- the link tables through each write

(local
 (defthm fn-cp-cplan-sim
   (implies (fn-cat$pcorr fn-cat$p fn-cat$a)
            (equal (fn-cat$p-cplan groups livep fn-cat$p) (fn-cpl-cplan groups livep fn-cat$a)))
   :hints (("Goal" :induct (fn-cpl-cplan groups livep fn-cat$a)
            :in-theory (e/d (fn-cat$p-cplan fn-cpl-cplan fn-cat$a-group-next fn-cat$a-group-live-high)
                            (fn-cat-live-last fn-cat$p-group-next fn-cat$p-group-live-high fn-cat$p-view)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-cat-group-next{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p))
                                   (fn-cat fn-cat$a) (group (car groups)))
                        (:instance fn-cat-group-live-high{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p))
                                   (fn-cat fn-cat$a) (group (car groups)))
                        fn-cp-corr-facts))))))

; Field frames of the commit's steps (D26: the commit lemmas below use
; these instead of opening the steps).
(local
 (defthm fn-cp-append-row-shape
   (and (equal (len (nth 0 (fn-cat$p-append-row h fn-cat$p))) (+ 1 (len (nth 0 fn-cat$p))))
        (equal (nth 1 (nth 1 (fn-cat$p-append-row h fn-cat$p))) (nth 1 (nth 1 fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-append-row) (fn-cp-row-of fn-cp-overflow-of))))))

(local
 (defthm fn-cp-tab-commit-shape
   (and (equal (nth 0 (fn-cat$p-tab-commit plan lplan hz seq h fn-cat$p)) (nth 0 fn-cat$p))
        (equal (nth 1 (nth 1 (fn-cat$p-tab-commit plan lplan hz seq h fn-cat$p))) (+ 1 seq)))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-tab-commit) (fn-cat$c-apply-plan fn-cat$c-live-apply))))))

(local
 (defthm fn-cp-step-link-fields
   (and (equal (nth 2 (fn-cat$p-append-row h fn-cat$p)) (nth 2 fn-cat$p))
        (equal (nth 3 (fn-cat$p-append-row h fn-cat$p)) (nth 3 fn-cat$p))
        (equal (nth 2 (fn-cat$p-tab-commit plan lplan hz seq h fn-cat$p)) (nth 2 fn-cat$p))
        (equal (nth 3 (fn-cat$p-tab-commit plan lplan hz seq h fn-cat$p)) (nth 3 fn-cat$p))
        (equal (nth 2 (fn-cat$p-tab-index-add m s fn-cat$p)) (nth 2 fn-cat$p))
        (equal (nth 3 (fn-cat$p-tab-index-add m s fn-cat$p)) (nth 3 fn-cat$p)))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-append-row fn-cat$p-tab-commit fn-cat$p-tab-index-add)
                                   (fn-cp-row-of fn-cp-overflow-of fn-cat$c-apply-plan fn-cat$c-live-apply
                                    fn-cat$c-index-add))))))

(local
 (defthm fn-cp-links-of-commit-w
    (and (equal (nth 2 (fn-cat$p-commit-w h fn-cat$p))
                (fn-cpl-link t (fn-cat$p-cplan (fn-record-groups h)
                                               (and (null (fn-held-withdrawn h))
                                                    (fn-scat-msgid-idp (fn-record-msgid h)))
                                               fn-cat$p)
                             (nth 2 fn-cat$p)))
         (equal (nth 3 (fn-cat$p-commit-w h fn-cat$p))
                (fn-cpl-link nil (fn-cat$p-cplan (fn-record-groups h)
                                                 (and (null (fn-held-withdrawn h))
                                                      (fn-scat-msgid-idp (fn-record-msgid h)))
                                                 fn-cat$p)
                             (nth 3 fn-cat$p))))
    :hints (("Goal" :in-theory (e/d (fn-cat$p-commit-w)
                                    (fn-cat$p-tab-commit fn-cat$p-append-row fn-cat$p-tab-index-add
                                     fn-cat$p-link fn-cat$p-wbv-put fn-cat$p-wbv-get fn-cat$p-cplan fn-cpl-link
                                     fn-cat$c-live-plan fn-cat$c-plan fn-cat$c-apply-plan
                                     fn-cat$c-live-apply fn-cat$c-index-add fn-cp-row-of fn-cp-overflow-of))))))

(local
 (defthm fn-cp-links-of-withdraw-w
   (and (equal (nth 2 (fn-cat$p-withdraw-w target by fn-cat$p))
               (if (null (fn-cat$p-withdrawn-of target fn-cat$p))
                   (fn-cpl-unlink t (fn-cat$p-wplan (fn-cat$p-numbers-of target fn-cat$p) target fn-cat$p)
                                  (nth 2 fn-cat$p))
                 (nth 2 fn-cat$p)))
        (equal (nth 3 (fn-cat$p-withdraw-w target by fn-cat$p))
               (if (null (fn-cat$p-withdrawn-of target fn-cat$p))
                   (fn-cpl-unlink nil (fn-cat$p-wplan (fn-cat$p-numbers-of target fn-cat$p) target fn-cat$p)
                                  (nth 3 fn-cat$p))
                 (nth 3 fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-withdraw-w fn-cat$p-set-withdrawn fn-cat$p-set-cell
                                    fn-cat$p-tab-withdraw fn-cat$p-columns-p)
                                   (fn-cat$p-wplan fn-cat$p-drop-plan fn-cat$p-at fn-cat$p-withdrawn-of
                                    fn-cat$p-numbers-of fn-cat$c-live-apply fn-held-with-withdrawn))))))

(local
 (defthm fn-cp-links-of-redecide-clear
   (and (equal (nth 2 (fn-cat$p-redecide seq ctx fn-cat$p)) (nth 2 fn-cat$p))
        (equal (nth 3 (fn-cat$p-redecide seq ctx fn-cat$p)) (nth 3 fn-cat$p))
        (equal (nth 2 (fn-cat$p-clear-w fn-cat$p)) nil)
        (equal (nth 3 (fn-cat$p-clear-w fn-cat$p)) nil)
        (equal (nth 2 (fn-cat$p-clear-keyed key fn-cat$p)) nil)
        (equal (nth 3 (fn-cat$p-clear-keyed key fn-cat$p)) nil))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-redecide fn-cat$p-set-cell fn-cat$p-clear-w fn-cat$p-clear-keyed)
                                   (fn-cat$p-at fn-held-with-context fn-cat$c-clear-w fn-cat$c-clear-keyed))))))

; The keystones at the logical writes.
(local
 (defthm fn-cp-okp-of-a-commit
   (implies (and (fn-cat-rowsp c) (fn-cpl-okp dir tab c))
            (fn-cpl-okp dir (fn-cpl-link dir (fn-cpl-cplan (fn-record-groups h)
                                                           (and (null (fn-held-withdrawn h))
                                                                (fn-scat-msgid-idp (fn-record-msgid h)))
                                                           c)
                                         tab)
                        (fn-cat$a-commit h c)))
   :hints (("Goal" :use fn-cpl-okp-of-commit
            :in-theory (e/d (fn-cat$a-commit) (fn-cpl-okp-of-commit fn-cpl-link fn-cpl-cplan))))))

(local
 (defthm fn-cp-okp-of-a-withdraw
   (implies (and (fn-cat-rowsp c) (natp r) (< r (len c)) (fn-cpl-okp dir tab c))
            (fn-cpl-okp dir (if (null (fn-held-withdrawn (nth r c)))
                                (fn-cpl-unlink dir (fn-cpl-wplan (fn-held-numbers (nth r c)) r c) tab)
                              tab)
                        (fn-cat$a-withdraw r by c)))
   :hints (("Goal" :use ((:instance fn-cpl-okp-of-withdraw (w (len c))))
            :in-theory (e/d (fn-cat$a-withdraw fn-cat-mark-withdrawn)
                            (fn-cpl-okp-of-withdraw fn-cpl-unlink fn-cpl-wplan))))))

;  Coverage at the logical writes (books/catalog-live-links.lisp sec. 6).
(local
 (defthm fn-cp-cover-of-a-commit
   (implies (and (fn-cat-rowsp c) (fn-cpl-coverp tab c))
            (fn-cpl-coverp (fn-cpl-link dir (fn-cpl-cplan (fn-record-groups h)
                                                          (and (null (fn-held-withdrawn h))
                                                               (fn-scat-msgid-idp (fn-record-msgid h)))
                                                          c)
                                        tab)
                           (fn-cat$a-commit h c)))
   :hints (("Goal" :use fn-cpl-coverp-of-commit
            :in-theory (e/d (fn-cat$a-commit) (fn-cpl-coverp-of-commit fn-cpl-link fn-cpl-cplan))))))

(local
 (defthm fn-cp-cover-of-a-withdraw
   (implies (and (fn-cat-rowsp c) (natp r) (< r (len c)) (fn-cpl-coverp tab c))
            (fn-cpl-coverp (if (null (fn-held-withdrawn (nth r c)))
                               (fn-cpl-unlink dir (fn-cpl-wplan (fn-held-numbers (nth r c)) r c) tab)
                             tab)
                           (fn-cat$a-withdraw r by c)))
   :hints (("Goal" :use ((:instance fn-cpl-coverp-of-withdraw (w (len c))))
            :in-theory (e/d (fn-cat$a-withdraw fn-cat-mark-withdrawn)
                            (fn-cpl-coverp-of-withdraw fn-cpl-unlink fn-cpl-wplan))))))

(local
 (defthm fn-cp-cover-of-a-redecide
   (implies (and (natp r) (< r (len c)) (fn-cpl-coverp tab c))
            (fn-cpl-coverp tab (fn-cat$a-redecide r ctx c)))
   :hints (("Goal" :use ((:instance fn-cpl-coverp-of-redecide (ctx ctx)))
            :in-theory (e/d (fn-cat$a-redecide) (fn-cpl-coverp-of-redecide fn-held-with-context))))))

(local
 (defthm fn-cp-okp-of-a-redecide
   (implies (and (natp r) (< r (len c)) (fn-cpl-okp dir tab c))
            (fn-cpl-okp dir tab (fn-cat$a-redecide r ctx c)))
   :hints (("Goal" :use ((:instance fn-cpl-okp-of-redecide (ctx ctx)))
            :in-theory (e/d (fn-cat$a-redecide) (fn-cpl-okp-of-redecide fn-held-with-context))))))

(local (in-theory (disable fn-cat$p-count fn-cat$p-wfp fn-cat$p-msgid-seqs fn-cat$p-group-number
                           fn-cat$p-group-next fn-cat$p-group-count fn-cat$p-total-octets
                           fn-cat$p-visible-at fn-cat$p-group-live-count fn-cat$p-group-live-low
                           fn-cat$p-group-live-high fn-cat$p-horizon fn-cat$p-commit-w
                           fn-cat$p-withdraw-w fn-cat$p-redecide fn-cat$p-clear-w fn-cat$p-withdrawn-at
                           fn-cat$p-clear-keyed fn-cat$p-msgid-saturatedp fn-cat$p-index-health)))

(local
 (defthm fn-cp-wfp-of-corr
   (implies (fn-cat$pcorr fn-cat$p fn-cat$a)
            (and (fn-cat$p-wfp fn-cat$p)
                 (equal (fn-cat$p-count fn-cat$p) (len fn-cat$a))))
   :hints (("Goal" :use fn-cp-corr-facts
            :in-theory (e/d (fn-cat$p-wfp fn-cat$p-count) (fn-cp-corr-facts))))))

(local
 (defthm fn-cp-commit-w-shape
    (and (equal (len (nth 0 (fn-cat$p-commit-w h fn-cat$p))) (+ 1 (len (nth 0 fn-cat$p))))
         (equal (nth 1 (nth 1 (fn-cat$p-commit-w h fn-cat$p))) (+ 1 (nth 1 (nth 1 fn-cat$p)))))
    :hints (("Goal" :in-theory (e/d (fn-cat$p-commit-w fn-cat$p-count)
                                    (fn-cat$p-tab-commit fn-cat$p-append-row fn-cat$p-tab-index-add
                                     fn-cat$p-link fn-cat$p-wbv-put fn-cat$p-wbv-get fn-cat$p-cplan
                                     fn-cat$c-live-plan fn-cat$c-plan fn-cat$c-apply-plan
                                     fn-cat$c-live-apply fn-cat$c-index-add fn-cat$c-wbv-put
                                     fn-cat$c-wbv-get fn-cp-row-of fn-cp-overflow-of))))))

(local
 (defthm fn-cp-tab-withdraw-shape
   (and (equal (nth 0 (fn-cat$p-tab-withdraw dplan hz fn-cat$p)) (nth 0 fn-cat$p))
        (equal (nth 1 (nth 1 (fn-cat$p-tab-withdraw dplan hz fn-cat$p))) (nth 1 (nth 1 fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-tab-withdraw) (fn-cat$c-live-apply fn-cat$c-wbv-put))))))

(local
 (defthm fn-cp-withdraw-w-shape
   (implies (and (natp target) (< target (len (nth 0 fn-cat$p)))
                 (<= (len (nth 0 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (and (equal (len (nth 0 (fn-cat$p-withdraw-w target by fn-cat$p))) (len (nth 0 fn-cat$p)))
                 (equal (nth 1 (nth 1 (fn-cat$p-withdraw-w target by fn-cat$p))) (nth 1 (nth 1 fn-cat$p)))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-withdraw-w)
                                   (fn-cat$p-set-withdrawn fn-cat$p-tab-withdraw fn-cat$p-drop-plan
                                    fn-cat$p-wplan fn-cat$p-withdrawn-of fn-cat$p-numbers-of))))))

(local
 (defthm fn-cp-redecide-shape
   (implies (and (natp seq) (< seq (len (nth 0 fn-cat$p)))
                 (<= (len (nth 0 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (and (equal (len (nth 0 (fn-cat$p-redecide seq context fn-cat$p))) (len (nth 0 fn-cat$p)))
                 (equal (nth 1 (nth 1 (fn-cat$p-redecide seq context fn-cat$p))) (nth 1 (nth 1 fn-cat$p)))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-redecide) (fn-cat$p-set-cell))))))

(local
 (defthm fn-cp-clear-w-shape
   (and (equal (nth 0 (fn-cat$p-clear-w fn-cat$p)) nil)
        (equal (nth 1 (nth 1 (fn-cat$p-clear-w fn-cat$p))) 0))
   :hints (("Goal" :in-theory (enable fn-cat$p-clear-w fn-cat$c-clear-w fn-cat$c-clear
                                      fn-cat$c-clear-base fn-cat$c-index-clear)))))

(local
 (defthm fn-cp-clear-shape
   (and (equal (nth 0 (fn-cat$p-clear-w fn-cat$p)) nil)
        (equal (nth 1 (nth 1 (fn-cat$p-clear-w fn-cat$p))) 0)
        (equal (nth 0 (fn-cat$p-clear-keyed key fn-cat$p)) nil)
        (equal (nth 1 (nth 1 (fn-cat$p-clear-keyed key fn-cat$p))) 0))
   :hints (("Goal" :in-theory (enable fn-cp-clear-keyed-unfolds fn-cat$c-index-set-key)))))

; The obligations, as `defabsstobj-missing-events' states them: each the old
; catalog's at the view, with the simulation of section 6.

(defthm create-fn-cat-paged{correspondence}
  (fn-cat$pcorr (create-fn-cat$p)
                                                     (create-fn-cat$a))
  :rule-classes nil
  :hints (("Goal" :use create-fn-cat{correspondence} :in-theory (enable create-fn-cat$p fn-cat$pcorr))))

(defthm create-fn-cat-paged{preserved}
  (fn-cat$ap (create-fn-cat$a))
  :rule-classes nil
  :hints (("Goal" :by create-fn-cat{preserved})))

(defthm fn-cat-paged-count{correspondence}
  (implies (fn-cat$pcorr fn-cat$p fn-cat-paged)
                (equal (fn-cat$p-count fn-cat$p)
                       (fn-cat$a-count fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-count{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-at{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (natp seq)
                        (if (< seq (fn-cat$a-count fn-cat-paged))
                            (fn-cat$ap fn-cat-paged)
                          'nil)
                      'nil)
                  'nil)
                (equal (fn-cat$p-at seq fn-cat$p)
                       (fn-cat$a-at seq fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-at{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-at{guard-thm}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (natp seq)
                        (if (< seq (fn-cat$a-count fn-cat-paged))
                            (fn-cat$ap fn-cat-paged)
                          'nil)
                      'nil)
                  'nil)
                (if (fn-cat$p-wfp fn-cat$p)
                    (if (natp seq)
                        (< seq (fn-cat$p-count fn-cat$p))
                      'nil)
                  'nil))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-at{guard-thm} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-msgid-seqs{correspondence}
  (implies (fn-cat$pcorr fn-cat$p fn-cat-paged)
                (equal (fn-cat$p-msgid-seqs msgid fn-cat$p)
                       (fn-cat$a-msgid-seqs msgid fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-msgid-seqs{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-msgid-seqs{guard-thm}
  (implies (fn-cat$pcorr fn-cat$p fn-cat-paged)
                (fn-cat$p-wfp fn-cat$p))
  :rule-classes nil
)

(defthm fn-cat-paged-group-number{correspondence}
  (implies (fn-cat$pcorr fn-cat$p fn-cat-paged)
                (equal (fn-cat$p-group-number group n fn-cat$p)
                       (fn-cat$a-group-number group n fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-group-number{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-group-next{correspondence}
  (implies (fn-cat$pcorr fn-cat$p fn-cat-paged)
                (equal (fn-cat$p-group-next group fn-cat$p)
                       (fn-cat$a-group-next group fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-group-next{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-group-count{correspondence}
  (implies (fn-cat$pcorr fn-cat$p fn-cat-paged)
                (equal (fn-cat$p-group-count group fn-cat$p)
                       (fn-cat$a-group-count group fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-group-count{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-total-octets{correspondence}
  (implies (fn-cat$pcorr fn-cat$p fn-cat-paged)
                (equal (fn-cat$p-total-octets fn-cat$p)
                       (fn-cat$a-total-octets fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-total-octets{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-visible-at{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (natp seq)
                        (if (< seq (fn-cat$a-count fn-cat-paged))
                            (if (natp v)
                                (fn-cat$ap fn-cat-paged)
                              'nil)
                          'nil)
                      'nil)
                  'nil)
                (equal (fn-cat$p-visible-at seq v fn-cat$p)
                       (fn-cat$a-visible-at seq v fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-visible-at{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-visible-at{guard-thm}
  (implies
    (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
        (if (natp seq)
            (if (< seq (fn-cat$a-count fn-cat-paged))
                (if (natp v)
                    (fn-cat$ap fn-cat-paged)
                  'nil)
              'nil)
          'nil)
      'nil)
    (if (fn-cat$p-wfp fn-cat$p)
        (if (natp seq)
            (if (natp v)
                (if (< seq (fn-cat$p-count fn-cat$p))
                    (fn-held-withdrawnp (fn-cat$p-withdrawn-of seq fn-cat$p))
                  'nil)
              'nil)
          'nil)
      'nil))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-visible-at{guard-thm} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-group-live-count{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (fn-cat$ap fn-cat-paged)
                  'nil)
                (equal (fn-cat$p-group-live-count group fn-cat$p)
                       (fn-cat$a-group-live-count group fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-group-live-count{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-group-live-low{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (fn-cat$ap fn-cat-paged)
                  'nil)
                (equal (fn-cat$p-group-live-low group fn-cat$p)
                       (fn-cat$a-group-live-low group fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-group-live-low{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-group-live-high{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (fn-cat$ap fn-cat-paged)
                  'nil)
                (equal (fn-cat$p-group-live-high group fn-cat$p)
                       (fn-cat$a-group-live-high group fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-group-live-high{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-horizon{correspondence}
  (implies (fn-cat$pcorr fn-cat$p fn-cat-paged)
                (equal (fn-cat$p-horizon fn-cat$p)
                       (fn-cat$a-horizon fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-horizon{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-commit{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (fn-held-p h)
                        (fn-cat$ap fn-cat-paged)
                      'nil)
                  'nil)
                (fn-cat$pcorr (fn-cat$p-commit-w h fn-cat$p)
                              (fn-cat$a-commit h fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-commit{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged))
                 (:instance fn-cp-corr-okp (fn-cat$a fn-cat-paged))
                 (:instance fn-cp-cplan-sim (fn-cat$a fn-cat-paged) (groups (fn-record-groups h))
                            (livep (and (null (fn-held-withdrawn h)) (fn-scat-msgid-idp (fn-record-msgid h)))))
                 (:instance fn-cp-okp-of-a-commit (dir t) (tab (nth 2 fn-cat$p)) (c fn-cat-paged))
                 (:instance fn-cp-okp-of-a-commit (dir nil) (tab (nth 3 fn-cat$p)) (c fn-cat-paged))
                 (:instance fn-cp-cover-of-a-commit (dir t) (tab (nth 2 fn-cat$p)) (c fn-cat-paged))
                 (:instance fn-cp-cover-of-a-commit (dir nil) (tab (nth 3 fn-cat$p)) (c fn-cat-paged)))
           :in-theory (e/d (fn-cat$pcorr) (fn-cp-corr-facts fn-cat$c-commit-w fn-cat$a-commit fn-held-p
                                                fn-cat$ap fn-cat$corr-w)))))

(defthm fn-cat-paged-commit{guard-thm}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (fn-held-p h)
                        (fn-cat$ap fn-cat-paged)
                      'nil)
                  'nil)
                (fn-cat$p-wfp fn-cat$p))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-commit{guard-thm} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-commit{preserved}
  (implies (if (fn-held-p h)
                    (fn-cat$ap fn-cat-paged)
                  'nil)
                (fn-cat$ap (fn-cat$a-commit h fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :by fn-cat-commit{preserved})))

; The withdrawal in two minimal-theory steps (D26: 21.8 s -> 0.01 s):
; the link tables (okp + coverage), then the view and the row count.
(local
 (defthm fn-cp-withdraw-links
   (implies (and (fn-cat$pcorr fn-cat$p a) (natp target) (< target (len a)))
            (and (fn-cpl-okp t (nth 2 (fn-cat$p-withdraw-w target by fn-cat$p)) (fn-cat$a-withdraw target by a))
                 (fn-cpl-okp nil (nth 3 (fn-cat$p-withdraw-w target by fn-cat$p)) (fn-cat$a-withdraw target by a))
                 (fn-cpl-coverp (nth 2 (fn-cat$p-withdraw-w target by fn-cat$p)) (fn-cat$a-withdraw target by a))
                 (fn-cpl-coverp (nth 3 (fn-cat$p-withdraw-w target by fn-cat$p)) (fn-cat$a-withdraw target by a))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-cp-corr-facts (fn-cat$a a))
                  (:instance fn-cp-corr-okp (fn-cat$a a))
                  (:instance fn-cat$p-withdrawn-of-is-row (fn-cat$a a) (seq target))
                  (:instance fn-cat$p-numbers-of-is-row (fn-cat$a a) (seq target))
                  (:instance fn-cat$p-wplan-sim (fn-cat$a a) (r target) (pairs (fn-held-numbers (nth target a))))
                  (:instance fn-cp-okp-of-a-withdraw (dir t) (tab (nth 2 fn-cat$p)) (c a) (r target))
                  (:instance fn-cp-okp-of-a-withdraw (dir nil) (tab (nth 3 fn-cat$p)) (c a) (r target))
                  (:instance fn-cp-cover-of-a-withdraw (dir t) (tab (nth 2 fn-cat$p)) (c a) (r target))
                  (:instance fn-cp-cover-of-a-withdraw (dir nil) (tab (nth 3 fn-cat$p)) (c a) (r target)))
            :in-theory (union-theories '(fn-cp-links-of-withdraw-w) (theory 'minimal-theory))))))

(local
 (defthm fn-cp-withdraw-view
   (implies (and (fn-cat$pcorr fn-cat$p a) (natp target) (< target (len a)) (natp by) (fn-cat$ap a))
            (and (fn-cat$corr-w (fn-cat$p-view (fn-cat$p-withdraw-w target by fn-cat$p)) (fn-cat$a-withdraw target by a))
                 (equal (len (nth 0 (fn-cat$p-withdraw-w target by fn-cat$p)))
                        (nth 1 (nth 1 (fn-cat$p-withdraw-w target by fn-cat$p))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-cat-withdraw{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat a))
                  (:instance fn-cp-corr-facts (fn-cat$a a))
                  (:instance fn-cat$p-withdraw-w-sim (fn-cat$a a))
                  fn-cp-withdraw-w-shape)
            :in-theory (union-theories '(fn-cat$a-count) (theory 'minimal-theory))))))

(defthm fn-cat-paged-withdraw{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (natp target)
                        (if (< target (fn-cat$a-count fn-cat-paged))
                            (if (natp by)
                                (fn-cat$ap fn-cat-paged)
                              'nil)
                          'nil)
                      'nil)
                  'nil)
                (fn-cat$pcorr (fn-cat$p-withdraw-w target by fn-cat$p)
                              (fn-cat$a-withdraw target by fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cp-withdraw-view (a fn-cat-paged))
                 (:instance fn-cp-withdraw-links (a fn-cat-paged)))
           :in-theory (union-theories '(fn-cat$a-count fn-cat$pcorr) (theory 'minimal-theory)))))

(defthm fn-cat-paged-withdraw{guard-thm}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (natp target)
                        (if (< target (fn-cat$a-count fn-cat-paged))
                            (if (natp by)
                                (fn-cat$ap fn-cat-paged)
                              'nil)
                          'nil)
                      'nil)
                  'nil)
                (if (fn-cat$p-wfp fn-cat$p)
                    (if (natp target)
                        (if (natp by)
                            (< target (fn-cat$p-count fn-cat$p))
                          'nil)
                      'nil)
                  'nil))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-withdraw{guard-thm} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-withdraw{preserved}
  (implies (if (natp target)
                    (if (< target (fn-cat$a-count fn-cat-paged))
                        (if (natp by)
                            (fn-cat$ap fn-cat-paged)
                          'nil)
                      'nil)
                  'nil)
                (fn-cat$ap (fn-cat$a-withdraw target by fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :by fn-cat-withdraw{preserved})))

(defthm fn-cat-paged-redecide{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (natp seq)
                        (if (< seq (fn-cat$a-count fn-cat-paged))
                            (if (fn-hc-p context)
                                (fn-cat$ap fn-cat-paged)
                              'nil)
                          'nil)
                      'nil)
                  'nil)
                (fn-cat$pcorr (fn-cat$p-redecide seq context fn-cat$p)
                              (fn-cat$a-redecide seq context fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-redecide{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged))
                 (:instance fn-cp-corr-okp (fn-cat$a fn-cat-paged))
                 (:instance fn-cp-okp-of-a-redecide (dir t) (tab (nth 2 fn-cat$p)) (c fn-cat-paged) (r seq) (ctx context))
                 (:instance fn-cp-okp-of-a-redecide (dir nil) (tab (nth 3 fn-cat$p)) (c fn-cat-paged) (r seq) (ctx context))
                 (:instance fn-cp-cover-of-a-redecide (tab (nth 2 fn-cat$p)) (c fn-cat-paged) (r seq) (ctx context))
                 (:instance fn-cp-cover-of-a-redecide (tab (nth 3 fn-cat$p)) (c fn-cat-paged) (r seq) (ctx context)))
           :in-theory (e/d (fn-cat$pcorr) (fn-cp-corr-facts)))))

(defthm fn-cat-paged-redecide{guard-thm}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (natp seq)
                        (if (< seq (fn-cat$a-count fn-cat-paged))
                            (if (fn-hc-p context)
                                (fn-cat$ap fn-cat-paged)
                              'nil)
                          'nil)
                      'nil)
                  'nil)
                (if (fn-cat$p-wfp fn-cat$p)
                    (if (natp seq)
                        (< seq (fn-cat$p-count fn-cat$p))
                      'nil)
                  'nil))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-redecide{guard-thm} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-redecide{preserved}
  (implies (if (natp seq)
                    (if (< seq (fn-cat$a-count fn-cat-paged))
                        (if (fn-hc-p context)
                            (fn-cat$ap fn-cat-paged)
                          'nil)
                      'nil)
                  'nil)
                (fn-cat$ap (fn-cat$a-redecide seq context fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :by fn-cat-redecide{preserved})))

(defthm fn-cat-paged-clear{correspondence}
  (implies (fn-cat$pcorr fn-cat$p fn-cat-paged)
                (fn-cat$pcorr (fn-cat$p-clear-w fn-cat$p)
                              (fn-cat$a-clear fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-clear{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (e/d (fn-cat$pcorr) (fn-cp-corr-facts)))))

(defthm fn-cat-paged-clear{preserved}
  (implies (fn-cat$ap fn-cat-paged)
                (fn-cat$ap (fn-cat$a-clear fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :by fn-cat-clear{preserved})))

(defthm fn-cat-paged-withdrawn-at{correspondence}
  (implies (fn-cat$pcorr fn-cat$p fn-cat-paged)
                (equal (fn-cat$p-withdrawn-at w fn-cat$p)
                       (fn-cat$a-withdrawn-at w fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-withdrawn-at{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-clear-keyed{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (fn-mpxt-keyp key)
                        (equal (len key) '32)
                      'nil)
                  'nil)
                (fn-cat$pcorr (fn-cat$p-clear-keyed key fn-cat$p)
                              (fn-cat$a-clear-keyed key fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-clear-keyed{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (e/d (fn-cat$pcorr) (fn-cp-corr-facts)))))

(defthm fn-cat-paged-clear-keyed{preserved}
  (implies (if (fn-cat$ap fn-cat-paged)
                    (if (fn-mpxt-keyp key)
                        (equal (len key) '32)
                      'nil)
                  'nil)
                (fn-cat$ap (fn-cat$a-clear-keyed key fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :by fn-cat-clear-keyed{preserved})))

(defthm fn-cat-paged-msgid-saturatedp{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (fn-mpxt-keyp key)
                        (if (equal (len key) '32)
                            (fn-cat$ap fn-cat-paged)
                          'nil)
                      'nil)
                  'nil)
                (equal (fn-cat$p-msgid-saturatedp key msgid fn-cat$p)
                       (fn-cat$a-msgid-saturatedp key msgid fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-msgid-saturatedp{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           ;; D26: the three saturation tests stay closed (the sim and the
           ;; instance meet; opened, the goal split 56 ways).
           :in-theory (disable fn-cp-corr-facts fn-cat$c-msgid-saturatedp fn-cat$a-msgid-saturatedp
                               fn-cat$p-msgid-saturatedp))))

(defthm fn-cat-paged-msgid-saturatedp{guard-thm}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (fn-mpxt-keyp key)
                        (if (equal (len key) '32)
                            (fn-cat$ap fn-cat-paged)
                          'nil)
                      'nil)
                  'nil)
                (if (fn-cat$p-wfp fn-cat$p)
                    (if (fn-mpxt-keyp key)
                        (equal (len key) '32)
                      'nil)
                  'nil))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-msgid-saturatedp{guard-thm} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-index-health{correspondence}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (fn-mpxt-keyp key)
                        (if (equal (len key) '32)
                            (fn-cat$ap fn-cat-paged)
                          'nil)
                      'nil)
                  'nil)
                (equal (fn-cat$p-index-health key fn-cat$p)
                       (fn-cat$a-index-health key fn-cat-paged)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-index-health{correspondence} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

(defthm fn-cat-paged-index-health{guard-thm}
  (implies (if (fn-cat$pcorr fn-cat$p fn-cat-paged)
                    (if (fn-mpxt-keyp key)
                        (if (equal (len key) '32)
                            (fn-cat$ap fn-cat-paged)
                          'nil)
                      'nil)
                  'nil)
                (if (fn-cat$p-wfp fn-cat$p)
                    (if (fn-mpxt-keyp key)
                        (equal (len key) '32)
                      'nil)
                  'nil))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-index-health{guard-thm} (fn-cat$c (fn-cat$p-view fn-cat$p)) (fn-cat fn-cat-paged))
                 (:instance fn-cp-corr-facts (fn-cat$a fn-cat-paged)))
           :in-theory (disable fn-cp-corr-facts))))

; -----------------------------------------------------------------------------
; 8. The paged catalog: the same :logic functions as `fn-cat' (books/catalog.lisp),
; so books/catalog-paged-attach.lisp attaches it to the generic.

(defabsstobj fn-cat-paged
  :foundation fn-cat$p
  :recognizer (fn-cat-paged-p :logic fn-cat$ap :exec fn-cat$pp)
  :creator (create-fn-cat-paged :logic create-fn-cat$a :exec create-fn-cat$p)
  :corr-fn fn-cat$pcorr
  :exports ((fn-cat-paged-count :logic fn-cat$a-count :exec fn-cat$p-count)
            (fn-cat-paged-at :logic fn-cat$a-at :exec fn-cat$p-at)
            (fn-cat-paged-msgid-seqs :logic fn-cat$a-msgid-seqs :exec fn-cat$p-msgid-seqs)
            (fn-cat-paged-group-number :logic fn-cat$a-group-number :exec fn-cat$p-group-number)
            (fn-cat-paged-group-next :logic fn-cat$a-group-next :exec fn-cat$p-group-next)
            (fn-cat-paged-group-count :logic fn-cat$a-group-count :exec fn-cat$p-group-count)
            (fn-cat-paged-total-octets :logic fn-cat$a-total-octets :exec fn-cat$p-total-octets)
            (fn-cat-paged-visible-at :logic fn-cat$a-visible-at :exec fn-cat$p-visible-at)
            (fn-cat-paged-group-live-count :logic fn-cat$a-group-live-count :exec fn-cat$p-group-live-count)
            (fn-cat-paged-group-live-low :logic fn-cat$a-group-live-low :exec fn-cat$p-group-live-low)
            (fn-cat-paged-group-live-high :logic fn-cat$a-group-live-high :exec fn-cat$p-group-live-high)
            (fn-cat-paged-horizon :logic fn-cat$a-horizon :exec fn-cat$p-horizon)
            (fn-cat-paged-commit :logic fn-cat$a-commit :exec fn-cat$p-commit-w :protect t)
            (fn-cat-paged-withdraw :logic fn-cat$a-withdraw :exec fn-cat$p-withdraw-w :protect t)
            (fn-cat-paged-redecide :logic fn-cat$a-redecide :exec fn-cat$p-redecide :protect t)
            (fn-cat-paged-clear :logic fn-cat$a-clear :exec fn-cat$p-clear-w :protect t)
            (fn-cat-paged-withdrawn-at :logic fn-cat$a-withdrawn-at :exec fn-cat$p-withdrawn-at)
            (fn-cat-paged-clear-keyed :logic fn-cat$a-clear-keyed :exec fn-cat$p-clear-keyed :protect t)
            (fn-cat-paged-msgid-saturatedp :logic fn-cat$a-msgid-saturatedp :exec fn-cat$p-msgid-saturatedp)
            (fn-cat-paged-index-health :logic fn-cat$a-index-health :exec fn-cat$p-index-health))
  :corr-fn-exists t
  :attachable t)
