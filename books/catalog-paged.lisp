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
;                                       identities, the facts, the context,
;                                       the numbers and the binding as ONE
;                                       tree in the pool (books/store-tree-
;                                       codec.lisp, KEYSTONE fn-scc-decode-
;                                       tree-of-encode)
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
(include-book "def-representation")
;; The tree codec's executables with their guards verified, and the tree
;; recognizer whose program is octets (fn-sccb-treep); its closure carries
;; the frame trailer and the digest attachments, which no recognizer or
;; correspondence below reaches (the catalog's digest-free row shape).
(include-book "store-checkpoint-buffer")
;; fn-record-ascii-string-implies-octet-string, fn-record-string-round-trip:
;; a Message-ID string comes back from its octets.
(include-book "records-invariants")

(local (in-theory (disable (tau-system))))

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
  (aux :octets))

; -----------------------------------------------------------------------------
; 2. The foundation: the row store beside the old foundation (its tables,
; and its rows array as the overflow cells).

(defstobj fn-cat$p
  (fn-cat$p-rows :type fn-crow)
  (fn-cat$p-tab :type fn-cat$c)
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

; The remainder: what the columns do not carry, as one tree.
(defun fn-cp-tree-of (h)
  (declare (xargs :guard t))
  (list (fn-held-groups h) (fn-held-obligation-id h) (fn-held-content-subject h)
        (fn-held-release-evidence h) (fn-held-facts h) (fn-held-context h)
        (fn-held-numbers h) (fn-held-binding h)
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
          (if (fn-sccb-treep tree) (fn-scc-program tree) nil))))

; A row the columns carry exactly: a catalog row (fn-cat-rowp) whose
; remainder is a tree; every other row is kept whole in its cell, so that
; the codec is exact for every row (fn-cp-row-held-of-row-of).
(defun fn-cp-overflow-of (h)
  (declare (xargs :guard t))
  (if (and (fn-cat-rowp h) (fn-sccb-treep (fn-cp-tree-of h))) nil h))

; The row from its columns: the tree decoded, the escape honoured.
(defun fn-cp-held (seq txid gen payload charge stamp msgid wpres wat wby esc aux)
  (declare (xargs :guard (fn-scc-octet-listp aux)))
  (let* ((d (fn-scc-decode-tree aux))
         (tree (if (and (consp d) (eq (car d) :ok) (consp (cdr d))) (car (cdr d)) nil))
         (e (adt-l-nth 8 tree))
         (payload (if esc (adt-l-nth 0 e) payload))
         (w (if esc (adt-l-nth 1 e) (if wpres (cons wat wby) nil))))
    (fn-held-make seq txid gen (fn-record-octets-string msgid) payload
                  (adt-l-nth 0 tree) (adt-l-nth 1 tree) (adt-l-nth 2 tree) (adt-l-nth 3 tree)
                  charge stamp (adt-l-nth 4 tree) (adt-l-nth 5 tree) (adt-l-nth 6 tree)
                  w (adt-l-nth 7 tree))))

(defun fn-cp-row-held (r)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cp-held (adt-l-nth 0 r) (adt-l-nth 1 r) (adt-l-nth 2 r) (adt-l-nth 3 r) (adt-l-nth 4 r)
              (adt-l-nth 5 r) (adt-l-nth 6 r) (adt-l-nth 7 r) (adt-l-nth 8 r) (adt-l-nth 9 r)
              (adt-l-nth 10 r) (adt-l-nth 11 r)))

; The columns of any row are a record of the schema.
(local
 (defthm fn-cp-rec-p-of-list
   (equal (adt-rec-p *fn-crow-schema* (list a b c d e f g h i j k l))
          (and (unsigned-byte-p 64 a) (unsigned-byte-p 64 b) (unsigned-byte-p 64 c)
               (unsigned-byte-p 64 d) (unsigned-byte-p 64 e) (unsigned-byte-p 64 f)
               (adt-octetsp g) (booleanp h) (unsigned-byte-p 64 i) (unsigned-byte-p 64 j)
               (booleanp k) (adt-octetsp l)))
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

(defthm fn-cp-row-of-rec-p
  (adt-rec-p *fn-crow-schema* (fn-cp-row-of h))
  :hints (("Goal" :in-theory (e/d (fn-cp-row-of) (fn-cp-u64 fn-cp-smallp fn-cp-msgid-octets
                                                   fn-cp-escapedp fn-sccb-treep)))))

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
 (defthm fn-cp-held-of-program
   (implies (fn-sccb-treep tree)
            (equal (fn-cp-held s tx g p c st m wp wa wb e (fn-scc-program tree))
                   (fn-held-make s tx g (fn-record-octets-string m)
                                 (if e (adt-l-nth 0 (adt-l-nth 8 tree)) p)
                                 (adt-l-nth 0 tree) (adt-l-nth 1 tree) (adt-l-nth 2 tree)
                                 (adt-l-nth 3 tree) c st (adt-l-nth 4 tree) (adt-l-nth 5 tree)
                                 (adt-l-nth 6 tree)
                                 (if e (adt-l-nth 1 (adt-l-nth 8 tree)) (if wp (cons wa wb) nil))
                                 (adt-l-nth 7 tree))))
   :hints (("Goal" :in-theory (e/d (fn-cp-held) (fn-scc-decode-tree fn-scc-program fn-sccb-treep))))))

(defthm fn-cp-row-held-of-row-of
  (implies (and (fn-cat-rowp h) (fn-sccb-treep (fn-cp-tree-of h)))
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

(defun-nx fn-cat$p-view (fn-cat$p)
  (update-nth 0 (fn-cp-merge (nth 0 fn-cat$p) (nth 0 (nth 1 fn-cat$p))) (nth 1 fn-cat$p)))

(defun-nx fn-cat$pcorr (fn-cat$p fn-cat$a)
  (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
       (fn-cat$corr-w (fn-cat$p-view fn-cat$p) fn-cat$a)))

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
           (adt-octetsp (nth 11 (nth i a))))
  :hints (("Goal" :use fn-cp-crow-row-rec-p
           :in-theory (e/d (adt-rec-p adt-val-okp nth) (fn-cp-crow-row-rec-p fn-crowp)))))

(defthm fn-cp-crowp-of-set-column
  (implies (and (fn-crowp a) (natp i) (< i (len a)) (natp j) (< j 12)
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
  (implies (and (fn-crowp a) (natp i) (< i (len a)) (natp j) (< j 12)
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
        (adt-octetsp (nth 11 (fn-cp-row-of h))))
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
                             (fn-crow-get-esc seq fn-crow) (fn-crow-get-aux seq fn-crow))))
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
                                   t (fn-crow-get-aux seq fn-crow))))
                     ((fn-crow-get-wpres seq fn-crow)
                      (cons (fn-crow-get-wat seq fn-crow) (fn-crow-get-wby seq fn-crow)))
                     (t nil)))
             w))

; A row written at SEQ (below the count): every column, and its overflow cell.
(defun fn-cat$p-put-row (seq h fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp seq) (< seq (fn-cat$p-count fn-cat$p)))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (enable adt-val-okp)))))
  (let ((r (fn-cp-row-of h)))
    (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
               (fn-crow fn-cat$c)
               (let* ((fn-crow (fn-crow-set-seq seq (nth 0 r) fn-crow))
                      (fn-crow (fn-crow-set-txid seq (nth 1 r) fn-crow))
                      (fn-crow (fn-crow-set-gen seq (nth 2 r) fn-crow))
                      (fn-crow (fn-crow-set-payload seq (nth 3 r) fn-crow))
                      (fn-crow (fn-crow-set-charge seq (nth 4 r) fn-crow))
                      (fn-crow (fn-crow-set-stamp seq (nth 5 r) fn-crow))
                      (fn-crow (fn-crow-set-msgid seq (nth 6 r) fn-crow))
                      (fn-crow (fn-crow-set-wpres seq (nth 7 r) fn-crow))
                      (fn-crow (fn-crow-set-wat seq (nth 8 r) fn-crow))
                      (fn-crow (fn-crow-set-wby seq (nth 9 r) fn-crow))
                      (fn-crow (fn-crow-set-esc seq (nth 10 r) fn-crow))
                      (fn-crow (fn-crow-set-aux seq (nth 11 r) fn-crow))
                      (fn-cat$c (update-fn-cat$c-rowsi seq (fn-cp-overflow-of h) fn-cat$c)))
                 (mv fn-crow fn-cat$c))
               fn-cat$p)))

; A row appended at the count: the columns appended, the overflow cells
; grown as the old rows array was and the cell written.
(defun fn-cat$p-append-row (h fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (fn-cat$p-wfp fn-cat$p)
                  :guard-hints (("Goal" :do-not-induct t))))
  (let ((r (fn-cp-row-of h)))
    (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
               (fn-crow fn-cat$c)
               (let* ((seq (fn-cat$c-count fn-cat$c))
                      (fn-crow (fn-crow-append r fn-crow))
                      (fn-cat$c (if (< seq (fn-cat$c-rows-length fn-cat$c))
                                    fn-cat$c
                                  (resize-fn-cat$c-rows (+ 1 (* 2 seq)) fn-cat$c)))
                      (fn-cat$c (update-fn-cat$c-rowsi seq (fn-cp-overflow-of h) fn-cat$c)))
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
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (x) (fn-cat$c-withdrawn-at w fn-cat$c) x))

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
             (let* ((x (fn-held-withdrawn h))
                    (fn-cat$c (fn-cat$c-apply-plan plan seq fn-cat$c))
                    (fn-cat$c (update-fn-cat$c-octets
                               (+ (fn-cat$c-octets fn-cat$c)
                                  (nfix (fn-hf-octets (fn-held-facts h))))
                               fn-cat$c))
                    (fn-cat$c (update-fn-cat$c-count (+ 1 seq) fn-cat$c))
                    (fn-cat$c (fn-cat$c-live-apply lplan fn-cat$c))
                    (fn-cat$c (update-fn-cat$c-hz hz fn-cat$c)))
               (if (consp x)
                   (fn-cat$c-wbv-put (car x)
                                     (fn-cat-insert-asc seq (fn-cat$c-wbv-get (car x) fn-cat$c))
                                     fn-cat$c)
                 fn-cat$c))
             fn-cat$p))

(local
 (defthm fn-cp-wfp-of-tab-index-add
   (implies (fn-cat$p-wfp fn-cat$p)
            (fn-cat$p-wfp (fn-cat$p-tab-index-add m s fn-cat$p)))
   :hints (("Goal" :in-theory (enable fn-cat$p-tab-index-add)))))

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
         (fn-cat$p (fn-cat$p-tab-index-add (fn-record-msgid h) seq fn-cat$p))
         (fn-cat$p (fn-cat$p-append-row row fn-cat$p)))
    (fn-cat$p-tab-commit plan lplan hz seq h fn-cat$p)))

; The live summary's scans, over the paged rows (the old fn-cat$c-live-at-p,
; -scan-up, -scan-down, -drop-entry, -drop-plan).
(defun fn-cat$p-live-at-p (group k fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (fn-cat$p-wfp fn-cat$p)))
  (let ((s (fn-cat$p-group-number group k fn-cat$p)))
    (and (natp s) (< s (fn-cat$p-count fn-cat$p))
         (fn-cat-live-rowp group k (fn-cat$p-at s fn-cat$p)))))

(defun fn-cat$p-scan-up (group k top fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (and (fn-cat$p-wfp fn-cat$p) (natp k) (natp top))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (if (fn-cat$p-live-at-p group k fn-cat$p)
          k
        (fn-cat$p-scan-up group (+ 1 k) top fn-cat$p))
    0))

(defun fn-cat$p-scan-down (group k fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (and (fn-cat$p-wfp fn-cat$p) (natp k))))
  (if (posp k)
      (if (fn-cat$p-live-at-p group k fn-cat$p)
          k
        (fn-cat$p-scan-down group (- k 1) fn-cat$p))
    0))

(defun fn-cat$p-drop-entry (group k fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (and (fn-cat$p-wfp fn-cat$p) (posp k))))
  (let* ((ge (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p))) (ge) (fn-cat$c-groups-get group fn-cat$c) ge))
         (top (nfix (- (if (consp ge) (nfix (cdr ge)) 1) 1)))
         (count (fn-cat$p-group-live-count group fn-cat$p))
         (low (fn-cat$p-group-live-low group fn-cat$p))
         (high (fn-cat$p-group-live-high group fn-cat$p)))
    (cons (nfix (- count 1))
          (cons (if (equal low k) (fn-cat$p-scan-up group (+ 1 k) top fn-cat$p) low)
                (if (equal high k) (fn-cat$p-scan-down group (- k 1) fn-cat$p) high)))))

(defun fn-cat$p-drop-plan (pairs target row fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (fn-cat$p-wfp fn-cat$p)))
  (if (consp pairs)
      (let* ((p (car pairs))
             (g (fn-cbor-ag-car p))
             (k (fn-cbor-ag-cdr p)))
        (if (and (consp p)
                 (equal (fn-cat$p-group-number g k fn-cat$p) target)
                 (fn-cat-live-rowp g k row))
            (cons (cons g (fn-cat$p-drop-entry g k fn-cat$p))
                  (fn-cat$p-drop-plan (cdr pairs) target row fn-cat$p))
          (fn-cat$p-drop-plan (cdr pairs) target row fn-cat$p)))
    nil))

; The withdrawal's table step (one stobj-let over the nested tables).
(defun fn-cat$p-tab-withdraw (dplan hz v target fn-cat$p)
  (declare (xargs :stobjs fn-cat$p :guard (and (natp hz) (natp target))))
  (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (fn-cat$c)
             (let* ((fn-cat$c (fn-cat$c-live-apply dplan fn-cat$c))
                    (fn-cat$c (update-fn-cat$c-hz hz fn-cat$c)))
               (fn-cat$c-wbv-put v (fn-cat-insert-asc target (fn-cat$c-wbv-get v fn-cat$c))
                                 fn-cat$c))
             fn-cat$p))

(defun fn-cat$p-withdraw-w (target by fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp target) (natp by)
                              (< target (fn-cat$p-count fn-cat$p)))))
  (let ((row (fn-cat$p-at target fn-cat$p)))
    (if (null (fn-held-withdrawn row))
        (let* ((v (fn-cat$p-count fn-cat$p))
               (dplan (fn-cat$p-drop-plan (fn-held-numbers row) target row fn-cat$p))
               (hz (stobj-let ((fn-cat$c (fn-cat$p-tab fn-cat$p)))
                              (hz)
                              (max (fn-cat$c-hz fn-cat$c) (+ 1 (fn-cat$c-count fn-cat$c)))
                              hz))
               (fn-cat$p (fn-cat$p-put-row target (fn-held-with-withdrawn row (cons v by)) fn-cat$p)))
          (fn-cat$p-tab-withdraw dplan hz v target fn-cat$p))
      fn-cat$p)))

(defun fn-cat$p-redecide (seq context fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-cat$p-wfp fn-cat$p) (natp seq) (< seq (fn-cat$p-count fn-cat$p)))))
  (fn-cat$p-put-row seq (fn-held-with-context (fn-cat$p-at seq fn-cat$p) context) fn-cat$p))

(defun fn-cat$p-clear-w (fn-cat$p)
  (declare (xargs :stobjs fn-cat$p))
  (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (fn-crow fn-cat$c)
             (let* ((fn-crow (fn-crow-clear fn-crow))
                    (fn-cat$c (fn-cat$c-clear-w fn-cat$c)))
               (mv fn-crow fn-cat$c))
             fn-cat$p))

(defun fn-cat$p-clear-keyed (key fn-cat$p)
  (declare (xargs :stobjs fn-cat$p
                  :guard (and (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))))
  (stobj-let ((fn-crow (fn-cat$p-rows fn-cat$p)) (fn-cat$c (fn-cat$p-tab fn-cat$p)))
             (fn-crow fn-cat$c)
             (let* ((fn-crow (fn-crow-clear fn-crow))
                    (fn-cat$c (fn-cat$c-clear-keyed key fn-cat$c)))
               (mv fn-crow fn-cat$c))
             fn-cat$p))


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
   (and (equal (fn-cat$c-count (update-nth 0 r c)) (fn-cat$c-count c))
        (equal (fn-cat$c-octets (update-nth 0 r c)) (fn-cat$c-octets c))
        (equal (fn-cat$c-mpx (update-nth 0 r c)) (fn-cat$c-mpx c))
        (equal (fn-cat$c-mpx2 (update-nth 0 r c)) (fn-cat$c-mpx2 c))
        (equal (fn-cat$c-unplaced (update-nth 0 r c)) (fn-cat$c-unplaced c))
        (equal (fn-cat$c-hz (update-nth 0 r c)) (fn-cat$c-hz c))
        (equal (fn-cat$c-numbers-get k (update-nth 0 r c)) (fn-cat$c-numbers-get k c))
        (equal (fn-cat$c-groups-get k (update-nth 0 r c)) (fn-cat$c-groups-get k c))
        (equal (fn-cat$c-lives-get k (update-nth 0 r c)) (fn-cat$c-lives-get k c))
        (equal (fn-cat$c-wbv-get k (update-nth 0 r c)) (fn-cat$c-wbv-get k c))
        (equal (fn-cat$c-rowsi i (update-nth 0 r c)) (nth i r))
        (equal (fn-cat$c-rows-length (update-nth 0 r c)) (len r)))))

(local
 (defthm fn-cp-writers-blind
   (and (equal (update-fn-cat$c-count n (update-nth 0 r c)) (update-nth 0 r (update-fn-cat$c-count n c)))
        (equal (update-fn-cat$c-octets n (update-nth 0 r c)) (update-nth 0 r (update-fn-cat$c-octets n c)))
        (equal (update-fn-cat$c-mpx x (update-nth 0 r c)) (update-nth 0 r (update-fn-cat$c-mpx x c)))
        (equal (update-fn-cat$c-mpx2 x (update-nth 0 r c)) (update-nth 0 r (update-fn-cat$c-mpx2 x c)))
        (equal (update-fn-cat$c-unplaced n (update-nth 0 r c)) (update-nth 0 r (update-fn-cat$c-unplaced n c)))
        (equal (update-fn-cat$c-hz n (update-nth 0 r c)) (update-nth 0 r (update-fn-cat$c-hz n c)))
        (equal (fn-cat$c-numbers-put k v (update-nth 0 r c)) (update-nth 0 r (fn-cat$c-numbers-put k v c)))
        (equal (fn-cat$c-groups-put k v (update-nth 0 r c)) (update-nth 0 r (fn-cat$c-groups-put k v c)))
        (equal (fn-cat$c-lives-put k v (update-nth 0 r c)) (update-nth 0 r (fn-cat$c-lives-put k v c)))
        (equal (fn-cat$c-wbv-put k v (update-nth 0 r c)) (update-nth 0 r (fn-cat$c-wbv-put k v c)))
        (equal (fn-cat$c-numbers-clear (update-nth 0 r c)) (update-nth 0 r (fn-cat$c-numbers-clear c)))
        (equal (fn-cat$c-groups-clear (update-nth 0 r c)) (update-nth 0 r (fn-cat$c-groups-clear c)))
        (equal (fn-cat$c-lives-clear (update-nth 0 r c)) (update-nth 0 r (fn-cat$c-lives-clear c)))
        (equal (fn-cat$c-wbv-clear (update-nth 0 r c)) (update-nth 0 r (fn-cat$c-wbv-clear c)))
        (equal (update-fn-cat$c-rowsi i v (update-nth 0 r c)) (update-nth 0 (update-nth i v r) c))
        (equal (resize-fn-cat$c-rows n (update-nth 0 r c)) (update-nth 0 (resize-list r n nil) c)))))

; The derived readers and writers of books/catalog.lisp, each by its definition.
(local
 (defthm fn-cp-plan-blind
   (equal (fn-cat$c-plan groups (update-nth 0 r c)) (fn-cat$c-plan groups c))
   :hints (("Goal" :in-theory (enable fn-cat$c-plan)))))

(local
 (defthm fn-cp-live-plan-blind
   (equal (fn-cat$c-live-plan groups livep (update-nth 0 r c)) (fn-cat$c-live-plan groups livep c))
   :hints (("Goal" :in-theory (enable fn-cat$c-live-plan fn-cat$c-group-live-count
                                      fn-cat$c-group-live-low fn-cat$c-group-live-high)))))

(local
 (defthm fn-cp-apply-plan-blind
   (equal (fn-cat$c-apply-plan plan seq (update-nth 0 r c))
          (update-nth 0 r (fn-cat$c-apply-plan plan seq c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-apply-plan)))))

(local
 (defthm fn-cp-live-apply-blind
   (equal (fn-cat$c-live-apply plan (update-nth 0 r c))
          (update-nth 0 r (fn-cat$c-live-apply plan c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-live-apply)))))

(local
 (defthm fn-cp-index-add-blind
   (equal (fn-cat$c-index-add m seq (update-nth 0 r c))
          (update-nth 0 r (fn-cat$c-index-add m seq c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-index-add)))))

(local
 (defthm fn-cp-index-clear-blind
   (equal (fn-cat$c-index-clear (update-nth 0 r c))
          (update-nth 0 r (fn-cat$c-index-clear c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-index-clear)))))

(local
 (defthm fn-cp-index-set-key-blind
   (equal (fn-cat$c-index-set-key key (update-nth 0 r c))
          (update-nth 0 r (fn-cat$c-index-set-key key c)))
   :hints (("Goal" :in-theory (enable fn-cat$c-index-set-key)))))

(local
 (defthm fn-cp-simple-readers-blind
   (and (equal (fn-cat$c-group-number g n (update-nth 0 r c)) (fn-cat$c-group-number g n c))
        (equal (fn-cat$c-group-next g (update-nth 0 r c)) (fn-cat$c-group-next g c))
        (equal (fn-cat$c-group-count g (update-nth 0 r c)) (fn-cat$c-group-count g c))
        (equal (fn-cat$c-total-octets (update-nth 0 r c)) (fn-cat$c-total-octets c))
        (equal (fn-cat$c-group-live-count g (update-nth 0 r c)) (fn-cat$c-group-live-count g c))
        (equal (fn-cat$c-group-live-low g (update-nth 0 r c)) (fn-cat$c-group-live-low g c))
        (equal (fn-cat$c-group-live-high g (update-nth 0 r c)) (fn-cat$c-group-live-high g c))
        (equal (fn-cat$c-horizon (update-nth 0 r c)) (fn-cat$c-horizon c))
        (equal (fn-cat$c-withdrawn-at w (update-nth 0 r c)) (fn-cat$c-withdrawn-at w c))
        (equal (fn-cat$c-wfp (update-nth 0 r c)) (<= (fn-cat$c-count c) (len r))))
   :hints (("Goal" :in-theory (enable fn-cat$c-group-number fn-cat$c-group-next fn-cat$c-group-count
                                      fn-cat$c-total-octets fn-cat$c-group-live-count
                                      fn-cat$c-group-live-low fn-cat$c-group-live-high
                                      fn-cat$c-horizon fn-cat$c-withdrawn-at fn-cat$c-wfp)))))

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
   (equal (fn-held-withdrawn (fn-cp-held s tx g p c st m wp wa wb e aux))
          (if e
              (adt-l-nth 1 (adt-l-nth 8 (let ((d (fn-scc-decode-tree aux)))
                                          (if (and (consp d) (eq (car d) :ok) (consp (cdr d)))
                                              (car (cdr d))
                                            nil))))
            (if wp (cons wa wb) nil)))
   :hints (("Goal" :in-theory (e/d (fn-cp-held) (fn-scc-decode-tree))))))

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
                                   (fn-cp-held fn-scc-decode-tree))))))

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

(local (in-theory (e/d (fn-cat$p-view) (fn-cat$p-at fn-cat$p-withdrawn-of fn-cat$p-at-is-row
                                          fn-cat$p-withdrawn-of-is-row fn-cp-view-row
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


; --- the live summary's scans and plans over the paged rows

(local
 (defthm fn-cat$p-live-at-p-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-live-at-p g k fn-cat$p)
                   (fn-cat$c-live-at-p g k (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (enable fn-cat$p-live-at-p fn-cat$c-live-at-p)))))

(local
 (defthm fn-cat$p-scan-up-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-scan-up g k top fn-cat$p)
                   (fn-cat$c-scan-up g k top (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-scan-up fn-cat$c-scan-up)
                                   (fn-cat$p-live-at-p fn-cat$c-live-at-p))
            :induct (fn-cat$p-scan-up g k top fn-cat$p)))))

(local
 (defthm fn-cat$p-scan-down-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-scan-down g k fn-cat$p)
                   (fn-cat$c-scan-down g k (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-scan-down fn-cat$c-scan-down)
                                   (fn-cat$p-live-at-p fn-cat$c-live-at-p))
            :induct (fn-cat$p-scan-down g k fn-cat$p)))))

(local
 (defthm fn-cat$p-drop-entry-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-drop-entry g k fn-cat$p)
                   (fn-cat$c-drop-entry g k (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-drop-entry fn-cat$c-drop-entry)
                                   (fn-cat$p-scan-up fn-cat$c-scan-up fn-cat$p-scan-down
                                    fn-cat$c-scan-down))))))

(local
 (defthm fn-cat$p-drop-plan-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (equal (fn-cat$p-drop-plan pairs target row fn-cat$p)
                   (fn-cat$c-drop-plan pairs target row (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-drop-plan fn-cat$c-drop-plan)
                                   (fn-cat$p-drop-entry fn-cat$c-drop-entry))
            :induct (fn-cat$p-drop-plan pairs target row fn-cat$p)))))

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
                               (nth 9 (fn-cp-row-of h)) (nth 10 (fn-cp-row-of h)) (nth 11 (fn-cp-row-of h)))
                   h))
   :hints (("Goal" :use fn-cp-row-held-of-row-of-any
            :in-theory (e/d (fn-cp-row-held adt-l-nth-is-nth) (fn-cp-row-held-of-row-of-any fn-cp-held))))))

(local
 (defthm fn-cp-overflow-of-is-h
   (implies (fn-cp-overflow-of h) (equal (fn-cp-overflow-of h) h))
   :hints (("Goal" :in-theory (enable fn-cp-overflow-of)))))

(local
 (defthm fn-cat$p-put-row-view
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (natp seq) (< seq (nth 1 (nth 1 fn-cat$p))) h)
            (equal (fn-cat$p-view (fn-cat$p-put-row seq h fn-cat$p))
                   (update-fn-cat$c-rowsi seq h (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :in-theory (e/d (fn-cat$p-put-row adt-set-a fn-cp-row-held adt-l-nth-is-nth)
                                   (fn-cp-row-of fn-cp-overflow-of fn-cp-held))
            :cases ((fn-cp-overflow-of h))))))

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
                 (x (fn-held-withdrawn h))
                 (c (fn-cat$c-apply-plan plan seq c))
                 (c (update-fn-cat$c-octets (+ (fn-cat$c-octets c) (nfix (fn-hf-octets (fn-held-facts h)))) c))
                 (c (update-fn-cat$c-count (+ 1 seq) c))
                 (c (fn-cat$c-live-apply lplan c))
                 (c (update-fn-cat$c-hz hz c)))
            (if (consp x)
                (fn-cat$c-wbv-put (car x) (fn-cat-insert-asc seq (fn-cat$c-wbv-get (car x) c)) c)
              c)))
   :hints (("Goal" :in-theory (enable fn-cat$p-tab-commit)))))

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
            :in-theory (e/d (fn-cat$p-commit-w fn-cat$c-commit-w fn-cat$c-commit fn-cat$c-commit-base)
                            (fn-cat$p-append-row fn-cat$p-tab-index-add fn-cat$p-tab-commit
                             fn-cat$c-live-plan fn-cat$c-plan fn-cat$c-apply-plan fn-cat$c-live-apply
                             fn-cat$c-index-add fn-cat$c-wbv-put fn-cat$c-wbv-get fn-held-with-numbers
                             fn-cat-plan-numbers fn-cat-insert-asc))))))

(local
 (defthm fn-cp-with-withdrawn-nonnil
   (fn-held-with-withdrawn h w)
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn)))))

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
                            (fn-cat$p-put-row fn-held-with-context))))))

(local
 (defthm fn-cp-view-of-tab-withdraw
   (equal (fn-cat$p-view (fn-cat$p-tab-withdraw dplan hz v target fn-cat$p))
          (let* ((c (fn-cat$p-view fn-cat$p))
                 (c (fn-cat$c-live-apply dplan c))
                 (c (update-fn-cat$c-hz hz c)))
            (fn-cat$c-wbv-put v (fn-cat-insert-asc target (fn-cat$c-wbv-get v c)) c)))
   :hints (("Goal" :in-theory (enable fn-cat$p-tab-withdraw)))))

(local
 (defthm fn-cp-put-row-shape
   (implies (and (natp seq) (< seq (len (nth 0 fn-cat$p)))
                 (<= (len (nth 0 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p)))))
            (and (equal (len (nth 0 (fn-cat$p-put-row seq h fn-cat$p))) (len (nth 0 fn-cat$p)))
                 (equal (nth 1 (nth 1 (fn-cat$p-put-row seq h fn-cat$p))) (nth 1 (nth 1 fn-cat$p)))
                 (equal (len (nth 0 (nth 1 (fn-cat$p-put-row seq h fn-cat$p))))
                        (len (nth 0 (nth 1 fn-cat$p))))))
   :hints (("Goal" :in-theory (enable fn-cat$p-put-row adt-set-a)))))

(local
 (defthm fn-cat$p-withdraw-w-sim
   (implies (and (equal (len (nth 0 fn-cat$p)) (nth 1 (nth 1 fn-cat$p)))
                 (<= (nth 1 (nth 1 fn-cat$p)) (len (nth 0 (nth 1 fn-cat$p))))
                 (natp target) (< target (nth 1 (nth 1 fn-cat$p))))
            (equal (fn-cat$p-view (fn-cat$p-withdraw-w target by fn-cat$p))
                   (fn-cat$c-withdraw-w target by (fn-cat$p-view fn-cat$p))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cat$p-withdraw-w fn-cat$c-withdraw-w fn-cat$c-withdraw
                             fn-cat$c-withdraw-base)
                            (fn-cat$p-put-row fn-cat$p-tab-withdraw fn-cat$p-drop-plan fn-cat$c-drop-plan
                             fn-cat$c-live-apply fn-cat$c-wbv-put fn-cat$c-wbv-get
                             fn-held-with-withdrawn fn-cat-insert-asc))))))

(local
 (defthm fn-cat$p-clear-w-sim
   (equal (fn-cat$p-view (fn-cat$p-clear-w fn-cat$p))
          (fn-cat$c-clear-w (fn-cat$p-view fn-cat$p)))
   :hints (("Goal" :in-theory (enable fn-cat$p-clear-w fn-cat$c-clear-w fn-cat$c-clear
                                      fn-cat$c-clear-base fn-cp-merge)))))

(local
 (defthm fn-cat$p-clear-keyed-sim
   (equal (fn-cat$p-view (fn-cat$p-clear-keyed key fn-cat$p))
          (fn-cat$c-clear-keyed key (fn-cat$p-view fn-cat$p)))
   :hints (("Goal" :in-theory (enable fn-cat$p-clear-keyed fn-cat$c-clear-keyed fn-cat$c-clear-w
                                      fn-cat$c-clear fn-cat$c-clear-base fn-cp-merge)))))

; -----------------------------------------------------------------------------
; 7. The obligations: each the old catalog's (books/catalog-logic.lisp), at the view.

(local
 (defthm fn-cp-corr-count-natp
   (implies (fn-cat$pcorr fn-cat$p fn-cat$a)
            (natp (nth 1 (nth 1 fn-cat$p))))
   :rule-classes :forward-chaining
   :hints (("Goal" :use fn-cp-corr-facts :in-theory (disable fn-cp-corr-facts)))))

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
   :hints (("Goal" :in-theory (e/d (fn-cat$p-commit-w fn-cat$p-tab-commit fn-cat$p-append-row
                                    fn-cat$p-count)
                                   (fn-cat$c-live-plan fn-cat$c-plan fn-cat$c-apply-plan
                                    fn-cat$c-live-apply fn-cat$c-index-add fn-cat$c-wbv-put
                                    fn-cat$c-wbv-get fn-cp-row-of fn-cp-overflow-of))))))

