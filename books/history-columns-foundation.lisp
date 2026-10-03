; fn: the store's history as an abstract stobj (lane history-columns,
; 2026-09-27; the coordinator's decision on PKT-PRS-1's event-index half,
; PKT-PRS-3 and PKT-PRS-4; D27).
;
; The LOGICAL value is the store's history exactly as every theorem knows
; it: the true list of retained events (`fn-sf-records', books/store-files
; .lisp), oldest first, an event's sequence being its position.  The
; EXECUTABLE is columns: an array of rows by sequence (so sequence access is
; one array read: the event index's uint32 radix trie, PKT-PRS-4, has
; nothing left to do), the count, and a Message-ID table from a salted
; 32-bit FNV-1a hash of a Message-ID to the sequences whose article carries
; a Message-ID with that hash, newest first.  A lookup walks that bucket
; and compares every candidate EXACTLY (the article decided by
; `fn-cei-event-article', `fn-held-p', and `equal' on the Message-ID), so no
; answer assumes a Message-ID names one row or that the hash separates two
; (PKT-774: the worst case is below, with the figure).
;
; Stage 1 of three (the brief): this book is the stobj, its abstraction and
; the refinement of the operations the event index answers (count, the
; event at a sequence, the article records under a Message-ID) and the one
; that grows it (append), with the bridge to the store node's index
; (`fn-cei-*', books/consumer-event-index.lisp): under the correspondence
; the store maintains for that index, each index answer IS this stobj's
; answer over the same history.  Stage 2 threads the stobj where the index
; is read and retires the index; stage 3 moves held rows' strings into a
; byte pool behind the same logical side (the rows column then holds
; offsets; `fn-hist-at' rebuilds the row).
;
; The correspondence is equality with the fold: the concrete object IS the
; one built by appending the history's events, one at a time, to the empty
; object with its salt (`fn-hist-build').  So an append preserves it by the
; fold's own step, and every export reads a field of that fold.  The fold
; and the append read only digest-free functions (the key article is taken
; by shape, `fn-hist-key-article'), because a correspondence function may
; not have an attached supporter (ACL2 :doc stobj-attachment-restrictions;
; books/crypto-attach attaches `fn-digest', which `fn-held-p' reaches); the
; exact test at lookup is where `fn-held-p' runs.
;
; Cost (stage 1, measured in the record): per event one array slot (8 B),
; and per event whose article has a Message-ID one cons in its bucket
; (16 B) plus one hash-table entry per distinct hash; the row itself is
; shared with the list, not copied.  Worst case (PKT-774): the hash is not
; a keyed PRF.  It is FNV-1a from a 32-bit salt, and the one host call
; passes the constant 0 (host/owner-host.lisp, `fn-hist-load' at install),
; so the function is public: an adversary who can choose Message-IDs can put
; every article in one bucket.  A lookup is then N exact comparisons of held
; records, an append stays O(1) (a cons onto the bucket).  No answer
; depends on the hash.
(in-package "ACL2")
(include-book "history-columns-logic")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable (tau-system))))
; Keep positional column terms stable when loaded after a codec's ADT
; vocabulary. These optional surrounding rules are absent in the standalone
; dependency world; the local event disables only rules actually present.
(local
 (make-event
  (value
   (list 'in-theory
    (cons 'disable
     (append (and (getpropc 'adt-nth-0 'theorem nil (w state)) '(adt-nth-0))
             (and (getpropc 'adt-nth-1+ 'theorem nil (w state)) '(adt-nth-1+))))))))


; The foundation: the columns.

(defstobj fn-hist$c
  (fn-hist$c-rows :type (array t (0)) :resizable t)
  (fn-hist$c-count :type (integer 0 *) :initially 0)
  (fn-hist$c-mids :type (hash-table eql))
  (fn-hist$c-salt :type (unsigned-byte 32) :initially 0)
  :inline t)

(local
 (deftheory fn-hist-open
   '(fn-hist$c-count update-fn-hist$c-count fn-hist$c-rowsi update-fn-hist$c-rowsi
     resize-fn-hist$c-rows fn-hist$c-rows-length fn-hist$c-salt update-fn-hist$c-salt
     fn-hist$c-mids-get fn-hist$c-mids-put fn-hist$c-mids-clear update-nth-array)))

(defun fn-hist$c-count-of (fn-hist$c)
  (declare (xargs :stobjs fn-hist$c))
  (fn-hist$c-count fn-hist$c))

(defun fn-hist$c-at (seq fn-hist$c)
  (declare (xargs :stobjs fn-hist$c
                  :guard (and (natp seq) (< seq (fn-hist$c-rows-length fn-hist$c)))))
  (fn-hist$c-rowsi seq fn-hist$c))

; Room for one more row: the rows column doubles (at least 16), so an
; append is amortized O(1); the growth is a function of the old length and
; the count alone, so the fold below fixes it.
(defun fn-hist$c-grow (fn-hist$c)
  (declare (xargs :stobjs fn-hist$c))
  (let ((n (fn-hist$c-count fn-hist$c))
        (cap (fn-hist$c-rows-length fn-hist$c)))
    (if (< n cap)
        fn-hist$c
      (resize-fn-hist$c-rows (max 16 (* 2 (max n cap))) fn-hist$c))))

(local
 (defthm fn-hist-len-of-resize-list
   (equal (len (resize-list l n d)) (nfix n))
   :hints (("Goal" :in-theory (enable resize-list)))))

(local
 (defthm fn-hist-rows-length-of-grow
   (implies (natp (nth 1 fn-hist$c))
            (< (nth 1 fn-hist$c) (len (nth 0 (fn-hist$c-grow fn-hist$c)))))
   :rule-classes :linear))

(local
 (defthm fn-hist-grow-fields
   (and (equal (nth 1 (fn-hist$c-grow fn-hist$c)) (nth 1 fn-hist$c))
        (equal (nth 2 (fn-hist$c-grow fn-hist$c)) (nth 2 fn-hist$c))
        (equal (nth 3 (fn-hist$c-grow fn-hist$c)) (nth 3 fn-hist$c)))))

(local
 (defthm fn-hist-rowsp-of-anything
   (equal (fn-hist$c-rowsp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-hist$c-rowsp)))))

(local
 (defthm fn-hist-cp-of-grow
   (implies (fn-hist$cp fn-hist$c)
            (fn-hist$cp (fn-hist$c-grow fn-hist$c)))))

(defun fn-hist$c-append (ev fn-hist$c)
  (declare (xargs :stobjs fn-hist$c))
  (let* ((n (fn-hist$c-count fn-hist$c))
         (fn-hist$c (fn-hist$c-grow fn-hist$c))
         (fn-hist$c (update-fn-hist$c-rowsi n ev fn-hist$c))
         (m (fn-hist-key-msgid ev))
         (fn-hist$c (if (stringp m)
                        (let ((h (fn-hist-hash m (fn-hist$c-salt fn-hist$c))))
                          (fn-hist$c-mids-put
                           h (cons n (fn-hist$c-mids-get h fn-hist$c)) fn-hist$c))
                      fn-hist$c)))
    (update-fn-hist$c-count (1+ n) fn-hist$c)))

; The bucket's candidates, newest first, collected onto ACC with the exact
; test: the result is oldest first.
(defun fn-hist$c-collect (msgid seqs acc fn-hist$c)
  (declare (xargs :stobjs fn-hist$c :guard (stringp msgid)))
  (if (consp seqs)
      (let ((i (car seqs)))
        (if (and (natp i) (< i (fn-hist$c-rows-length fn-hist$c)))
            (let ((rec (fn-cei-event-article (fn-hist$c-rowsi i fn-hist$c))))
              (fn-hist$c-collect msgid (cdr seqs)
                                 (if (and (fn-held-p rec)
                                          (equal msgid (fn-record-msgid rec)))
                                     (cons rec acc)
                                   acc)
                                 fn-hist$c))
          (fn-hist$c-collect msgid (cdr seqs) acc fn-hist$c)))
    acc))

(defun fn-hist$c-msgid-records (msgid fn-hist$c)
  (declare (xargs :stobjs fn-hist$c :guard (stringp msgid)))
  (fn-hist$c-collect msgid
                     (fn-hist$c-mids-get
                      (fn-hist-hash msgid (fn-hist$c-salt fn-hist$c)) fn-hist$c)
                     nil fn-hist$c))

(defun fn-hist$c-clear (salt fn-hist$c)
  (declare (xargs :stobjs fn-hist$c :guard (unsigned-byte-p 32 salt)))
  (let* ((fn-hist$c (resize-fn-hist$c-rows 0 fn-hist$c))
         (fn-hist$c (update-fn-hist$c-count 0 fn-hist$c))
         (fn-hist$c (fn-hist$c-mids-clear fn-hist$c)))
    (update-fn-hist$c-salt salt fn-hist$c)))

; -----------------------------------------------------------------------------
; The correspondence: the object is the fold of the history's appends from
; the empty object with its salt.

(defun fn-hist$c-empty (salt)
  (declare (xargs :guard t))
  (list nil 0 nil salt))

(defun-nx fn-hist-build (events c)
  (if (consp events)
      (fn-hist-build (cdr events) (fn-hist$c-append (car events) c))
    c))

(defun-nx fn-hist$corr (fn-hist$c fn-hist$a)
  (and (fn-hist$cp fn-hist$c)
       (true-listp fn-hist$a)
       (equal fn-hist$c
              (fn-hist-build fn-hist$a (fn-hist$c-empty (nth 3 fn-hist$c))))))

; -----------------------------------------------------------------------------
; The fold, field by field.

(local
 (defun fn-hist-resize-induct (i l k)
   (if (and (posp k) (posp i))
       (fn-hist-resize-induct (1- i) (if (consp l) (cdr l) l) (1- k))
     (list i l k))))

(local
 (defthm fn-hist-resize-list-open
   (and (implies (posp k)
                 (equal (resize-list l k d)
                        (cons (if (atom l) d (car l))
                              (resize-list (if (atom l) l (cdr l)) (1- k) d))))
        (implies (not (posp k))
                 (equal (resize-list l k d) nil))
        (equal (car (resize-list l k d))
               (if (posp k) (if (atom l) d (car l)) nil)))
   :hints (("Goal" :in-theory (enable resize-list)))))

(local
 (defthm fn-hist-nth-of-resize-list
   (implies (natp i)
            (equal (nth i (resize-list l k nil))
                   (if (< i (nfix k)) (nth i l) nil)))
   :hints (("Goal" :in-theory (union-theories
             '(fn-hist-resize-induct fn-hist-resize-list-open nth nfix natp posp zp
               not car-cons cdr-cons fold-consts-in-+)
             (theory 'minimal-theory))
            :induct (fn-hist-resize-induct i l k)))))

(local (in-theory (disable fn-hist-resize-list-open)))

(local
 (defthm fn-hist-append-fields
   (and (equal (nth 1 (fn-hist$c-append x c)) (1+ (nth 1 c)))
        (equal (nth 3 (fn-hist$c-append x c)) (nth 3 c))
        (equal (nth 0 (fn-hist$c-append x c))
               (update-nth (nth 1 c) x (nth 0 (fn-hist$c-grow c))))
        (equal (nth 2 (fn-hist$c-append x c))
               (if (stringp (fn-hist-key-msgid x))
                   (let ((h (fn-hist-hash (fn-hist-key-msgid x) (nth 3 c))))
                     (cons (cons h (cons (nth 1 c)
                                         (cdr (hons-assoc-equal h (nth 2 c)))))
                           (nth 2 c)))
                 (nth 2 c))))
   :hints (("Goal" :use ((:instance fn-hist-grow-fields (fn-hist$c c)))
             :in-theory (union-theories
              '(fn-hist-open fn-hist$c-append nth-update-nth car-cons cdr-cons
                fold-consts-in-+ nfix natp zp)
              (theory 'minimal-theory))))))

(local (in-theory (disable fn-hist$c-append)))

(defthm fn-hist-build-of-append-one
  (equal (fn-hist-build (append events (list x)) c)
         (fn-hist$c-append x (fn-hist-build events c)))
  :hints (("Goal" :in-theory (enable fn-hist-build))))

(local
 (defthm fn-hist-build-count
   (implies (natp (nth 1 c))
            (equal (nth 1 (fn-hist-build events c))
                   (+ (nth 1 c) (len events))))
   :hints (("Goal" :in-theory (enable fn-hist-build)))))

(local
 (defthm fn-hist-build-salt
   (equal (nth 3 (fn-hist-build events c)) (nth 3 c))
   :hints (("Goal" :in-theory (enable fn-hist-build)))))

(local
 (defthm fn-hist-append-room
   (implies (natp (nth 1 c))
            (< (nth 1 c) (len (nth 0 (fn-hist$c-append x c)))))
   :rule-classes :linear))

(local
 (defthm fn-hist-build-room
   (implies (and (natp (nth 1 c)) (<= (nth 1 c) (len (nth 0 c))))
            (<= (nth 1 (fn-hist-build events c))
                (len (nth 0 (fn-hist-build events c)))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-hist-build) (fn-hist-append-fields))
            :induct (fn-hist-build events c))
           ("Subgoal *1/1" :use ((:instance fn-hist-append-fields (x (car events)))
                                 (:instance fn-hist-append-room (x (car events))))))))

(local
 (defthm fn-hist-grow-rows-below
   (implies (and (natp i) (natp (nth 1 c)) (< i (nth 1 c)))
            (equal (nth i (nth 0 (fn-hist$c-grow c)))
                   (nth i (nth 0 c))))
   :hints (("Goal" :in-theory (e/d (fn-hist-open) (nth update-nth resize-list))))))

(local
 (defthm fn-hist-append-rows-below
   (implies (and (natp i) (natp (nth 1 c)) (< i (nth 1 c)))
            (equal (nth i (nth 0 (fn-hist$c-append x c)))
                   (nth i (nth 0 c))))
   :hints (("Goal" :in-theory (disable fn-hist$c-grow nth update-nth)))))

(local
 (defthm fn-hist-append-rows-at
   (implies (natp (nth 1 c))
            (equal (nth (nth 1 c) (nth 0 (fn-hist$c-append x c))) x))))

(local
 (defthm fn-hist-nth-cons-natural
  (implies (natp i)
   (equal (nth i (cons x xs))
          (if (zp i) x (nth (- i 1) xs))))
  :hints (("Goal" :in-theory (union-theories
             '(nth nfix natp zp car-cons cdr-cons) (theory 'minimal-theory))))))

(local
 (defthm fn-hist-build-rows
   (implies (and (natp i) (natp (nth 1 c))
                 (< i (+ (nth 1 c) (len events))))
            (equal (nth i (nth 0 (fn-hist-build events c)))
                   (if (< i (nth 1 c))
                       (nth i (nth 0 c))
                     (nth (- i (nth 1 c)) events))))
   :hints (("Goal" :in-theory (e/d (fn-hist-build fn-hist-nth-cons-natural)
                             (fn-hist$c-grow fn-hist$c-append nth update-nth))
            :induct (fn-hist-build events c)))))

(local
 (defthm fn-hist-cp-of-writes
   (implies (fn-hist$cp c)
            (and (implies (and (natp i) (< i (fn-hist$c-rows-length c)))
                          (fn-hist$cp (update-fn-hist$c-rowsi i v c)))
                 (fn-hist$cp (fn-hist$c-mids-put k v c))
                 (implies (natp n) (fn-hist$cp (update-fn-hist$c-count n c)))))
   :hints (("Goal" :in-theory (enable fn-hist-open fn-hist$cp fn-hist$c-rowsp)))))

(local
 (defthm fn-hist-grow-rows-length
   (implies (natp (fn-hist$c-count c))
            (< (fn-hist$c-count c) (fn-hist$c-rows-length (fn-hist$c-grow c))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-hist-open) (fn-hist$c-grow nth))
            :use ((:instance fn-hist-rows-length-of-grow (fn-hist$c c)))))))

(local
 (defthm fn-hist-grow-count
   (equal (fn-hist$c-count (fn-hist$c-grow c)) (fn-hist$c-count c))
   :hints (("Goal" :in-theory (e/d (fn-hist-open) (fn-hist$c-grow))))))

(local
 (defthm fn-hist-count-natp-of-cp
   (implies (fn-hist$cp c) (natp (fn-hist$c-count c)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-hist-open fn-hist$cp)))))

(local
 (defthm fn-hist-cp-of-append
   (implies (fn-hist$cp c) (fn-hist$cp (fn-hist$c-append x c)))
   :hints (("Goal" :in-theory (e/d (fn-hist$c-append)
                                   (fn-hist$cp fn-hist$c-grow fn-hist-key-msgid fn-hist-hash
                                    fn-hist$c-count fn-hist$c-rows-length
                                    update-fn-hist$c-rowsi fn-hist$c-mids-put
                                    update-fn-hist$c-count))))))

(local
 (defthm fn-hist-build-cp
   (implies (fn-hist$cp c) (fn-hist$cp (fn-hist-build events c)))
   :hints (("Goal" :in-theory (e/d (fn-hist-build) (fn-hist$cp))))))

; -----------------------------------------------------------------------------
; The Message-ID column over the fold.

; Every event whose exact article is a held record is keyed by that record.
(defthm fn-hist-held-p-is-not-hstxa-headed
  (implies (fn-held-p x) (not (equal (car x) :hstxa)))
  :hints (("Goal" :in-theory (enable fn-held-internals fn-record-internals
                                     fn-held-p))))

(defthm fn-hist-key-article-of-held
  (implies (fn-held-p (fn-cei-event-article x))
           (equal (fn-hist-key-article x) (fn-cei-event-article x)))
  :hints (("Goal" :in-theory (e/d (fn-cei-event-article fn-replay-composite-held)
                                  (fn-held-p)))))

(defun fn-hist-below-p (s n)
  (declare (xargs :guard t))
  (if (consp s)
      (and (natp (car s)) (< (car s) (nfix n)) (fn-hist-below-p (cdr s) n))
    t))

(local
 (defthm fn-hist-below-p-monotone
   (implies (and (fn-hist-below-p s n) (natp n) (natp k) (<= n k))
            (fn-hist-below-p s k))))

(local
 (defthm fn-hist-collect-append-acc
   (equal (fn-hist$c-collect m s (append a b) c)
          (append (fn-hist$c-collect m s a c) b))
   :hints (("Goal" :in-theory (disable fn-held-p fn-cei-event-article)))))

(local
 (defthm fn-hist-collect-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-hist$c-collect m s acc c)
                   (append (fn-hist$c-collect m s nil c) acc)))
   :hints (("Goal" :use ((:instance fn-hist-collect-append-acc (a nil) (b acc)))
            :in-theory (disable fn-hist-collect-append-acc)))))

(local
 (defthm fn-hist-collect-true-listp
   (implies (true-listp acc) (true-listp (fn-hist$c-collect m s acc c)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (disable fn-hist-collect-acc fn-hist-collect-append-acc
                                       fn-held-p fn-cei-event-article)))))

(local
 (defthm fn-hist-collect-of-append-below
   (implies (and (fn-hist-below-p s (nth 1 c))
                 (natp (nth 1 c))
                 (<= (nth 1 c) (len (nth 0 c))))
            (equal (fn-hist$c-collect m s acc (fn-hist$c-append x c))
                   (fn-hist$c-collect m s acc c)))
   :hints (("Goal" :in-theory (e/d (fn-hist-open)
                                   (nth update-nth fn-hist-collect-acc
                                    fn-hist-collect-append-acc fn-held-p
                                    fn-cei-event-article fn-hist$c-grow (:definition fn-hist$c-collect)))
            :induct (fn-hist$c-collect m s acc c)
            :expand ((fn-hist$c-collect m s acc c)
                     (fn-hist$c-collect m s acc (fn-hist$c-append x c)))))))

(defun fn-hist$c-bucket (h c)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (hons-assoc-equal h (nth 2 c))))

(local
 (defthm fn-hist-bucket-of-append
   (equal (fn-hist$c-bucket h (fn-hist$c-append x c))
          (if (and (stringp (fn-hist-key-msgid x))
                   (equal h (fn-hist-hash (fn-hist-key-msgid x) (nth 3 c))))
              (cons (nth 1 c) (fn-hist$c-bucket h c))
            (fn-hist$c-bucket h c)))
   :hints (("Goal" :in-theory (disable fn-hist-hash fn-hist-key-msgid nth
                                       update-nth fn-hist$c-grow)))))

(local
 (defthm fn-hist-below-p-of-append
   (implies (and (fn-hist-below-p (fn-hist$c-bucket h c) (nth 1 c))
                 (natp (nth 1 c)))
            (fn-hist-below-p (fn-hist$c-bucket h (fn-hist$c-append x c))
                             (1+ (nth 1 c))))
   :hints (("Goal" :in-theory (disable fn-hist-hash fn-hist-key-msgid nth
                                       update-nth fn-hist$c-grow fn-hist$c-bucket)))))

(local
 (defthm fn-hist-msgid-records-is-collect-bucket
   (equal (fn-hist$c-msgid-records m c)
          (fn-hist$c-collect m (fn-hist$c-bucket (fn-hist-hash m (nth 3 c)) c)
                             nil c))
   :hints (("Goal" :in-theory (enable fn-hist-open)))))

(local (in-theory (disable fn-hist$c-bucket fn-hist$c-msgid-records)))

(local
 (defthm fn-hist-records-for-of-one
   (equal (fn-cei-article-records-for m (cons x rest))
          (if (and (fn-held-p (fn-cei-event-article x))
                   (equal m (fn-record-msgid (fn-cei-event-article x))))
              (cons (fn-cei-event-article x)
                    (fn-cei-article-records-for m rest))
            (fn-cei-article-records-for m rest)))))

(local
 (defthm fn-hist-msgid-records-of-append
   (implies (and (stringp m)
                 (natp (nth 1 c))
                 (<= (nth 1 c) (len (nth 0 c)))
                 (fn-hist-below-p (fn-hist$c-bucket (fn-hist-hash m (nth 3 c)) c)
                                  (nth 1 c)))
            (equal (fn-hist$c-msgid-records m (fn-hist$c-append x c))
                   (append (fn-hist$c-msgid-records m c)
                           (fn-cei-article-records-for m (list x)))))
   :hints (("Goal" :in-theory (e/d (fn-hist-open fn-hist-key-msgid)
                                   (nth update-nth fn-held-p fn-cei-event-article
                                    fn-hist-key-article fn-hist-hash))
            :expand ((:free (acc c) (fn-hist$c-collect m (cons (nth 1 c) s) acc c)))
            :use ((:instance fn-hist-key-article-of-held))))))

(local
 (defthm fn-hist-records-for-split
   (implies (consp events)
            (equal (fn-cei-article-records-for m events)
                   (append (fn-cei-article-records-for m (list (car events)))
                           (fn-cei-article-records-for m (cdr events)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-held-p fn-cei-event-article)))))

(local
 (defthm fn-hist-msgid-records-true-listp
   (true-listp (fn-hist$c-msgid-records m c))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm fn-hist-records-for-of-atom
   (implies (not (consp events))
            (equal (fn-cei-article-records-for m events) nil))))

(local (in-theory (disable fn-hist-msgid-records-is-collect-bucket
                           fn-hist-bucket-of-append fn-hist-collect-of-append-below
                           fn-hist-records-for-of-one)))

(local
 (defthm fn-hist-build-msgid-records
   (implies (and (stringp m)
                 (natp (nth 1 c))
                 (<= (nth 1 c) (len (nth 0 c)))
                 (fn-hist-below-p (fn-hist$c-bucket (fn-hist-hash m (nth 3 c)) c)
                                  (nth 1 c)))
            (equal (fn-hist$c-msgid-records m (fn-hist-build events c))
                   (append (fn-hist$c-msgid-records m c)
                           (fn-cei-article-records-for m events))))
   :hints (("Goal" :in-theory (e/d (fn-hist-build)
                                   (fn-cei-article-records-for fn-held-p
                                    fn-cei-event-article fn-hist-hash
                                    fn-hist-fnv nth update-nth))
            :induct (fn-hist-build events c))
           ("Subgoal *1/1" :use ((:instance fn-hist-records-for-split)
                                 (:instance fn-hist-below-p-of-append
                                            (x (car events))
                                            (h (fn-hist-hash m (nth 3 c)))))))))

; -----------------------------------------------------------------------------
; The defabsstobj obligations.  Each is proved over an object that IS a fold
; from the empty object with some salt S (the `-of-build' lemmas: the
; variable is then substitutable), then instantiated at the object's own
; salt, which is what the correspondence says.

(local
 (defthm fn-hist-empty-fields
   (and (equal (nth 0 (fn-hist$c-empty s)) nil)
        (equal (nth 1 (fn-hist$c-empty s)) 0)
        (equal (nth 2 (fn-hist$c-empty s)) nil)
        (equal (nth 3 (fn-hist$c-empty s)) s))))

(local
 (defthm fn-hist-empty-bucket
   (equal (fn-hist$c-bucket h (fn-hist$c-empty s)) nil)
   :hints (("Goal" :in-theory (enable fn-hist$c-bucket)))))

(local
 (defthm fn-hist-empty-msgid-records
   (equal (fn-hist$c-msgid-records m (fn-hist$c-empty s)) nil)
   :hints (("Goal" :in-theory (e/d (fn-hist-msgid-records-is-collect-bucket)
                                   (fn-hist$c-empty fn-hist-hash))))))

(local (in-theory (disable fn-hist$c-empty)))

(local
 (defthm fn-hist-count-of-build
   (implies (equal c (fn-hist-build a (fn-hist$c-empty s)))
            (equal (nth 1 c) (len a)))))

(local
 (defthm fn-hist-room-of-build
   (implies (equal c (fn-hist-build a (fn-hist$c-empty s)))
            (<= (len a) (len (nth 0 c))))
   :hints (("Goal" :use ((:instance fn-hist-build-room (events a)
                                    (c (fn-hist$c-empty s))))
            :in-theory (disable fn-hist-build-room)))))

(local
 (defthm fn-hist-at-of-build
   (implies (and (equal c (fn-hist-build a (fn-hist$c-empty s)))
                 (natp seq) (< seq (len a)))
            (equal (nth seq (nth 0 c)) (nth seq a)))
   :hints (("Goal" :in-theory (disable nth fn-hist-build-rows)
            :use ((:instance fn-hist-build-rows (i seq) (events a)
                             (c (fn-hist$c-empty s))))))))

(local
 (defthm fn-hist-msgid-records-of-build
   (implies (and (equal c (fn-hist-build a (fn-hist$c-empty s)))
                 (stringp m))
            (equal (fn-hist$c-msgid-records m c)
                   (fn-cei-article-records-for m a)))
   :hints (("Goal" :in-theory (disable fn-cei-article-records-for fn-held-p
                                       fn-cei-event-article)))))

(local (in-theory (disable fn-hist$corr)))

(local
 (defthm fn-hist-corr-facts
   (implies (fn-hist$corr c a)
            (and (fn-hist$cp c)
                 (true-listp a)
                 (equal (nth 1 c) (len a))
                 (<= (len a) (len (nth 0 c)))
                 (implies (and (natp seq) (< seq (len a)))
                          (equal (nth seq (nth 0 c)) (nth seq a)))
                 (implies (stringp m)
                          (equal (fn-hist$c-msgid-records m c)
                                 (fn-cei-article-records-for m a)))))
   :hints (("Goal" :in-theory (e/d (fn-hist$corr)
                                   (fn-hist-count-of-build fn-hist-room-of-build
                                    fn-hist-at-of-build fn-hist-msgid-records-of-build
                                    fn-cei-article-records-for fn-held-p
                                    fn-cei-event-article nth))
            :use ((:instance fn-hist-count-of-build (s (nth 3 c)))
                  (:instance fn-hist-room-of-build (s (nth 3 c)))
                  (:instance fn-hist-at-of-build (s (nth 3 c)))
                  (:instance fn-hist-msgid-records-of-build (s (nth 3 c))))))))

(defthm create-fn-hist{correspondence}
  (fn-hist$corr (create-fn-hist$c) (create-fn-hist$a))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hist$corr fn-hist$c-empty fn-hist-build))))

(defthm create-fn-hist{preserved}
  (fn-hist$ap (create-fn-hist$a))
  :rule-classes nil)

(defthm fn-hist-count{correspondence}
  (implies (and (fn-hist$corr fn-hist$c fn-hist)
                (fn-hist$ap fn-hist))
           (equal (fn-hist$c-count fn-hist$c) (fn-hist$a-count fn-hist)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hist-open))))

(defthm fn-hist-at{correspondence}
  (implies (and (fn-hist$corr fn-hist$c fn-hist)
                (natp seq) (fn-hist$ap fn-hist) (< seq (fn-hist$a-count fn-hist)))
           (equal (fn-hist$c-at seq fn-hist$c) (fn-hist$a-at seq fn-hist)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hist-open) (nth)))))

(defthm fn-hist-at{guard-thm}
  (implies (and (fn-hist$corr fn-hist$c fn-hist)
                (natp seq) (fn-hist$ap fn-hist) (< seq (fn-hist$a-count fn-hist)))
           (and (natp seq) (< seq (fn-hist$c-rows-length fn-hist$c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hist-open) (nth fn-hist-corr-facts))
           :use ((:instance fn-hist-corr-facts (c fn-hist$c) (a fn-hist))))))

(defthm fn-hist-msgid-records{correspondence}
  (implies (and (fn-hist$corr fn-hist$c fn-hist)
                (stringp msgid) (fn-hist$ap fn-hist))
           (equal (fn-hist$c-msgid-records msgid fn-hist$c)
                  (fn-hist$a-msgid-records msgid fn-hist)))
  :rule-classes nil)

(defthm fn-hist-append{correspondence}
  (implies (and (fn-hist$corr fn-hist$c fn-hist) (fn-hist$ap fn-hist))
           (fn-hist$corr (fn-hist$c-append ev fn-hist$c)
                         (fn-hist$a-append ev fn-hist)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hist$corr) (fn-hist-corr-facts))
           :use ((:instance fn-hist-build-of-append-one
                            (events fn-hist) (x ev)
                            (c (fn-hist$c-empty (nth 3 fn-hist$c))))))))

(defthm fn-hist-append{preserved}
  (implies (fn-hist$ap fn-hist)
           (fn-hist$ap (fn-hist$a-append ev fn-hist)))
  :rule-classes nil)

(local
 (defthm fn-hist-clear-is-empty
   (implies (fn-hist$cp c)
            (equal (fn-hist$c-clear salt c) (fn-hist$c-empty salt)))
   :hints (("Goal" :in-theory (enable fn-hist-open fn-hist$cp fn-hist$c-empty update-nth)
            :expand ((len c) (len (cdr c)) (len (cddr c)) (len (cdddr c))
                     (len (cddddr c)))))))

(defthm fn-hist-clear{correspondence}
  (implies (and (fn-hist$corr fn-hist$c fn-hist)
                (unsigned-byte-p 32 salt))
           (fn-hist$corr (fn-hist$c-clear salt fn-hist$c)
                         (fn-hist$a-clear salt fn-hist)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hist$corr fn-hist-build fn-hist$c-empty))))

(defthm fn-hist-clear{preserved}
  (implies (and (fn-hist$ap fn-hist) (unsigned-byte-p 32 salt))
           (fn-hist$ap (fn-hist$a-clear salt fn-hist)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The history.


(local
 (defun-nx fn-hist-model-build-induct (events h c)
   (if (consp events)
       (fn-hist-model-build-induct (cdr events) (append h (list (car events)))
                                  (fn-hist$c-append (car events) c))
     (list h c))))

(local
 (defthm fn-hist-build-preserves-correspondence
   (implies (and (fn-hist$corr c h) (fn-hist$ap h) (true-listp events))
            (fn-hist$corr (fn-hist-build events c) (append h events)))
   :hints (("Goal" :induct (fn-hist-model-build-induct events h c)
            :in-theory (e/d (fn-hist-build fn-hist$ap fn-hist$a-append)
                            (fn-hist$corr fn-hist$c-append)))
           ("Subgoal *1/1" :use ((:instance fn-hist-append{correspondence}
                                             (fn-hist$c c) (fn-hist h) (ev (car events))))))))

(local
 (defthm fn-hist-empty-establishes-correspondence
   (implies (unsigned-byte-p 32 salt) (fn-hist$corr (fn-hist$c-empty salt) nil))
   :hints (("Goal" :in-theory (enable fn-hist$corr fn-hist$c-empty fn-hist$cp
                                      fn-hist$c-rowsp fn-hist-build)))))

; Shared fold boundary for alternate physical history implementations. The
; index is shared by ordinals while its events may reside in another backing.
(defthm fn-hist-fold-establishes-correspondence
  (implies (and (true-listp h) (unsigned-byte-p 32 salt))
           (fn-hist$corr (fn-hist-build h (fn-hist$c-empty salt)) h))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hist$ap)
                                  (fn-hist$corr fn-hist$c-empty fn-hist-build))
           :use ((:instance fn-hist-build-preserves-correspondence
                            (events h) (h nil) (c (fn-hist$c-empty salt)))))))

(local
 (defthm fn-hist-build-bucket-below
   (implies (and (natp (nth 1 c))
                 (fn-hist-below-p (fn-hist$c-bucket key c) (nth 1 c)))
            (fn-hist-below-p (fn-hist$c-bucket key (fn-hist-build events c))
                             (+ (nth 1 c) (len events))))
   :hints (("Goal" :induct (fn-hist-build events c)
            :in-theory (e/d (fn-hist-build)
                            (fn-hist$c-bucket fn-hist$c-append fn-hist-hash
                             fn-hist-key-msgid nth update-nth))))))

(defthm fn-hist-fold-table-facts
  (let ((c (fn-hist-build h (fn-hist$c-empty salt))))
    (implies (and (true-listp h) (unsigned-byte-p 32 salt))
      (and (equal (nth 1 c) (len h))
           (<= (len h) (len (nth 0 c)))
           (equal (nth 3 c) salt)
           (fn-hist-below-p (fn-hist$c-bucket key c) (len h))
           (implies (and (natp seq) (< seq (len h)))
                    (equal (nth seq (nth 0 c)) (nth seq h))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-hist$c-empty fn-hist-build fn-hist$c-bucket nth)
           :use ((:instance fn-hist-build-bucket-below
                            (events h) (c (fn-hist$c-empty salt)))
                 (:instance fn-hist-room-of-build
                            (a h) (s salt)
                            (c (fn-hist-build h (fn-hist$c-empty salt))))
                 (:instance fn-hist-at-of-build
                            (a h) (s salt)
                            (c (fn-hist-build h (fn-hist$c-empty salt))))))))

(defthm fn-hist-fold-mids-of-append
 (let* ((c (fn-hist-build h (fn-hist$c-empty salt)))
        (m (fn-hist-key-msgid ev)))
  (implies (and (true-listp h) (unsigned-byte-p 32 salt))
   (equal (nth 2 (fn-hist-build (append h (list ev)) (fn-hist$c-empty salt)))
          (if (stringp m)
              (let ((key (fn-hist-hash m salt)))
               (cons (cons key (cons (len h) (cdr (hons-assoc-equal key (nth 2 c)))))
                     (nth 2 c)))
            (nth 2 c)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-hist-build fn-hist$c-append fn-hist$c-empty
                                      nth fn-hist-key-msgid fn-hist-hash))))
