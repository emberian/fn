; fn: the two durable kinds as one sequence-ordered stream (packet R5/R6 of
; specs/reconfiguration.md, the "two-kind on-disk interleaving" open item of
; its section 8).
;
; THE DECISION, stated before the proofs.  A store keeps its article records
; in the transaction journal and its configuration records under `config/',
; two directories, because a configuration record has its own codec and its
; own fsync order.  That is a LAYOUT choice.  The STREAM is one: every record
; of either kind carries its position in the unified stream in its own
; sequence field, and recovery merges the two files by that field before it
; replays anything.  `fn-cstr-merge' is that merge, and the book below is
; what earns the right to offer `set-capacity' at all:
;
;   * a configuration-only replay (`fn-cnode-config-replay', what the host
;     does today) admits a capacity decrease against the reservation total of
;     a node that has replayed NO articles, which is zero.  Every decrease is
;     admissible to it.  That is why `tools/run_store.py' does not offer the
;     command;
;   * the merged replay hands each configuration record to
;     `fn-cnode-record-acceptablep' at the node the EARLIER ARTICLE RECORDS
;     produced, so a decrease is re-checked against the reservation total
;     that was live when the operator's request was admitted.
;
; The two are not equal, and the separating witness is in
; `tests/acl2/config-stream-tests.lisp': a history the configuration-only
; replay accepts and the merged replay refuses with `:config-refusal'.  The
; merged replay is strictly the stronger one; it is the one `set-capacity'
; is safe under.
;
; This book owns the prefix `fn-cstr-' (docs/prefixes.md).  It adds no record
; shape: a merged element is the `fn-jrec' of books/config-records.lisp, and
; the loop it feeds is `fn-cnode-replay-loop' of books/node-config.lisp,
; unchanged, with its fold keystone
; `fn-cnode-replay-loop-splits-at-any-prefix' unchanged.

(in-package "ACL2")
(include-book "node-config")

; -----------------------------------------------------------------------------
; The two kinds, lifted to journal records

(defun fn-cstr-config-jrec (r)
  (declare (xargs :guard t))
  (fn-jrec-make :config (fn-cfg-record-sequence r) r))

(defun fn-cstr-article-jrec (r)
  (declare (xargs :guard t))
  (fn-jrec-make :article (fn-record-sequence r) r))

(defun fn-cstr-config-jrecs (rs)
  (declare (xargs :guard t))
  (if (consp rs)
      (cons (fn-cstr-config-jrec (car rs)) (fn-cstr-config-jrecs (cdr rs)))
    nil))

(defun fn-cstr-article-jrecs (rs)
  (declare (xargs :guard t))
  (if (consp rs)
      (cons (fn-cstr-article-jrec (car rs)) (fn-cstr-article-jrecs (cdr rs)))
    nil))

; `books/node-config' builds the configuration-only stream the host replays
; today; this book's config arm is that same list, so the two agree by
; definition and the equality is named for what it is.
(defthm fn-cstr-config-jrecs-is-fn-cnode-config-jrecs-by-definition
  (equal (fn-cstr-config-jrecs rs) (fn-cnode-config-jrecs rs)))

; -----------------------------------------------------------------------------
; The merge

(defun fn-cstr-merge (configs articles)
  ; The unified stream: the two durable kinds ordered by the sequence field
  ; each record already carries.  A configuration record ties with an article
  ; record only in a malformed history; it goes first, deterministically.
  (declare (xargs :guard t :measure (+ (len configs) (len articles))))
  (cond ((not (consp configs)) (fn-cstr-article-jrecs articles))
        ((not (consp articles)) (fn-cstr-config-jrecs configs))
        ((<= (nfix (fn-cfg-record-sequence (car configs)))
             (nfix (fn-record-sequence (car articles))))
         (cons (fn-cstr-config-jrec (car configs))
               (fn-cstr-merge (cdr configs) articles)))
        (t (cons (fn-cstr-article-jrec (car articles))
                 (fn-cstr-merge configs (cdr articles))))))

(defun fn-cstr-replay (configs articles)
  ; The entry point a host that interleaves would call at open, in place of
  ; `fn-cnode-config-replay' followed by an article-only replay.
  (declare (xargs :guard t))
  (fn-cnode-replay (fn-cstr-merge configs articles)))

; -----------------------------------------------------------------------------
; Losslessness: the merge drops nothing and invents nothing

(defun fn-cstr-kind-bodies (kind js)
  (declare (xargs :guard t))
  (if (consp js)
      (if (equal (fn-jrec-kind (car js)) kind)
          (cons (fn-jrec-body (car js)) (fn-cstr-kind-bodies kind (cdr js)))
        (fn-cstr-kind-bodies kind (cdr js)))
    nil))

(local (defthm fn-cstr-kind-bodies-of-config-jrecs
  (and (implies (true-listp rs)
                (equal (fn-cstr-kind-bodies :config (fn-cstr-config-jrecs rs))
                       rs))
       (equal (fn-cstr-kind-bodies :article (fn-cstr-config-jrecs rs))
              nil))))

(local (defthm fn-cstr-kind-bodies-of-article-jrecs
  (and (implies (true-listp rs)
                (equal (fn-cstr-kind-bodies :article (fn-cstr-article-jrecs rs))
                       rs))
       (equal (fn-cstr-kind-bodies :config (fn-cstr-article-jrecs rs))
              nil))))

(defthm fn-cstr-merge-length
  (equal (len (fn-cstr-merge configs articles))
         (+ (len configs) (len articles))))

; KEYSTONE.  The merged stream carries exactly the configuration records of
; the configuration directory, in order, and exactly the article records of
; the journal, in order.  Neither side is defined in terms of the other: the
; left walks the merge, the right walks the input file.
(defthm fn-cstr-merge-keeps-every-config-record
  (implies (true-listp configs)
           (equal (fn-cstr-kind-bodies :config (fn-cstr-merge configs articles))
                  configs)))

(defthm fn-cstr-merge-keeps-every-article-record
  (implies (true-listp articles)
           (equal (fn-cstr-kind-bodies :article (fn-cstr-merge configs articles))
                  articles)))

; -----------------------------------------------------------------------------
; Order: the merge is sequence-ordered when its inputs are

(defun fn-cstr-jrec-seqs (js)
  (declare (xargs :guard t))
  (if (consp js)
      (cons (nfix (fn-jrec-sequence (car js))) (fn-cstr-jrec-seqs (cdr js)))
    nil))

(defun fn-cstr-nondecreasingp (ns)
  (declare (xargs :guard t))
  (if (and (consp ns) (consp (cdr ns)))
      (and (<= (nfix (car ns)) (nfix (car (cdr ns))))
           (fn-cstr-nondecreasingp (cdr ns)))
    t))

(defun fn-cstr-config-seqs (rs)
  (declare (xargs :guard t))
  (if (consp rs)
      (cons (nfix (fn-cfg-record-sequence (car rs))) (fn-cstr-config-seqs (cdr rs)))
    nil))

(defun fn-cstr-article-seqs (rs)
  (declare (xargs :guard t))
  (if (consp rs)
      (cons (nfix (fn-record-sequence (car rs))) (fn-cstr-article-seqs (cdr rs)))
    nil))

(local (defthm fn-cstr-jrec-seqs-of-config-jrecs
  (equal (fn-cstr-jrec-seqs (fn-cstr-config-jrecs rs))
         (fn-cstr-config-seqs rs))))

(local (defthm fn-cstr-jrec-seqs-of-article-jrecs
  (equal (fn-cstr-jrec-seqs (fn-cstr-article-jrecs rs))
         (fn-cstr-article-seqs rs))))

; KEYSTONE.  Two sequence-ordered files merge into one sequence-ordered
; stream.  With `fn-jrec-sequences-from' (books/config-records) this is what
; says the layout split loses no ordering information: the unified stream the
; replay loop demands is recoverable from the two files alone.
(defthm fn-cstr-merge-is-sequence-ordered
  (implies (and (fn-cstr-nondecreasingp (fn-cstr-config-seqs configs))
                (fn-cstr-nondecreasingp (fn-cstr-article-seqs articles)))
           (fn-cstr-nondecreasingp
            (fn-cstr-jrec-seqs (fn-cstr-merge configs articles)))))

; -----------------------------------------------------------------------------
; What the merged replay buys, and the honest name for what it does not

; A configuration-only history merges to the stream the host replays today,
; so adopting the merge changes nothing about a store that has no articles.
; This is a definitional agreement, not a proof event.
(defthm fn-cstr-replay-of-a-config-only-history-is-fn-cnode-config-replay-by-definition
  (equal (fn-cstr-replay configs nil) (fn-cnode-config-replay configs))
  :hints (("Goal" :in-theory (enable (:d fn-cstr-replay) (:d fn-cstr-merge)
                                     (:d fn-cnode-config-replay)))))

(local (defthm fn-cstr-replay-loop-ok-is-a-configured-node
  (implies (equal (fn-replay-result-kind (fn-cnode-replay-loop cn ceiling js expected))
                  :ok)
           (fn-cnode-statep
            (fn-replay-result-node (fn-cnode-replay-loop cn ceiling js expected))))
  :hints (("Goal" :induct (fn-cnode-replay-loop cn ceiling js expected)
           :in-theory (e/d ((:d fn-cnode-replay-loop))
                           (fn-cnode-statep fn-cnode-apply-record
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-jrec-p))))))

; KEYSTONE (R6).  A merged replay that reports `:ok' ends in a configured
; node state -- which carries, through `fn-node-statep', the retention
; accounting invariant `reserved <= capacity'.  Every configuration record in
; the history was therefore admitted at a node that had already replayed the
; article records before it, and the capacity it set was above the
; reservation total live at its own position.  This is the statement
; `fn-cnode-config-replay' cannot make: its nodes have replayed no articles.
(defthm fn-cstr-ok-merged-replay-ends-in-a-configured-node
  (implies (equal (fn-replay-result-kind (fn-cstr-replay configs articles)) :ok)
           (fn-cnode-statep
            (fn-replay-result-node (fn-cstr-replay configs articles))))
  :hints (("Goal" :in-theory (e/d ((:d fn-cstr-replay) (:d fn-cnode-replay))
                                  (fn-cnode-replay-loop fn-cnode-statep
                                   fn-cstr-merge fn-cnode-initial)))))

; -----------------------------------------------------------------------------
; What a generation serves
;
; The served table of a generation is `fn-cfg-group-names' at that
; generation.  These two statements are what make a per-connection
; configuration pin (packet R5, `books/owner-config.lisp') mean something:
; the answer to "is this group served" is a question about a NUMBER, and the
; number partitions the connections into those that see a creation and those
; that do not.

; KEYSTONE.  A group created by the delta that produces generation g is
; served at every generation from g on, and at none below it.  Both
; directions: a connection pinned below g must not see it, which is the half
; a "creation is monotone" statement would silently drop.
(defthm fn-cstr-created-group-is-served-exactly-from-its-generation
  (implies (and (natp gen) (natp g2) (< 0 gen))
           (iff (fn-cfg-group-livep
                 (fn-cfg-apply-delta v gen stamp (fn-cfg-create-group name policy))
                 g2 name)
                (<= gen g2)))
  :hints (("Goal" :in-theory (enable (:d fn-cfg-apply-delta)
                                     (:d fn-cfg-create-group)
                                     (:d fn-cfg-group-livep)
                                     (:d fn-cfg-set-groups)))))

; KEYSTONE.  A group retired by the delta that produces generation g is
; served at every generation below g at which it was served, and at none
; from g on.  Retirement is a generation, never a deletion (NNT-006).
(defthm fn-cstr-retired-group-is-served-exactly-below-its-generation
  (implies (and (natp gen) (natp g2) (fn-cfg-group-livep v gen name))
           (iff (fn-cfg-group-livep
                 (fn-cfg-apply-delta v gen stamp (fn-cfg-remove-group name))
                 g2 name)
                (and (<= (fn-cfg-group-created-gen
                          (fn-cfg-group-find (fn-cfg-groups v) name))
                         g2)
                     (< g2 gen))))
  :hints (("Goal" :in-theory (enable (:d fn-cfg-apply-delta)
                                     (:d fn-cfg-remove-group)
                                     (:d fn-cfg-group-livep)
                                     (:d fn-cfg-set-groups)))))

; -----------------------------------------------------------------------------
; Export theory.

(deftheory fn-cstr-vocabulary
  '((:d fn-cstr-config-jrec) (:d fn-cstr-article-jrec)
    (:d fn-cstr-config-jrecs) (:d fn-cstr-article-jrecs)
    (:d fn-cstr-merge) (:d fn-cstr-replay) (:d fn-cstr-kind-bodies)
    (:d fn-cstr-jrec-seqs) (:d fn-cstr-nondecreasingp)
    (:d fn-cstr-config-seqs) (:d fn-cstr-article-seqs)))

(in-theory (disable fn-cstr-vocabulary))
