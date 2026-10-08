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
(include-book "def-representation-index")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The instance: what the index is told about the history's events.  The exact
; test at lookup is `fn-hist-article-matches'; an event whose exact article is
; a held record is keyed by that record.

(defun fn-hist-article-matches (msgid ev)
  (declare (xargs :guard t))
  (let ((rec (fn-cei-event-article ev)))
    (and (fn-held-p rec)
         (equal msgid (fn-record-msgid rec)))))

(defthm fn-hist-article-matches-by-definition
  (equal (fn-hist-article-matches msgid ev)
         (and (fn-held-p (fn-cei-event-article ev))
              (equal msgid (fn-record-msgid (fn-cei-event-article ev)))))
  :rule-classes nil)

(defthm fn-hist-held-p-is-not-hstxa-headed
  (implies (fn-held-p x) (not (equal (car x) :hstxa)))
  :hints (("Goal" :in-theory (enable fn-held-internals fn-record-internals
                                     fn-held-p))))

(defthm fn-hist-key-article-of-held
  (implies (fn-held-p (fn-cei-event-article x))
           (equal (fn-hist-key-article x) (fn-cei-event-article x)))
  :hints (("Goal" :in-theory (e/d (fn-cei-event-article fn-replay-composite-held)
                                  (fn-held-p)))))

(defthm fn-hist-held-msgid-stringp
  (implies (fn-held-p x) (stringp (fn-record-msgid x)))
  :hints (("Goal" :in-theory (enable fn-held-p fn-held-internals fn-record-internals
                                     fn-record-msgidp))))

(defthm fn-hist-query-of-atom
  (implies (not (consp events))
           (equal (fn-hist$a-msgid-records m events) nil)))

(defthm fn-hist-query-of-cons
  (equal (fn-hist$a-msgid-records m (cons x rest))
         (if (fn-hist-article-matches m x)
             (cons (fn-cei-event-article x) (fn-hist$a-msgid-records m rest))
           (fn-hist$a-msgid-records m rest)))
  )

; The exact test implies the key (stated over the test's body: the lemma
; assumes no predicate of its own).
(defthm fn-hist-article-matches-implies-key
  (implies (and (fn-held-p (fn-cei-event-article x))
                (equal m (fn-record-msgid (fn-cei-event-article x))))
           (and (stringp m) (equal (fn-hist-key-msgid x) m)))
  :hints (("Goal" :in-theory (e/d (fn-hist-key-msgid) (fn-hist-key-article fn-held-p fn-cei-event-article))
           :use ((:instance fn-hist-key-article-of-held)
                 (:instance fn-hist-held-msgid-stringp (x (fn-cei-event-article x)))))))


; -----------------------------------------------------------------------------
; The foundation, its fold and its obligations, derived
; (books/def-representation-index.lisp); the proofs over the key, hash and
; test are the generic ones (books/def-representation-index-lib.lisp).

(def-representation-index fn-hist (event :object)
  :index (:key fn-hist-key-msgid :key-p stringp :hash fn-hist-hash
          :test fn-hist-article-matches :project fn-cei-event-article
          :query-export fn-hist-msgid-records)
  :model (:recognizer fn-hist$ap :creator create-fn-hist$a
          :count fn-hist$a-count :at fn-hist$a-at :append fn-hist$a-append
          :clear fn-hist$a-clear :query fn-hist$a-msgid-records)
  :lemmas (fn-hist-hash-natp fn-hist-article-matches-implies-key
           fn-hist-query-of-atom fn-hist-query-of-cons))
