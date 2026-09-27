; fn: the maintained relation between the catalog, the arena and the store's
; history (wave 5, lane catalog-slice step 6, 2026-09-26; D33; the
; consolidation design 1.5).
;
; R(C, A, S): every row of the catalog, materialized by its handle from the
; arena (alpha, books/catalog-record.lisp fn-held-wire-of), is the ARTICLE
; record at that position of the store's history, in order.  The history
; (fn-sf-records, books/store-files.lisp) holds every event kind -- article
; records beside retention, identity, consumer and topic events -- oldest
; first with contiguous sequences; the catalog's rows are the articles, so
; the catalog INDEX is the article index and the store sequence is a column
; of the row (a finding of step 4 against the design's "sequence = position",
; which holds only of a history of articles).  The other kinds stay in the
; history and in fn-sn-finish over the event (PKT-585).
;
;   fn-cat-history-relation (records fn-arena fn-cat)
;     = (fn-cat-p fn-cat) and (fn-arena-p fn-arena) and every handle in the
;       arena and (fn-cat-wire-list 0 fn-arena fn-cat) = (fn-sf-article-records records)
;   fn-cat-owner-relation (o fn-arena fn-cat)
;     = the above against (fn-sf-records (fn-sn-files (fn-own-store o))), and
;       the owner's own relation fn-own-relation (books/owner-invariants.lisp)
;
; THE ENTRIES.  (1) init: the creators (create-fn-cat, create-fn-arena)
; against the empty history: fn-cat-relation-at-init.  (2) open from the
; journal, (3) open from a checkpoint and (4) recovery after a cut are ONE
; fold, fn-cat-load: each decoded record in order, an article interned
; (fn-cat-intern-list) and committed (fn-cat-commit: the E-row loader
; fn-cat-load-row of the design IS the commit), every other kind skipped.
; KEYSTONE fn-cat-load-establishes-relation: from a state in the relation
; with history H, loading RECORDS puts it in the relation with H ++ RECORDS,
; whatever the keyring and generation the contexts are decided under; so
; the fold from the empty state over the replayed history (entry 2:
; fn-sn-recover's fn-sf-records; entry 4 is the same replay after a cut) or
; over the checkpoint's decoded records then the suffix (entry 3: fn-sco-open's
; value is a record list) establishes it (fn-cat-load-from-empty).
;
; PRESERVED by every row update that keeps the wire positions: a withdrawal
; and a redecision (fn-cat-relation-of-withdraw, -of-redecide), and by the
; completion (fn-cat-complete: the commit of an interned row whose wire is
; the record the history appends, the load's step: fn-cat-relation-of-commit).
; The reads preserve it trivially.  The arena's seals keep every sealed
; handle (fn-arena-seals-keep-sealed), which is what lets the fold extend.

(in-package "ACL2")
(include-book "catalog-delta")   ; and catalog-commit through it; the redecide lemmas
                                  ; fn-cat-redecide-count, -keeps-handles, fn-cat-handles-inp-of-redecide
(include-book "owner-invariants")

; -----------------------------------------------------------------------------
; The article sub-history, and the catalog materialized.

(defun fn-sf-article-records (records)
  (declare (xargs :guard t))
  (if (consp records)
      (if (fn-record-p (car records))
          (cons (car records) (fn-sf-article-records (cdr records)))
        (fn-sf-article-records (cdr records)))
    nil))

(defthm fn-sf-article-records-of-append
  (equal (fn-sf-article-records (append a b))
         (append (fn-sf-article-records a) (fn-sf-article-records b))))



; The rows [i, count) materialized, in order.
(defun fn-cat-wire-list (i fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp i) (<= i (fn-cat-count fn-cat))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :measure (nfix (- (fn-cat-count fn-cat) (nfix i)))
                  :verify-guards nil))
  (if (or (not (natp i)) (>= i (fn-cat-count fn-cat)))
      nil
    (cons (fn-held-wire-of (fn-cat-at i fn-cat) fn-arena)
          (fn-cat-wire-list (+ i 1) fn-arena fn-cat))))

(verify-guards fn-cat-wire-list
  :hints (("Goal" :in-theory (e/d (fn-held-wire-of)
                                  (fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth))
           :use ((:instance fn-cat-handles-inp-at (n (fn-cat-count fn-cat)) (seq i))))))

(defun fn-cat-history-relation (records fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)))
  (and (fn-cat-p fn-cat)
       (fn-arena-p fn-arena)
       (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (equal (fn-cat-wire-list 0 fn-arena fn-cat) (fn-sf-article-records records))))


; -----------------------------------------------------------------------------
; Entry 1: the creators against the empty history.

(defthm fn-cat-relation-at-init
  (fn-cat-history-relation nil (create-fn-arena) (create-fn-cat))
  :hints (("Goal" :in-theory (enable create-fn-cat create-fn-arena fn-cat-p fn-arena-p))))

; -----------------------------------------------------------------------------
; The load: entries 2, 3 and 4 are this fold over the records they decode.

(defun fn-cat-load-row (w keyring generation fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-record-p w) (fn-prin-keyringp keyring) (natp generation))))
  (mv-let (held fn-arena)
    (fn-cat-intern-list w keyring generation fn-arena)
    (let ((fn-cat (fn-cat-commit held fn-cat)))
      (mv fn-arena fn-cat))))

(defun fn-cat-load (records keyring generation fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (if (consp records)
      (if (fn-record-p (car records))
          (mv-let (fn-arena fn-cat)
            (fn-cat-load-row (car records) keyring generation fn-arena fn-cat)
            (fn-cat-load (cdr records) keyring generation fn-arena fn-cat))
        (fn-cat-load (cdr records) keyring generation fn-arena fn-cat))
    (mv fn-arena fn-cat)))

; -----------------------------------------------------------------------------
; The step: one article loaded onto a state in the relation.

; The wire record of a row does not depend on its numbers, its withdrawal or
; its context.
(local (defthm fn-held-wire-of-with-numbers
   (equal (fn-held-wire (fn-held-with-numbers h numbers) payload) (fn-held-wire h payload))
   :hints (("Goal" :in-theory (enable fn-held-wire fn-held-with-numbers fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-held-wire-of-with-withdrawn
   (equal (fn-held-wire (fn-held-with-withdrawn h w) payload) (fn-held-wire h payload))
   :hints (("Goal" :in-theory (enable fn-held-wire fn-held-with-withdrawn fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-held-wire-of-with-context
   (equal (fn-held-wire (fn-held-with-context h ctx) payload) (fn-held-wire h payload))
   :hints (("Goal" :in-theory (enable fn-held-wire fn-held-with-context fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-record-payload-of-with-numbers
   (equal (fn-record-payload (fn-held-with-numbers h numbers)) (fn-record-payload h))
   :hints (("Goal" :in-theory (enable fn-held-with-numbers fn-record-internals fn-held-internals)))))

(local (defthm fn-cat-assign-wire
   (equal (fn-held-wire (fn-cat-assign h c) payload) (fn-held-wire h payload))
   :hints (("Goal" :in-theory (enable fn-cat-assign)))))

(local (defthm fn-cat-assign-payload
   (equal (fn-record-payload (fn-cat-assign h c)) (fn-record-payload h))
   :hints (("Goal" :in-theory (enable fn-cat-assign)))))

; A seal keeps every sealed handle's payload (the arena's keystone, in the
; one-seal form).
(local (defthm fn-crl-payload-of-seal
   (implies (and (natp h) (< h (fn-arena-count fn-arena)))
            (equal (fn-arena-payload h (fn-arena-seal-list xs fn-arena))
                   (fn-arena-payload h fn-arena)))
   :hints (("Goal" :use ((:instance fn-arena-seals-keep-sealed (payloads (list xs))))
            :in-theory (e/d (fn-arn-seal-many)
                            (fn-arena-payload-is-nth fn-arena-count-is-len
                             fn-arena-seal-list-is-append fn-arn-seal-many-is-append))))))

; The rows below the old count materialize the same after a seal (their
; handles are below the old arena count).
(local (defthm fn-cat-wire-list-of-seal
   (implies (and (fn-cat-p fn-cat) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                 (natp i))
            (equal (fn-cat-wire-list i (fn-arena-seal-list xs fn-arena) fn-cat)
                   (fn-cat-wire-list i fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-cat-wire-list i fn-arena fn-cat)
            :in-theory (e/d (fn-held-wire-of)
                            (fn-arena-payload-is-nth fn-arena-count-is-len
                             fn-arena-seal-list-is-append fn-cat-at-is-nth
                             fn-cat-count-is-len fn-cat-p-is-rowsp))))))

; The rows below the old count materialize the same after a commit.
(local (defthm fn-cat-wire-list-of-commit-below
   (implies (and (natp i) (<= i (fn-cat-count fn-cat)))
            (equal (fn-cat-wire-list i fn-arena (fn-cat-commit h fn-cat))
                   (append (fn-cat-wire-list i fn-arena fn-cat)
                           (list (fn-held-wire-of (fn-cat-assign h fn-cat) fn-arena)))))
   :hints (("Goal" :induct (fn-cat-wire-list i fn-arena fn-cat)
            :expand ((fn-cat-wire-list i fn-arena (fn-cat-commit h fn-cat))
                     (fn-cat-wire-list (+ 1 i) fn-arena (fn-cat-commit h fn-cat)))
            :in-theory (e/d (fn-cat-commit-keeps-rows fn-cat-commit-new-row fn-cat-commit-count)
                            (fn-cat-at-is-nth fn-cat-count-is-len fn-cat-commit-is-append
                             fn-cat-p-is-rowsp))))))

(local (defthm fn-cat-handles-inp-of-seal
   (implies (fn-cat-handles-inp n fn-arena fn-cat)
            (fn-cat-handles-inp n (fn-arena-seal-list xs fn-arena) fn-cat))
   :hints (("Goal" :in-theory (disable fn-arena-count-is-len fn-arena-seal-list-is-append
                                       fn-cat-at-is-nth fn-cat-count-is-len)))))

(local (defthm fn-cat-handles-inp-of-commit
   (implies (and (fn-cat-handles-inp n fn-arena fn-cat) (natp n) (<= n (fn-cat-count fn-cat)))
            (fn-cat-handles-inp n fn-arena (fn-cat-commit h fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-commit-keeps-rows)
                                   (fn-cat-at-is-nth fn-cat-count-is-len fn-cat-commit-is-append
                                    fn-cat-p-is-rowsp))))))

(local (defthm fn-cat-handles-inp-extend
   (implies (and (fn-cat-handles-inp n fn-arena fn-cat) (natp n) (equal n (fn-cat-count fn-cat))
                 (< (fn-record-payload (fn-cat-assign h fn-cat)) (fn-arena-count fn-arena)))
            (fn-cat-handles-inp (+ 1 n) fn-arena (fn-cat-commit h fn-cat)))
   :hints (("Goal" :expand ((fn-cat-handles-inp (+ 1 n) fn-arena (fn-cat-commit h fn-cat)))
            :in-theory (e/d (fn-cat-commit-keeps-rows fn-cat-commit-new-row fn-cat-commit-count)
                            (fn-cat-at-is-nth fn-cat-count-is-len fn-cat-commit-is-append
                             fn-cat-p-is-rowsp))))))

; The recognizers are kept by the two stobjs' own exports (their
; {preserved} obligations), and a wire record's payload is an octet list.
(local (defthm fn-crl-cat-p-of-commit
   (implies (and (fn-cat-p fn-cat) (fn-held-p h))
            (fn-cat-p (fn-cat-commit h fn-cat)))
   :hints (("Goal" :use ((:instance fn-cat-commit{preserved}))
            :in-theory (e/d (fn-cat-p fn-cat-commit)
                            (fn-cat-p-is-rowsp fn-cat-commit-is-append))))))

(local (defthm fn-crl-arena-p-of-seal
   (implies (and (fn-arena-p fn-arena) (fn-cbor-octet-listp xs))
            (fn-arena-p (fn-arena-seal-list xs fn-arena)))
   :hints (("Goal" :use ((:instance fn-arena-seal-list{preserved}))
            :in-theory (e/d (fn-arena-p fn-arena-seal-list)
                            (fn-arena-p-is-payload-listp fn-arena-seal-list-is-append))))))

(local (defthm fn-crl-record-payload-octets
   (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))

; Alpha reads through the numbers' assignment.
(local (defthm fn-crl-wire-of-assign
   (equal (fn-held-wire-of (fn-cat-assign h c) fn-arena) (fn-held-wire-of h fn-arena))
   :hints (("Goal" :in-theory (enable fn-held-wire-of)))))

(defthm fn-cat-load-row-keeps-relation
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-record-p w) (natp generation))
           (mv-let (fn-arena2 fn-cat2)
             (fn-cat-load-row w keyring generation fn-arena fn-cat)
             (fn-cat-history-relation (append records (list w)) fn-arena2 fn-cat2)))
  :hints (("Goal" :in-theory (e/d (fn-cat-load-row fn-cat-history-relation)
                                  (fn-cat-intern-list fn-held-wire-of
                                   fn-arena-payload-is-nth fn-arena-count-is-len
                                   fn-arena-seal-list-is-append fn-arena-p-is-payload-listp
                                   fn-cat-commit-is-append fn-cat-count-is-len fn-cat-at-is-nth
                                   fn-cat-p-is-rowsp fn-cat-handles-inp))
           :use ((:instance fn-cat-intern-list-materializes)
                 (:instance fn-held-p-of-intern-list)
                 (:instance fn-intern-list-handle)
                 (:instance fn-cat-handles-inp-of-seal
                            (n (fn-cat-count fn-cat)) (xs (fn-record-payload w)))
                 (:instance fn-cat-handles-inp-extend
                            (n (fn-cat-count fn-cat))
                            (fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena))
                            (h (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena)))))
           :do-not-induct t)))

; An event that is not an article, appended to the history, changes what
; the catalog must materialize to not at all.
(local (defthm fn-crl-relation-of-non-article
   (implies (not (fn-record-p r))
            (equal (fn-cat-history-relation (append history (list r)) fn-arena fn-cat)
                   (fn-cat-history-relation history fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-history-relation)
                                   (fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-rowsp
                                    fn-cat-handles-inp fn-cat-wire-list))))))

(local (defthm fn-crl-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; The article sub-history is a true list; an atom appended to a history
; adds no article.
(local (defthm fn-crl-article-records-true-listp
   (true-listp (fn-sf-article-records x))))

(local (defthm fn-crl-append-nil
   (implies (true-listp l) (equal (append l nil) l))))

(local (defthm fn-crl-relation-of-append-atom
   (implies (not (consp x))
            (equal (fn-cat-history-relation (append history x) fn-arena fn-cat)
                   (fn-cat-history-relation history fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-history-relation)
                                   (fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-rowsp
                                    fn-cat-handles-inp fn-cat-wire-list))))))

; The fold's induction, carrying the history it has appended so far.
(local (defun fn-crl-load-ind (records history keyring generation fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil)
            (irrelevant history))
   (if (consp records)
       (if (fn-record-p (car records))
           (mv-let (fn-arena fn-cat)
             (fn-cat-load-row (car records) keyring generation fn-arena fn-cat)
             (fn-crl-load-ind (cdr records) (append history (list (car records)))
                              keyring generation fn-arena fn-cat))
         (fn-crl-load-ind (cdr records) (append history (list (car records)))
                          keyring generation fn-arena fn-cat))
     (mv fn-arena fn-cat))))

; KEYSTONE: the fold.
(defthm fn-cat-load-establishes-relation
  (implies (and (fn-cat-history-relation history fn-arena fn-cat)
                (natp generation))
           (mv-let (fn-arena2 fn-cat2)
             (fn-cat-load records keyring generation fn-arena fn-cat)
             (fn-cat-history-relation (append history records) fn-arena2 fn-cat2)))
  :hints (("Goal" :induct (fn-crl-load-ind records history keyring generation fn-arena fn-cat)
           :expand ((fn-cat-load records keyring generation fn-arena fn-cat))
           :in-theory (e/d (fn-cat-load)
                           (fn-cat-history-relation fn-cat-load-row
                            fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-rowsp)))
          ("Subgoal *1/1" :use ((:instance fn-cat-load-row-keeps-relation
                                          (w (car records)) (records history))))))

(defthm fn-cat-load-from-empty
  (implies (natp generation)
           (mv-let (fn-arena2 fn-cat2)
             (fn-cat-load records keyring generation (create-fn-arena) (create-fn-cat))
             (fn-cat-history-relation records fn-arena2 fn-cat2)))
  :hints (("Goal" :use ((:instance fn-cat-load-establishes-relation
                                   (history nil) (fn-arena (create-fn-arena))
                                   (fn-cat (create-fn-cat))))
           :in-theory (disable fn-cat-history-relation fn-cat-load))))

; -----------------------------------------------------------------------------
; Preserved by the row updates and the completion.

; A withdrawal and a redecision keep every row's wire positions and handle
; (the row updates at the target; every other row is the same object).
(local (defthm fn-crl-payload-of-with-withdrawn
   (equal (fn-record-payload (fn-held-with-withdrawn h w)) (fn-record-payload h))
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-crl-payload-of-with-context
   (equal (fn-record-payload (fn-held-with-context h ctx)) (fn-record-payload h))
   :hints (("Goal" :in-theory (enable fn-held-with-context fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-crl-wire-of-at-withdraw
   (implies (and (natp target) (< target (fn-cat-count fn-cat)) (natp k))
            (equal (fn-held-wire-of (fn-cat-at k (fn-cat-withdraw target by fn-cat)) fn-arena)
                   (fn-held-wire-of (fn-cat-at k fn-cat) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-cat-mark-withdrawn fn-held-wire-of)
                                   (fn-cat-p-is-rowsp))))))

(local (defthm fn-crl-wire-of-at-redecide
   (implies (and (natp seq) (< seq (fn-cat-count fn-cat)) (natp k))
            (equal (fn-held-wire-of (fn-cat-at k (fn-cat-redecide seq ctx fn-cat)) fn-arena)
                   (fn-held-wire-of (fn-cat-at k fn-cat) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-held-wire-of) (fn-cat-p-is-rowsp))))))

(local (defthm fn-crl-count-of-withdraw
   (implies (and (natp target) (< target (fn-cat-count fn-cat)))
            (equal (fn-cat-count (fn-cat-withdraw target by fn-cat)) (fn-cat-count fn-cat)))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

(local (defthm fn-cat-wire-list-of-withdraw
   (implies (and (natp target) (< target (fn-cat-count fn-cat)) (natp i))
            (equal (fn-cat-wire-list i fn-arena (fn-cat-withdraw target by fn-cat))
                   (fn-cat-wire-list i fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-cat-wire-list i fn-arena fn-cat)
            :in-theory (disable fn-cat-withdraw-is-mark fn-cat-count-is-len fn-cat-at-is-nth
                                fn-cat-p-is-rowsp fn-held-wire-of)))))

(local (defthm fn-cat-wire-list-of-redecide
   (implies (and (natp seq) (< seq (fn-cat-count fn-cat)) (natp i))
            (equal (fn-cat-wire-list i fn-arena (fn-cat-redecide seq ctx fn-cat))
                   (fn-cat-wire-list i fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-cat-wire-list i fn-arena fn-cat)
            :in-theory (disable fn-cat-redecide-is-update-nth fn-cat-count-is-len fn-cat-at-is-nth
                                fn-cat-p-is-rowsp fn-held-wire-of)))))

(local (defthm fn-crl-handles-of-withdraw
   (implies (and (natp target) (< target (fn-cat-count fn-cat)))
            (equal (fn-cat-handles-inp n fn-arena (fn-cat-withdraw target by fn-cat))
                   (fn-cat-handles-inp n fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-mark-withdrawn) (fn-cat-p-is-rowsp))))))

(local (defthm fn-crl-cat-p-of-withdraw
   (implies (and (fn-cat-p fn-cat) (natp target) (< target (fn-cat-count fn-cat)) (natp by))
            (fn-cat-p (fn-cat-withdraw target by fn-cat)))
   :hints (("Goal" :use ((:instance fn-cat-withdraw{preserved}))
            :in-theory (e/d (fn-cat-p fn-cat-withdraw fn-cat-count)
                            (fn-cat-p-is-rowsp fn-cat-withdraw-is-mark fn-cat-count-is-len))))))

(local (defthm fn-crl-cat-p-of-redecide
   (implies (and (fn-cat-p fn-cat) (natp seq) (< seq (fn-cat-count fn-cat)) (fn-hc-p ctx))
            (fn-cat-p (fn-cat-redecide seq ctx fn-cat)))
   :hints (("Goal" :use ((:instance fn-cat-redecide{preserved} (context ctx)))
            :in-theory (e/d (fn-cat-p fn-cat-redecide fn-cat-count)
                            (fn-cat-p-is-rowsp fn-cat-redecide-is-update-nth
                             fn-cat-count-is-len))))))

(defthm fn-cat-relation-of-withdraw
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (natp target) (< target (fn-cat-count fn-cat)) (natp by))
           (fn-cat-history-relation records fn-arena (fn-cat-withdraw target by fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-cat-history-relation)
                                  (fn-cat-withdraw-is-mark fn-cat-count-is-len fn-cat-at-is-nth
                                   fn-cat-p-is-rowsp fn-cat-handles-inp fn-cat-wire-list)))))

(defthm fn-cat-relation-of-redecide
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (natp seq) (< seq (fn-cat-count fn-cat)) (fn-hc-p ctx))
           (fn-cat-history-relation records fn-arena (fn-cat-redecide seq ctx fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-cat-history-relation)
                                  (fn-cat-redecide-is-update-nth fn-cat-count-is-len fn-cat-at-is-nth
                                   fn-cat-p-is-rowsp fn-cat-handles-inp fn-cat-wire-list)))))

; The completion: the commit of the pending's held record, whose wire (with
; its sealed bytes) is the record W the history appends.
(defthm fn-cat-relation-of-complete
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count fn-arena))
                (equal (fn-held-wire-of (fn-pc-held pending) fn-arena) w)
                (fn-record-p w))
           (fn-cat-history-relation (append records (list w)) fn-arena
                                    (mv-nth 2 (fn-cat-complete token pending fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-cat-complete fn-cat-history-relation)
                                  (fn-pc-p fn-arena-payload-is-nth fn-arena-count-is-len
                                   fn-held-wire-of fn-cat-commit-is-append fn-cat-count-is-len
                                   fn-cat-at-is-nth fn-cat-p-is-rowsp fn-cat-handles-inp))
           :use ((:instance fn-cat-handles-inp-extend
                            (n (fn-cat-count fn-cat)) (h (fn-pc-held pending))))
           :do-not-induct t)))

; The hidden completion (R1, step 8): the same append; the row's wire ignores
; its withdrawal.
(local (defthm fn-crl-wire-of-with-withdrawn
   (equal (fn-held-wire-of (fn-held-with-withdrawn h w) fn-arena) (fn-held-wire-of h fn-arena))
   :hints (("Goal" :in-theory (enable fn-held-wire-of)))))

(defthm fn-cat-relation-of-complete-hidden
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count fn-arena))
                (equal (fn-held-wire-of (fn-pc-held pending) fn-arena) w)
                (fn-record-p w)
                (natp by))
           (fn-cat-history-relation (append records (list w)) fn-arena
                                    (mv-nth 2 (fn-cat-complete-hidden token pending by fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-cat-complete-hidden fn-cat-history-relation fn-held-withdrawnp)
                                  (fn-pc-p fn-arena-payload-is-nth fn-arena-count-is-len
                                   fn-held-wire-of fn-cat-commit-is-append fn-cat-count-is-len
                                   fn-cat-at-is-nth fn-cat-p-is-rowsp fn-cat-handles-inp
                                   fn-held-with-withdrawn))
           :use ((:instance fn-cat-handles-inp-extend
                            (n (fn-cat-count fn-cat))
                            (h (fn-held-with-withdrawn (fn-pc-held pending)
                                                       (cons (fn-pc-expected pending) by)))))
           :do-not-induct t)))

; The load of a row the owner's view hides (E, step 8: a recovery over a
; history with effective cancels; books/served-catalog-owner.lisp
; fn-sco-load-history): the held record is committed withdrawn at its own
; index, as fn-cat-complete-hidden commits it, so no view shows it.
(defun fn-cat-load-row-hidden (w keyring generation fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-record-p w) (fn-prin-keyringp keyring) (natp generation))
                  :guard-hints (("Goal"
                                 :in-theory (e/d (fn-held-withdrawnp)
                                                 (fn-held-p fn-held-with-withdrawn
                                                  fn-cat-intern-list))
                                 :use ((:instance fn-held-p-of-intern-list)
                                       (:instance fn-held-p-of-fn-held-with-withdrawn
                                                  (h (mv-nth 0 (fn-cat-intern-list
                                                                w keyring generation fn-arena)))
                                                  (w (cons (fn-cat-count fn-cat) 0))))))))
  (mv-let (held fn-arena)
    (fn-cat-intern-list w keyring generation fn-arena)
    (let ((fn-cat (fn-cat-commit (fn-held-with-withdrawn held (cons (fn-cat-count fn-cat) 0))
                                 fn-cat)))
      (mv fn-arena fn-cat))))

(defthm fn-cat-load-row-hidden-keeps-relation
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-record-p w) (natp generation))
           (mv-let (fn-arena2 fn-cat2)
             (fn-cat-load-row-hidden w keyring generation fn-arena fn-cat)
             (fn-cat-history-relation (append records (list w)) fn-arena2 fn-cat2)))
  :hints (("Goal" :in-theory (e/d (fn-cat-load-row-hidden fn-cat-history-relation
                                   fn-held-withdrawnp)
                                  (fn-cat-intern-list fn-held-wire-of
                                   fn-arena-payload-is-nth fn-arena-count-is-len
                                   fn-arena-seal-list-is-append fn-arena-p-is-payload-listp
                                   fn-cat-commit-is-append fn-cat-count-is-len fn-cat-at-is-nth
                                   fn-cat-p-is-rowsp fn-cat-handles-inp
                                   fn-held-with-withdrawn))
           :use ((:instance fn-cat-intern-list-materializes)
                 (:instance fn-held-p-of-intern-list)
                 (:instance fn-intern-list-handle)
                 (:instance fn-cat-handles-inp-of-seal
                            (n (fn-cat-count fn-cat)) (xs (fn-record-payload w)))
                 (:instance fn-cat-handles-inp-extend
                            (n (fn-cat-count fn-cat))
                            (fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena))
                            (h (fn-held-with-withdrawn
                                (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena))
                                (cons (fn-cat-count fn-cat) 0)))))
           :do-not-induct t)))

; -----------------------------------------------------------------------------
; R against the owner: the history relation over the owner's store, with the
; owner's own relation (books/owner-invariants.lisp).  Its establishment at
; the host's entries (fn-owner-recover, fn-owner-recover-from-checkpoint) is
; step 8 (PKT-585); the catalog side above is what those entries call.

(defun-nx fn-cat-owner-relation (o fn-arena fn-cat)
  (and (fn-cat-history-relation (fn-sf-records (fn-sn-files (fn-own-store o))) fn-arena fn-cat)
       (fn-own-relation o)))
