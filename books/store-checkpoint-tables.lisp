; fn: the state checkpoint's storage schema 3: four TABLES, each a run of
; FNSC segments, instead of one postfix program over the whole checkpoint
; value (lane checkpoint-pipeline, 2026-09-26; D33, D34; design
; planning/design-2026-09-26-consolidation.md section 2.1).
;
; The schema-2 file (fn-sco-freeze of the 7-tuple, encoded as one tree)
; carried every payload twice: once in the event index and once in the
; configuration fold's node, whose stored article is (MSGID PAYLOAD GROUPS
; MEMBERSHIPS PIN STAMP) with PAYLOAD the record's own octet list
; (fn-replay-apply-record hands fn-record-payload to fn-node-prepare): 670 MB
; for 320 MB of payload (PKT-307, PKT-314).  Schema 3 writes four tables:
;
;   F  one row (3 S FRONTIER REVISION): the schema, the count covered, the
;      store's frontier txid at the capture, the writer's source revision,
;      the record log's position at S (fn-sct-log-positionp);
;   P  one row per committed event s: `fn-sct-payload-of' the event (an
;      article's payload, a composite's article-record bytes, else NIL);
;   E  one row per committed event: the event itself, every octets leaf
;      equal to P[s] written as a REFERENCE to s (the record minus its
;      payload; its other fields are the record's own until the catalog
;      slice, planning/briefs-wave5);
;   R  four rows, the fold roots: the configuration fold paused at S, the
;      identity context, the consumer cursor, the topic prefix state, with
;      every stored article's payload written as a reference to its P row,
;      found through the event index's Message-ID trie.
;
; The event index is not stored: the load rebuilds it from E
; (fn-cei-build-aux, as fn-sco-capture does).  A row is a value of the
; postfix tree codec (fn-scc-program, books/store-checkpoint-codec.lisp)
; extended by ONE op, ref: `8 NAT(s)' pushes P[s]'s bytes
; (`fn-sct-ref-get').  A run's program is its rows' programs concatenated;
; the stack after the run IS the rows, reversed (fn-sct-run-of-rows-program);
; no per-row framing.  Each run is fn-scc-chunks of its program in segments
; of at most SEG octets, framed and chained from the genesis by the codec's
; unchanged fn-scc-frames (header 37 octets with schema 3 and sequence S,
; chunk, trailer), so fn-scc-decode-segments's refusals of reorder,
; truncation, splice and corruption, and the reader's per-segment
; admission (fn-sccr-admit-segment, PRF-135), are reused.  The runs are in
; the order F, P, E, R, so the open refuses a wrong schema or count before
; it reads a payload.
;
; What the tables MEAN is fn-sco-capture: `fn-sct-tables-of-capture' builds
; them from a capture, `fn-sct-capture-of-tables' rebuilds the capture, and
; `fn-sct-capture-of-tables-of-capture' says they are inverses.  The
; dedupe is by EQUALITY with P[s] (the logic has no object identity; on the
; host `equal' short-circuits on the shared pointer): a leaf is written as a
; reference exactly when it equals the P row the reference restores
; (`fn-sct-refp'), so the load restores equal lists.  A composite's carried
; record (fn-replay-composite-record, decoded from the composite's bytes) is
; a distinct object with distinct bytes: its payload in R stays literal.
; The file-local index s becomes the fresh P table's index at the load
; (`fn-cei-build' of the rows read, in order): the translation is the
; identity on a fresh table, and is never assumed for a live one.
;
; KEYSTONE (list level) `fn-sct-decode-file-of-file-is-the-capture': the
; reader's decode of the segments written for the tables of a capture is
; those tables, and their value is the capture.  The buffer-level twin and
; the batched writer are books/store-checkpoint-tables-reader.lisp and
; books/owner-checkpoint-pipeline.lisp.

(in-package "ACL2")
(include-book "store-checkpoint-open")
(include-book "store-checkpoint-codec")
(local (include-book "arithmetic/top" :dir :system))

(defconst *fn-sct-schema* 3)
(assert-event (equal *fn-sct-schema* *fn-scc-schema*))
; The one op added to the tree codec's 0..7.
(defconst *fn-sct-op-ref* 8)

(local
 (defthm fn-sct-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-sct-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-sct-true-list-fix-of-true-list
   (implies (true-listp x) (equal (true-list-fix x) x))))

; -----------------------------------------------------------------------------
; The payload projection: what a P row holds of an event, and what a
; reference restores.  Total, cheap (no recognizer runs): an article
; record has its Message-ID string at 3 and its payload at 4
; (fn-record-make, books/records-shape); a composite has its article-record
; bytes at 6 (fn-stxa-make-full, books/stx-accept-records); a P row is
; itself; anything else has no payload.

(defun fn-sct-octets-or-nil (v)
  (declare (xargs :guard t))
  (if (fn-scc-octets-valuep v) v nil))

(defun fn-sct-payload-of (v)
  (declare (xargs :guard t))
  (cond ((not (consp v)) nil)
        ((stringp (fn-sco-at 3 v)) (fn-sct-octets-or-nil (fn-sco-at 4 v)))
        ((consp (fn-sco-at 6 v)) (fn-sct-octets-or-nil (fn-sco-at 6 v)))
        (t (fn-sct-octets-or-nil v))))

(defthm fn-sct-payload-of-shape
  (or (null (fn-sct-payload-of v))
      (fn-scc-octets-valuep (fn-sct-payload-of v)))
  :rule-classes nil)

(local
 (defthm fn-sct-nth-of-octet-listp
   (implies (fn-scc-octet-listp x)
            (and (not (stringp (nth n x)))
                 (not (consp (nth n x)))))
   :hints (("Goal" :induct (nth n x)))))

(defthm fn-sct-payload-of-idempotent
  (equal (fn-sct-payload-of (fn-sct-payload-of v))
         (fn-sct-payload-of v))
  :hints (("Goal" :in-theory (enable fn-sco-at))))

(in-theory (disable fn-sct-payload-of))

; The reference target: P[s], read through an event index (fn-cei-get, the
; u32-keyed sequence trie).  At the encode the index is the capture's
; (records by sequence: the payload of record s); at the decode it is the
; index built from the P rows read (P[s] itself, idempotently).
(defun fn-sct-ref-get (s table)
  (declare (xargs :guard t))
  (fn-sct-payload-of (fn-cei-get s table)))

; Two tables agree on every sequence below N.
(defun fn-sct-agreep (te td n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (equal (fn-sct-ref-get (1- n) te) (fn-sct-ref-get (1- n) td))
         (fn-sct-agreep te td (1- n)))))

(defthm fn-sct-agreep-get
  (implies (and (natp n) (fn-sct-agreep te td n) (natp s) (< s n))
           (equal (fn-sct-ref-get s td) (fn-sct-ref-get s te)))
  :hints (("Goal" :induct (fn-sct-agreep te td n)
           :in-theory (disable fn-sct-ref-get))))

(defthm fn-sct-agreep-reflexive
  (fn-sct-agreep te te n))

(in-theory (disable fn-sct-ref-get fn-sct-agreep))

; -----------------------------------------------------------------------------
; The decoder: the tree codec's stack machine with the ref op.

; (STACK . REST), NIL (malformed) or :dangling (a reference to a P row that
; is absent or empty: refused by name).
(defun fn-sct-step (xs stack table)
  (declare (xargs :guard (and (consp xs) (fn-scc-octet-listp xs))))
  (if (equal (car xs) *fn-sct-op-ref*)
      (let ((n (fn-scc-read-nat (cdr xs))))
        (if (not n)
            nil
          (let ((v (fn-sct-ref-get (car n) table)))
            (if (not v) :dangling (cons (cons v stack) (cdr n))))))
    (fn-scc-step xs stack)))

(defthm fn-sct-step-facts
  (implies (and (consp xs) (fn-scc-octet-listp xs)
                (consp (fn-sct-step xs stack table)))
           (and (fn-scc-octet-listp (cdr (fn-sct-step xs stack table)))
                (< (len (cdr (fn-sct-step xs stack table))) (len xs))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-read-nat-facts (xs (cdr xs)))
                 fn-scc-step-facts fn-scc-step-shrinks)
           :in-theory (disable fn-scc-read-nat fn-scc-step fn-scc-read-nat-facts
                               fn-scc-step-facts fn-scc-step-shrinks))))

(defun fn-sct-run (xs stack table)
  (declare (xargs :guard (fn-scc-octet-listp xs) :measure (len xs)
                  :verify-guards nil))
  (if (not (consp xs))
      stack
    (let ((next (fn-sct-step xs stack table)))
      (cond ((eq next :dangling) :dangling)
            ((and (consp next) (mbt (< (len (cdr next)) (len xs))))
             (fn-sct-run (cdr next) (car next) table))
            (t :refused)))))

(verify-guards fn-sct-run
  :hints (("Goal" :use fn-sct-step-facts :in-theory (disable fn-sct-step-facts fn-sct-step))))

; -----------------------------------------------------------------------------
; The encoder: the tree codec's program with references.

; X is written as a reference to S: S below N, encodable, and X the (nonempty)
; bytes the reference restores.
(defun fn-sct-refp (x s n table)
  (declare (xargs :guard t))
  (and (natp n) (natp s) (< s n) (fn-scc-nat-encodablep s) (consp x)
       (equal x (fn-sct-ref-get s table))))

; The candidate for a stored article (MSGID PAYLOAD ...): the sequence of a
; record the Message-ID trie lists whose P row is this payload.
(defun fn-sct-candidate-among (payload records n table)
  (declare (xargs :guard t))
  (if (consp records)
      (let ((s (fn-record-sequence (car records))))
        (if (fn-sct-refp payload s n table)
            s
          (fn-sct-candidate-among payload (cdr records) n table)))
    nil))

(defun fn-sct-candidate (x mtrie n table)
  (declare (xargs :guard t))
  (if (and (consp x) (stringp (car x)) (consp (cdr x)) (consp (cadr x)))
      (fn-sct-candidate-among (cadr x) (fn-cei-trie-records (car x) mtrie) n table)
    nil))

(defthm fn-sct-candidate-among-natp
  (or (null (fn-sct-candidate-among payload records n table))
      (natp (fn-sct-candidate-among payload records n table)))
  :rule-classes :type-prescription)

(defthm fn-sct-candidate-natp
  (or (null (fn-sct-candidate x mtrie n table))
      (natp (fn-sct-candidate x mtrie n table)))
  :rule-classes :type-prescription)

; The program of X.  CAND: nil, or the sequence a leaf below may reference
; (an E row's own sequence; in R, the candidate found at the enclosing
; stored article).  MTRIE: the Message-ID trie candidates are found in (nil
; for F, P and E).
(defun fn-sct-program (x cand mtrie n table)
  (declare (xargs :guard (fn-scc-treep x) :verify-guards nil
                  :measure (acl2-count x)))
  (cond ((and cand (fn-sct-refp x cand n table))
         (cons *fn-sct-op-ref* (fn-scc-nat-octets cand)))
        ((fn-scc-octets-valuep x) (fn-scc-program x))
        ((consp x)
         (let ((c (let ((k (fn-sct-candidate x mtrie n table))) (if k k cand))))
           (append (fn-sct-program (car x) c mtrie n table)
                   (fn-sct-program (cdr x) c mtrie n table)
                   (list *fn-scc-op-cons*))))
        (t (fn-scc-atom-octets x))))

(local
 (defthm fn-sct-le-digits-true-listp
   (true-listp (fn-scc-le-digits n))))

(local
 (defthm fn-sct-atom-octets-true-listp
   (true-listp (fn-scc-atom-octets x))
   :hints (("Goal" :in-theory (enable fn-scc-atom-octets fn-scc-nat-octets
                                      fn-scc-string-octets)))))

(defthm fn-sct-program-true-listp
  (true-listp (fn-sct-program x cand mtrie n table))
  :hints (("Goal" :induct (fn-sct-program x cand mtrie n table)
           :in-theory (e/d (fn-sct-program)
                           (fn-scc-program fn-scc-atom-octets fn-scc-nat-octets
                            fn-sct-refp fn-sct-candidate fn-scc-octets-valuep
                            fn-scc-treep)))))

(verify-guards fn-sct-program
  :hints (("Goal" :expand ((fn-scc-treep x))
           :in-theory (e/d (fn-sct-refp)
                           (fn-scc-program fn-scc-atom-octets fn-scc-nat-octets
                            fn-sct-candidate fn-scc-treep fn-scc-octets-valuep
                            fn-sct-program)))))

; -----------------------------------------------------------------------------
; Running the program of X pushes X: the codec's fn-scc-run-of-program with
; the ref case.  The decoder's table TD may differ from the encoder's TE as
; long as they agree below N (the load's table is built from the P rows,
; the encoder's is the capture's index: fn-sct-agreep-of-build below).

(local
 (defthm fn-sct-step-of-atom
   (implies (fn-scc-atomp x)
            (equal (fn-sct-step (append (fn-scc-atom-octets x) rest) stack table)
                   (cons (cons x stack) rest)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d ()
                            (fn-scc-read-nat fn-scc-read-string fn-scc-string-octets
                             fn-scc-nat-octets))))))

(local
 (defthm fn-sct-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-sct-step-of-octets
   (implies (fn-scc-octets-valuep x)
            (equal (fn-sct-step (cons *fn-scc-op-octets*
                                      (append (fn-scc-nat-octets (len x))
                                              (append x rest)))
                                stack table)
                   (cons (cons x stack) rest)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-read-nat-of-octets (n (len x))
                             (rest (append x rest))))
            :in-theory (e/d () (fn-scc-read-nat fn-scc-nat-octets
                                fn-scc-read-nat-of-octets))))))

(local
 (defthm fn-sct-step-of-ref
   (implies (and (natp s) (fn-sct-ref-get s table))
            (equal (fn-sct-step (cons *fn-sct-op-ref* (append (fn-scc-nat-octets s) rest))
                                stack table)
                   (cons (cons (fn-sct-ref-get s table) stack) rest)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-read-nat-of-octets (n s)))
            :in-theory (e/d () (fn-scc-read-nat fn-scc-nat-octets
                                fn-scc-read-nat-of-octets))))))

(local
 (defthm fn-sct-step-of-cons-op
   (equal (fn-sct-step (cons *fn-scc-op-cons* rest) (cons b (cons a stack)) table)
          (cons (cons (cons a b) stack) rest))))

(local
 (defthm fn-sct-atom-octets-consp
   (and (consp (fn-scc-atom-octets x))
        (consp (append (fn-scc-atom-octets x) rest)))))

(local
 (defthm fn-sct-atom-octets-len
   (< 0 (len (fn-scc-atom-octets x)))
   :rule-classes :linear))

; One step of the run, as a rewrite: a step that answers (STACK . REST)
; shorter than the input continues the run from it.
(local
 (defthm fn-sct-run-step
   (implies (and (consp xs) (consp (fn-sct-step xs stack table))
                 (< (len (cdr (fn-sct-step xs stack table))) (len xs)))
            (equal (fn-sct-run xs stack table)
                   (fn-sct-run (cdr (fn-sct-step xs stack table))
                               (car (fn-sct-step xs stack table)) table)))
   :hints (("Goal" :expand ((fn-sct-run xs stack table))))))

(local
 (defun fn-sct-ind (x cand mtrie n te rest stack)
   (declare (xargs :verify-guards nil))
   (cond ((and cand (fn-sct-refp x cand n te)) (list rest stack))
         ((fn-scc-octets-valuep x) (list rest stack))
         ((consp x)
          (let ((c (let ((k (fn-sct-candidate x mtrie n te))) (if k k cand))))
            (list (fn-sct-ind (car x) c mtrie n te
                              (append (fn-sct-program (cdr x) c mtrie n te)
                                      (cons *fn-scc-op-cons* rest))
                              stack)
                  (fn-sct-ind (cdr x) c mtrie n te (cons *fn-scc-op-cons* rest)
                              (cons (car x) stack)))))
         (t (list rest stack)))))

(local
 (defthm fn-sct-refp-target
   (implies (and (fn-sct-refp x s n te) (fn-sct-agreep te td n))
            (and (natp s) (fn-sct-ref-get s td)
                 (equal (fn-sct-ref-get s td) x)))
   :hints (("Goal" :use ((:instance fn-sct-agreep-get))
            :in-theory (disable fn-sct-agreep-get)))))

(defthm fn-sct-run-of-program
  (implies (and (fn-scc-treep x) (fn-sct-agreep te td n))
           (equal (fn-sct-run (append (fn-sct-program x cand mtrie n te) rest) stack td)
                  (fn-sct-run rest (cons x stack) td)))
  :hints (("Goal" :induct (fn-sct-ind x cand mtrie n te rest stack)
           :in-theory (e/d (fn-sct-program)
                           (fn-sct-step fn-scc-atom-octets fn-scc-nat-octets
                            fn-scc-atomp fn-scc-octets-valuep fn-sct-refp
                            fn-sct-candidate fn-scc-program fn-scc-treep)))
          ("Subgoal *1/4" :in-theory (e/d (fn-sct-program fn-scc-treep)
                                          (fn-sct-step fn-scc-atom-octets fn-scc-nat-octets
                                           fn-scc-atomp fn-scc-octets-valuep fn-sct-refp
                                           fn-sct-candidate fn-scc-program)))
          ("Subgoal *1/3" :in-theory (e/d (fn-sct-program fn-scc-treep)
                                          (fn-sct-step fn-scc-atom-octets fn-scc-nat-octets
                                           fn-scc-atomp fn-scc-octets-valuep fn-sct-refp
                                           fn-sct-candidate fn-scc-program)))
          ("Subgoal *1/2" :in-theory (e/d (fn-sct-program fn-scc-program fn-scc-treep)
                                          (fn-sct-step fn-scc-atom-octets fn-scc-nat-octets
                                           fn-scc-atomp fn-scc-octets-valuep fn-sct-refp
                                           fn-sct-candidate)))
          ("Subgoal *1/1" :use ((:instance fn-sct-refp-target (s cand)))
           :in-theory (e/d (fn-sct-program)
                           (fn-sct-step fn-scc-atom-octets fn-scc-nat-octets
                            fn-scc-atomp fn-scc-octets-valuep fn-sct-refp
                            fn-sct-candidate fn-scc-program fn-scc-treep
                            fn-sct-refp-target)))))

(in-theory (disable fn-sct-step fn-sct-run fn-sct-program fn-sct-refp fn-sct-candidate))

; -----------------------------------------------------------------------------
; A table's run: its rows' programs, concatenated.  SELFP: row i is
; encoded with candidate i (the E table); else with none (F, P, R; R finds
; its candidates through MTRIE).

(defun fn-sct-rows-treep (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-scc-treep (car rows)) (fn-sct-rows-treep (cdr rows)))
    (null rows)))

(defthm fn-sct-rows-treep-true-listp
  (implies (fn-sct-rows-treep rows) (true-listp rows))
  :rule-classes :forward-chaining)

(defun fn-sct-rows-program (rows i selfp mtrie n table)
  (declare (xargs :guard (and (natp i) (fn-sct-rows-treep rows))))
  (if (consp rows)
      (append (fn-sct-program (car rows) (if selfp i nil) mtrie n table)
              (fn-sct-rows-program (cdr rows) (+ 1 i) selfp mtrie n table))
    nil))

(defthm fn-sct-rows-program-true-listp
  (true-listp (fn-sct-rows-program rows i selfp mtrie n table)))

(local
 (defun fn-sct-rows-ind (rows i stack)
   (if (consp rows)
       (fn-sct-rows-ind (cdr rows) (+ 1 i) (cons (car rows) stack))
     (list i stack))))

(defthm fn-sct-run-of-rows-program
  (implies (and (fn-sct-rows-treep rows) (fn-sct-agreep te td n))
           (equal (fn-sct-run (append (fn-sct-rows-program rows i selfp mtrie n te) rest)
                              stack td)
                  (fn-sct-run rest (revappend rows stack) td)))
  :hints (("Goal" :induct (fn-sct-rows-ind rows i stack)
           :in-theory (disable fn-sct-run fn-sct-program))))

; The rows of a run's program: the stack, reversed; a dangling reference
; and a malformed program are refused by name.
(defun fn-sct-decode-rows (xs table)
  (declare (xargs :guard (fn-scc-octet-listp xs)))
  (let ((st (fn-sct-run xs nil table)))
    (cond ((true-listp st) (list :ok (reverse st)))
          ((eq st :dangling) (list :refused :ref))
          (t (list :refused :tree)))))

(local
 (defthm fn-sct-run-of-nil
   (equal (fn-sct-run nil stack table) stack)
   :hints (("Goal" :in-theory (enable fn-sct-run)))))

(local
 (defthm fn-sct-reverse-revappend
   (implies (true-listp rows)
            (equal (reverse (revappend rows nil)) rows))
   :hints (("Goal" :in-theory (enable reverse)))))

(local
 (defthm fn-sct-true-listp-revappend
   (implies (true-listp b) (true-listp (revappend a b)))))

(defthm fn-sct-decode-rows-of-rows-program
  (implies (and (fn-sct-rows-treep rows) (fn-sct-agreep te td n))
           (equal (fn-sct-decode-rows (fn-sct-rows-program rows i selfp mtrie n te) td)
                  (list :ok rows)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sct-run-of-rows-program (rest nil) (stack nil)))
           :in-theory (e/d () (fn-sct-run fn-sct-rows-program fn-sct-run-of-rows-program)))))

(in-theory (disable fn-sct-decode-rows fn-sct-rows-program))

; -----------------------------------------------------------------------------
; The tables of a capture, and the capture of the tables.

(defun fn-sct-payloads (records)
  (declare (xargs :guard t))
  (if (consp records)
      (cons (fn-sct-payload-of (car records)) (fn-sct-payloads (cdr records)))
    nil))

(defthm fn-sct-len-payloads
  (equal (len (fn-sct-payloads records)) (len records)))

(defthm fn-sct-nth-payloads
  (implies (and (natp s) (< s (len records)))
           (equal (nth s (fn-sct-payloads records))
                  (fn-sct-payload-of (nth s records)))))

; LOG (a format-9 store, lane log-recovery): where the history's suffix at S
; starts in the record log, (K GENESIS): the first segment this checkpoint
; does not cover and the trailer its first entry chains from
; (books/store-log-segments.lisp: the capture ROTATED the active segment at
; S, so every record below S is in the segments below K).  NIL: no log
; position (the open scans the log from segment 1).
(defun fn-sct-log-positionp (log)
  (declare (xargs :guard t))
  (or (null log)
      (and (true-listp log) (equal (len log) 2)
           (posp (car log))
           (fn-cbor-octet-listp (cadr log))
           (equal (len (cadr log)) 32))))

(defun fn-sct-f-row (s frontier revision log)
  (declare (xargs :guard t))
  (list *fn-sct-schema* s frontier revision log))

(defun fn-sct-f-rowp (row)
  (declare (xargs :guard t))
  (and (true-listp row) (equal (len row) 5)
       (equal (car row) *fn-sct-schema*)
       (natp (cadr row))
       (fn-sct-log-positionp (nth 4 row))))

(defun fn-sct-tables-of-capture (c frontier revision log)
  (declare (xargs :guard t))
  (let ((e (fn-sco-records c)))
    (list (fn-sct-f-row (len e) frontier revision log)
          (fn-sct-payloads e)
          e
          (list (fn-sco-cpr c) (fn-sco-identity c) (fn-sco-consumer c)
                (fn-sco-topic c)))))

(defun fn-sct-tables-f (tables) (declare (xargs :guard t)) (fn-sco-at 0 tables))
; The F row's log position (fn-sct-log-positionp).
(defun fn-sct-tables-log (tables) (declare (xargs :guard t)) (fn-sco-at 4 (fn-sct-tables-f tables)))
(defun fn-sct-tables-p (tables) (declare (xargs :guard t)) (fn-sco-at 1 tables))
(defun fn-sct-tables-e (tables) (declare (xargs :guard t)) (fn-sco-at 2 tables))
(defun fn-sct-tables-r (tables) (declare (xargs :guard t)) (fn-sco-at 3 tables))

; The value the tables mean: the capture's 7-tuple, its event index rebuilt
; from E as fn-sco-capture builds it.
(defun fn-sct-capture-of-tables (tables)
  (declare (xargs :guard t))
  (let ((e (true-list-fix (fn-sct-tables-e tables)))
        (r (fn-sct-tables-r tables)))
    (fn-sco-make e (fn-sco-at 0 r) (fn-sco-at 1 r) (fn-sco-at 2 r) (fn-sco-at 3 r)
                 (fn-cei-build-aux e 0 nil))))

(local
 (defthm fn-sct-true-list-fix-idempotent
   (equal (true-list-fix (true-list-fix x)) (true-list-fix x))))

(local
 (defthm fn-sct-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

; The tables of a capture mean the capture: the inverse, for every
; configuration history and record list.
(defthm fn-sct-capture-of-tables-of-capture
  (equal (fn-sct-capture-of-tables
          (fn-sct-tables-of-capture (fn-sco-capture configs records) frontier revision log))
         (fn-sco-capture configs records))
  :hints (("Goal" :in-theory (e/d (fn-sco-capture fn-sco-make fn-sco-records fn-sco-cpr
                                   fn-sco-identity fn-sco-consumer fn-sco-topic
                                   fn-sco-event-index fn-sco-at)
                                  (fn-sco-cpr-prefix fn-replay-identity-loop
                                   fn-cpe-projection-replay fn-th-prefix-loop
                                   fn-cei-build-aux)))))

; -----------------------------------------------------------------------------
; The encoder's table and the decoder's agree: the capture's event index
; (records by sequence) and the index built from the P rows give the same
; P[s] for every s below the count, for histories the u32 index keys.

(local
 (defthm fn-sct-ref-get-of-build
   (implies (and (true-listp events) (natp s) (< s (len events))
                 (<= (len events) (1+ *fn-cbor-max-uint*)))
            (equal (fn-sct-ref-get s (fn-cei-build events))
                   (fn-sct-payload-of (nth s events))))
   :hints (("Goal" :in-theory (e/d (fn-sct-ref-get fn-cp-uintp)
                                   (fn-cei-build fn-cei-get))))))

(local
 (defthm fn-sct-agreep-of-build-aux
   (implies (and (true-listp records) (natp n) (<= n (len records))
                 (<= (len records) (1+ *fn-cbor-max-uint*)))
            (fn-sct-agreep (fn-cei-build records)
                           (fn-cei-build (fn-sct-payloads records))
                           n))
   :hints (("Goal" :induct (fn-sct-agreep (fn-cei-build records)
                                          (fn-cei-build (fn-sct-payloads records)) n)
            :in-theory (e/d (fn-sct-agreep)
                            (fn-cei-build fn-cei-get fn-sct-ref-get fn-sct-payloads))))))

(defthm fn-sct-agreep-of-build
  (implies (and (true-listp records)
                (<= (len records) (1+ *fn-cbor-max-uint*)))
           (fn-sct-agreep (fn-cei-build-aux records 0 nil)
                          (fn-cei-build (fn-sct-payloads records))
                          (len records)))
  :hints (("Goal" :use ((:instance fn-sct-agreep-of-build-aux (n (len records))))
           :in-theory (e/d (fn-cei-build) (fn-sct-agreep-of-build-aux fn-cei-build-aux)))))

; -----------------------------------------------------------------------------
; The four runs' programs (the encode side: INDEX is the capture's event
; index) and the decode of four programs (the decode side: the table is
; built from the P rows read).

(defun fn-sct-tables-treep (tables)
  (declare (xargs :guard t))
  (and (true-listp tables) (equal (len tables) 4)
       (fn-scc-treep (fn-sct-tables-f tables))
       (fn-sct-rows-treep (fn-sct-tables-p tables))
       (fn-sct-rows-treep (fn-sct-tables-e tables))
       (fn-sct-rows-treep (fn-sct-tables-r tables))))

(defun fn-sct-table-programs (tables index)
  (declare (xargs :guard (fn-sct-tables-treep tables)))
  (let ((n (len (fn-sct-tables-e tables))))
    (list (fn-sct-rows-program (list (fn-sct-tables-f tables)) 0 nil nil n nil)
          (fn-sct-rows-program (fn-sct-tables-p tables) 0 nil nil n nil)
          (fn-sct-rows-program (fn-sct-tables-e tables) 0 t nil n index)
          (fn-sct-rows-program (fn-sct-tables-r tables) 0 nil
                               (fn-cei-msgid-trie index) n index))))

(defun fn-sct-programsp (progs)
  (declare (xargs :guard t))
  (and (true-listp progs) (equal (len progs) 4)
       (fn-scc-octet-listp (nth 0 progs)) (fn-scc-octet-listp (nth 1 progs))
       (fn-scc-octet-listp (nth 2 progs)) (fn-scc-octet-listp (nth 3 progs))))

; (:ok TABLES) or (:refused REASON): :f-row (the F run is not one schema-3
; row), :close (a table's row count is not the F row's S, or R is not the
; four roots), :ref (a reference to an absent P row), :tree (a malformed
; program).
(defun fn-sct-decode-programs (progs)
  (declare (xargs :guard (fn-sct-programsp progs)))
  (let ((f (fn-sct-decode-rows (nth 0 progs) nil)))
    (if (not (eq (car f) :ok))
        f
      (let ((frows (cadr f)))
        (if (not (and (consp frows) (null (cdr frows)) (fn-sct-f-rowp (car frows))))
            (list :refused :f-row)
          (let* ((frow (car frows))
                 (s (cadr frow))
                 (p (fn-sct-decode-rows (nth 1 progs) nil)))
            (if (not (eq (car p) :ok))
                p
              (if (not (equal (len (cadr p)) s))
                  (list :refused :close)
                (let* ((table (fn-cei-build (cadr p)))
                       (e (fn-sct-decode-rows (nth 2 progs) table)))
                  (if (not (eq (car e) :ok))
                      e
                    (if (not (equal (len (cadr e)) s))
                        (list :refused :close)
                      (let ((r (fn-sct-decode-rows (nth 3 progs) table)))
                        (if (not (eq (car r) :ok))
                            r
                          (if (not (equal (len (cadr r)) 4))
                              (list :refused :close)
                            (list :ok (list frow (cadr p) (cadr e) (cadr r)))))))))))))))))

(local
 (defthm fn-sct-tables-of-capture-shape
   (let ((tables (fn-sct-tables-of-capture (fn-sco-capture configs records) frontier revision log)))
     (and (equal (nth 0 tables) (fn-sct-f-row (len records) frontier revision log))
          (equal (nth 1 tables) (fn-sct-payloads (true-list-fix records)))
          (equal (nth 2 tables) (true-list-fix records))
          (equal (nth 3 tables)
                 (list (fn-sco-cpr (fn-sco-capture configs records))
                       (fn-sco-identity (fn-sco-capture configs records))
                       (fn-sco-consumer (fn-sco-capture configs records))
                       (fn-sco-topic (fn-sco-capture configs records))))))
   :hints (("Goal" :in-theory (e/d (fn-sco-capture fn-sco-make fn-sco-records fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux fn-sco-cpr fn-sco-identity
                                    fn-sco-consumer fn-sco-topic))))))

(local
 (defthm fn-sct-event-index-of-capture
   (equal (fn-sco-event-index (fn-sco-capture configs records))
          (fn-cei-build-aux (true-list-fix records) 0 nil))
   :hints (("Goal" :in-theory (e/d (fn-sco-capture fn-sco-make fn-sco-event-index fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

(local
 (defthm fn-sct-records-of-capture
   (equal (fn-sco-records (fn-sco-capture configs records))
          (true-list-fix records))
   :hints (("Goal" :in-theory (e/d (fn-sco-capture fn-sco-make fn-sco-records fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

; The decode of the four programs written for the tables of a capture is
; those tables: the round trip at the row level, for every configuration
; history and every record list the codec encodes and the u32 index keys.
(defthm fn-sct-decode-programs-of-table-programs
  (implies (and (fn-sct-tables-treep
                 (fn-sct-tables-of-capture (fn-sco-capture configs records) frontier revision log))
                (fn-sct-log-positionp log)
                (<= (len records) (1+ *fn-cbor-max-uint*)))
           (equal (fn-sct-decode-programs
                   (fn-sct-table-programs
                    (fn-sct-tables-of-capture (fn-sco-capture configs records) frontier revision log)
                    (fn-sco-event-index (fn-sco-capture configs records))))
                  (list :ok (fn-sct-tables-of-capture (fn-sco-capture configs records)
                                                      frontier revision log))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sct-agreep-of-build (records (true-list-fix records))))
           :in-theory (e/d (fn-sct-tables-treep fn-sct-table-programs fn-sct-decode-programs
                            fn-sct-f-rowp fn-sct-f-row fn-sct-tables-of-capture)
                           (fn-sco-capture fn-sco-event-index fn-sco-records
                            fn-cei-build fn-cei-build-aux fn-sct-payloads fn-sco-cpr
                            fn-sco-identity fn-sco-consumer fn-sco-topic
                            fn-sct-agreep-of-build)))))

(in-theory (disable fn-sct-tables-of-capture fn-sct-capture-of-tables
                    fn-sct-table-programs fn-sct-decode-programs))

; -----------------------------------------------------------------------------
; The file: four runs of segments, F, P, E, R, each fn-scc-chunks of its
; program framed and chained from the genesis with sequence S.

(defun fn-sct-run-segments (prog seg s)
  (declare (xargs :guard (and (true-listp prog) (natp seg) (natp s)) :verify-guards nil))
  (let ((chunks (fn-scc-chunks prog seg)))
    (fn-scc-frames chunks 0 (len chunks) s *fn-scc-genesis*)))

(defun fn-sct-file-segments (progs seg s)
  (declare (xargs :guard (and (fn-sct-programsp progs) (natp seg) (natp s)) :verify-guards nil))
  (append (fn-sct-run-segments (nth 0 progs) seg s)
          (fn-sct-run-segments (nth 1 progs) seg s)
          (fn-sct-run-segments (nth 2 progs) seg s)
          (fn-sct-run-segments (nth 3 progs) seg s)))

(defun fn-sct-file-octets (progs seg s)
  (declare (xargs :guard (and (fn-sct-programsp progs) (natp seg) (natp s)) :verify-guards nil))
  (fn-scc-concat (fn-sct-file-segments progs seg s)))

; The reader, list level: one run at a time.  The first header names the
; run's count; that many segments are joined (the codec's chain check) into
; the run's program.
(defun fn-sct-take-segs (n segs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (not (consp segs)))
      nil
    (cons (car segs) (fn-sct-take-segs (1- n) (cdr segs)))))

(defun fn-sct-drop-segs (n segs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (not (consp segs)))
      segs
    (fn-sct-drop-segs (1- n) (cdr segs))))

(defthm fn-sct-take-segs-segment-listp
  (implies (fn-scc-segment-listp segs)
           (fn-scc-segment-listp (fn-sct-take-segs n segs))))

(defthm fn-sct-drop-segs-segment-listp
  (implies (fn-scc-segment-listp segs)
           (fn-scc-segment-listp (fn-sct-drop-segs n segs))))

(local
 (defthm fn-sct-parse-header-count-natp
   (implies (and (fn-scc-octet-listp seg) (fn-scc-parse-header seg))
            (natp (nth 1 (fn-scc-parse-header seg))))
   :hints (("Goal" :in-theory (enable fn-scc-parse-header fn-scc-u64-at)))))

; (:ok PROGRAM REST) or the codec's refusal (:header, :segment, :truncated),
; or :sequence when the run's header does not carry S.
(defun fn-sct-run-decode (segs s)
  (declare (xargs :guard (fn-scc-segment-listp segs)
                  :guard-hints (("Goal" :expand ((fn-scc-segment-listp segs))
                                 :in-theory (disable fn-scc-parse-header fn-scc-join
                                                     fn-scc-segment-listp)))))
  (let ((h (and (consp segs) (fn-scc-parse-header (car segs)))))
    (if (not h)
        (list :refused :header)
      (if (not (equal (nth 3 h) s))
          (list :refused :sequence)
        (let* ((count (nth 1 h))
               (j (fn-scc-join (fn-sct-take-segs count segs) 0 count s *fn-scc-genesis* nil)))
          (if (not (eq (car j) :ok))
              j
            (list :ok (nth 1 j) (fn-sct-drop-segs count segs))))))))

(defthm fn-sct-run-decode-ok-shape
  (implies (and (fn-scc-segment-listp segs)
                (eq (car (fn-sct-run-decode segs s)) :ok))
           (and (fn-scc-octet-listp (nth 1 (fn-sct-run-decode segs s)))
                (fn-scc-segment-listp (nth 2 (fn-sct-run-decode segs s)))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-scc-segment-listp segs))
           :use ((:instance fn-scc-join-octets
                            (segs (fn-sct-take-segs (nth 1 (fn-scc-parse-header (car segs))) segs))
                            (index 0) (count (nth 1 (fn-scc-parse-header (car segs))))
                            (sequence s) (prev *fn-scc-genesis*) (racc nil)))
           :in-theory (e/d (fn-sct-run-decode)
                           (fn-scc-parse-header fn-scc-join fn-scc-join-octets
                            fn-scc-segment-listp)))))

; The file: (:ok TABLES) or (:refused REASON), S read from the first header.
(defun fn-sct-decode-file (segs)
  (declare (xargs :guard (fn-scc-segment-listp segs)
                  :guard-hints (("Goal" :expand ((fn-scc-segment-listp segs))
                                 :in-theory (disable fn-scc-parse-header fn-sct-run-decode
                                                     fn-sct-decode-programs fn-scc-segment-listp)))))
  (let ((h (and (consp segs) (fn-scc-parse-header (car segs)))))
    (if (not h)
        (list :refused :header)
      (let* ((s (nth 3 h))
             (f (fn-sct-run-decode segs s)))
        (if (not (eq (car f) :ok))
            f
          (let ((p (fn-sct-run-decode (nth 2 f) s)))
            (if (not (eq (car p) :ok))
                p
              (let ((e (fn-sct-run-decode (nth 2 p) s)))
                (if (not (eq (car e) :ok))
                    e
                  (let ((r (fn-sct-run-decode (nth 2 e) s)))
                    (if (not (eq (car r) :ok))
                        r
                      (if (consp (nth 2 r))
                          (list :refused :trailing)
                        (let ((tables (fn-sct-decode-programs
                                       (list (nth 1 f) (nth 1 p) (nth 1 e) (nth 1 r)))))
                          (if (not (eq (car tables) :ok))
                              tables
                            (if (not (equal (fn-sco-at 1 (fn-sct-tables-f (cadr tables))) s))
                                (list :refused :close)
                              tables)))))))))))))))

; -----------------------------------------------------------------------------
; The round trip at the segment level: a run decodes to its program and
; leaves the rest of the file.

(local
 (defthm fn-sct-frames-len
   (equal (len (fn-scc-frames chunks index count sequence prev)) (len chunks))))

(local
 (defthm fn-sct-take-segs-of-append
   (implies (equal n (len a))
            (equal (fn-sct-take-segs n (append a b)) (true-list-fix a)))))

(local
 (defthm fn-sct-drop-segs-of-append
   (implies (equal n (len a))
            (equal (fn-sct-drop-segs n (append a b)) b))))

(local
 (defthm fn-sct-frames-true-listp
   (true-listp (fn-scc-frames chunks index count sequence prev))))

(local
 (defthm fn-sct-car-append
   (implies (consp a) (equal (car (append a b)) (car a)))))

(local
 (defthm fn-sct-consp-append
   (implies (consp a) (consp (append a b)))))

(defthm fn-sct-run-decode-of-run-segments
  (implies (and (fn-scc-octet-listp prog)
                (< (+ 1 (len prog)) *fn-scc-u64-bound*)
                (natp s) (< s *fn-scc-u64-bound*))
           (equal (fn-sct-run-decode (append (fn-sct-run-segments prog seg s) rest) s)
                  (list :ok prog rest)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-chunks-shape (payload prog))
                 (:instance fn-scc-join-of-chunks (p prog) (q s) (prev *fn-scc-genesis*))
                 (:instance fn-scc-parse-header-of-first-frame
                            (chunks (fn-scc-chunks prog seg))
                            (n (len (fn-scc-chunks prog seg))) (q s) (prev *fn-scc-genesis*))
                 (:instance fn-scc-parse-header-of-first-frame-sequence
                            (chunks (fn-scc-chunks prog seg))
                            (n (len (fn-scc-chunks prog seg))) (q s) (prev *fn-scc-genesis*)))
           :in-theory (e/d (fn-sct-run-segments)
                           (fn-scc-chunks fn-scc-frames fn-scc-join fn-scc-parse-header
                            fn-scc-chunks-shape fn-scc-join-of-chunks
                            fn-scc-parse-header-of-first-frame
                            fn-scc-parse-header-of-first-frame-sequence)))))

(local
 (defthm fn-sct-run-segments-consp
   (consp (fn-sct-run-segments prog seg s))
   :hints (("Goal" :in-theory (e/d (fn-sct-run-segments) (fn-scc-frames fn-scc-chunks))))))

(local
 (defthm fn-sct-parse-header-of-run-segments
   (implies (and (fn-scc-octet-listp prog)
                 (< (+ 1 (len prog)) *fn-scc-u64-bound*)
                 (natp s) (< s *fn-scc-u64-bound*))
            (and (fn-scc-parse-header (car (fn-sct-run-segments prog seg s)))
                 (equal (nth 3 (fn-scc-parse-header (car (fn-sct-run-segments prog seg s)))) s)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-chunks-shape (payload prog))
                  (:instance fn-scc-parse-header-of-first-frame-sequence
                             (chunks (fn-scc-chunks prog seg))
                             (n (len (fn-scc-chunks prog seg))) (q s) (prev *fn-scc-genesis*)))
            :in-theory (e/d (fn-sct-run-segments)
                            (fn-scc-chunks fn-scc-frames fn-scc-parse-header
                             fn-scc-chunks-shape
                             fn-scc-parse-header-of-first-frame-sequence))))))

(in-theory (disable fn-sct-run-segments fn-sct-run-decode))

(defun fn-sct-programs-widthp (progs)
  (declare (xargs :guard t))
  (and (fn-sct-programsp progs)
       (< (+ 1 (len (nth 0 progs))) *fn-scc-u64-bound*)
       (< (+ 1 (len (nth 1 progs))) *fn-scc-u64-bound*)
       (< (+ 1 (len (nth 2 progs))) *fn-scc-u64-bound*)
       (< (+ 1 (len (nth 3 progs))) *fn-scc-u64-bound*)))

(local
 (defthm fn-sct-len-4-shape
   (implies (and (true-listp progs) (equal (len progs) 4))
            (equal (list (car progs) (nth 1 progs) (nth 2 progs) (nth 3 progs))
                   progs))
   :hints (("Goal" :expand ((len progs) (len (cdr progs)) (len (cddr progs))
                            (len (cdddr progs)) (len (cddddr progs)))))))

; The four runs decode to the four programs, and the tables are what those
; programs decode to, with S checked against the F row.
(defthm fn-sct-decode-file-of-file-segments
  (implies (and (fn-sct-programs-widthp progs)
                (natp s) (< s *fn-scc-u64-bound*))
           (equal (fn-sct-decode-file (fn-sct-file-segments progs seg s))
                  (let ((tables (fn-sct-decode-programs progs)))
                    (if (not (eq (car tables) :ok))
                        tables
                      (if (not (equal (fn-sco-at 1 (fn-sct-tables-f (cadr tables))) s))
                          (list :refused :close)
                        tables)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sct-run-decode-of-run-segments (prog (nth 0 progs))
                            (rest (append (fn-sct-run-segments (nth 1 progs) seg s)
                                          (fn-sct-run-segments (nth 2 progs) seg s)
                                          (fn-sct-run-segments (nth 3 progs) seg s))))
                 (:instance fn-sct-run-decode-of-run-segments (prog (nth 1 progs))
                            (rest (append (fn-sct-run-segments (nth 2 progs) seg s)
                                          (fn-sct-run-segments (nth 3 progs) seg s))))
                 (:instance fn-sct-run-decode-of-run-segments (prog (nth 2 progs))
                            (rest (fn-sct-run-segments (nth 3 progs) seg s)))
                 (:instance fn-sct-run-decode-of-run-segments (prog (nth 3 progs))
                            (rest nil))
                 (:instance fn-sct-parse-header-of-run-segments (prog (nth 0 progs))))
           :in-theory (e/d (fn-sct-decode-file fn-sct-file-segments fn-sct-programsp
                            fn-sct-programs-widthp)
                           (fn-sct-run-decode-of-run-segments fn-sct-parse-header-of-run-segments
                            fn-scc-parse-header fn-sct-decode-programs)))))

; -----------------------------------------------------------------------------
; KEYSTONE, list level: reading the file written for the tables of a capture
; gives the tables, and their value is the capture.

(local
 (defthm fn-sct-f-of-tables-of-capture
   (equal (nth 1 (nth 0 (fn-sct-tables-of-capture (fn-sco-capture configs records)
                                                  frontier revision log)))
          (len records))
   :hints (("Goal" :in-theory (e/d (fn-sct-tables-of-capture fn-sco-capture fn-sco-make
                                    fn-sco-records fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

(defthm fn-sct-decode-file-of-file-is-the-capture
  (let* ((c (fn-sco-capture configs records))
         (tables (fn-sct-tables-of-capture c frontier revision log))
         (progs (fn-sct-table-programs tables (fn-sco-event-index c))))
    (implies (and (fn-sct-tables-treep tables)
                  (fn-sct-log-positionp log)
                  (<= (len records) (1+ *fn-cbor-max-uint*))
                  (fn-sct-programs-widthp progs))
             (and (equal (fn-sct-decode-file (fn-sct-file-segments progs seg (len records)))
                         (list :ok tables))
                  (equal (fn-sct-capture-of-tables tables) c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cp-uintp)
                           (fn-sct-event-index-of-capture
                            fn-sct-tables-of-capture fn-sco-capture fn-sco-event-index
                            fn-sct-table-programs fn-sct-decode-file fn-sct-file-segments
                            fn-sct-tables-treep fn-sct-programs-widthp fn-sct-decode-programs
                            fn-sct-capture-of-tables)))))

(in-theory (disable fn-sct-file-segments fn-sct-file-octets fn-sct-decode-file))

; -----------------------------------------------------------------------------
; The open's choice with this schema's refusal named (host
; fn-store-sco-select): a file of another schema (the reader's :schema,
; fn-sccr-admit-segment) replays the journal as `checkpoint-schema'; every
; other status is fn-sco-select's.

(defun fn-sco-select-named (status sequence count k)
  (declare (xargs :guard t))
  (if (eq status :schema)
      (list :full-replay :checkpoint-schema)
    (fn-sco-select status sequence count k)))

(defthm fn-sco-select-named-unfolds
  (implies (not (eq status :schema))
           (equal (fn-sco-select-named status sequence count k)
                  (fn-sco-select status sequence count k))))

(defthm fn-sco-select-named-refuses-schema
  (equal (fn-sco-select-named :schema sequence count k)
         (list :full-replay :checkpoint-schema)))
