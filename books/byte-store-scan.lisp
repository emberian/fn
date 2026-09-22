; The scan, the byte-store/kernel relation, and the K1-K3 keystones.
;
; specs/crash-model-v2.md sections 3.1 to 3.3.  This book answers the question
; the byte model exists to answer: what the host's recover() reads out of a
; crash image, and why that reading is one the file kernel
; (books/store-files.lisp) already admits.  The kernel predicate this book
; proves inhabited by every byte-level crash of a related state is
; fn-sf-recovery-crash-imagep, what the PLATFORM may leave (decision D14-b).
; fn-sf-crash-imagep, what a consumer may RELY on, is unchanged and is not
; K2's conclusion: widening it is false for the composition, and the
; counterexample is in tests/acl2/owner-tests.lisp.
;
; The route.  The previous lane (w9/storage, planning/lanes/HANDOFF-w9-storage.md)
; recorded that the natural PER-DIRECTORY lemma -- "one directory's entries
; after a list of operations depend only on that directory's operations" -- is
; both a looping rewrite and an induction that does not close, because the
; branch where the head operation names another directory needs a commutation
; lemma nothing has.  The route that works, and the one taken here, is
; PER-NAME: byte-store-invariants.lisp reduces one entry's value to
; fn-bs-entry-after, which ignores other directories' operations BY
; CONSTRUCTION, so no commutation is ever needed.  This book lifts exactly
; that shape to the name LIST (fn-bs-names-after, section 2) and to the
; content at each name (section 4), then composes over the name list by
; induction with the record decoder closed (section 5).
;
; Two seams are constrained functions, as section 3.1 prescribes: the frontier
; codec (Python owns the JSON+sha256 today; packet P4 makes it an fn-frame
; frame) and the transaction file name (the host's "{:020d}.txn"; ACL2 owning
; the decimal format is its own packet).  fn-bs-config-okp is the third, for
; the same reason.  Each is an encapsulate with a local witness, and the
; theorems below use only the named constraints.

(in-package "ACL2")
(include-book "byte-store-invariants")
(include-book "store-files-invariants")
(local (include-book "arithmetic/top" :dir :system))

; The readers only.  fn-bs-invariants-vocabulary is seventy rules over alists,
; octets, tears and selections; enabling it book-wide made the name-list
; induction of section 2 exhaust a 2,000,000 step limit re-deriving table
; well-formedness in every branch.  It is enabled where section 5 needs it.
(local (in-theory (enable fn-bs-view fn-bs-lookup fn-bs-content
                          fn-bs-names fn-bs-durable-content fn-bs-durable-entry
                          fn-bs-fencedp fn-bs-dir-quietp)))

; -----------------------------------------------------------------------------
; 0. The two list facts a certify-book world does not have.
;
; This is the certify/ld gap lane w9/storage-2 recorded, and it is not subtle
; once named: an `ld' driver that includes several books inherits their
; enabled rules, and this book's include-closure (byte-store-invariants,
; store-files-invariants, arithmetic/top) carries neither of these.  Without
; the first, fn-bs-crash-select-names-are-an-outcome recursed to the
; induction-depth-limit at 33,381,159 prover steps
; (build/acl2/certify-20260920T193919Z-1122107,
; books--byte-store-scan.certify.log:16128); without the second,
; fn-bs-txn-names-length failed at Subgoal *1/4'.  Both are local: nothing
; below the book should acquire a global APPEND rule from it.
; fn-bs-member-of-append is byte-store-invariants' own rule, withdrawn with
; the rest of fn-bs-invariants-vocabulary at that book's end; it is enabled
; here rather than restated, so the tree keeps one APPEND membership rule.
(local (in-theory (enable fn-bs-member-of-append)))

; This one is local to byte-store-invariants, so there is nothing to enable.
(local
 (defthm fn-bs-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

; -----------------------------------------------------------------------------
; 1. The three seams.

; The frontier codec (design 3.1).  Today the frontier file is JSON with a
; Python-computed sha256 (tools/run_store.py:567), which the assurance rules
; forbid as a twin; after packet P4 it is an fn-frame frame and this becomes
; (fn-frame-open octets ...) followed by a CBOR uint decode.  The theorems in
; this book depend only on the two constraints.
(encapsulate
  (((fn-bs-frontier-decode *) => *)
   ((fn-bs-frontier-encode *) => *))
  (local (defun fn-bs-frontier-encode (n) (list n)))
  (local (defun fn-bs-frontier-decode (octets)
           (if (and (consp octets) (natp (car octets)) (null (cdr octets)))
               (car octets)
             nil)))
  ; The host allocator and the deterministic CBOR uint profile are uint32.
  ; The earlier all-natural constraint could not be realized by the bounded
  ; metadata codec; no scan/crash theorem uses round-trip outside this domain.
  (defthm fn-bs-frontier-round-trip
    (implies (and (natp n) (<= n *fn-cbor-max-uint*))
             (equal (fn-bs-frontier-decode (fn-bs-frontier-encode n)) n)))
  (defthm fn-bs-frontier-decode-nat-or-nil
    (or (natp (fn-bs-frontier-decode octets))
        (null (fn-bs-frontier-decode octets)))
    :rule-classes :type-prescription))

; The transaction file name.  The decimal format "{:020d}.txn" is the host's
; (tools/run_store.py); what the scan needs of it is that it is a name and
; that distinct sequence numbers get distinct names.
(encapsulate
  (((fn-bs-txn-name *) => *))
  (local
   (defun fn-bs-txn-chars (n)
     (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
     (if (zp n) nil (cons #\a (fn-bs-txn-chars (1- n))))))
  (local
   (defthm fn-bs-txn-chars-are-characters
     (character-listp (fn-bs-txn-chars n))))
  (local
   (defthm fn-bs-txn-chars-length
     (equal (len (fn-bs-txn-chars n)) (nfix n))))
  (local
   (defthm fn-bs-txn-chars-injective
     (implies (and (natp i) (natp j)
                   (equal (fn-bs-txn-chars i) (fn-bs-txn-chars j)))
              (equal i j))
     :rule-classes nil
     :hints (("Goal" :use ((:instance fn-bs-txn-chars-length (n i))
                           (:instance fn-bs-txn-chars-length (n j)))
              :in-theory (disable fn-bs-txn-chars-length)))))
  (local
   (defthm fn-bs-coerce-list-of-string
     (implies (character-listp x)
              (equal (coerce (coerce x 'string) 'list) x))
     :rule-classes nil
     :hints (("Goal" :use coerce-inverse-2))))
  ; Under the minimal theory nothing rewrites the two coerce terms away, so
  ; the string equality carries to the character lists by congruence.
  (local
   (defthm fn-bs-txn-chars-injective-through-coerce
     (implies (and (natp i) (natp j)
                   (equal (coerce (fn-bs-txn-chars i) 'string)
                          (coerce (fn-bs-txn-chars j) 'string)))
              (equal i j))
     :rule-classes nil
     :hints (("Goal"
              :use ((:instance fn-bs-coerce-list-of-string (x (fn-bs-txn-chars i)))
                    (:instance fn-bs-coerce-list-of-string (x (fn-bs-txn-chars j)))
                    fn-bs-txn-chars-injective
                    (:instance fn-bs-txn-chars-are-characters (n i))
                    (:instance fn-bs-txn-chars-are-characters (n j)))
              :in-theory (theory 'minimal-theory)))))
  (local (defun fn-bs-txn-name (n) (coerce (fn-bs-txn-chars n) 'string)))
  (defthm fn-bs-txn-name-is-a-name
    (fn-bs-namep (fn-bs-txn-name n)))
  (defthm fn-bs-txn-name-is-injective
    (implies (and (natp i) (natp j) (not (equal i j)))
             (not (equal (fn-bs-txn-name i) (fn-bs-txn-name j))))
    :hints (("Goal" :use fn-bs-txn-chars-injective-through-coerce))))

; The config file.  Same seam as the frontier: run_store.py computes its
; integrity value today (config_with_checksum), which packet P4 moves into
; ACL2.  The scan only needs that the check is a function of the octets, so
; the encapsulate carries no constraint beyond that.
(encapsulate
  (((fn-bs-config-okp *) => *))
  (local (defun fn-bs-config-okp (octets) (declare (ignore octets)) t)))

(defconst *fn-bs-scan-config-name* "config.json")
(defconst *fn-bs-scan-frontier-name* "allocation-frontier.json")

; -----------------------------------------------------------------------------
; 2. The name list of one directory, per-name.
;
; fn-bs-names-after is to strip-cars what fn-bs-entry-after (byte-store-
; invariants) is to one entry's value: a projection of the operation list onto
; ONE directory that ignores every other directory's operations by
; construction.  That is the whole reason the per-directory route failed and
; this one does not.

; Exactly the alist rules this section inducts through, and no others.
(local (in-theory (enable fn-bs-assoc-of-put-assoc-same
                          fn-bs-assoc-of-put-assoc-other
                          fn-bs-alistp-of-put-assoc
                          fn-bs-entriesp-implies-alistp
                          ; the rewrite, so fn-bs-dir-tablep does not have to
                          ; be OPENED to learn (alistp dirs): profiling the
                          ; bridge below found 42,664 frames of
                          ; (:DEFINITION FN-BS-DIR-TABLEP) with no useful
                          ; application doing exactly that.
                          fn-bs-dir-tablep-implies-alistp
                          fn-bs-dir-tablep-entries-are-entries
                          fn-bs-put-assoc-preserves-entriesp
                          fn-bs-del-assoc-preserves-entriesp
                          fn-bs-put-assoc-preserves-dir-tablep)))

(defun fn-bs-name-step (op old)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car op) :set-entry)
      (if (member-equal (nth 2 op) old) old (append old (list (nth 2 op))))
    (remove-equal (nth 2 op) old)))

(defun fn-bs-names-after (ops old dir)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (let ((op (car ops)))
        (fn-bs-names-after
         (cdr ops)
         (if (and (member-equal (car op) '(:set-entry :del-entry))
                  (equal (nth 1 op) dir))
             (fn-bs-name-step op old)
           old)
         dir))
    old))

(defthm fn-bs-strip-cars-of-put-assoc
  (implies (alistp alist)
           (equal (strip-cars (fn-bs-put-assoc key val alist))
                  (if (member-equal key (strip-cars alist))
                      (strip-cars alist)
                    (append (strip-cars alist) (list key))))))

(defthm fn-bs-strip-cars-of-del-assoc
  (implies (alistp alist)
           (equal (strip-cars (fn-bs-del-assoc key alist))
                  (remove-equal key (strip-cars alist)))))

(defthm fn-bs-alistp-of-del-assoc
  (implies (alistp alist) (alistp (fn-bs-del-assoc key alist))))

(defthm fn-bs-alistp-of-dir-entries
  (implies (fn-bs-dir-tablep dirs)
           (alistp (cdr (assoc-equal dir dirs)))))

(defthm fn-bs-apply-entries-preserves-alistp-of-entries
  (implies (and (fn-bs-dir-tablep dirs) (fn-bs-op-listp ops))
           (fn-bs-dir-tablep (fn-bs-apply-entries dirs ops))))

; The projection onto one directory, as a single IF-producing rewrite.  The
; two conditional rules fn-bs-assoc-of-put-assoc-{same,other} express the
; same fact, but as rewrites they leave the induction step below to discover
; the case split for itself, which exhausted a 2,000,000 step limit twice.
(local
 (defthm fn-bs-strip-cars-of-assoc-of-put-assoc
   (implies (alistp dirs)
            (equal (strip-cars (cdr (assoc-equal dir (fn-bs-put-assoc k v dirs))))
                   (if (equal k dir)
                       (strip-cars v)
                     (strip-cars (cdr (assoc-equal dir dirs))))))))

; The bridge from fn-bs-apply-entries to fn-bs-names-after.
(defthm fn-bs-apply-entries-names-is-names-after
  (implies (and dir (fn-bs-dir-tablep dirs) (fn-bs-op-listp ops))
           (equal (strip-cars
                   (cdr (assoc-equal dir (fn-bs-apply-entries dirs ops))))
                  (fn-bs-names-after
                   ops (strip-cars (cdr (assoc-equal dir dirs))) dir)))
  :hints (("Goal" :induct (fn-bs-apply-entries dirs ops)
           ; The recognizers stay CLOSED.  tools/proof_profile.py on this
           ; form reported 13 runes with no useful application at all, and
           ; the top four were the recognizers opening: DEFAULT-CAR 113,606
           ; frames, FN-BS-ENTRIESP 47,712, FN-BS-DIR-TABLEP 42,664,
           ; FN-BS-ENTRIESP-IMPLIES-ALISTP 27,456, ALISTP 16,224,
           ; ASSOC-EQUAL 26,504, plus FN-SF-ADMISSIBLE-IMAGE-FACTS 8,379
           ; from a book that has nothing to say here.  The two conditional
           ; fn-bs-assoc-of-put-assoc rules are disabled in favour of the
           ; IF-producing fn-bs-strip-cars-of-assoc-of-put-assoc above.
           :in-theory (disable fn-bs-assoc-of-put-assoc-same
                               fn-bs-assoc-of-put-assoc-other
                               fn-bs-dir-tablep fn-bs-entriesp alistp
                               assoc-equal fn-sf-admissible-image-facts))))

; How it closed, recorded because the answer was not another hint.  Three
; hints were tried by the previous lane and none of them was the cause: the
; book-wide fn-bs-invariants-vocabulary enable narrowed to the alist rules
; this section inducts through, fn-bs-strip-cars-of-assoc-of-put-assoc above
; (one IF-producing rewrite in place of the two conditional ones), and
; :do-not '(generalize fertilize).  The form still reached the
; induction-depth-limit at 2,016,278 prover steps.
;
; tools/proof_profile.py named the cause in one run: THIRTEEN runes with no
; useful application at all, and the top of that list was the recognizers
; being opened -- FN-BS-ENTRIESP 47,712 frames, FN-BS-DIR-TABLEP 42,664,
; ALISTP 16,224, ASSOC-EQUAL 26,504, all of them re-deriving (alistp dirs)
; in every branch.  Closing them, and enabling fn-bs-dir-tablep-implies-alistp
; so the fact arrives as a rewrite instead, takes the form to 33,789 prover
; steps and 0.05 seconds.

(defthm fn-bs-names-after-of-tear-write
  (equal (fn-bs-names-after (fn-bs-tear-write op sels i unit) old dir) old))

(defthm fn-bs-names-after-of-append
  (equal (fn-bs-names-after (append a b) old dir)
         (fn-bs-names-after b (fn-bs-names-after a old dir) dir)))

; The outcome enumeration, exactly as fn-bs-entry-outcomes does it for one
; entry's value: every name list a crash can leave, from the operations of
; this directory alone.
; OPS is already one directory's operation list, so the enumeration takes no
; directory argument: it mirrors fn-bs-entry-outcomes (byte-store-invariants)
; exactly, formal for formal.
(defun fn-bs-names-outcomes (ops old)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (append (fn-bs-names-outcomes (cdr ops) old)
              (fn-bs-names-outcomes (cdr ops) (fn-bs-name-step (car ops) old)))
    (list old)))

; The two enumerations the relation's shape clause actually produces: a quiet
; directory, and a directory with exactly one pending entry operation.  The
; shape clause bounds the list by (len ops), not by its spine, so
; fn-bs-names-outcomes never opens on it without these.
(defthm fn-bs-names-outcomes-of-no-ops
  (implies (not (consp ops))
           (equal (fn-bs-names-outcomes ops old) (list old))))

(defthm fn-bs-names-outcomes-of-one-op
  (implies (and (consp ops) (not (consp (cdr ops))))
           (equal (fn-bs-names-outcomes ops old)
                  (list old (fn-bs-name-step (car ops) old)))))

(local
 (defun fn-bs-names-induct (ops choices old dir)
   (if (consp ops)
       (let ((op (car ops)))
         (list (fn-bs-names-induct (cdr ops) (cdr choices) old dir)
               (fn-bs-names-induct (cdr ops) (cdr choices)
                                   (fn-bs-name-step op old) dir)))
     (list old choices dir))))

(defthm fn-bs-crash-select-names-are-an-outcome
  (member-equal (fn-bs-names-after (fn-bs-crash-select ops choices unit) old dir)
                (fn-bs-names-outcomes (fn-bs-ops-for-dir ops dir) old))
  :hints (("Goal" :induct (fn-bs-names-induct ops choices old dir))))

; -----------------------------------------------------------------------------
; 3. The scan (design 3.1).

; The record decoder is a function of the OCTETS, and section 6 needs exactly
; that: two images that hold the same content at an inode read the same
; record there.  With the decoder written only as (fn-bs-record-of s ino) the
; two sides of that equality are two disabled terms over different states and
; nothing connects them; split in two, the content equality in the hypothesis
; substitutes and the two sides become the same term.
(defun fn-bs-record-of-octets (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((frame (fn-frame-store-decode
                 octets (fn-frame-digest (fn-frame-protected-prefix octets))))
         (decoded (and (fn-frame-result-okp frame)
                       (fn-store-event-decode-exact
                        (fn-frame-result-payload frame)))))
    (if (and (consp decoded) (equal (car decoded) :ok)
             (fn-store-event-p (nth 1 decoded)))
        (nth 1 decoded)
      nil)))

(defun fn-bs-record-of (s ino)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-record-of-octets (fn-bs-content s ino)))

(defun fn-bs-txn-names (n)
  (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (if (zp n) nil (append (fn-bs-txn-names (1- n)) (list (fn-bs-txn-name (1- n))))))

(defun fn-bs-contiguous-namesp (names n)
  (declare (xargs :guard t :verify-guards nil))
  (equal names (fn-bs-txn-names n)))

(defun fn-bs-txn-observation-pairs (names sequence)
  "Bind each sorted observed transaction name to the scan codec's sequence."
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (if (equal (car names) (fn-bs-txn-name sequence))
          ; `nfix': `fn-bs-txn-observation-covered' (books/byte-store-txn-name)
          ; reaches this function in the branch where its own `natp' checks
          ; failed, so `:guard t' here leaves (acl2-numberp sequence) with
          ; nothing to prove it and the guard conjecture suggests no induction.
          ; The two callers start at 0 or at a checked lower bound, so `nfix'
          ; is the identity on the composed machine.
          (let ((rest (fn-bs-txn-observation-pairs (cdr names)
                                                   (1+ (nfix sequence)))))
            (if (equal rest :invalid)
                :invalid
              (cons (list sequence (car names)) rest)))
        :invalid)
    (if (null names) nil :invalid)))

(verify-guards fn-bs-txn-observation-pairs)

(defun fn-bs-read-records (s n count)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (nfix count) (nfix n)))))
  (if (or (not (natp n)) (not (natp count)) (>= n count))
      nil
    (let* ((ino (fn-bs-lookup s :transactions (fn-bs-txn-name n)))
           (record (and (fn-bs-inop ino) (fn-bs-record-of s ino)))
           (rest (fn-bs-read-records s (1+ n) count)))
      (if (or (not (fn-store-event-p record))
              (not (equal (fn-store-event-sequence record) n))
              (equal rest :fault))
          :fault
        (cons record rest)))))

(defun fn-bs-scan-store (image)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-bs-lookup image :root *fn-bs-scan-config-name*))
        (f (fn-bs-lookup image :root *fn-bs-scan-frontier-name*))
        (names (fn-bs-names image :transactions)))
    (cond ((not (fn-bs-inop c)) (list :fault :config))
          ((not (fn-bs-config-okp (fn-bs-content image c))) (list :fault :config))
          ((not (fn-bs-inop f)) (list :fault :frontier))
          ((not (natp (fn-bs-frontier-decode (fn-bs-content image f))))
           (list :fault :frontier))
          ((not (fn-bs-contiguous-namesp names (len names))) (list :fault :namespace))
          (t (let ((records (fn-bs-read-records image 0 (len names))))
               (if (equal records :fault)
                   (list :fault :record)
                 (list :ok (fn-bs-frontier-decode (fn-bs-content image f)) records)))))))

(defun fn-bs-scan-okp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp x) (equal (car x) :ok)))
(defun fn-bs-scan-frontier (x) (declare (xargs :guard t :verify-guards nil)) (nth 1 x))
(defun fn-bs-scan-records (x) (declare (xargs :guard t :verify-guards nil)) (nth 2 x))

; -----------------------------------------------------------------------------
; 4. The relation (design 3.2), with the durable contiguity the handoff names.

(defun fn-bs-durable (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs) nil
              (fn-bs-next-ino bs)))

(defun fn-bs-durable-names (bs dir)
  (declare (xargs :guard t :verify-guards nil))
  (strip-cars (cdr (assoc-equal dir (fn-bs-dirs bs)))))

(defun fn-bs-durable-frontier (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-frontier-decode
   (fn-bs-durable-content bs (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))))

(defun fn-bs-durable-records (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-read-records (fn-bs-durable bs) 0
                      (len (fn-bs-durable-names bs :transactions))))

; The recovery window (design 3.2, decision D14-a): the phases a process is
; in between replaying what it SCANNED and completing the five recovery
; fences (tools/run_store.py:1179-1201).  A store reaches them with a
; NON-EMPTY pending list whenever the previous process died between its link
; or rename and that operation's directory fence -- process death is not
; power loss, so the entry operation is still in the kernel's cache and the
; next process's scan reads it (run_store.py:1100 scans the live directory,
; 1164 replays what it read, host/store-node-host.lisp:39 builds the
; :replaying image from it).
(defun fn-bs-replay-visiblep (ks)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal (fn-sf-phase ks) '(:replaying :recovering :fenced-recovery)))

; The SHAPE of the pending half: at most one entry operation per authority
; directory, at the name the DURABLE namespace fixes, pointing at a fenced
; inode.  Which VALUE that inode holds is the window's question, below.
;
; The name is written from the durable namespace and not as
; (fn-bs-txn-name (len (fn-sf-records ks))): in the publish window the two
; are the same number, and in the recovery window the kernel's count is one
; HIGHER, so only this form names the pending entry at every cut.  That is
; decision D14-a, and the evidence is in planning/decisions.md.
(defun fn-bs-pending-shape-okp (bs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((root-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
        (txn-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
    (and (or (null root-ops)
             ; "exactly one" by SPINE, not by (len ops): the enumeration
             ; fn-bs-names-outcomes walks the spine, and a bound on the
             ; length leaves it closed.
             (and (consp root-ops) (not (consp (cdr root-ops)))
                  (equal (car (car root-ops)) :set-entry)
                  (equal (nth 2 (car root-ops)) *fn-bs-scan-frontier-name*)
                  (fn-bs-inop (nth 3 (car root-ops)))
                  (fn-bs-fencedp bs (nth 3 (car root-ops)))))
         (or (null txn-ops)
             (and (consp txn-ops) (not (consp (cdr txn-ops)))
                  (equal (car (car txn-ops)) :set-entry)
                  (equal (nth 2 (car txn-ops))
                         (fn-bs-txn-name
                          (len (fn-bs-durable-names bs :transactions))))
                  (fn-bs-inop (nth 3 (car txn-ops)))
                  (fn-bs-fencedp bs (nth 3 (car txn-ops))))))))

; The publish window.  The kernel has not observed the directory barrier, so
; its record list is still the DURABLE list and the pending entry names the
; candidate.  The equality is on the record LIST, not on its length: that is
; what excludes the image holding the candidate twice, because it forces the
; durable namespace to be the pre-candidate one whenever a link is pending.
(defun fn-bs-pending-matches-phase (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (let ((root-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
        (txn-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
    (and (fn-bs-pending-shape-okp bs)
         (if root-ops
             (and (fn-sf-frontier-new-visiblep ks)
                  (equal (fn-bs-frontier-decode
                          (fn-bs-durable-content bs (nth 3 (car root-ops))))
                         (fn-sf-frontier-candidate ks)))
           t)
         (if txn-ops
             (and (fn-sf-record-present-visiblep ks)
                  (equal (fn-bs-durable-records bs) (fn-sf-records ks))
                  (equal (fn-bs-record-of (fn-bs-durable bs) (nth 3 (car txn-ops)))
                         (fn-sf-record-candidate ks)))
           t))))

; The recovery window.  The kernel is exactly what THIS process's scan of the
; view said, and it carries no success: fn-sn-initial starts with none and
; Store.recover runs once per process, at open (run_store.py:1674,
; run_owner.py:660, fn9p.py:428, run_reader.py:313, run_bp_ingress.py:132).
; The last conjunct lines this arm up with the recovery arm of
; fn-sf-recovery-crash-imagep, whose own (null (fn-sf-successes s)) conjunct
; is why a crash here loses no acknowledged record (D14-b).  K2r is retired:
; fn-sf-recovery-admissible-image-facts proves it at the kernel.
(defun fn-bs-replay-matches-scan (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (let ((scan (fn-bs-scan-store bs))
        (root-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
        (txn-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
    (and (fn-bs-pending-shape-okp bs)
         (fn-bs-scan-okp scan)
         (equal (fn-sf-frontier ks) (fn-bs-scan-frontier scan))
         (equal (fn-sf-records ks) (fn-bs-scan-records scan))
         (equal (fn-sf-successes ks) nil)
         ; K2f, the frontier half of the window (specs/crash-model-v2.md
         ; s3.3).  The window is entered with a pending :root rename as well
         ; as with a pending :transactions link -- die at frontier-replaced
         ; (run_store.py:1305), reopen, and _load_frontier reads the VIEW --
         ; and :root is drained only by the FOURTH recovery barrier,
         ; fsync_dir(self.root) at :1216.  So while that operation is pending
         ; the DURABLE frontier is the scanned one minus one, because
         ; advance_frontier writes old+1 (run_store.py:1281), and a crash
         ; here rolls the kernel's frontier back to it.
         ;
         ; (null txn-ops) is the EXCLUSIVITY the phase used to supply.  In the
         ; publish window fn-bs-pending-matches-phase gets it for free:
         ; fn-sf-frontier-new-visiblep and fn-sf-record-present-visiblep are
         ; disjoint phase sets, so at most one branch can hold.  In the
         ; recovery window the phase says nothing, so the relation says it,
         ; and it is true of the host for the same reason -- advance_frontier
         ; fences :root and publish fences :transactions before either
         ; returns, and neither runs before recovery completes, so a dead
         ; process leaves at most one un-fenced authority entry behind.
         ;
         ; fn-sf-frontier-rollback-visiblep is named rather than spelled out:
         ; it is exactly the arm of fn-sf-recovery-crash-imagep that the
         ; rolled-back image lands in, and its fn-sf-record-listp conjunct --
         ; no record holds the txid this rename reserves -- is what makes
         ; that image a kernel state.  True of the host because the record
         ; that consumes the reservation is published only after the rename
         ; is durable.
         (if root-ops
             (and (null txn-ops)
                  (fn-sf-frontier-rollback-visiblep ks)
                  (equal (fn-bs-durable-frontier bs)
                         (1- (fn-sf-frontier ks))))
           t))))

; Every inode an authority entry names, durable or pending, is fenced: no
; pending write can reach it, so a crash keeps its content exactly (D1, D2).
(defun fn-bs-pending-entry-targets (ops)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((and (equal (car (car ops)) :set-entry)
              (member-equal (nth 1 (car ops)) '(:root :transactions)))
         (cons (nth 3 (car ops)) (fn-bs-pending-entry-targets (cdr ops))))
        (t (fn-bs-pending-entry-targets (cdr ops)))))

(defun fn-bs-authority-inode-list (bs)
  (declare (xargs :guard t :verify-guards nil))
  (append (list (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)
                (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))
          (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs bs))))
          (fn-bs-pending-entry-targets (fn-bs-pending bs))))

(defun fn-bs-all-fencedp (bs inos)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp inos)
      (and (fn-bs-fencedp bs (car inos)) (fn-bs-all-fencedp bs (cdr inos)))
    t))

(defun fn-bs-authority-fencedp (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-all-fencedp bs (fn-bs-authority-inode-list bs)))

; K0 needs allocation separation, not merely a natural-number inode
; target.  The byte-state recognizer permits dangling directory targets,
; and the abstract codec seams alone do not rule out decoding empty absent
; content.  Such a target can equal next-ino and be reused by staging
; create/write.  Actual authority publication always names a created inode.
(defun fn-bs-inode-list-knownp (bs inos)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp inos)
      (and (consp (assoc-equal (car inos) (fn-bs-inodes bs)))
           (fn-bs-inode-list-knownp bs (cdr inos)))
    t))

(defun fn-bs-authority-knownp (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-inode-list-knownp bs (fn-bs-authority-inode-list bs)))

(defun fn-bs-store-relation (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-statep bs) (fn-sf-statep ks)
       (fn-bs-inop (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
       (fn-bs-config-okp
        (fn-bs-durable-content bs (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)))
       (fn-bs-inop (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))
       ; the durable transaction namespace is contiguous: the handoff's
       ; clause, without which the scan's namespace test is not decidable
       ; from the pending list alone.
       (fn-bs-contiguous-namesp (fn-bs-durable-names bs :transactions)
                                (len (fn-bs-durable-names bs :transactions)))
       (not (equal (fn-bs-durable-records bs) :fault))
       (if (fn-bs-replay-visiblep ks)
           (fn-bs-replay-matches-scan bs ks)
         (and (fn-sf-crash-imagep ks (fn-bs-durable-frontier bs)
                                  (fn-bs-durable-records bs))
              (fn-bs-pending-matches-phase bs ks)))
       (fn-bs-authority-fencedp bs)
       (fn-bs-authority-knownp bs)))

; -----------------------------------------------------------------------------
; 5. From a crash image back to the durable state, name by name.
;
; Everything here is stated on ONE name (or one inode) at a time, and the
; composition over the transaction directory is an induction over the name
; list with fn-record-p and the frame decoder closed.

(local (in-theory (enable fn-bs-statep fn-bs-invariants-vocabulary
                          fn-bs-entry-after)))

(defthm fn-bs-crash-pending-is-nil
  (equal (fn-bs-pending (fn-bs-crash s choices)) nil)
  :hints (("Goal" :in-theory (enable fn-bs-crash))))

(defthm fn-bs-crash-image-is-quiet
  (implies (fn-bs-crash-imagep s image) (equal (fn-bs-pending image) nil))
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep))))

(defthm fn-bs-quiet-lookup-is-durable-entry
  (implies (equal (fn-bs-pending s) nil)
           (equal (fn-bs-lookup s dir name) (fn-bs-durable-entry s dir name))))
(defthm fn-bs-quiet-content-is-durable-content
  (implies (equal (fn-bs-pending s) nil)
           (equal (fn-bs-content s ino) (fn-bs-durable-content s ino))))
(defthm fn-bs-quiet-names-are-durable-names
  (implies (equal (fn-bs-pending s) nil)
           (equal (fn-bs-names s dir) (fn-bs-durable-names s dir))))

(defthm fn-bs-durable-is-quiet
  (and (equal (fn-bs-pending (fn-bs-durable bs)) nil)
       (equal (fn-bs-inodes (fn-bs-durable bs)) (fn-bs-inodes bs))
       (equal (fn-bs-dirs (fn-bs-durable bs)) (fn-bs-dirs bs))))

; One name's operations are the operations of its directory, filtered again.
; As a rewrite its right side matches its own left side (with OPS bound to
; (fn-bs-ops-for-dir ops dir)), so it is cited, never left to match.
(defthm fn-bs-ops-for-name-through-ops-for-dir
  (equal (fn-bs-ops-for-name ops dir name)
         (fn-bs-ops-for-name (fn-bs-ops-for-dir ops dir) dir name))
  :rule-classes nil)

(defthm fn-bs-entry-outcomes-of-nil
  (equal (fn-bs-entry-outcomes nil old) (list old)))

; A name none of the directory's pending operations touches keeps its durable
; value across every admissible crash.
(defthm fn-bs-crash-keeps-untouched-entry
  (implies (and (fn-bs-dir-idp dir) (fn-bs-namep name)
                (fn-bs-crash-imagep s image)
                (equal (fn-bs-ops-for-name (fn-bs-ops-for-dir (fn-bs-pending s) dir)
                                           dir name)
                       nil))
           (equal (fn-bs-durable-entry image dir name)
                  (fn-bs-durable-entry s dir name)))
  :hints (("Goal"
           :use ((:instance fn-bs-crash-entry-is-old-or-a-pending-target)
                 (:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending s))))
           :in-theory (disable fn-bs-crash-entry-is-old-or-a-pending-target
                               fn-bs-ops-for-name fn-bs-ops-for-dir))))

; The fenced-inode list vocabulary the relation's authority clause needs.
(defthm fn-bs-all-fencedp-of-append
  (equal (fn-bs-all-fencedp bs (append a b))
         (and (fn-bs-all-fencedp bs a) (fn-bs-all-fencedp bs b))))
(defthm fn-bs-all-fencedp-member
  (implies (and (fn-bs-all-fencedp bs inos) (member-equal ino inos))
           (fn-bs-fencedp bs ino)))
(defthm fn-bs-assoc-value-is-in-strip-cdrs
  (implies (assoc-equal k alist)
           (member-equal (cdr (assoc-equal k alist)) (strip-cdrs alist))))
; ALISTP is load-bearing, not decoration: without it (STRIP-CARS '(NIL)) is
; (NIL), NAME = NIL is a member of it, and (ASSOC-EQUAL NIL '(NIL)) is NIL --
; the same shape of falsehood fn-cpp-find-of-append had.  Every entry alist
; this book applies it to is an alist by fn-bs-alistp-of-dir-entries.
(defthm fn-bs-assoc-of-name-in-entries
  (implies (and (alistp alist) (member-equal name (strip-cars alist)))
           (assoc-equal name alist)))

; -----------------------------------------------------------------------------
; 6. The record list of a prefix of the transaction namespace.

(defun fn-bs-txn-prefix-agreesp (a b n count)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nfix (- (nfix count) (nfix n)))))
  (if (or (not (natp n)) (not (natp count)) (>= n count))
      t
    (and (equal (fn-bs-lookup a :transactions (fn-bs-txn-name n))
                (fn-bs-lookup b :transactions (fn-bs-txn-name n)))
         (equal (fn-bs-content a (fn-bs-lookup a :transactions (fn-bs-txn-name n)))
                (fn-bs-content b (fn-bs-lookup b :transactions (fn-bs-txn-name n))))
         (fn-bs-txn-prefix-agreesp a b (1+ n) count))))

; The composition step: the scan reads a name and a content at each index and
; nothing else, so two images that agree at every index of a range read the
; same records there.  fn-record-p and fn-frame-store-decode stay closed.
(defthm fn-bs-read-records-under-agreement
  (implies (fn-bs-txn-prefix-agreesp a b n count)
           (equal (fn-bs-read-records a n count)
                  (fn-bs-read-records b n count)))
  :hints (("Goal" :induct (fn-bs-txn-prefix-agreesp a b n count)
           ; fn-bs-record-of is OPEN here, and only here: it opens to
           ; fn-bs-record-of-octets of the content, which the agreement
           ; hypothesis then makes the same term on both sides.  The decoder
           ; itself stays closed.
           :in-theory (e/d (fn-bs-record-of)
                           (fn-bs-lookup fn-bs-content fn-bs-record-of-octets)))))

(defthm fn-bs-read-records-len
  (implies (and (natp n) (natp count)
                (not (equal (fn-bs-read-records s n count) :fault)))
           (equal (len (fn-bs-read-records s n count)) (nfix (- count n))))
  :hints (("Goal" :in-theory (disable fn-bs-lookup fn-bs-content fn-bs-record-of))))

(defthm fn-bs-read-records-is-a-true-list
  (implies (not (equal (fn-bs-read-records s n count) :fault))
           (true-listp (fn-bs-read-records s n count)))
  :hints (("Goal" :in-theory (disable fn-bs-lookup fn-bs-content fn-bs-record-of))))

; Reading one more name appends one more record.
(defthm fn-bs-read-records-of-one-more
  (implies (and (natp n) (natp count) (<= n count)
                (not (equal (fn-bs-read-records s n count) :fault))
                (not (equal (fn-bs-read-records s count (1+ count)) :fault)))
           (equal (fn-bs-read-records s n (1+ count))
                  (append (fn-bs-read-records s n count)
                          (fn-bs-read-records s count (1+ count)))))
  :hints (("Goal" :induct (fn-bs-read-records s n count)
           :in-theory (disable fn-bs-lookup fn-bs-content fn-bs-record-of))))

(defthm fn-bs-txn-names-length
  (equal (len (fn-bs-txn-names n)) (nfix n)))

; -----------------------------------------------------------------------------
; 7. The transaction namespace of a crash image.

; No :in-theory disabling fn-bs-txn-name: it is a CONSTRAINED function, so
; there is no definition rule of that name and a theory expression naming it
; is a hard error under certify-book.  It is already closed; what does the
; work is the injectivity constraint.
(defthm fn-bs-txn-name-not-in-txn-names
  (implies (and (natp i) (natp n) (<= n i))
           (not (member-equal (fn-bs-txn-name i) (fn-bs-txn-names n)))))

(defthm fn-bs-txn-names-of-1+
  (implies (natp n)
           (equal (fn-bs-txn-names (1+ n))
                  (append (fn-bs-txn-names n) (list (fn-bs-txn-name n))))))

; The namespace half of K1.  One directory's name list after a crash is that
; directory's own operations applied to its durable name list -- the bridge
; of section 2 at the selected operation list.
(defthm fn-bs-crash-names-is-names-after
  (implies (and dir (fn-bs-statep s)
                (fn-bs-crash-choicesp choices (fn-bs-pending s) (fn-bs-unit s)))
           (equal (fn-bs-durable-names (fn-bs-crash s choices) dir)
                  (fn-bs-names-after
                   (fn-bs-crash-select (fn-bs-pending s) choices (fn-bs-unit s))
                   (fn-bs-durable-names s dir) dir)))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash)
                                  (fn-bs-apply-entries-names-is-names-after))
           :use ((:instance fn-bs-apply-entries-names-is-names-after
                            (dirs (fn-bs-dirs s))
                            (ops (fn-bs-crash-select (fn-bs-pending s) choices
                                                     (fn-bs-unit s))))))))

; And therefore it is one of the outcomes that directory's pending operations
; enumerate, for every admissible image.
(defthm fn-bs-crash-image-names-are-an-outcome
  (implies (and dir (fn-bs-statep s) (fn-bs-crash-imagep s image))
           (member-equal (fn-bs-durable-names image dir)
                         (fn-bs-names-outcomes
                          (fn-bs-ops-for-dir (fn-bs-pending s) dir)
                          (fn-bs-durable-names s dir))))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash-imagep)
                                  (fn-bs-crash-select-names-are-an-outcome
                                   fn-bs-crash-names-is-names-after))
           :use ((:instance fn-bs-crash-select-names-are-an-outcome
                            (ops (fn-bs-pending s))
                            (choices (fn-bs-crash-imagep-witness s image))
                            (unit (fn-bs-unit s))
                            (old (fn-bs-durable-names s dir)))
                 (:instance fn-bs-crash-names-is-names-after
                            (choices (fn-bs-crash-imagep-witness s image)))))))
;
; The K1 namespace clause: a crash image of a related state holds exactly the
; durable transaction namespace, or that namespace with the one pending link's
; name appended -- never anything else, and never a gap.
(defthm fn-bs-crash-image-transaction-names
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (let ((m (len (fn-bs-durable-names bs :transactions))))
             (or (equal (fn-bs-names image :transactions) (fn-bs-txn-names m))
                 (equal (fn-bs-names image :transactions)
                        (fn-bs-txn-names (1+ m))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-crash-image-names-are-an-outcome
                            (s bs) (dir :transactions))
                 (:instance fn-bs-txn-name-not-in-txn-names
                            (i (len (fn-bs-durable-names bs :transactions)))
                            (n (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-txn-names-of-1+
                            (n (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-crash-image-is-quiet (s bs))
                 (:instance fn-bs-quiet-names-are-durable-names
                            (s image) (dir :transactions)))
           ; fn-bs-names and fn-bs-durable-names both stay CLOSED: the only
           ; thing that connects them is the image's quietness, and with
           ; either one open they are two unrelated alist reads.
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-shape-okp
                            fn-bs-replay-matches-scan fn-bs-pending-matches-phase
                            fn-bs-contiguous-namesp)
                           (fn-bs-crash-image-names-are-an-outcome
                            fn-bs-txn-name-not-in-txn-names
                            fn-bs-txn-names-of-1+
                            fn-bs-txn-names fn-bs-names fn-bs-durable-names
                            fn-bs-read-records fn-bs-record-of
                            fn-bs-scan-store fn-sf-crash-imagep)))))

; K1, K2, K3 and K4 are CLOSED as of 2026-09-21 (lane w11/k1-scan).  K1 and
; K2 are sections 8 to 10 below; K3 and K4 are books/byte-store-keystones.lisp,
; which sits at the seam where the host reopen entry lives.  K1 is the four
; scan clauses: the config entry and content, the frontier entry and its
; decode, contiguity, and no :fault; the namespace clause above is the third
; and w9/storage-3 closed it.  D14-a and D14-b stand unchanged, and both of
; D14-c's rollback arms are LIVE in K2's proof rather than decoration -- a
; crash that loses the pending link lands in the record arm, one that loses
; the pending rename in the frontier arm.
;
; What is STILL open in this cluster is K0 (fn-bs-program-step-preserves-
; relation), which is what discharges the relation's own clauses on the
; host's programs -- including the two D14-c added to fn-bs-replay-matches-
; scan, that the durable frontier is the scanned one minus one under a
; pending :root operation and that at most one authority directory has a
; pending entry operation in the window.  Those are obligations on K0, not
; theorems, and K2 assumes them through the relation.  K5 to K8 are open.

; -----------------------------------------------------------------------------
; 8. K1: the scan of a crash image of a related state never faults.
;
; The four clauses in fn-bs-scan-store's own order: the config entry and its
; content, the frontier entry and its decode, the transaction namespace
; (section 7, closed), and the record list.  Section 7's discipline holds
; throughout -- the projections stay CLOSED, because fn-bs-lookup and
; fn-bs-durable-entry are two unrelated alist reads once opened and what
; connects them is the image's quietness, which is a rewrite over the closed
; terms.

(local (in-theory (disable fn-bs-view fn-bs-lookup fn-bs-content fn-bs-names
                           fn-bs-durable-content fn-bs-durable-entry
                           fn-bs-durable-names fn-bs-record-of
                           fn-bs-read-records fn-bs-scan-store)))

; 8.1 Namespace and alist vocabulary.

; The other way round from section 7's fn-bs-txn-name-not-in-txn-names: every
; EARLIER name is in the namespace, which is what puts each durable
; transaction inode in the relation's authority list.
(defthm fn-bs-txn-name-in-txn-names
  (implies (and (natp i) (natp n) (< i n))
           (member-equal (fn-bs-txn-name i) (fn-bs-txn-names n))))

; A name the alist does not hold reads NIL.  This is what makes the durable
; entry at the pending link's name NIL, and so what tells the two namespace
; outcomes of section 7 apart.
(local
 (defthm fn-bs-assoc-of-a-name-not-in-strip-cars
   (implies (not (member-equal name (strip-cars alist)))
            (equal (assoc-equal name alist) nil))))

; And the converse for the value: fn-bs-entry-valuep is natp or keywordp and
; NIL is neither, so a name the namespace DOES hold reads a non-NIL value.
; Without this the image whose namespace grew by the link's name could still
; read NIL there, and clause 4 would be false for a reason no crash produces.
(local
 (defthm fn-bs-entriesp-value-of-a-present-name-is-not-nil
   (implies (and (fn-bs-entriesp x) (member-equal name (strip-cars x)))
            (not (equal (cdr (assoc-equal name x)) nil)))))

; One entry's value depends only on that name's operations, and one
; directory's name list only on that directory's.  Both right sides match
; their own left sides, so both are cited and never left to match -- section
; 5's fn-bs-ops-for-name-through-ops-for-dir is the third of the family.
(defthm fn-bs-entry-after-through-ops-for-name
  (equal (fn-bs-entry-after ops old dir name)
         (fn-bs-entry-after (fn-bs-ops-for-name ops dir name) old dir name))
  :rule-classes nil)

(defthm fn-bs-names-after-through-ops-for-dir
  (equal (fn-bs-names-after ops old dir)
         (fn-bs-names-after (fn-bs-ops-for-dir ops dir) old dir))
  :rule-classes nil)

; 8.2 What the VIEW reads, from the pending list alone.
;
; fn-bs-entry-after joins the closed projections here, for section 5's
; reason: opened, it recurses on a variable pending list in every branch,
; and the two sides of every equality below become unrelated alist reads.

(local (in-theory (disable fn-bs-entry-after)))

(local
 (defthm fn-bs-ops-for-name-is-a-true-list
   (true-listp (fn-bs-ops-for-name ops dir name))))

(local
 (defthm fn-bs-ops-for-dir-is-a-true-list
   (true-listp (fn-bs-ops-for-dir ops dir))))

; The filter's head matches the filter, which is what lets a "there is
; exactly one operation at this name" hypothesis be USED rather than
; re-derived at each of the three places it is needed.
(local
 (defthm fn-bs-ops-for-name-head-matches
   (implies (consp (fn-bs-ops-for-name ops dir name))
            (and (equal (nth 1 (car (fn-bs-ops-for-name ops dir name))) dir)
                 (equal (nth 2 (car (fn-bs-ops-for-name ops dir name))) name)))))

(local
 (defthm fn-bs-entry-after-of-nil
   (equal (fn-bs-entry-after nil old dir name) old)
   :hints (("Goal" :in-theory (enable fn-bs-entry-after)))))

(local
 (defthm fn-bs-ops-for-dir-head-matches
   (implies (consp (fn-bs-ops-for-dir ops dir))
            (equal (nth 1 (car (fn-bs-ops-for-dir ops dir))) dir))))

; A name no pending operation touches reads its durable value in the VIEW,
; exactly as fn-bs-crash-keeps-untouched-entry says it does in every crash
; image.
(defthm fn-bs-lookup-of-an-untouched-name
  (implies (and dir name
                (equal (fn-bs-ops-for-name (fn-bs-pending s) dir name) nil))
           (equal (fn-bs-lookup s dir name) (fn-bs-durable-entry s dir name)))
  :hints (("Goal"
           :use ((:instance fn-bs-entry-after-through-ops-for-name
                            (ops (fn-bs-pending s))
                            (old (fn-bs-durable-entry s dir name))))
           :in-theory (enable fn-bs-lookup fn-bs-view fn-bs-durable-entry))))

; And a name with exactly one pending :set-entry reads that entry's target.
(defthm fn-bs-lookup-of-a-pending-target
  (implies (and dir name
                (consp (fn-bs-ops-for-name (fn-bs-pending s) dir name))
                (not (consp (cdr (fn-bs-ops-for-name (fn-bs-pending s) dir name))))
                (equal (car (car (fn-bs-ops-for-name (fn-bs-pending s) dir name)))
                       :set-entry))
           (equal (fn-bs-lookup s dir name)
                  (nth 3 (car (fn-bs-ops-for-name (fn-bs-pending s) dir name)))))
  :hints (("Goal"
           :use ((:instance fn-bs-entry-after-through-ops-for-name
                            (ops (fn-bs-pending s))
                            (old (fn-bs-durable-entry s dir name))))
           :in-theory (e/d (fn-bs-lookup fn-bs-view fn-bs-durable-entry
                            fn-bs-entry-after)
                           (fn-bs-ops-for-name)))))

; A fenced inode reads the same octets in the view as durably: fn-bs-fencedp
; is exactly "no pending write names it", and a write to another inode never
; lands in this one.
(defthm fn-bs-content-of-a-fenced-inode
  (implies (fn-bs-fencedp s ino)
           (equal (fn-bs-content s ino) (fn-bs-durable-content s ino)))
  :hints (("Goal" :in-theory (enable fn-bs-content fn-bs-view
                                     fn-bs-durable-content))))

; The view's name list of one directory, as section 2's projection.
(defthm fn-bs-names-is-names-after-the-pending-list
  (implies (and dir (fn-bs-dir-tablep (fn-bs-dirs s))
                (fn-bs-op-listp (fn-bs-pending s)))
           (equal (fn-bs-names s dir)
                  (fn-bs-names-after (fn-bs-pending s)
                                     (fn-bs-durable-names s dir) dir)))
  :hints (("Goal" :in-theory (enable fn-bs-names fn-bs-view
                                     fn-bs-durable-names))))

; 8.3 What the relation's shape clause says at each authority name.
;
; Three names matter, and the relation bounds the pending operations at each:
; the config name, which no pending operation ever touches; the frontier
; name, which at most the one pending :root rename touches; and
; (fn-bs-txn-name m) for m the size of the DURABLE transaction namespace,
; which at most the one pending link touches (D14-a).  fn-bs-fencedp joins
; the closed vocabulary here so the shape clause's fencing conjuncts arrive
; as the hypothesis fn-bs-crash-keeps-fenced-content wants.

(local (in-theory (disable fn-bs-fencedp)))

(defthm fn-bs-store-relation-implies-the-pending-shape
  (implies (fn-bs-store-relation bs ks) (fn-bs-pending-shape-okp bs))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-store-relation
                                   fn-bs-pending-matches-phase
                                   fn-bs-replay-matches-scan)
                                  (fn-bs-pending-shape-okp)))))

; The config name is touched by nothing: the one :root operation the shape
; clause allows is at the frontier name, and the two constants differ.
(defthm fn-bs-shape-leaves-the-config-name-quiet
  (implies (fn-bs-pending-shape-okp bs)
           (equal (fn-bs-ops-for-name (fn-bs-pending bs) :root
                                      *fn-bs-scan-config-name*)
                  nil))
  :hints (("Goal"
           :use ((:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending bs)) (dir :root)
                            (name *fn-bs-scan-config-name*)))
           :in-theory (enable fn-bs-pending-shape-okp))))

; At the frontier name and at the pending link's name the two filters
; COINCIDE: the shape clause bounds each directory's operations by its
; SPINE, so one operation at the directory is one operation at the name.
(defthm fn-bs-shape-at-the-frontier-name
  (implies (fn-bs-pending-shape-okp bs)
           (equal (fn-bs-ops-for-name (fn-bs-pending bs) :root
                                      *fn-bs-scan-frontier-name*)
                  (fn-bs-ops-for-dir (fn-bs-pending bs) :root)))
  :hints (("Goal"
           :use ((:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending bs)) (dir :root)
                            (name *fn-bs-scan-frontier-name*)))
           :in-theory (enable fn-bs-pending-shape-okp))))

(defthm fn-bs-shape-at-the-pending-link-name
  (implies (fn-bs-pending-shape-okp bs)
           (equal (fn-bs-ops-for-name
                   (fn-bs-pending bs) :transactions
                   (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions))))
                  (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
  :hints (("Goal"
           :use ((:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending bs)) (dir :transactions)
                            (name (fn-bs-txn-name
                                   (len (fn-bs-durable-names bs :transactions))))))
           :in-theory (enable fn-bs-pending-shape-okp))))

; And every EARLIER transaction name is quiet, by the injectivity constraint
; on the name seam.
(defthm fn-bs-shape-leaves-earlier-transaction-names-quiet
  (implies (and (fn-bs-pending-shape-okp bs) (natp i)
                (< i (len (fn-bs-durable-names bs :transactions))))
           (equal (fn-bs-ops-for-name (fn-bs-pending bs) :transactions
                                      (fn-bs-txn-name i))
                  nil))
  :hints (("Goal"
           :use ((:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending bs)) (dir :transactions)
                            (name (fn-bs-txn-name i)))
                 (:instance fn-bs-txn-name-is-injective
                            (i (len (fn-bs-durable-names bs :transactions)))
                            (j i)))
           :in-theory (e/d (fn-bs-pending-shape-okp)
                           (fn-bs-txn-name-is-injective)))))

; A name outside a directory's namespace reads NIL, and a name inside it
; does not.
(local
 (defthm fn-bs-durable-entry-outside-the-namespace-is-nil
   (implies (not (member-equal name (fn-bs-durable-names bs dir)))
            (equal (fn-bs-durable-entry bs dir name) nil))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry fn-bs-durable-names)))))

(local
 (defthm fn-bs-durable-entry-inside-the-namespace-is-not-nil
   (implies (and (fn-bs-dir-tablep (fn-bs-dirs bs))
                 (member-equal name (fn-bs-durable-names bs dir)))
            (not (equal (fn-bs-durable-entry bs dir name) nil)))
   :hints (("Goal"
            :use ((:instance fn-bs-entriesp-value-of-a-present-name-is-not-nil
                             (x (cdr (assoc-equal dir (fn-bs-dirs bs))))))
            :in-theory (enable fn-bs-durable-entry fn-bs-durable-names)))))

; 8.4 The relation and the scan, each read once.
;
; Both of these restate a definition under a hypothesis and neither is a
; proof event; they are named for what they are (docs/proof-style.md, and
; the assurance rule "cite keystones, never corollaries").  They exist so
; that the clause proofs below cite one fact each instead of opening a
; whole-state recognizer, which is the most expensive mistake available in
; this cluster.

(defthm fn-bs-store-relation-unfolds
  (implies (fn-bs-store-relation bs ks)
           (and (fn-bs-statep bs)
                (fn-sf-statep ks)
                (fn-bs-inop (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
                (fn-bs-config-okp
                 (fn-bs-durable-content
                  bs (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)))
                (fn-bs-inop (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))
                (equal (fn-bs-durable-names bs :transactions)
                       (fn-bs-txn-names
                        (len (fn-bs-durable-names bs :transactions))))
                (not (equal (fn-bs-durable-records bs) :fault))
                (fn-bs-authority-fencedp bs)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-store-relation fn-bs-contiguous-namesp)
                                  (fn-bs-statep fn-sf-statep
                                   fn-bs-authority-fencedp
                                   fn-bs-durable-records
                                   fn-bs-replay-matches-scan
                                   fn-bs-pending-matches-phase
                                   fn-sf-crash-imagep)))))

(defthm fn-bs-scan-okp-unfolds
  (implies (fn-bs-scan-okp (fn-bs-scan-store s))
           (and (fn-bs-inop (fn-bs-lookup s :root *fn-bs-scan-config-name*))
                (fn-bs-inop (fn-bs-lookup s :root *fn-bs-scan-frontier-name*))
                (natp (fn-bs-frontier-decode
                       (fn-bs-content s (fn-bs-lookup s :root
                                                      *fn-bs-scan-frontier-name*))))
                (equal (fn-bs-names s :transactions)
                       (fn-bs-txn-names (len (fn-bs-names s :transactions))))
                (not (equal (fn-bs-read-records s 0 (len (fn-bs-names s :transactions)))
                            :fault))
                (equal (fn-bs-scan-frontier (fn-bs-scan-store s))
                       (fn-bs-frontier-decode
                        (fn-bs-content s (fn-bs-lookup s :root
                                                       *fn-bs-scan-frontier-name*))))
                (equal (fn-bs-scan-records (fn-bs-scan-store s))
                       (fn-bs-read-records s 0 (len (fn-bs-names s :transactions))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-scan-store fn-bs-contiguous-namesp))))

; The relation's authority clause, at the three inode positions the scan
; reads.  fn-bs-all-fencedp distributes over the append that builds the
; list, so each is one membership away.
(defthm fn-bs-store-relation-fences-the-root-inodes
  (implies (fn-bs-store-relation bs ks)
           (and (fn-bs-fencedp bs (fn-bs-durable-entry bs :root
                                                       *fn-bs-scan-config-name*))
                (fn-bs-fencedp bs (fn-bs-durable-entry bs :root
                                                       *fn-bs-scan-frontier-name*))))
  :rule-classes nil
  :hints (("Goal" :use (fn-bs-store-relation-unfolds)
           :in-theory (e/d (fn-bs-authority-fencedp fn-bs-authority-inode-list)
                           (fn-bs-store-relation)))))

(defthm fn-bs-store-relation-fences-the-transaction-inodes
  (implies (and (fn-bs-store-relation bs ks)
                (member-equal name (fn-bs-durable-names bs :transactions)))
           (fn-bs-fencedp bs (fn-bs-durable-entry bs :transactions name)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 (:instance fn-bs-all-fencedp-member
                            (inos (strip-cdrs
                                   (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                            (ino (fn-bs-durable-entry bs :transactions name)))
                 (:instance fn-bs-assoc-value-is-in-strip-cdrs
                            (k name)
                            (alist (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                 (:instance fn-bs-assoc-of-name-in-entries
                            (alist (cdr (assoc-equal :transactions (fn-bs-dirs bs))))))
           :in-theory (e/d (fn-bs-authority-fencedp fn-bs-authority-inode-list
                            fn-bs-durable-entry fn-bs-durable-names)
                           (fn-bs-store-relation fn-bs-all-fencedp-member
                            fn-bs-assoc-value-is-in-strip-cdrs
                            fn-bs-assoc-of-name-in-entries)))))

; The two crash facts of section 5, restated over fn-bs-ops-for-name of the
; whole pending list -- which is the form section 8.3 delivers.
(defthm fn-bs-crash-keeps-a-quiet-name
  (implies (and (fn-bs-dir-idp dir) (fn-bs-namep name)
                (fn-bs-crash-imagep s image)
                (equal (fn-bs-ops-for-name (fn-bs-pending s) dir name) nil))
           (equal (fn-bs-durable-entry image dir name)
                  (fn-bs-durable-entry s dir name)))
  :hints (("Goal"
           :use ((:instance fn-bs-crash-keeps-untouched-entry)
                 (:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending s))))
           :in-theory (disable fn-bs-crash-keeps-untouched-entry))))

(defthm fn-bs-crash-entry-is-the-durable-one-or-the-pending-target
  (implies (and (fn-bs-dir-idp dir) (fn-bs-namep name)
                (fn-bs-crash-imagep s image)
                (consp (fn-bs-ops-for-name (fn-bs-pending s) dir name))
                (not (consp (cdr (fn-bs-ops-for-name (fn-bs-pending s) dir name))))
                (equal (car (car (fn-bs-ops-for-name (fn-bs-pending s) dir name)))
                       :set-entry))
           (or (equal (fn-bs-durable-entry image dir name)
                      (fn-bs-durable-entry s dir name))
               (equal (fn-bs-durable-entry image dir name)
                      (nth 3 (car (fn-bs-ops-for-name (fn-bs-pending s) dir name))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-crash-entry-is-old-or-a-pending-target))
           :in-theory (disable fn-bs-crash-entry-is-old-or-a-pending-target))))

; What the kernel says about the two candidate values, which is what makes
; the frontier decode a natural and the pending link's record a record.
(defthm fn-bs-kernel-candidates-are-typed
  (implies (fn-sf-statep ks)
           (and (natp (fn-sf-frontier ks))
                (implies (fn-sf-frontier-new-visiblep ks)
                         (natp (fn-sf-frontier-candidate ks)))
                (implies (fn-sf-record-present-visiblep ks)
                         (and (fn-store-event-p (fn-sf-record-candidate ks))
                              (equal (fn-store-event-sequence (fn-sf-record-candidate ks))
                                     (len (fn-sf-records ks)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sf-statep fn-sf-phase-shapep
                                     fn-sf-record-phasep fn-sf-frontier-phasep
                                     fn-sf-completion-phasep
                                     fn-sf-record-present-visiblep
                                     fn-sf-frontier-new-visiblep
                                     fn-sf-candidatep))))

; 8.5 Clause 1: the config entry and its content.
;
; No pending operation names the config file at all -- the host writes it
; once, at initialize -- so the crash image reads the durable inode and, the
; inode being an authority inode and therefore fenced, the durable octets.
; fn-bs-config-okp is a function of those octets and nothing else.
(defthm fn-bs-crash-image-reads-the-config
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (and (equal (fn-bs-lookup image :root *fn-bs-scan-config-name*)
                       (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
                (equal (fn-bs-content image
                                      (fn-bs-lookup image :root
                                                    *fn-bs-scan-config-name*))
                       (fn-bs-durable-content
                        bs (fn-bs-durable-entry bs :root
                                                *fn-bs-scan-config-name*)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-fences-the-root-inodes
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-shape-leaves-the-config-name-quiet))
           :in-theory (e/d (fn-bs-inop fn-bs-dir-idp fn-bs-namep)
                           (fn-bs-store-relation fn-bs-pending-shape-okp
                            fn-bs-statep)))))

; 8.6 Clause 2: the frontier entry, and that it decodes to a natural.
;
; The frontier name is the ONE authority name a pending :root operation may
; sit at (the os.replace of advance_frontier, tools/run_store.py:1305), so a
; crash image reads either the durable inode or the rename's target -- and
; both are fenced authority inodes, so each reads its own durable octets.
(defthm fn-bs-crash-image-reads-a-frontier-inode
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (fn-bs-inop (fn-bs-lookup image :root *fn-bs-scan-frontier-name*)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-shape-at-the-frontier-name)
                 (:instance fn-bs-crash-entry-is-the-durable-one-or-the-pending-target
                            (s bs) (dir :root) (name *fn-bs-scan-frontier-name*)))
           :in-theory (e/d (fn-bs-pending-shape-okp fn-bs-inop fn-bs-dir-idp
                            fn-bs-namep)
                           (fn-bs-store-relation fn-bs-statep)))))


; The relation's window clause, read once.  Below this point
; fn-bs-store-relation is never opened again: each clause cites this and
; enables at most the one window it is about, which is what keeps a
; whole-state recognizer out of every goal that follows.
(defthm fn-bs-store-relation-window-unfolds
  (implies (fn-bs-store-relation bs ks)
           (if (fn-bs-replay-visiblep ks)
               (fn-bs-replay-matches-scan bs ks)
             (and (fn-sf-crash-imagep ks (fn-bs-durable-frontier bs)
                                      (fn-bs-durable-records bs))
                  (fn-bs-pending-matches-phase bs ks))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-store-relation)
                                  (fn-bs-statep fn-sf-statep
                                   fn-bs-durable-records fn-bs-durable-frontier
                                   fn-bs-authority-fencedp
                                   fn-bs-replay-matches-scan
                                   fn-bs-pending-matches-phase
                                   fn-bs-replay-visiblep
                                   fn-bs-contiguous-namesp fn-bs-txn-names
                                   fn-sf-crash-imagep)))))

(defthm fn-bs-replay-matches-scan-unfolds
  (implies (fn-bs-replay-matches-scan bs ks)
           (and (fn-bs-pending-shape-okp bs)
                (fn-bs-scan-okp (fn-bs-scan-store bs))
                (equal (fn-sf-frontier ks)
                       (fn-bs-scan-frontier (fn-bs-scan-store bs)))
                (equal (fn-sf-records ks)
                       (fn-bs-scan-records (fn-bs-scan-store bs)))
                (equal (fn-sf-successes ks) nil)
                (implies (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                         (and (not (consp (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                             :transactions)))
                              (fn-sf-frontier-rollback-visiblep ks)
                              (equal (fn-bs-durable-frontier bs)
                                     (1- (fn-sf-frontier ks)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-replay-matches-scan)
                                  (fn-bs-pending-shape-okp fn-bs-scan-store
                                   fn-bs-scan-okp fn-bs-scan-frontier
                                   fn-bs-scan-records fn-bs-durable-frontier
                                   fn-sf-frontier-rollback-visiblep)))))

(defthm fn-bs-pending-matches-phase-unfolds
  (implies (fn-bs-pending-matches-phase bs ks)
           (and (fn-bs-pending-shape-okp bs)
                (implies (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                         (and (fn-sf-frontier-new-visiblep ks)
                              (equal (fn-bs-frontier-decode
                                      (fn-bs-durable-content
                                       bs (nth 3 (car (fn-bs-ops-for-dir
                                                       (fn-bs-pending bs) :root)))))
                                     (fn-sf-frontier-candidate ks))))
                (implies (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                         (and (fn-sf-record-present-visiblep ks)
                              (equal (fn-bs-durable-records bs) (fn-sf-records ks))
                              (equal (fn-bs-record-of
                                      (fn-bs-durable bs)
                                      (nth 3 (car (fn-bs-ops-for-dir
                                                   (fn-bs-pending bs) :transactions))))
                                     (fn-sf-record-candidate ks))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-pending-matches-phase)
                                  (fn-bs-pending-shape-okp fn-bs-durable-records
                                   fn-bs-record-of fn-bs-durable
                                   fn-sf-frontier-new-visiblep
                                   fn-sf-record-present-visiblep)))))

; What the RUNNING process's frontier file holds: the rename's target while
; one is pending, the durable inode otherwise.  Both are fenced -- the
; target by the shape clause, the durable inode by the authority clause --
; so in both cases the view reads durable octets, which is what lets the
; recovery window's scan hypothesis speak about a durable value.
(defthm fn-bs-store-relation-view-frontier-content
  (implies (fn-bs-store-relation bs ks)
           (equal (fn-bs-content bs (fn-bs-lookup bs :root
                                                  *fn-bs-scan-frontier-name*))
                  (if (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                      (fn-bs-durable-content
                       bs (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs) :root))))
                    (fn-bs-durable-content
                     bs (fn-bs-durable-entry bs :root
                                             *fn-bs-scan-frontier-name*)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-fences-the-root-inodes
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-shape-at-the-frontier-name)
                 (:instance fn-bs-lookup-of-an-untouched-name
                            (s bs) (dir :root) (name *fn-bs-scan-frontier-name*))
                 (:instance fn-bs-lookup-of-a-pending-target
                            (s bs) (dir :root) (name *fn-bs-scan-frontier-name*)))
           :in-theory (e/d (fn-bs-pending-shape-okp fn-bs-dir-idp fn-bs-namep)
                           (fn-bs-store-relation fn-bs-statep
                            fn-bs-txn-names
                            fn-bs-shape-at-the-frontier-name
                            fn-bs-shape-leaves-the-config-name-quiet
                            fn-bs-shape-at-the-pending-link-name
                            fn-bs-shape-leaves-earlier-transaction-names-quiet
                            fn-bs-lookup-of-an-untouched-name
                            fn-bs-lookup-of-a-pending-target)))))

; Both values the frontier file may hold after a crash decode to naturals,
; which is the scan's second test.  Four cases, one per window and per
; "is a rename pending", each citing one window and nothing else.

; Publish window, durable value: the kernel admits the image the durable
; half already is, and an admissible image's frontier is a uint32.
(defthm fn-bs-publish-window-durable-frontier-is-a-natural
  (implies (and (fn-bs-store-relation bs ks) (not (fn-bs-replay-visiblep ks)))
           (natp (fn-bs-durable-frontier bs)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-window-unfolds
                 (:instance fn-sf-admissible-image-facts
                            (s ks) (frontier (fn-bs-durable-frontier bs))
                            (records (fn-bs-durable-records bs)) (pair nil)))
           :in-theory (e/d (fn-record-uint32p)
                           (fn-bs-store-relation fn-bs-statep fn-sf-statep
                            fn-bs-durable-frontier fn-bs-durable-records
                            fn-bs-replay-matches-scan fn-bs-pending-matches-phase
                            fn-sf-crash-imagep fn-sf-admissible-image-facts
                            fn-sf-record-listp fn-sf-record-has-pairp)))))

; Publish window, the rename's target: fn-bs-pending-matches-phase says it
; holds the kernel's frontier candidate, which fn-sf-phase-shapep types.
(defthm fn-bs-publish-window-pending-frontier-is-a-natural
  (implies (and (fn-bs-store-relation bs ks) (not (fn-bs-replay-visiblep ks))
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root)))
           (natp (fn-bs-frontier-decode
                  (fn-bs-durable-content
                   bs (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs) :root)))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-window-unfolds
                 fn-bs-store-relation-unfolds
                 fn-bs-pending-matches-phase-unfolds
                 fn-bs-kernel-candidates-are-typed)
           :in-theory (disable fn-bs-store-relation fn-bs-statep fn-sf-statep
                               fn-bs-txn-names fn-bs-durable-records
                               fn-bs-authority-fencedp fn-bs-durable-frontier
                               fn-bs-replay-matches-scan
                               fn-bs-pending-matches-phase
                               fn-sf-crash-imagep
                               fn-sf-frontier-new-visiblep))))

; Recovery window: THIS process's scan of the view succeeded, and the view's
; frontier file is whichever inode is live -- so the live value is a natural
; outright.  Under a pending rename the durable value is the scanned one
; minus one (advance_frontier writes old+1, tools/run_store.py:1281), a
; natural because K2f's gate carries (posp (fn-sf-frontier ks)).
(defthm fn-bs-recovery-window-frontier-values-are-naturals
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-replay-visiblep ks))
           (and (natp (fn-bs-durable-frontier bs))
                (implies (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                         (natp (fn-bs-frontier-decode
                                (fn-bs-durable-content
                                 bs (nth 3 (car (fn-bs-ops-for-dir
                                                 (fn-bs-pending bs) :root)))))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-window-unfolds
                 fn-bs-replay-matches-scan-unfolds
                 fn-bs-store-relation-view-frontier-content
                 (:instance fn-bs-scan-okp-unfolds (s bs))
                 (:instance fn-sf-frontier-rollback-visiblep-unfolds (s ks)))
           :in-theory (e/d (fn-bs-durable-frontier)
                           (fn-bs-store-relation fn-bs-statep fn-sf-statep
                            fn-bs-txn-names fn-bs-durable-records
                            fn-bs-authority-fencedp
                            fn-bs-replay-matches-scan
                            fn-bs-pending-matches-phase
                            fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-scan-frontier fn-bs-scan-records
                            fn-sf-crash-imagep
                            fn-sf-frontier-rollback-visiblep
                            fn-sf-frontier-rollback-visiblep-unfolds)))))

; The two together, which is what clause 2 cites.
(defthm fn-bs-store-relation-frontier-values-are-naturals
  (implies (fn-bs-store-relation bs ks)
           (and (natp (fn-bs-durable-frontier bs))
                (implies (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                         (natp (fn-bs-frontier-decode
                                (fn-bs-durable-content
                                 bs (nth 3 (car (fn-bs-ops-for-dir
                                                 (fn-bs-pending bs) :root)))))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-publish-window-durable-frontier-is-a-natural
                 fn-bs-publish-window-pending-frontier-is-a-natural
                 fn-bs-recovery-window-frontier-values-are-naturals)
           :in-theory (disable fn-bs-store-relation fn-bs-statep
                               fn-bs-durable-frontier fn-bs-replay-visiblep))))

; Clause 2, closed: whichever of the two inodes the crash image's frontier
; name points at, its octets are that inode's durable octets and they decode
; to a natural.
(defthm fn-bs-crash-image-frontier-decodes-to-a-natural
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (natp (fn-bs-frontier-decode
                  (fn-bs-content image
                                 (fn-bs-lookup image :root
                                               *fn-bs-scan-frontier-name*)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-fences-the-root-inodes
                 fn-bs-store-relation-implies-the-pending-shape
                 fn-bs-store-relation-frontier-values-are-naturals
                 (:instance fn-bs-shape-at-the-frontier-name)
                 (:instance fn-bs-crash-entry-is-the-durable-one-or-the-pending-target
                            (s bs) (dir :root) (name *fn-bs-scan-frontier-name*)))
           :in-theory (e/d (fn-bs-pending-shape-okp fn-bs-dir-idp fn-bs-namep
                            fn-bs-durable-frontier)
                           (fn-bs-store-relation fn-bs-statep fn-bs-txn-names
                            fn-bs-shape-at-the-frontier-name
                            fn-bs-shape-leaves-the-config-name-quiet
                            fn-bs-shape-at-the-pending-link-name
                            fn-bs-shape-leaves-earlier-transaction-names-quiet)))))

; 8.7 Clause 3: the namespace is contiguous.
;
; Section 7 proved the image's transaction namespace is the durable one or
; the durable one with the pending link's name appended.  Each is
; (fn-bs-txn-names k) at its own length, which is the scan's third test.
(defthm fn-bs-crash-image-namespace-is-contiguous
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (equal (fn-bs-names image :transactions)
                  (fn-bs-txn-names (len (fn-bs-names image :transactions)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-crash-image-transaction-names
                 (:instance fn-bs-txn-names-length
                            (n (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-txn-names-length
                            (n (1+ (len (fn-bs-durable-names bs :transactions))))))
           :in-theory (disable fn-bs-txn-names-length fn-bs-txn-names
                               fn-bs-store-relation fn-bs-statep))))

; 8.8 Clause 4: the record list of a crash image never faults.
;
; The route the handoff named: fn-bs-read-records-under-agreement against
; (fn-bs-durable bs) for the durable prefix, and one of two arguments for
; the pending link's record -- the kernel's candidate in the publish window,
; this process's own successful scan of the view in the recovery window.

; The durable state read as a store: quiet, and the same tables.
(local
 (defthm fn-bs-durable-entry-of-the-durable-state
   (equal (fn-bs-durable-entry (fn-bs-durable bs) dir name)
          (fn-bs-durable-entry bs dir name))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry)))))
(local
 (defthm fn-bs-durable-content-of-the-durable-state
   (equal (fn-bs-durable-content (fn-bs-durable bs) ino)
          (fn-bs-durable-content bs ino))
   :hints (("Goal" :in-theory (enable fn-bs-durable-content)))))
(local
 (defthm fn-bs-durable-names-of-the-durable-state
   (equal (fn-bs-durable-names (fn-bs-durable bs) dir)
          (fn-bs-durable-names bs dir))
   :hints (("Goal" :in-theory (enable fn-bs-durable-names)))))

; With the three bridges in hand fn-bs-durable joins the closed vocabulary:
; opened, it is (fn-bs-make ...) and every rewrite above stops matching --
; which is how the prefix induction below first failed.
(local (in-theory (disable fn-bs-durable)))

(defthm fn-bs-crash-imagep-preserves-statep
  (implies (and (fn-bs-statep s) (fn-bs-crash-imagep s image))
           (fn-bs-statep image))
  :hints (("Goal"
           :use ((:instance fn-bs-crash-preserves-statep
                            (choices (fn-bs-crash-imagep-witness s image))))
           :in-theory (e/d (fn-bs-crash-imagep)
                           (fn-bs-statep fn-bs-crash-preserves-statep)))))

; One earlier transaction name, read out of the crash image.  The hypotheses
; are the relation's, spelled without KS so that the induction below carries
; them; (fn-bs-crash-imagep bs image) comes first because it is what binds
; BS when the rule fires on a term that mentions only IMAGE.
(local
 (defthm fn-bs-crash-image-reads-a-durable-transaction-entry
   (implies (and (fn-bs-crash-imagep bs image) (fn-bs-statep bs)
                 (fn-bs-pending-shape-okp bs)
                 (equal (fn-bs-durable-names bs :transactions)
                        (fn-bs-txn-names
                         (len (fn-bs-durable-names bs :transactions))))
                 (natp i) (< i (len (fn-bs-durable-names bs :transactions))))
            (equal (fn-bs-lookup image :transactions (fn-bs-txn-name i))
                   (fn-bs-durable-entry bs :transactions (fn-bs-txn-name i))))
   :hints (("Goal"
            :use ((:instance fn-bs-shape-leaves-earlier-transaction-names-quiet)
                  (:instance fn-bs-crash-keeps-a-quiet-name
                             (s bs) (dir :transactions)
                             (name (fn-bs-txn-name i))))
            :in-theory (e/d (fn-bs-dir-idp fn-bs-namep)
                            (fn-bs-statep fn-bs-txn-names
                             fn-bs-pending-shape-okp
                             fn-bs-shape-leaves-earlier-transaction-names-quiet
                             fn-bs-crash-keeps-a-quiet-name))))))

; fn-bs-statep is CLOSED in every proof of this section, so the one fact
; the entry alists need from it is a rule of its own.
(local
 (defthm fn-bs-statep-dirs-are-a-table
   (implies (fn-bs-statep s) (fn-bs-dir-tablep (fn-bs-dirs s)))
   :hints (("Goal" :in-theory (enable fn-bs-statep)))))

(local
 (defthm fn-bs-crash-image-reads-a-durable-transaction-content
   (implies (and (fn-bs-crash-imagep bs image) (fn-bs-statep bs)
                 (fn-bs-all-fencedp
                  bs (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                 (equal (fn-bs-durable-names bs :transactions)
                        (fn-bs-txn-names
                         (len (fn-bs-durable-names bs :transactions))))
                 (natp i) (< i (len (fn-bs-durable-names bs :transactions))))
            (equal (fn-bs-content
                    image (fn-bs-durable-entry bs :transactions (fn-bs-txn-name i)))
                   (fn-bs-durable-content
                    bs (fn-bs-durable-entry bs :transactions (fn-bs-txn-name i)))))
   :hints (("Goal"
            :use ((:instance fn-bs-txn-name-in-txn-names
                             (n (len (fn-bs-durable-names bs :transactions))))
                  (:instance fn-bs-all-fencedp-member
                             (inos (strip-cdrs
                                    (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                             (ino (fn-bs-durable-entry bs :transactions
                                                       (fn-bs-txn-name i))))
                  (:instance fn-bs-assoc-value-is-in-strip-cdrs
                             (k (fn-bs-txn-name i))
                             (alist (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                  (:instance fn-bs-assoc-of-name-in-entries
                             (name (fn-bs-txn-name i))
                             (alist (cdr (assoc-equal :transactions (fn-bs-dirs bs))))))
            :in-theory (e/d (fn-bs-durable-entry fn-bs-durable-names)
                            (fn-bs-statep fn-bs-txn-names
                             fn-bs-txn-name-in-txn-names
                             fn-bs-all-fencedp-member
                             fn-bs-assoc-value-is-in-strip-cdrs
                             fn-bs-assoc-of-name-in-entries))))))

; And therefore the whole durable prefix agrees, which is what
; fn-bs-read-records-under-agreement consumes.
(local
 (defthm fn-bs-crash-image-agrees-with-the-durable-prefix
   (implies (and (fn-bs-crash-imagep bs image) (fn-bs-statep bs)
                 (fn-bs-pending-shape-okp bs)
                 (fn-bs-all-fencedp
                  bs (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                 (equal (fn-bs-durable-names bs :transactions)
                        (fn-bs-txn-names
                         (len (fn-bs-durable-names bs :transactions))))
                 (natp n))
            (fn-bs-txn-prefix-agreesp
             image (fn-bs-durable bs) n
             (len (fn-bs-durable-names bs :transactions))))
   :hints (("Goal"
            :induct (fn-bs-txn-prefix-agreesp
                     image (fn-bs-durable bs) n
                     (len (fn-bs-durable-names bs :transactions)))
            :in-theory (disable fn-bs-statep fn-bs-txn-names
                                fn-bs-pending-shape-okp)))))

(defthm fn-bs-crash-image-reads-the-durable-records
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (equal (fn-bs-read-records
                   image 0 (len (fn-bs-durable-names bs :transactions)))
                  (fn-bs-durable-records bs)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-read-records-under-agreement
                            (a image) (b (fn-bs-durable bs)) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-authority-fencedp
                            fn-bs-authority-inode-list)
                           (fn-bs-store-relation fn-bs-statep fn-bs-txn-names
                            fn-bs-pending-shape-okp
                            fn-bs-read-records-under-agreement)))))

; The namespace grows only where a link is pending, so a crash image with
; more names than the durable state has exactly one more and it is the
; link's.
(defthm fn-bs-crash-image-namespace-grows-only-with-a-pending-link
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (not (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))))
           (equal (fn-bs-names image :transactions)
                  (fn-bs-durable-names bs :transactions)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 (:instance fn-bs-crash-image-names-are-an-outcome
                            (s bs) (dir :transactions))
                 (:instance fn-bs-crash-image-is-quiet (s bs))
                 (:instance fn-bs-quiet-names-are-durable-names
                            (s image) (dir :transactions))
                 (:instance fn-bs-names-outcomes-of-no-ops
                            (ops (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                            (old (fn-bs-durable-names bs :transactions))))
           :in-theory (disable fn-bs-store-relation fn-bs-statep fn-bs-txn-names
                               fn-bs-crash-image-names-are-an-outcome
                               fn-bs-crash-image-is-quiet
                               fn-bs-quiet-names-are-durable-names
                               fn-bs-names-outcomes fn-bs-names-outcomes-of-no-ops))))

; And when the image DOES hold the link's name, the inode under it is the
; link's target: the durable namespace does not hold that name, so the only
; other outcome is NIL, and a well-formed entry alist holds no NIL value.
(defthm fn-bs-crash-image-that-kept-the-link-reads-its-target
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                (member-equal
                 (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions)))
                 (fn-bs-names image :transactions)))
           (equal (fn-bs-lookup
                   image :transactions
                   (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions))))
                  (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                 :transactions)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-shape-at-the-pending-link-name)
                 (:instance fn-bs-crash-entry-is-the-durable-one-or-the-pending-target
                            (s bs) (dir :transactions)
                            (name (fn-bs-txn-name
                                   (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-txn-name-not-in-txn-names
                            (i (len (fn-bs-durable-names bs :transactions)))
                            (n (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-crash-imagep-preserves-statep (s bs))
                 (:instance fn-bs-crash-image-is-quiet (s bs))
                 (:instance fn-bs-quiet-names-are-durable-names
                            (s image) (dir :transactions))
                 (:instance fn-bs-durable-entry-inside-the-namespace-is-not-nil
                            (bs image) (dir :transactions)
                            (name (fn-bs-txn-name
                                   (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-durable-entry-outside-the-namespace-is-nil
                            (dir :transactions)
                            (name (fn-bs-txn-name
                                   (len (fn-bs-durable-names bs :transactions))))))
           :in-theory (e/d (fn-bs-pending-shape-okp fn-bs-dir-idp fn-bs-namep)
                           (fn-bs-store-relation fn-bs-statep fn-bs-txn-names
                            fn-bs-shape-at-the-frontier-name
                            fn-bs-shape-leaves-the-config-name-quiet
                            fn-bs-shape-at-the-pending-link-name
                            fn-bs-shape-leaves-earlier-transaction-names-quiet
                            fn-bs-crash-imagep-preserves-statep
                            fn-bs-crash-image-is-quiet
                            fn-bs-quiet-names-are-durable-names
                            fn-bs-durable-entry-inside-the-namespace-is-not-nil
                            fn-bs-durable-entry-outside-the-namespace-is-nil
                            fn-bs-txn-name-not-in-txn-names)))))

; The durable record list has one record per durable transaction name.
(defthm fn-bs-durable-records-length
  (implies (fn-bs-store-relation bs ks)
           (equal (len (fn-bs-durable-records bs))
                  (len (fn-bs-durable-names bs :transactions))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 (:instance fn-bs-read-records-len
                            (s (fn-bs-durable bs)) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (e/d (fn-bs-durable-records)
                           (fn-bs-store-relation fn-bs-statep fn-bs-txn-names
                            fn-bs-read-records fn-bs-read-records-len)))))

; Publish window, the pending link's record, in two steps -- the octets
; first, then the scan's one-name read of them.  Split because with
; fn-bs-read-records open in the same goal as the relation the rewriter
; reached its call-depth limit of 1000 rather than a checkpoint.
;
; The octets under the link's target are the data-durable candidate (D1:
; the link is issued after the inode's fence, so a crash cannot tear it),
; the kernel types the candidate, and its sequence is the size of the
; durable record list -- which is the durable namespace's size, which is
; the index the scan reads it at.
(defthm fn-bs-publish-window-crash-image-reads-the-candidate-octets
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (not (fn-bs-replay-visiblep ks))
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
           (and (fn-bs-inop (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                           :transactions))))
                (equal (fn-bs-record-of
                        image (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                             :transactions))))
                       (fn-sf-record-candidate ks))
                (fn-store-event-p (fn-sf-record-candidate ks))
                (equal (fn-store-event-sequence (fn-sf-record-candidate ks))
                       (len (fn-bs-durable-names bs :transactions)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-window-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 fn-bs-pending-matches-phase-unfolds
                 fn-bs-kernel-candidates-are-typed
                 fn-bs-durable-records-length
                 (:instance fn-bs-crash-image-is-quiet (s bs))
                 (:instance fn-bs-crash-keeps-fenced-content
                            (s bs)
                            (ino (nth 3 (car (fn-bs-ops-for-dir
                                              (fn-bs-pending bs) :transactions))))))
           ; fn-bs-authority-fencedp must stay CLOSED: opened,
           ; fn-bs-all-fencedp recurses on (fn-bs-pending-entry-targets
           ; (fn-bs-pending bs)), a variable list, and the rewriter hits its
           ; call-depth limit rather than a checkpoint.
           :in-theory (e/d (fn-bs-record-of fn-bs-pending-shape-okp)
                           (fn-bs-store-relation fn-bs-statep fn-sf-statep
                            fn-bs-txn-names fn-bs-record-of-octets
                            fn-bs-durable-records fn-bs-durable-frontier
                            fn-bs-authority-fencedp fn-bs-authority-inode-list
                            fn-bs-all-fencedp fn-bs-read-records
                            fn-bs-replay-matches-scan fn-bs-pending-matches-phase
                            fn-sf-crash-imagep fn-sf-admissible-image-facts
                            fn-sf-record-present-visiblep
                            fn-bs-shape-at-the-frontier-name
                            fn-bs-shape-leaves-the-config-name-quiet
                            fn-bs-shape-at-the-pending-link-name
                            fn-bs-shape-leaves-earlier-transaction-names-quiet
                            fn-bs-crash-image-is-quiet
                            fn-bs-crash-keeps-fenced-content)))))

; fn-bs-read-records is never ENABLED below: on a symbolic index the
; rewriter unfolds it without bound and reaches its call-depth limit of
; 1000 rather than a checkpoint.  These two are its one-step opening and
; its empty range, each forced by :expand exactly once.
(local
 (defthm fn-bs-read-records-one-step
   (implies (and (natp n) (natp count) (< n count))
            (equal (fn-bs-read-records s n count)
                   (let* ((ino (fn-bs-lookup s :transactions (fn-bs-txn-name n)))
                          (record (and (fn-bs-inop ino) (fn-bs-record-of s ino)))
                          (rest (fn-bs-read-records s (1+ n) count)))
                     (if (or (not (fn-store-event-p record))
                             (not (equal (fn-store-event-sequence record) n))
                             (equal rest :fault))
                         :fault
                       (cons record rest)))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-bs-read-records s n count))))))

(local
 (defthm fn-bs-read-records-of-an-empty-range
   (implies (and (natp n) (natp count) (<= count n))
            (equal (fn-bs-read-records s n count) nil))
   :hints (("Goal" :expand ((fn-bs-read-records s n count))))))

(defthm fn-bs-publish-window-crash-image-reads-the-candidate
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (not (fn-bs-replay-visiblep ks))
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                (equal (fn-bs-lookup
                        image :transactions
                        (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions))))
                       (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                      :transactions)))))
           (not (equal (fn-bs-read-records
                        image (len (fn-bs-durable-names bs :transactions))
                        (1+ (len (fn-bs-durable-names bs :transactions))))
                       :fault)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-publish-window-crash-image-reads-the-candidate-octets
                 (:instance fn-bs-read-records-one-step
                            (s image)
                            (n (len (fn-bs-durable-names bs :transactions)))
                            (count (1+ (len (fn-bs-durable-names bs
                                                                 :transactions))))))
           :in-theory (disable fn-bs-store-relation fn-bs-statep fn-sf-statep
                               fn-bs-txn-names fn-bs-record-of
                               fn-bs-record-of-octets fn-bs-durable-records
                               fn-bs-durable-frontier fn-bs-authority-fencedp
                               fn-bs-authority-inode-list fn-bs-all-fencedp
                               fn-bs-pending-shape-okp fn-bs-replay-visiblep
                               fn-bs-replay-matches-scan
                               fn-bs-pending-matches-phase
                               fn-sf-crash-imagep fn-sf-admissible-image-facts
                               fn-bs-crash-imagep))))

; Recovery window.  There the pending link's record is not the kernel's
; candidate -- in :replaying the kernel holds no candidate at all -- but
; THIS process already read it: fn-bs-replay-matches-scan says the scan of
; the VIEW succeeded, and the view holds the link.  So the image's read at
; that index is the view's read at that index.

(local
 (defthm fn-bs-statep-pending-is-an-op-list
   (implies (fn-bs-statep s) (fn-bs-op-listp (fn-bs-pending s)))
   :hints (("Goal" :in-theory (enable fn-bs-statep)))))

; A successful read of a range is a successful read of each of its tails.
(local
 (defthm fn-bs-read-records-tail-not-fault
   (implies (and (natp n) (natp count) (<= n count)
                 (not (equal (fn-bs-read-records s n (1+ count)) :fault)))
            (not (equal (fn-bs-read-records s count (1+ count)) :fault)))
   :hints (("Goal" :induct (fn-bs-read-records s n count)
            :in-theory (e/d (fn-bs-read-records)
                            (fn-bs-lookup fn-bs-content fn-bs-record-of))))))

; The view's transaction namespace under a pending link: the durable one
; with the link's name appended, so the scan reads exactly one more index.
(defthm fn-bs-store-relation-view-namespace-with-a-pending-link
  (implies (and (fn-bs-store-relation bs ks)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
           (equal (fn-bs-names bs :transactions)
                  (fn-bs-txn-names
                   (1+ (len (fn-bs-durable-names bs :transactions))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-names-is-names-after-the-pending-list
                            (s bs) (dir :transactions))
                 (:instance fn-bs-names-after-through-ops-for-dir
                            (ops (fn-bs-pending bs))
                            (old (fn-bs-durable-names bs :transactions))
                            (dir :transactions))
                 (:instance fn-bs-txn-name-not-in-txn-names
                            (i (len (fn-bs-durable-names bs :transactions)))
                            (n (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-txn-names-of-1+
                            (n (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (e/d (fn-bs-pending-shape-okp fn-bs-name-step)
                           (fn-bs-store-relation fn-bs-statep fn-bs-txn-names
                            fn-bs-names-is-names-after-the-pending-list
                            fn-bs-txn-names-of-1+ fn-bs-txn-name-not-in-txn-names
                            fn-bs-shape-at-the-frontier-name
                            fn-bs-shape-leaves-the-config-name-quiet
                            fn-bs-shape-at-the-pending-link-name
                            fn-bs-shape-leaves-earlier-transaction-names-quiet)))))

(local
 (defthm fn-bs-txn-prefix-agreesp-of-an-empty-range
   (implies (and (natp n) (natp count) (<= count n))
            (fn-bs-txn-prefix-agreesp a b n count))
   :hints (("Goal" :expand ((fn-bs-txn-prefix-agreesp a b n count))))))

; At the link's index the crash image and the view read the same inode and
; the same octets, the inode being fenced (D1).
(defthm fn-bs-crash-image-agrees-with-the-view-at-the-link
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                (equal (fn-bs-lookup
                        image :transactions
                        (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions))))
                       (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                      :transactions)))))
           (fn-bs-txn-prefix-agreesp
            image bs (len (fn-bs-durable-names bs :transactions))
            (1+ (len (fn-bs-durable-names bs :transactions)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-shape-at-the-pending-link-name)
                 (:instance fn-bs-lookup-of-a-pending-target
                            (s bs) (dir :transactions)
                            (name (fn-bs-txn-name
                                   (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-crash-image-is-quiet (s bs))
                 (:instance fn-bs-crash-keeps-fenced-content
                            (s bs)
                            (ino (nth 3 (car (fn-bs-ops-for-dir
                                              (fn-bs-pending bs) :transactions))))))
           :in-theory (e/d (fn-bs-pending-shape-okp fn-bs-dir-idp fn-bs-namep)
                           (fn-bs-store-relation fn-bs-statep fn-bs-txn-names
                            fn-bs-read-records fn-bs-record-of
                            fn-bs-durable-records fn-bs-durable-frontier
                            fn-bs-authority-fencedp fn-bs-authority-inode-list
                            fn-bs-all-fencedp
                            fn-bs-lookup-of-a-pending-target
                            fn-bs-crash-image-is-quiet
                            fn-bs-crash-keeps-fenced-content
                            fn-bs-shape-at-the-frontier-name
                            fn-bs-shape-leaves-the-config-name-quiet
                            fn-bs-shape-at-the-pending-link-name
                            fn-bs-shape-leaves-earlier-transaction-names-quiet)))))

(defthm fn-bs-recovery-window-crash-image-reads-the-scanned-record
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (fn-bs-replay-visiblep ks)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                (equal (fn-bs-lookup
                        image :transactions
                        (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions))))
                       (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                      :transactions)))))
           (not (equal (fn-bs-read-records
                        image (len (fn-bs-durable-names bs :transactions))
                        (1+ (len (fn-bs-durable-names bs :transactions))))
                       :fault)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-window-unfolds
                 fn-bs-replay-matches-scan-unfolds
                 fn-bs-store-relation-view-namespace-with-a-pending-link
                 fn-bs-crash-image-agrees-with-the-view-at-the-link
                 (:instance fn-bs-scan-okp-unfolds (s bs))
                 (:instance fn-bs-txn-names-length
                            (n (1+ (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-read-records-tail-not-fault
                            (s bs) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                            (a image) (b bs)
                            (n (len (fn-bs-durable-names bs :transactions)))
                            (count (1+ (len (fn-bs-durable-names bs
                                                                 :transactions))))))
           :in-theory (disable fn-bs-store-relation fn-bs-statep fn-sf-statep
                               fn-bs-txn-names fn-bs-txn-names-length
                               fn-bs-read-records fn-bs-record-of
                               fn-bs-durable-records fn-bs-durable-frontier
                               fn-bs-authority-fencedp fn-bs-authority-inode-list
                               fn-bs-all-fencedp fn-bs-pending-shape-okp
                               fn-bs-replay-visiblep fn-bs-replay-matches-scan
                               fn-bs-pending-matches-phase fn-bs-scan-store
                               fn-bs-scan-okp fn-bs-scan-frontier
                               fn-bs-scan-records fn-bs-txn-prefix-agreesp
                               fn-bs-read-records-under-agreement
                               fn-bs-read-records-tail-not-fault
                               fn-sf-crash-imagep fn-bs-crash-imagep))))

; The two windows together: whichever one the state is in, the image's read
; at the link's index succeeds.
(defthm fn-bs-crash-image-reads-the-linked-record
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                (equal (fn-bs-lookup
                        image :transactions
                        (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions))))
                       (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                      :transactions)))))
           (not (equal (fn-bs-read-records
                        image (len (fn-bs-durable-names bs :transactions))
                        (1+ (len (fn-bs-durable-names bs :transactions))))
                       :fault)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-publish-window-crash-image-reads-the-candidate
                 fn-bs-recovery-window-crash-image-reads-the-scanned-record)
           :in-theory (disable fn-bs-store-relation fn-bs-statep
                               fn-bs-read-records fn-bs-replay-visiblep
                               fn-bs-crash-imagep fn-bs-txn-names))))

(local
 (defthm fn-bs-append-of-a-non-fault-is-not-a-fault
   (implies (not (equal b :fault)) (not (equal (append a b) :fault)))))

; Clause 4, closed.  Either the image's namespace is the durable one, and
; its record list is the durable record list the relation already says is
; not a fault; or it is that namespace with the link's name, and the read
; is the durable list followed by the one record under the link's target.
(defthm fn-bs-crash-image-records-do-not-fault
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (not (equal (fn-bs-read-records
                        image 0 (len (fn-bs-names image :transactions)))
                       :fault)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-crash-image-transaction-names
                 fn-bs-crash-image-reads-the-durable-records
                 fn-bs-crash-image-reads-the-linked-record
                 fn-bs-crash-image-namespace-grows-only-with-a-pending-link
                 fn-bs-crash-image-that-kept-the-link-reads-its-target
                 (:instance fn-bs-txn-names-length
                            (n (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-txn-names-length
                            (n (1+ (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-txn-name-in-txn-names
                            (i (len (fn-bs-durable-names bs :transactions)))
                            (n (1+ (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-read-records-of-one-more
                            (s image) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (disable fn-bs-store-relation fn-bs-statep fn-sf-statep
                               fn-bs-txn-names fn-bs-txn-names-length
                               fn-bs-txn-name-in-txn-names
                               fn-bs-read-records fn-bs-read-records-of-one-more
                               fn-bs-record-of fn-bs-durable-records
                               fn-bs-durable-frontier fn-bs-authority-fencedp
                               fn-bs-authority-inode-list fn-bs-all-fencedp
                               fn-bs-pending-shape-okp fn-bs-replay-visiblep
                               fn-bs-replay-matches-scan
                               fn-bs-pending-matches-phase
                               fn-sf-crash-imagep fn-bs-crash-imagep))))

; -----------------------------------------------------------------------------
; 9. K1 (specs/crash-model-v2.md section 3.3).
;
; The scan of EVERY crash image of a related state succeeds: the config
; entry and its content, the frontier entry and its decode, a contiguous
; transaction namespace, and a record list with no fault.  No trailer
; assumption is used anywhere in it: no authority inode is ever torn,
; because a link or a rename is issued only after that inode's fence (D1)
; and an authority inode is never overwritten (D2), so the only freedom a
; crash has over the authority namespace is whether the last entry
; operation landed.
(defthm fn-bs-store-crash-image-scans
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (fn-bs-scan-okp (fn-bs-scan-store image)))
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-crash-image-reads-the-config
                 fn-bs-crash-image-reads-a-frontier-inode
                 fn-bs-crash-image-frontier-decodes-to-a-natural
                 fn-bs-crash-image-namespace-is-contiguous
                 fn-bs-crash-image-records-do-not-fault)
           :in-theory (e/d (fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-contiguous-namesp)
                           (fn-bs-store-relation fn-bs-statep fn-sf-statep
                            fn-bs-txn-names fn-bs-read-records fn-bs-record-of
                            fn-bs-durable-records fn-bs-durable-frontier
                            fn-bs-authority-fencedp fn-bs-authority-inode-list
                            fn-bs-all-fencedp fn-bs-pending-shape-okp
                            fn-bs-replay-visiblep fn-bs-replay-matches-scan
                            fn-bs-pending-matches-phase
                            fn-sf-crash-imagep fn-bs-crash-imagep)))))

; -----------------------------------------------------------------------------
; 10. K2 (specs/crash-model-v2.md section 3.3): what the scan reads is an
; image the kernel admits.
;
; The conclusion is fn-sf-recovery-crash-imagep, what the PLATFORM may
; leave (D14-b), and not fn-sf-crash-imagep, what a consumer may rely on:
; widening the reliance predicate is false for the composition and the
; counterexample is in tests/acl2/owner-tests.lisp.  K1 supplies the scan's
; success; what is left is to name, for each of the two windows and each
; of the two entry operations, which arm of the predicate the read lands in.

(local
 (defthm fn-bs-but-last-of-an-append-of-one
   (implies (true-listp xs)
            (equal (fn-sf-but-last (append xs (list y))) xs))))

(local
 (defthm fn-bs-durable-transaction-inode-is-fenced
   (implies (and (fn-bs-statep bs)
                 (fn-bs-all-fencedp
                  bs (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                 (equal (fn-bs-durable-names bs :transactions)
                        (fn-bs-txn-names
                         (len (fn-bs-durable-names bs :transactions))))
                 (natp i) (< i (len (fn-bs-durable-names bs :transactions))))
            (fn-bs-fencedp bs (fn-bs-durable-entry bs :transactions
                                                   (fn-bs-txn-name i))))
   :hints (("Goal"
            :use ((:instance fn-bs-txn-name-in-txn-names
                             (n (len (fn-bs-durable-names bs :transactions))))
                  (:instance fn-bs-all-fencedp-member
                             (inos (strip-cdrs
                                    (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                             (ino (fn-bs-durable-entry bs :transactions
                                                       (fn-bs-txn-name i))))
                  (:instance fn-bs-assoc-value-is-in-strip-cdrs
                             (k (fn-bs-txn-name i))
                             (alist (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                  (:instance fn-bs-assoc-of-name-in-entries
                             (name (fn-bs-txn-name i))
                             (alist (cdr (assoc-equal :transactions
                                                      (fn-bs-dirs bs))))))
            :in-theory (e/d (fn-bs-durable-entry fn-bs-durable-names)
                            (fn-bs-statep fn-bs-txn-names
                             fn-bs-txn-name-in-txn-names
                             fn-bs-all-fencedp-member
                             fn-bs-assoc-value-is-in-strip-cdrs
                             fn-bs-assoc-of-name-in-entries))))))

(local
 (defthm fn-bs-view-reads-a-durable-transaction-entry
   (implies (and (fn-bs-pending-shape-okp bs) (natp i)
                 (< i (len (fn-bs-durable-names bs :transactions))))
            (equal (fn-bs-lookup bs :transactions (fn-bs-txn-name i))
                   (fn-bs-durable-entry bs :transactions (fn-bs-txn-name i))))
   :hints (("Goal"
            :use ((:instance fn-bs-shape-leaves-earlier-transaction-names-quiet)
                  (:instance fn-bs-lookup-of-an-untouched-name
                             (s bs) (dir :transactions)
                             (name (fn-bs-txn-name i))))
            :in-theory (e/d (fn-bs-dir-idp fn-bs-namep)
                            (fn-bs-pending-shape-okp fn-bs-txn-names
                             fn-bs-shape-leaves-earlier-transaction-names-quiet
                             fn-bs-lookup-of-an-untouched-name))))))

(local
 (defthm fn-bs-view-agrees-with-the-durable-prefix
   (implies (and (fn-bs-statep bs) (fn-bs-pending-shape-okp bs)
                 (fn-bs-all-fencedp
                  bs (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                 (equal (fn-bs-durable-names bs :transactions)
                        (fn-bs-txn-names
                         (len (fn-bs-durable-names bs :transactions))))
                 (natp n))
            (fn-bs-txn-prefix-agreesp
             bs (fn-bs-durable bs) n
             (len (fn-bs-durable-names bs :transactions))))
   :hints (("Goal"
            :induct (fn-bs-txn-prefix-agreesp
                     bs (fn-bs-durable bs) n
                     (len (fn-bs-durable-names bs :transactions)))
            :in-theory (disable fn-bs-statep fn-bs-txn-names
                                fn-bs-pending-shape-okp)))))

; The running process reads the durable record list at the durable indices,
; for the same reason a crash image does: the one pending link is at a name
; outside them and every inode they name is fenced.
(defthm fn-bs-view-reads-the-durable-records
  (implies (fn-bs-store-relation bs ks)
           (equal (fn-bs-read-records
                   bs 0 (len (fn-bs-durable-names bs :transactions)))
                  (fn-bs-durable-records bs)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-read-records-under-agreement
                            (a bs) (b (fn-bs-durable bs)) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-view-agrees-with-the-durable-prefix (n 0)))
           :in-theory (e/d (fn-bs-durable-records)
                           (fn-bs-store-relation fn-bs-statep fn-bs-txn-names
                            fn-bs-read-records fn-bs-pending-shape-okp
                            fn-bs-read-records-under-agreement)))))

; The view's namespace without a pending link is the durable one.
(defthm fn-bs-store-relation-view-namespace-without-a-pending-link
  (implies (and (fn-bs-store-relation bs ks)
                (not (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))))
           (equal (fn-bs-names bs :transactions)
                  (fn-bs-durable-names bs :transactions)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 (:instance fn-bs-names-is-names-after-the-pending-list
                            (s bs) (dir :transactions))
                 (:instance fn-bs-names-after-through-ops-for-dir
                            (ops (fn-bs-pending bs))
                            (old (fn-bs-durable-names bs :transactions))
                            (dir :transactions)))
           :in-theory (disable fn-bs-store-relation fn-bs-statep fn-bs-txn-names
                               fn-bs-names-is-names-after-the-pending-list))))

; The publish window's index-m read, as a VALUE and not only as a non-fault:
; it is the kernel's record candidate, which is the arm of
; fn-sf-recovery-crash-imagep the image lands in.
(defthm fn-bs-publish-window-crash-image-reads-the-candidate-record
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (not (fn-bs-replay-visiblep ks))
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                (equal (fn-bs-lookup
                        image :transactions
                        (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions))))
                       (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                      :transactions)))))
           (equal (fn-bs-read-records
                   image (len (fn-bs-durable-names bs :transactions))
                   (1+ (len (fn-bs-durable-names bs :transactions))))
                  (list (fn-sf-record-candidate ks))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-publish-window-crash-image-reads-the-candidate-octets
                 (:instance fn-bs-read-records-one-step
                            (s image)
                            (n (len (fn-bs-durable-names bs :transactions)))
                            (count (1+ (len (fn-bs-durable-names bs
                                                                 :transactions))))))
           :in-theory (disable fn-bs-store-relation fn-bs-statep fn-sf-statep
                               fn-bs-txn-names fn-bs-record-of
                               fn-bs-record-of-octets fn-bs-durable-records
                               fn-bs-durable-frontier fn-bs-authority-fencedp
                               fn-bs-authority-inode-list fn-bs-all-fencedp
                               fn-bs-pending-shape-okp fn-bs-replay-visiblep
                               fn-bs-replay-matches-scan
                               fn-bs-pending-matches-phase
                               fn-sf-crash-imagep fn-sf-admissible-image-facts
                               fn-bs-crash-imagep))))

; The octets the crash image's frontier name points at: the durable ones, or
; the pending rename's target's.
(defthm fn-bs-crash-image-frontier-content
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (or (equal (fn-bs-content image
                                     (fn-bs-lookup image :root
                                                   *fn-bs-scan-frontier-name*))
                      (fn-bs-durable-content
                       bs (fn-bs-durable-entry bs :root
                                               *fn-bs-scan-frontier-name*)))
               (and (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                    (equal (fn-bs-content image
                                          (fn-bs-lookup image :root
                                                        *fn-bs-scan-frontier-name*))
                           (fn-bs-durable-content
                            bs (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                              :root))))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-fences-the-root-inodes
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-shape-at-the-frontier-name)
                 (:instance fn-bs-crash-entry-is-the-durable-one-or-the-pending-target
                            (s bs) (dir :root) (name *fn-bs-scan-frontier-name*)))
           :in-theory (e/d (fn-bs-pending-shape-okp fn-bs-dir-idp fn-bs-namep)
                           (fn-bs-store-relation fn-bs-statep fn-bs-txn-names
                            fn-bs-durable-frontier fn-bs-authority-fencedp
                            fn-bs-authority-inode-list fn-bs-all-fencedp
                            fn-bs-shape-at-the-frontier-name
                            fn-bs-shape-leaves-the-config-name-quiet
                            fn-bs-shape-at-the-pending-link-name
                            fn-bs-shape-leaves-earlier-transaction-names-quiet)))))

(local
 (defthm fn-bs-but-last-of-an-append-of-one-element
   (implies (and (true-listp xs) (true-listp ys) (equal (len ys) 1))
            (equal (fn-sf-but-last (append xs ys)) xs))))

; What the crash image's scan READS, as a value: the durable record list, or
; that list followed by the one record under the link's target.
(defthm fn-bs-crash-image-scan-records
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (or (equal (fn-bs-scan-records (fn-bs-scan-store image))
                      (fn-bs-durable-records bs))
               (and (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                    (equal (fn-bs-lookup
                            image :transactions
                            (fn-bs-txn-name
                             (len (fn-bs-durable-names bs :transactions))))
                           (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                          :transactions))))
                    (equal (fn-bs-scan-records (fn-bs-scan-store image))
                           (append (fn-bs-durable-records bs)
                                   (fn-bs-read-records
                                    image
                                    (len (fn-bs-durable-names bs :transactions))
                                    (1+ (len (fn-bs-durable-names
                                              bs :transactions)))))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-crash-image-scans
                 (:instance fn-bs-scan-okp-unfolds (s image))
                 fn-bs-crash-image-transaction-names
                 fn-bs-crash-image-reads-the-durable-records
                 fn-bs-crash-image-reads-the-linked-record
                 fn-bs-crash-image-namespace-grows-only-with-a-pending-link
                 fn-bs-crash-image-that-kept-the-link-reads-its-target
                 (:instance fn-bs-txn-names-length
                            (n (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-txn-names-length
                            (n (1+ (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-txn-name-in-txn-names
                            (i (len (fn-bs-durable-names bs :transactions)))
                            (n (1+ (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-read-records-of-one-more
                            (s image) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (disable fn-bs-store-relation fn-bs-statep fn-sf-statep
                               fn-bs-txn-names fn-bs-txn-names-length
                               fn-bs-txn-name-in-txn-names
                               fn-bs-read-records fn-bs-read-records-of-one-more
                               fn-bs-record-of fn-bs-durable-records
                               fn-bs-durable-frontier fn-bs-authority-fencedp
                               fn-bs-authority-inode-list fn-bs-all-fencedp
                               fn-bs-pending-shape-okp fn-bs-replay-visiblep
                               fn-bs-replay-matches-scan
                               fn-bs-pending-matches-phase
                               fn-bs-scan-store fn-bs-scan-okp
                               fn-bs-scan-records fn-bs-scan-frontier
                               fn-sf-crash-imagep fn-bs-crash-imagep))))

; In the recovery window the kernel IS this process's scan of the view, so
; both of its components are byte-store values.
(defthm fn-bs-recovery-window-kernel-records
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-replay-visiblep ks))
           (if (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
               (and (equal (fn-sf-records ks)
                           (append (fn-bs-durable-records bs)
                                   (fn-bs-read-records
                                    bs (len (fn-bs-durable-names bs :transactions))
                                    (1+ (len (fn-bs-durable-names
                                              bs :transactions))))))
                    (equal (len (fn-bs-read-records
                                 bs (len (fn-bs-durable-names bs :transactions))
                                 (1+ (len (fn-bs-durable-names
                                           bs :transactions)))))
                           1))
             (equal (fn-sf-records ks) (fn-bs-durable-records bs))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-window-unfolds
                 fn-bs-replay-matches-scan-unfolds
                 fn-bs-view-reads-the-durable-records
                 fn-bs-store-relation-view-namespace-with-a-pending-link
                 fn-bs-store-relation-view-namespace-without-a-pending-link
                 (:instance fn-bs-scan-okp-unfolds (s bs))
                 (:instance fn-bs-txn-names-length
                            (n (1+ (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-read-records-tail-not-fault
                            (s bs) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-read-records-of-one-more
                            (s bs) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-read-records-len
                            (s bs) (n (len (fn-bs-durable-names bs :transactions)))
                            (count (1+ (len (fn-bs-durable-names
                                             bs :transactions))))))
           :in-theory (disable fn-bs-store-relation fn-bs-statep fn-sf-statep
                               fn-bs-txn-names fn-bs-txn-names-length
                               fn-bs-read-records fn-bs-read-records-len
                               fn-bs-read-records-of-one-more
                               fn-bs-read-records-tail-not-fault
                               fn-bs-record-of fn-bs-durable-records
                               fn-bs-durable-frontier fn-bs-authority-fencedp
                               fn-bs-authority-inode-list fn-bs-all-fencedp
                               fn-bs-pending-shape-okp fn-bs-replay-visiblep
                               fn-bs-replay-matches-scan
                               fn-bs-pending-matches-phase
                               fn-bs-scan-store fn-bs-scan-okp
                               fn-bs-scan-records fn-bs-scan-frontier
                               fn-sf-crash-imagep))))

(defthm fn-bs-recovery-window-kernel-frontier
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-replay-visiblep ks))
           (and (implies (not (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root)))
                         (equal (fn-sf-frontier ks) (fn-bs-durable-frontier bs)))
                (implies (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                         (and (equal (fn-sf-frontier ks)
                                     (fn-bs-frontier-decode
                                      (fn-bs-durable-content
                                       bs (nth 3 (car (fn-bs-ops-for-dir
                                                       (fn-bs-pending bs) :root))))))
                              (equal (fn-bs-durable-frontier bs)
                                     (1- (fn-sf-frontier ks)))
                              (fn-sf-frontier-rollback-visiblep ks)
                              (not (consp (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                             :transactions)))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-window-unfolds
                 fn-bs-replay-matches-scan-unfolds
                 fn-bs-store-relation-view-frontier-content
                 (:instance fn-bs-scan-okp-unfolds (s bs)))
           :in-theory (e/d (fn-bs-durable-frontier)
                           (fn-bs-store-relation fn-bs-statep fn-sf-statep
                            fn-bs-txn-names fn-bs-read-records fn-bs-record-of
                            fn-bs-durable-records fn-bs-authority-fencedp
                            fn-bs-authority-inode-list fn-bs-all-fencedp
                            fn-bs-pending-shape-okp fn-bs-replay-visiblep
                            fn-bs-replay-matches-scan
                            fn-bs-pending-matches-phase
                            fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-scan-records fn-bs-scan-frontier
                            fn-sf-crash-imagep
                            fn-sf-frontier-rollback-visiblep)))))

; Outside the recovery window the image the scan reads is one the RELIANCE
; predicate already admits -- old-or-new at the frontier, absent-or-present
; at the record -- so K2's conclusion there is
; fn-sf-crash-imagep-implies-recovery-crash-imagep applied.  The two
; disjuncts are proved apart and joined: with both in one goal the rewriter
; reached its call-depth limit of 1000 on the nesting alone, with no loop
; and no checkpoint to read.
(defthm fn-bs-publish-window-scan-frontier-is-admissible
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (not (fn-bs-replay-visiblep ks)))
           (or (equal (fn-bs-scan-frontier (fn-bs-scan-store image))
                      (fn-sf-frontier ks))
               (and (fn-sf-frontier-new-visiblep ks)
                    (equal (fn-bs-scan-frontier (fn-bs-scan-store image))
                           (fn-sf-frontier-candidate ks)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-window-unfolds
                 fn-bs-pending-matches-phase-unfolds
                 fn-bs-store-crash-image-scans
                 fn-bs-crash-image-frontier-content
                 (:instance fn-bs-scan-okp-unfolds (s image)))
           :in-theory (e/d (fn-sf-crash-imagep fn-bs-durable-frontier)
                           (fn-bs-store-relation fn-bs-statep fn-sf-statep
                            fn-bs-names-after
                            fn-bs-names-is-names-after-the-pending-list
                            fn-bs-crash-keeps-a-quiet-name
                            fn-bs-lookup-of-an-untouched-name
                            fn-bs-lookup-of-a-pending-target
                            fn-bs-crash-image-is-quiet
                            fn-bs-quiet-lookup-is-durable-entry
                            fn-bs-quiet-content-is-durable-content
                            fn-bs-quiet-names-are-durable-names
                            fn-bs-shape-at-the-frontier-name
                            fn-bs-shape-leaves-the-config-name-quiet
                            fn-bs-shape-at-the-pending-link-name
                            fn-bs-shape-leaves-earlier-transaction-names-quiet
                            fn-bs-txn-names fn-bs-read-records fn-bs-record-of
                            fn-bs-durable-records fn-bs-authority-fencedp
                            fn-bs-authority-inode-list fn-bs-all-fencedp
                            fn-bs-pending-shape-okp fn-bs-replay-visiblep
                            fn-bs-replay-matches-scan
                            fn-bs-pending-matches-phase
                            fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-scan-records fn-bs-scan-frontier
                            fn-sf-frontier-new-visiblep
                            fn-sf-record-present-visiblep
                            fn-bs-crash-imagep)))))

; The reliance predicate read once, so that the record clause below never
; has to open it: opened in the same goal as the two candidate values it
; splits eight ways and the rewriter reaches its call-depth limit.
(defthm fn-sf-crash-imagep-unfolds
  (implies (fn-sf-crash-imagep s frontier records)
           (and (or (equal frontier (fn-sf-frontier s))
                    (and (fn-sf-frontier-new-visiblep s)
                         (equal frontier (fn-sf-frontier-candidate s))))
                (or (equal records (fn-sf-records s))
                    (and (fn-sf-record-present-visiblep s)
                         (equal records
                                (append (fn-sf-records s)
                                        (list (fn-sf-record-candidate s))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sf-crash-imagep)
                                  (fn-sf-statep fn-sf-frontier-new-visiblep
                                   fn-sf-record-present-visiblep)))))

(defthm fn-bs-publish-window-scan-records-are-admissible
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (not (fn-bs-replay-visiblep ks)))
           (or (equal (fn-bs-scan-records (fn-bs-scan-store image))
                      (fn-sf-records ks))
               (and (fn-sf-record-present-visiblep ks)
                    (equal (fn-bs-scan-records (fn-bs-scan-store image))
                           (append (fn-sf-records ks)
                                   (list (fn-sf-record-candidate ks)))))))
  :rule-classes nil
  ; Under the minimal theory: every fact this needs is cited, and in the
  ; ambient theory the rewriter reaches its call-depth limit of 1000 with no
  ; loop, no useful rule in its Rules list and no checkpoint to read.
  :hints (("Goal"
           :use (fn-bs-store-relation-window-unfolds
                 fn-bs-pending-matches-phase-unfolds
                 fn-bs-crash-image-scan-records
                 fn-bs-publish-window-crash-image-reads-the-candidate-record
                 (:instance fn-sf-crash-imagep-unfolds
                            (s ks) (frontier (fn-bs-durable-frontier bs))
                            (records (fn-bs-durable-records bs))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-bs-publish-window-crash-image-is-kernel-admissible
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (not (fn-bs-replay-visiblep ks)))
           (fn-sf-crash-imagep ks
                               (fn-bs-scan-frontier (fn-bs-scan-store image))
                               (fn-bs-scan-records (fn-bs-scan-store image))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-publish-window-scan-frontier-is-admissible
                 fn-bs-publish-window-scan-records-are-admissible)
           :in-theory (e/d (fn-sf-crash-imagep)
                           (fn-bs-store-relation fn-bs-statep fn-sf-statep
                            fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-scan-records fn-bs-scan-frontier
                            fn-bs-durable-records fn-bs-durable-frontier
                            fn-bs-authority-fencedp fn-bs-txn-names
                            fn-sf-frontier-new-visiblep
                            fn-sf-record-present-visiblep
                            fn-bs-crash-imagep fn-bs-replay-visiblep)))))

(local
 (defthm fn-bs-a-one-element-list-is-a-cons
   (implies (equal (len x) 1) (consp x))
   :rule-classes nil))
(local
 (defthm fn-bs-append-onto-a-cons-is-a-cons
   (implies (consp b) (consp (append a b)))))

; In the recovery window the scan's one extra read is one record long, and
; both halves of the kernel's record list are true lists -- what
; fn-sf-but-last needs to give the durable list back.
(defthm fn-bs-recovery-window-linked-read-is-one-record
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-replay-visiblep ks)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
           (and (true-listp (fn-bs-durable-records bs))
                (true-listp (fn-bs-read-records
                             bs (len (fn-bs-durable-names bs :transactions))
                             (1+ (len (fn-bs-durable-names bs :transactions)))))
                (equal (len (fn-bs-read-records
                             bs (len (fn-bs-durable-names bs :transactions))
                             (1+ (len (fn-bs-durable-names bs :transactions)))))
                       1)
                (consp (fn-sf-records ks))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-window-unfolds
                 fn-bs-recovery-window-kernel-records
                 fn-bs-replay-matches-scan-unfolds
                 fn-bs-store-relation-view-namespace-with-a-pending-link
                 (:instance fn-bs-scan-okp-unfolds (s bs))
                 (:instance fn-bs-txn-names-length
                            (n (1+ (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-read-records-tail-not-fault
                            (s bs) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-read-records-len
                            (s bs) (n (len (fn-bs-durable-names bs :transactions)))
                            (count (1+ (len (fn-bs-durable-names
                                             bs :transactions)))))
                 (:instance fn-bs-read-records-is-a-true-list
                            (s bs) (n (len (fn-bs-durable-names bs :transactions)))
                            (count (1+ (len (fn-bs-durable-names
                                             bs :transactions)))))
                 (:instance fn-bs-read-records-is-a-true-list
                            (s (fn-bs-durable bs)) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-a-one-element-list-is-a-cons
                            (x (fn-bs-read-records
                                bs (len (fn-bs-durable-names bs :transactions))
                                (1+ (len (fn-bs-durable-names
                                          bs :transactions)))))))
           :in-theory (e/d (fn-bs-durable-records)
                           (fn-bs-store-relation fn-bs-statep fn-sf-statep
                            fn-bs-names-after
                            fn-bs-names-is-names-after-the-pending-list
                            fn-bs-txn-names fn-bs-txn-names-length
                            fn-bs-read-records fn-bs-read-records-len
                            fn-bs-read-records-is-a-true-list
                            fn-bs-read-records-tail-not-fault
                            fn-bs-record-of fn-bs-durable-frontier
                            fn-bs-authority-fencedp fn-bs-authority-inode-list
                            fn-bs-all-fencedp fn-bs-pending-shape-okp
                            fn-bs-replay-visiblep fn-bs-replay-matches-scan
                            fn-bs-pending-matches-phase
                            fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-scan-records fn-bs-scan-frontier
                            fn-sf-crash-imagep fn-bs-crash-imagep)))))

(defthm fn-bs-recovery-window-scan-records-are-admissible
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (fn-bs-replay-visiblep ks))
           (or (equal (fn-bs-scan-records (fn-bs-scan-store image))
                      (fn-sf-records ks))
               (and (fn-sf-record-rollback-visiblep ks)
                    (equal (fn-bs-scan-records (fn-bs-scan-store image))
                           (fn-sf-but-last (fn-sf-records ks))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-window-unfolds
                 fn-bs-replay-matches-scan-unfolds
                 fn-bs-crash-image-scan-records
                 fn-bs-recovery-window-kernel-records
                 fn-bs-recovery-window-linked-read-is-one-record
                 fn-bs-crash-image-agrees-with-the-view-at-the-link
                 (:instance fn-bs-read-records-under-agreement
                            (a image) (b bs)
                            (n (len (fn-bs-durable-names bs :transactions)))
                            (count (1+ (len (fn-bs-durable-names
                                             bs :transactions)))))
                 (:instance fn-bs-but-last-of-an-append-of-one-element
                            (xs (fn-bs-durable-records bs))
                            (ys (fn-bs-read-records
                                 bs (len (fn-bs-durable-names bs :transactions))
                                 (1+ (len (fn-bs-durable-names
                                           bs :transactions)))))))
           :in-theory (union-theories '(fn-sf-record-rollback-visiblep
                                        fn-sf-recovery-visiblep
                                        fn-bs-replay-visiblep)
                                      (theory 'minimal-theory)))))

(defthm fn-bs-recovery-window-scan-frontier-is-admissible
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (fn-bs-replay-visiblep ks))
           (or (equal (fn-bs-scan-frontier (fn-bs-scan-store image))
                      (fn-sf-frontier ks))
               (and (fn-sf-frontier-rollback-visiblep ks)
                    (equal (fn-bs-scan-frontier (fn-bs-scan-store image))
                           (1- (fn-sf-frontier ks)))
                    (equal (fn-bs-scan-records (fn-bs-scan-store image))
                           (fn-sf-records ks)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-crash-image-scans
                 fn-bs-crash-image-frontier-content
                 fn-bs-crash-image-scan-records
                 fn-bs-recovery-window-kernel-frontier
                 fn-bs-recovery-window-kernel-records
                 (:instance fn-bs-scan-okp-unfolds (s image)))
           :in-theory (e/d (fn-bs-durable-frontier)
                           (fn-bs-store-relation fn-bs-statep fn-sf-statep
                            fn-bs-names-after
                            fn-bs-names-is-names-after-the-pending-list
                            fn-bs-crash-keeps-a-quiet-name
                            fn-bs-lookup-of-an-untouched-name
                            fn-bs-lookup-of-a-pending-target
                            fn-bs-crash-image-is-quiet
                            fn-bs-quiet-lookup-is-durable-entry
                            fn-bs-quiet-content-is-durable-content
                            fn-bs-quiet-names-are-durable-names
                            fn-bs-shape-at-the-frontier-name
                            fn-bs-shape-leaves-the-config-name-quiet
                            fn-bs-shape-at-the-pending-link-name
                            fn-bs-shape-leaves-earlier-transaction-names-quiet
                            fn-bs-txn-names fn-bs-read-records fn-bs-record-of
                            fn-bs-durable-records fn-bs-authority-fencedp
                            fn-bs-authority-inode-list fn-bs-all-fencedp
                            fn-bs-pending-shape-okp fn-bs-replay-visiblep
                            fn-bs-replay-matches-scan
                            fn-bs-pending-matches-phase
                            fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-scan-records fn-bs-scan-frontier
                            fn-sf-frontier-rollback-visiblep
                            fn-sf-crash-imagep fn-bs-crash-imagep)))))

(defthm fn-bs-recovery-window-crash-image-is-kernel-admissible
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image)
                (fn-bs-replay-visiblep ks))
           (fn-sf-recovery-crash-imagep
            ks
            (fn-bs-scan-frontier (fn-bs-scan-store image))
            (fn-bs-scan-records (fn-bs-scan-store image))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-recovery-window-scan-frontier-is-admissible
                 fn-bs-recovery-window-scan-records-are-admissible)
           :in-theory (union-theories '(fn-sf-recovery-crash-imagep)
                                      (theory 'minimal-theory)))))

; K2.  Old-or-new and absent-or-present as a THEOREM: every byte-level crash
; image of a related state scans to an image the file kernel admits.  The
; conclusion is the PLATFORM predicate (D14-b, D14-c), which in the recovery
; window is strictly wider than what a consumer may rely on -- and it is the
; rollback arms, both of them, that the window needs.
(defthm fn-bs-store-crash-image-is-kernel-admissible
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (fn-sf-recovery-crash-imagep
            ks
            (fn-bs-scan-frontier (fn-bs-scan-store image))
            (fn-bs-scan-records (fn-bs-scan-store image))))
  :hints (("Goal"
           :use (fn-bs-recovery-window-crash-image-is-kernel-admissible
                 fn-bs-publish-window-crash-image-is-kernel-admissible
                 (:instance fn-sf-crash-imagep-implies-recovery-crash-imagep
                            (s ks)
                            (frontier (fn-bs-scan-frontier
                                       (fn-bs-scan-store image)))
                            (records (fn-bs-scan-records
                                      (fn-bs-scan-store image)))))
           :in-theory (union-theories '(fn-bs-replay-visiblep)
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 11. Export theory (docs/proof-style.md section 2).
;
; Enabled on include: the keystones (K1, K2 and the four clause theorems
; under K1), fn-bs-crash-imagep-preserves-statep, the seams' constraints and
; the two namespace facts about fn-bs-txn-names.  Withdrawn: every
; definition the keystones are STATED over, because one downstream unfold of
; fn-bs-scan-frontier or fn-bs-scan-records stops them matching (the ledger's
; enabled-projection warning, and the reason sections 8 to 10 keep them
; closed at every step); and the per-name, per-window and shape vocabulary,
; which is proof machinery for this book and nothing above it.
;
; The -unfolds lemmas are absent from this theory on purpose and not by
; omission: each is :rule-classes nil, so it designates no rule, and a
; :rule-classes nil theorem named in a theory expression is a HARD ACL2
; ERROR under certify-book rather than a no-op.

(deftheory fn-bs-scan-vocabulary
  '(fn-bs-strip-cars-of-put-assoc fn-bs-strip-cars-of-del-assoc
    fn-bs-alistp-of-del-assoc fn-bs-alistp-of-dir-entries
    fn-bs-apply-entries-preserves-alistp-of-entries
    fn-bs-apply-entries-names-is-names-after
    fn-bs-names-after-of-tear-write fn-bs-names-after-of-append
    fn-bs-names-outcomes-of-no-ops fn-bs-names-outcomes-of-one-op
    fn-bs-crash-select-names-are-an-outcome
    fn-bs-crash-pending-is-nil fn-bs-crash-image-is-quiet
    fn-bs-quiet-lookup-is-durable-entry fn-bs-quiet-content-is-durable-content
    fn-bs-quiet-names-are-durable-names fn-bs-durable-is-quiet
    fn-bs-entry-outcomes-of-nil fn-bs-crash-keeps-untouched-entry
    fn-bs-all-fencedp-of-append fn-bs-all-fencedp-member
    fn-bs-assoc-value-is-in-strip-cdrs fn-bs-assoc-of-name-in-entries
    fn-bs-read-records-under-agreement fn-bs-read-records-len
    fn-bs-read-records-is-a-true-list fn-bs-read-records-of-one-more
    fn-bs-txn-names-length
    fn-bs-crash-names-is-names-after fn-bs-crash-image-names-are-an-outcome
    fn-bs-shape-leaves-the-config-name-quiet fn-bs-shape-at-the-frontier-name
    fn-bs-shape-at-the-pending-link-name
    fn-bs-shape-leaves-earlier-transaction-names-quiet
    fn-bs-lookup-of-an-untouched-name fn-bs-lookup-of-a-pending-target
    fn-bs-content-of-a-fenced-inode fn-bs-names-is-names-after-the-pending-list
    fn-bs-crash-keeps-a-quiet-name))

(in-theory (disable fn-bs-scan-vocabulary
                    fn-bs-record-of-octets fn-bs-record-of fn-bs-txn-names
                    fn-bs-contiguous-namesp fn-bs-read-records
                    fn-bs-scan-store fn-bs-scan-okp fn-bs-scan-frontier
                    fn-bs-scan-records
                    fn-bs-durable fn-bs-durable-names fn-bs-durable-frontier
                    fn-bs-durable-records fn-bs-replay-visiblep
                    fn-bs-pending-shape-okp fn-bs-pending-matches-phase
                    fn-bs-replay-matches-scan fn-bs-pending-entry-targets
                    fn-bs-authority-inode-list fn-bs-all-fencedp
                    fn-bs-authority-fencedp fn-bs-inode-list-knownp
                    fn-bs-authority-knownp fn-bs-store-relation
                    fn-bs-name-step fn-bs-names-after fn-bs-names-outcomes
                    fn-bs-txn-prefix-agreesp))
