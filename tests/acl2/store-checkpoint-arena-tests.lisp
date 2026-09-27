; fn: witnesses and teeth for the state checkpoint under the records flip
; (books/store-checkpoint-arena.lisp, -load.lisp, -writer.lisp; lanes
; checkpoint-arena and checkpoint-arena-2).
;
; The live store below is reached by the host's own calls: the history's
; wire events interned into a local arena by fn-intern-events (the open),
; with an ORPHAN payload sealed between two articles (a prepare whose
; commit did not happen), so the live handles are not the canonical ones
; and the writer must canonicalize.  Then, end to end: the arena run
; written by fn-scka-write-run and the tables by fn-ockp-run into one file,
; the file read back through the host's plan shape (each segment its own
; frame over a fresh buffer), loaded by fn-scka-load, and opened over a
; suffix by fn-scka-recover-rows, against the full recover of the whole
; history.  Hypothesis-removal witnesses check every retained hypothesis,
; the failure of the omitted one and of the conclusion; corrupted-file
; (mutation) witnesses are labelled.  (Attachments evaluate in assert-event
; and defun bodies: the seal is fn-sha256's.)

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/store-checkpoint-arena-load")
(include-book "../../books/store-checkpoint-arena-writer")

; Every executable function the host reaches is guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-scka-seal-n (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scka-finish (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scka-write-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scka-write-setup (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scka-publication-setup (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scka-initial-state (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scka-write-donep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scka-canon-rows (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-intern-events (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sshr-share (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scka-srcs-n (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scka-lens-setup (w state)) :common-lisp-compliant)))

; fn-sshr-share-is-identity (no hypothesis): repeated contents, a dotted
; tail, a string tail, nested lists, atoms.  (That the answer holds one
; object per content is measured, not stated: the heap census by content,
; planning/evidence/checkpoint-arena-3-2026-09-27.md.)
(assert-event
 (let ((x (list "a" (cons "a" "b") (list* 1 2 "c") "c" nil 7 (list (list "a" "")) "")))
   (equal (fn-sshr-share x) x)))

; -----------------------------------------------------------------------------
; The history: three articles and a retention event (a wire event that seals
; nothing), and a suffix article.

(defconst *sckat-groups* '("fn.letters" "fn.test"))
(defconst *sckat-w1*
  (fn-record-make 0 0 0 "<one@example>" '(1 2 3) *sckat-groups*
                  "p1" "c1" "r1" 2 841000000))
(defconst *sckat-w2*
  (fn-record-make 1 1 0 "<two@example>" '(65 66) *sckat-groups*
                  "p2" "c2" "r2" 2 841000001))
(defconst *sckat-w3*
  (fn-record-make 2 2 0 "<three@example>" '(7 8 9 10) *sckat-groups*
                  "p3" "c3" "r3" 2 841000002))
(defconst *sckat-e*
  (fn-store-retention-event-make :undertake 3 3 0 "forward-cpo" "subject" "evidence" 10))
(defconst *sckat-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
(defconst *sckat-prefix* (list *sckat-w1* *sckat-e* *sckat-w2*))
(defconst *sckat-suffix* (list *sckat-w3*))
(defconst *sckat-orphan* '(99 99 99 99 99))

(assert-event (and (fn-record-p *sckat-w1*) (fn-record-p *sckat-w2*) (fn-record-p *sckat-w3*)
                   (fn-wire-event-p *sckat-e*) (not (fn-scka-sealsp *sckat-e*))))

; The arena's logical value, read by handle.
(defun sckat-arena-list (h fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil
                  :measure (nfix (- (fn-arena-count fn-arena) (nfix h)))))
  (if (and (natp h) (< h (fn-arena-count fn-arena)))
      (cons (fn-arena-payload h fn-arena) (sckat-arena-list (+ 1 h) fn-arena))
    nil))

(defun sckat-seal-all (ps fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom ps)
      fn-arena
    (let ((fn-arena (fn-arena-seal-list (car ps) fn-arena)))
      (sckat-seal-all (cdr ps) fn-arena))))

; -----------------------------------------------------------------------------
; 1. The canonical intern (fn-intern-events-is-intern-at,
; fn-intern-events-arena-is-payloads): over an arena already holding A0.

(defun sckat-intern (a0 ws)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (let ((fn-arena (sckat-seal-all a0 fn-arena)))
        (mv-let (rows fn-arena)
          (fn-intern-events ws nil 0 fn-arena)
          (mv (list rows (sckat-arena-list 0 fn-arena)) fn-arena)))
      out)))

; Reachable positive witness: both conclusions, the antecedents.
(assert-event
 (let ((r (sckat-intern (list *sckat-orphan*) *sckat-prefix*)))
   (and (true-listp (list *sckat-orphan*))
        (not (equal (fn-scka-intern-at *sckat-prefix* 1) :bad))
        (equal (car r) (fn-scka-intern-at *sckat-prefix* 1))
        (equal (cadr r) (append (list *sckat-orphan*) (fn-scka-payloads *sckat-prefix*)))
        (equal (fn-scka-payloads *sckat-prefix*) (list '(1 2 3) '(65 66)))
        ; the handles are the canonical counter from the arena's count
        (equal (fn-record-payload (car (car r))) 1)
        (equal (fn-record-payload (caddr (car r))) 2))))

; fn-intern-events-arena-is-payloads without "the intern is not refused": a
; history with a value the intern refuses between two articles; the arena
; holds the first article's payload only, not the canonical payloads.
(defconst *sckat-bad-history* (list *sckat-w1* 'not-an-event *sckat-w2*))
(assert-event
 (let ((r (sckat-intern nil *sckat-bad-history*)))
   (and (true-listp nil)
        (equal (fn-scka-intern-at *sckat-bad-history* 0) :bad)
        (not (equal (cadr r) (append nil (fn-scka-payloads *sckat-bad-history*)))))))

; ... without "the arena is a true list" (a logical value no stobj holds:
; the recognizer carries the hypothesis): a history that seals nothing
; leaves any arena unchanged, and an improper list is not its append.
(defthm sckat-intern-sealing-nothing-keeps-the-arena
  (equal (mv-nth 1 (fn-intern-events (list *sckat-e*) nil 0 a)) a)
  :hints (("Goal" :in-theory (enable fn-intern-events fn-intern-event))))
(defthm sckat-improper-arena-is-not-its-append
  (and (not (true-listp '((1) . 5)))
       (not (equal (fn-scka-intern-at (list *sckat-e*) 0) :bad))
       (not (equal '((1) . 5) (append '((1) . 5) (fn-scka-payloads (list *sckat-e*))))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; 2. The live store: the prefix interned at the open, an orphan payload
; sealed, the suffix interned after it (a POST whose handle is not the
; canonical one).  ROWS are the live rows.

(defun sckat-live-in (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows1 fn-arena)
    (fn-intern-events *sckat-prefix* nil 0 fn-arena)
    (let ((fn-arena (fn-arena-seal-list *sckat-orphan* fn-arena)))
      (mv-let (rows2 fn-arena)
        (fn-intern-events (list *sckat-w3*) nil 0 fn-arena)
        (mv (append rows1 rows2) fn-arena)))))

(defun sckat-live ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (mv-let (rows fn-arena)
        (sckat-live-in fn-arena)
        (mv (list rows (sckat-arena-list 0 fn-arena)
                  (fn-scka-canon-rows rows fn-arena 0)
                  (fn-scka-canon-payloads rows fn-arena)
                  (fn-rows-wire-of rows fn-arena))
            fn-arena))
      out)))

(defconst *sckat-history* (append *sckat-prefix* *sckat-suffix*))

; The live handles are not canonical (w3's is 3, its canonical handle 2);
; alpha of the live rows is the history; the canonical rows and payloads
; are the intern of it (fn-scka-canon-rows-is-intern-at-of-alpha,
; fn-scka-canon-payloads-is-payloads-of-alpha).
(assert-event
 (let ((r (sckat-live)))
   (and (equal (fn-record-payload (nth 3 (car r))) 3)
        (equal (nth 4 r) *sckat-history*)
        (equal (nth 2 r) (fn-scka-intern-at *sckat-history* 0))
        (equal (fn-record-payload (nth 3 (nth 2 r))) 2)
        (equal (nth 3 r) (fn-scka-payloads *sckat-history*))
        (equal (nth 3 r) (list '(1 2 3) '(65 66) '(7 8 9 10)))
        (not (equal (cadr r) (nth 3 r))))))

; -----------------------------------------------------------------------------
; 3. End to end: the file written from the live store, read back through the
; host's plan shape, loaded, and opened over a suffix.

(defconst *sckat-seg* 8)
(defconst *sckat-w4*
  (fn-record-make 4 4 0 "<four@example>" '(11 12) *sckat-groups*
                  "p4" "c4" "r4" 2 841000003))

(defun sckat-frames-of (octets header-octets trailer-octets acc fuel fn-octets)
  ; The host's read (host/native/io.lisp fnn-state-checkpoint-plan): split
  ; OCTETS into frames (HEADER A B TRAILER) by each header's LENGTH,
  ; appending each chunk into the buffer.
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil
                  :measure (nfix fuel)))
  (if (or (zp fuel) (not (consp octets)))
      (mv (if (consp octets) :torn (revappend acc nil)) fn-octets)
    (let* ((header (take header-octets octets))
           (h (fn-scc-parse-header header)))
      (if (or (not h) (< (len octets) (+ header-octets (nth 2 h) trailer-octets)))
          (mv :torn fn-octets)
        (let* ((chunk (take (nth 2 h) (nthcdr header-octets octets)))
               (trailer (take trailer-octets (nthcdr (+ header-octets (nth 2 h)) octets)))
               (rest (nthcdr (+ header-octets (nth 2 h) trailer-octets) octets))
               (a (fn-octets-len fn-octets))
               (fn-octets (fn-octets-append-list chunk fn-octets)))
          (sckat-frames-of rest header-octets trailer-octets
                           (cons (list header a (+ a (len chunk)) trailer) acc)
                           (1- fuel) fn-octets))))))

; The host's walk (host/native/io.lisp fnn-checkpoint-walk): fn-scka-srcs-n
; N rows per call until the rows are consumed.
(defun sckat-walk (st n fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (atom (nth 0 st)))
      st
    (sckat-walk (fn-scka-srcs-n (nth 0 st) n (nth 1 st) (nth 2 st) fn-arena) n (1- fuel)
                fn-arena)))

; The writer over the live store: (VERDICT ESTIMATE V-ARENA A-OCTETS
; V-TABLES T-OCTETS NEXT TABLES WRITE-SETUP), KS the batches (or the setup's).
; The arena run's setup and sources come from the walk, two rows per call.
(defun sckat-write-in (rows ks-override b fn-arena fn-octets)
  (declare (xargs :stobjs (fn-arena fn-octets) :verify-guards nil))
  (let* ((canon (fn-scka-canon-rows rows fn-arena 0))
         (next (fn-sco-capture *sckat-configs* canon))
         (walk (sckat-walk (list rows nil nil) 2 100 fn-arena))
         (ws (fn-scka-lens-setup (reverse (nth 1 walk)) *sckat-seg*))
         (ks (or ks-override (nth 1 ws)))
         (setup (fn-scka-publication-setup next 9 "rev-test" nil *sckat-seg* 1000000000
                                           1000000000000 (nth 3 ws)))
         (s (len rows)))
    (mv-let (v1 aoct fn-octets)
      (fn-scka-write-run (fn-scka-initial-state (reverse (nth 2 walk)) ks 0) (nth 0 ws)
                         (+ 1 (len ks)) s 100000 100000000 1000 fn-arena fn-octets)
      (mv-let (v2 toct fn-octets)
        (fn-ockp-run setup (fn-ockp-initial-state (cadr setup) fn-octets) b 1000000
                     *sckat-seg* s 100000 100000000 1000 fn-octets)
        (mv (list (car setup) (nth 6 setup) v1 aoct v2 toct next (cadr setup) ws)
            fn-octets)))))

; The load of FILE into the (emptied) arena, then the open over the suffix
; VS: (LOADED ARENA-AFTER-LOAD OPENED ARENA-AFTER-OPEN).
(defun sckat-load-open-in (file vs fn-arena fn-octets)
  (declare (xargs :stobjs (fn-arena fn-octets) :verify-guards nil))
  (let ((fn-octets (fn-octets-clear fn-octets)))
    (mv-let (plan fn-octets)
      (sckat-frames-of file *fn-scc-segment-header-octets* *fn-frame-trailer-octets*
                       nil 100000 fn-octets)
      (if (eq plan :torn)
          (mv (list :torn nil nil nil) fn-arena fn-octets)
        (mv-let (loaded fn-arena)
          (fn-scka-load plan fn-octets fn-arena)
          (let ((a1 (sckat-arena-list 0 fn-arena)))
            (if (not (eq (car loaded) :ok))
                (mv (list loaded a1 nil nil) fn-arena fn-octets)
              (mv-let (opened fn-arena)
                (fn-scka-recover-rows (fn-sct-capture-of-tables (cadr loaded)) *sckat-configs*
                                      vs fn-arena)
                (mv (list loaded a1 opened (sckat-arena-list 0 fn-arena))
                    fn-arena fn-octets)))))))))

; The full recover of HISTORY from the emptied arena: (OPENED ARENA).
(defun sckat-full-in (history fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((fn-arena (fn-arena-clear fn-arena)))
    (mv-let (opened fn-arena)
      (fn-scka-recover-rows (fn-sco-capture *sckat-configs* nil) *sckat-configs* history
                            fn-arena)
      (mv (list opened (sckat-arena-list 0 fn-arena)) fn-arena))))

; (WRITTEN LOAD-OPEN FULL CANON-PAYLOADS FILE), the file the writer's two
; loops wrote (arena run, then tables); MUTATE edits it before the read.
(defun sckat-e2e (ks-override mutate)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (with-local-stobj fn-octets
        (mv-let (out fn-arena fn-octets)
          (mv-let (rows fn-arena)
            (sckat-live-in fn-arena)
            (let ((ps (fn-scka-canon-payloads rows fn-arena)))
              (mv-let (written fn-octets)
                (sckat-write-in rows ks-override 1 fn-arena fn-octets)
                (let* ((file0 (append (nth 3 written) (nth 5 written)))
                       (file (cond ((eq mutate :tables-only) (nth 5 written))
                                   ((natp mutate) (update-nth mutate
                                                              (logxor 1 (nth mutate file0))
                                                              file0))
                                   (t file0))))
                  (mv-let (lo fn-arena fn-octets)
                    (sckat-load-open-in file (list *sckat-w4*) fn-arena fn-octets)
                    (mv-let (full fn-arena)
                      (sckat-full-in (append *sckat-history* (list *sckat-w4*)) fn-arena)
                      (mv (list written lo full ps file) fn-arena fn-octets)))))))
          (mv out fn-arena)))
      out)))

(defconst *sckat-canon-payloads* (list '(1 2 3) '(65 66) '(7 8 9 10)))

; KEYSTONE witnesses, the whole chain on one reachable store:
;  - the writer (fn-scka-write-run-is-run-segments): the setup's batches sum
;    to the payload count, both loops answer :ok, and the arena run's octets
;    are the run segments of the canonical payloads;
;  - the publication's estimate is the file's length;
;  - the load (fn-scka-load-of-written-file): the plan of the file loads to
;    the tables with the arena exactly the canonical payloads, and the tables
;    mean NEXT;
;  - the open (fn-scka-recover-from-checkpoint-is-full-recover): over the
;    suffix it is the full recover of the whole history, extension and arena.
(assert-event
 (let* ((r (sckat-e2e nil nil))
        (written (nth 0 r)) (lo (nth 1 r)) (full (nth 2 r)) (ws (nth 8 written)))
   (and (equal (nth 3 r) *sckat-canon-payloads*)
        (equal (fn-scka-sum (nth 1 ws)) (len (nth 3 r)))
        (< 1 (len (nth 1 ws)))
        (eq (nth 2 written) :ok)
        (eq (nth 4 written) :ok)
        (equal (nth 3 written)
               (fn-scc-concat (fn-scka-run-segments (nth 3 r) (nth 1 ws) 4)))
        (equal (car written) (list :plan (len (nth 4 r))))
        (equal (nth 1 written) (len (nth 4 r)))
        (equal (car lo) (list :ok (nth 7 written)))
        (equal (nth 1 lo) *sckat-canon-payloads*)
        (equal (fn-sct-capture-of-tables (nth 7 written)) (nth 6 written))
        (not (equal (fn-scka-intern-at (append *sckat-history* (list *sckat-w4*)) 0) :bad))
        (not (eq (nth 2 lo) :bad))
        (equal (nth 2 lo) (car full))
        (equal (nth 3 lo) (cadr full)))))

; fn-scka-write-run-is-run-segments without "the batches sum to the payload
; count": one batch more than the payloads fill; the loop still answers :ok
; but its octets are not the run segments (the specification's extra chunk
; is a padded empty payload, the writer's is empty).
(assert-event
 (let* ((r0 (sckat-e2e nil nil))
        (ks (append (nth 1 (nth 8 (nth 0 r0))) (list 1)))
        (r (sckat-e2e ks nil))
        (written (nth 0 r)))
   (and (not (equal (fn-scka-sum ks) (len (nth 3 r))))
        (eq (nth 2 written) :ok)
        (not (equal (nth 3 written)
                    (fn-scc-concat (fn-scka-run-segments (nth 3 r) ks 4)))))))

; CORRUPTED FILE (mutation): a tables-only file (the schema-3 file written
; before the flip) is refused by name, :arena; the journal then replays.
(assert-event
 (let ((r (sckat-e2e nil :tables-only)))
   (equal (car (nth 1 r)) (list :refused :arena))))

; CORRUPTED FILE (mutation): one bit flipped in a payload of the arena run
; (octet 50: inside the second segment's chunk) is refused: the chain.
(assert-event
 (let ((r (sckat-e2e nil 50)))
   (and (< 50 (len (nth 3 (nth 0 r))))
        (equal (car (car (nth 1 r))) :refused))))

;; -----------------------------------------------------------------------------
;; 3b. The walk and the sources (checkpoint-arena-3).  On the live store the
;; orphan payload sits between the second and the third article, so the
;; third article's SOURCE is its live handle 3 while its canonical position
;; is 2: the sources are not the canonical handles, and they read back the
;; canonical payloads (fn-scka-src-payloads-of-canon-srcs).
;; (WALK-BY-2 WALK-AT-ONCE CANON-LENS CANON-SRCS SRC-PAYLOADS CANON-PAYLOADS
;;  SRCS-OKP ROWS-TRUE-LISTP)
(defun sckat-walked ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (mv-let (rows fn-arena)
        (sckat-live-in fn-arena)
        (mv (list (sckat-walk (list rows '(9) '(x)) 2 100 fn-arena)
                  (fn-scka-srcs-n rows (len rows) '(9) '(x) fn-arena)
                  (fn-scka-canon-lens rows fn-arena)
                  (fn-scka-canon-srcs rows fn-arena)
                  (fn-scka-src-payloads (fn-scka-canon-srcs rows fn-arena) fn-arena)
                  (fn-scka-canon-payloads rows fn-arena)
                  (fn-scka-srcs-okp (fn-scka-canon-srcs rows fn-arena) fn-arena)
                  (true-listp rows)
                  (len rows))
            fn-arena))
      out)))

; fn-scka-srcs-n-compose and -complete (reachable, nonempty accumulators):
; the walk two rows per call is the walk at once, the canonical lengths and
; sources reversed onto the accumulators, the rows consumed.
(assert-event
 (let ((r (sckat-walked)))
   (and (nth 7 r) (< 2 (nth 8 r))
        (equal (nth 0 r) (nth 1 r))
        (equal (nth 1 r) (list nil (revappend (nth 2 r) '(9)) (revappend (nth 3 r) '(x)))))))

; fn-scka-src-payloads-of-canon-srcs, fn-scka-srcs-okp-of-canon-srcs: the
; sources are the live handles (0 1 3), not the canonical ones (0 1 2), and
; read back the canonical payloads.
(assert-event
 (let ((r (sckat-walked)))
   (and (equal (nth 3 r) '(0 1 3))
        (equal (nth 4 r) *sckat-canon-payloads*)
        (equal (nth 5 r) *sckat-canon-payloads*)
        (nth 6 r))))

(defun sckat-walk-short (n)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (mv-let (rows fn-arena)
        (sckat-live-in fn-arena)
        (mv (fn-scka-srcs-n rows n nil nil fn-arena) fn-arena))
      out)))

; fn-scka-srcs-n-complete without "the walk covers the rows": one row short,
; the rows are not consumed and the lengths and sources are not all there.
(assert-event
 (let* ((r (sckat-walked)) (n (1- (nth 8 r))))
   (and (nth 7 r) (not (<= (nth 8 r) n))
        (not (equal (sckat-walk-short n)
                    (list nil (reverse (nth 2 r)) (reverse (nth 3 r))))))))

;; -----------------------------------------------------------------------------
;; 3c. REPRESENTATION BOUNDS of the load keystone (checkpoint-arena-3).
;; fn-scka-load-of-written-file assumes the file's counts fit the codec's
;; fields: the run's and each table's segment count below 2^64 (the
;; (< (+ 1 (len ks)) *fn-scc-u64-bound*) and fn-sct-programs-widthp
;; hypotheses), S below 2^64, every chunk shorter than 2^64 octets
;; (fn-scc-chunk-listp), and at most 2^32 records (the P table's reference
;; index keys a u32).  No store reaches them: the profile's bounds are far
;; below, and a file past them cannot be built to load.  So the witness for
;; each hypothesis is at the FIELD it protects: the value at the bound reads
;; back, the value one past it does not (the count the loader would read is
;; not the count written), which is how the keystone's conclusion fails
;; without it.  Component-level witnesses, labelled as such.

; The segment count (the header's count field, both the arena run's and a
; table run's): 2^64 - 1 reads back, 2^64 reads as 0.
(assert-event
 (let ((at (fn-scc-parse-header (fn-scc-header 0 (1- *fn-scc-u64-bound*) 5 3)))
       (past (fn-scc-parse-header (fn-scc-header 0 *fn-scc-u64-bound* 5 3))))
   (and (equal (nth 1 at) (1- *fn-scc-u64-bound*))
        (consp past)
        (not (equal (nth 1 past) *fn-scc-u64-bound*))
        (equal (nth 1 past) 0))))

; S (the header's sequence field): 2^64 - 1 reads back, 2^64 reads as 0,
; so the loader's check that the F row's S is the run's compares a
; different number.
(assert-event
 (let ((at (fn-scc-parse-header (fn-scc-header 0 2 5 (1- *fn-scc-u64-bound*))))
       (past (fn-scc-parse-header (fn-scc-header 0 2 5 *fn-scc-u64-bound*))))
   (and (equal (nth 3 at) (1- *fn-scc-u64-bound*))
        (not (equal (nth 3 past) *fn-scc-u64-bound*))
        (equal (nth 3 past) 0))))

; A chunk's length (the header's length field): 2^64 octets would read as
; an empty chunk.
(assert-event
 (let ((at (fn-scc-parse-header (fn-scc-header 0 2 (1- *fn-scc-u64-bound*) 3)))
       (past (fn-scc-parse-header (fn-scc-header 0 2 *fn-scc-u64-bound* 3))))
   (and (equal (nth 2 at) (1- *fn-scc-u64-bound*))
        (not (equal (nth 2 past) *fn-scc-u64-bound*))
        (equal (nth 2 past) 0))))

; At most 2^32 records: the P table's reference index (fn-cei-build, the
; E and R tables' ref op) finds the payload at 2^32 - 1 and nothing at
; 2^32, so a reference past it is :dangling and the load refuses.
(assert-event
 (let ((ix (fn-cei-put *fn-cbor-max-uint* (list 7 7)
                       (fn-cei-put (+ 1 *fn-cbor-max-uint*) (list 9 9) nil))))
   (and (equal (fn-sct-ref-get *fn-cbor-max-uint* ix) (list 7 7))
        (null (fn-sct-ref-get (+ 1 *fn-cbor-max-uint*) ix)))))

; -----------------------------------------------------------------------------
; 4. The owner's next checkpoint (fn-scka-next-checkpoint-is-capture): BASE
; the capture (under BASE-CONFIGS) of the canonical rows of the first PLEN
; live rows, H0 given or their canonical payload count.
; (NEXT CAPTURE-OF-ALL CANONICAL-H0)

(defun sckat-owner (plen h0 stale)
  ; STALE: the base's records name the prefix but its state is the empty
  ; capture's (a base that is not the capture of the prefix).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (mv-let (rows fn-arena)
        (sckat-live-in fn-arena)
        (let* ((prefix (fn-scka-canon-rows (take plen rows) fn-arena 0))
               (base (if stale
                         (update-nth 1 prefix (fn-sco-capture *sckat-configs* nil))
                       (fn-sco-capture *sckat-configs* prefix)))
               (h (len (fn-scka-canon-payloads (take plen rows) fn-arena))))
          (mv (list (fn-scka-next-checkpoint base (if h0 h0 h) *sckat-configs* rows fn-arena)
                    (fn-sco-capture *sckat-configs* (fn-scka-canon-rows rows fn-arena 0))
                    h
                    (equal base (fn-sco-capture *sckat-configs* prefix))
                    (equal (len (fn-sco-records base)) plen))
              fn-arena)))
      out)))

; Reachable positive witness: the base of the prefix (the open's), H0 = 2;
; the orphan sealed after it does not move the suffix's canonical handle.
(assert-event
 (let ((r (sckat-owner 3 nil nil)))
   (and (equal (nth 2 r) 2)
        (nth 3 r) (nth 4 r)
        (not (equal (fn-scka-intern-at *sckat-history* 0) :bad))
        (equal (car r) (cadr r)))))

; Without "H0 is the base's canonical payload count": H0 = 3, the live
; arena's count when the suffix was posted (the orphan counted).
(assert-event
 (let ((r (sckat-owner 3 3 nil)))
   (and (nth 3 r) (nth 4 r)
        (not (equal 3 (nth 2 r)))
        (not (equal (car r) (cadr r))))))

; Without "BASE is the capture of the prefix's canonical rows" (CORRUPTED
; base: its records name the prefix, its state is the empty capture's).
(assert-event
 (let ((r (sckat-owner 3 nil t)))
   (and (equal (nth 2 r) 2)
        (not (nth 3 r)) (nth 4 r)
        (not (equal (car r) (cadr r))))))

; fn-scka-restore-base-of-strip-of-capture (reachable positive witness): the
; owner's base at the open (the capture of the prefix's canonical rows),
; stripped as the owner keeps it, has no event index, and restored is the
; capture again, whose index is not empty.
(defun sckat-kept-base ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (mv-let (rows fn-arena)
        (sckat-live-in fn-arena)
        (mv (fn-sco-capture *sckat-configs* (fn-scka-canon-rows (take 3 rows) fn-arena 0))
            fn-arena))
      out)))

(assert-event
 (let* ((base (sckat-kept-base)) (kept (fn-scka-strip-base base)))
   (and (equal (len (fn-sco-records base)) 3)
        (fn-sco-event-index base)
        (null (fn-sco-event-index kept))
        (equal (fn-sco-records kept) (fn-sco-records base))
        (equal (fn-scka-restore-base kept) base))))

; -----------------------------------------------------------------------------
; 5. fn-scka-recover-from-checkpoint-is-full-recover without "the whole
; history interns": a prefix the intern refuses, a suffix it takes.  The
; open from the (refused) prefix's checkpoint extends it; the full recover
; faults.

(defun sckat-recover-pair (ws vs)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (let ((fn-arena (sckat-seal-all (fn-scka-payloads ws) fn-arena)))
        (mv-let (lhs fn-arena)
          (fn-scka-recover-rows (fn-sco-capture *sckat-configs* (fn-scka-intern-at ws 0))
                                *sckat-configs* vs fn-arena)
          (let ((a1 (sckat-arena-list 0 fn-arena)))
            (mv-let (full fn-arena)
              (sckat-full-in (append ws vs) fn-arena)
              (mv (list lhs a1 (car full) (cadr full)) fn-arena)))))
      out)))

(assert-event
 (let ((r (sckat-recover-pair (list 'not-an-event) (list *sckat-w1*))))
   (and (equal (fn-scka-intern-at (list 'not-an-event *sckat-w1*) 0) :bad)
        (not (equal (list (car r) (cadr r)) (list (caddr r) (cadddr r))))
        (eq (caddr r) :bad)
        (not (eq (car r) :bad)))))

; And its reachable positive witness without the load (the prefix's
; canonical arena sealed directly): the same extension and arena.
(assert-event
 (let ((r (sckat-recover-pair *sckat-prefix* (list *sckat-w3* *sckat-w4*))))
   (and (not (equal (fn-scka-intern-at (append *sckat-prefix* (list *sckat-w3* *sckat-w4*)) 0)
                    :bad))
        (equal (car r) (caddr r))
        (equal (cadr r) (cadddr r))
        (not (eq (car r) :bad)))))

; -----------------------------------------------------------------------------
; 6. The host's seal loop (fn-scka-seal-n-compose, fn-scka-seal-n-of-body):
; the body of the canonical payloads in a buffer, sealed in steps of N1 and
; N2 payloads, is the one loop of N1 + N2.  (OK I ARENA) of each.

(defun sckat-seal-steps (n1 n2 whole)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (out fn-octets)
      (let ((fn-octets (fn-octets-append-list (fn-scka-body *sckat-canon-payloads*) fn-octets)))
        (mv (with-local-stobj fn-arena
              (mv-let (out fn-arena)
                (if whole
                    (mv-let (ok i fn-arena)
                      (fn-scka-seal-n 0 (fn-octets-len fn-octets) (+ n1 n2) fn-octets fn-arena)
                      (mv (list ok i (sckat-arena-list 0 fn-arena)) fn-arena))
                  (mv-let (ok i fn-arena)
                    (fn-scka-seal-n 0 (fn-octets-len fn-octets) n1 fn-octets fn-arena)
                    (if ok
                        (mv-let (ok i fn-arena)
                          (fn-scka-seal-n i (fn-octets-len fn-octets) n2 fn-octets fn-arena)
                          (mv (list ok i (sckat-arena-list 0 fn-arena)) fn-arena))
                      (mv (list ok i (sckat-arena-list 0 fn-arena)) fn-arena))))
                out))
            fn-octets))
      out)))

(assert-event
 (and (equal (sckat-seal-steps 1 2 nil) (sckat-seal-steps 1 2 t))
      (equal (sckat-seal-steps 1 2 t)
             (list t (len (fn-scka-body *sckat-canon-payloads*)) *sckat-canon-payloads*))))

; Without "N1 is a natural": N1 = -1 seals nothing in its step, the one
; loop of N1 + N2 = 2 payloads one fewer than the steps' 3.
; (a value outside the guard: evaluated by the prover, not the guarded run)
(defthm sckat-seal-compose-needs-natural-n1
  (and (natp 3) (not (natp -1))
       (not (equal (sckat-seal-steps -1 3 nil) (sckat-seal-steps -1 3 t))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; fn-scka-recover-rows-rii-is-recover-rows (no hypothesis; keystone-audit
; 2026-09-27: it had no witness).  The host's open from a checkpoint interns
; the suffix and extends with fn-rii-sco-extend (host/store-node-host.lisp
; fn-store-sn-recover-from-checkpoint): the body of fn-scka-recover-rows-rii.
; Over the whole history from the emptied arena, and over a history the
; intern refuses, both entries give the same extension and arena.
(defun sckat-full-rii-in (history fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((fn-arena (fn-arena-clear fn-arena)))
    (mv-let (opened fn-arena)
      (fn-scka-recover-rows-rii (fn-sco-capture *sckat-configs* nil) *sckat-configs*
                                history fn-arena)
      (mv (list opened (sckat-arena-list 0 fn-arena)) fn-arena))))
(defun sckat-full-both (history)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (mv-let (full fn-arena)
        (sckat-full-in history fn-arena)
        (mv-let (rii fn-arena)
          (sckat-full-rii-in history fn-arena)
          (mv (list full rii) fn-arena)))
      out)))
(assert-event
 (let ((r (sckat-full-both (append *sckat-history* (list *sckat-w4*)))))
   (and (not (eq (car (car r)) :bad))
        (equal (take 3 (cadr (car r))) *sckat-canon-payloads*)
        (equal (len (cadr (car r))) 4)
        (equal (car r) (cadr r)))))
(assert-event
 (let ((r (sckat-full-both (list *sckat-w4* 'not-an-event))))
   (and (eq (car (car r)) :bad)
        (equal (car r) (cadr r)))))

; -----------------------------------------------------------------------------
; PRF-129's disk half: fn-scka-publication-setup-plans-within-the-disk (the
; setup host/owner-host.lisp fn-owner-sco-prepare and host/store-node-host.lisp
; fn-store-sco-publish-setup call before allocating anything).
; REACHABLE: a ground capture, an arena run of 100 octets; with the budget the
; whole estimate and the free octets the estimate plus the reservation the
; setup plans that estimate, which is 100 plus the tables' file octets; one
; octet less free (or budget) defers by name.
(defconst *sckat-pnext* (fn-sco-capture *sckat-configs* nil))
(defconst *sckat-pest*
  (nth 6 (fn-scka-publication-setup *sckat-pnext* 9 "rev-test" nil *sckat-seg* 0 0 100)))
(defconst *sckat-psetup*
  (fn-scka-publication-setup *sckat-pnext* 9 "rev-test" nil *sckat-seg* *sckat-pest*
                             (+ *sckat-pest* (fn-smr-reserve-octets)) 100))
(assert-event
 (and (not (equal (car *sckat-psetup*) :unencodable))
      (equal (nth 6 *sckat-psetup*)
             (+ 100 (len (fn-sct-file-octets (fn-sct-table-programs (nth 1 *sckat-psetup*)
                                                                    (nth 4 *sckat-psetup*))
                                             *sckat-seg* 3))))
      (< 100 *sckat-pest*)
      (equal (car *sckat-psetup*) (list :plan *sckat-pest*))
      (<= *sckat-pest* *sckat-pest*)
      (natp (+ *sckat-pest* (fn-smr-reserve-octets)))
      (equal (fn-ockp-space (+ *sckat-pest* (fn-smr-reserve-octets))) *sckat-pest*)))
(assert-event
 (equal (car (fn-scka-publication-setup *sckat-pnext* 9 "rev-test" nil *sckat-seg* *sckat-pest*
                                        (+ *sckat-pest* (fn-smr-reserve-octets) -1) 100))
        (list :deferred :exceeds-space *sckat-pest* (1- *sckat-pest*))))
(assert-event
 (equal (car (fn-scka-publication-setup *sckat-pnext* 9 "rev-test" nil *sckat-seg* (1- *sckat-pest*)
                                        (+ *sckat-pest* (fn-smr-reserve-octets)) 100))
        (list :deferred :exceeds-budget *sckat-pest* (1- *sckat-pest*))))
(assert-event
 (equal (car (car (fn-scka-publication-setup *sckat-pnext* 9 "rev-test" nil *sckat-seg*
                                             *sckat-pest* nil 100)))
        :deferred))

; HYPOTHESIS REMOVAL (the one hypothesis): a capture whose row the codec
; refuses (a natural of 2^2040).  The setup is :unencodable (the hypothesis
; fails); the plan does not happen although every bound on the right of the
; iff holds (an estimate of 0 within the budget and the space): the
; conclusion fails.
; (car (car SETUP)) of the theorem, total: the car of an atom is NIL.
(defun sckat-car-car (x)
  (declare (xargs :guard t))
  (if (consp x) (if (consp (car x)) (car (car x)) nil) nil))
(defthm sckat-car-car-is-car-car (equal (sckat-car-car x) (car (car x))))
(defconst *sckat-bad-next* (fn-sco-capture *sckat-configs* (list (expt 2 2040))))
(defconst *sckat-bad-psetup*
  (fn-scka-publication-setup *sckat-bad-next* 9 "rev-test" nil *sckat-seg* 1000 100000 0))
(assert-event (equal (car *sckat-bad-psetup*) :unencodable))
(assert-event
 (not (iff (equal (sckat-car-car *sckat-bad-psetup*) :plan)
           (and (<= (nth 6 *sckat-bad-psetup*) 1000)
                (natp 100000)
                (<= (nth 6 *sckat-bad-psetup*) (fn-ockp-space 100000))))))
(must-fail
 (defthm sckat-plans-within-the-disk-without-encodable
   (let* ((setup (fn-scka-publication-setup next frontier revision log seg budget free alen))
          (estimate (nth 6 setup)))
     (iff (equal (car (car setup)) :plan)
          (and (<= estimate budget) (natp free) (<= estimate (fn-ockp-space free)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-scka-publication-setup fn-ockp-setup fn-ockp-space fn-ockp-decide)
                            (fn-sct-file-octets fn-sct-table-programs fn-ockp-counts
                             fn-ockp-tables-encodablep))))))
