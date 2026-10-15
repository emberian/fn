; A5's controls precede the universal proof in log-checkpoint-composite.
; All large-frame shortcuts have unconditional equalities to the full formula.
(in-package "ACL2")
(include-book "lc-cold-id5-tests")
(include-book "lc-cold-control-fallback-tests")
(include-book "lc-open-composite-counterexample-tests")
(include-book "lc-open-composite-limit-counterexample-tests")
(local (include-book "std/lists/take" :dir :system))

(defun lca5-observe (disk r mode configs frontier max-conns segs outcome count k fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let* ((header (fn-lc-cold-adopted-header disk r mode))
        (max (fn-lc-tail-max header))
        (selection (ec-call (fn-lc-open-selection disk r mode count segs header)))
        (before (fn-lbc-p fn-lbc))
        (prefix (+ (* 2 (fn-lc-root-slot-octets))
                   (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets))))
        (factor (mbe :logic (+ 1 k) :exec (+ 1 (if (acl2-numberp k) k 0)))))
  (mv-let (answer fn-lbc nextdisk nextsegs trace oc)
   (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)
   (declare (ignore nextdisk nextsegs oc))
   (let* ((requested (fn-lc-read-octets trace))
          (allowed (* factor (fn-lc-entry-octets-bound max)))
          (allowed (+ prefix allowed)))
    (mv (list before (fn-lc-segsp segs)
          (equal (mbe :logic (car selection) :exec (fn-lc-head selection)) :checkpoint) (natp k)
          (mbe :logic (<= (len (fn-lc-selection-tail selection)) k)
               :exec (not (fn-ag-less k (len (ec-call (fn-lc-selection-tail selection))))))
          answer requested allowed
          (mbe :logic (<= requested allowed)
               :exec (not (fn-ag-less allowed requested)))
          prefix (fn-lc-header-next-id header)
          (fn-lc-header-next-id (fn-lc-adopted-header disk r mode))) fn-lbc)))))

(local (defthm lcx-len-make-list-ac
 (equal (len (make-list-ac n value acc)) (+ (nfix n) (len acc)))
 :hints (("Goal" :induct (make-list-ac n value acc)
   :in-theory (union-theories (theory 'minimal-theory)
     '((:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
       (:COMPOUND-RECOGNIZER ZP-COMPOUND-RECOGNIZER)
       (:DEFINITION FIX)
       (:DEFINITION LEN)
       (:DEFINITION MAKE-LIST-AC)
       (:DEFINITION NFIX)
       (:DEFINITION SYNP)
       (:EXECUTABLE-COUNTERPART BINARY-+)
       (:INDUCTION MAKE-LIST-AC)
       (:REWRITE CDR-CONS)
       (:REWRITE COMMUTATIVITY-2-OF-+)
       (:REWRITE COMMUTATIVITY-OF-+)
       (:REWRITE FOLD-CONSTS-IN-+)
       (:REWRITE PGS-X-NFIX-WHEN-NATP)
       (:REWRITE UNICITY-OF-0)
       (:TYPE-PRESCRIPTION LEN)))))))

(local (defthm lcx-bytes-length
 (equal (len (lcx-terminal-bytes)) 16777259)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
     '((:DEFINITION LCX-TERMINAL-BYTES)
       (:EXECUTABLE-COUNTERPART BINARY-+)
       (:EXECUTABLE-COUNTERPART EQUAL)
       (:EXECUTABLE-COUNTERPART LEN)
       (:EXECUTABLE-COUNTERPART NFIX)
       (:REWRITE FN-LGC-LEN-APPEND)
       (:REWRITE LCX-LEN-MAKE-LIST-AC)))))))

(defun lca5p-frame ()
 (declare (xargs :guard t))
 (fn-lc-move-frame *fn-lg-genesis* 0 nil nil))

(defun lca5p-bytes ()
 (declare (xargs :guard t))
 (append (lca5p-frame) (lcx-terminal-bytes)))

(local (in-theory (disable lca5p-bytes)))

(verify-guards lca5-observe :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-head fn-ag-less fn-lc-entry-octets-bound fn-lg-batch-entry-bound max nfix
   (:executable-counterpart natp) (:executable-counterpart binary-+)
   (:executable-counterpart not) (:executable-counterpart zp)
   (:type-prescription len) (:type-prescription fn-lc-read-octets)))
 :use ((:instance completion-of-+ (x 1) (y k))))))

(defun lca5-fixture (kind count k)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((input (lco-id5-input 1))
        (disk (case kind (:page99 (lcc-fallback-disk))
                         (:late (lcc-late-fallback-disk))
                         (:wide (lco-wide-fallback-disk 1030))
                         (:divergence (lci-cold-pgs-different-root-disk))
                         (otherwise (fn-lc-at 0 input))))
        (segs (if (equal kind :one-terminal) '((0 (65) nil) (1 nil nil))
                (fn-lc-at 3 input))))
  (with-local-stobj fn-lbc
   (mv-let (out fn-lbc)
    (lca5-observe disk :lc :eager (fn-lc-at 2 input) 8 4 segs
                  (make-list 1100 :initial-element :ok) count k fn-lbc) out))))

(verify-guards lca5-fixture)

(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
 (assert-event (let ((o (lca5-fixture :empty 0 0)))
  (and (nth 0 o) (nth 1 o) (nth 2 o) (nth 3 o) (nth 4 o) (nth 8 o))))
 (assert-event (let ((o (lca5-fixture :page99 0 0)))
  (and (nth 0 o) (nth 1 o) (nth 2 o) (nth 3 o) (nth 4 o) (nth 8 o))))
 (assert-event (let ((o (lca5-fixture :late 0 0)))
  (and (nth 0 o) (nth 1 o) (nth 2 o) (nth 3 o) (nth 4 o) (nth 8 o))))
 ; No semantic validity premise: this is the exact legacy selector result.
 (assert-event (let ((o (lca5-fixture :divergence 0 0)))
  (and (equal (nth 5 o) :ok) (not (nth 2 o)) (nth 8 o)
       (equal (nth 10 o) 1) (equal (nth 11 o) 100))))
 ; Proposed standing-rule DROP of NATP K: the length comparison already
 ; enforces the ordered lower bound; a non-natural positive K still works.
 (assert-event (let ((o (lca5-fixture :empty 0 1/2)))
  (and (nth 2 o) (not (nth 3 o)) (nth 4 o) (nth 8 o))))
 ; Removing the remaining tail-length hypothesis: one charged torn byte,
 ; K=-1, chosen checkpoint retained, and zero entry allowance.
 (assert-event (let ((o (lca5-fixture :one-terminal 0 -1)))
  (and (nth 2 o) (not (nth 4 o)) (not (nth 8 o)))))
 (value-triple (list (lca5-fixture :empty 0 0) (lca5-fixture :page99 0 0)
                    (lca5-fixture :late 0 0) (lca5-fixture :divergence 0 0)
                    (lca5-fixture :one-terminal 0 -1))))

(local (defthm lcx-move-kind-must-match
 (implies (not (equal (nth 5 frame) *fn-lc-move-kind*))
          (not (fn-lc-move-framep frame prev max)))
 :hints (("Goal" :use ((:instance fn-lc-open-kind-is-header-kind (slice frame)))
  :in-theory (union-theories (theory 'minimal-theory)
     '((:DEFINITION FN-LC-MOVE-FRAMEP)
       (:DEFINITION NOT)
       (:REWRITE FN-LC-OPEN-KIND-IS-HEADER-KIND)
       (:TYPE-PRESCRIPTION FN-FRAME-RESULT-OKP)))))))

(local (defthm lcx-record-kind-must-match
 (implies (not (equal (nth 5 frame) *fn-lc-record-kind*))
          (not (fn-lc-record-framep frame prev max)))
 :hints (("Goal" :use ((:instance fn-lc-open-kind-is-header-kind (slice frame)))
  :in-theory (union-theories (theory 'minimal-theory)
     '((:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
       (:DEFINITION FN-LC-RECORD-FRAMEP)
       (:DEFINITION NFIX)
       (:DEFINITION NOT)
       (:EXECUTABLE-COUNTERPART BINARY-+)
       (:REWRITE FN-LC-DROP-IS-NTHCDR)
       (:REWRITE FN-LC-OPEN-KIND-IS-HEADER-KIND)
       (:REWRITE FN-LC-TAKE-IS-TAKE)
       (:REWRITE FN-LGC-NTHCDR-NTHCDR)
       (:TYPE-PRESCRIPTION FN-FRAME-RESULT-OKP)))))))

(local (defthm lcx-nth-of-take
 (implies (and (natp i) (natp n) (< i n))
  (equal (nth i (take n bytes)) (nth i bytes)))
 :hints (("Goal" :induct (fn-lc-split-nth-induction n i bytes)
  :in-theory (union-theories (theory 'minimal-theory)
     '((:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
       (:COMPOUND-RECOGNIZER ZP-COMPOUND-RECOGNIZER)
       (:DEFINITION NATP)
       (:DEFINITION NOT)
       (:DEFINITION NTH)
       (:DEFINITION TAKE)
       (:EXECUTABLE-COUNTERPART CONSP)
       (:EXECUTABLE-COUNTERPART EQUAL)
       (:EXECUTABLE-COUNTERPART NOT)
       (:EXECUTABLE-COUNTERPART TAU-SYSTEM)
       (:EXECUTABLE-COUNTERPART ZP)
       (:INDUCTION FN-LC-SPLIT-NTH-INDUCTION)
       (:REWRITE CAR-OF-TAKE)
       (:REWRITE CDR-CONS)
       (:REWRITE CONSP-OF-TAKE)
       (:REWRITE DEFAULT-CAR)
       (:REWRITE DEFAULT-CDR)
       (:REWRITE PGS-X-NFIX-WHEN-NATP)
       (:TYPE-PRESCRIPTION TAKE)
       (:TYPE-PRESCRIPTION ZP)))))))

(local (defthm lcx-rotation-is-terminal
 (implies (and (equal (fn-lg-declared-len bytes) n)
               (posp n) (<= n (len bytes))
               (<= n (fn-lc-entry-octets-bound max))
               (equal (nth 5 bytes) *fn-lg-rotation-kind*)
               (< 5 n) (posp fuel))
  (equal (fn-lc-scan-bytes bytes prev unit max fuel)
         (list :terminal nil (list n) prev)))
 :rule-classes nil
 :hints (("Goal" :cases ((consp bytes))
  :expand ((fn-lc-scan-bytes bytes prev unit max fuel))
  :in-theory (union-theories (theory 'minimal-theory)
     '((:DEFINITION FN-LC-SCAN-BYTES)
       (:DEFINITION LEN)
       (:DEFINITION NATP)
       (:DEFINITION NOT)
       (:DEFINITION POSP)
       (:DEFINITION ZP)
       (:EXECUTABLE-COUNTERPART <)
       (:EXECUTABLE-COUNTERPART EQUAL)
       (:EXECUTABLE-COUNTERPART INTEGERP)
       (:REWRITE LCX-MOVE-KIND-MUST-MATCH)
       (:REWRITE LCX-NTH-OF-TAKE)
       (:REWRITE LCX-RECORD-KIND-MUST-MATCH)))))))

(local (defthm lcx-octets-make-list-ac
 (implies (fn-cbor-octet-listp acc)
          (fn-cbor-octet-listp (make-list-ac n 0 acc)))
 :hints (("Goal" :induct (make-list-ac n 0 acc)
          :in-theory (union-theories (theory 'minimal-theory)
     '((:DEFINITION NOT)
       (:EXECUTABLE-COUNTERPART TAU-SYSTEM)
       (:INDUCTION MAKE-LIST-AC)
       (:REWRITE FN-LGX-MAKE-LIST-AC-IS-ZEROS)
       (:REWRITE FN-LGX-ZEROS-CONS-ZERO)
       (:TYPE-PRESCRIPTION FN-CBOR-OCTET-LISTP)))))))

(local (defthm lcx-bytes-octets
 (fn-cbor-octet-listp (lcx-terminal-bytes))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
     '((:DEFINITION BINARY-APPEND)
       (:DEFINITION FN-CBOR-OCTET-LISTP)
       (:DEFINITION LCX-TERMINAL-BYTES)
       (:EXECUTABLE-COUNTERPART CAR)
       (:EXECUTABLE-COUNTERPART CDR)
       (:EXECUTABLE-COUNTERPART CONSP)
       (:EXECUTABLE-COUNTERPART FN-CBOR-OCTET-LISTP)
       (:EXECUTABLE-COUNTERPART FN-CBOR-OCTETP)
       (:REWRITE CAR-CONS)
       (:REWRITE CDR-CONS)
       (:REWRITE FN-CP-APPEND-NIL-LEFT)
       (:REWRITE LCX-OCTETS-MAKE-LIST-AC)
       (:TYPE-PRESCRIPTION FN-CBOR-OCTET-LISTP)))))))

(local (defthm lcx-bytes-header
 (and (equal (fn-lg-declared-len (lcx-terminal-bytes)) 16777259)
      (equal (nth 5 (lcx-terminal-bytes)) *fn-lg-rotation-kind*)
      (consp (lcx-terminal-bytes)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
     '((:DEFINITION BINARY-APPEND)
       (:DEFINITION FN-BS-TAKE)
       (:DEFINITION FN-LG-DECLARED-LEN)
       (:DEFINITION LCX-TERMINAL-BYTES)
       (:DEFINITION LEN)
       (:DEFINITION NTHCDR)
       (:EXECUTABLE-COUNTERPART <)
       (:EXECUTABLE-COUNTERPART BINARY-+)
       (:EXECUTABLE-COUNTERPART CAR)
       (:EXECUTABLE-COUNTERPART CDR)
       (:EXECUTABLE-COUNTERPART CONS)
       (:EXECUTABLE-COUNTERPART CONSP)
       (:EXECUTABLE-COUNTERPART EQUAL)
       (:EXECUTABLE-COUNTERPART FN-CBOR-OCTET-LISTP)
       (:EXECUTABLE-COUNTERPART FN-CBOR-U32-FROM)
       (:EXECUTABLE-COUNTERPART LEN)
       (:EXECUTABLE-COUNTERPART NFIX)
       (:EXECUTABLE-COUNTERPART TAU-SYSTEM)
       (:EXECUTABLE-COUNTERPART ZP)
       (:REWRITE CAR-CONS)
       (:REWRITE CDR-CONS)
       (:REWRITE FN-CP-APPEND-NIL-LEFT)
       (:REWRITE FN-LC-NTH-3-ALIAS)
       (:REWRITE LCX-LEN-MAKE-LIST-AC)
       (:REWRITE NTH-ADD1)))))))

(local (defthm lca5-terminal-scan-any-fuel
 (implies (posp fuel)
  (equal (fn-lc-scan-bytes (lcx-terminal-bytes) prev 1 16777217 fuel)
   (list :terminal nil '(16777259) prev)))
 :hints (("Goal" :use ((:instance lcx-rotation-is-terminal
  (bytes (lcx-terminal-bytes)) (unit 1) (max 16777217)
  (n 16777259)))
 :in-theory (union-theories (theory 'minimal-theory)
  '(lcx-bytes-length lcx-bytes-header posp
    (:executable-counterpart fn-lc-entry-octets-bound)
    (:executable-counterpart <) (:executable-counterpart equal)
    (:executable-counterpart not)))))))

(defun lca5p-segs ()
 (declare (xargs :guard t)) (list (list 0 (lca5p-bytes) nil)))

(local (in-theory (disable lca5p-segs)))

(local (defthm lca5p-bytes-length
 (equal (len (lca5p-bytes)) 16777345)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '((:definition lca5p-bytes) fn-lgc-len-append lcx-bytes-length
   (:executable-counterpart lca5p-frame) (:executable-counterpart len)
   (:executable-counterpart binary-+)))))))

(local (defthm lca5p-scan
 (equal (fn-lc-scan-bytes (lca5p-bytes) *fn-lg-genesis* 1 16777217
                         16777345)
  (list :terminal (list (fn-lc-move-event (lca5p-frame) 16777217))
        (list (len (lca5p-frame)) 16777259) (fn-lg-trailer (lca5p-frame))))
 :hints (("Goal"
  :expand ((:free (bytes)
    (fn-lc-scan-bytes bytes *fn-lg-genesis* 1 16777217 16777345)))
  :in-theory (union-theories (theory 'minimal-theory)
   '((:definition lca5p-bytes) (:executable-counterpart lca5p-frame)
     (:executable-counterpart len) (:definition binary-append)
     (:definition fn-lg-declared-len) (:definition fn-bs-take)
     (:executable-counterpart fn-cbor-octet-listp)
     (:executable-counterpart fn-cbor-u32-from)
     (:executable-counterpart fn-lc-entry-octets-bound)
     (:executable-counterpart fn-lc-move-framep)
     (:executable-counterpart fn-lc-move-event)
     (:executable-counterpart fn-lg-trailer)
     (:executable-counterpart fn-lg-pad-len)
     (:definition take) (:definition nthcdr) (:definition nfix)
     (:definition natp) (:definition posp) (:definition len)
     (:executable-counterpart nth) (:definition posp) car-cons cdr-cons fn-lgc-len-append lcx-bytes-length lca5-terminal-scan-any-fuel
     (:executable-counterpart equal) (:executable-counterpart <)
     (:executable-counterpart zp) (:executable-counterpart not)
     (:executable-counterpart binary-+) (:executable-counterpart binary-*)
     (:executable-counterpart nfix)))))))

(local (defthm lca5p-tail-scan
 (implies (and (equal (fn-lc-header-S header) (list 0 0 0 8 *fn-lg-genesis*))
               (equal (fn-lc-tail-max header) 16777217)
               (equal (fn-lc-tail-unit header) 1))
  (equal (fn-lc-tail-scan (lca5p-segs) header)
   (list :terminal (list (fn-lc-move-event (lca5p-frame) 16777217))
         '(86 16777259) (fn-lg-trailer (lca5p-frame)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-insert-segment fn-lc-ordered-segments fn-lc-scan-segments
   fn-lc-tail-scan (:definition lca5p-segs) nthcdr nfix nth car-cons cdr-cons
   lca5p-bytes-length lca5p-scan
   (:executable-counterpart fn-lc-ordered-segments)
   (:executable-counterpart fn-lg-trailer) (:executable-counterpart fn-lc-move-event)
   (:executable-counterpart lca5p-frame) (:executable-counterpart <)
   (:executable-counterpart nfix) (:executable-counterpart equal)
   (:executable-counterpart len) (:executable-counterpart not)
   (:executable-counterpart zp)))))))

(local (defthm lca5p-cold-requests
 (implies (lcx-metadata-ready-p input)
  (equal (fn-lc-cold-tail-entries (car input) :lc :eager (lca5p-segs))
         '(86 16777259)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '((:definition lcx-metadata-ready-p) fn-lc-cold-tail-entries fn-lc-at-is-nth
   lca5p-tail-scan fn-lc-head fn-lc-rest default-car default-cdr nth car-cons cdr-cons (:executable-counterpart zp)))))))

(local (defthm lca5p-read-of-append
 (equal (fn-lc-read-octets (append a b))
        (+ (fn-lc-read-octets a) (fn-lc-read-octets b)))
 :hints (("Goal" :induct (fn-lc-read-octets a)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-read-octets binary-append fn-lc-head fn-lc-at-is-nth
   (:induction fn-lc-read-octets) car-cons cdr-cons
   associativity-of-+ commutativity-of-+ fold-consts-in-+))))))

(local (defthm lca5-ready-facts
 (implies (lcx-metadata-ready-p input)
  (let ((trace (nth 5 (fn-lc-cold-select (car input) :lc :eager))))
   (and (equal (fn-lc-cold-adopted-header (car input) :lc :eager) (cadr input))
        (equal (fn-lc-adopted-header (car input) :lc :eager) (cadr input))
        (equal (fn-lc-header-of-open (pgs-open (car input) :lc :eager)) (cadr input))
        (equal (fn-lc-tail-max (cadr input)) 16777217)
        (true-listp trace) (equal (len trace) 8)
        (equal (fn-lc-read-octets trace) 98564)
        (equal (len (fn-lc-open-metadata-pages (car input) :lc :eager)) 6))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '((:definition lcx-metadata-ready-p) fn-lc-at-is-nth fn-lc-nth-1-alias
   fn-lc-head nth default-car default-cdr car-cons cdr-cons
   (:executable-counterpart zp)))))))

(local (defthm lca5p-program-cost
 (implies (lcx-metadata-ready-p input)
  (let ((p (fn-lc-open-program (car input) :lc :eager (lca5p-segs))))
   (and (true-listp p) (equal (len p) 10)
        (equal (fn-lc-read-octets p) 16875909))))
 :hints (("Goal" :use (lca5p-cold-requests lca5-ready-facts) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-open-program fn-lc-open-tail-program
   fn-lc-read-octets fn-lc-at-is-nth fn-lc-join-is-append
   fn-lc-head fn-lc-rest default-car default-cdr lca5p-cold-requests lca5p-read-of-append
   fn-lgc-len-append true-listp-append car-cons cdr-cons nth len
   (:executable-counterpart fn-lc-open-tail-program)
   (:executable-counterpart fn-lc-read-octets)
   (:executable-counterpart binary-+) (:executable-counterpart nfix)
   (:executable-counterpart zp) (:executable-counterpart equal)))))))

(local (defthm lca5-open-trace-by-definition
 (equal (mv-nth 4 (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
        (take (min (+ 1 (fn-lc-outcome-ok-count outcome (len (fn-lc-open-program disk r mode segs))))
                   (len (fn-lc-open-program disk r mode segs)))
              (fn-lc-open-program disk r mode segs)))
 :hints (("Goal" :in-theory
  (union-theories (theory 'minimal-theory)
     '((:DEFINITION FN-LC-OPEN)
       (:DEFINITION MIN)
       (:REWRITE FN-LC-TAKE-IS-TAKE)))))))

(local (defthm lca5p-trace-cost
 (implies (lcx-metadata-ready-p input)
  (equal (fn-lc-read-octets
    (mv-nth 4 (fn-lc-open (car input) :lc :eager configs frontier max-conns
                         (lca5p-segs) '(:ok :ok :ok :ok :ok :ok :ok :ok :ok :ok) fn-lbc)))
         16875909))
 :hints (("Goal" :use (lca5p-program-cost)
 :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-open-trace-by-definition
   (:executable-counterpart fn-lc-outcome-ok-count) (:executable-counterpart binary-+)
   (:executable-counterpart min) (:executable-counterpart equal)
   adt-true-list-fix-when-true-listp take-of-len-free))))))

(defun lca5-compact (disk r mode configs frontier max-conns segs outcome count k fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (mv-let (o fn-lbc)
  (lca5-observe disk r mode configs frontier max-conns segs outcome count k fn-lbc)
  (mv (list (fn-lc-at 2 o) (fn-lc-at 4 o) (fn-lc-at 6 o)
            (fn-lc-at 7 o) (fn-lc-at 9 o)) fn-lbc)))

(defun-nx lca5-formula-vector (disk r mode configs frontier max-conns segs outcome count k fn-lbc)
 (let* ((header (fn-lc-cold-adopted-header disk r mode))
        (max (fn-lc-tail-max header))
        (selection (fn-lc-open-selection disk r mode count segs header))
        (out (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc))
        (prefix (+ (* 2 (fn-lc-root-slot-octets))
                   (* (len (fn-lc-open-metadata-pages disk r mode)) (fn-lc-page-octets)))))
  (list (equal (car selection) :checkpoint)
        (<= (len (fn-lc-selection-tail selection)) k)
        (fn-lc-read-octets (mv-nth 4 out))
        (+ prefix (* (+ 1 k) (fn-lc-entry-octets-bound max))) prefix)))

(local (defthm lca5-compact-is-the-formula-vector-by-definition
 (equal (mv-nth 0 (lca5-compact disk r mode configs frontier max-conns segs outcome count k fn-lbc))
        (lca5-formula-vector disk r mode configs frontier max-conns segs outcome count k fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-compact lca5-formula-vector lca5-observe fn-lc-at-is-nth fn-lc-head
   nth mv-nth car-cons cdr-cons (:executable-counterpart zp)))))))

(local (defthm lca5p-formula-vector
 (implies (lcx-metadata-ready-p input)
  (equal (lca5-formula-vector (car input) :lc :eager configs frontier max-conns
           (lca5p-segs) '(:ok :ok :ok :ok :ok :ok :ok :ok :ok :ok) -1 0 fn-lbc)
         '(nil t 16875909 16875823 98564)))
 :hints (("Goal" :use (lca5-ready-facts lca5p-trace-cost)
 :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-formula-vector fn-lc-open-selection fn-lc-selection-tail
   fn-lc-root-slot-octets fn-lc-page-octets
   (:executable-counterpart fn-lc-entry-octets-bound)
   (:executable-counterpart natp) (:executable-counterpart len)
   (:executable-counterpart binary-+) (:executable-counterpart binary-*)
   (:executable-counterpart <) (:executable-counterpart equal)
   (:executable-counterpart zp) nth car-cons cdr-cons))))))

(local (defthm lca5-limit-old-vector
 (implies (lcx-metadata-ready-p input)
  (equal (lcx-a4-logical-observation input fn-lbc)
         (list (fn-lbc-p fn-lbc) t t t t 16875823 16875822 nil)))
 :hints (("Goal" :use lcx-a4-scalar-observation-is-the-full-formula
 :in-theory (union-theories (theory 'minimal-theory)
 '(lcx-a4-scalar-observation mv-nth car-cons cdr-cons
   (:executable-counterpart zp)))))))

(defun lca5-fast-compact (disk r mode configs frontier max-conns segs outcome count k fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (let ((input (lcx-limit-input)))
  (cond
   ((and (equal r :lc) (equal mode :eager) (equal k 0)
         (equal disk (fn-lc-at 0 input)) (lcx-metadata-ready-p input)
         (equal count -1) (equal outcome '(:ok :ok :ok :ok :ok :ok :ok :ok :ok :ok))
         (equal segs (lca5p-segs)))
    (mv '(nil t 16875909 16875823 98564) fn-lbc))
   ((and (equal r :lc) (equal mode :eager) (equal k 0)
         (equal disk (fn-lc-at 0 input)) (lcx-metadata-ready-p input)
         (equal count 0) (equal outcome '(:ok :ok :ok :ok :ok :ok :ok :ok))
         (equal configs (fn-lc-at 2 input)) (equal frontier 8) (equal max-conns 4)
         (equal segs (lcx-limit-segs)))
    (mv '(t t 16875823 16875823 98564) fn-lbc))
   (t (lca5-compact disk r mode configs frontier max-conns segs outcome count k fn-lbc)))))

(local (defthm lca5-limit-fields
 (implies (lcx-metadata-ready-p input)
  (and (equal (nth 2 (lcx-a4-logical-observation input fn-lbc)) t)
       (equal (nth 4 (lcx-a4-logical-observation input fn-lbc)) t)
       (equal (nth 5 (lcx-a4-logical-observation input fn-lbc)) 16875823)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-limit-old-vector nth car-cons cdr-cons
   (:executable-counterpart zp)))))))

(local (defthm lca5-limit-formula-vector
 (implies (lcx-metadata-ready-p input)
  (equal (lca5-formula-vector (car input) :lc :eager (caddr input) 8 4
           (lcx-limit-segs) '(:ok :ok :ok :ok :ok :ok :ok :ok) 0 0 fn-lbc)
         '(t t 16875823 16875823 98564)))
 :hints (("Goal" :use (lca5-ready-facts lca5-limit-fields)
 :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-formula-vector lcx-a4-logical-observation fn-lc-root-slot-octets fn-lc-page-octets
   (:executable-counterpart fn-lc-entry-octets-bound)
   (:executable-counterpart binary-+) (:executable-counterpart binary-*)
   (:executable-counterpart len) (:executable-counterpart natp)
   nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart equal) (:executable-counterpart <)))))))

(local (defthm lca5-compact-car-is-the-formula-vector-by-definition
 (equal (car (lca5-compact disk r mode configs frontier max-conns segs outcome count k fn-lbc))
        (lca5-formula-vector disk r mode configs frontier max-conns segs outcome count k fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-compact lca5-formula-vector lca5-observe fn-lc-at-is-nth fn-lc-head
   nth mv-nth car-cons cdr-cons (:executable-counterpart zp)))))))

(defthm lca5-fast-compact-is-the-formula-vector
 (equal (mv-nth 0 (lca5-fast-compact disk r mode configs frontier max-conns segs outcome count k fn-lbc))
        (lca5-formula-vector disk r mode configs frontier max-conns segs outcome count k fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '((:type-prescription lcx-limit-input) (:type-prescription lca5-compact) lca5-fast-compact lca5-compact-car-is-the-formula-vector-by-definition
   lca5-limit-formula-vector lca5p-formula-vector
   fn-lc-at-is-nth fn-lc-nth-2-alias nth mv-nth car-cons cdr-cons default-car
   (:executable-counterpart zp))))))

(local (defthm lca5-vector-prefix-natp
 (natp (nth 4 (mv-nth 0 (lca5-fast-compact disk r mode configs frontier max-conns segs outcome count k fn-lbc))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lca5-fast-compact-is-the-formula-vector lca5-formula-vector nth mv-nth
   natp car-cons cdr-cons (:executable-counterpart zp)
   fn-lc-root-slot-octets fn-lc-page-octets (:type-prescription len)))))))

(defun lca5-tooth (which disk r mode configs frontier max-conns segs outcome count k fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (mv-let (v fn-lbc)
  (lca5-fast-compact disk r mode configs frontier max-conns segs outcome count k fn-lbc)
  (mv (case which
       (:chosen (fn-lc-at 0 v)) (:tail (fn-lc-at 1 v))
       (:oldmax
        (let* ((factor (mbe :logic (+ 1 k) :exec (+ 1 (if (acl2-numberp k) k 0))))
               (bound (+ (fn-lc-at 4 v) (* factor 16777258))))
         (not (fn-ag-less bound (fn-lc-at 2 v)))))
       (otherwise (not (fn-ag-less (fn-lc-at 3 v) (fn-lc-at 2 v))))) fn-lbc)))

(local (defthm lca5-vector-prefix-car-natp
 (natp (nth 4 (car (lca5-fast-compact disk r mode configs frontier max-conns segs outcome count k fn-lbc))))
 :hints (("Goal" :use lca5-vector-prefix-natp
 :in-theory (union-theories (theory 'minimal-theory)
 '(mv-nth nth (:type-prescription lca5-fast-compact)
   (:executable-counterpart zp)))))))

(verify-guards lca5-tooth
 :hints (("Goal" :use (lca5-vector-prefix-car-natp (:instance completion-of-+ (x 1) (y k)))
 :in-theory (union-theories (theory 'minimal-theory)
 '((:type-prescription lca5-fast-compact) fn-lc-at-is-nth natp mv-nth lca5-vector-prefix-natp (:executable-counterpart equal)
   (:executable-counterpart zp) (:type-prescription natp))))))

(defun lca5-large-control (prefixp)
 (declare (xargs :guard t))
 (let* ((input (lcx-limit-input))
        (segs (if prefixp (lca5p-segs) (lcx-limit-segs)))
        (outcome (if prefixp '(:ok :ok :ok :ok :ok :ok :ok :ok :ok :ok)
                    '(:ok :ok :ok :ok :ok :ok :ok :ok))))
  (with-local-stobj fn-lbc
   (mv-let (v fn-lbc)
    (lca5-fast-compact (fn-lc-at 0 input) :lc :eager (fn-lc-at 2 input) 8 4
                      segs outcome (if prefixp -1 0) 0 fn-lbc) v))))

(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
 (assert-event (lcx-metadata-ready-p (lcx-limit-input)))
 (assert-event (equal (lca5-large-control t) '(nil t 16875909 16875823 98564)))
 (assert-event (equal (lca5-large-control nil) '(t t 16875823 16875823 98564))))

(defthm lca5-fast-compact-car-is-the-formula-vector
 (equal (car (lca5-fast-compact disk r mode configs frontier max-conns segs outcome count k fn-lbc))
        (lca5-formula-vector disk r mode configs frontier max-conns segs outcome count k fn-lbc))
 :hints (("Goal" :use lca5-fast-compact-is-the-formula-vector
 :in-theory (union-theories (theory 'minimal-theory)
 '(mv-nth nth (:type-prescription lca5-fast-compact)
   (:executable-counterpart zp))))))

(defun lca5-oldmax-mutant-control ()
 (declare (xargs :guard t))
 (let ((input (lcx-limit-input)))
  (with-local-stobj fn-lbc
   (mv-let (yes fn-lbc)
    (lca5-tooth :oldmax (fn-lc-at 0 input) :lc :eager (fn-lc-at 2 input)
     8 4 (lcx-limit-segs) '(:ok :ok :ok :ok :ok :ok :ok :ok) 0 0 fn-lbc) yes))))

(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
 (assert-event (not (lca5-oldmax-mutant-control))))
