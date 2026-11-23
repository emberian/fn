; Layer C1c: maintained summaries of the installed view of runs
; (fn2-run-installed) for the sealer's whole-table scans. fn2-seal-live-runs
; and fn2-seal-free-rows count over every row, fn2-run-version is a maximum
; over every row, and fn2-seal-most-runs (sealer.lisp) recounts the table at
; each live row it meets: R + L*R row visits, 8,320 at R=128, L=64.
;
; A row changes only through fn2-run-install (free -> live), fn2-run-retire
; (live -> retired) and fn2-run-retired-next (retired -> retired or free),
; and each writes one row, so each count moves by at most one per
; transition. The laws below give the new count from the old one and the
; row's old and new contents alone: a maintained per-schema count and a
; maintained free count follow every transition in O(1), and so does a
; schema's version when a run with a greater identifier is installed (the
; seal's and C5's merge's invariant).
;
; The selector fn2-seal-most-counts reads a list of per-schema counts (S
; visits) and equals fn2-seal-most-runs, tie-breaking included, whenever the
; list matches fn2-seal-live-runs (fn2-seal-counts-match-p) and covers every
; live schema (fn2-seal-live-within-p). fn2-seal-live-histogram builds such
; a list in one pass over the rows (R visits; a live row's count is advanced
; by update-nth at its schema, at most S conses), fn2-seal-most-runs-fast
; composes the two, falling back to the scan when a live schema lies beyond
; MAX-SID, and fn2-seal-counts-bump keeps the list matching across every
; transition.
(in-package "ACL2")
(include-book "sealer")
(fn2-book-layer :c)

; ---------------------------------------------------------------------------
; Reading a row after one column write. The readers stay folded in the
; proofs below; every read of a written table goes through these.
(defconst *fn2-seal-columns*
 '(state schema run top slot gen unit counter entries okind oslot ogen filter funit fcounter ufirst ulast))
(defun fn2-seal-col (prefix column)
 (declare (xargs :verify-guards nil))
 (intern-in-package-of-symbol (concatenate 'string prefix (symbol-name column)) 'fn2-run-installed))
(defun fn2-seal-col-runes (columns)
 (declare (xargs :verify-guards nil))
 (if (atom columns) nil
  (let ((column (symbol-name (car columns))))
   (list* (fn2-seal-col "FN2-RUN-INSTALLED-" (car columns))
          (fn2-seal-col "FN2-RUN-INSTALLED-" (intern (concatenate 'string column "$AI") "ACL2"))
          (fn2-seal-col "FN2-RUN-INSTALLED-SET-" (intern (concatenate 'string column "-NTH") "ACL2"))
          (fn2-seal-col "FN2-RUN-INSTALLED-SET-" (intern (concatenate 'string column "-ROWS") "ACL2"))
          (fn2-seal-col-runes (cdr columns))))))
; The proofs below read only these tables' columns and the sealer's counts:
; they run in the boot theory and these rules, not the includer's.
(make-event
 `(local (in-theory (union-theories (theory 'ground-zero)
                                    '(fn2-seal-live-runs fn2-seal-free-rows fn2-run-version
                                      fn2-seal-most-better-p fn2-seal-live-within-p fn2-seal-most-by-schema
                                      (:type-prescription fn2-seal-live-runs-natp)
                                      (:type-prescription fn2-seal-free-rows-natp)
                                      (:type-prescription fn2-run-version-natp)
                                      ,@(fn2-seal-col-runes *fn2-seal-columns*))))))
(defun fn2-seal-row-events (read writers)
 (declare (xargs :verify-guards nil))
 (if (atom writers) nil
  (let ((reader (fn2-seal-col "FN2-RUN-INSTALLED-" read))
        (writer (fn2-seal-col "FN2-RUN-INSTALLED-SET-" (car writers))))
   (cons `(defthm ,(fn2-seal-col (concatenate 'string "FN2-SEAL-" (symbol-name read) "-OF-SET-") (car writers))
           (equal (,reader i (,writer r v fn2-run-installed))
                  ,(if (eq read (car writers))
                       `(if (equal (nfix i) (nfix r)) v (,reader i fn2-run-installed))
                     `(,reader i fn2-run-installed))))
         (fn2-seal-row-events read (cdr writers))))))
(defun fn2-seal-read-names (column reads)
 (declare (xargs :verify-guards nil))
 (if (atom reads) nil
  (cons (fn2-seal-col (concatenate 'string "FN2-SEAL-" (symbol-name (car reads)) "-OF-SET-") column)
        (fn2-seal-read-names column (cdr reads)))))
(make-event
 `(local (progn ,@(fn2-seal-row-events 'state *fn2-seal-columns*)
                ,@(fn2-seal-row-events 'schema *fn2-seal-columns*)
                ,@(fn2-seal-row-events 'run *fn2-seal-columns*)
                ,@(fn2-seal-row-events 'ufirst *fn2-seal-columns*)
                ,@(fn2-seal-row-events 'ulast *fn2-seal-columns*))))
(local (in-theory (disable fn2-run-installed-state fn2-run-installed-schema fn2-run-installed-run
                           fn2-run-installed-ufirst fn2-run-installed-ulast)))

; Row R lies among rows J.. (K) of TABLE; its contribution to the live runs
; of SID.
(defmacro fn2-seal-row-in (r k j table)
 `(and (natp ,j) (<= ,j ,r) (< ,r (+ ,j (nfix ,k))) (< ,r (fn2-run-installed-rows ,table))))
(defmacro fn2-seal-live-bit (state schema sid)
 `(if (and (equal ,state *fn2-run-installed-state-live*) (equal ,schema ,sid)) 1 0))

; ---------------------------------------------------------------------------
; One column write. A count moves by the written row's new contribution less
; its old one; a write to another column moves nothing.
(defthm fn2-seal-live-runs-of-set-state
 (implies (natp r)
  (equal (fn2-seal-live-runs k j sid (fn2-run-installed-set-state r v fn2-run-installed))
         (if (fn2-seal-row-in r k j fn2-run-installed)
             (+ (fn2-seal-live-runs k j sid fn2-run-installed)
                (fn2-seal-live-bit v (fn2-run-installed-schema r fn2-run-installed) sid)
                (- (fn2-seal-live-bit (fn2-run-installed-state r fn2-run-installed)
                                      (fn2-run-installed-schema r fn2-run-installed) sid)))
           (fn2-seal-live-runs k j sid fn2-run-installed))))
 :hints (("Goal" :induct (fn2-seal-live-runs k j sid fn2-run-installed))))
(defthm fn2-seal-live-runs-of-set-schema
 (implies (natp r)
  (equal (fn2-seal-live-runs k j sid (fn2-run-installed-set-schema r s fn2-run-installed))
         (if (fn2-seal-row-in r k j fn2-run-installed)
             (+ (fn2-seal-live-runs k j sid fn2-run-installed)
                (fn2-seal-live-bit (fn2-run-installed-state r fn2-run-installed) s sid)
                (- (fn2-seal-live-bit (fn2-run-installed-state r fn2-run-installed)
                                      (fn2-run-installed-schema r fn2-run-installed) sid)))
           (fn2-seal-live-runs k j sid fn2-run-installed))))
 :hints (("Goal" :induct (fn2-seal-live-runs k j sid fn2-run-installed))))
; (fn2-run-installed-put r (state v)) is this write.
(defthm fn2-seal-free-rows-of-put
 (implies (natp r)
  (equal (fn2-seal-free-rows k j (fn2-run-installed-put r (state v)))
         (if (fn2-seal-row-in r k j fn2-run-installed)
             (+ (fn2-seal-free-rows k j fn2-run-installed)
                (if (equal v *fn2-run-installed-state-free*) 1 0)
                (- (if (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*) 1 0)))
           (fn2-seal-free-rows k j fn2-run-installed))))
 :hints (("Goal" :induct (fn2-seal-free-rows k j fn2-run-installed))))

; Frames: (FN ... (fn2-run-installed-set-COLUMN i v table) ...) is
; (FN ... table ...) for every COLUMN FN does not read.
(defun fn2-seal-frame-events (call columns)
 (declare (xargs :verify-guards nil))
 (if (atom columns) nil
  (let ((column (car columns)))
   (cons `(defthm ,(fn2-seal-col (concatenate 'string (symbol-name (car call)) "-OF-SET-") column)
           (equal (,(car call) ,@(subst `(,(fn2-seal-col "FN2-RUN-INSTALLED-SET-" column) i v fn2-run-installed)
                                        'fn2-run-installed (cdr call)))
                  ,call)
           :hints (("Goal" :induct ,call
                    :in-theory (union-theories
                                '(,(car call)
                                  ,(intern-in-package-of-symbol
                                    (concatenate 'string "FN2-RUN-INSTALLED-SET-" (symbol-name column) "-ROWS")
                                    'fn2-run-installed)
                                  ,@(fn2-seal-read-names column '(state schema run)))
                                (theory 'minimal-theory)))))
         (fn2-seal-frame-events call (cdr columns))))))
(make-event
 (let ((others (cdddr *fn2-seal-columns*)))
  `(progn ,@(fn2-seal-frame-events '(fn2-seal-live-runs k j sid fn2-run-installed) (cons 'run others))
          ,@(fn2-seal-frame-events '(fn2-seal-free-rows k j fn2-run-installed) (list* 'schema 'run others))
          ,@(fn2-seal-frame-events '(fn2-run-version sid n fn2-run-installed) others))))

; ---------------------------------------------------------------------------
; The transitions' writes. A row put live under schema S (an installation):
; SID's count gains the row if S is SID and loses what the row held before.
(defthm fn2-seal-live-runs-of-put-live
 (implies (natp r)
  (equal (fn2-seal-live-runs k j sid (fn2-run-installed-put r (state *fn2-run-installed-state-live*) (schema s)))
         (if (fn2-seal-row-in r k j fn2-run-installed)
             (+ (fn2-seal-live-runs k j sid fn2-run-installed)
                (if (equal s sid) 1 0)
                (- (fn2-seal-live-bit (fn2-run-installed-state r fn2-run-installed)
                                      (fn2-run-installed-schema r fn2-run-installed) sid)))
           (fn2-seal-live-runs k j sid fn2-run-installed)))))
; A row put in any other state (a retirement, a release): the count loses
; what the row held.
(defthm fn2-seal-live-runs-of-put-nonlive
 (implies (and (natp r) (not (equal v *fn2-run-installed-state-live*)))
  (equal (fn2-seal-live-runs k j sid (fn2-run-installed-put r (state v)))
         (if (fn2-seal-row-in r k j fn2-run-installed)
             (- (fn2-seal-live-runs k j sid fn2-run-installed)
                (fn2-seal-live-bit (fn2-run-installed-state r fn2-run-installed)
                                   (fn2-run-installed-schema r fn2-run-installed) sid))
           (fn2-seal-live-runs k j sid fn2-run-installed)))))
; A version is a maximum: a row put live raises it to the row's run when
; that is greater, and a row taken out of the live state leaves it where it
; was unless the row held SID's greatest run.
(defthm fn2-run-version-of-put-live
 (implies (and (natp r) (not (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)))
  (equal (fn2-run-version sid n (fn2-run-installed-put r (state *fn2-run-installed-state-live*) (schema s) (run x)))
         (if (and (< r (nfix n)) (equal s sid) (< (fn2-run-version sid n fn2-run-installed) (nfix x)))
             (nfix x)
           (fn2-run-version sid n fn2-run-installed))))
 :hints (("Goal" :induct (fn2-run-version sid n fn2-run-installed))))
(local (defthm fn2-seal-version-drop
 (implies (and (natp r) (not (equal v *fn2-run-installed-state-live*)))
  (let ((new (fn2-run-version sid n (fn2-run-installed-set-state r v fn2-run-installed)))
        (old (fn2-run-version sid n fn2-run-installed)))
   (and (<= new old)
        (or (equal new old)
            (and (equal old (nfix (fn2-run-installed-run r fn2-run-installed)))
                 (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)
                 (equal (fn2-run-installed-schema r fn2-run-installed) sid))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-run-version sid n fn2-run-installed)))))
(defthm fn2-run-version-of-put-nonlive
 (implies (and (natp r) (not (equal v *fn2-run-installed-state-live*))
               (or (not (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*))
                   (not (equal (fn2-run-installed-schema r fn2-run-installed) sid))
                   (< (nfix (fn2-run-installed-run r fn2-run-installed)) (fn2-run-version sid n fn2-run-installed))))
          (equal (fn2-run-version sid n (fn2-run-installed-put r (state v)))
                 (fn2-run-version sid n fn2-run-installed)))
 :hints (("Goal" :use fn2-seal-version-drop)))

; ---------------------------------------------------------------------------
; The transitions themselves, over any range of rows (the whole table is
; K = rows, J = 0). Each moves a count only when it succeeds (:ok).
(defmacro fn2-seal-install-call ()
 '(fn2-run-install r schema run top slot gen unit counter entries okind oslot ogen fn2-run-installed))
(defthm fn2-seal-live-runs-of-install
 (equal (fn2-seal-live-runs k j sid (mv-nth 1 (fn2-seal-install-call)))
        (+ (fn2-seal-live-runs k j sid fn2-run-installed)
           (if (and (equal (mv-nth 0 (fn2-seal-install-call)) :ok)
                    (fn2-seal-row-in r k j fn2-run-installed) (equal schema sid))
               1 0)))
 :hints (("Goal" :in-theory (e/d (fn2-run-install) (unsigned-byte-p)))))
(defthm fn2-seal-live-runs-of-retire
 (equal (fn2-seal-live-runs k j sid (mv-nth 1 (fn2-run-retire r fn2-run-installed)))
        (- (fn2-seal-live-runs k j sid fn2-run-installed)
           (if (and (equal (mv-nth 0 (fn2-run-retire r fn2-run-installed)) :ok)
                    (fn2-seal-row-in r k j fn2-run-installed)
                    (equal (fn2-run-installed-schema r fn2-run-installed) sid))
               1 0)))
 :hints (("Goal" :in-theory (e/d (fn2-run-retire) (unsigned-byte-p)))))
(defthm fn2-seal-live-runs-of-retired-next
 (equal (fn2-seal-live-runs k j sid (mv-nth 1 (fn2-run-retired-next r fn2-run-installed)))
        (fn2-seal-live-runs k j sid fn2-run-installed))
 :hints (("Goal" :in-theory (e/d (fn2-run-retired-next) (unsigned-byte-p)))))
(defthm fn2-seal-free-rows-of-install
 (equal (fn2-seal-free-rows k j (mv-nth 1 (fn2-seal-install-call)))
        (- (fn2-seal-free-rows k j fn2-run-installed)
           (if (and (equal (mv-nth 0 (fn2-seal-install-call)) :ok) (fn2-seal-row-in r k j fn2-run-installed)) 1 0)))
 :hints (("Goal" :in-theory (e/d (fn2-run-install) (unsigned-byte-p)))))
(defthm fn2-seal-free-rows-of-retire
 (equal (fn2-seal-free-rows k j (mv-nth 1 (fn2-run-retire r fn2-run-installed)))
        (fn2-seal-free-rows k j fn2-run-installed))
 :hints (("Goal" :in-theory (e/d (fn2-run-retire) (unsigned-byte-p)))))
(defthm fn2-seal-free-rows-of-retired-next
 (equal (fn2-seal-free-rows k j (mv-nth 1 (fn2-run-retired-next r fn2-run-installed)))
        (+ (fn2-seal-free-rows k j fn2-run-installed)
           (if (and (equal (mv-nth 0 (fn2-run-retired-next r fn2-run-installed)) :ok)
                    (fn2-seal-row-in r k j fn2-run-installed)
                    (< (nfix (fn2-run-installed-ulast r fn2-run-installed))
                       (+ 1 (nfix (fn2-run-installed-ufirst r fn2-run-installed)))))
               1 0)))
 :hints (("Goal" :in-theory (e/d (fn2-run-retired-next) (unsigned-byte-p)))))
; An installation under SID whose run is greater than SID's version makes
; the run the version: (fn2-run-version sid rows ...) of the new table is
; RUN, with no scan.
(defthm fn2-run-version-of-install
 (equal (fn2-run-version sid n (mv-nth 1 (fn2-seal-install-call)))
        (if (and (equal (mv-nth 0 (fn2-seal-install-call)) :ok) (< r (nfix n)) (equal schema sid)
                 (< (fn2-run-version sid n fn2-run-installed) run))
            run
          (fn2-run-version sid n fn2-run-installed)))
 :hints (("Goal" :in-theory (e/d (fn2-run-install) (unsigned-byte-p)))))
(defthm fn2-run-version-of-retire
 (implies (or (not (equal (fn2-run-installed-schema r fn2-run-installed) sid))
              (< (nfix (fn2-run-installed-run r fn2-run-installed)) (fn2-run-version sid n fn2-run-installed)))
          (equal (fn2-run-version sid n (mv-nth 1 (fn2-run-retire r fn2-run-installed)))
                 (fn2-run-version sid n fn2-run-installed)))
 :hints (("Goal" :in-theory (e/d (fn2-run-retire) (unsigned-byte-p)))))
(defthm fn2-run-version-of-retired-next
 (equal (fn2-run-version sid n (mv-nth 1 (fn2-run-retired-next r fn2-run-installed)))
        (fn2-run-version sid n fn2-run-installed))
 :hints (("Goal" :in-theory (e/d (fn2-run-retired-next) (unsigned-byte-p)))))

; ---------------------------------------------------------------------------
; The selection. Over per-schema counts, the Ith of COUNTS the live runs
; of schema SID+I: the schema with the most live runs above BEST-N, a
; smaller SID breaking ties and a schema without live runs never chosen:
; (mv best best-n), one visit per count. Over matching counts it is
; fn2-seal-most-by-schema (sealer.lisp) with each count read, not recounted.
(defun fn2-seal-most-counts (counts sid best best-n)
 (declare (xargs :guard t))
 (if (atom counts) (mv (nfix best) (nfix best-n))
  (let* ((n (nfix (car counts)))
         (better (and (< 0 n) (fn2-seal-most-better-p sid n best best-n))))
   (fn2-seal-most-counts (cdr counts) (+ 1 (nfix sid)) (if better (nfix sid) best) (if better n best-n)))))
; COUNTS holds the live runs of schemas SID, SID+1, ..., as many as it has.
(defun fn2-seal-counts-match-p (counts sid fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :guard (fn2-run-installed-wfp fn2-run-installed)))
 (or (atom counts)
     (and (equal (nfix (car counts))
                 (fn2-seal-live-runs (fn2-run-installed-rows fn2-run-installed) 0 (nfix sid) fn2-run-installed))
          (fn2-seal-counts-match-p (cdr counts) (+ 1 (nfix sid)) fn2-run-installed))))

; The selection over matching counts is the scan's, for any starting
; (BEST, BEST-N), whenever the counts cover every live schema.
(local (progn
(defthm fn2-sc-by-schema-done
 (implies (<= (nfix w) (nfix sid))
          (equal (fn2-seal-most-by-schema sid w best best-n fn2-run-installed) (mv (nfix best) (nfix best-n)))))
(defthm fn2-sc-by-schema-next
 (implies (< (nfix sid) (nfix w))
          (equal (fn2-seal-most-by-schema sid w best best-n fn2-run-installed)
                 (let* ((n (fn2-seal-live-runs (fn2-run-installed-rows fn2-run-installed) 0 (nfix sid) fn2-run-installed))
                        (better (and (< 0 n) (fn2-seal-most-better-p (nfix sid) n best best-n))))
                  (fn2-seal-most-by-schema (+ 1 (nfix sid)) w (if better (nfix sid) best) (if better n best-n)
                                           fn2-run-installed)))))
(defthm fn2-sc-most-counts-is-by-schema
 (implies (and (natp sid) (fn2-seal-counts-match-p counts sid fn2-run-installed))
          (equal (fn2-seal-most-counts counts sid best best-n)
                 (fn2-seal-most-by-schema sid (+ sid (len counts)) best best-n fn2-run-installed)))
 :hints (("Goal" :induct (fn2-seal-most-counts counts sid best best-n)
          :in-theory (disable fn2-seal-live-runs fn2-seal-most-better-p fn2-seal-most-by-schema))))))
(defthm fn2-seal-most-counts-is-most-runs
 (implies (and (fn2-seal-counts-match-p counts 0 fn2-run-installed)
               (fn2-seal-live-within-p (fn2-run-installed-rows fn2-run-installed) 0 (len counts) fn2-run-installed))
          (equal (fn2-seal-most-counts counts 0 best best-n)
                 (fn2-seal-most-runs (fn2-run-installed-rows fn2-run-installed) 0 best best-n fn2-run-installed)))
 :hints (("Goal" :use ((:instance fn2-sc-most-counts-is-by-schema (sid 0))
                       (:instance fn2-seal-most-by-schema-is-most-runs (w (len counts))))
          :in-theory (disable fn2-seal-live-runs fn2-seal-most-counts fn2-seal-most-runs fn2-seal-most-by-schema
                              fn2-sc-most-counts-is-by-schema))))

; ---------------------------------------------------------------------------
; Counting from scratch: one pass over rows R.. (K) adds every live row to
; COUNTS under its schema (an update-nth at the schema); (mv ok counts), OK
; nil (COUNTS partial) at the first live row whose schema is not below
; WIDTH.
(defun fn2-seal-zero-counts (n)
 (declare (xargs :guard (natp n)))
 (if (zp n) nil (cons 0 (fn2-seal-zero-counts (- n 1)))))
(defthm fn2-seal-zero-counts-len (equal (len (fn2-seal-zero-counts n)) (nfix n)))
(defun fn2-seal-live-histogram (k r width counts fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :measure (nfix k)
  :guard (and (fn2-run-installed-wfp fn2-run-installed) (natp r) (natp width) (true-listp counts) (<= width (len counts)))))
 (b* (((unless (and (posp k) (natp r) (< r (fn2-run-installed-rows fn2-run-installed)))) (mv t counts))
      ((unless (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*))
       (fn2-seal-live-histogram (- k 1) (+ 1 r) width counts fn2-run-installed))
      (s (fn2-run-installed-schema r fn2-run-installed))
      ((unless (and (natp s) (< s (nfix width)))) (mv nil counts)))
  (fn2-seal-live-histogram (- k 1) (+ 1 r) width (update-nth s (+ 1 (nfix (nth s counts))) counts) fn2-run-installed)))
(defthm fn2-seal-live-histogram-ok
 (equal (mv-nth 0 (fn2-seal-live-histogram k r width counts fn2-run-installed))
        (fn2-seal-live-within-p k r width fn2-run-installed)))
(defthm fn2-seal-live-histogram-len
 (implies (<= (nfix width) (len counts))
          (equal (len (mv-nth 1 (fn2-seal-live-histogram k r width counts fn2-run-installed))) (len counts))))
(local (progn
(defthm fn2-sc-hist-nth
 (implies (and (fn2-seal-live-within-p k r width fn2-run-installed) (natp s))
          (equal (nfix (nth s (mv-nth 1 (fn2-seal-live-histogram k r width counts fn2-run-installed))))
                 (+ (nfix (nth s counts)) (fn2-seal-live-runs k r s fn2-run-installed))))
 :hints (("Goal" :induct (fn2-seal-live-histogram k r width counts fn2-run-installed)
          :expand ((fn2-seal-live-within-p k r width fn2-run-installed)))))
(defun fn2-sc-down2 (s n) (if (or (zp s) (zp n)) t (fn2-sc-down2 (- s 1) (- n 1))))
(defthm fn2-sc-zero-counts-nth (equal (nfix (nth s (fn2-seal-zero-counts n))) 0)
 :hints (("Goal" :induct (fn2-sc-down2 s n) :expand ((fn2-seal-zero-counts n)))))
(defthm fn2-sc-car-nthcdr (equal (car (nthcdr i l)) (nth i l)))
(defthm fn2-sc-cdr-nthcdr (implies (natp i) (equal (cdr (nthcdr i l)) (nthcdr (+ 1 i) l))))
(defthm fn2-sc-nthcdr-past-end (implies (and (natp i) (<= (len l) i)) (not (consp (nthcdr i l)))))
(defthm fn2-sc-counts-match-of-atom (implies (atom counts) (fn2-seal-counts-match-p counts sid fn2-run-installed)))
(defun fn2-sc-up (i n)
 (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
 (if (< (nfix i) (nfix n)) (fn2-sc-up (+ 1 (nfix i)) n) t))
(defthm fn2-sc-hist-matches-from
 (implies (and (natp width) (fn2-seal-live-within-p (fn2-run-installed-rows fn2-run-installed) 0 width fn2-run-installed) (natp i))
          (fn2-seal-counts-match-p
           (nthcdr i (mv-nth 1 (fn2-seal-live-histogram (fn2-run-installed-rows fn2-run-installed) 0 width
                                                        (fn2-seal-zero-counts width) fn2-run-installed)))
           i fn2-run-installed))
 :hints (("Goal" :induct (fn2-sc-up i (len (mv-nth 1 (fn2-seal-live-histogram (fn2-run-installed-rows fn2-run-installed) 0 width
                                                                               (fn2-seal-zero-counts width) fn2-run-installed))))
          :in-theory (disable fn2-seal-live-runs fn2-seal-live-histogram))))
))
(defthm fn2-seal-live-histogram-matches
 (implies (and (natp width) (fn2-seal-live-within-p (fn2-run-installed-rows fn2-run-installed) 0 width fn2-run-installed))
          (fn2-seal-counts-match-p
           (mv-nth 1 (fn2-seal-live-histogram (fn2-run-installed-rows fn2-run-installed) 0 width
                                              (fn2-seal-zero-counts width) fn2-run-installed))
           0 fn2-run-installed))
 :hints (("Goal" :use ((:instance fn2-sc-hist-matches-from (i 0))) :in-theory (disable fn2-sc-hist-matches-from))))

; The selection in R + S visits (R rows counted once, S = MAX-SID + 1
; counts read once) against the scan's R + L*R, the scan itself where a
; live schema exceeds MAX-SID.
(defun fn2-seal-most-runs-fast (max-sid fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :guard (and (fn2-run-installed-wfp fn2-run-installed) (natp max-sid))))
 (let* ((rows (fn2-run-installed-rows fn2-run-installed)) (width (+ 1 (nfix max-sid))))
  (mv-let (ok counts) (fn2-seal-live-histogram rows 0 width (fn2-seal-zero-counts width) fn2-run-installed)
   (if ok (fn2-seal-most-counts counts 0 0 0) (fn2-seal-most-runs rows 0 0 0 fn2-run-installed)))))
(local (defthm fn2-sc-fast-body
 (let ((rows (fn2-run-installed-rows fn2-run-installed)))
  (mv-let (ok counts) (fn2-seal-live-histogram rows 0 width (fn2-seal-zero-counts width) fn2-run-installed)
   (implies (and (natp width) ok)
            (equal (fn2-seal-most-counts counts 0 0 0) (fn2-seal-most-runs rows 0 0 0 fn2-run-installed)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn2-seal-live-histogram fn2-seal-most-counts fn2-seal-most-runs fn2-seal-zero-counts)
          :use ((:instance fn2-seal-most-counts-is-most-runs
                 (counts (mv-nth 1 (fn2-seal-live-histogram (fn2-run-installed-rows fn2-run-installed) 0 width
                                                            (fn2-seal-zero-counts width) fn2-run-installed)))
                 (best 0) (best-n 0)))))))
(defthm fn2-seal-most-runs-fast-is-most-runs
 (equal (fn2-seal-most-runs-fast max-sid fn2-run-installed)
        (fn2-seal-most-runs (fn2-run-installed-rows fn2-run-installed) 0 0 0 fn2-run-installed))
 :hints (("Goal" :in-theory (disable fn2-seal-live-histogram fn2-seal-most-counts fn2-seal-most-runs fn2-seal-zero-counts)
          :use ((:instance fn2-sc-fast-body (width (+ 1 (nfix max-sid))))))))

; ---------------------------------------------------------------------------
; Maintaining the counts. A list matching the table before a transition,
; bumped by the transition's own arguments (an installation adds one under
; its schema, a retirement takes one from the retired row's schema, a
; release changes nothing), matches the table after it; and
; every live schema stays below WIDTH while installations stay below it. So
; counts read once (fn2-seal-live-histogram, or zeros over an empty table)
; and kept this way select as fn2-seal-most-runs at every step, in S visits.
(defun fn2-seal-counts-bump (counts sid i delta)
 (declare (xargs :guard (and (natp sid) (integerp delta))))
 (cond ((atom counts) counts)
       ((equal (nfix sid) i) (cons (nfix (+ delta (nfix (car counts)))) (cdr counts)))
       (t (cons (car counts) (fn2-seal-counts-bump (cdr counts) (+ 1 (nfix sid)) i delta)))))
(local (progn
(defthm fn2-sc-install-ok
 (implies (equal (car (fn2-seal-install-call)) :ok)
          (and (natp r) (< r (fn2-run-installed-rows fn2-run-installed)) (natp schema) (natp run)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (e/d (fn2-run-install) (unsigned-byte-p)))))
(defthm fn2-sc-install-refused
 (implies (not (equal (car (fn2-seal-install-call)) :ok))
          (equal (mv-nth 1 (fn2-seal-install-call)) fn2-run-installed))
 :hints (("Goal" :in-theory (e/d (fn2-run-install) (unsigned-byte-p)))))
(defthm fn2-sc-install-rows
 (equal (fn2-run-installed-rows (mv-nth 1 (fn2-seal-install-call))) (fn2-run-installed-rows fn2-run-installed))
 :hints (("Goal" :in-theory (e/d (fn2-run-install) (unsigned-byte-p)))))
(defthm fn2-sc-retire-ok
 (implies (equal (car (fn2-run-retire r fn2-run-installed)) :ok)
          (and (natp r) (< r (fn2-run-installed-rows fn2-run-installed))
               (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable fn2-run-retire))))
(defthm fn2-sc-retire-refused
 (implies (not (equal (car (fn2-run-retire r fn2-run-installed)) :ok))
          (equal (mv-nth 1 (fn2-run-retire r fn2-run-installed)) fn2-run-installed))
 :hints (("Goal" :in-theory (enable fn2-run-retire))))
(defthm fn2-sc-retire-rows
 (equal (fn2-run-installed-rows (mv-nth 1 (fn2-run-retire r fn2-run-installed))) (fn2-run-installed-rows fn2-run-installed))
 :hints (("Goal" :in-theory (enable fn2-run-retire))))
(defthm fn2-sc-retired-next-rows
 (equal (fn2-run-installed-rows (mv-nth 1 (fn2-run-retired-next r fn2-run-installed))) (fn2-run-installed-rows fn2-run-installed))
 :hints (("Goal" :in-theory (e/d (fn2-run-retired-next) (unsigned-byte-p)))))
(defthm fn2-sc-bump-below
 (implies (< i (nfix sid)) (equal (fn2-seal-counts-bump counts sid i delta) counts)))
(defthm fn2-sc-match-of-install-above
 (implies (and (natp (fn2-run-installed-rows fn2-run-installed))
               (fn2-seal-counts-match-p counts sid fn2-run-installed)
               (or (not (equal (mv-nth 0 (fn2-seal-install-call)) :ok)) (< schema (nfix sid))))
          (fn2-seal-counts-match-p counts sid (mv-nth 1 (fn2-seal-install-call))))
 :hints (("Goal" :induct (fn2-seal-counts-match-p counts sid fn2-run-installed)
          :in-theory (disable fn2-seal-live-runs fn2-run-install))))
(defthm fn2-sc-match-of-install-ok
 (implies (and (natp (fn2-run-installed-rows fn2-run-installed)) (fn2-seal-counts-match-p counts sid fn2-run-installed)
               (equal (car (fn2-seal-install-call)) :ok))
          (fn2-seal-counts-match-p (fn2-seal-counts-bump counts sid schema 1) sid (mv-nth 1 (fn2-seal-install-call))))
 :hints (("Goal" :induct (fn2-seal-counts-bump counts sid schema 1) :in-theory (disable fn2-seal-live-runs fn2-run-install))))
(defthm fn2-sc-match-of-retire-above
 (implies (and (natp (fn2-run-installed-rows fn2-run-installed))
               (fn2-seal-counts-match-p counts sid fn2-run-installed)
               (not (and (equal (car (fn2-run-retire r fn2-run-installed)) :ok)
                         (natp (fn2-run-installed-schema r fn2-run-installed))
                         (<= (nfix sid) (fn2-run-installed-schema r fn2-run-installed)))))
          (fn2-seal-counts-match-p counts sid (mv-nth 1 (fn2-run-retire r fn2-run-installed))))
 :hints (("Goal" :induct (fn2-seal-counts-match-p counts sid fn2-run-installed)
          :in-theory (disable fn2-seal-live-runs fn2-run-retire))))
(defthm fn2-sc-match-of-retire-ok
 (implies (and (natp (fn2-run-installed-rows fn2-run-installed)) (fn2-seal-counts-match-p counts sid fn2-run-installed)
               (equal (car (fn2-run-retire r fn2-run-installed)) :ok)
               (< 0 (fn2-seal-live-runs (fn2-run-installed-rows fn2-run-installed) 0
                                        (fn2-run-installed-schema r fn2-run-installed) fn2-run-installed)))
          (fn2-seal-counts-match-p (fn2-seal-counts-bump counts sid (fn2-run-installed-schema r fn2-run-installed) -1)
                                   sid (mv-nth 1 (fn2-run-retire r fn2-run-installed))))
 :hints (("Goal" :induct (fn2-seal-counts-bump counts sid (fn2-run-installed-schema r fn2-run-installed) -1)
          :expand ((fn2-seal-counts-match-p counts sid fn2-run-installed))
          :in-theory (disable fn2-seal-live-runs fn2-run-retire))))
))
(defthm fn2-seal-counts-match-p-of-install
 (implies (and (natp (fn2-run-installed-rows fn2-run-installed)) (fn2-seal-counts-match-p counts sid fn2-run-installed))
          (fn2-seal-counts-match-p
           (if (equal (mv-nth 0 (fn2-seal-install-call)) :ok) (fn2-seal-counts-bump counts sid schema 1) counts)
           sid (mv-nth 1 (fn2-seal-install-call))))
 :hints (("Goal" :in-theory (disable fn2-run-install fn2-seal-counts-match-p fn2-seal-counts-bump))))
(defthm fn2-seal-counts-match-p-of-retire
 (implies (and (natp (fn2-run-installed-rows fn2-run-installed)) (fn2-seal-counts-match-p counts sid fn2-run-installed))
          (fn2-seal-counts-match-p
           (if (equal (mv-nth 0 (fn2-run-retire r fn2-run-installed)) :ok)
               (fn2-seal-counts-bump counts sid (fn2-run-installed-schema r fn2-run-installed) -1)
             counts)
           sid (mv-nth 1 (fn2-run-retire r fn2-run-installed))))
 :hints (("Goal" :use ((:instance fn2-seal-live-row-counted (i r)))
          :in-theory (disable fn2-run-retire fn2-seal-counts-match-p fn2-seal-counts-bump fn2-seal-live-runs))))
(defthm fn2-seal-counts-match-p-of-retired-next
 (implies (fn2-seal-counts-match-p counts sid fn2-run-installed)
          (fn2-seal-counts-match-p counts sid (mv-nth 1 (fn2-run-retired-next r fn2-run-installed))))
 :hints (("Goal" :induct (fn2-seal-counts-match-p counts sid fn2-run-installed)
          :in-theory (disable fn2-seal-live-runs fn2-run-retired-next))))

(make-event
 `(progn ,@(fn2-seal-frame-events '(fn2-seal-live-within-p k j w fn2-run-installed) (cons 'run (cdddr *fn2-seal-columns*)))))
(defthm fn2-seal-live-within-p-of-put-live
 (implies (and (natp r) (fn2-seal-live-within-p k j w fn2-run-installed) (natp s) (< s (nfix w)))
          (fn2-seal-live-within-p k j w (fn2-run-installed-put r (state *fn2-run-installed-state-live*) (schema s))))
 :hints (("Goal" :induct (fn2-seal-live-within-p k j w fn2-run-installed))))
(defthm fn2-seal-live-within-p-of-put-nonlive
 (implies (and (natp r) (not (equal v *fn2-run-installed-state-live*)) (fn2-seal-live-within-p k j w fn2-run-installed))
          (fn2-seal-live-within-p k j w (fn2-run-installed-put r (state v))))
 :hints (("Goal" :induct (fn2-seal-live-within-p k j w fn2-run-installed))))
(defthm fn2-seal-live-within-p-of-install
 (implies (and (fn2-seal-live-within-p k j w fn2-run-installed)
               (or (not (equal (mv-nth 0 (fn2-seal-install-call)) :ok)) (< schema (nfix w))))
          (fn2-seal-live-within-p k j w (mv-nth 1 (fn2-seal-install-call))))
 :hints (("Goal" :in-theory (e/d (fn2-run-install) (unsigned-byte-p)))))
(defthm fn2-seal-live-within-p-of-retire
 (implies (fn2-seal-live-within-p k j w fn2-run-installed)
          (fn2-seal-live-within-p k j w (mv-nth 1 (fn2-run-retire r fn2-run-installed))))
 :hints (("Goal" :in-theory (e/d (fn2-run-retire) (unsigned-byte-p)))))
(defthm fn2-seal-live-within-p-of-retired-next
 (implies (fn2-seal-live-within-p k j w fn2-run-installed)
          (fn2-seal-live-within-p k j w (mv-nth 1 (fn2-run-retired-next r fn2-run-installed))))
 :hints (("Goal" :in-theory (e/d (fn2-run-retired-next) (unsigned-byte-p)))))

(assert-event (fn2-assert-compliant-p
               '(fn2-seal-most-better-p fn2-seal-most-counts fn2-seal-counts-match-p fn2-seal-live-within-p
                 fn2-seal-zero-counts fn2-seal-live-histogram fn2-seal-most-runs-fast fn2-seal-counts-bump)
               (w state)))
