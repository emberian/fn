; Layer C in the served core, seam C-S4's first half (fn2/docs/c-ordered-runs.md
; §8 item 12; fn2/docs/d-machines-nntp.md §15.8): served reads for layer D's
; query cursor rows. Written by D on C's ruling (C and B read the diff), as
; machines-c-groups.lisp is written, to C's binding amendments (a)-(e):
;
; (a) Read row X (one per query cursor slot, (fn2-b-read-rows profile) of
;     them) owns a field stripe of *fn2-read-stride* rows below the sealer's
;     stripe, which sits below the transactions' stripes anchored at the
;     table's end: base(X) = rows - 1024*t - *fn2-b-seal-field-rows* -
;     *fn2-b-read-stride**(X+1); B's per-slot stripes lie at or below the
;     lowest read stripe. In a stripe: the lo key at +0, the hi key at +80,
;     the decoded heads of the range's eight sources from +160 (the exact
;     lookup decodes into source 0's region: a row runs one read at a time).
;     The row's other state: range row X of fn2-ranges, sources [8X, 8X+8)
;     of fn2-range-sources, seek row X of fn2-seeks, the exact lookup's
;     continuation in transaction row t+X of fn2-succ-txns with run cursor
;     t+X (fn2-xl-step serves it unchanged: the generalization by
;     allocation of §15.9), the sources' run cursors t+R+8X+i.
; (b) Staleness. The sealer moves an overlay into a run and frees its arena
;     in one step between any two of a reader's steps. Every continuation is
;     re-checked at each step: a range or seek re-finds every source strictly
;     after its resume key when the schema's run version moved
;     (fn2-range-step) or when an overlay source no longer holds the taking
;     it located (its row's phase, schema and SEQ: a SEQ is issued once per
;     taking, so it names the arena's life; fn2-rd-sources-live); the exact
;     lookup re-reads its overlay leg each call and restarts its run leg on a
;     version move (fn2-xl-step). A delivered entry is read (fn2-read-value,
;     fn2-read-octets) only while its schema's run version is the one it was
;     delivered under, else :stale: no read touches a freed arena. :miss
;     keeps its word though resident pages cannot raise it before M2.
; (c) fn2-read-frontier: the view a connection pins, C's :published
;     position (fn2-id-engine, written by fn2-succ-publish as max(published,
;     batch cov)), read through C's fn2-successor-published; (mv code
;     position), every published batch at or below the position.
; (d) LIST's whole-schema ordered scan (fn2-read-scan, -scan-next): the
;     range read's sources and merge over any schema, octet keys included,
;     its resume key the delivered key itself (copied into the caller's
;     workspace), skipped once by the next step; never an octet-keyed range.
; (e) The identity read (fn2-read-identity): the decision path's own
;     lower query (the Message-ID, an empty content) and classification
;     (fn2-run-octets-field-compare), over the same merge in Message-ID
;     order: (:found article), :evidence or :absent.
;
; Every operation is (... fn2-core) with a defcost; the core wrappers are
; fn2-read-core-events, materialized in assembly-callbacks-c.lisp.
(in-package "ACL2")
(include-book "machines-c-sealer")
(fn2-book-layer :c)
(local (in-theory (disable fn2-run-layout-fields fn2-run-layout-keys fn2-run-layout-merge fn2-run-layout-size
                           fn2-fold-key-arg fn2-fold-arity fn2-fold-assigned-p fn2-run-layout-octets-max
                           fn2-run-layout-value-ok fn2-run-layout-fold-p fn2-run-version)))

; ---------------------------------------------------------------------------
; The stripe.
(defconst *fn2-read-sources* 8)
(defconst *fn2-read-identity-sid* 1)
(defconst *fn2-read-lo* 0)
(defconst *fn2-read-hi* *fn2-run-entry-rows*)
(defconst *fn2-read-heads* (* 2 *fn2-run-entry-rows*))
(defconst *fn2-read-stride* (+ *fn2-read-heads* (* *fn2-read-sources* *fn2-run-reader-fields*)))
(assert-event (and (<= *fn2-read-stride* *fn2-b-read-stride*) (<= *fn2-b-read-stride* 1024)
                   (equal (fn2-b-read-rows '((:x . 4))) 0) (equal (fn2-b-read-rows '((:x . 4) (:reading . t))) 4)
                   (equal (fn2-b-field-rows '((:t . 3) (:x . 2) (:reading . t) (:format-slots . 3)))
                          (+ (* 3 *fn2-idc-b-stripe*) (* 3 *fn2-idc-stride*) *fn2-b-seal-field-rows* (* 2 *fn2-b-read-stride*)))))

; A read row: the operation it holds (one at a time), the schema, the
; owner its octet key fields are read under (QSET once given), and the
; delivered entry (ENTRY: its rows at EROW, octets readable under EK ES EG,
; delivered under the schema's run version EVER).
; A scan (C-S4 (d)) keeps its resume key in the lo region, its octets in
; the caller's workspace WSLOT/WGEN (under the query owner), EXCL once a key
; was delivered (the next step skips it); the identity read (C-S4 (e)) SEEN
; once it met conflict evidence for its Message-ID.
(defcolumns fn2-reads
 ((op (:enum fn2-read-op (:idle :lookup :range :seek :scan :identity)))
  (sid :u60) (qset :bool) (qk :u8) (qs :u32) (qg :u60)
  (entry :bool) (erow :u32) (ek :u8) (es :u32) (eg :u60) (ever :u60)
  (wslot :u32) (wgen :u60) (excl :bool) (found :bool) (selected :u60) (evidence :u32)))

; The read rows' children, their inits' guards proved once over their own
; profile predicate (the transaction-sized children's is fn2-idc-profilep).
(defun fn2-read-profilep (profile)
 (declare (xargs :guard t))
 (unsigned-byte-p 32 (* *fn2-read-sources* (fn2-b-read-rows profile))))
(defmacro fn2-read-child (field stobj init why)
 (let ((fn (fn2-columns-sym stobj "-INIT-FOR")))
  `(progn
    (defun ,fn (profile ,stobj)
     (declare (xargs :stobjs ,stobj :guard (fn2-read-profilep profile)
                     :guard-hints (("Goal" :in-theory (enable fn2-read-profilep)))))
     ,init)
    (defthm ,(fn2-columns-sym fn "-TYPE")
     (implies (and (,(fn2-columns-sym stobj "P") ,stobj) (fn2-read-profilep profile))
              (,(fn2-columns-sym stobj "P") (,fn profile ,stobj)))
     :hints (("Goal" :in-theory (enable fn2-read-profilep))))
    (defthm ,(fn2-columns-sym fn "-WFP")
     (implies (fn2-read-profilep profile) (,(fn2-columns-sym stobj "-WFP") (,fn profile ,stobj)))
     :hints (("Goal" :in-theory (enable fn2-read-profilep))))
    (in-theory (disable ,fn))
    (defcorechild ,field ,stobj :init (,fn profile ,stobj) :profilep (fn2-read-profilep profile) :why ,why))))
(in-theory (disable fn2-read-profilep))
(fn2-read-child fn2-core-reads fn2-reads (fn2-reads-init (fn2-b-read-rows profile) fn2-reads)
 "One read row per query cursor slot (C-S4): its operation, its query owner and its delivered entry survive the cursor's yields.")
(fn2-read-child fn2-core-ranges fn2-ranges (fn2-ranges-init (fn2-b-read-rows profile) fn2-ranges)
 "Read row X's range read (C3) resumes from its resume key across the cursor's yields.")
(fn2-read-child fn2-core-range-sources fn2-range-sources
 (fn2-range-sources-init (* *fn2-read-sources* (fn2-b-read-rows profile)) fn2-range-sources)
 "Read row X's range sources [8X, 8X+8): one per overlay or live run of the schema.")
(fn2-read-child fn2-core-seeks fn2-seeks (fn2-seeks-init (fn2-b-read-rows profile) fn2-seeks)
 "Read row X's positioned seek (INBOX 4.1) over its range row.")

; Read row X's stripe base, or :bounds when X is no read row or B's
; stripes (FCROWS format slots) would reach the lowest read stripe.
(defun fn2-read-stripe (x fcrows fn2-reads fn2-id-decides fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-fields) :guard t))
 (let* ((n (fn2-reads-rows fn2-reads)) (tn (fn2-id-decides-rows fn2-id-decides)) (rows (fn2-fields-rows fn2-fields))
        (top (- (nfix rows) (+ (* *fn2-idc-stride* (nfix tn)) *fn2-b-seal-field-rows*))))
  (if (and (natp x) (< x (nfix n)) (<= (+ (* *fn2-idc-b-stripe* (nfix fcrows)) (* *fn2-b-read-stride* (nfix n))) top))
      (mv :ok (- top (* *fn2-b-read-stride* (+ x 1))))
    (mv :bounds 0))))
(defthm fn2-read-stripe-natp (natp (mv-nth 1 (fn2-read-stripe x fcrows fn2-reads fn2-id-decides fn2-fields)))
 :rule-classes :type-prescription)
(in-theory (disable fn2-read-stripe))

; ---------------------------------------------------------------------------
; Shapes (type, wfp and rows of every stobj a function returns), proved
; right after each function with it opened and its callees folded.
(defun fn2-rd-shape-disables (stobjs)
 (declare (xargs :verify-guards nil))
 (if (atom stobjs) nil (cons (fn2-columns-sym (car stobjs) "-ROWS") (fn2-rd-shape-disables (cdr stobjs)))))
;; READS entries (:keep F) leave F enabled (a stobj's -ROWS where an
;; element is read from a stobj the function also writes).
(defun fn2-rd-keeps (reads)
 (declare (xargs :verify-guards nil))
 (cond ((atom reads) nil) ((consp (car reads)) (cons (car reads) (fn2-rd-keeps (cdr reads)))) (t (fn2-rd-keeps (cdr reads)))))
(defun fn2-rd-folds (reads)
 (declare (xargs :verify-guards nil))
 (cond ((atom reads) nil) ((consp (car reads)) (fn2-rd-folds (cdr reads))) (t (cons (car reads) (fn2-rd-folds (cdr reads))))))
;; Every stobj's -ROWS folded (the shape lemmas and the reads' guards are
;; stated over it), the fields and pool recognizers folded (C-ASSEMBLY-THEORY),
;; and READS: the callees and the row reads whose values only feed checks
;; and arguments (C-SHAPE-READS).
(defmacro fn2-rd-shape (fn args outs stobjs &optional reads (disable 't))
 `(progn
   (defthm ,(fn2-columns-sym fn "-RD-SHAPE")
    (implies (and ,@(fn2-idc-hyp-list stobjs)) (and ,@(fn2-fc-shape-claims outs (cons fn args))))
    :hints (("Goal" :in-theory (e/d (,fn ,@(strip-cadrs (fn2-rd-keeps reads)))
                                   (,@(set-difference-eq (fn2-rd-shape-disables stobjs) (strip-cadrs (fn2-rd-keeps reads)))
                                    fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp ,@(fn2-rd-folds reads))))))
   ,@(and disable `((in-theory (disable ,fn))))))

;; The range engine's entry points, whose shapes range.lisp's adapters do
;; not need (they use local stobjs).
(fn2-rd-shape fn2-range-start (g sid qbase hbase sbase smax cbase rbase pfield plimit qk qs qg
                               fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 ((fn2-ranges 1) (fn2-range-sources 2)) (fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed) (fn2-range-enumerate))
(fn2-rd-shape fn2-range-deliver (g fn2-ranges fn2-range-sources fn2-fields fn2-pool)
 ((fn2-ranges 1) (fn2-range-sources 2) (fn2-fields 3)) (fn2-ranges fn2-range-sources fn2-fields fn2-pool)
 (fn2-range-pick fn2-range-consume fn2-range-successor fn2-range-past fn2-range-sources-rb fn2-range-sources-okind
  fn2-range-sources-oslot fn2-range-sources-ogen))
(fn2-rd-shape fn2-range-step (g budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                              fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-ranges 1) (fn2-range-sources 2) (fn2-run-cursors 3) (fn2-run-paths 4) (fn2-fields 5))
 (fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
  fn2-fields fn2-pool)
 (fn2-range-enumerate fn2-range-recheck fn2-range-advance-all fn2-range-deliver fn2-range-keys-ok fn2-run-version
  fn2-ranges-phase fn2-ranges-schema fn2-ranges-vrun fn2-ranges-scount))
(fn2-rd-shape fn2-seek-start (k g lo hi p pfield fn2-seeks) ((fn2-seeks 1)) (fn2-seeks))
(fn2-rd-shape fn2-seek-probe (k fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
 ((fn2-seeks 1) (fn2-ranges 2) (fn2-range-sources 3) (fn2-fields 4))
 (fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
 (fn2-range-start fn2-seeks-g fn2-seeks-lo fn2-seeks-hi fn2-seeks-probes fn2-ranges-schema fn2-ranges-qbase fn2-ranges-hbase
  fn2-ranges-sbase fn2-ranges-smax fn2-ranges-cbase fn2-ranges-rbase fn2-ranges-qk fn2-ranges-qs fn2-ranges-qg))
(fn2-rd-shape fn2-seek-narrow (k code fn2-seeks fn2-ranges fn2-fields) ((fn2-seeks 1)) (fn2-seeks fn2-ranges fn2-fields)
 ((:keep fn2-seeks-rows) fn2-seeks-g fn2-seeks-pfield fn2-seeks-after fn2-ranges-out fn2-ranges-schema fn2-fields-value))
(fn2-rd-shape fn2-seek-step (k budget fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                             fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-seeks 1) (fn2-ranges 2) (fn2-range-sources 3) (fn2-run-cursors 4) (fn2-run-paths 5) (fn2-fields 6))
 (fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths
  fn2-run-cache fn2-fields fn2-pool)
 (fn2-seek-probe fn2-seek-narrow fn2-range-step))

; ---------------------------------------------------------------------------
; Keys. Integer key field J (below *fn2-run-entry-rows*) of REGION (:lo or
; :hi) of read row X (stripe B0) takes VALUE; a key written ends the row's
; operation (its continuation is over a key it no longer holds).
(defun fn2-rd-key (x region j value b0 fn2-reads fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-fields) :guard t))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-fields-wfp fn2-fields))) (mv :state fn2-reads fn2-fields))
      ((unless (and (natp x) (< x (fn2-reads-rows fn2-reads)) (natp b0) (natp j) (< j *fn2-run-entry-rows*)
                    (member-eq region '(:lo :hi)) (unsigned-byte-p 60 value)
                    (<= (+ b0 *fn2-read-stride*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-reads fn2-fields))
      (row (+ b0 (if (eq region :lo) *fn2-read-lo* *fn2-read-hi*) j))
      (fn2-fields (fn2-fields-put row (value value) (ref-slot 0) (ref-gen 0) (ref-off 0) (ref-len 0)))
      (fn2-reads (fn2-reads-put x (op *fn2-read-op-idle*) (entry 0))))
  (mv :ok fn2-reads fn2-fields)))
(fn2-rd-shape fn2-rd-key (x region j value b0 fn2-reads fn2-fields) ((fn2-reads 1) (fn2-fields 2)) (fn2-reads fn2-fields))

; Octet key field J of the lo region: the LEN octets at [OFF, OFF+LEN) of
; SLOT/GEN, readable under OKIND OSLOT OGEN while the row reads with it.
; Every octet key field of a row is read under one owner until its
; release (:owner otherwise).
(defun fn2-rd-key-octets (x j slot gen off len okind oslot ogen b0 fn2-reads fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-fields) :guard t))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-fields-wfp fn2-fields))) (mv :state fn2-reads fn2-fields))
      ((unless (and (natp x) (< x (fn2-reads-rows fn2-reads)) (natp b0) (natp j) (< j *fn2-run-entry-rows*)
                    (posp len) (<= len *fn2-run-key-octets-max*) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                    (unsigned-byte-p 32 off) (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
                    (<= (+ b0 *fn2-read-stride*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-reads fn2-fields))
      ((when (and (equal (fn2-reads-qset x fn2-reads) 1)
                  (not (and (equal (fn2-reads-qk x fn2-reads) okind) (equal (fn2-reads-qs x fn2-reads) oslot)
                            (equal (fn2-reads-qg x fn2-reads) ogen)))))
       (mv :owner fn2-reads fn2-fields))
      (fn2-fields (fn2-fields-put (+ b0 *fn2-read-lo* j) (value 0) (ref-slot slot) (ref-gen gen) (ref-off off) (ref-len len)))
      (fn2-reads (fn2-reads-put x (op *fn2-read-op-idle*) (entry 0) (qset 1) (qk okind) (qs oslot) (qg ogen))))
  (mv :ok fn2-reads fn2-fields)))
(fn2-rd-shape fn2-rd-key-octets (x j slot gen off len okind oslot ogen b0 fn2-reads fn2-fields)
 ((fn2-reads 1) (fn2-fields 2)) (fn2-reads fn2-fields))

; ---------------------------------------------------------------------------
; The exact lookup of the lo key in SID, one source per call (fn2-xl-step
; over transaction row and run cursor TN+X): :ok with the entry delivered,
; :absent, :more, :miss, or a refusal. A lookup of another schema, or after
; another operation, starts over.
(defun fn2-rd-lookup (x sid budget b0 tn fn2-reads fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed
                      fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-xl-step fn2-xl-done fn2-fields-rows fn2-reads-rows)))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-succ-txns-wfp fn2-succ-txns) (fn2-overlays-wfp fn2-overlays)
                    (fn2-overlay-index-wfp fn2-overlay-index) (fn2-run-installed-wfp fn2-run-installed)
                    (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp fn2-run-cache)
                    (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-reads fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (natp x) (< x (fn2-reads-rows fn2-reads)) (natp tn) (< (+ tn x) (fn2-succ-txns-rows fn2-succ-txns))
                    (unsigned-byte-p 60 sid) (natp budget) (<= budget 4096) (natp b0)
                    (<= (+ b0 *fn2-read-stride*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-reads fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      (tx (+ tn x))
      (fresh (not (and (equal (fn2-reads-op x fn2-reads) *fn2-read-op-lookup*) (equal (fn2-reads-sid x fn2-reads) sid))))
      ((mv code fn2-succ-txns) (if fresh (fn2-xl-done tx :ok fn2-succ-txns) (mv :ok fn2-succ-txns)))
      ((unless (eq code :ok)) (mv code fn2-reads fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      ((mv code erow fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-xl-step tx sid budget (+ b0 *fn2-read-lo*) (+ b0 *fn2-read-heads*)
                    (fn2-reads-qk x fn2-reads) (fn2-reads-qs x fn2-reads) (fn2-reads-qg x fn2-reads)
                    fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths
                    fn2-run-cache fn2-fields fn2-pool))
      (ever (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed))
      ((unless (and (unsigned-byte-p 32 erow) (unsigned-byte-p 60 ever)))
       (mv :bounds fn2-reads fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      (fn2-reads (if (eq code :ok)
                     (fn2-reads-put x (op *fn2-read-op-lookup*) (sid sid) (entry 1) (erow erow)
                                    (ek *fn2-idc-owner-kind*) (es *fn2-idc-owner-slot*) (eg *fn2-idc-owner-gen*) (ever ever))
                   (fn2-reads-put x (op *fn2-read-op-lookup*) (sid sid) (entry 0)))))
  (mv code fn2-reads fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
(fn2-rd-shape fn2-rd-lookup (x sid budget b0 tn fn2-reads fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed
                             fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-reads 1) (fn2-succ-txns 2) (fn2-run-cursors 3) (fn2-run-paths 4) (fn2-fields 5))
 (fn2-reads fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
  fn2-fields fn2-pool)
 (fn2-xl-step fn2-xl-done fn2-run-version fn2-reads-op fn2-reads-sid fn2-reads-qk fn2-reads-qs fn2-reads-qg))

; ---------------------------------------------------------------------------
; Range reads. Start range row X over SID from the lo key to the hi key
; (PFIELD the entry's position field and PLIMIT the greatest position
; delivered, or PFIELD *fn2-range-no-position*), its sources [8X, 8X+8)
; reading through run cursors TN+N+8X+i (N read rows), their heads decoded
; in the stripe.
(defun fn2-rd-range-args-ok (x sid b0 tn fn2-reads fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-fields) :guard t))
 (and (natp x) (< x (fn2-reads-rows fn2-reads)) (natp tn) (natp b0) (unsigned-byte-p 60 sid)
      (unsigned-byte-p 32 (+ b0 *fn2-read-stride*)) (<= (+ b0 *fn2-read-stride*) (fn2-fields-rows fn2-fields))
      (unsigned-byte-p 32 (+ tn (nfix (fn2-reads-rows fn2-reads)) (* *fn2-read-sources* (+ x 1))))
      (unsigned-byte-p 32 (* *fn2-read-sources* (+ x 1)))))
(in-theory (disable fn2-rd-range-args-ok))
(defun fn2-rd-range-start (x sid pfield plimit b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources)
              (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed))
  :guard-hints (("Goal" :in-theory (disable fn2-range-start)))))
 (b* (((unless (and (natp x) (< x (fn2-reads-rows fn2-reads)) (< x (fn2-ranges-rows fn2-ranges)) (natp tn) (natp b0)))
       (mv :bounds fn2-ranges fn2-range-sources)))
  (fn2-range-start x sid (+ b0 *fn2-read-lo*) (+ b0 *fn2-read-hi*) (* *fn2-read-sources* x) *fn2-read-sources*
                   (+ tn (fn2-reads-rows fn2-reads) (* *fn2-read-sources* x)) (+ b0 *fn2-read-heads*) pfield plimit
                   (fn2-reads-qk x fn2-reads) (fn2-reads-qs x fn2-reads) (fn2-reads-qg x fn2-reads)
                   fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)))
(fn2-rd-shape fn2-rd-range-start (x sid pfield plimit b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 ((fn2-ranges 1) (fn2-range-sources 2)) (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 (fn2-range-start fn2-reads-qk fn2-reads-qs fn2-reads-qg))

(defun fn2-rd-range (x sid pfield plimit b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields) :guard t
  :guard-hints (("Goal" :in-theory (e/d (fn2-rd-range-args-ok) (fn2-rd-range-start fn2-range-keys-ok))))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources)
                    (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields)))
       (mv :state fn2-reads fn2-ranges fn2-range-sources))
      ((unless (and (fn2-rd-range-args-ok x sid b0 tn fn2-reads fn2-fields) (< x (fn2-ranges-rows fn2-ranges))
                    (<= (* *fn2-read-sources* (+ x 1)) (fn2-range-sources-rows fn2-range-sources))))
       (mv :bounds fn2-reads fn2-ranges fn2-range-sources))
      ((unless (fn2-range-keys-ok sid)) (mv :key-kind fn2-reads fn2-ranges fn2-range-sources))
      (fn2-reads (fn2-reads-put x (op *fn2-read-op-range*) (sid sid) (entry 0)))
      ((mv code fn2-ranges fn2-range-sources)
       (fn2-rd-range-start x sid pfield plimit b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)))
  (mv code fn2-reads fn2-ranges fn2-range-sources)))
(fn2-rd-shape fn2-rd-range (x sid pfield plimit b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
 ((fn2-reads 1) (fn2-ranges 2) (fn2-range-sources 3))
 (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
 ((:keep fn2-rd-range-args-ok) fn2-rd-range-start fn2-range-keys-ok))

; Amendment (b): every overlay source of range G still holds the overlay
; taking it located (phase active or frozen, the range's schema, its SEQ).
(defun fn2-rd-sources-live (n g fn2-ranges fn2-range-sources fn2-overlays)
 (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-overlays) :measure (nfix n)
  :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays)
   (natp n))))
 (b* (((when (zp n)) t)
      ((unless (and (natp g) (< g (fn2-ranges-rows fn2-ranges)))) nil)
      (s (+ (fn2-ranges-sbase g fn2-ranges) (- n 1)))
      ((unless (< s (fn2-range-sources-rows fn2-range-sources))) nil)
      ((unless (equal (fn2-range-sources-kind s fn2-range-sources) *fn2-range-kind-overlay*))
       (fn2-rd-sources-live (- n 1) g fn2-ranges fn2-range-sources fn2-overlays))
      (o (fn2-range-sources-src s fn2-range-sources)))
  (and (< o (fn2-overlays-rows fn2-overlays))
       (member (fn2-overlays-phase o fn2-overlays) (list *fn2-overlay-phase-active* *fn2-overlay-phase-frozen*))
       (equal (fn2-overlays-schema o fn2-overlays) (fn2-ranges-schema g fn2-ranges))
       (equal (fn2-overlays-seq o fn2-overlays) (fn2-range-sources-run s fn2-range-sources))
       (fn2-rd-sources-live (- n 1) g fn2-ranges fn2-range-sources fn2-overlays))))
(in-theory (disable fn2-rd-sources-live))

; Range G between steps: a stale overlay source re-finds every source
; strictly after the resume key (the query rows hold the delivered key's
; successor). A range not merging holds no source to check.
(defun fn2-rd-refresh (g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
  :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays)
              (fn2-run-installed-wfp fn2-run-installed))
  :guard-hints (("Goal" :in-theory (disable fn2-range-enumerate fn2-rd-sources-live)))))
 (if (and (natp g) (< g (fn2-ranges-rows fn2-ranges))
          (member (fn2-ranges-phase g fn2-ranges) (list *fn2-range-phase-seek* *fn2-range-phase-merge*))
          (not (fn2-rd-sources-live (fn2-ranges-scount g fn2-ranges) g fn2-ranges fn2-range-sources fn2-overlays)))
     (fn2-range-enumerate g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
   (mv :ok fn2-ranges fn2-range-sources)))
(fn2-rd-shape fn2-rd-refresh (g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 ((fn2-ranges 1) (fn2-range-sources 2)) (fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 (fn2-range-enumerate fn2-rd-sources-live fn2-ranges-phase fn2-ranges-scount))

; One bounded step of read row X's range: :entry (delivered: the row reads
; it until its next step), :end, :more, :miss, or a refusal; :state when
; the row holds no range.
(defun fn2-rd-next (x budget fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                    fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-range-step fn2-rd-refresh fn2-ranges-schema fn2-ranges-out fn2-ranges-ok
                                            fn2-ranges-os fn2-ranges-og fn2-run-version fn2-reads-rows fn2-ranges-rows fn2-range-sources-rows fn2-seeks-rows fn2-run-cursors-rows fn2-run-paths-rows fn2-fields-rows fn2-pool-rows)))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-rga-guard)))
       (mv :state fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (natp x) (< x (fn2-reads-rows fn2-reads)) (< x (fn2-ranges-rows fn2-ranges)) (natp budget) (<= budget 4096)))
       (mv :bounds fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (equal (fn2-reads-op x fn2-reads) *fn2-read-op-range*))
       (mv :state fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      (fn2-reads (fn2-reads-set-entry x 0 fn2-reads))
      ((mv code fn2-ranges fn2-range-sources) (fn2-rd-refresh x fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed))
      ((unless (eq code :ok)) (mv code fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((mv code fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-range-step x budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                       fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
      ((unless (eq code :entry)) (mv code fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (< x (fn2-ranges-rows fn2-ranges))) (mv :bounds fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      (sid (fn2-ranges-schema x fn2-ranges))
      (ever (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed))
      (out (fn2-ranges-out x fn2-ranges)) (ok (fn2-ranges-ok x fn2-ranges))
      (os (fn2-ranges-os x fn2-ranges)) (og (fn2-ranges-og x fn2-ranges))
      ((unless (and (unsigned-byte-p 60 ever) (unsigned-byte-p 32 out) (unsigned-byte-p 8 ok) (unsigned-byte-p 32 os)
                    (unsigned-byte-p 60 og)))
       (mv :bounds fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      (fn2-reads (fn2-reads-put x (entry 1) (erow out) (ek ok) (es os) (eg og) (ever ever))))
  (mv :entry fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
(fn2-rd-shape fn2-rd-next (x budget fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                           fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-reads 1) (fn2-ranges 2) (fn2-range-sources 3) (fn2-run-cursors 4) (fn2-run-paths 5) (fn2-fields 6))
 (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths
  fn2-run-cache fn2-fields fn2-pool)
 (fn2-rd-refresh fn2-range-step fn2-run-version fn2-reads-op fn2-ranges-schema fn2-ranges-out fn2-ranges-ok fn2-ranges-os
  fn2-ranges-og (:keep fn2-reads-rows)))

; ---------------------------------------------------------------------------
; Positioned seek (INBOX 4.1) of read row X over SID: the caller holds the
; stream's key prefix (every key field but the last) in the lo and hi
; regions; the answer is the least last-field value in [LO, HI] from which
; every entry has a position above P (PFIELD the position field).
(defun fn2-rd-seek (x sid lo hi p pfield b0 tn fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays
                    fn2-run-installed fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
   :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-rd-range fn2-seek-start fn2-reads-rows fn2-ranges-rows fn2-range-sources-rows fn2-seeks-rows fn2-run-cursors-rows fn2-run-paths-rows fn2-fields-rows fn2-pool-rows)))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-seeks-wfp fn2-seeks) (fn2-ranges-wfp fn2-ranges)
                    (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays)
                    (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields)))
       (mv :state fn2-reads fn2-seeks fn2-ranges fn2-range-sources))
      ((unless (and (natp x) (< x (fn2-seeks-rows fn2-seeks)) (unsigned-byte-p 32 x)))
       (mv :bounds fn2-reads fn2-seeks fn2-ranges fn2-range-sources))
      ((mv code fn2-reads fn2-ranges fn2-range-sources)
       (fn2-rd-range x sid *fn2-range-no-position* 0 b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays
                     fn2-run-installed fn2-fields))
      ((unless (eq code :ok)) (mv code fn2-reads fn2-seeks fn2-ranges fn2-range-sources))
      ((mv code fn2-seeks) (fn2-seek-start x x lo hi p pfield fn2-seeks))
      ((unless (and (eq code :ok) (natp x) (< x (fn2-reads-rows fn2-reads))))
       (mv (if (eq code :ok) :bounds code) fn2-reads fn2-seeks fn2-ranges fn2-range-sources))
      (fn2-reads (fn2-reads-set-op x *fn2-read-op-seek* fn2-reads)))
  (mv :ok fn2-reads fn2-seeks fn2-ranges fn2-range-sources)))
(fn2-rd-shape fn2-rd-seek (x sid lo hi p pfield b0 tn fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays
                           fn2-run-installed fn2-fields)
 ((fn2-reads 1) (fn2-seeks 2) (fn2-ranges 3) (fn2-range-sources 4))
 (fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
 (fn2-rd-range fn2-seek-start))

; One bounded step of read row X's seek: :done with the answer, :more,
; :miss, or a refusal; :state when the row holds no seek.
(defun fn2-rd-seek-step (x budget fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
                         fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
   fn2-run-installed
                          fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-seek-step fn2-rd-refresh fn2-seeks-lo fn2-reads-rows fn2-ranges-rows fn2-range-sources-rows fn2-seeks-rows fn2-run-cursors-rows fn2-run-paths-rows fn2-fields-rows fn2-pool-rows)))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-seeks-wfp fn2-seeks) (fn2-rga-guard)))
       (mv :state 0 fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (natp x) (< x (fn2-reads-rows fn2-reads)) (< x (fn2-seeks-rows fn2-seeks)) (natp budget) (<= budget 4096)))
       (mv :bounds 0 fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (equal (fn2-reads-op x fn2-reads) *fn2-read-op-seek*))
       (mv :state 0 fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((mv code fn2-ranges fn2-range-sources)
       (if (equal (fn2-seeks-phase x fn2-seeks) *fn2-seek-phase-read*)
           (fn2-rd-refresh (fn2-seeks-g x fn2-seeks) fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
         (mv :ok fn2-ranges fn2-range-sources)))
      ((unless (eq code :ok)) (mv code 0 fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((mv code fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-seek-step x budget fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                      fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
      ((unless (and (eq code :done) (< x (fn2-seeks-rows fn2-seeks))))
       (mv code 0 fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
  (mv :done (nfix (fn2-seeks-lo x fn2-seeks)) fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
(fn2-rd-shape fn2-rd-seek-step (x budget fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
                                fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-seeks 2) (fn2-ranges 3) (fn2-range-sources 4) (fn2-run-cursors 5) (fn2-run-paths 6) (fn2-fields 7))
 (fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors
  fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (fn2-seek-step fn2-rd-refresh fn2-reads-op fn2-seeks-phase fn2-seeks-g fn2-seeks-lo))
(defthm fn2-rd-seek-step-natp
 (natp (mv-nth 1 (fn2-rd-seek-step x budget fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
                                   fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
 :hints (("Goal" :in-theory (enable fn2-rd-seek-step))) :rule-classes :type-prescription)

; ---------------------------------------------------------------------------
; The delivered entry. Row ROW of it (field F), while the schema's run
; version is the one it was delivered under: (mv code row).
(defun fn2-rd-entry-row (x f fn2-reads fn2-run-installed fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-run-installed fn2-fields) :guard t))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields)))
       (mv :state 0))
      ((unless (and (natp x) (< x (fn2-reads-rows fn2-reads)) (natp f))) (mv :bounds 0))
      ((unless (equal (fn2-reads-entry x fn2-reads) 1)) (mv :state 0))
      (sid (fn2-reads-sid x fn2-reads))
      ((unless (equal (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed)
                      (fn2-reads-ever x fn2-reads)))
       (mv :stale 0))
      ((unless (< f (fn2-run-layout-fields sid nil))) (mv :bounds 0))
      (row (+ (nfix (fn2-reads-erow x fn2-reads)) f))
      ((unless (< row (fn2-fields-rows fn2-fields))) (mv :bounds 0)))
  (mv :ok row)))
(defthm fn2-rd-entry-row-natp (natp (mv-nth 1 (fn2-rd-entry-row x f fn2-reads fn2-run-installed fn2-fields)))
 :rule-classes :type-prescription)
(defthm fn2-rd-entry-row-bound
 (implies (and (equal (mv-nth 0 (fn2-rd-entry-row x f fn2-reads fn2-run-installed fn2-fields)) :ok))
          (< (mv-nth 1 (fn2-rd-entry-row x f fn2-reads fn2-run-installed fn2-fields)) (fn2-fields-rows fn2-fields)))
 :rule-classes :linear)
(in-theory (disable fn2-rd-entry-row))

; Integer field F of the entry: (mv code value).
(defun fn2-rd-value (x f fn2-reads fn2-run-installed fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-run-installed fn2-fields) :guard t))
 (b* (((mv code row) (fn2-rd-entry-row x f fn2-reads fn2-run-installed fn2-fields))
      ((unless (and (eq code :ok) (fn2-fields-wfp fn2-fields))) (mv (if (eq code :ok) :state code) 0)))
  (mv :ok (fn2-fields-value row fn2-fields))))


; Copy at most N octets of the entry's octet field F, from octet FROM, to
; DSLOT/DGEN at DOFF (written under DK DS DG): (mv code copied left), LEFT
; the field's octets after the copied ones.
(defun fn2-rd-copy (n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix n) :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp soff) (natp doff))
  :guard-hints (("Goal" :in-theory (disable fn2-pool-read fn2-pool-write)))))
 (if (zp n) (mv :ok fn2-pool)
  (b* (((mv code byte) (fn2-pool-read sslot sgen soff sk ss sg fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool))
       ((mv code fn2-pool) (fn2-pool-write dslot dgen doff byte dk ds dg fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool)))
   (fn2-rd-copy (- n 1) sslot sgen (+ 1 soff) sk ss sg dslot dgen (+ 1 doff) dk ds dg fn2-pool))))
(fn2-pool-preserves fn2-rd-copy (n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool) :position 1
 :hints (("Goal" :in-theory (disable fn2-pool-read fn2-pool-write fn2-pool-rows))))
(defun fn2-rd-octets (x f from n dslot dgen doff dk ds dg fn2-reads fn2-run-installed fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-run-installed fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-rd-copy fn2-rd-entry-row fn2-fields-ref-len fn2-fields-ref-slot fn2-fields-ref-gen
                                            fn2-fields-ref-off fn2-fields-rows fn2-reads-rows)))))
 (b* (((unless (fn2-pool-wfp fn2-pool)) (mv :state 0 0 fn2-pool))
      ((mv code row) (fn2-rd-entry-row x f fn2-reads fn2-run-installed fn2-fields))
      ((unless (and (eq code :ok) (fn2-fields-wfp fn2-fields) (fn2-reads-wfp fn2-reads) (natp x) (< x (fn2-reads-rows fn2-reads))))
       (mv (if (eq code :ok) :state code) 0 0 fn2-pool))
      ((unless (and (natp from) (natp n) (<= n 4096) (natp doff))) (mv :bounds 0 0 fn2-pool))
      (len (nfix (fn2-fields-ref-len row fn2-fields)))
      ((unless (<= from len)) (mv :bounds 0 0 fn2-pool))
      (k (min n (- len from)))
      ((mv code fn2-pool)
       (fn2-rd-copy k (fn2-fields-ref-slot row fn2-fields) (fn2-fields-ref-gen row fn2-fields)
                    (+ (nfix (fn2-fields-ref-off row fn2-fields)) from) (fn2-reads-ek x fn2-reads) (fn2-reads-es x fn2-reads)
                    (fn2-reads-eg x fn2-reads) dslot dgen doff dk ds dg fn2-pool))
      ((unless (eq code :ok)) (mv code 0 0 fn2-pool)))
  (mv :ok k (- len (+ from k)) fn2-pool)))
(fn2-pool-preserves fn2-rd-octets (x f from n dslot dgen doff dk ds dg fn2-reads fn2-run-installed fn2-fields fn2-pool) :position 3
 :hints (("Goal" :in-theory (disable fn2-rd-copy fn2-rd-entry-row fn2-pool-rows))))
(in-theory (disable fn2-rd-copy fn2-rd-octets fn2-rd-value))

; ---------------------------------------------------------------------------
; Release read row X: its range, seek and lookup idle, its query owner and
; entry gone.
(defun fn2-rd-release (x tn fn2-reads fn2-ranges fn2-seeks fn2-succ-txns)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-seeks fn2-succ-txns) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-xl-done)))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-ranges-wfp fn2-ranges) (fn2-seeks-wfp fn2-seeks) (fn2-succ-txns-wfp fn2-succ-txns)))
       (mv :state fn2-reads fn2-ranges fn2-seeks fn2-succ-txns))
      ((unless (and (natp x) (< x (fn2-reads-rows fn2-reads)) (< x (fn2-ranges-rows fn2-ranges)) (< x (fn2-seeks-rows fn2-seeks))
                    (natp tn) (< (+ tn x) (fn2-succ-txns-rows fn2-succ-txns))))
       (mv :bounds fn2-reads fn2-ranges fn2-seeks fn2-succ-txns))
      ((mv & fn2-succ-txns) (fn2-xl-done (+ tn x) :ok fn2-succ-txns))
      (fn2-ranges (fn2-ranges-set-phase x *fn2-range-phase-idle* fn2-ranges))
      (fn2-seeks (fn2-seeks-set-phase x *fn2-seek-phase-idle* fn2-seeks))
      (fn2-reads (fn2-reads-put x (op *fn2-read-op-idle*) (sid 0) (qset 0) (qk 0) (qs 0) (qg 0) (entry 0) (erow 0)
                                (ek 0) (es 0) (eg 0) (ever 0) (wslot 0) (wgen 0) (excl 0) (found 0) (selected 0) (evidence 0))))
  (mv :ok fn2-reads fn2-ranges fn2-seeks fn2-succ-txns)))
(fn2-rd-shape fn2-rd-release (x tn fn2-reads fn2-ranges fn2-seeks fn2-succ-txns)
 ((fn2-reads 1) (fn2-ranges 2) (fn2-seeks 3) (fn2-succ-txns 4)) (fn2-reads fn2-ranges fn2-seeks fn2-succ-txns)
 (fn2-xl-done))

; ---------------------------------------------------------------------------
; C-S4 (d), (e): ordered scans. The range read's sources and merge, with the
; scan's own resume: the delivered key itself, skipped once. A scan between
; steps re-finds its sources from the query when the schema's run version
; moved or an overlay source is stale: (mv code moved ranges sources).
(defun fn2-rd-scan-refresh (g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
  :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays)
              (fn2-run-installed-wfp fn2-run-installed))
  :guard-hints (("Goal" :in-theory (disable fn2-range-enumerate fn2-rd-sources-live fn2-run-version)))))
 (if (and (natp g) (< g (fn2-ranges-rows fn2-ranges))
          (member (fn2-ranges-phase g fn2-ranges) (list *fn2-range-phase-seek* *fn2-range-phase-merge*))
          (or (not (equal (fn2-run-version (fn2-ranges-schema g fn2-ranges) (fn2-run-installed-rows fn2-run-installed)
                                           fn2-run-installed)
                          (fn2-ranges-vrun g fn2-ranges)))
              (not (fn2-rd-sources-live (fn2-ranges-scount g fn2-ranges) g fn2-ranges fn2-range-sources fn2-overlays))))
     (mv-let (code fn2-ranges fn2-range-sources) (fn2-range-enumerate g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
      (mv code t fn2-ranges fn2-range-sources))
   (mv :ok nil fn2-ranges fn2-range-sources)))
(fn2-rd-shape fn2-rd-scan-refresh (g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 ((fn2-ranges 2) (fn2-range-sources 3)) (fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 (fn2-range-enumerate fn2-rd-sources-live fn2-run-version fn2-ranges-phase fn2-ranges-scount fn2-ranges-schema fn2-ranges-vrun))

; Every source among BASE..BASE+N-1 whose head equals the query at QBASE
; (read under QK QS QG) moves on: (mv code changed sources).
(defun fn2-rd-skip-equal (n base sid qbase qk qs qg changed fn2-range-sources fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-range-sources fn2-fields fn2-pool) :measure (nfix n)
  :guard (and (fn2-range-sources-wfp fn2-range-sources) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (natp n) (natp base) (natp qbase))))
 (b* (((when (zp n)) (mv :ok changed fn2-range-sources))
      (s (+ base (- n 1)))
      ((unless (and (< s (fn2-range-sources-rows fn2-range-sources))
                    (equal (fn2-range-sources-state s fn2-range-sources) *fn2-range-state-head*)))
       (fn2-rd-skip-equal (- n 1) base sid qbase qk qs qg changed fn2-range-sources fn2-fields fn2-pool))
      (eb (+ (fn2-range-sources-rb s fn2-range-sources) *fn2-run-reader-entry*))
      ((unless (and (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))
                    (<= (+ qbase *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))))
       (mv :bounds changed fn2-range-sources))
      ((mv code order) (fn2-run-layout-compare sid eb qbase (fn2-range-sources-okind s fn2-range-sources)
                                               (fn2-range-sources-oslot s fn2-range-sources)
                                               (fn2-range-sources-ogen s fn2-range-sources) qk qs qg fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code changed fn2-range-sources))
      (fn2-range-sources (if (eq order :eq) (fn2-range-sources-set-state s *fn2-range-state-next* fn2-range-sources)
                           fn2-range-sources)))
  (fn2-rd-skip-equal (- n 1) base sid qbase qk qs qg (or changed (eq order :eq)) fn2-range-sources fn2-fields fn2-pool)))
(fn2-range-sources-preserves fn2-rd-skip-equal (n base sid qbase qk qs qg changed fn2-range-sources fn2-fields fn2-pool)
 :position 2 :raw-rows t
 :hyps ((fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources) (natp base)))
(in-theory (disable fn2-rd-skip-equal))

; Key fields J..NK-1 of the entry at EB (octets read under EK ES EG) become
; the query at QBASE: an integer field by value, an octet field copied into
; WSLOT/WGEN from offset WOFF on (written under WK WS WG, the query owner).
(defun fn2-rd-key-save (j nk sid eb ek es eg qbase woff wslot wgen wk ws wg fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :measure (nfix (- (nfix nk) (nfix j)))
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-rd-copy)))))
 (b* (((unless (and (natp j) (natp nk) (< j nk))) (mv :ok fn2-fields fn2-pool))
      ((unless (and (natp eb) (natp qbase) (natp woff) (< (+ eb j) (fn2-fields-rows fn2-fields))
                    (< (+ qbase j) (fn2-fields-rows fn2-fields)) (unsigned-byte-p 32 wslot) (unsigned-byte-p 60 wgen)))
       (mv :bounds fn2-fields fn2-pool))
      (v (nfix (fn2-fields-value (+ eb j) fn2-fields)))
      ((unless (unsigned-byte-p 60 v)) (mv :bounds fn2-fields fn2-pool))
      ((unless (fn2-run-layout-octets-max sid j))
       (let ((fn2-fields (fn2-fields-put (+ qbase j) (value v) (ref-slot 0) (ref-gen 0) (ref-off 0) (ref-len 0))))
        (fn2-rd-key-save (+ 1 j) nk sid eb ek es eg qbase woff wslot wgen wk ws wg fn2-fields fn2-pool)))
      (len (nfix (fn2-fields-ref-len (+ eb j) fn2-fields)))
      ((unless (and (<= len *fn2-run-key-octets-max*) (unsigned-byte-p 32 (+ woff len)))) (mv :bounds fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-rd-copy len (fn2-fields-ref-slot (+ eb j) fn2-fields) (fn2-fields-ref-gen (+ eb j) fn2-fields)
                                       (nfix (fn2-fields-ref-off (+ eb j) fn2-fields)) ek es eg wslot wgen woff wk ws wg fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields fn2-pool))
      (fn2-fields (fn2-fields-put (+ qbase j) (value v) (ref-slot wslot) (ref-gen wgen) (ref-off woff) (ref-len len))))
  (fn2-rd-key-save (+ 1 j) nk sid eb ek es eg qbase (+ woff len) wslot wgen wk ws wg fn2-fields fn2-pool)))
(fn2-rd-shape fn2-rd-key-save (j nk sid eb ek es eg qbase woff wslot wgen wk ws wg fn2-fields fn2-pool)
 ((fn2-fields 1) (fn2-pool 2)) (fn2-fields fn2-pool)
 (fn2-rd-copy fn2-run-layout-octets-max fn2-fields-value fn2-fields-ref-len fn2-fields-ref-slot fn2-fields-ref-gen
  fn2-fields-ref-off))

; A scan step's first half: read row X's range re-found when stale, its
; overlays re-checked, every source advanced (one bounded step each).
; (mv code moved ranges sources cursors paths fields)
(defun fn2-rd-scan-advance (x budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                            fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-rd-scan-refresh fn2-range-recheck fn2-range-advance-all fn2-ranges-scount
                                            fn2-ranges-rows fn2-range-sources-rows fn2-run-cursors-rows fn2-run-paths-rows
                                            fn2-fields-rows fn2-pool-rows)))))
 (b* (((unless (fn2-rga-guard)) (mv :state nil fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (natp x) (< x (fn2-ranges-rows fn2-ranges)) (natp budget) (<= budget 4096)))
       (mv :bounds nil fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((mv code moved fn2-ranges fn2-range-sources) (fn2-rd-scan-refresh x fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed))
      ((unless (and (eq code :ok) (< x (fn2-ranges-rows fn2-ranges))))
       (mv (if (eq code :ok) :bounds code) moved fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      (n (fn2-ranges-scount x fn2-ranges))
      ((unless (unsigned-byte-p 32 n)) (mv :bounds moved fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((mv code fn2-range-sources) (fn2-range-recheck n x fn2-ranges fn2-range-sources fn2-overlays))
      ((unless (eq code :ok)) (mv code moved fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((mv code fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-range-advance-all n x budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                              fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
  (mv code moved fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
(fn2-rd-shape fn2-rd-scan-advance (x budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                                   fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-ranges 2) (fn2-range-sources 3) (fn2-run-cursors 4) (fn2-run-paths 5) (fn2-fields 6))
 (fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
  fn2-fields fn2-pool)
 (fn2-rd-scan-refresh fn2-range-recheck fn2-range-advance-all fn2-ranges-scount))

; A scan step's second half, every source at a head or its end: with
; RESUME and a key delivered before, a source still at that key moves on
; first (:more); else the least head is delivered (:entry), its key saved
; as the query when RESUME, or :end past the last.
; (mv code reads ranges sources fields pool)
(defun fn2-rd-scan-deliver (x resume fn2-reads fn2-ranges fn2-range-sources fn2-run-installed fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-run-installed fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-range-pick fn2-range-consume fn2-rd-skip-equal fn2-rd-key-save fn2-run-version
                                            fn2-ranges-schema fn2-ranges-sbase fn2-ranges-scount fn2-ranges-qbase
                                            fn2-range-sources-rb fn2-range-sources-okind fn2-range-sources-oslot
                                            fn2-range-sources-ogen fn2-reads-qk fn2-reads-qs fn2-reads-qg fn2-reads-wslot
                                            fn2-reads-wgen fn2-reads-excl fn2-reads-rows fn2-ranges-rows
                                            fn2-range-sources-rows fn2-fields-rows fn2-pool-rows)))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources)
                    (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool))
      ((unless (and (natp x) (< x (fn2-reads-rows fn2-reads)) (< x (fn2-ranges-rows fn2-ranges))))
       (mv :bounds fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool))
      (sid (fn2-ranges-schema x fn2-ranges)) (sbase (fn2-ranges-sbase x fn2-ranges))
      (n (fn2-ranges-scount x fn2-ranges)) (qbase (fn2-ranges-qbase x fn2-ranges))
      (qk (fn2-reads-qk x fn2-reads)) (qs (fn2-reads-qs x fn2-reads)) (qg (fn2-reads-qg x fn2-reads))
      (wslot (fn2-reads-wslot x fn2-reads)) (wgen (fn2-reads-wgen x fn2-reads)) (excl (fn2-reads-excl x fn2-reads))
      ((unless (and (unsigned-byte-p 60 sid) (unsigned-byte-p 32 sbase) (unsigned-byte-p 32 n) (unsigned-byte-p 32 qbase)))
       (mv :bounds fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool))
      ((mv code changed fn2-range-sources)
       (if (and resume (equal excl 1))
           (fn2-rd-skip-equal n sbase sid qbase qk qs qg nil fn2-range-sources fn2-fields fn2-pool)
         (mv :ok nil fn2-range-sources)))
      ((unless (eq code :ok)) (mv code fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool))
      ((when changed) (mv :more fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool))
      ((mv code best) (fn2-range-pick n sbase sid nil fn2-range-sources fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool))
      ((unless (and (natp best) (< best (fn2-range-sources-rows fn2-range-sources))))
       (let ((fn2-ranges (fn2-ranges-set-phase x *fn2-range-phase-done* fn2-ranges)))
        (mv :end fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool)))
      (eb (+ (nfix (fn2-range-sources-rb best fn2-range-sources)) *fn2-run-reader-entry*))
      (ok (fn2-range-sources-okind best fn2-range-sources)) (os (fn2-range-sources-oslot best fn2-range-sources))
      (og (fn2-range-sources-ogen best fn2-range-sources))
      ((unless (and (unsigned-byte-p 32 eb) (unsigned-byte-p 8 ok) (unsigned-byte-p 32 os) (unsigned-byte-p 60 og)))
       (mv :bounds fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool))
      ((mv code fn2-range-sources) (fn2-range-consume n sbase sid best fn2-range-sources fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool))
      ((mv code fn2-fields fn2-pool)
       (if resume
           (fn2-rd-key-save 0 (fn2-run-layout-keys sid) sid eb ok os og qbase 0 wslot wgen qk qs qg fn2-fields fn2-pool)
         (mv :ok fn2-fields fn2-pool)))
      ((unless (eq code :ok)) (mv code fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool))
      (ever (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed))
      ((unless (unsigned-byte-p 60 ever)) (mv :bounds fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool))
      (fn2-ranges (fn2-ranges-set-phase x *fn2-range-phase-merge* fn2-ranges))
      (fn2-reads (fn2-reads-put x (entry 1) (erow eb) (ek ok) (es os) (eg og) (ever ever) (excl (if resume 1 0)))))
  (mv :entry fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool)))
(fn2-rd-shape fn2-rd-scan-deliver (x resume fn2-reads fn2-ranges fn2-range-sources fn2-run-installed fn2-fields fn2-pool)
 ((fn2-reads 1) (fn2-ranges 2) (fn2-range-sources 3) (fn2-fields 4) (fn2-pool 5))
 (fn2-reads fn2-ranges fn2-range-sources fn2-run-installed fn2-fields fn2-pool)
 (fn2-range-pick fn2-range-consume fn2-rd-skip-equal fn2-rd-key-save fn2-run-version fn2-ranges-schema fn2-ranges-sbase
  fn2-ranges-scount fn2-ranges-qbase fn2-range-sources-rb fn2-range-sources-okind fn2-range-sources-oslot
  fn2-range-sources-ogen fn2-reads-qk fn2-reads-qs fn2-reads-qg fn2-reads-wslot fn2-reads-wgen fn2-reads-excl))

; One bounded step of read row X's ordered scan: :entry (delivered as a
; range's is), :end, :more, :miss, or a refusal; MOVED when its sources were
; found again. RESUME: the delivered key becomes the query and is skipped
; once (a scan that renders, LIST); otherwise the query stays the scan's
; start and a move restarts it there (the identity read, which recounts).
; (mv code moved reads ranges sources cursors paths fields pool)
(defun fn2-rd-scan-step (x budget resume fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                         fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-rd-scan-advance fn2-rd-scan-deliver fn2-reads-rows)))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (natp x) (< x (fn2-reads-rows fn2-reads))))
       (mv :state nil fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool))
      (fn2-reads (fn2-reads-set-entry x 0 fn2-reads))
      ((mv code moved fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-rd-scan-advance x budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                            fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code moved fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool))
      ((mv code fn2-reads fn2-ranges fn2-range-sources fn2-fields fn2-pool)
       (fn2-rd-scan-deliver x resume fn2-reads fn2-ranges fn2-range-sources fn2-run-installed fn2-fields fn2-pool)))
  (mv code moved fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool)))
(fn2-rd-shape fn2-rd-scan-step (x budget resume fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
                                fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-reads 2) (fn2-ranges 3) (fn2-range-sources 4) (fn2-run-cursors 5) (fn2-run-paths 6) (fn2-fields 7) (fn2-pool 8))
 (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths
  fn2-run-cache fn2-fields fn2-pool)
 (fn2-rd-scan-advance fn2-rd-scan-deliver))

; The least key of SID in the lo region from field J on: integers 0, octet
; fields empty references into WSLOT/WGEN.
(defun fn2-rd-key-least (j nk sid b0 wslot wgen fn2-fields)
 (declare (xargs :stobjs fn2-fields :measure (nfix (- (nfix nk) (nfix j))) :guard (fn2-fields-wfp fn2-fields)))
 (b* (((unless (and (natp j) (natp nk) (< j nk))) (mv :ok fn2-fields))
      ((unless (and (natp b0) (< (+ b0 *fn2-read-lo* j) (fn2-fields-rows fn2-fields)) (unsigned-byte-p 32 wslot)
                    (unsigned-byte-p 60 wgen)))
       (mv :bounds fn2-fields))
      (fn2-fields (if (fn2-run-layout-octets-max sid j)
                      (fn2-fields-put (+ b0 *fn2-read-lo* j) (value 0) (ref-slot wslot) (ref-gen wgen) (ref-off 0) (ref-len 0))
                    (fn2-fields-put (+ b0 *fn2-read-lo* j) (value 0) (ref-slot 0) (ref-gen 0) (ref-off 0) (ref-len 0)))))
  (fn2-rd-key-least (+ 1 j) nk sid b0 wslot wgen fn2-fields)))
(fn2-rd-shape fn2-rd-key-least (j nk sid b0 wslot wgen fn2-fields) ((fn2-fields 1)) (fn2-fields) (fn2-run-layout-octets-max))

; Start read row X's whole-schema scan of SID from its least key; the
; resume key's octets live in WSLOT/WGEN, written and read under WK WS WG.
(defun fn2-rd-scan (x sid wslot wgen wk ws wg b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields) :guard t
  :guard-hints (("Goal" :in-theory (e/d (fn2-rd-range-args-ok) (fn2-rd-range-start fn2-rd-key-least fn2-reads-rows
                                                                 fn2-fields-rows fn2-ranges-rows fn2-range-sources-rows))))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources)
                    (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields)))
       (mv :state fn2-reads fn2-ranges fn2-range-sources fn2-fields))
      ((unless (and (fn2-rd-range-args-ok x sid b0 tn fn2-reads fn2-fields) (< x (fn2-ranges-rows fn2-ranges))
                    (<= (* *fn2-read-sources* (+ x 1)) (fn2-range-sources-rows fn2-range-sources))
                    (unsigned-byte-p 32 wslot) (unsigned-byte-p 60 wgen) (unsigned-byte-p 8 wk) (unsigned-byte-p 32 ws)
                    (unsigned-byte-p 60 wg) (posp (fn2-run-layout-keys sid))))
       (mv :bounds fn2-reads fn2-ranges fn2-range-sources fn2-fields))
      ((mv code fn2-fields) (fn2-rd-key-least 0 (fn2-run-layout-keys sid) sid b0 wslot wgen fn2-fields))
      ((unless (and (eq code :ok) (< x (fn2-reads-rows fn2-reads))))
       (mv (if (eq code :ok) :bounds code) fn2-reads fn2-ranges fn2-range-sources fn2-fields))
      (fn2-reads (fn2-reads-put x (op *fn2-read-op-scan*) (sid sid) (entry 0) (qset 1) (qk wk) (qs ws) (qg wg)
                                (wslot wslot) (wgen wgen) (excl 0) (found 0) (selected 0) (evidence 0)))
      ((mv code fn2-ranges fn2-range-sources)
       (fn2-rd-range-start x sid *fn2-range-no-position* 0 b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays
                           fn2-run-installed)))
  (mv code fn2-reads fn2-ranges fn2-range-sources fn2-fields)))
(fn2-rd-shape fn2-rd-scan (x sid wslot wgen wk ws wg b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
 ((fn2-reads 1) (fn2-ranges 2) (fn2-range-sources 3) (fn2-fields 4))
 (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
 ((:keep fn2-rd-range-args-ok) fn2-rd-range-start fn2-rd-key-least (:keep fn2-reads-rows)))

; One step of read row X's scan: :entry, :end, :more, :miss, or a refusal;
; :state when the row holds no scan.
(defun fn2-rd-scan-next (x budget fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                         fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-rd-scan-step)))))
 (if (not (and (fn2-reads-wfp fn2-reads) (natp x) (< x (fn2-reads-rows fn2-reads))
               (equal (fn2-reads-op x fn2-reads) *fn2-read-op-scan*)))
     (mv :state fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool)
  (mv-let (code moved fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool)
    (fn2-rd-scan-step x budget t fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                      fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
   (declare (ignore moved))
   (mv code fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool))))
(fn2-rd-shape fn2-rd-scan-next (x budget fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
                                fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-reads 1) (fn2-ranges 2) (fn2-range-sources 3) (fn2-run-cursors 4) (fn2-run-paths 5) (fn2-fields 6) (fn2-pool 7))
 (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths
  fn2-run-cache fn2-fields fn2-pool)
 (fn2-rd-scan-step fn2-reads-op))

; The identity read (C-S4 (e)) of the Message-ID at [MOFF, MOFF+MLEN) of
; MSLOT/MGEN (readable under OKIND OSLOT OGEN, the same arguments on every
; call): the first call places the decision path's lower query (the
; Message-ID, an empty content) and starts a scan of the identity schema;
; each later call takes one step, over the whole block of the Message-ID in
; content order. The answer is the first half of the typed read result
; (IDENTITY-ACROSS-PEERS ruling 8) over C's engine as it stands: the
; selection (the accepted fact's article: :found, else :evidence when
; conflict evidence was met, else :absent) and the evidence status (the
; locally known conflict candidates at this cut, a count of facts, never a
; global count). Availability, coverage and authorization are not in it:
; C's engine stores (name, content) with :accepted/:conflict and at most four
; contents a name (rulings 3 and 7 replace it with attributed receipts, an
; exact lookup, a per-name summary and an evidence cursor); the gap is the
; owed row fn2-read-identity-typed. A move of the sources restarts the block.
; (mv code article candidates reads ranges sources cursors paths fields pool)
(defun fn2-rd-identity-start (x mslot mgen moff mlen okind oslot ogen b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays
                              fn2-run-installed fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields) :guard t
  :guard-hints (("Goal" :in-theory (e/d (fn2-rd-range-args-ok) (fn2-rd-range-start fn2-reads-rows fn2-fields-rows
                                                                 fn2-ranges-rows fn2-range-sources-rows))))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources)
                    (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields)))
       (mv :state fn2-reads fn2-ranges fn2-range-sources fn2-fields))
      ((unless (and (fn2-rd-range-args-ok x *fn2-read-identity-sid* b0 tn fn2-reads fn2-fields) (< x (fn2-ranges-rows fn2-ranges))
                    (<= (* *fn2-read-sources* (+ x 1)) (fn2-range-sources-rows fn2-range-sources))
                    (posp mlen) (<= mlen 250) (unsigned-byte-p 32 mslot) (unsigned-byte-p 60 mgen) (unsigned-byte-p 32 moff)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds fn2-reads fn2-ranges fn2-range-sources fn2-fields))
      (q (+ b0 *fn2-read-lo*))
      (fn2-fields (fn2-fields-put (+ q *fn2-id-mid*) (value 0) (ref-slot mslot) (ref-gen mgen) (ref-off moff) (ref-len mlen)))
      (fn2-fields (fn2-fields-put (+ q *fn2-id-con*) (value 0) (ref-slot mslot) (ref-gen mgen) (ref-off moff) (ref-len 0)))
      (fn2-reads (fn2-reads-put x (op *fn2-read-op-identity*) (sid *fn2-read-identity-sid*) (entry 0) (qset 1) (qk okind)
                                (qs oslot) (qg ogen) (excl 0) (found 0) (selected 0) (evidence 0))))
  (mv-let (code fn2-ranges fn2-range-sources)
    (fn2-rd-range-start x *fn2-read-identity-sid* *fn2-range-no-position* 0 b0 tn fn2-reads fn2-ranges fn2-range-sources
                        fn2-overlays fn2-run-installed)
   (mv code fn2-reads fn2-ranges fn2-range-sources fn2-fields))))
(fn2-rd-shape fn2-rd-identity-start (x mslot mgen moff mlen okind oslot ogen b0 tn fn2-reads fn2-ranges fn2-range-sources
                                     fn2-overlays fn2-run-installed fn2-fields)
 ((fn2-reads 1) (fn2-ranges 2) (fn2-range-sources 3) (fn2-fields 4))
 (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
 ((:keep fn2-rd-range-args-ok) fn2-rd-range-start (:keep fn2-reads-rows)))

; How the delivered entry stands to the query, by the decision path's own
; classification: :other-mid, :exact or :other (accepted), :evidence.
(defun fn2-rd-identity-class (x b0 fn2-reads fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-fields fn2-pool) :guard t))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp x)
                    (< x (fn2-reads-rows fn2-reads)) (natp b0)))
       (mv :state :other-mid 0))
      (eb (fn2-reads-erow x fn2-reads))
      ((unless (and (natp eb) (< (+ eb *fn2-identity-entry-field-article*) (fn2-fields-rows fn2-fields))
                    (< (+ eb *fn2-identity-entry-field-state*) (fn2-fields-rows fn2-fields))))
       (mv :bounds :other-mid 0))
      ;; the Message-ID compared exactly; the content is ignored (any
      ;; content of the Message-ID is its block)
      ((mv code class) (fn2-id-classify eb (fn2-reads-ek x fn2-reads) (fn2-reads-es x fn2-reads) (fn2-reads-eg x fn2-reads)
                                        (+ b0 *fn2-read-lo*) (fn2-reads-qk x fn2-reads) (fn2-reads-qs x fn2-reads)
                                        (fn2-reads-qg x fn2-reads) fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code :other-mid 0))
      ((when (eq class :other-mid)) (mv :ok :other-mid 0))
      (accepted (equal (fn2-fields-value (+ eb *fn2-identity-entry-field-state*) fn2-fields) *fn2-identity-state-accepted*)))
  (mv :ok (if accepted :accepted :evidence) (nfix (fn2-fields-value (+ eb *fn2-identity-entry-field-article*) fn2-fields)))))
(in-theory (disable fn2-rd-identity-class))

; After one scan step answered CODE (MOVED: its sources were found again):
; the identity read's accounting over the delivered entry.
; (mv code article candidates reads)
(defun fn2-rd-identity-note (x code moved b0 fn2-reads fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-rd-identity-class fn2-reads-rows fn2-reads-found fn2-reads-selected
                                            fn2-reads-evidence)))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (natp x) (< x (fn2-reads-rows fn2-reads)))) (mv :state 0 0 fn2-reads))
      (fn2-reads (if moved (fn2-reads-put x (found 0) (selected 0) (evidence 0)) fn2-reads))
      (found (equal (fn2-reads-found x fn2-reads) 1))
      (selected (nfix (fn2-reads-selected x fn2-reads)))
      (evidence (nfix (fn2-reads-evidence x fn2-reads)))
      (done (cond (found :found) ((< 0 evidence) :evidence) (t :absent)))
      ((unless (member-eq code '(:entry :end))) (mv code 0 0 fn2-reads))
      ((mv code class article)
       (if (eq code :entry) (fn2-rd-identity-class x b0 fn2-reads fn2-fields fn2-pool) (mv :ok :other-mid 0)))
      ((unless (eq code :ok)) (mv code 0 0 fn2-reads))
      ((when (eq class :other-mid))
       (let ((fn2-reads (fn2-reads-set-op x *fn2-read-op-idle* fn2-reads))) (mv done selected evidence fn2-reads)))
      ((unless (and (unsigned-byte-p 32 (+ 1 evidence)) (unsigned-byte-p 60 article))) (mv :bounds 0 0 fn2-reads))
      (fn2-reads (if (eq class :accepted)
                     (fn2-reads-put x (found 1) (selected article))
                   (fn2-reads-set-evidence x (+ 1 evidence) fn2-reads))))
  (mv :more 0 0 fn2-reads)))
(fn2-rd-shape fn2-rd-identity-note (x code moved b0 fn2-reads fn2-fields fn2-pool) ((fn2-reads 3)) (fn2-reads fn2-fields fn2-pool)
 (fn2-rd-identity-class fn2-reads-found fn2-reads-selected fn2-reads-evidence))
(defthm fn2-rd-identity-note-natp
 (and (natp (mv-nth 1 (fn2-rd-identity-note x code moved b0 fn2-reads fn2-fields fn2-pool)))
      (natp (mv-nth 2 (fn2-rd-identity-note x code moved b0 fn2-reads fn2-fields fn2-pool))))
 :hints (("Goal" :in-theory (enable fn2-rd-identity-note fn2-rd-identity-class))))

(defun fn2-rd-identity (x mslot mgen moff mlen okind oslot ogen budget b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays
                        fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-rd-identity-start fn2-rd-scan-step fn2-rd-identity-note fn2-reads-rows)))))
 (b* (((unless (and (fn2-reads-wfp fn2-reads) (natp x) (< x (fn2-reads-rows fn2-reads))))
       (mv :state 0 0 fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool))
      ((unless (equal (fn2-reads-op x fn2-reads) *fn2-read-op-identity*))
       (mv-let (code fn2-reads fn2-ranges fn2-range-sources fn2-fields)
         (fn2-rd-identity-start x mslot mgen moff mlen okind oslot ogen b0 tn fn2-reads fn2-ranges fn2-range-sources fn2-overlays
                                fn2-run-installed fn2-fields)
        (mv (if (eq code :ok) :more code) 0 0 fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields
            fn2-pool)))
      ((mv code moved fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool)
       (fn2-rd-scan-step x budget nil fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                         fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
      ((mv code article candidates fn2-reads) (fn2-rd-identity-note x code moved b0 fn2-reads fn2-fields fn2-pool)))
  (mv code article candidates fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool)))
(fn2-rd-shape fn2-rd-identity (x mslot mgen moff mlen okind oslot ogen budget b0 tn fn2-reads fn2-ranges fn2-range-sources
                               fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
                               fn2-fields fn2-pool)
 ((fn2-reads 3) (fn2-ranges 4) (fn2-range-sources 5) (fn2-run-cursors 6) (fn2-run-paths 7) (fn2-fields 8) (fn2-pool 9))
 (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths
  fn2-run-cache fn2-fields fn2-pool)
 (fn2-rd-identity-start fn2-rd-scan-step fn2-rd-identity-note fn2-reads-op))
(defthm fn2-rd-identity-natp
 (and (natp (mv-nth 1 (fn2-rd-identity x mslot mgen moff mlen okind oslot ogen budget b0 tn fn2-reads fn2-ranges fn2-range-sources
                                       fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
                                       fn2-fields fn2-pool)))
      (natp (mv-nth 2 (fn2-rd-identity x mslot mgen moff mlen okind oslot ogen budget b0 tn fn2-reads fn2-ranges fn2-range-sources
                                       fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
                                       fn2-fields fn2-pool))))
 :hints (("Goal" :in-theory (e/d (fn2-rd-identity) (fn2-rd-identity-start fn2-rd-scan-step fn2-rd-identity-note)))))

; ---------------------------------------------------------------------------
; Costs and the core wrappers.
(defcost fn2-read-key :child fn2-read-key-children :answers (:bounds :ok :state)
 :tables (fn2-core-reads fn2-core-fields)
 :doc "Write one integer key field of a read row's lo or hi key.")
(defcost fn2-read-key-octets :child fn2-read-key-octets-children :answers (:bounds :ok :owner :state)
 :tables (fn2-core-reads fn2-core-fields)
 :doc "Point one octet key field of a read row's lo key at a caller's workspace.")
(defcost fn2-read-lookup :child fn2-read-lookup-children :answers (:absent :bad-magic :bounds :done :end :entry :format :invariant :length :lost :miss :more
  :noncanonical :ok :owner :part :payload :schema :stale :state :truncated :unknown-tag :wide)
 :bytes 4096
 :tables (fn2-core-reads fn2-core-succ-txns fn2-core-run-cursors fn2-core-run-paths fn2-core-fields)
 :doc "One source of a read row's exact lookup: one overlay search or one run step of at most 4,096 pool reads.")
(defcost fn2-read-range :child fn2-read-range-children :answers (:bounds :key-kind :ok :sources :state)
 :bytes 256 :tables (fn2-core-reads fn2-core-ranges fn2-core-range-sources)
 :doc "Start a read row's range read: enumerate the schema's overlays and live runs into at most eight sources.")
; fn2-read-next never answers :ok, so :answers is open (t) until defcost takes a
; list without :ok. Its answers, from the code: :absent :bad-magic :bounds :done :end :entry :format :found :invariant :key-kind :length
;   :miss :more :noncanonical :owner :part :payload :schema :sources :stale :state :truncated
;   :unknown-tag :wide
(defcost fn2-read-next :child fn2-read-next-children :answers t
 :bytes 4096
 :tables (fn2-core-reads fn2-core-ranges fn2-core-range-sources fn2-core-run-cursors fn2-core-run-paths fn2-core-fields)
 :doc "One range step: each of at most eight sources advanced by at most the budget's pool reads, one entry delivered.")
(defcost fn2-read-seek :child fn2-read-seek-children :answers (:bounds :key-kind :ok :sources :state)
 :bytes 256 :tables (fn2-core-reads fn2-core-seeks fn2-core-ranges fn2-core-range-sources)
 :doc "Start a read row's positioned seek over its range row.")
; fn2-read-seek-step never answers :ok, so :answers is open (t) until defcost takes a
; list without :ok. Its answers, from the code: :absent :bad-magic :bounds :done :end :entry :format :found :invariant :key-kind :length
;   :miss :more :noncanonical :owner :part :payload :schema :sources :stale :state :truncated
;   :unknown-tag :wide
(defcost fn2-read-seek-step :child fn2-read-seek-step-children :answers t
 :bytes 4096
 :tables (fn2-core-seeks fn2-core-ranges fn2-core-range-sources fn2-core-run-cursors fn2-core-run-paths fn2-core-fields)
 :doc "One step of a positioned seek: a probe's range start or one range step.")
(defcost fn2-read-value :child fn2-read-value-children :answers (:bounds :ok :stale :state)
 :doc "Read one integer field of the delivered entry.")
(defcost fn2-read-octets :child fn2-read-octets-children :answers (:bounds :ok :owner :stale :state)
 :bytes 4096 :tables (fn2-core-pool)
 :doc "Copy at most 4,096 octets of the delivered entry's octet field into a workspace.")
(defcost fn2-read-scan :child fn2-read-scan-children :answers (:bounds :ok :sources :state)
 :bytes 256 :tables (fn2-core-reads fn2-core-ranges fn2-core-range-sources fn2-core-fields)
 :doc "Start a read row's whole-schema ordered scan: the least key, the schema's overlays and live runs into at most eight sources.")
; fn2-read-scan-next never answers :ok, so :answers is open (t) until defcost takes a
; list without :ok. Its answers, from the code: :absent :bad-magic :bounds :done :end :entry :format :found :invariant :length :miss :more
;   :noncanonical :owner :part :payload :schema :sources :stale :state :truncated :unknown-tag
;   :wide
(defcost fn2-read-scan-next :child fn2-read-scan-next-children :answers t
 :bytes 4096
 :tables (fn2-core-reads fn2-core-ranges fn2-core-range-sources fn2-core-run-cursors fn2-core-run-paths fn2-core-fields fn2-core-pool)
 :doc "One scan step: each of at most eight sources advanced by at most the budget's pool reads, one entry delivered and its key (at most 512 octets a field) saved.")
; fn2-read-identity never answers :ok, so :answers is open (t) until defcost takes a
; list without :ok. Its answers, from the code: :absent :bad-magic :bounds :done :end :entry :evidence :format :found :invariant :length
;   :miss :more :noncanonical :owner :part :payload :schema :sources :stale :state :truncated
;   :unknown-tag :wide
(defcost fn2-read-identity :child fn2-read-identity-children :answers t
 :bytes 4096
 :tables (fn2-core-reads fn2-core-ranges fn2-core-range-sources fn2-core-run-cursors fn2-core-run-paths fn2-core-fields fn2-core-pool)
 :doc "One step of an identity read: its start, or one scan step over the identity schema and one Message-ID comparison (at most 250 octets); the answer is (code article candidates).")
(defcost fn2-read-frontier :child fn2-succ-published :answers (:ok :state) :tables (fn2-core-id-engine)
 :doc "The served frontier, C's :published position: (mv code position). Pure: reads the engine, writes nothing.")
(defcost fn2-read-release :child fn2-read-release-children :answers (:bounds :ok :state)
 :tables (fn2-core-reads fn2-core-ranges fn2-core-seeks fn2-core-succ-txns)
 :doc "Idle a read row's range, seek and lookup.")

; Each read operation over the core children it touches (MACHINE-FORM 6.5 P2):
; the defcost names it as :child, so an arm in child form calls it directly,
; and the core wrapper below is one stobj-let around it.
(defun fn2-read-key-children (x region j value fn2-reads fn2-id-decides fn2-fields fn2-fc)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-fields fn2-fc)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-fields-wfp fn2-fields) (fn2-fc-wfp
   fn2-fc))))
 (mv-let (c b0) (fn2-read-stripe x (fn2-fc-rows fn2-fc) fn2-reads fn2-id-decides fn2-fields)
  (if (eq c :ok) (fn2-rd-key x region j value b0 fn2-reads fn2-fields) (mv c fn2-reads fn2-fields))))
(defun fn2-read-key-octets-children (x j slot gen off len okind oslot ogen fn2-reads fn2-id-decides fn2-fields fn2-fc)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-fields fn2-fc)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-fields-wfp fn2-fields) (fn2-fc-wfp
   fn2-fc))))
 (mv-let (c b0) (fn2-read-stripe x (fn2-fc-rows fn2-fc) fn2-reads fn2-id-decides fn2-fields)
  (if (eq c :ok) (fn2-rd-key-octets x j slot gen off len okind oslot ogen b0 fn2-reads fn2-fields)
    (mv c fn2-reads fn2-fields))))
(defun fn2-read-lookup-children (x sid budget fn2-reads fn2-id-decides fn2-succ-txns fn2-overlays fn2-overlay-index
  fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool fn2-fc)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed
   fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool fn2-fc)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-succ-txns-wfp fn2-succ-txns)
   (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-run-installed-wfp fn2-run-installed)
   (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp fn2-run-cache)
   (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-fc-wfp fn2-fc))))
 (mv-let (c b0) (fn2-read-stripe x (fn2-fc-rows fn2-fc) fn2-reads fn2-id-decides fn2-fields)
  (if (eq c :ok)
      (fn2-rd-lookup x sid budget b0 (fn2-id-decides-rows fn2-id-decides) fn2-reads fn2-succ-txns fn2-overlays
                     fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
    (mv c fn2-reads fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))))
(defun fn2-read-range-children (x sid pfield plimit fn2-reads fn2-id-decides fn2-ranges fn2-range-sources fn2-overlays
  fn2-run-installed fn2-fields fn2-fc)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed
   fn2-fields fn2-fc)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-ranges-wfp fn2-ranges)
   (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed)
   (fn2-fields-wfp fn2-fields) (fn2-fc-wfp fn2-fc))))
 (mv-let (c b0) (fn2-read-stripe x (fn2-fc-rows fn2-fc) fn2-reads fn2-id-decides fn2-fields)
  (if (eq c :ok)
      (fn2-rd-range x sid pfield plimit b0 (fn2-id-decides-rows fn2-id-decides) fn2-reads fn2-ranges fn2-range-sources
                    fn2-overlays fn2-run-installed fn2-fields)
    (mv c fn2-reads fn2-ranges fn2-range-sources))))
(defun fn2-read-next-children (x budget fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
  fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
   fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources)
   (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-run-installed-wfp fn2-run-installed)
   (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp fn2-run-cache)
   (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (fn2-rd-next x budget fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
              fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
(defun fn2-read-seek-children (x sid lo hi p pfield fn2-reads fn2-id-decides fn2-seeks fn2-ranges fn2-range-sources
  fn2-overlays fn2-run-installed fn2-fields fn2-fc)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-seeks fn2-ranges fn2-range-sources fn2-overlays
   fn2-run-installed fn2-fields fn2-fc)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-seeks-wfp fn2-seeks) (fn2-ranges-wfp
   fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp
   fn2-run-installed) (fn2-fields-wfp fn2-fields) (fn2-fc-wfp fn2-fc))))
 (mv-let (c b0) (fn2-read-stripe x (fn2-fc-rows fn2-fc) fn2-reads fn2-id-decides fn2-fields)
  (if (eq c :ok)
      (fn2-rd-seek x sid lo hi p pfield b0 (fn2-id-decides-rows fn2-id-decides) fn2-reads fn2-seeks fn2-ranges
                   fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
    (mv c fn2-reads fn2-seeks fn2-ranges fn2-range-sources))))
(defun fn2-read-seek-step-children (x budget fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays
  fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
   fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-seeks-wfp fn2-seeks) (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp
   fn2-range-sources) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-run-installed-wfp
   fn2-run-installed) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp
   fn2-run-cache) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (fn2-rd-seek-step x budget fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
                   fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
(defun fn2-read-value-children (x f fn2-reads fn2-run-installed fn2-fields)
 (declare (xargs :stobjs (fn2-reads fn2-run-installed fn2-fields)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields))))
 (fn2-rd-value x f fn2-reads fn2-run-installed fn2-fields))
(defun fn2-read-octets-children (x f from n dslot dgen doff dk ds dg fn2-reads fn2-run-installed fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-run-installed fn2-fields fn2-pool)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields)
   (fn2-pool-wfp fn2-pool))))
 (fn2-rd-octets x f from n dslot dgen doff dk ds dg fn2-reads fn2-run-installed fn2-fields fn2-pool))
(defun fn2-read-release-children (x fn2-reads fn2-id-decides fn2-ranges fn2-seeks fn2-succ-txns)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-ranges fn2-seeks fn2-succ-txns)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-ranges-wfp fn2-ranges) (fn2-seeks-wfp
   fn2-seeks) (fn2-succ-txns-wfp fn2-succ-txns))))
 (fn2-rd-release x (fn2-id-decides-rows fn2-id-decides) fn2-reads fn2-ranges fn2-seeks fn2-succ-txns))
(defun fn2-read-scan-children (x sid wslot wgen wk ws wg fn2-reads fn2-id-decides fn2-ranges fn2-range-sources
  fn2-overlays fn2-run-installed fn2-fields fn2-fc)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed
   fn2-fields fn2-fc)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-ranges-wfp fn2-ranges)
   (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed)
   (fn2-fields-wfp fn2-fields) (fn2-fc-wfp fn2-fc))))
 (mv-let (c b0) (fn2-read-stripe x (fn2-fc-rows fn2-fc) fn2-reads fn2-id-decides fn2-fields)
  (if (eq c :ok)
      (fn2-rd-scan x sid wslot wgen wk ws wg b0 (fn2-id-decides-rows fn2-id-decides) fn2-reads fn2-ranges fn2-range-sources
                   fn2-overlays fn2-run-installed fn2-fields)
    (mv c fn2-reads fn2-ranges fn2-range-sources fn2-fields))))
(defun fn2-read-scan-next-children (x budget fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
  fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
   fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources)
   (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-run-installed-wfp fn2-run-installed)
   (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp fn2-run-cache)
   (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (fn2-rd-scan-next x budget fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                   fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
(defun fn2-read-identity-children (x mslot mgen moff mlen okind oslot ogen budget fn2-reads fn2-id-decides fn2-ranges
  fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
  fn2-fields fn2-pool fn2-fc)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
   fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool fn2-fc)
  :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-ranges-wfp fn2-ranges)
   (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
   (fn2-run-installed-wfp fn2-run-installed) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths)
   (fn2-run-cache-wfp fn2-run-cache) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-fc-wfp fn2-fc))))
 (mv-let (c b0) (fn2-read-stripe x (fn2-fc-rows fn2-fc) fn2-reads fn2-id-decides fn2-fields)
  (if (eq c :ok)
      (fn2-rd-identity x mslot mgen moff mlen okind oslot ogen budget b0 (fn2-id-decides-rows fn2-id-decides) fn2-reads
                       fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors
                       fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
    (mv c 0 0 fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool))))

(defmacro fn2-read-core-events ()
 '(progn
   (defun fn2-read-key (x region j value fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code fn2-reads fn2-fields)
     (fn2-read-key-children x region j value fn2-reads fn2-id-decides fn2-fields fn2-fc)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-read-key (x region j value fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-key-octets (x j slot gen off len okind oslot ogen fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code fn2-reads fn2-fields)
     (fn2-read-key-octets-children x j slot gen off len okind oslot ogen fn2-reads fn2-id-decides fn2-fields fn2-fc)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-read-key-octets (x j slot gen off len okind oslot ogen fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-lookup (x sid budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core))
                (fn2-overlay-index (fn2-core-overlay-index fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
                (fn2-run-cursors (fn2-core-run-cursors fn2-core)) (fn2-run-paths (fn2-core-run-paths fn2-core))
                (fn2-run-cache (fn2-core-run-cache fn2-core)) (fn2-fields (fn2-core-fields fn2-core))
                (fn2-pool (fn2-core-pool fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code fn2-reads fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)
     (fn2-read-lookup-children x sid budget fn2-reads fn2-id-decides fn2-succ-txns fn2-overlays fn2-overlay-index
       fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool fn2-fc)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-read-lookup (x sid budget fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-range (x sid pfield plimit fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-ranges (fn2-core-ranges fn2-core)) (fn2-range-sources (fn2-core-range-sources fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code fn2-reads fn2-ranges fn2-range-sources)
     (fn2-read-range-children x sid pfield plimit fn2-reads fn2-id-decides fn2-ranges fn2-range-sources fn2-overlays
       fn2-run-installed fn2-fields fn2-fc)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-read-range (x sid pfield plimit fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-next (x budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-ranges (fn2-core-ranges fn2-core))
                (fn2-range-sources (fn2-core-range-sources fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core))
                (fn2-overlay-index (fn2-core-overlay-index fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
                (fn2-run-cursors (fn2-core-run-cursors fn2-core)) (fn2-run-paths (fn2-core-run-paths fn2-core))
                (fn2-run-cache (fn2-core-run-cache fn2-core)) (fn2-fields (fn2-core-fields fn2-core))
                (fn2-pool (fn2-core-pool fn2-core)))
     (code fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
     (fn2-read-next-children x budget fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
       fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-read-next (x budget fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-seek (x sid lo hi p pfield fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-seeks (fn2-core-seeks fn2-core)) (fn2-ranges (fn2-core-ranges fn2-core))
                (fn2-range-sources (fn2-core-range-sources fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core))
                (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-fields (fn2-core-fields fn2-core))
                (fn2-fc (fn2-core-fc fn2-core)))
     (code fn2-reads fn2-seeks fn2-ranges fn2-range-sources)
     (fn2-read-seek-children x sid lo hi p pfield fn2-reads fn2-id-decides fn2-seeks fn2-ranges fn2-range-sources
       fn2-overlays fn2-run-installed fn2-fields fn2-fc)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-read-seek (x sid lo hi p pfield fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-seek-step (x budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-seeks (fn2-core-seeks fn2-core))
                (fn2-ranges (fn2-core-ranges fn2-core)) (fn2-range-sources (fn2-core-range-sources fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
                (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-run-cursors (fn2-core-run-cursors fn2-core))
                (fn2-run-paths (fn2-core-run-paths fn2-core)) (fn2-run-cache (fn2-core-run-cache fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
     (code answer fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
     (fn2-read-seek-step-children x budget fn2-reads fn2-seeks fn2-ranges fn2-range-sources fn2-overlays
       fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
     (mv code answer fn2-core)))
   (fn2-core-preserves fn2-read-seek-step (x budget fn2-core) :position 2 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-value (x f fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)))
     (code value)
     (fn2-read-value-children x f fn2-reads fn2-run-installed fn2-fields)
     (mv code value)))
   (defun fn2-read-octets (x f from n dslot dgen doff dk ds dg fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
     (code copied left fn2-pool)
     (fn2-read-octets-children x f from n dslot dgen doff dk ds dg fn2-reads fn2-run-installed fn2-fields fn2-pool)
     (mv code copied left fn2-core)))
   (fn2-core-preserves fn2-read-octets (x f from n dslot dgen doff dk ds dg fn2-core) :position 3 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-release (x fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-ranges (fn2-core-ranges fn2-core)) (fn2-seeks (fn2-core-seeks fn2-core))
                (fn2-succ-txns (fn2-core-succ-txns fn2-core)))
     (code fn2-reads fn2-ranges fn2-seeks fn2-succ-txns)
     (fn2-read-release-children x fn2-reads fn2-id-decides fn2-ranges fn2-seeks fn2-succ-txns)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-read-release (x fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-frontier (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (fn2-successor-published fn2-core))
   (defun fn2-read-scan (x sid wslot wgen wk ws wg fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-ranges (fn2-core-ranges fn2-core)) (fn2-range-sources (fn2-core-range-sources fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code fn2-reads fn2-ranges fn2-range-sources fn2-fields)
     (fn2-read-scan-children x sid wslot wgen wk ws wg fn2-reads fn2-id-decides fn2-ranges fn2-range-sources
       fn2-overlays fn2-run-installed fn2-fields fn2-fc)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-read-scan (x sid wslot wgen wk ws wg fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-scan-next (x budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-ranges (fn2-core-ranges fn2-core))
                (fn2-range-sources (fn2-core-range-sources fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core))
                (fn2-overlay-index (fn2-core-overlay-index fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
                (fn2-run-cursors (fn2-core-run-cursors fn2-core)) (fn2-run-paths (fn2-core-run-paths fn2-core))
                (fn2-run-cache (fn2-core-run-cache fn2-core)) (fn2-fields (fn2-core-fields fn2-core))
                (fn2-pool (fn2-core-pool fn2-core)))
     (code fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool)
     (fn2-read-scan-next-children x budget fn2-reads fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
       fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-read-scan-next (x budget fn2-core) :position 1 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-read-identity (x mslot mgen moff mlen okind oslot ogen budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-reads (fn2-core-reads fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-ranges (fn2-core-ranges fn2-core)) (fn2-range-sources (fn2-core-range-sources fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
                (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-run-cursors (fn2-core-run-cursors fn2-core))
                (fn2-run-paths (fn2-core-run-paths fn2-core)) (fn2-run-cache (fn2-core-run-cache fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code article candidates fn2-reads fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields fn2-pool)
     (fn2-read-identity-children x mslot mgen moff mlen okind oslot ogen budget fn2-reads fn2-id-decides fn2-ranges
       fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
       fn2-fields fn2-pool fn2-fc)
     (mv code article candidates fn2-core)))
   (fn2-core-preserves fn2-read-identity (x mslot mgen moff mlen okind oslot ogen budget fn2-core) :position 3 :rows nil
    :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-read-key fn2-read-key-octets fn2-read-lookup fn2-read-range fn2-read-next fn2-read-seek
                       fn2-read-seek-step fn2-read-value fn2-read-octets fn2-read-release fn2-read-scan fn2-read-scan-next
                       fn2-read-identity))
   (assert-event (fn2-assert-compliant-p '(fn2-read-key fn2-read-key-octets fn2-read-lookup fn2-read-range fn2-read-next
                                           fn2-read-seek fn2-read-seek-step fn2-read-value fn2-read-octets fn2-read-release
                                           fn2-read-scan fn2-read-scan-next fn2-read-identity)
                                         (w state)))))
