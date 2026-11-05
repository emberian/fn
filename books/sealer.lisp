; Layer C1c, the sealer's engine half (docs/c-ordered-runs.md §5): a
; published (frozen) overlay becomes a sealed run through the real build,
; with a Ribbon filter for the identity summary, is installed in the resident
; view of runs (fn2-run-installed), and the overlay is retired with its arena
; released, in one step. The engine half names runs and pages itself (a run
; counter and a physical-unit counter in the seal row) and keeps every sealed
; page resident in the verified-page cache; B's run-replacement member (GC2)
; makes the run durable (the device half). The sealer machine
; (machines-c-sealer.lisp) drives fn2-seal-step from its arms. One seal row;
; its continuation is the row (phase, the overlay, the next entry, the run).
;
; Order (C-SEAL-ORDER): an overlay is sealable when it is frozen and no
; overlay of its schema that is frozen, private or active has a smaller SEQ;
; of the sealable ones the least SEQ goes first. Run identifiers grow, so run
; order follows SEQ order, and every overlay a reader still meets is newer
; than every run, which is what the readers' newest-wins rules assume.
(in-package "ACL2")
(include-book "machines-c-groups")
(fn2-book-layer :c)
(local (in-theory (disable fn2-run-layout-fields fn2-run-layout-keys fn2-run-layout-merge fn2-run-layout-size
                           fn2-fold-key-arg fn2-fold-arity fn2-fold-assigned-p fn2-run-layout-octets-max
                           fn2-run-layout-value-ok fn2-run-layout-fold-p fn2-run-version)))

; The seal row. WBASE: the build's six writer rows, then the filter's; FBASE:
; its field rows (the build's, then the decoded entry, then the filter
; writer's); CROW: its checker row (B's format-row map: 3 + the upload
; windows), whose digest stripe holds the six levels' parent-held hashes
; (regions 129-134) and the filter's (135); FILL: the page fill. RUN and UNIT
; count the identifiers handed out.
(defconst *fn2-seal-eb* *fn2-run-build-fields*)
(defconst *fn2-seal-fw* (+ *fn2-run-build-fields* *fn2-run-entry-rows*))
(defconst *fn2-seal-field-rows* (+ *fn2-seal-fw* *fn2-run-writer-fields*))
(defconst *fn2-seal-writer-rows* (+ 1 *fn2-run-max-levels*))
(defconst *fn2-seal-hash-region* 129)
(defconst *fn2-seal-filter-region* (+ *fn2-seal-hash-region* *fn2-run-max-levels*))
(assert-event (and (< *fn2-fc-previous-seal* *fn2-seal-hash-region*) (< *fn2-seal-filter-region* *fn2-digest-stride*)))
(defconst *fn2-seal-hash-bytes* (* 32 *fn2-run-max-levels*))
; The schema whose runs carry a Ribbon filter: the identity summary (§4a),
; keyed by the name N, which the identity decision reads first; the filter
; holds each entry's name.
(defconst *fn2-seal-identity* *fn2-id-summary-sid*)
(defconst *fn2-seal-filter-field* *fn2-identity-summary-entry-field-name*)
(defcolumns fn2-seals
 ((phase (:enum fn2-seal-phase (:idle :build :filter :install :failed :release)))
  (sub (:enum fn2-seal-sub (:open :clear :add :drive :finish :solve)))
  (o :u32) (pos :u32) (sid :u60) (run :u60) (runs :u60) (units :u60)
  (top :u8) (rslot :u32) (rgen :u60) (runit :u60) (rcounter :u60) (entries :u60)
  (hslot :u32) (hgen :u60) (filter :bool) (funit :u60) (fcounter :u60)
  (wbase :u32) (fbase :u32) (crow :u32) (fill :u32) (okind :u8) (oslot :u32) (ogen :u60)
  (k :u8) (rlo :u60) (ufirst :u60) (held :bool) (rg :u32) (sbase :u32) (cbase :u32) (qbase :u32) (rbase :u32)))

; Shapes (type, wfp, rows of every stobj returned), with every table's rows
; accessor folded (the shape lemmas of the callees are stated over them).
(defconst *fn2-seal-rows-folded*
 '(fn2-seals-rows fn2-run-cache-rows fn2-run-installed-rows fn2-run-builds-rows fn2-run-writers-rows fn2-run-restarts-rows
   fn2-ribbon-builds-rows fn2-ribbon-band-rows fn2-digests-rows fn2-fc-rows fn2-fc-context-rows fn2-b3-rows
   fn2-ranges-rows fn2-range-sources-rows fn2-run-cursors-rows fn2-run-paths-rows))
(defmacro fn2-seal-shape (fn args outs stobjs &optional (mode 't) reads)
 `(fn2-idc-fn-shape ,fn ,args ,outs ,stobjs ,mode ,(append reads *fn2-seal-rows-folded*)))

; Set the seal row's resources: idle, no run or unit handed out yet.
(defun fn2-seal-init (wbase fbase crow pagefill okind oslot ogen fn2-seals)
 (declare (xargs :stobjs fn2-seals :guard (fn2-seals-wfp fn2-seals)))
 (if (not (and (< 0 (fn2-seals-rows fn2-seals)) (unsigned-byte-p 32 wbase) (unsigned-byte-p 32 fbase)
               (unsigned-byte-p 32 crow) (unsigned-byte-p 32 pagefill) (unsigned-byte-p 8 okind)
               (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
     (mv :bounds fn2-seals)
  (let ((fn2-seals (fn2-seals-put 0 (phase *fn2-seal-phase-idle*) (sub *fn2-seal-sub-open*) (o 0) (pos 0) (sid 0) (run 0)
                                  (runs 0) (units 0) (filter 0) (wbase wbase) (fbase fbase) (crow crow) (fill pagefill)
                                  (okind okind) (oslot oslot) (ogen ogen))))
   (mv :ok fn2-seals))))
(fn2-seal-shape fn2-seal-init (wbase fbase crow pagefill okind oslot ogen fn2-seals) (fn2-seals) (fn2-seals))
; The merge's read resources (C5): range row RG, its eight sources from
; SBASE reading through run cursors from CBASE, the query key's field rows
; at QBASE and the sources' reader rows from RBASE.
(defun fn2-seal-merge-rows (rg sbase cbase qbase rbase fn2-seals)
 (declare (xargs :stobjs fn2-seals :guard (fn2-seals-wfp fn2-seals)))
 (if (not (and (< 0 (fn2-seals-rows fn2-seals)) (unsigned-byte-p 32 rg) (unsigned-byte-p 32 sbase) (unsigned-byte-p 32 cbase)
               (unsigned-byte-p 32 qbase) (unsigned-byte-p 32 rbase)))
     (mv :bounds fn2-seals)
  (let ((fn2-seals (fn2-seals-put 0 (k 0) (rlo 0) (held 0) (rg rg) (sbase sbase) (cbase cbase) (qbase qbase) (rbase rbase))))
   (mv :ok fn2-seals))))
(fn2-seal-shape fn2-seal-merge-rows (rg sbase cbase qbase rbase fn2-seals) (fn2-seals) (fn2-seals))

; ---------------------------------------------------------------------------
; The pick. Does an overlay of schema SID among rows O.. (K) in phase frozen,
; private or active have a SEQ below SEQ?
(defun fn2-seal-older-p (k o sid seq fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :measure (nfix k) :guard (and (fn2-overlays-wfp fn2-overlays) (natp o))))
 (and (posp k) (natp o) (< o (fn2-overlays-rows fn2-overlays))
      (or (and (member (fn2-overlays-phase o fn2-overlays)
                       (list *fn2-overlay-phase-frozen* *fn2-overlay-phase-private* *fn2-overlay-phase-active*))
               (equal (fn2-overlays-schema o fn2-overlays) sid)
               (< (nfix (fn2-overlays-seq o fn2-overlays)) (nfix seq)))
          (fn2-seal-older-p (- k 1) (+ 1 o) sid seq fn2-overlays))))
(defun fn2-seal-sealable-p (o fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :guard (fn2-overlays-wfp fn2-overlays)))
 (and (natp o) (< o (fn2-overlays-rows fn2-overlays))
      (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-frozen*)
      (not (fn2-seal-older-p (fn2-overlays-rows fn2-overlays) 0 (fn2-overlays-schema o fn2-overlays)
                             (fn2-overlays-seq o fn2-overlays) fn2-overlays))))
; The sealable overlay with the least SEQ among rows O.. (K); BEST the row
; count when none.
(defun fn2-seal-pick (k o best fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :measure (nfix k) :guard (and (fn2-overlays-wfp fn2-overlays) (natp o))))
 (if (not (and (posp k) (natp o) (< o (fn2-overlays-rows fn2-overlays)))) best
  (fn2-seal-pick (- k 1) (+ 1 o)
                 (if (and (fn2-seal-sealable-p o fn2-overlays)
                          (or (not (and (natp best) (< best (fn2-overlays-rows fn2-overlays))))
                              (< (nfix (fn2-overlays-seq o fn2-overlays)) (nfix (fn2-overlays-seq best fn2-overlays)))))
                     o best)
                 fn2-overlays)))
(defthm fn2-seal-pick-natp
 (implies (natp best) (natp (fn2-seal-pick k o best fn2-overlays))) :rule-classes :type-prescription)
; Work is pending in the seal row when it is in a non-idle active phase
; (:build, :filter, :install, :release), or when it is :idle and a published overlay is
; sealable.
(defun fn2-seal-pending-p (fn2-seals fn2-overlays)
 (declare (xargs :stobjs (fn2-seals fn2-overlays) :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays))))
 (and (< 0 (fn2-seals-rows fn2-seals))
      (let ((phase (fn2-seals-phase 0 fn2-seals)))
       (or (equal phase *fn2-seal-phase-build*)
           (equal phase *fn2-seal-phase-filter*)
           (equal phase *fn2-seal-phase-install*)
           (equal phase *fn2-seal-phase-release*)
           (and (equal phase *fn2-seal-phase-idle*)
                (< (fn2-seal-pick (fn2-overlays-rows fn2-overlays) 0 (fn2-overlays-rows fn2-overlays) fn2-overlays)
                   (fn2-overlays-rows fn2-overlays)))))))
(in-theory (disable fn2-seal-older-p fn2-seal-sealable-p fn2-seal-pick fn2-seal-pending-p))

; Retire overlay O (frozen -> free) and release its arena.
(defun fn2-seal-retire (o fn2-overlays fn2-pool)
 (declare (xargs :stobjs (fn2-overlays fn2-pool) :guard (and (fn2-overlays-wfp fn2-overlays) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-ov-retire fn2-ov-advance fn2-pool-release fn2-pool-release-countp)))))
 (b* (((unless (and (natp o) (< o (fn2-overlays-rows fn2-overlays)))) (mv :bounds fn2-overlays fn2-pool))
      (slot (fn2-overlays-slot o fn2-overlays)) (gen (fn2-overlays-gen o fn2-overlays))
      (okind (fn2-overlays-okind o fn2-overlays)) (oslot (fn2-overlays-oslot o fn2-overlays)) (ogen (fn2-overlays-ogen o fn2-overlays))
      ((unless (fn2-pool-release-countp slot fn2-pool)) (mv :bounds fn2-overlays fn2-pool))
      ((mv code fn2-overlays) (fn2-ov-advance o *fn2-overlay-phase-frozen* *fn2-overlay-phase-free* fn2-overlays))
      ((unless (eq code :ok)) (mv code fn2-overlays fn2-pool))
      ((mv code fn2-pool) (fn2-pool-release slot gen okind oslot ogen fn2-pool)))
  (mv code fn2-overlays fn2-pool)))
(fn2-seal-shape fn2-seal-retire (o fn2-overlays fn2-pool) (fn2-overlays fn2-pool) (fn2-overlays fn2-pool) t
 (fn2-ov-advance fn2-pool-release-countp fn2-overlays-slot fn2-overlays-gen fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))

; ---------------------------------------------------------------------------
; C5's merge, chosen when a seal starts (docs/c-ordered-runs.md §5). The
; frozen overlay O of schema SID is sealed together with SID's newest live
; runs (a suffix in run order, so the new run, whose identifier is greater
; than every run's, stands where they stood); its inputs retire when it
; installs and their pages are released unit by unit after it (:release).
; Size-tiered: a run joins while its entries are at most twice the entries
; gathered so far (O's, then each joined run's), so a schema holds about
; log2(entries) runs and an entry is rewritten about log2(n) times. Every
; run joins (FORCE) when the 64 KiB class or the installed view has at most
; one free row left (backpressure: the next seal needs a page and a row, and
; a merge frees its inputs'), or when the schema already holds
; *fn2-seal-run-budget* runs (a reader merges at most eight sources of a
; schema; stage keeps its overlays to the other four, machines-c.lisp). At
; most seven runs join, the overlay being the eighth source.
(defconst *fn2-seal-run-budget* *fn2-idc-run-budget*)
(defconst *fn2-seal-merge-runs* 7)
; Live runs of SID among rows R.. (K), and free rows.
(defun fn2-seal-live-runs (k r sid fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :measure (nfix k) :guard (and (fn2-run-installed-wfp fn2-run-installed) (natp r))))
 (if (not (and (posp k) (natp r) (< r (fn2-run-installed-rows fn2-run-installed)))) 0
  (+ (if (and (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)
              (equal (fn2-run-installed-schema r fn2-run-installed) sid)) 1 0)
     (fn2-seal-live-runs (- k 1) (+ 1 r) sid fn2-run-installed))))
(defun fn2-seal-free-rows (k r fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :measure (nfix k) :guard (and (fn2-run-installed-wfp fn2-run-installed) (natp r))))
 (if (not (and (posp k) (natp r) (< r (fn2-run-installed-rows fn2-run-installed)))) 0
  (+ (if (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*) 1 0)
     (fn2-seal-free-rows (- k 1) (+ 1 r) fn2-run-installed))))
(defthm fn2-seal-live-runs-natp (natp (fn2-seal-live-runs k r sid fn2-run-installed)) :rule-classes :type-prescription)
(defthm fn2-seal-free-rows-natp (natp (fn2-seal-free-rows k r fn2-run-installed)) :rule-classes :type-prescription)
; The runs that join, newest first from below BOUND (I more at most), ACC
; the entries gathered: (mv count least-run).
(defun fn2-seal-select (i acc bound force sid fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :measure (nfix i) :guard (fn2-run-installed-wfp fn2-run-installed)))
 (b* (((unless (posp i)) (mv 0 0))
      (rows (fn2-run-installed-rows fn2-run-installed))
      (r (fn2-succ-newest-run rows 0 sid bound rows fn2-run-installed))
      ((unless (and (natp r) (< r rows))) (mv 0 0))
      (e (nfix (fn2-run-installed-entries r fn2-run-installed)))
      (run (nfix (fn2-run-installed-run r fn2-run-installed)))
      ((unless (or force (<= e (* 2 (nfix acc))))) (mv 0 0))
      ((mv n least) (fn2-seal-select (- i 1) (+ (nfix acc) e) run force sid fn2-run-installed)))
  (mv (+ 1 (nfix n)) (if (equal (nfix n) 0) run (nfix least)))))
; Free rows of the page class (its free count; 0 when the pool has no such class).
(defun fn2-seal-free-pages (fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
 (let ((class (fn2-pool-class-for *fn2-run-page-size* fn2-pool)))
  (if (and (natp class) (< class (fn2-pool-nclasses fn2-pool))) (nfix (fn2-pool-free-count class fn2-pool)) 0)))
; Overlay O of SID with E entries: (mv count least-run) of the runs joining it.
(defun fn2-seal-plan (sid e fn2-run-installed fn2-pool)
 (declare (xargs :stobjs (fn2-run-installed fn2-pool) :guard (and (fn2-run-installed-wfp fn2-run-installed) (fn2-pool-wfp fn2-pool))))
 (let* ((rows (fn2-run-installed-rows fn2-run-installed))
        (force (or (<= (fn2-seal-free-pages fn2-pool) 1) (<= (fn2-seal-free-rows rows 0 fn2-run-installed) 1)
                   (<= *fn2-seal-run-budget* (fn2-seal-live-runs rows 0 sid fn2-run-installed)))))
  (mv-let (k rlo) (fn2-seal-select *fn2-seal-merge-runs* e *fn2-u60-max* force sid fn2-run-installed)
   (mv (min *fn2-seal-merge-runs* (nfix k)) (nfix rlo)))))
(defthm fn2-seal-plan-types
 (and (natp (mv-nth 0 (fn2-seal-plan sid e fn2-run-installed fn2-pool)))
      (<= (mv-nth 0 (fn2-seal-plan sid e fn2-run-installed fn2-pool)) *fn2-seal-merge-runs*)
      (natp (mv-nth 1 (fn2-seal-plan sid e fn2-run-installed fn2-pool))))
 :rule-classes ((:linear :corollary (<= (mv-nth 0 (fn2-seal-plan sid e fn2-run-installed fn2-pool)) *fn2-seal-merge-runs*))
                (:type-prescription :corollary (natp (mv-nth 0 (fn2-seal-plan sid e fn2-run-installed fn2-pool))))
                (:type-prescription :corollary (natp (mv-nth 1 (fn2-seal-plan sid e fn2-run-installed fn2-pool))))))
(in-theory (disable fn2-seal-live-runs fn2-seal-free-rows fn2-seal-select fn2-seal-free-pages fn2-seal-plan))

; Start: pick the next overlay. None: :idle. An empty one is retired at
; once (:retired). Otherwise the next run identifier is handed out, the hash
; workspace taken under the seal row's owner, and the build started.
(defun fn2-seal-start (fn2-seals fn2-overlays fn2-run-installed fn2-run-builds fn2-run-writers fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-overlays fn2-run-installed fn2-run-builds fn2-run-writers fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed)
              (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-seal-pick fn2-seal-retire fn2-pool-reserve fn2-pool-class-for fn2-run-build-start fn2-seal-plan
                                            fn2-overlays-rows fn2-seals-rows fn2-run-builds-rows fn2-run-writers-rows fn2-pool-rows
                                            fn2-seals-okind fn2-seals-oslot fn2-seals-ogen fn2-seals-crow fn2-seals-runs
                                            fn2-seals-wbase fn2-seals-fbase fn2-seals-fill fn2-overlays-count fn2-seals-units)))))
 (b* (((unless (< 0 (fn2-seals-rows fn2-seals))) (mv :bounds fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool))
      (rows (fn2-overlays-rows fn2-overlays))
      (o (fn2-seal-pick rows 0 rows fn2-overlays))
      ((unless (< o rows)) (mv :idle fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool))
      ((unless (posp (fn2-overlays-count o fn2-overlays)))
       (mv-let (code fn2-overlays fn2-pool) (fn2-seal-retire o fn2-overlays fn2-pool)
        (mv (if (eq code :ok) :retired code) fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool)))
      (okind (fn2-seals-okind 0 fn2-seals)) (oslot (fn2-seals-oslot 0 fn2-seals)) (ogen (fn2-seals-ogen 0 fn2-seals))
      (crow (fn2-seals-crow 0 fn2-seals))
      (run (+ 1 (nfix (fn2-seals-runs 0 fn2-seals))))
      (hbase (+ (* *fn2-digest-stride* (nfix crow)) *fn2-seal-hash-region*))
      (sid (fn2-overlays-schema o fn2-overlays))
      ((mv k rlo) (fn2-seal-plan sid (fn2-overlays-count o fn2-overlays) fn2-run-installed fn2-pool))
      (ufirst (+ 1 (nfix (fn2-seals-units 0 fn2-seals))))
      ((unless (and (unsigned-byte-p 60 run) (unsigned-byte-p 32 hbase) (unsigned-byte-p 32 o)
                    (unsigned-byte-p 60 sid) (unsigned-byte-p 8 k) (unsigned-byte-p 60 rlo) (unsigned-byte-p 60 ufirst)))
       (mv :bounds fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool))
      (class (fn2-pool-class-for *fn2-seal-hash-bytes* fn2-pool))
      ((unless (natp class)) (mv :capacity fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool))
      ((mv code hslot hgen fn2-pool) (fn2-pool-reserve class okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv (if (eq code :exhausted) :full code) fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool))
      ((unless (and (unsigned-byte-p 32 hslot) (unsigned-byte-p 60 hgen)))
       (mv :bounds fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool))
      ((mv code fn2-run-builds fn2-run-writers fn2-pool)
       (fn2-run-build-start 0 sid run (fn2-seals-wbase 0 fn2-seals) crow hbase hslot hgen (fn2-seals-fbase 0 fn2-seals)
                            (fn2-seals-fill 0 fn2-seals) 1 1 okind oslot ogen fn2-run-builds fn2-run-writers fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool))
      (fn2-seals (fn2-seals-put 0 (phase *fn2-seal-phase-build*) (sub *fn2-seal-sub-open*) (o o) (pos 0) (sid sid) (run run)
                                (runs run) (hslot hslot) (hgen hgen) (filter 0) (entries 0) (k k) (rlo rlo) (ufirst ufirst)
                                (held 0))))
  (mv :more fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool)))
(fn2-seal-shape fn2-seal-start (fn2-seals fn2-overlays fn2-run-installed fn2-run-builds fn2-run-writers fn2-pool)
 (fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool) (fn2-seals fn2-overlays fn2-run-installed fn2-run-builds fn2-run-writers fn2-pool) t
 (fn2-seal-pick fn2-seal-retire fn2-run-build-start fn2-seal-plan fn2-seals-okind fn2-seals-oslot fn2-seals-ogen fn2-seals-crow fn2-seals-runs
  fn2-seals-wbase fn2-seals-fbase fn2-seals-fill fn2-seals-units fn2-overlays-schema fn2-overlays-count))

; The next physical unit whose cache row holds no page (the engine half
; keeps every page resident, so a direct-mapped row held by a live page is
; passed over, never evicted: units are identities only, and a run's pages
; are the cached units of its interval, C5). At most K units are tried, one
; per cache row; every row held is :cache (backpressure).
(defun fn2-seal-unit-scan (k unit fn2-run-cache)
 (declare (xargs :stobjs fn2-run-cache :measure (nfix k) :guard (and (fn2-run-cache-wfp fn2-run-cache) (natp unit))))
 (b* (((unless (and (posp k) (natp unit) (unsigned-byte-p 60 unit) (< 0 (fn2-run-cache-rows fn2-run-cache)))) nil)
      (i (fn2-run-cache-row unit fn2-run-cache))
      ((when (and (natp i) (< i (fn2-run-cache-rows fn2-run-cache))
                  (not (equal (fn2-run-cache-state i fn2-run-cache) *fn2-run-cache-state-ready*))))
       unit))
  (fn2-seal-unit-scan (- k 1) (+ 1 unit) fn2-run-cache)))
(defthm fn2-seal-unit-scan-type
 (or (null (fn2-seal-unit-scan k unit fn2-run-cache)) (unsigned-byte-p 60 (fn2-seal-unit-scan k unit fn2-run-cache)))
 :rule-classes ((:type-prescription :corollary (or (null (fn2-seal-unit-scan k unit fn2-run-cache))
                                                   (natp (fn2-seal-unit-scan k unit fn2-run-cache))))
                (:rewrite :corollary (implies (fn2-seal-unit-scan k unit fn2-run-cache)
                                              (unsigned-byte-p 60 (fn2-seal-unit-scan k unit fn2-run-cache))))))
(in-theory (disable fn2-seal-unit-scan))
; (mv code unit seals)
(defun fn2-seal-unit (fn2-seals fn2-run-cache)
 (declare (xargs :stobjs (fn2-seals fn2-run-cache) :guard (and (fn2-seals-wfp fn2-seals) (fn2-run-cache-wfp fn2-run-cache))))
 (b* (((unless (and (< 0 (fn2-seals-rows fn2-seals)) (< 0 (fn2-run-cache-rows fn2-run-cache)))) (mv :bounds 0 fn2-seals))
      (unit (fn2-seal-unit-scan (fn2-run-cache-rows fn2-run-cache) (+ 1 (nfix (fn2-seals-units 0 fn2-seals))) fn2-run-cache))
      ((unless unit) (mv :cache 0 fn2-seals))
      (fn2-seals (fn2-seals-set-units 0 unit fn2-seals)))
  (mv :ok unit fn2-seals)))
(fn2-seal-shape fn2-seal-unit (fn2-seals fn2-run-cache) ((fn2-seals 2)) (fn2-seals fn2-run-cache) t
 (fn2-seals-units fn2-seal-unit-scan))
(defthm fn2-seal-unit-natp
 (natp (mv-nth 1 (fn2-seal-unit fn2-seals fn2-run-cache))) :hints (("Goal" :in-theory (enable fn2-seal-unit)))
 :rule-classes :type-prescription)

; A unit and a 64 KiB workspace under the seal row's owner. (mv code unit
; slot gen seals pool)
(defun fn2-seal-take-page (fn2-seals fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-run-cache fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-seal-unit fn2-pool-reserve fn2-pool-class-for fn2-seals-rows)))))
 (b* (((mv code unit fn2-seals) (fn2-seal-unit fn2-seals fn2-run-cache))
      ((unless (and (eq code :ok) (< 0 (fn2-seals-rows fn2-seals)))) (mv (if (eq code :ok) :bounds code) 0 0 0 fn2-seals fn2-pool))
      (class (fn2-pool-class-for *fn2-run-page-size* fn2-pool))
      ((unless (natp class)) (mv :capacity 0 0 0 fn2-seals fn2-pool))
      ((mv code slot gen fn2-pool) (fn2-pool-reserve class (fn2-seals-okind 0 fn2-seals) (fn2-seals-oslot 0 fn2-seals)
                                                     (fn2-seals-ogen 0 fn2-seals) fn2-pool))
      ((unless (eq code :ok)) (mv (if (eq code :exhausted) :full code) 0 0 0 fn2-seals fn2-pool))
      ((unless (and (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))) (mv :bounds 0 0 0 fn2-seals fn2-pool)))
  (mv :ok unit slot gen fn2-seals fn2-pool)))
(fn2-seal-shape fn2-seal-take-page (fn2-seals fn2-run-cache fn2-pool) ((fn2-seals 4) (fn2-pool 5)) (fn2-seals fn2-run-cache fn2-pool) t
 (fn2-seal-unit fn2-seals-okind fn2-seals-oslot fn2-seals-ogen))
(defthm fn2-seal-take-page-types
 (and (natp (mv-nth 1 (fn2-seal-take-page fn2-seals fn2-run-cache fn2-pool)))
      (natp (mv-nth 2 (fn2-seal-take-page fn2-seals fn2-run-cache fn2-pool)))
      (natp (mv-nth 3 (fn2-seal-take-page fn2-seals fn2-run-cache fn2-pool))))
 :hints (("Goal" :in-theory (enable fn2-seal-take-page))))

; A fresh page for level LEVEL of the build. (mv code seals builds writers pool)
(defun fn2-seal-page (level fn2-seals fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers)
              (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-seal-take-page fn2-run-build-page fn2-run-buildp)))))
 (b* (((unless (fn2-run-buildp 0 fn2-run-builds fn2-run-writers)) (mv :bounds fn2-seals fn2-run-builds fn2-run-writers fn2-pool))
      ((mv code unit slot gen fn2-seals fn2-pool) (fn2-seal-take-page fn2-seals fn2-run-cache fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-run-builds fn2-run-writers fn2-pool))
      ((mv code fn2-run-builds fn2-run-writers fn2-pool)
       (fn2-run-build-page 0 level slot gen unit 1 unit fn2-run-builds fn2-run-writers fn2-pool)))
  (mv code fn2-seals fn2-run-builds fn2-run-writers fn2-pool)))
(fn2-seal-shape fn2-seal-page (level fn2-seals fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)
 (fn2-seals fn2-run-builds fn2-run-writers fn2-pool) (fn2-seals fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool) t
 (fn2-seal-take-page fn2-run-build-page fn2-run-buildp))

; A page writer W just sealed: cache it, so readers find it resident; refuse
; :cache when its direct-mapped row already holds a ready page.
(defun fn2-seal-cache (w fn2-run-writers fn2-run-cache)
 (declare (xargs :stobjs (fn2-run-writers fn2-run-cache) :guard (and (fn2-run-writers-wfp fn2-run-writers) (fn2-run-cache-wfp fn2-run-cache))
  :guard-hints (("Goal" :in-theory (disable fn2-run-cache-install fn2-run-cache-row)))))
 (b* (((unless (and (natp w) (< w (fn2-run-writers-rows fn2-run-writers)) (< 0 (fn2-run-cache-rows fn2-run-cache))))
       (mv :bounds fn2-run-cache))
      (unit (fn2-run-writers-unit w fn2-run-writers))
      (i (fn2-run-cache-row unit fn2-run-cache))
      ((unless (and (natp i) (< i (fn2-run-cache-rows fn2-run-cache)))) (mv :bounds fn2-run-cache))
      ((when (equal (fn2-run-cache-state i fn2-run-cache) *fn2-run-cache-state-ready*))
       (mv :cache fn2-run-cache)))
  (fn2-run-cache-install unit (fn2-run-writers-counter w fn2-run-writers)
                         (fn2-run-writers-slot w fn2-run-writers) (fn2-run-writers-gen w fn2-run-writers) fn2-run-cache)))
(fn2-seal-shape fn2-seal-cache (w fn2-run-writers fn2-run-cache) (fn2-run-cache) (fn2-run-writers fn2-run-cache) t
 (fn2-run-cache-install fn2-run-cache-row fn2-run-cache-state fn2-run-writers-unit fn2-run-writers-counter
  fn2-run-writers-slot fn2-run-writers-gen))

; The column readers of the build's and filter's tables, folded in the
; callee shapes below (C-SHAPE-READS: their values only feed run-time checks
; and callee arguments).
(defconst *fn2-seal-readers*
 '(fn2-run-builds-phase fn2-run-builds-schema fn2-run-builds-run fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-entries fn2-run-builds-pages fn2-run-builds-crow fn2-run-builds-hbase fn2-run-builds-hslot fn2-run-builds-hgen fn2-run-builds-fields fn2-run-builds-limit fn2-run-builds-history fn2-run-builds-incarnation fn2-run-builds-okind fn2-run-builds-oslot fn2-run-builds-ogen fn2-run-writers-phase fn2-run-writers-schema fn2-run-writers-schema-version fn2-run-writers-level fn2-run-writers-run fn2-run-writers-ordinal fn2-run-writers-page-kind fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-cursor fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-pos fn2-run-writers-prev fn2-run-writers-fields fn2-run-writers-limit fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-ribbon-builds-phase fn2-ribbon-builds-schema fn2-ribbon-builds-run fn2-ribbon-builds-seed fn2-ribbon-builds-base fn2-ribbon-builds-slots fn2-ribbon-builds-keys fn2-ribbon-builds-added fn2-ribbon-builds-i fn2-ribbon-builds-w fn2-ribbon-builds-crow fn2-ribbon-builds-hrow fn2-ribbon-builds-pending fn2-ribbon-builds-ps fn2-ribbon-builds-plo fn2-ribbon-builds-phi))
(defmacro fn2-seal-callee-shape (fn args outs hyps reads)
 `(fn2-idc-op-shape ,fn ,args ,outs ,hyps :min ,(append reads *fn2-seal-readers*)))
; Shapes of the build and filter entry points the sealer drives (their own
; books verify their guards; these are their output shapes), each opened
; alone over its callees' shapes.
(fn2-seal-callee-shape fn2-run-build-work (b budget fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                      fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 ((fn2-run-builds 2) (fn2-run-writers 3) (fn2-run-restarts 4) (fn2-fields 5) (fn2-pool 6) (fn2-fc 7) (fn2-fc-context 8)
  (fn2-b3 9) (fn2-digests 10))
 ((fn2-run-buildsp fn2-run-builds) (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
  (fn2-run-restartsp fn2-run-restarts) (fn2-run-restarts-wfp fn2-run-restarts) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
  (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-fc-contextp fn2-fc-context)
  (fn2-fc-context-wfp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
  (fn2-run-buildp b fn2-run-builds fn2-run-writers) (natp b) (< b (fn2-run-builds-rows fn2-run-builds)) (natp budget))
 (fn2-run-scan fn2-run-close-step fn2-run-head fn2-run-seal-step fn2-run-seal-context fn2-run-close fn2-run-buildp
       fn2-run-writers-rows fn2-run-restarts-rows fn2-fc-rows fn2-fc-context-rows fn2-run-builds-rows fn2-digests-rows fn2-b3-rows))
(fn2-seal-callee-shape fn2-run-build-add (b ebase fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
 (fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
 ((fn2-run-buildsp fn2-run-builds) (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
  (fn2-run-restartsp fn2-run-restarts) (fn2-run-restarts-wfp fn2-run-restarts) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
  (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-run-buildp b fn2-run-builds fn2-run-writers) (natp b) (< b (fn2-run-builds-rows fn2-run-builds)))
 (fn2-run-add fn2-run-close fn2-run-writers-rows fn2-run-restarts-rows fn2-run-builds-rows))
(fn2-seal-callee-shape fn2-run-build-promote (b l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)
 (fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)
 ((fn2-run-buildsp fn2-run-builds) (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
  (fn2-run-restartsp fn2-run-restarts) (fn2-run-restarts-wfp fn2-run-restarts) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
  (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
  (fn2-run-buildp b fn2-run-builds fn2-run-writers) (natp b) (< b (fn2-run-builds-rows fn2-run-builds)) (natp l))
 (fn2-run-promote-check fn2-run-layout-decode fn2-run-child-ref fn2-run-add fn2-run-promote-commit fn2-run-buildp
       fn2-run-writers-rows fn2-run-restarts-rows fn2-run-builds-rows fn2-digests-rows))
(fn2-seal-callee-shape fn2-run-build-finish (b fn2-run-builds) (fn2-run-builds)
 ((fn2-run-buildsp fn2-run-builds) (fn2-run-builds-wfp fn2-run-builds) (natp b) (< b (fn2-run-builds-rows fn2-run-builds)))
 (fn2-run-builds-rows))
;; The Ribbon build's phase helpers (ribbon.lisp proves their guards and
;; leaves them disabled; fn2-ribbon-work's shape is opened over these).
(fn2-seal-callee-shape fn2-ribbon-continue (f budget fn2-ribbon-builds fn2-ribbon-band) (fn2-ribbon-builds fn2-ribbon-band)
 ((fn2-ribbon-buildsp fn2-ribbon-builds) (fn2-ribbon-builds-wfp fn2-ribbon-builds) (fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band))
 (fn2-ribbon-insert fn2-ribbon-builds-rows fn2-ribbon-band-rows))
(fn2-seal-callee-shape fn2-ribbon-clear-step (f budget fn2-ribbon-builds fn2-ribbon-band) (fn2-ribbon-builds fn2-ribbon-band)
 ((fn2-ribbon-buildsp fn2-ribbon-builds) (fn2-ribbon-builds-wfp fn2-ribbon-builds) (fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band))
 (fn2-ribbon-clear-rows fn2-ribbon-builds-rows fn2-ribbon-band-rows))
(fn2-seal-callee-shape fn2-ribbon-solve-step (f budget fn2-ribbon-builds fn2-ribbon-band) (fn2-ribbon-builds fn2-ribbon-band)
 ((fn2-ribbon-buildsp fn2-ribbon-builds) (fn2-ribbon-builds-wfp fn2-ribbon-builds) (fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band))
 (fn2-ribbon-solve-rows fn2-ribbon-builds-rows fn2-ribbon-band-rows))
(fn2-seal-callee-shape fn2-ribbon-emit-step (f budget fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool)
 (fn2-ribbon-builds fn2-run-writers fn2-pool)
 ((fn2-ribbon-buildsp fn2-ribbon-builds) (fn2-ribbon-builds-wfp fn2-ribbon-builds) (fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band)
  (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 (fn2-ribbon-emit-bytes fn2-run-close fn2-ribbon-builds-rows fn2-ribbon-band-rows fn2-run-writers-rows))
(fn2-seal-callee-shape fn2-ribbon-close-step (f budget fn2-ribbon-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
 (fn2-ribbon-builds fn2-run-writers fn2-fields fn2-pool)
 ((fn2-ribbon-buildsp fn2-ribbon-builds) (fn2-ribbon-builds-wfp fn2-ribbon-builds) (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
  (fn2-run-restartsp fn2-run-restarts) (fn2-run-restarts-wfp fn2-run-restarts) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
  (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 (fn2-run-writerp fn2-run-close-step fn2-ribbon-builds-rows fn2-run-writers-rows fn2-run-restarts-rows))
(fn2-seal-callee-shape fn2-ribbon-head (f fn2-ribbon-builds fn2-run-writers fn2-fields fn2-pool fn2-fc-context)
 (fn2-ribbon-builds fn2-run-writers fn2-fields fn2-pool fn2-fc-context)
 ((fn2-ribbon-buildsp fn2-ribbon-builds) (fn2-ribbon-builds-wfp fn2-ribbon-builds) (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
  (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
  (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context))
 (fn2-run-head-b fn2-ribbon-header-encode fn2-run-seal-context fn2-digest-slot fn2-ribbon-builds-rows fn2-run-writers-rows fn2-fc-context-rows))
(fn2-seal-callee-shape fn2-ribbon-seal (f budget fn2-ribbon-builds fn2-run-writers fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (fn2-ribbon-builds fn2-run-writers fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
 ((fn2-ribbon-buildsp fn2-ribbon-builds) (fn2-ribbon-builds-wfp fn2-ribbon-builds) (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
  (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
  (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
  (natp budget))
 (fn2-run-seal-step fn2-ribbon-builds-rows fn2-run-writers-rows fn2-fc-rows fn2-fc-context-rows fn2-digests-rows fn2-b3-rows))
(fn2-seal-callee-shape fn2-ribbon-work (f budget fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                   fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 ((fn2-ribbon-buildsp fn2-ribbon-builds) (fn2-ribbon-builds-wfp fn2-ribbon-builds) (fn2-ribbon-bandp fn2-ribbon-band)
  (fn2-ribbon-band-wfp fn2-ribbon-band) (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
  (fn2-run-restartsp fn2-run-restarts) (fn2-run-restarts-wfp fn2-run-restarts) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
  (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-fc-contextp fn2-fc-context)
  (fn2-fc-context-wfp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
  (natp budget))
 (fn2-ribbon-continue fn2-ribbon-clear-step fn2-ribbon-solve-step fn2-ribbon-emit-step
       fn2-ribbon-close-step fn2-ribbon-head fn2-ribbon-seal fn2-ribbon-builds-rows fn2-ribbon-band-rows fn2-run-writers-rows fn2-run-restarts-rows fn2-fc-rows fn2-fc-context-rows
       fn2-digests-rows fn2-b3-rows))
(in-theory (disable fn2-run-build-work fn2-run-build-add fn2-run-build-promote fn2-run-build-finish fn2-ribbon-work))

;; The build's root is sealed at level L (writer W): the row names the root
;; page and moves on (the filter for identity, else install). (mv code seals)
(defun fn2-seal-root (l w fn2-seals fn2-run-builds fn2-run-writers)
 (declare (xargs :stobjs (fn2-seals fn2-run-builds fn2-run-writers)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers))))
 (b* (((unless (and (< 0 (fn2-seals-rows fn2-seals)) (< 0 (fn2-run-builds-rows fn2-run-builds))
                    (natp w) (< w (fn2-run-writers-rows fn2-run-writers)) (natp l) (< l *fn2-run-max-levels*)))
       (mv :bounds fn2-seals))
      (rslot (fn2-run-writers-slot w fn2-run-writers)) (rgen (fn2-run-writers-gen w fn2-run-writers))
      (runit (fn2-run-writers-unit w fn2-run-writers)) (rcounter (fn2-run-writers-counter w fn2-run-writers))
      (entries (fn2-run-builds-entries 0 fn2-run-builds))
      ((unless (and (unsigned-byte-p 32 rslot) (unsigned-byte-p 60 rgen) (unsigned-byte-p 60 runit)
                    (unsigned-byte-p 60 rcounter) (unsigned-byte-p 60 entries)))
       (mv :bounds fn2-seals))
      ;; A merged run carries no filter (C5: the band holds one overlay's
      ;; keys; a run's filter beyond it is C5's partitioned filter, owed).
      (fn2-seals (fn2-seals-put 0 (phase (if (and (equal (fn2-seals-sid 0 fn2-seals) *fn2-seal-identity*)
                                                  (equal (nfix (fn2-seals-k 0 fn2-seals)) 0))
                                             *fn2-seal-phase-filter* *fn2-seal-phase-install*))
                                (sub *fn2-seal-sub-open*) (pos 0) (top l) (rslot rslot) (rgen rgen) (runit runit)
                                (rcounter rcounter) (entries entries))))
  (mv :more fn2-seals)))
(fn2-seal-shape fn2-seal-root (l w fn2-seals fn2-run-builds fn2-run-writers) (fn2-seals) (fn2-seals fn2-run-builds fn2-run-writers) t
 (fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-unit fn2-run-writers-counter fn2-run-builds-entries fn2-seals-sid fn2-seals-k))

;; The build is idle: add the overlay's next entry (POS), or finish when
;; every entry is in. (mv code seals builds writers restarts fields pool)
(defun fn2-seal-next (fn2-seals fn2-overlays fn2-overlay-index fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                      fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-overlays fn2-overlay-index fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                          fn2-fields fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
              (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers) (fn2-run-restarts-wfp fn2-run-restarts)
              (fn2-run-cache-wfp fn2-run-cache) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-run-build-add fn2-run-build-finish fn2-seal-page fn2-ov-entry fn2-run-buildp
                                            fn2-seals-rows fn2-fields-rows fn2-run-writers-rows fn2-overlays-rows
                                            fn2-run-builds-rows fn2-run-restarts-rows fn2-run-cache-rows fn2-pool-rows
                                            fn2-seals-o fn2-seals-pos fn2-seals-fbase fn2-overlays-count)))))
 (b* (((unless (and (< 0 (fn2-seals-rows fn2-seals)) (< 0 (fn2-run-builds-rows fn2-run-builds))
                    (fn2-run-buildp 0 fn2-run-builds fn2-run-writers)))
       (mv :bounds fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      (o (fn2-seals-o 0 fn2-seals)) (pos (nfix (fn2-seals-pos 0 fn2-seals)))
      (eb (+ (nfix (fn2-seals-fbase 0 fn2-seals)) *fn2-seal-eb*))
      ((unless (and (natp o) (< o (fn2-overlays-rows fn2-overlays))))
       (mv :bounds fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((when (<= (nfix (fn2-overlays-count o fn2-overlays)) pos))
       (mv-let (c fn2-run-builds) (fn2-run-build-finish 0 fn2-run-builds)
        (mv (if (eq c :ok) :more c) fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
      ((mv c & fn2-fields) (fn2-ov-entry o pos eb fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq c :ok)) (mv c fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((mv c fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
       (fn2-run-build-add 0 eb fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((when (eq c :ok))
       (b* ((next (+ 1 pos))
            ((unless (unsigned-byte-p 32 next)) (mv :bounds fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
            (fn2-seals (fn2-seals-set-pos 0 next fn2-seals)))
        (mv :more fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
      ((unless (eq c :need-page)) (mv c fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((unless (and (< 0 (fn2-run-builds-rows fn2-run-builds)) (fn2-run-buildp 0 fn2-run-builds fn2-run-writers)))
       (mv :bounds fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((mv c fn2-seals fn2-run-builds fn2-run-writers fn2-pool)
       (fn2-seal-page 0 fn2-seals fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)))
  (mv (if (eq c :ok) :more c) fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
(fn2-seal-shape fn2-seal-next (fn2-seals fn2-overlays fn2-overlay-index fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                                 fn2-fields fn2-pool)
 (fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
 (fn2-seals fn2-overlays fn2-overlay-index fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-fields fn2-pool) t
 (fn2-run-build-add fn2-run-build-finish fn2-seal-page fn2-ov-entry fn2-run-buildp fn2-seals-o fn2-seals-pos fn2-seals-fbase
  fn2-overlays-count))

;; C5's merge source: range row RG over the overlay and the runs joining it
;; (source 0 the overlay, then SID's live runs from RLO on), every source
;; seeking SID's least key (octet fields empty references into the hash
;; workspace, read under the seal row's owner). Only the sealer moves SID's
;; runs and the overlay is frozen, so the sources are never found again
;; while it merges (the merge's step refuses a move as an invariant).
;; (mv code seals ranges sources fields)
(defun fn2-seal-merge-open (fn2-seals fn2-overlays fn2-ranges fn2-range-sources fn2-run-installed fn2-fields)
 (declare (xargs :stobjs (fn2-seals fn2-overlays fn2-ranges fn2-range-sources fn2-run-installed fn2-fields)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays) (fn2-ranges-wfp fn2-ranges)
              (fn2-range-sources-wfp fn2-range-sources) (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields))
  :guard-hints (("Goal" :in-theory (disable fn2-range-add-source fn2-range-add-runs fn2-range-key-least fn2-run-version
                                            fn2-seals-rows fn2-ranges-rows fn2-overlays-rows fn2-run-installed-rows
                                            fn2-seals-rg fn2-seals-o fn2-seals-sid fn2-seals-qbase fn2-seals-sbase fn2-seals-cbase
                                            fn2-seals-rbase fn2-seals-okind fn2-seals-oslot fn2-seals-ogen fn2-seals-rlo
                                            fn2-seals-k fn2-seals-hslot fn2-seals-hgen fn2-overlays-seq fn2-overlays-okind
                                            fn2-overlays-oslot fn2-overlays-ogen fn2-fields-rows fn2-range-sources-rows)))))
 (b* (((unless (< 0 (fn2-seals-rows fn2-seals))) (mv :bounds fn2-seals fn2-ranges fn2-range-sources fn2-fields))
      (g (fn2-seals-rg 0 fn2-seals)) (o (fn2-seals-o 0 fn2-seals)) (sid (fn2-seals-sid 0 fn2-seals))
      (qbase (fn2-seals-qbase 0 fn2-seals)) (sbase (fn2-seals-sbase 0 fn2-seals)) (cbase (fn2-seals-cbase 0 fn2-seals))
      (rbase (fn2-seals-rbase 0 fn2-seals))
      (okind (fn2-seals-okind 0 fn2-seals)) (oslot (fn2-seals-oslot 0 fn2-seals)) (ogen (fn2-seals-ogen 0 fn2-seals))
      ((unless (and (natp g) (< g (fn2-ranges-rows fn2-ranges)) (natp o) (< o (fn2-overlays-rows fn2-overlays))
                    (unsigned-byte-p 60 sid) (unsigned-byte-p 32 qbase) (unsigned-byte-p 32 sbase) (unsigned-byte-p 32 cbase)
                    (unsigned-byte-p 32 rbase) (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds fn2-seals fn2-ranges fn2-range-sources fn2-fields))
      (fn2-ranges (fn2-ranges-put g (phase *fn2-range-phase-seek*) (schema sid) (qbase qbase) (hbase qbase)
                                  (sbase sbase) (smax *fn2-idc-seal-cursors*) (scount 0)
                                  (cbase cbase) (rbase rbase) (vrun 0)
                                  (pfield *fn2-range-no-position*) (plimit 0) (out 0) (ok 0) (os 0) (og 0) (delivered 0)
                                  (qk okind) (qs oslot) (qg ogen)))
      ((mv code fn2-range-sources)
       (fn2-range-add-source g 0 *fn2-range-kind-overlay* o (fn2-overlays-seq o fn2-overlays) (fn2-overlays-okind o fn2-overlays)
                             (fn2-overlays-oslot o fn2-overlays) (fn2-overlays-ogen o fn2-overlays) fn2-ranges fn2-range-sources))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-ranges fn2-range-sources fn2-fields))
      ((mv code n fn2-range-sources)
       (fn2-range-add-runs (fn2-run-installed-rows fn2-run-installed) 1 g sid (fn2-seals-rlo 0 fn2-seals)
                           fn2-ranges fn2-range-sources fn2-run-installed))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-ranges fn2-range-sources fn2-fields))
      ;; the overlay and every run of the plan (K) are the sources
      ((unless (equal n (+ 1 (nfix (fn2-seals-k 0 fn2-seals))))) (mv :invariant fn2-seals fn2-ranges fn2-range-sources fn2-fields))
      (vrun (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed))
      ((unless (and (unsigned-byte-p 32 n) (unsigned-byte-p 60 vrun) (< g (fn2-ranges-rows fn2-ranges))))
       (mv :bounds fn2-seals fn2-ranges fn2-range-sources fn2-fields))
      (fn2-ranges (fn2-ranges-put g (scount n) (vrun vrun)))
      ((mv code fn2-fields) (fn2-range-key-least 0 (fn2-run-layout-keys sid) sid qbase (fn2-seals-hslot 0 fn2-seals)
                                                 (fn2-seals-hgen 0 fn2-seals) fn2-fields))
      ((unless (and (eq code :ok) (< 0 (fn2-seals-rows fn2-seals))))
       (mv (if (eq code :ok) :bounds code) fn2-seals fn2-ranges fn2-range-sources fn2-fields))
      (fn2-seals (fn2-seals-put 0 (sub *fn2-seal-sub-add*) (held 0))))
  (mv :more fn2-seals fn2-ranges fn2-range-sources fn2-fields)))
(fn2-seal-shape fn2-seal-merge-open (fn2-seals fn2-overlays fn2-ranges fn2-range-sources fn2-run-installed fn2-fields)
 (fn2-seals fn2-ranges fn2-range-sources fn2-fields) (fn2-seals fn2-overlays fn2-ranges fn2-range-sources fn2-run-installed fn2-fields) t
 (fn2-range-add-source fn2-range-add-runs fn2-range-key-least fn2-run-version fn2-seals-rg fn2-seals-o fn2-seals-sid fn2-seals-qbase
  fn2-seals-okind fn2-seals-oslot fn2-seals-ogen fn2-seals-sbase fn2-seals-cbase fn2-seals-rbase fn2-seals-rlo fn2-seals-k
  fn2-seals-hslot fn2-seals-hgen fn2-overlays-seq fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))

;; The build is idle in a merge: the held entry (decoded at the entry rows,
;; waiting for a page) goes in; else every source is advanced to its head
;; (one bounded step each), the least key is taken, the newest source
;; winning on equal keys and every source at that key moving on (the
;; schema's merge rule as every reader applies it), copied to the entry
;; rows and added; with every source at its end the build finishes.
;; (mv code seals ranges sources builds writers restarts cursors paths fields pool)
(defmacro fn2-seal-merge-mv (code)
 `(mv ,code fn2-seals fn2-ranges fn2-range-sources fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors
      fn2-run-paths fn2-fields fn2-pool))
(defun fn2-seal-merge-add (fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-fields fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers)
              (fn2-run-restarts-wfp fn2-run-restarts) (fn2-run-cache-wfp fn2-run-cache) (fn2-fields-wfp fn2-fields)
              (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-run-build-add fn2-seal-page fn2-run-buildp fn2-seals-rows fn2-fields-rows
                                            fn2-run-writers-rows fn2-run-builds-rows fn2-run-restarts-rows fn2-run-cache-rows
                                            fn2-pool-rows fn2-seals-fbase)))))
 (b* (((unless (and (< 0 (fn2-seals-rows fn2-seals)) (< 0 (fn2-run-builds-rows fn2-run-builds))
                    (fn2-run-buildp 0 fn2-run-builds fn2-run-writers)))
       (mv :bounds fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      (eb (+ (nfix (fn2-seals-fbase 0 fn2-seals)) *fn2-seal-eb*))
      ((mv c fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
       (fn2-run-build-add 0 eb fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((when (eq c :ok))
       (let ((fn2-seals (fn2-seals-set-held 0 0 fn2-seals)))
        (mv :more fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
      ((unless (eq c :need-page)) (mv c fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((unless (and (< 0 (fn2-run-builds-rows fn2-run-builds)) (fn2-run-buildp 0 fn2-run-builds fn2-run-writers)))
       (mv :bounds fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((mv c fn2-seals fn2-run-builds fn2-run-writers fn2-pool)
       (fn2-seal-page 0 fn2-seals fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)))
  (mv (if (eq c :ok) :more c) fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
(fn2-seal-shape fn2-seal-merge-add (fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-fields fn2-pool)
 (fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
 (fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-fields fn2-pool) t
 (fn2-run-build-add fn2-seal-page fn2-run-buildp fn2-seals-fbase))
(defun fn2-seal-merge-next (budget fn2-seals fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                            fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-run-cursors fn2-run-paths
                            fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-run-cursors fn2-run-paths
                          fn2-fields fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources)
              (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-run-installed-wfp fn2-run-installed)
              (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers) (fn2-run-restarts-wfp fn2-run-restarts)
              (fn2-run-cache-wfp fn2-run-cache) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp budget))
  :guard-hints (("Goal" :in-theory (disable fn2-seal-merge-open fn2-seal-merge-add fn2-range-advance-all fn2-range-pick
                                            fn2-range-consume fn2-range-copy-rows fn2-run-build-finish fn2-seals-rows
                                            fn2-ranges-rows fn2-range-sources-rows fn2-fields-rows fn2-run-builds-rows
                                            fn2-seals-sub fn2-seals-held fn2-seals-rg fn2-seals-fbase fn2-seals-sid
                                            fn2-ranges-scount fn2-ranges-sbase fn2-range-sources-rb)))))
 (b* (((unless (and (< 0 (fn2-seals-rows fn2-seals)) (< 0 (fn2-run-builds-rows fn2-run-builds)))) (fn2-seal-merge-mv :bounds))
      ((when (equal (fn2-seals-sub 0 fn2-seals) *fn2-seal-sub-open*))
       (mv-let (code fn2-seals fn2-ranges fn2-range-sources fn2-fields)
         (fn2-seal-merge-open fn2-seals fn2-overlays fn2-ranges fn2-range-sources fn2-run-installed fn2-fields)
        (fn2-seal-merge-mv code)))
      ((when (equal (fn2-seals-held 0 fn2-seals) 1))
       (mv-let (code fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
         (fn2-seal-merge-add fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-fields fn2-pool)
        (fn2-seal-merge-mv code)))
      (g (fn2-seals-rg 0 fn2-seals)) (sid (fn2-seals-sid 0 fn2-seals))
      ((unless (and (natp g) (< g (fn2-ranges-rows fn2-ranges)) (natp budget))) (fn2-seal-merge-mv :bounds))
      (n (fn2-ranges-scount g fn2-ranges)) (sbase (fn2-ranges-sbase g fn2-ranges))
      ((unless (and (natp n) (natp sbase))) (fn2-seal-merge-mv :bounds))
      ((mv code fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-range-advance-all n g budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                              fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
      ((unless (eq code :ok)) (fn2-seal-merge-mv code))
      ((mv code best) (fn2-range-pick n sbase sid nil fn2-range-sources fn2-fields fn2-pool))
      ((unless (eq code :ok)) (fn2-seal-merge-mv code))
      ((unless (and (natp best) (< best (fn2-range-sources-rows fn2-range-sources))))
       (mv-let (c fn2-run-builds) (fn2-run-build-finish 0 fn2-run-builds)
        (fn2-seal-merge-mv (if (eq c :ok) :more c))))
      (from (+ (nfix (fn2-range-sources-rb best fn2-range-sources)) *fn2-run-reader-entry*))
      (eb (+ (nfix (fn2-seals-fbase 0 fn2-seals)) *fn2-seal-eb*))
      ((mv code fn2-fields) (fn2-range-copy-rows *fn2-run-entry-rows* from eb fn2-fields))
      ((unless (eq code :ok)) (fn2-seal-merge-mv code))
      ((mv code fn2-range-sources) (fn2-range-consume n sbase sid best fn2-range-sources fn2-fields fn2-pool))
      ((unless (and (eq code :ok) (< 0 (fn2-seals-rows fn2-seals)))) (fn2-seal-merge-mv (if (eq code :ok) :bounds code)))
      (fn2-seals (fn2-seals-set-held 0 1 fn2-seals))
      ((mv code fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
       (fn2-seal-merge-add fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-fields fn2-pool)))
  (fn2-seal-merge-mv code)))
(fn2-seal-shape fn2-seal-merge-next (budget fn2-seals fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                                     fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-run-cursors fn2-run-paths
                                     fn2-fields fn2-pool)
 (fn2-seals fn2-ranges fn2-range-sources fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths fn2-fields fn2-pool)
 (fn2-seals fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
  fn2-run-restarts fn2-run-cache fn2-run-cursors fn2-run-paths fn2-fields fn2-pool) t
 (fn2-seal-merge-open fn2-seal-merge-add fn2-range-advance-all fn2-range-pick fn2-range-consume fn2-range-copy-rows
  fn2-run-build-finish fn2-seals-sub fn2-seals-held fn2-seals-rg fn2-seals-fbase fn2-seals-sid fn2-ranges-scount
  fn2-ranges-sbase fn2-range-sources-rb))

; One unit of the build: drive the build's work and act on what it answers
; (C1b'): cache a sealed page, promote, give a level a page, the root, or
; the next entry. (mv code seals builds writers restarts cache fields pool
; fc fc-context b3 digests): :more, or a refusal.
(defmacro fn2-seal-build-mv (code)
 `(mv ,code fn2-seals fn2-ranges fn2-range-sources fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths
      fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
(defun fn2-seal-build (budget fn2-seals fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                       fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-run-cursors fn2-run-paths
                       fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (declare (xargs :stobjs (fn2-seals fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-run-cursors fn2-run-paths
                          fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
              (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-run-installed-wfp fn2-run-installed)
              (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths)
              (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers) (fn2-run-restarts-wfp fn2-run-restarts)
              (fn2-run-cache-wfp fn2-run-cache) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-fc-wfp fn2-fc)
              (fn2-fc-context-wfp fn2-fc-context) (fn2-b3-wfp fn2-b3) (fn2-digests-wfp fn2-digests) (natp budget))
  :guard-hints (("Goal" :in-theory (disable fn2-run-build-work fn2-run-build-promote fn2-seal-next fn2-seal-merge-next fn2-seal-root fn2-seals-k
                                            fn2-seal-page fn2-seal-cache fn2-run-buildp fn2-run-builds-wbase
                                            fn2-seals-rows fn2-fields-rows fn2-run-writers-rows fn2-overlays-rows
                                            fn2-run-builds-rows fn2-run-restarts-rows fn2-run-cache-rows fn2-pool-rows
                                            fn2-fc-rows fn2-fc-context-rows fn2-b3-rows fn2-digests-rows)))))
 (b* (((unless (and (natp budget) (< 0 (fn2-seals-rows fn2-seals)) (< 0 (fn2-run-builds-rows fn2-run-builds))
                    (fn2-run-buildp 0 fn2-run-builds fn2-run-writers)))
       (fn2-seal-build-mv :bounds))
      ((mv code l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-run-build-work 0 budget fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((unless (and (< 0 (fn2-run-builds-rows fn2-run-builds)) (fn2-run-buildp 0 fn2-run-builds fn2-run-writers) (natp l)))
       (fn2-seal-build-mv :bounds))
      (w (+ (nfix (fn2-run-builds-wbase 0 fn2-run-builds)) l)))
  (case code
   (:more (fn2-seal-build-mv :more))
   (:sealed
    (mv-let (c fn2-run-cache) (fn2-seal-cache w fn2-run-writers fn2-run-cache)
     (fn2-seal-build-mv (if (eq c :ok) :more c))))
   (:promote
    (mv-let (c fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)
      (fn2-run-build-promote 0 l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)
     (fn2-seal-build-mv (if (member-eq c '(:ok :more :need-page)) :more c))))
   (:need-page
    (mv-let (c fn2-seals fn2-run-builds fn2-run-writers fn2-pool)
      (fn2-seal-page l fn2-seals fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)
     (fn2-seal-build-mv (if (eq c :ok) :more c))))
   (:root
    (mv-let (c fn2-seals) (fn2-seal-root l w fn2-seals fn2-run-builds fn2-run-writers)
     (fn2-seal-build-mv c)))
   (:idle
    (if (equal (nfix (fn2-seals-k 0 fn2-seals)) 0)
        (mv-let (c fn2-seals fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
          (fn2-seal-next fn2-seals fn2-overlays fn2-overlay-index fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                         fn2-fields fn2-pool)
         (fn2-seal-build-mv c))
      (mv-let (c fn2-seals fn2-ranges fn2-range-sources fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors
                 fn2-run-paths fn2-fields fn2-pool)
        (fn2-seal-merge-next budget fn2-seals fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                             fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-run-cursors fn2-run-paths
                             fn2-fields fn2-pool)
       (fn2-seal-build-mv c))))
   (otherwise (fn2-seal-build-mv code)))))
(fn2-seal-shape fn2-seal-build (budget fn2-seals fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                                  fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-run-cursors fn2-run-paths
                                  fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (fn2-seals fn2-ranges fn2-range-sources fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths fn2-run-cache
  fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (fn2-seals fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
  fn2-run-restarts fn2-run-cache fn2-run-cursors fn2-run-paths fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests) t
 (fn2-run-build-work fn2-run-build-promote fn2-seal-next fn2-seal-merge-next fn2-seal-root fn2-seal-page fn2-seal-cache
  fn2-run-buildp fn2-run-builds-wbase fn2-seals-k))

; ---------------------------------------------------------------------------
; The filter (identity summary runs): open the filter page on writer WBASE+6,
; clear the band, add each overlay entry's name, finish, solve and seal.
; Open writer W on the filter page (unit, SLOT/GEN) and start the Ribbon
; build over the overlay's N keys. (mv code ribbon-builds writers pool)
(defun fn2-seal-filter-begin (w unit slot gen n fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-ribbon-builds-wfp fn2-ribbon-builds) (fn2-ribbon-band-wfp fn2-ribbon-band)
              (fn2-run-writers-wfp fn2-run-writers) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-run-open fn2-run-reset-writers fn2-ribbon-start fn2-seals-rows fn2-run-writers-rows
                                            fn2-seals-crow fn2-seals-sid fn2-seals-run fn2-seals-fbase fn2-seals-okind
                                            fn2-seals-oslot fn2-seals-ogen)))))
 (b* (((unless (and (< 0 (fn2-seals-rows fn2-seals)) (natp w) (< w (fn2-run-writers-rows fn2-run-writers)) (natp n)))
       (mv :bounds fn2-ribbon-builds fn2-run-writers fn2-pool))
      ((mv code fn2-run-writers) (fn2-run-reset-writers 1 w fn2-run-writers))
      ((unless (and (eq code :ok) (< w (fn2-run-writers-rows fn2-run-writers))))
       (mv (if (eq code :ok) :bounds code) fn2-ribbon-builds fn2-run-writers fn2-pool))
      (crow (fn2-seals-crow 0 fn2-seals))
      ((mv code fn2-run-writers fn2-pool)
       (fn2-run-open w slot gen (fn2-seals-sid 0 fn2-seals) 1 0 (fn2-seals-run 0 fn2-seals) 0 *page-kind-partitioned-filter*
                     unit 1 unit 1 1 (fn2-seals-okind 0 fn2-seals) (fn2-seals-oslot 0 fn2-seals) (fn2-seals-ogen 0 fn2-seals)
                     (+ (nfix (fn2-seals-fbase 0 fn2-seals)) *fn2-seal-fw*) *fn2-run-page-size* fn2-run-writers fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-ribbon-builds fn2-run-writers fn2-pool))
      ((mv code fn2-ribbon-builds)
       (fn2-ribbon-start 0 w crow (+ (* *fn2-digest-stride* (nfix crow)) *fn2-seal-filter-region*) 0 n
                         fn2-ribbon-builds fn2-ribbon-band fn2-run-writers)))
  (mv code fn2-ribbon-builds fn2-run-writers fn2-pool)))
(fn2-seal-shape fn2-seal-filter-begin (w unit slot gen n fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool)
 (fn2-ribbon-builds fn2-run-writers fn2-pool) (fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool) t
 (fn2-run-open fn2-run-reset-writers fn2-ribbon-start fn2-seals-crow fn2-seals-sid fn2-seals-run fn2-seals-fbase
  fn2-seals-okind fn2-seals-oslot fn2-seals-ogen))
(defun fn2-seal-filter-open (fn2-seals fn2-overlays fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-overlays fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays) (fn2-ribbon-builds-wfp fn2-ribbon-builds)
              (fn2-ribbon-band-wfp fn2-ribbon-band) (fn2-run-writers-wfp fn2-run-writers) (fn2-run-cache-wfp fn2-run-cache)
              (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-seal-take-page fn2-seal-filter-begin fn2-seals-rows fn2-overlays-rows)))))
 (b* (((unless (< 0 (fn2-seals-rows fn2-seals))) (mv :bounds fn2-seals fn2-ribbon-builds fn2-run-writers fn2-pool))
      (w (+ (nfix (fn2-seals-wbase 0 fn2-seals)) *fn2-run-max-levels*))
      (o (fn2-seals-o 0 fn2-seals))
      ((unless (and (natp o) (< o (fn2-overlays-rows fn2-overlays)))) (mv :bounds fn2-seals fn2-ribbon-builds fn2-run-writers fn2-pool))
      (n (fn2-overlays-count o fn2-overlays))
      ((mv code unit slot gen fn2-seals fn2-pool) (fn2-seal-take-page fn2-seals fn2-run-cache fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-ribbon-builds fn2-run-writers fn2-pool))
      ((mv code fn2-ribbon-builds fn2-run-writers fn2-pool)
       (fn2-seal-filter-begin w unit slot gen n fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool))
      ((unless (and (eq code :ok) (< 0 (fn2-seals-rows fn2-seals))))
       (mv (if (eq code :ok) :bounds code) fn2-seals fn2-ribbon-builds fn2-run-writers fn2-pool))
      (fn2-seals (fn2-seals-put 0 (sub *fn2-seal-sub-clear*) (pos 0))))
  (mv :more fn2-seals fn2-ribbon-builds fn2-run-writers fn2-pool)))
(fn2-seal-shape fn2-seal-filter-open (fn2-seals fn2-overlays fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-pool)
 (fn2-seals fn2-ribbon-builds fn2-run-writers fn2-pool)
 (fn2-seals fn2-overlays fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-pool) t
 (fn2-seal-take-page fn2-seal-filter-begin fn2-seals-wbase fn2-seals-o fn2-overlays-count))

; One unit of the filter's work after the open. (mv code seals ribbon-builds
; ribbon-band writers cache fields pool fc fc-context b3 digests)
(defun fn2-seal-filter (budget fn2-seals fn2-overlays fn2-overlay-index fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts
                        fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (declare (xargs :stobjs (fn2-seals fn2-overlays fn2-overlay-index fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts
                          fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
              (fn2-ribbon-builds-wfp fn2-ribbon-builds) (fn2-ribbon-band-wfp fn2-ribbon-band) (fn2-run-writers-wfp fn2-run-writers)
              (fn2-run-restarts-wfp fn2-run-restarts) (fn2-run-cache-wfp fn2-run-cache) (fn2-fields-wfp fn2-fields)
              (fn2-pool-wfp fn2-pool) (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context) (fn2-b3-wfp fn2-b3) (fn2-digests-wfp fn2-digests)
              (natp budget))
  :guard-hints (("Goal" :in-theory (disable fn2-ribbon-work fn2-ribbon-add fn2-ribbon-finish fn2-ov-entry fn2-seal-cache
                                            fn2-seals-rows fn2-fields-rows fn2-run-writers-rows fn2-overlays-rows)))))
 (b* (((unless (and (natp budget) (< 0 (fn2-seals-rows fn2-seals))))
       (mv :bounds fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      (sub (fn2-seals-sub 0 fn2-seals)) (o (fn2-seals-o 0 fn2-seals)) (pos (nfix (fn2-seals-pos 0 fn2-seals)))
      (eb (+ (nfix (fn2-seals-fbase 0 fn2-seals)) *fn2-seal-eb*))
      ((unless (and (natp o) (< o (fn2-overlays-rows fn2-overlays))))
       (mv :bounds fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
  (cond
   ((equal sub *fn2-seal-sub-add*)
    (if (<= (nfix (fn2-overlays-count o fn2-overlays)) pos)
        (b* (((mv c fn2-ribbon-builds) (fn2-ribbon-finish 0 fn2-ribbon-builds))
             ((unless (eq c :ok))
              (mv c fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
             (fn2-seals (fn2-seals-set-sub 0 *fn2-seal-sub-solve* fn2-seals)))
         (mv :more fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
     (b* (((mv c & fn2-fields) (fn2-ov-entry o pos eb fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
          ((unless (eq c :ok))
           (mv c fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
          ((mv c fn2-ribbon-builds fn2-ribbon-band)
           (fn2-ribbon-add 0 (+ eb *fn2-seal-filter-field*) (fn2-overlays-okind o fn2-overlays) (fn2-overlays-oslot o fn2-overlays)
                           (fn2-overlays-ogen o fn2-overlays) fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool))
          ((unless (member-eq c '(:ok :more)))
           (mv c fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
          (next (+ 1 pos))
          ((unless (unsigned-byte-p 32 next))
           (mv :bounds fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
          (fn2-seals (fn2-seals-put 0 (pos next) (sub (if (eq c :more) *fn2-seal-sub-drive* *fn2-seal-sub-add*)))))
      (mv :more fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))))
   (t
    ; :clear (until :ready), :drive (until :idle), :solve (until :sealed)
    (b* (((mv c fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
          (fn2-ribbon-work 0 budget fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                           fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         ((when (eq c :more))
          (mv :more fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         ((when (or (and (equal sub *fn2-seal-sub-clear*) (eq c :ready)) (and (equal sub *fn2-seal-sub-drive*) (eq c :idle))))
          (let ((fn2-seals (fn2-seals-set-sub 0 *fn2-seal-sub-add* fn2-seals)))
           (mv :more fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
         ((unless (and (equal sub *fn2-seal-sub-solve*) (eq c :sealed)))
          (mv c fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         (w (+ (nfix (fn2-seals-wbase 0 fn2-seals)) *fn2-run-max-levels*))
         ((unless (< w (fn2-run-writers-rows fn2-run-writers)))
          (mv :bounds fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         ((mv c fn2-run-cache) (fn2-seal-cache w fn2-run-writers fn2-run-cache))
         ((unless (eq c :ok))
          (mv c fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         (funit (fn2-run-writers-unit w fn2-run-writers)) (fcounter (fn2-run-writers-counter w fn2-run-writers))
         ((unless (and (unsigned-byte-p 60 funit) (unsigned-byte-p 60 fcounter)))
          (mv :bounds fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         (fn2-seals (fn2-seals-put 0 (phase *fn2-seal-phase-install*) (filter 1) (funit funit) (fcounter fcounter))))
     (mv :more fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))))))
(fn2-seal-shape fn2-seal-filter (budget fn2-seals fn2-overlays fn2-overlay-index fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts
                                   fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (fn2-seals fn2-overlays fn2-overlay-index fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts
  fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests) t
 (fn2-ribbon-work fn2-ribbon-add fn2-ribbon-finish fn2-ov-entry fn2-seal-cache fn2-seals-sub fn2-seals-o fn2-seals-pos
  fn2-seals-fbase fn2-seals-wbase fn2-overlays-count fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen
  fn2-run-writers-unit fn2-run-writers-counter))

; ---------------------------------------------------------------------------
; Install: the run enters a free row of the resident view (the schema's run
; version moves), its filter is named, and the overlay is retired with its
; arena and the build's hash workspace released, in this one step.
(defun fn2-seal-free-row (k r fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :measure (nfix k) :guard (and (fn2-run-installed-wfp fn2-run-installed) (natp r))))
 (cond ((not (and (posp k) (natp r) (< r (fn2-run-installed-rows fn2-run-installed)))) (nfix (fn2-run-installed-rows fn2-run-installed)))
       ((equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*) r)
       (t (fn2-seal-free-row (- k 1) (+ 1 r) fn2-run-installed))))
(defthm fn2-seal-free-row-natp (natp (fn2-seal-free-row k r fn2-run-installed)) :rule-classes :type-prescription)
(in-theory (disable fn2-seal-free-row))
; The run named by the seal row enters a free row of the resident view, with
; its filter when it has one. (mv code installed)
(defun fn2-seal-install-run (fn2-seals fn2-run-installed)
 (declare (xargs :stobjs (fn2-seals fn2-run-installed)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-run-installed-wfp fn2-run-installed))
  :guard-hints (("Goal" :in-theory (disable fn2-run-install fn2-run-install-filter fn2-run-install-units fn2-seal-free-row fn2-seals-rows fn2-run-installed-rows fn2-seals-ufirst fn2-seals-units
                                            fn2-seals-okind fn2-seals-oslot fn2-seals-ogen fn2-seals-sid fn2-seals-run fn2-seals-top
                                            fn2-seals-rslot fn2-seals-rgen fn2-seals-runit fn2-seals-rcounter fn2-seals-entries)))))
 (b* (((unless (< 0 (fn2-seals-rows fn2-seals))) (mv :bounds fn2-run-installed))
      (rows (fn2-run-installed-rows fn2-run-installed))
      (r (fn2-seal-free-row rows 0 fn2-run-installed))
      ((unless (< r rows)) (mv :full fn2-run-installed))
      ((mv code fn2-run-installed)
       (fn2-run-install r (fn2-seals-sid 0 fn2-seals) (fn2-seals-run 0 fn2-seals) (fn2-seals-top 0 fn2-seals)
                        (fn2-seals-rslot 0 fn2-seals) (fn2-seals-rgen 0 fn2-seals) (fn2-seals-runit 0 fn2-seals)
                        (fn2-seals-rcounter 0 fn2-seals) (fn2-seals-entries 0 fn2-seals)
                        (fn2-seals-okind 0 fn2-seals) (fn2-seals-oslot 0 fn2-seals) (fn2-seals-ogen 0 fn2-seals) fn2-run-installed))
      ((unless (eq code :ok)) (mv code fn2-run-installed))
      ((mv code fn2-run-installed) (fn2-run-install-units r (fn2-seals-ufirst 0 fn2-seals) (fn2-seals-units 0 fn2-seals) fn2-run-installed))
      ((unless (eq code :ok)) (mv code fn2-run-installed))
      ((unless (equal (fn2-seals-filter 0 fn2-seals) 1)) (mv :ok fn2-run-installed)))
  (fn2-run-install-filter r (fn2-seals-funit 0 fn2-seals) (fn2-seals-fcounter 0 fn2-seals) fn2-run-installed)))
(fn2-seal-shape fn2-seal-install-run (fn2-seals fn2-run-installed) (fn2-run-installed) (fn2-seals fn2-run-installed) t
 (fn2-run-install fn2-run-install-filter fn2-run-install-units fn2-seal-free-row fn2-seals-okind fn2-seals-oslot fn2-seals-ogen fn2-seals-sid fn2-seals-run fn2-seals-top fn2-seals-rslot fn2-seals-rgen
  fn2-seals-runit fn2-seals-rcounter fn2-seals-entries fn2-seals-filter fn2-seals-funit fn2-seals-fcounter fn2-seals-o
  fn2-seals-hslot fn2-seals-hgen fn2-seals-ufirst fn2-seals-units))
; A merge's inputs: the live runs of SID from RLO on among rows R.. (K) (the
; plan's suffix; the run being installed is not yet among them).
(defun fn2-seal-inputs (k r sid rlo fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :measure (nfix k) :guard (and (fn2-run-installed-wfp fn2-run-installed) (natp r))))
 (if (not (and (posp k) (natp r) (< r (fn2-run-installed-rows fn2-run-installed)))) 0
  (+ (if (and (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)
              (equal (fn2-run-installed-schema r fn2-run-installed) sid)
              (<= (nfix rlo) (nfix (fn2-run-installed-run r fn2-run-installed))))
         1 0)
     (fn2-seal-inputs (- k 1) (+ 1 r) sid rlo fn2-run-installed))))
(defthm fn2-seal-inputs-natp (natp (fn2-seal-inputs k r sid rlo fn2-run-installed)) :rule-classes :type-prescription)
(in-theory (disable fn2-seal-inputs))
; ... and they retire.
(defun fn2-seal-retire-runs (k r sid rlo fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :measure (nfix k) :guard (and (fn2-run-installed-wfp fn2-run-installed) (natp r))
  :guard-hints (("Goal" :in-theory (disable fn2-run-retire)))))
 (b* (((unless (and (posp k) (natp r) (< r (fn2-run-installed-rows fn2-run-installed)))) (mv :ok fn2-run-installed))
      ((mv code fn2-run-installed)
       (if (and (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)
                (equal (fn2-run-installed-schema r fn2-run-installed) sid)
                (<= (nfix rlo) (nfix (fn2-run-installed-run r fn2-run-installed))))
           (fn2-run-retire r fn2-run-installed)
         (mv :ok fn2-run-installed)))
      ((unless (eq code :ok)) (mv code fn2-run-installed)))
  (fn2-seal-retire-runs (- k 1) (+ 1 r) sid rlo fn2-run-installed)))
(fn2-seal-shape fn2-seal-retire-runs (k r sid rlo fn2-run-installed) (fn2-run-installed) (fn2-run-installed) t (fn2-run-retire))
; Install, then retire the overlay and release the hash workspace: one step
; (no reader sees the run beside its published overlay, nor neither).
(defun fn2-seal-install (fn2-seals fn2-overlays fn2-run-installed fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-overlays fn2-run-installed fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-seal-install-run fn2-seal-retire fn2-seal-retire-runs fn2-seal-inputs fn2-pool-release fn2-pool-release-countp fn2-seals-k fn2-seals-sid fn2-seals-rlo
                                            fn2-seals-rows fn2-run-installed-rows fn2-overlays-rows fn2-pool-rows
                                            fn2-seals-o fn2-seals-hslot fn2-seals-hgen fn2-seals-okind fn2-seals-oslot fn2-seals-ogen)))))
 (b* (((unless (< 0 (fn2-seals-rows fn2-seals))) (mv :bounds fn2-seals fn2-overlays fn2-run-installed fn2-pool))
      (k (nfix (fn2-seals-k 0 fn2-seals)))
      (sid (fn2-seals-sid 0 fn2-seals)) (rlo (fn2-seals-rlo 0 fn2-seals))
      (rows (fn2-run-installed-rows fn2-run-installed))
      ;; the plan's runs, every one of them (only the sealer moves runs)
      ((unless (or (zp k) (equal (fn2-seal-inputs rows 0 sid rlo fn2-run-installed) k)))
       (mv :invariant fn2-seals fn2-overlays fn2-run-installed fn2-pool))
      ((mv code fn2-run-installed)
       (if (zp k) (mv :ok fn2-run-installed) (fn2-seal-retire-runs rows 0 sid rlo fn2-run-installed)))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-overlays fn2-run-installed fn2-pool))
      ((mv code fn2-run-installed) (fn2-seal-install-run fn2-seals fn2-run-installed))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-overlays fn2-run-installed fn2-pool))
      ((mv code fn2-overlays fn2-pool) (fn2-seal-retire (fn2-seals-o 0 fn2-seals) fn2-overlays fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-overlays fn2-run-installed fn2-pool))
      (hslot (fn2-seals-hslot 0 fn2-seals))
      ((unless (fn2-pool-release-countp hslot fn2-pool)) (mv :bounds fn2-seals fn2-overlays fn2-run-installed fn2-pool))
      ((mv code fn2-pool) (fn2-pool-release hslot (fn2-seals-hgen 0 fn2-seals) (fn2-seals-okind 0 fn2-seals)
                                            (fn2-seals-oslot 0 fn2-seals) (fn2-seals-ogen 0 fn2-seals) fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-overlays fn2-run-installed fn2-pool))
      (fn2-seals (fn2-seals-put 0 (phase (if (zp k) *fn2-seal-phase-idle* *fn2-seal-phase-release*)) (sub *fn2-seal-sub-open*)
                                (filter 0) (k 0) (held 0))))
  (mv :done fn2-seals fn2-overlays fn2-run-installed fn2-pool)))
(fn2-seal-shape fn2-seal-install (fn2-seals fn2-overlays fn2-run-installed fn2-pool)
 (fn2-seals fn2-overlays fn2-run-installed fn2-pool) (fn2-seals fn2-overlays fn2-run-installed fn2-pool) t
 (fn2-seal-install-run fn2-seal-retire fn2-seal-retire-runs fn2-seal-inputs fn2-seals-k fn2-seals-rlo fn2-pool-release fn2-pool-release-countp fn2-seals-okind fn2-seals-oslot fn2-seals-ogen fn2-seals-sid fn2-seals-run fn2-seals-top fn2-seals-rslot fn2-seals-rgen
  fn2-seals-runit fn2-seals-rcounter fn2-seals-entries fn2-seals-filter fn2-seals-funit fn2-seals-fcounter fn2-seals-o
  fn2-seals-hslot fn2-seals-hgen))

; ---------------------------------------------------------------------------
; Release (C5): a retired run's pages leave the cache and their workspaces
; return to the pool, one unit per step, UFIRST counting up to ULAST; the row
; is free once past it. Readers never meet a retired run's page: every run
; reader re-finds its sources when the schema's run version moved, which the
; merged run's install moved, before it reads a page again
; (machines-c-read.lisp (b); the transaction's run search,
; fn2-succ-resolve-step). With no retired row left the seal row is idle.
(defun fn2-seal-retired-row (k r fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :measure (nfix k) :guard (and (fn2-run-installed-wfp fn2-run-installed) (natp r))))
 (cond ((not (and (posp k) (natp r) (< r (fn2-run-installed-rows fn2-run-installed)))) (nfix (fn2-run-installed-rows fn2-run-installed)))
       ((equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-retired*) r)
       (t (fn2-seal-retired-row (- k 1) (+ 1 r) fn2-run-installed))))
(defthm fn2-seal-retired-row-natp (natp (fn2-seal-retired-row k r fn2-run-installed)) :rule-classes :type-prescription)
(in-theory (disable fn2-seal-retired-row))
(defun fn2-seal-release (fn2-seals fn2-run-installed fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-run-installed fn2-run-cache fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-run-installed-wfp fn2-run-installed) (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-seal-retired-row fn2-run-cache-drop fn2-run-retired-next fn2-pool-release
                                            fn2-pool-release-countp fn2-seals-rows fn2-run-installed-rows fn2-seals-okind
                                            fn2-seals-oslot fn2-seals-ogen)))))
 (b* (((unless (< 0 (fn2-seals-rows fn2-seals))) (mv :bounds fn2-seals fn2-run-installed fn2-run-cache fn2-pool))
      (rows (fn2-run-installed-rows fn2-run-installed))
      (r (fn2-seal-retired-row rows 0 fn2-run-installed))
      ((unless (< r rows))
       (let ((fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-idle* fn2-seals)))
        (mv :done fn2-seals fn2-run-installed fn2-run-cache fn2-pool)))
      (u (fn2-run-installed-ufirst r fn2-run-installed))
      ((mv code fn2-run-cache fn2-pool)
       (if (<= (nfix u) (nfix (fn2-run-installed-ulast r fn2-run-installed)))
           (b* (((mv code slot gen fn2-run-cache) (fn2-run-cache-drop (nfix u) fn2-run-cache))
                ((unless (eq code :ok)) (mv (if (eq code :absent) :ok code) fn2-run-cache fn2-pool))
                ((unless (fn2-pool-release-countp slot fn2-pool)) (mv :bounds fn2-run-cache fn2-pool))
                ((mv code fn2-pool) (fn2-pool-release slot gen (fn2-seals-okind 0 fn2-seals) (fn2-seals-oslot 0 fn2-seals)
                                                      (fn2-seals-ogen 0 fn2-seals) fn2-pool)))
             (mv code fn2-run-cache fn2-pool))
         (mv :ok fn2-run-cache fn2-pool)))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-run-installed fn2-run-cache fn2-pool))
      ((mv code fn2-run-installed) (fn2-run-retired-next r fn2-run-installed)))
  (mv (if (eq code :ok) :more code) fn2-seals fn2-run-installed fn2-run-cache fn2-pool)))
(fn2-seal-shape fn2-seal-release (fn2-seals fn2-run-installed fn2-run-cache fn2-pool)
 (fn2-seals fn2-run-installed fn2-run-cache fn2-pool) (fn2-seals fn2-run-installed fn2-run-cache fn2-pool) t
 (fn2-seal-retired-row fn2-run-cache-drop fn2-run-retired-next fn2-pool-release fn2-pool-release-countp fn2-seals-okind
  fn2-seals-oslot fn2-seals-ogen fn2-run-installed-ufirst fn2-run-installed-ulast))

; ---------------------------------------------------------------------------
; One bounded step of the sealer (BUDGET at most 4,096 bytes of page work):
; :idle (nothing sealable), :more, :retired (an empty overlay freed), :done
; (a run installed and its overlay retired), :full or :cache (backpressure:
; step again later), or a refusal (an invariant: the sealer machine's arm,
; fn2-sealer-seal, stops the executor with reason :sealer and the row goes
; :stopped; the step itself never sets a phase on refusal).
(defmacro fn2-seal-mv (code) `(mv ,code fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
                                  fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                                  fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths))
(defun fn2-seal-step (budget fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
                      fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                      fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)
 (declare (xargs :stobjs (fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
                          fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                          fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-seal-start fn2-seal-build fn2-seal-filter-open fn2-seal-filter fn2-seal-install
                                            fn2-seal-release fn2-seals-rows)))))
 (b* (((unless (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
                    (fn2-run-installed-wfp fn2-run-installed) (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers)
                    (fn2-run-restarts-wfp fn2-run-restarts) (fn2-run-cache-wfp fn2-run-cache) (fn2-ribbon-builds-wfp fn2-ribbon-builds)
                    (fn2-ribbon-band-wfp fn2-ribbon-band) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-fc-wfp fn2-fc)
                    (fn2-fc-context-wfp fn2-fc-context) (fn2-b3-wfp fn2-b3) (fn2-digests-wfp fn2-digests)
                    (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-run-cursors-wfp fn2-run-cursors)
                    (fn2-run-paths-wfp fn2-run-paths)
                    (< 0 (fn2-seals-rows fn2-seals)) (natp budget) (<= budget 4096)))
       (fn2-seal-mv :state))
      (phase (fn2-seals-phase 0 fn2-seals)))
  (cond
   ((equal phase *fn2-seal-phase-idle*)
    (mv-let (code fn2-seals fn2-overlays fn2-run-builds fn2-run-writers fn2-pool)
      (fn2-seal-start fn2-seals fn2-overlays fn2-run-installed fn2-run-builds fn2-run-writers fn2-pool)
     (fn2-seal-mv code)))
   ((equal phase *fn2-seal-phase-build*)
    (mv-let (code fn2-seals fn2-ranges fn2-range-sources fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths
                  fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
      (fn2-seal-build budget fn2-seals fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                      fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-run-cursors fn2-run-paths
                      fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (fn2-seal-mv code)))
   ((and (equal phase *fn2-seal-phase-filter*) (equal (fn2-seals-sub 0 fn2-seals) *fn2-seal-sub-open*))
    (mv-let (code fn2-seals fn2-ribbon-builds fn2-run-writers fn2-pool)
      (fn2-seal-filter-open fn2-seals fn2-overlays fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-pool)
     (fn2-seal-mv code)))
   ((equal phase *fn2-seal-phase-filter*)
    (mv-let (code fn2-seals fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
      (fn2-seal-filter budget fn2-seals fn2-overlays fn2-overlay-index fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts
                       fn2-run-cache fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (fn2-seal-mv code)))
   ((equal phase *fn2-seal-phase-install*)
    (mv-let (code fn2-seals fn2-overlays fn2-run-installed fn2-pool)
      (fn2-seal-install fn2-seals fn2-overlays fn2-run-installed fn2-pool)
     (fn2-seal-mv code)))
   ((equal phase *fn2-seal-phase-release*)
    (mv-let (code fn2-seals fn2-run-installed fn2-run-cache fn2-pool)
      (fn2-seal-release fn2-seals fn2-run-installed fn2-run-cache fn2-pool)
     (fn2-seal-mv code)))
   (t (fn2-seal-mv :state)))))
(fn2-seal-shape fn2-seal-step (budget fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
                                 fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                                 fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)
 (fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
  fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests
  fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)
 (fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
  fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests
  fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths) t
 (fn2-seal-start fn2-seal-build fn2-seal-filter-open fn2-seal-filter fn2-seal-install fn2-seal-release fn2-seals-phase fn2-seals-sub))
(assert-event (fn2-assert-compliant-p '(fn2-seal-step fn2-seal-pending-p fn2-seal-cache) (w state)))
