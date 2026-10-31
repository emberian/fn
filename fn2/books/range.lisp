; Layer C3: range reads over a schema's overlays and live runs, and the read
; contract (UNIVERSAL-CONSTRUCTIONS 2.4 with section 12 decision 2).
;
; A range read delivers, in key order, the entries whose keys lie in
; [lo, hi]: a merge of one source per overlay of the schema (active or
; frozen) and per live run. Each source holds one decoded head; a step
; advances the sources that need it, delivers the least head, and makes
; that key's successor the query, so the read's meaning is its resume key
; and the schema's version, never a physical position. When the version
; moved (a seal, a merge) every source is found again strictly after the
; resume key; when an overlay took an insert its source is located again.
; Equal keys in two sources (an overlay and the run it is being sealed into)
; deliver once, the newest source winning: an overlay is newer than any
; run, a run with a greater identifier newer than one with a smaller, an
; overlay taken later (its SEQ: batch order, C-S3) newer than one taken
; earlier.
; Range reads take schemas whose key fields are integers (C-RANGE-KEYS).
; Every step is bounded; :more resumes, :miss names the page a run source's
; cursor waits for.
(in-package "ACL2")
(include-book "runs-assemble")
(fn2-book-layer :c)
; B's and A's shape lemmas are stated over the rows accessors; keep them folded.
(local (in-theory (disable fn2-pool-rows fn2-fields-rows fn2-digests-rows fn2-fc-rows fn2-fc-context-rows fn2-b3-rows)))

(defcolumns fn2-ranges
 ((phase (:enum fn2-range-phase (:idle :seek :merge :done)))
  (schema :u60) (qbase :u32) (hbase :u32) (sbase :u32) (smax :u32) (scount :u32)
  (cbase :u32) (rbase :u32) (vrun :u60) (pfield :u32) (plimit :u60)
  (out :u32) (ok :u8) (os :u32) (og :u60) (delivered :u60)
  (qk :u8) (qs :u32) (qg :u60)))
; A source's SRC is its overlay row or its run's fn2-run-installed row (not
; named REF: the reference view names each core child's copy NAME-REF).
(defcolumns fn2-range-sources
 ((kind (:enum fn2-range-kind (:none :overlay :run)))
  (src :u32) (state (:enum fn2-range-state (:seek :next :scan :head :end)))
  (pos :u32) (count :u32) (cursor :u32) (rb :u32) (run :u60)
  (okind :u8) (oslot :u32) (ogen :u60)))
; A read with no position limit names this field.
(defconst *fn2-range-no-position* 4294967295)

; ---------------------------------------------------------------------------
; The read contract. STRENGTH is :exactly-at or :at-least, P the position
; asked for, FALLBACK :wait, :stale-ok or :catch-up, COV the schema's
; coverage, APPEND whether the schema is a stream (an entry never changes,
; so its prefix at any position up to cov is retained) or latest-only.
; (mv outcome position limit): :read at POSITION, LIMIT the greatest
; position a delivered stream entry may carry (nil: none); :stale (read at
; cov, said so); :wait (at cov; come back when cov reaches p); :gap (exact
; history at p is not retained); :unavailable (catch-up needs maintenance
; state and a suffix interpreter this schema does not have); :refused.
; Every outcome carries its position.
(defun fn2-read-plan (strength p fallback cov append)
 (declare (xargs :guard t))
 (cond ((not (and (natp p) (natp cov) (member-eq strength '(:exactly-at :at-least))
                  (member-eq fallback '(:wait :stale-ok :catch-up))))
        (mv :refused 0 nil))
       ((<= p cov)
        (cond ((eq strength :at-least) (mv :read cov nil))
              (append (mv :read p p))
              ((equal p cov) (mv :read cov nil))
              (t (mv :gap cov nil))))
       ((eq fallback :wait) (mv :wait cov nil))
       ((eq fallback :stale-ok) (mv :stale cov nil))
       (t (mv :unavailable cov nil))))
(assert-event (and (equal (mv-list 3 (fn2-read-plan :at-least 5 :wait 9 t)) '(:read 9 nil))
                   (equal (mv-list 3 (fn2-read-plan :exactly-at 5 :wait 9 t)) '(:read 5 5))
                   (equal (mv-list 3 (fn2-read-plan :exactly-at 5 :wait 9 nil)) '(:gap 9 nil))
                   (equal (mv-list 3 (fn2-read-plan :exactly-at 9 :wait 9 nil)) '(:read 9 nil))
                   (equal (mv-list 3 (fn2-read-plan :at-least 12 :wait 9 t)) '(:wait 9 nil))
                   (equal (mv-list 3 (fn2-read-plan :at-least 12 :stale-ok 9 t)) '(:stale 9 nil))
                   (equal (mv-list 3 (fn2-read-plan :exactly-at 12 :catch-up 9 t)) '(:unavailable 9 nil))
                   (equal (mv-list 3 (fn2-read-plan :sometime 1 :wait 9 t)) '(:refused 0 nil))))

; ---------------------------------------------------------------------------
; Sources. Source I of range G is row SBASE+I; a run source reads through
; cursor row CBASE+I; every source's head is decoded at the reader region
; RBASE + I * reader-fields (its entry rows at +*fn2-run-reader-entry*).
(defmacro fn2-rg-ok (g) `(and (natp ,g) (< ,g (fn2-ranges-rows fn2-ranges))))
(defun fn2-range-add-source (g i kind ref run ok os og fn2-ranges fn2-range-sources)
 (declare (xargs :stobjs (fn2-ranges fn2-range-sources)
  :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources))))
 (b* (((unless (and (fn2-rg-ok g) (natp i))) (mv :bounds fn2-range-sources))
      ((unless (< i (fn2-ranges-smax g fn2-ranges))) (mv :sources fn2-range-sources))
      (row (+ (fn2-ranges-sbase g fn2-ranges) i))
      (cursor (+ (fn2-ranges-cbase g fn2-ranges) i))
      (rb (+ (fn2-ranges-rbase g fn2-ranges) (* i *fn2-run-reader-fields*)))
      ((unless (and (< row (fn2-range-sources-rows fn2-range-sources)) (natp kind) (< kind *fn2-range-kind-count*)
                    (unsigned-byte-p 32 ref) (unsigned-byte-p 32 cursor) (unsigned-byte-p 32 rb) (unsigned-byte-p 60 run)
                    (unsigned-byte-p 8 ok) (unsigned-byte-p 32 os) (unsigned-byte-p 60 og)))
       (mv :bounds fn2-range-sources))
      (fn2-range-sources (fn2-range-sources-put row (kind kind) (src ref) (state *fn2-range-state-seek*) (pos 0) (count 0)
                                                (cursor cursor) (rb rb) (run run) (okind ok) (oslot os) (ogen og))))
  (mv :ok fn2-range-sources)))
(fn2-range-sources-preserves fn2-range-add-source (g i kind ref run ok os og fn2-ranges fn2-range-sources) :position 1 :raw-rows t
 :hyps ((fn2-rangesp fn2-ranges) (fn2-ranges-wfp fn2-ranges) (fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources)))
; The schema's overlays (active or frozen), from overlay row N-1 down; I is
; the next source index. (mv code i sources)
(defun fn2-range-add-overlays (n i g sid fn2-ranges fn2-range-sources fn2-overlays)
 (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-overlays) :measure (nfix n)
  :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays)
              (natp n) (<= n (fn2-overlays-rows fn2-overlays)) (natp i))
  :guard-hints (("Goal" :in-theory (disable fn2-range-add-source)))))
 (b* (((when (zp n)) (mv :ok i fn2-range-sources))
      (o (- n 1))
      ((unless (and (equal (fn2-overlays-schema o fn2-overlays) sid)
                    (member (fn2-overlays-phase o fn2-overlays) (list *fn2-overlay-phase-active* *fn2-overlay-phase-frozen*))))
       (fn2-range-add-overlays (- n 1) i g sid fn2-ranges fn2-range-sources fn2-overlays))
      ((mv code fn2-range-sources)
       (fn2-range-add-source g i *fn2-range-kind-overlay* o (fn2-overlays-seq o fn2-overlays) (fn2-overlays-okind o fn2-overlays)
                             (fn2-overlays-oslot o fn2-overlays) (fn2-overlays-ogen o fn2-overlays) fn2-ranges fn2-range-sources))
      ((unless (eq code :ok)) (mv code i fn2-range-sources)))
  (fn2-range-add-overlays (- n 1) (+ 1 i) g sid fn2-ranges fn2-range-sources fn2-overlays)))
(defthm fn2-range-add-overlays-natp
 (implies (natp i) (natp (mv-nth 1 (fn2-range-add-overlays n i g sid fn2-ranges fn2-range-sources fn2-overlays))))
 :rule-classes :type-prescription)
(fn2-range-sources-preserves fn2-range-add-overlays (n i g sid fn2-ranges fn2-range-sources fn2-overlays) :position 2 :raw-rows t
 :hyps ((fn2-rangesp fn2-ranges) (fn2-ranges-wfp fn2-ranges) (fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources)))
(defun fn2-range-add-runs (n i g sid fn2-ranges fn2-range-sources fn2-run-installed)
 (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-run-installed) :measure (nfix n)
  :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-run-installed-wfp fn2-run-installed)
              (natp n) (<= n (fn2-run-installed-rows fn2-run-installed)) (natp i))
  :guard-hints (("Goal" :in-theory (disable fn2-range-add-source)))))
 (b* (((when (zp n)) (mv :ok i fn2-range-sources))
      (r (- n 1))
      ((unless (and (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)
                    (equal (fn2-run-installed-schema r fn2-run-installed) sid)))
       (fn2-range-add-runs (- n 1) i g sid fn2-ranges fn2-range-sources fn2-run-installed))
      ((mv code fn2-range-sources)
       (fn2-range-add-source g i *fn2-range-kind-run* r (fn2-run-installed-run r fn2-run-installed)
                             (fn2-run-installed-okind r fn2-run-installed) (fn2-run-installed-oslot r fn2-run-installed)
                             (fn2-run-installed-ogen r fn2-run-installed) fn2-ranges fn2-range-sources))
      ((unless (eq code :ok)) (mv code i fn2-range-sources)))
  (fn2-range-add-runs (- n 1) (+ 1 i) g sid fn2-ranges fn2-range-sources fn2-run-installed)))
(defthm fn2-range-add-runs-natp
 (implies (natp i) (natp (mv-nth 1 (fn2-range-add-runs n i g sid fn2-ranges fn2-range-sources fn2-run-installed))))
 :rule-classes :type-prescription)
(fn2-range-sources-preserves fn2-range-add-runs (n i g sid fn2-ranges fn2-range-sources fn2-run-installed) :position 2 :raw-rows t
 :hyps ((fn2-rangesp fn2-ranges) (fn2-ranges-wfp fn2-ranges) (fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources)))
; (Re)find every source: the schema's overlays and live runs, all to seek
; strictly after the current query, the version taken now.
(defun fn2-range-enumerate (g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
  :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays)
              (fn2-run-installed-wfp fn2-run-installed))
  :guard-hints (("Goal" :in-theory (disable fn2-range-add-overlays fn2-range-add-runs)))))
 (b* (((unless (fn2-rg-ok g)) (mv :bounds fn2-ranges fn2-range-sources))
      (sid (fn2-ranges-schema g fn2-ranges))
      ((mv code i fn2-range-sources)
       (fn2-range-add-overlays (fn2-overlays-rows fn2-overlays) 0 g sid fn2-ranges fn2-range-sources fn2-overlays))
      ((unless (eq code :ok)) (mv code fn2-ranges fn2-range-sources))
      ((mv code i fn2-range-sources)
       (fn2-range-add-runs (fn2-run-installed-rows fn2-run-installed) i g sid fn2-ranges fn2-range-sources fn2-run-installed))
      ((unless (eq code :ok)) (mv code fn2-ranges fn2-range-sources))
      (vrun (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed))
      ((unless (and (unsigned-byte-p 32 i) (unsigned-byte-p 60 vrun))) (mv :bounds fn2-ranges fn2-range-sources))
      (fn2-ranges (fn2-ranges-put g (phase *fn2-range-phase-seek*) (scount i) (vrun vrun))))
  (mv :ok fn2-ranges fn2-range-sources)))
(fn2-ranges-preserves fn2-range-enumerate (g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed) :position 1 :raw-rows t :disable nil
 :hyps ((fn2-rangesp fn2-ranges) (fn2-ranges-wfp fn2-ranges) (fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources)))
(fn2-range-sources-preserves fn2-range-enumerate (g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed) :position 2
 :prefix "-SOURCES-PRESERVES" :raw-rows t
 :hyps ((fn2-rangesp fn2-ranges) (fn2-ranges-wfp fn2-ranges) (fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources)))

; An overlay that took an insert since its source located it is located
; again (strictly after the query); N counts the sources down.
(defun fn2-range-recheck (n g fn2-ranges fn2-range-sources fn2-overlays)
 (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-overlays) :measure (nfix n)
  :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays) (natp n))))
 (b* (((when (zp n)) (mv :ok fn2-range-sources))
      ((unless (fn2-rg-ok g)) (mv :bounds fn2-range-sources))
      (s (+ (fn2-ranges-sbase g fn2-ranges) (- n 1)))
      ((unless (< s (fn2-range-sources-rows fn2-range-sources))) (mv :bounds fn2-range-sources))
      (o (fn2-range-sources-src s fn2-range-sources))
      (fn2-range-sources
       (if (and (equal (fn2-range-sources-kind s fn2-range-sources) *fn2-range-kind-overlay*)
                (not (equal (fn2-range-sources-state s fn2-range-sources) *fn2-range-state-seek*))
                (< o (fn2-overlays-rows fn2-overlays))
                (not (equal (fn2-overlays-count o fn2-overlays) (fn2-range-sources-count s fn2-range-sources))))
           (fn2-range-sources-set-state s *fn2-range-state-seek* fn2-range-sources)
         fn2-range-sources)))
  (fn2-range-recheck (- n 1) g fn2-ranges fn2-range-sources fn2-overlays)))
(fn2-range-sources-preserves fn2-range-recheck (n g fn2-ranges fn2-range-sources fn2-overlays) :position 1 :raw-rows t
 :hyps ((fn2-rangesp fn2-ranges) (fn2-ranges-wfp fn2-ranges) (fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources)))

; Start range read G over schema SID. The caller holds lo's key fields at
; QBASE and hi's at HBASE (query owner QK QS QG); PFIELD names the entry's
; position field and PLIMIT the greatest position delivered (a stream read
; exactly at PLIMIT), or PFIELD is *fn2-range-no-position*.
(defun fn2-range-start (g sid qbase hbase sbase smax cbase rbase pfield plimit qk qs qg
                          fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)
  :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays)
              (fn2-run-installed-wfp fn2-run-installed))
  :guard-hints (("Goal" :in-theory (disable fn2-range-enumerate)))))
 (b* (((unless (and (fn2-rg-ok g) (unsigned-byte-p 60 sid) (unsigned-byte-p 32 qbase) (unsigned-byte-p 32 hbase)
                    (unsigned-byte-p 32 sbase) (unsigned-byte-p 32 smax) (unsigned-byte-p 32 cbase) (unsigned-byte-p 32 rbase)
                    (unsigned-byte-p 32 pfield) (unsigned-byte-p 60 plimit)
                    (unsigned-byte-p 8 qk) (unsigned-byte-p 32 qs) (unsigned-byte-p 60 qg)))
       (mv :bounds fn2-ranges fn2-range-sources))
      (fn2-ranges (fn2-ranges-put g (phase *fn2-range-phase-idle*) (schema sid) (qbase qbase) (hbase hbase) (sbase sbase)
                                  (smax smax) (scount 0) (cbase cbase) (rbase rbase) (vrun 0) (pfield pfield) (plimit plimit)
                                  (out 0) (ok 0) (os 0) (og 0) (delivered 0) (qk qk) (qs qs) (qg qg))))
  (fn2-range-enumerate g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)))
(assert-event (fn2-assert-compliant-p '(fn2-range-start fn2-range-recheck) (w state)))

; A positioned seek (INBOX 4.1, Seek(stream, after = p)) over a stream whose
; position grows with its key's last field (overview within a group): the
; least last-field value N from which every entry carries a position above
; P, found by bisection over range reads of one entry each (C-POSITION-SEEK). A row
; drives range G: its query and hi regions hold the stream's key prefix;
; the seek writes only their last key field.
(defcolumns fn2-seeks
 ((phase (:enum fn2-seek-phase (:idle :probe :read :entry :end :done)))
  (g :u32) (lo :u60) (hi :u60) (mid :u60) (after :u60) (pfield :u32) (probes :u32)))
; Start positioned seek K over range row G (already started by the caller
; on the stream's prefix: its query and hi regions hold the prefix fields):
; the answer is the least last-field value in [LO, HI] from which every
; entry has a position above P. PFIELD names the position field.
(defun fn2-seek-start (k g lo hi p pfield fn2-seeks)
 (declare (xargs :stobjs fn2-seeks :guard (fn2-seeks-wfp fn2-seeks)))
 (b* (((unless (and (natp k) (< k (fn2-seeks-rows fn2-seeks)) (unsigned-byte-p 32 g) (unsigned-byte-p 60 lo)
                    (unsigned-byte-p 60 hi) (unsigned-byte-p 60 p) (unsigned-byte-p 32 pfield)))
       (mv :bounds fn2-seeks))
      (fn2-seeks (fn2-seeks-put k (phase *fn2-seek-phase-probe*) (g g) (lo lo) (hi hi) (mid lo) (after p)
                                            (pfield pfield) (probes 0))))
  (mv :ok fn2-seeks)))
; Copy N field rows from FROM to TO (value, reference, status).
(defun fn2-range-copy-rows (n from to fn2-fields)
 (declare (xargs :stobjs fn2-fields :measure (nfix n)
  :guard (and (fn2-fields-wfp fn2-fields) (natp n) (natp from) (natp to))
  :guard-hints (("Goal" :in-theory (disable fn2-run-copy-row)))))
 (cond ((zp n) (mv :ok fn2-fields))
       ((not (and (natp from) (natp to) (< (+ from n -1) (fn2-fields-rows fn2-fields)) (< (+ to n -1) (fn2-fields-rows fn2-fields))))
        (mv :bounds fn2-fields))
       (t (let ((fn2-fields (fn2-run-copy-row (+ from n -1) (+ to n -1) fn2-fields)))
           (fn2-range-copy-rows (- n 1) from to fn2-fields)))))
(fn2-fields-preserves fn2-range-copy-rows (n from to fn2-fields) :position 1
 :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (natp from) (natp to)))

; ---------------------------------------------------------------------------
; The parts that read entries, generated after the run assembly.
(defun fn2-rga-integer-kindp (k)
 (declare (xargs :guard t))
 (or (member-eq k '(:u8 :u16 :u32 :u64 :u60 :bool :varint))
     (and (consp k) (member-eq (car k) '(:id :enum)))))
(defun fn2-rga-integer-keysp (key)
 (declare (xargs :guard t))
 (or (atom key) (and (consp (car key)) (consp (cdar key)) (fn2-rga-integer-kindp (cadar key)) (fn2-rga-integer-keysp (cdr key)))))
(defun fn2-rga-integer-ids (rows)
 (declare (xargs :verify-guards nil))
 (cond ((atom rows) nil)
       ((fn2-rga-integer-keysp (fn2-decl-get :key (cdar rows))) (cons (fn2-decl-get :id (cdar rows)) (fn2-rga-integer-ids (cdr rows))))
       (t (fn2-rga-integer-ids (cdr rows)))))
(defmacro fn2-rga-guard ()
 '(and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays)
       (fn2-overlay-index-wfp fn2-overlay-index) (fn2-run-installed-wfp fn2-run-installed) (fn2-run-cursors-wfp fn2-run-cursors)
       (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp fn2-run-cache) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))

(defmacro fn2-range-assemble ()
 '(encapsulate ()
   (fn2-run-assembly-theory)
   ;; Schemas whose key fields are all integers.
   (make-event (value `(defun fn2-range-keys-ok (sid)
                         (declare (xargs :guard t))
                         (if (member-equal sid ',(fn2-rga-integer-ids (fn2-decl-rows :schema (w state)))) t nil))))
   ;; Advance overlay source S: from :seek, locate the least entry at or
   ;; after the query; from :next, the following position.
   (defun fn2-range-advance-overlay (s qbase qk qs qg fn2-range-sources fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
    (declare (xargs :stobjs (fn2-range-sources fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
     :guard (and (fn2-range-sources-wfp fn2-range-sources) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
                 (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
     :guard-hints (("Goal" :in-theory (disable fn2-ov-locate fn2-ov-entry fn2-fields-rows)))))
    (b* (((unless (and (natp s) (< s (fn2-range-sources-rows fn2-range-sources)))) (mv :bounds fn2-range-sources fn2-fields))
         (o (fn2-range-sources-src s fn2-range-sources))
         (eb (+ (fn2-range-sources-rb s fn2-range-sources) *fn2-run-reader-entry*))
         ((unless (and (< o (fn2-overlays-rows fn2-overlays)) (natp qbase)
                       (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))))
          (mv :bounds fn2-range-sources fn2-fields))
         (count (fn2-overlays-count o fn2-overlays))
         ((mv code pos fn2-fields)
          (if (equal (fn2-range-sources-state s fn2-range-sources) *fn2-range-state-seek*)
              (mv-let (code pos order fn2-fields) (fn2-ov-locate o eb qbase qk qs qg fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
               (declare (ignore order)) (mv code pos fn2-fields))
            (mv :ok (+ 1 (nfix (fn2-range-sources-pos s fn2-range-sources))) fn2-fields)))
         ((unless (eq code :ok)) (mv code fn2-range-sources fn2-fields))
         ((unless (and (natp pos) (unsigned-byte-p 32 pos) (unsigned-byte-p 32 count))) (mv :bounds fn2-range-sources fn2-fields))
         ((unless (< pos count))
          (let ((fn2-range-sources (fn2-range-sources-put s (state *fn2-range-state-end*) (pos pos) (count count))))
           (mv :ok fn2-range-sources fn2-fields)))
         ((mv code & fn2-fields) (fn2-ov-entry o pos eb fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
         ((unless (eq code :ok)) (mv code fn2-range-sources fn2-fields))
         (fn2-range-sources (fn2-range-sources-put s (state *fn2-range-state-head*) (pos pos) (count count))))
     (mv :ok fn2-range-sources fn2-fields)))
   ;; Advance run source S: start its cursor at the run's root, then scan
   ;; to its next entry at or after the query.
   (defun fn2-range-advance-run (s sid budget qbase qk qs qg fn2-range-sources fn2-run-installed fn2-run-cursors fn2-run-paths
                                   fn2-run-cache fn2-fields fn2-pool)
    (declare (xargs :stobjs (fn2-range-sources fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
     :guard (and (fn2-range-sources-wfp fn2-range-sources) (fn2-run-installed-wfp fn2-run-installed) (fn2-run-cursors-wfp fn2-run-cursors)
                 (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp fn2-run-cache) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
                 (natp budget))
     :guard-hints (("Goal" :in-theory (disable fn2-run-cursor-start fn2-run-scan-step)))))
    (b* (((unless (and (natp s) (< s (fn2-range-sources-rows fn2-range-sources)))) (mv :bounds fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         (r (fn2-range-sources-src s fn2-range-sources)) (c (fn2-range-sources-cursor s fn2-range-sources))
         ((unless (< r (fn2-run-installed-rows fn2-run-installed))) (mv :bounds fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         ((mv code fn2-run-cursors)
          (if (equal (fn2-range-sources-state s fn2-range-sources) *fn2-range-state-seek*)
              (fn2-run-cursor-start c sid (fn2-run-installed-top r fn2-run-installed) (fn2-run-installed-slot r fn2-run-installed)
                                    (fn2-run-installed-gen r fn2-run-installed) (fn2-run-installed-unit r fn2-run-installed)
                                    (fn2-run-installed-counter r fn2-run-installed) (fn2-range-sources-rb s fn2-range-sources)
                                    (fn2-run-installed-okind r fn2-run-installed) (fn2-run-installed-oslot r fn2-run-installed)
                                    (fn2-run-installed-ogen r fn2-run-installed) fn2-run-cursors)
            (mv :ok fn2-run-cursors)))
         ((unless (eq code :ok)) (mv code fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         (fn2-range-sources (fn2-range-sources-set-state s *fn2-range-state-scan* fn2-range-sources))
         ((mv code fn2-run-cursors fn2-run-paths fn2-fields)
          (fn2-run-scan-step c budget qbase qk qs qg fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
         ((unless (and (natp s) (< s (fn2-range-sources-rows fn2-range-sources)))) (mv :bounds fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
     (case code
      (:entry (let ((fn2-range-sources (fn2-range-sources-set-state s *fn2-range-state-head* fn2-range-sources)))
               (mv :ok fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
      (:end (let ((fn2-range-sources (fn2-range-sources-set-state s *fn2-range-state-end* fn2-range-sources)))
             (mv :ok fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
      (:lost (let ((fn2-range-sources (fn2-range-sources-set-state s *fn2-range-state-seek* fn2-range-sources)))
              (mv :more fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
      (otherwise (mv code fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))))
   (fn2-ra-shape fn2-range-advance-overlay-shape
    (fn2-range-advance-overlay s qbase qk qs qg fn2-range-sources fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
    (and (fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))
    ((fn2-range-sources 1) (fn2-fields 2)) (fn2-range-sourcesp fn2-range-sources-wfp fn2-ov-locate fn2-ov-entry fn2-run-cursors-rows fn2-run-paths-rows fn2-fields-rows fn2-range-sources-rows fn2-ranges-rows))
   (fn2-ra-shape fn2-range-advance-run-shape
    (fn2-range-advance-run s sid budget qbase qk qs qg fn2-range-sources fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
    (and (fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-run-cursorsp fn2-run-cursors) (fn2-run-cursors-wfp fn2-run-cursors)
         (fn2-run-pathsp fn2-run-paths) (fn2-run-paths-wfp fn2-run-paths))
    ((fn2-range-sources 1) (fn2-run-cursors 2) (fn2-run-paths 3) (fn2-fields 4))
    (fn2-range-sourcesp fn2-range-sources-wfp fn2-run-cursor-start fn2-run-scan-step fn2-run-cursors-rows fn2-run-paths-rows fn2-fields-rows fn2-range-sources-rows fn2-ranges-rows))
   (in-theory (disable fn2-range-advance-overlay fn2-range-advance-run))
   ;; Advance every source that needs it, sources counted down by N.
   ;; :ok when all have a head or are at their end.
   (defun fn2-range-advance-all (n g budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                                   fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
    (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                             fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
     :measure (nfix n) :guard (and (fn2-rga-guard) (natp n) (natp budget))
     :guard-hints (("Goal" :in-theory (disable fn2-range-advance-overlay fn2-range-advance-run fn2-fields-rows)))))
    (b* (((when (zp n)) (mv :ok fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         ((unless (fn2-rg-ok g)) (mv :bounds fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         (s (+ (fn2-ranges-sbase g fn2-ranges) (- n 1)))
         ((unless (< s (fn2-range-sources-rows fn2-range-sources))) (mv :bounds fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         (st (fn2-range-sources-state s fn2-range-sources))
         ((when (or (equal st *fn2-range-state-head*) (equal st *fn2-range-state-end*)))
          (fn2-range-advance-all (- n 1) g budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                                 fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
         (qbase (fn2-ranges-qbase g fn2-ranges)) (qk (fn2-ranges-qk g fn2-ranges))
         (qs (fn2-ranges-qs g fn2-ranges)) (qg (fn2-ranges-qg g fn2-ranges))
         ((mv code fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
          (if (equal (fn2-range-sources-kind s fn2-range-sources) *fn2-range-kind-overlay*)
              (mv-let (code fn2-range-sources fn2-fields)
                (fn2-range-advance-overlay s qbase qk qs qg fn2-range-sources fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
               (mv code fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
            (fn2-range-advance-run s (fn2-ranges-schema g fn2-ranges) budget qbase qk qs qg fn2-range-sources fn2-run-installed
                                   fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
         ((unless (eq code :ok)) (mv code fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
     (fn2-range-advance-all (- n 1) g budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                            fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
   (fn2-ra-shape fn2-range-advance-all-shape
    (fn2-range-advance-all n g budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                           fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
    (and (fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-run-cursorsp fn2-run-cursors) (fn2-run-cursors-wfp fn2-run-cursors)
         (fn2-run-pathsp fn2-run-paths) (fn2-run-paths-wfp fn2-run-paths))
    ((fn2-range-sources 1) (fn2-run-cursors 2) (fn2-run-paths 3) (fn2-fields 4))
    (fn2-range-sourcesp fn2-range-sources-wfp fn2-run-cursors-rows fn2-run-paths-rows fn2-fields-rows fn2-range-sources-rows fn2-ranges-rows))
   (in-theory (disable fn2-range-advance-all))
   ;; How the heads of sources A and B (absolute rows) compare: (mv code order).
   (defun fn2-range-order (sid a b fn2-range-sources fn2-fields fn2-pool)
    (declare (xargs :stobjs (fn2-range-sources fn2-fields fn2-pool)
     :guard (and (fn2-range-sources-wfp fn2-range-sources) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
    (b* (((unless (and (natp a) (< a (fn2-range-sources-rows fn2-range-sources)) (natp b) (< b (fn2-range-sources-rows fn2-range-sources))))
          (mv :bounds :eq))
         (ea (+ (fn2-range-sources-rb a fn2-range-sources) *fn2-run-reader-entry*))
         (eb (+ (fn2-range-sources-rb b fn2-range-sources) *fn2-run-reader-entry*))
         ((unless (and (<= (+ ea *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields)) (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))))
          (mv :bounds :eq)))
     (fn2-run-layout-compare sid ea eb (fn2-range-sources-okind a fn2-range-sources) (fn2-range-sources-oslot a fn2-range-sources)
                             (fn2-range-sources-ogen a fn2-range-sources) (fn2-range-sources-okind b fn2-range-sources)
                             (fn2-range-sources-oslot b fn2-range-sources) (fn2-range-sources-ogen b fn2-range-sources) fn2-fields fn2-pool)))
   ;; Source A is newer than B: an overlay than a run; a later run than an
   ;; earlier; an overlay taken later (its SEQ, C-S3) than an earlier.
   (defun fn2-range-newer (a b fn2-range-sources)
    (declare (xargs :stobjs fn2-range-sources :guard (fn2-range-sources-wfp fn2-range-sources)))
    (and (natp a) (< a (fn2-range-sources-rows fn2-range-sources)) (natp b) (< b (fn2-range-sources-rows fn2-range-sources))
         (or (and (equal (fn2-range-sources-kind a fn2-range-sources) *fn2-range-kind-overlay*)
                  (not (equal (fn2-range-sources-kind b fn2-range-sources) *fn2-range-kind-overlay*)))
             (and (equal (fn2-range-sources-kind a fn2-range-sources) (fn2-range-sources-kind b fn2-range-sources))
                  (< (fn2-range-sources-run b fn2-range-sources) (fn2-range-sources-run a fn2-range-sources))))))
   (in-theory (disable fn2-range-order fn2-range-newer))
   ;; The least head among sources BASE+N-1 .. BASE (absolute rows), the
   ;; newest on equal keys; BEST is the best so far or nil.
   (defun fn2-range-pick (n base sid best fn2-range-sources fn2-fields fn2-pool)
    (declare (xargs :stobjs (fn2-range-sources fn2-fields fn2-pool) :measure (nfix n)
     :guard (and (fn2-range-sources-wfp fn2-range-sources) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp n) (natp base))
     :guard-hints (("Goal" :in-theory (disable fn2-range-order fn2-range-newer)))))
    (b* (((when (zp n)) (mv :ok best))
         (s (+ base (- n 1)))
         ((unless (and (< s (fn2-range-sources-rows fn2-range-sources))
                       (equal (fn2-range-sources-state s fn2-range-sources) *fn2-range-state-head*)))
          (fn2-range-pick (- n 1) base sid best fn2-range-sources fn2-fields fn2-pool))
         ((unless (natp best)) (fn2-range-pick (- n 1) base sid s fn2-range-sources fn2-fields fn2-pool))
         ((mv code order) (fn2-range-order sid s best fn2-range-sources fn2-fields fn2-pool))
         ((unless (eq code :ok)) (mv code best))
         (better (or (eq order :lt) (and (eq order :eq) (fn2-range-newer s best fn2-range-sources)))))
     (fn2-range-pick (- n 1) base sid (if better s best) fn2-range-sources fn2-fields fn2-pool)))
   ;; Every source whose head equals BEST's key (BEST among them) moves on.
   (defun fn2-range-consume (n base sid best fn2-range-sources fn2-fields fn2-pool)
    (declare (xargs :stobjs (fn2-range-sources fn2-fields fn2-pool) :measure (nfix n)
     :guard (and (fn2-range-sources-wfp fn2-range-sources) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp n) (natp base)
                 (natp best))))
    (b* (((when (zp n)) (mv :ok fn2-range-sources))
         (s (+ base (- n 1)))
         ((unless (and (< s (fn2-range-sources-rows fn2-range-sources))
                       (equal (fn2-range-sources-state s fn2-range-sources) *fn2-range-state-head*)))
          (fn2-range-consume (- n 1) base sid best fn2-range-sources fn2-fields fn2-pool))
         ((mv code order) (fn2-range-order sid s best fn2-range-sources fn2-fields fn2-pool))
         ((unless (eq code :ok)) (mv code fn2-range-sources))
         (fn2-range-sources (if (eq order :eq) (fn2-range-sources-set-state s *fn2-range-state-next* fn2-range-sources) fn2-range-sources)))
     (fn2-range-consume (- n 1) base sid best fn2-range-sources fn2-fields fn2-pool)))
   (fn2-range-sources-preserves fn2-range-consume (n base sid best fn2-range-sources fn2-fields fn2-pool) :position 1 :raw-rows t
    :hyps ((fn2-range-sourcesp fn2-range-sources) (fn2-range-sources-wfp fn2-range-sources) (natp base)))
   (in-theory (disable fn2-range-pick))
   ;; The query becomes the successor of the delivered key at EB: its key
   ;; fields, the last one plus one (integer keys).
   (defun fn2-range-successor (sid eb qbase fn2-fields)
    (declare (xargs :stobjs fn2-fields :guard (fn2-fields-wfp fn2-fields)
     :guard-hints (("Goal" :in-theory (disable fn2-run-copy-row)))))
    (b* ((nk (fn2-run-layout-keys sid))
         ((unless (and (natp eb) (natp qbase) (posp nk) (<= nk *fn2-run-key-fields-max*)
                       (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))
                       (<= (+ qbase *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))))
          (mv :bounds fn2-fields))
         ((mv code fn2-fields) (fn2-range-copy-rows nk eb qbase fn2-fields))
         ((unless (eq code :ok)) (mv code fn2-fields))
         (last (+ qbase (- nk 1)))
         ((unless (< last (fn2-fields-rows fn2-fields))) (mv :bounds fn2-fields))
         (v (+ 1 (nfix (fn2-fields-value last fn2-fields))))
         ((unless (unsigned-byte-p 60 v)) (mv :bounds fn2-fields))
         (fn2-fields (fn2-fields-set-value last v fn2-fields)))
     (mv :ok fn2-fields)))
   (fn2-ra-shape fn2-range-successor-shape (fn2-range-successor sid eb qbase fn2-fields)
    (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)) ((fn2-fields 1)) (fn2-range-copy-rows fn2-run-cursors-rows fn2-run-paths-rows fn2-fields-rows fn2-range-sources-rows fn2-ranges-rows))
   (in-theory (disable fn2-range-successor))
   ;; Is the entry at EB past the range's end: its key above hi, or its
   ;; position above the limit? (mv code past)
   (defun fn2-range-past (g eb ok os og fn2-ranges fn2-fields fn2-pool)
    (declare (xargs :stobjs (fn2-ranges fn2-fields fn2-pool)
     :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
    (b* (((unless (and (fn2-rg-ok g) (natp eb) (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields)))) (mv :bounds t))
         (hbase (fn2-ranges-hbase g fn2-ranges))
         ((unless (<= (+ hbase *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))) (mv :bounds t))
         ((mv code order) (fn2-run-layout-compare (fn2-ranges-schema g fn2-ranges) eb hbase ok os og
                                                  (fn2-ranges-qk g fn2-ranges) (fn2-ranges-qs g fn2-ranges) (fn2-ranges-qg g fn2-ranges)
                                                  fn2-fields fn2-pool))
         ((unless (eq code :ok)) (mv code t))
         ((when (eq order :gt)) (mv :ok t))
         (pf (fn2-ranges-pfield g fn2-ranges))
         ((when (equal pf *fn2-range-no-position*)) (mv :ok nil))
         ((unless (< pf *fn2-run-entry-rows*)) (mv :bounds t)))
     (mv :ok (< (fn2-ranges-plimit g fn2-ranges) (nfix (fn2-fields-value (+ eb pf) fn2-fields))))))
   ;; One bounded step of range read G: :entry (the delivered entry's rows
   ;; are at the range's OUT, read under its OK OS OG, until the next step),
   ;; :end, :more, :miss, or a refusal.
   (defun fn2-range-deliver (g fn2-ranges fn2-range-sources fn2-fields fn2-pool)
    (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-fields fn2-pool)
     :guard (and (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
     :guard-hints (("Goal" :in-theory (disable fn2-range-pick fn2-range-consume fn2-range-successor fn2-range-past)))))
    (b* (((unless (fn2-rg-ok g)) (mv :bounds fn2-ranges fn2-range-sources fn2-fields))
         (sid (fn2-ranges-schema g fn2-ranges)) (sbase (fn2-ranges-sbase g fn2-ranges)) (n (fn2-ranges-scount g fn2-ranges))
         ((unless (and (natp sbase) (natp n))) (mv :bounds fn2-ranges fn2-range-sources fn2-fields))
         ((mv code best) (fn2-range-pick n sbase sid nil fn2-range-sources fn2-fields fn2-pool))
         ((unless (eq code :ok)) (mv code fn2-ranges fn2-range-sources fn2-fields))
         ((unless (and (natp best) (< best (fn2-range-sources-rows fn2-range-sources))))
          (let ((fn2-ranges (fn2-ranges-set-phase g *fn2-range-phase-done* fn2-ranges))) (mv :end fn2-ranges fn2-range-sources fn2-fields)))
         (eb (+ (fn2-range-sources-rb best fn2-range-sources) *fn2-run-reader-entry*))
         (ok (fn2-range-sources-okind best fn2-range-sources)) (os (fn2-range-sources-oslot best fn2-range-sources))
         (og (fn2-range-sources-ogen best fn2-range-sources))
         ((mv code past) (fn2-range-past g eb ok os og fn2-ranges fn2-fields fn2-pool))
         ((unless (eq code :ok)) (mv code fn2-ranges fn2-range-sources fn2-fields))
         ((when past) (let ((fn2-ranges (fn2-ranges-set-phase g *fn2-range-phase-done* fn2-ranges))) (mv :end fn2-ranges fn2-range-sources fn2-fields)))
         ((mv code fn2-range-sources) (fn2-range-consume n sbase sid best fn2-range-sources fn2-fields fn2-pool))
         ((unless (eq code :ok)) (mv code fn2-ranges fn2-range-sources fn2-fields))
         ((mv code fn2-fields) (fn2-range-successor sid eb (fn2-ranges-qbase g fn2-ranges) fn2-fields))
         ((unless (eq code :ok)) (mv code fn2-ranges fn2-range-sources fn2-fields))
         (delivered (+ 1 (fn2-ranges-delivered g fn2-ranges)))
         ((unless (and (unsigned-byte-p 32 eb) (unsigned-byte-p 60 delivered)))
          (mv :bounds fn2-ranges fn2-range-sources fn2-fields))
         (fn2-ranges (fn2-ranges-put g (phase *fn2-range-phase-merge*) (out eb) (ok ok) (os os) (og og)
                                     (delivered delivered))))
     (mv :entry fn2-ranges fn2-range-sources fn2-fields)))
   (in-theory (disable fn2-range-deliver))
   (defun fn2-range-step (g budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                            fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
    (declare (xargs :stobjs (fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                             fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
     :guard (and (fn2-rga-guard) (natp budget))
     :guard-hints (("Goal" :in-theory (disable fn2-range-enumerate fn2-range-recheck fn2-range-advance-all fn2-range-deliver)))))
    (b* (((unless (fn2-rg-ok g)) (mv :bounds fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         (phase (fn2-ranges-phase g fn2-ranges))
         ((when (equal phase *fn2-range-phase-done*)) (mv :end fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         ((when (equal phase *fn2-range-phase-idle*)) (mv :state fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         ((unless (fn2-range-keys-ok (fn2-ranges-schema g fn2-ranges)))
          (mv :key-kind fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         ;; The sources moved (a seal, a merge): find them again.
         ((mv code fn2-ranges fn2-range-sources)
          (if (equal (fn2-run-version (fn2-ranges-schema g fn2-ranges) (fn2-run-installed-rows fn2-run-installed) fn2-run-installed)
                     (fn2-ranges-vrun g fn2-ranges))
              (mv :ok fn2-ranges fn2-range-sources)
            (fn2-range-enumerate g fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed)))
         ((unless (eq code :ok)) (mv code fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         ((unless (fn2-rg-ok g)) (mv :bounds fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         (n (fn2-ranges-scount g fn2-ranges))
         ((unless (natp n)) (mv :bounds fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         ((mv code fn2-range-sources) (fn2-range-recheck n g fn2-ranges fn2-range-sources fn2-overlays))
         ((unless (eq code :ok)) (mv code fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         ((mv code fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
          (fn2-range-advance-all n g budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
                                 fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
         ((unless (eq code :ok)) (mv code fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         ((mv code fn2-ranges fn2-range-sources fn2-fields) (fn2-range-deliver g fn2-ranges fn2-range-sources fn2-fields fn2-pool)))
     (mv code fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
   (in-theory (disable fn2-range-step))
   (assert-event (fn2-assert-compliant-p '(fn2-range-step fn2-range-keys-ok) (w state)))
   ;; The positioned seek's step, over range row G's regions.
   (defun fn2-seek-probe (k fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
    (declare (xargs :stobjs (fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
     :guard (and (fn2-seeks-wfp fn2-seeks) (fn2-ranges-wfp fn2-ranges) (fn2-range-sources-wfp fn2-range-sources)
                 (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields))
     :guard-hints (("Goal" :in-theory (disable fn2-range-start)))))
    (b* (((unless (and (natp k) (< k (fn2-seeks-rows fn2-seeks)))) (mv :bounds fn2-seeks fn2-ranges fn2-range-sources fn2-fields))
         (g (fn2-seeks-g k fn2-seeks))
         ((unless (fn2-rg-ok g)) (mv :bounds fn2-seeks fn2-ranges fn2-range-sources fn2-fields))
         (lo (fn2-seeks-lo k fn2-seeks)) (hi (fn2-seeks-hi k fn2-seeks))
         ((when (<= hi lo)) (let ((fn2-seeks (fn2-seeks-set-phase k *fn2-seek-phase-done* fn2-seeks)))
                              (mv :done fn2-seeks fn2-ranges fn2-range-sources fn2-fields)))
         (mid (floor (+ lo hi) 2))
         (sid (fn2-ranges-schema g fn2-ranges)) (nk (fn2-run-layout-keys sid))
         (qbase (fn2-ranges-qbase g fn2-ranges)) (hbase (fn2-ranges-hbase g fn2-ranges))
         ((unless (and (posp nk) (< (+ qbase nk -1) (fn2-fields-rows fn2-fields)) (< (+ hbase nk -1) (fn2-fields-rows fn2-fields))
                       (unsigned-byte-p 60 mid) (posp hi)))
          (mv :bounds fn2-seeks fn2-ranges fn2-range-sources fn2-fields))
         (fn2-fields (fn2-fields-set-value (+ qbase nk -1) mid fn2-fields))
         (fn2-fields (fn2-fields-set-value (+ hbase nk -1) (- hi 1) fn2-fields))
         ((mv code fn2-ranges fn2-range-sources)
          (fn2-range-start g sid qbase hbase (fn2-ranges-sbase g fn2-ranges) (fn2-ranges-smax g fn2-ranges)
                           (fn2-ranges-cbase g fn2-ranges) (fn2-ranges-rbase g fn2-ranges) *fn2-range-no-position* 0
                           (fn2-ranges-qk g fn2-ranges) (fn2-ranges-qs g fn2-ranges) (fn2-ranges-qg g fn2-ranges)
                           fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed))
         ((unless (eq code :ok)) (mv code fn2-seeks fn2-ranges fn2-range-sources fn2-fields))
         (probes (+ 1 (fn2-seeks-probes k fn2-seeks)))
         ((unless (unsigned-byte-p 32 probes)) (mv :bounds fn2-seeks fn2-ranges fn2-range-sources fn2-fields))
         (fn2-seeks (fn2-seeks-put k (phase *fn2-seek-phase-read*) (mid mid) (probes probes))))
     (mv :more fn2-seeks fn2-ranges fn2-range-sources fn2-fields)))
   ;; After a probe's range step answered CODE (the delivered entry still at
   ;; the range's OUT): narrow [lo, hi).
   (defun fn2-seek-narrow (k code fn2-seeks fn2-ranges fn2-fields)
    (declare (xargs :stobjs (fn2-seeks fn2-ranges fn2-fields)
     :guard (and (fn2-seeks-wfp fn2-seeks) (fn2-ranges-wfp fn2-ranges) (fn2-fields-wfp fn2-fields))))
    (b* (((unless (and (natp k) (< k (fn2-seeks-rows fn2-seeks)))) (mv :bounds fn2-seeks))
         (g (fn2-seeks-g k fn2-seeks))
         ((unless (fn2-rg-ok g)) (mv :bounds fn2-seeks))
         ((when (eq code :end))
          (let ((fn2-seeks (fn2-seeks-put k (phase *fn2-seek-phase-probe*) (hi (fn2-seeks-mid k fn2-seeks)))))
           (mv :more fn2-seeks)))
         ((unless (eq code :entry)) (mv code fn2-seeks))
         (out (fn2-ranges-out g fn2-ranges)) (nk (fn2-run-layout-keys (fn2-ranges-schema g fn2-ranges)))
         (pf (fn2-seeks-pfield k fn2-seeks))
         ((unless (and (posp nk) (< pf *fn2-run-entry-rows*) (< (+ out pf) (fn2-fields-rows fn2-fields))
                       (< (+ out nk -1) (fn2-fields-rows fn2-fields))))
          (mv :bounds fn2-seeks))
         (n (nfix (fn2-fields-value (+ out nk -1) fn2-fields)))
         (pos (nfix (fn2-fields-value (+ out pf) fn2-fields)))
         ((unless (unsigned-byte-p 60 (+ 1 n))) (mv :bounds fn2-seeks))
         (fn2-seeks (if (< (fn2-seeks-after k fn2-seeks) pos)
                              (fn2-seeks-put k (phase *fn2-seek-phase-probe*) (hi n))
                            (fn2-seeks-put k (phase *fn2-seek-phase-probe*) (lo (+ 1 n))))))
     (mv :more fn2-seeks)))
   ;; One bounded step: :more, :miss, :done (the answer is the row's LO), or a refusal.
   (defun fn2-seek-step (k budget fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                           fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
    (declare (xargs :stobjs (fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                             fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
     :guard (and (fn2-seeks-wfp fn2-seeks) (fn2-rga-guard) (natp budget))
     :guard-hints (("Goal" :in-theory (disable fn2-seek-probe fn2-seek-narrow fn2-range-step)))))
    (b* (((unless (and (natp k) (< k (fn2-seeks-rows fn2-seeks))))
          (mv :bounds fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
         (phase (fn2-seeks-phase k fn2-seeks)))
     (cond
      ((equal phase *fn2-seek-phase-done*) (mv :done fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields))
      ((equal phase *fn2-seek-phase-probe*)
       (mv-let (code fn2-seeks fn2-ranges fn2-range-sources fn2-fields)
         (fn2-seek-probe k fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed fn2-fields)
        (mv code fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
      ((equal phase *fn2-seek-phase-read*)
       (b* (((mv code fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
             (fn2-range-step (fn2-seeks-g k fn2-seeks) budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index
                             fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
            (fn2-seeks (case code
                         (:entry (fn2-seeks-set-phase k *fn2-seek-phase-entry* fn2-seeks))
                         (:end (fn2-seeks-set-phase k *fn2-seek-phase-end* fn2-seeks))
                         (otherwise fn2-seeks))))
        (mv (if (member-eq code '(:entry :end)) :more code) fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
      ((or (equal phase *fn2-seek-phase-entry*) (equal phase *fn2-seek-phase-end*))
       (mv-let (code fn2-seeks)
         (fn2-seek-narrow k (if (equal phase *fn2-seek-phase-entry*) :entry :end) fn2-seeks fn2-ranges fn2-fields)
        (mv code fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))
      (t (mv :state fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))))
   (in-theory (disable fn2-seek-step))
   (assert-event (fn2-assert-compliant-p '(fn2-seek-step) (w state)))
   (fn2-range-adapters)))

; ---------------------------------------------------------------------------
; Specification (lists; logic only). SOURCES are entry lists, oldest first:
; the runs in the order of their identifiers, then the overlay; an entry of
; a later source replaces one with an equal key. A read delivers the union
; in key order, from LO to HI (key value lists), up to the first entry whose
; field PIDX exceeds PLIMIT when PIDX is a field index.
(defun fn2-range-put-spec (key e acc)
 (declare (xargs :verify-guards nil))
 (cond ((atom acc) (list e))
       ((eq (fn2-run-key-order-spec key (car acc) e) :lt) (cons (car acc) (fn2-range-put-spec key e (cdr acc))))
       ((eq (fn2-run-key-order-spec key (car acc) e) :eq) (cons e (cdr acc)))
       (t (cons e acc))))
(defun fn2-range-puts-spec (key es acc)
 (declare (xargs :verify-guards nil))
 (if (atom es) acc (fn2-range-puts-spec key (cdr es) (fn2-range-put-spec key (car es) acc))))
(defun fn2-range-union-spec (key sources acc)
 (declare (xargs :verify-guards nil))
 (if (atom sources) acc (fn2-range-union-spec key (cdr sources) (fn2-range-puts-spec key (car sources) acc))))
(defun fn2-range-window-spec (key es lo hi pidx plimit)
 (declare (xargs :verify-guards nil))
 (cond ((atom es) nil)
       ((eq (fn2-run-key-order-spec key (car es) lo) :lt) (fn2-range-window-spec key (cdr es) lo hi pidx plimit))
       ((eq (fn2-run-key-order-spec key (car es) hi) :gt) nil)
       ((and (natp pidx) (< (nfix plimit) (nfix (nth pidx (car es))))) nil)
       (t (cons (car es) (fn2-range-window-spec key (cdr es) lo hi pidx plimit)))))
(defun fn2-range-spec (key sources lo hi pidx plimit)
 (declare (xargs :verify-guards nil))
 (fn2-range-window-spec key (fn2-range-union-spec key sources nil) lo hi pidx plimit))
; Inputs the adapter accepts: at most six sources of at most 48 sorted,
; well-formed entries each; a budget of at least one.
(defun fn2-range-listsp (layout key sources)
 (declare (xargs :verify-guards nil))
 (if (atom sources) (null sources)
  (and (true-listp (car sources)) (<= (len (car sources)) 48)
       (fn2-run-entries-layoutp layout (car sources)) (fn2-run-sorted-spec key (car sources))
       (fn2-range-listsp layout key (cdr sources)))))
(defun fn2-range-inputp (layout key sources budget)
 (declare (xargs :verify-guards nil))
 (and (fn2-layoutp layout) (consp sources) (<= (len sources) 6) (fn2-range-listsp layout key sources) (posp budget)))


; Positioned seek specification: over the union, among the entries whose
; first key fields equal PREFIX and whose last key field is below HI, the
; answer is one more than the last key field of the last entry whose field
; PIDX is at most P, or 0 when none is: reading from there delivers exactly
; the entries after position P. Positions grow with the key within a prefix.
(defun fn2-range-prefixp (prefix e)
 (declare (xargs :verify-guards nil))
 (or (atom prefix) (and (consp e) (equal (car prefix) (car e)) (fn2-range-prefixp (cdr prefix) (cdr e)))))
(defun fn2-range-seek-scan (es prefix nk p hi pidx acc)
 (declare (xargs :verify-guards nil))
 (cond ((atom es) acc)
       ((and (fn2-range-prefixp prefix (car es)) (< (nfix (nth (- nk 1) (car es))) hi) (<= (nfix (nth pidx (car es))) p))
        (fn2-range-seek-scan (cdr es) prefix nk p hi pidx (+ 1 (nfix (nth (- nk 1) (car es))))))
       (t (fn2-range-seek-scan (cdr es) prefix nk p hi pidx acc))))
(defun fn2-range-seek-spec (key sources prefix p hi pidx)
 (declare (xargs :verify-guards nil))
 (fn2-range-seek-scan (fn2-range-union-spec key sources nil) prefix (len key) p hi pidx 0))
(defun fn2-range-monotone-scan (es prefix pidx last)
 (declare (xargs :verify-guards nil))
 (cond ((atom es) t)
       ((fn2-range-prefixp prefix (car es))
        (and (< last (nfix (nth pidx (car es)))) (fn2-range-monotone-scan (cdr es) prefix pidx (nfix (nth pidx (car es))))))
       (t (fn2-range-monotone-scan (cdr es) prefix pidx last))))
; Positions strictly grow with the key within PREFIX in the union.
(defun fn2-range-monotonep (key sources prefix pidx)
 (declare (xargs :verify-guards nil))
 (fn2-range-monotone-scan (fn2-range-union-spec key sources nil) prefix pidx -1))

; ---------------------------------------------------------------------------
; Logic adapter. RUNS (oldest first) are built through the real build and
; installed as runs 1, 2, ...; OVERLAY is inserted through the real insert;
; the read runs with BUDGET per step. SEALAT, when a number, seals the
; overlay into a further run right after that many deliveries (the sources
; move under the read). Field plan above the run adapter's: lo at 1400, hi
; at 1500, sources' heads from 2000; owner (9 0 1), queries (10 0 1).
(defconst *fn2-rga-stobjs*
 '(fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
   fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
(defmacro fn2-rga-defun (name args &rest r)
 (let* ((measure (and (eq (car r) :measure) (cadr r))) (body (if measure (caddr r) (car r))))
  `(defun ,name ,(append args *fn2-rga-stobjs*)
    (declare (xargs :stobjs ,*fn2-rga-stobjs* :verify-guards nil ,@(and measure `(:measure ,measure))))
    ,body)))
(defmacro fn2-rga-mv (&rest values) `(mv ,@values ,@*fn2-rga-stobjs*))
(defmacro fn2-rga-call (name &rest args) `(,name ,@args ,@*fn2-rga-stobjs*))
(defmacro fn2-rga-local (name &rest args) `(fn2-run-with-local ,*fn2-rga-stobjs* (,name ,@args ,@*fn2-rga-stobjs*)))
(defconst *fn2-rga-lo* 1400)
(defconst *fn2-rga-hi* 1500)
(defconst *fn2-rga-heads* 2000)
(defconst *fn2-rga-smax* 8)

(defmacro fn2-range-adapters ()
 '(progn
   (fn2-rga-defun fn2-rga-setup ()
    (b* ((fn2-ranges (fn2-ranges-init 1 fn2-ranges))
         (fn2-range-sources (fn2-range-sources-init *fn2-rga-smax* fn2-range-sources))
         (fn2-overlays (fn2-overlays-init 1 fn2-overlays))
         (fn2-overlay-index (fn2-overlay-index-init 256 fn2-overlay-index))
         (fn2-run-installed (fn2-run-installed-init 16 fn2-run-installed))
         (fn2-run-builds (fn2-run-builds-init 1 fn2-run-builds))
         (fn2-run-cursors (fn2-run-cursors-init *fn2-rga-smax* fn2-run-cursors))
         (fn2-run-paths (fn2-run-paths-init (* *fn2-rga-smax* *fn2-run-max-levels*) fn2-run-paths))
         (fn2-run-cache (fn2-run-cache-init 4096 fn2-run-cache))
         (fn2-run-writers (fn2-run-writers-init *fn2-run-max-levels* fn2-run-writers))
         (fn2-run-restarts (fn2-run-restarts-init (* *fn2-run-max-levels* *fn2-run-restart-capacity*) fn2-run-restarts))
         (fn2-fields (fn2-fields-init (+ *fn2-rga-heads* (* *fn2-rga-smax* *fn2-run-reader-fields*)) fn2-fields))
         (fn2-pool (fn2-pool-init '((300 . 65536)) 1 100 fn2-pool))
         (fn2-fc (fn2-fc-init 1 fn2-fc))
         (fn2-fc-context (fn2-fc-context-init 1 fn2-fc-context))
         (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
         (fn2-digests (fn2-digests-init 150 fn2-digests)))
     (fn2-rga-mv :ok)))
   ;; Build ENTRIES into run K+1 (row K; pages from unit 1+1000K) and install it.
   (fn2-rga-defun fn2-rga-build (sid layout entries k)
    (if (atom entries) (fn2-rga-mv :ok)
     (b* (((mv & hslot hgen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
          ((mv & src sgen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
          ((mv code fn2-run-builds fn2-run-writers fn2-pool)
           (fn2-run-build-start 0 sid (+ 1 k) 0 0 136 hslot hgen 0 2048 1 1 9 0 1 fn2-run-builds fn2-run-writers fn2-pool))
          ((unless (eq code :ok)) (fn2-rga-mv (list :start code)))
          ((mv code pages fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts
               fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
           (fn2-run-run-loop 1000000 layout entries src sgen 0 (+ 1 (* 1000 k)) nil fn2-run-builds fn2-run-cursors fn2-run-paths
                             fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
          ((unless (eq code :root)) (fn2-rga-mv (list :build code)))
          (fn2-run-cache (fn2-run-run-cache-all pages fn2-run-cache))
          (root (car pages))
          ((mv code fn2-run-installed)
           (fn2-run-install k sid (+ 1 k) (nth 0 root) (nth 3 root) (nth 4 root) (nth 1 root) (nth 2 root) (len entries) 9 0 1 fn2-run-installed)))
      (fn2-rga-mv code))))
   (fn2-rga-defun fn2-rga-builds (sid layout runs k)
    (if (atom runs) (fn2-rga-mv :ok k)
     (b* (((mv code fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
               fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
           (fn2-rga-call fn2-rga-build sid layout (car runs) k))
          ((unless (eq code :ok)) (fn2-rga-mv code k)))
      (fn2-rga-call fn2-rga-builds sid layout (cdr runs) (+ 1 k)))))
   (fn2-rga-defun fn2-rga-overlay (sid layout entries)
    (b* (((mv & aslot agen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
         ((mv & src sgen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
         ((mv code fn2-overlays fn2-pool) (fn2-ov-start 0 sid aslot agen 0 256 9 0 1 0 fn2-overlays fn2-overlay-index fn2-pool))
         ((unless (eq code :ok)) (fn2-rga-mv (list :overlay code)))
         ((mv codes fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
          (fn2-ov-adapter-load sid layout entries src sgen 0 fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
     (fn2-rga-mv (if (subsetp-eq codes '(:ok)) :ok (list :insert codes)))))
   ;; Seal overlay 0 into run K+1: its entries are read in order and built.
   (fn2-rga-defun fn2-rga-seal (sid layout k)
    (b* (((mv code fn2-overlays) (fn2-ov-freeze 0 fn2-overlays))
         ((unless (eq code :ok)) (fn2-rga-mv (list :freeze code)))
         ((mv entries fn2-fields)
          (fn2-ov-adapter-read (fn2-overlays-count 0 fn2-overlays) 0 layout fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
         ((mv code fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
              fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
          (fn2-rga-call fn2-rga-build sid layout entries k))
         ((unless (eq code :ok)) (fn2-rga-mv code))
         ((mv code fn2-overlays) (fn2-ov-retire 0 fn2-overlays)))
     (fn2-rga-mv code)))
   ;; Step until :end, unloading each delivered entry.
   (fn2-rga-defun fn2-rga-drive (fuel sid layout budget sealat k) :measure (nfix fuel)
    (if (zp fuel) (fn2-rga-mv (list :fuel))
     (b* (((mv code fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
           (fn2-range-step 0 budget fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                           fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
      (case code
       (:more (fn2-rga-call fn2-rga-drive (- fuel 1) sid layout budget sealat k))
       (:end (fn2-rga-mv nil))
       (:entry
        (b* ((e (fn2-run-unload-values layout (fn2-ranges-out 0 fn2-ranges) fn2-fields fn2-pool))
             ((mv sealed fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
                  fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
              (if (equal sealat (fn2-ranges-delivered 0 fn2-ranges)) (fn2-rga-call fn2-rga-seal sid layout k) (fn2-rga-mv :ok)))
             ((unless (eq sealed :ok)) (fn2-rga-mv (list (list :seal sealed))))
             ((mv rest fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
                  fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
              (fn2-rga-call fn2-rga-drive (- fuel 1) sid layout budget sealat k)))
         (fn2-rga-mv (cons e rest))))
       (otherwise (fn2-rga-mv (list code)))))))
   (fn2-rga-defun fn2-rga-run (sid layout sources lo hi pidx plimit budget sealat)
    (b* (((mv & fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
              fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
          (fn2-rga-call fn2-rga-setup))
         (runs (butlast sources 1)) (overlay (car (last sources)))
         ((mv code k fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
              fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
          (fn2-rga-call fn2-rga-builds sid layout runs 0))
         ((unless (eq code :ok)) (fn2-rga-mv (list code)))
         ((mv code fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
              fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
          (fn2-rga-call fn2-rga-overlay sid layout overlay))
         ((unless (eq code :ok)) (fn2-rga-mv (list code)))
         (key-layout (take (fn2-run-layout-keys sid) layout))
         ((mv & qslot qgen fn2-pool) (fn2-pool-reserve 0 10 0 1 fn2-pool))
         ((mv & off fn2-fields fn2-pool) (fn2-run-load-values key-layout lo *fn2-rga-lo* qslot qgen 0 10 0 1 fn2-fields fn2-pool))
         ((mv & & fn2-fields fn2-pool) (fn2-run-load-values key-layout hi *fn2-rga-hi* qslot qgen off 10 0 1 fn2-fields fn2-pool))
         ((mv code fn2-ranges fn2-range-sources)
          (fn2-range-start 0 sid *fn2-rga-lo* *fn2-rga-hi* 0 *fn2-rga-smax* 0 *fn2-rga-heads*
                           (if (natp pidx) pidx *fn2-range-no-position*) (nfix plimit) 10 0 1
                           fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed))
         ((unless (eq code :ok)) (fn2-rga-mv (list (list :start code)))))
     (fn2-rga-call fn2-rga-drive 100000 sid layout budget sealat k)))
   (defun fn2-range-image (sid layout sources lo hi pidx plimit budget sealat)
    (declare (xargs :verify-guards nil))
    (fn2-rga-local fn2-rga-run sid layout sources lo hi pidx plimit budget sealat))
   ;; Keystone (UC 2.4; INBOX 4.1): a range read through the real steps over
   ;; an overlay and runs, the overlay sealed into a run in the middle of the
   ;; read, delivers exactly the specified window of the union.
   (defthm-owed fn2-range-read-exact (sources lo hi pidx plimit budget sealat)
    (implies (and (fn2-range-inputp *fn2-overview-entry* '((group (:id group)) (number (:id group-number))) sources budget)
                  (true-listp lo) (equal (len lo) 2) (true-listp hi) (equal (len hi) 2))
             (equal (fn2-range-image 3 *fn2-overview-entry* sources lo hi pidx plimit budget sealat)
                    (fn2-range-spec '((group (:id group)) (number (:id group-number))) sources lo hi pidx plimit)))
    :teeth (fn2-range-read-exact-positive fn2-range-read-exact-negative)
    :schema :g1 :claim :representation
    :doc "A range read over a schema's overlay and runs (its key's successor as the resume point, its sources found again when they move) delivers, in key order, the newest entry of each key between lo and hi, up to the position limit, whatever the step budget and whenever the overlay is sealed.")
   ;; Positioned seek adapter: the range image's sources; range 0 holds the
   ;; prefix (with a zero last field); seek row 0 bisects [0, HI).
   (defun fn2-rgs-drive (fuel budget fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
    (declare (xargs :stobjs (fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests) :verify-guards nil :measure (nfix fuel)))
    (if (zp fuel) (mv :fuel fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
     (mv-let (code fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-seek-step 0 budget fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed
                      fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
      (if (eq code :more)
          (fn2-rgs-drive (- fuel 1) budget fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
        (mv code fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)))))
   (defun fn2-rgs-run (sid layout sources prefix p hi pidx budget fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
    (declare (xargs :stobjs (fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests) :verify-guards nil))
    (b* ((fn2-seeks (fn2-seeks-init 1 fn2-seeks))
         ((mv & fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests) (fn2-rga-call fn2-rga-setup))
         ((mv code & fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests) (fn2-rga-call fn2-rga-builds sid layout (butlast sources 1) 0))
         ((unless (eq code :ok)) (mv (list code) fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         ((mv code fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests) (fn2-rga-call fn2-rga-overlay sid layout (car (last sources))))
         ((unless (eq code :ok)) (mv (list code) fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         (key-layout (take (fn2-run-layout-keys sid) layout))
         ((mv & qslot qgen fn2-pool) (fn2-pool-reserve 0 10 0 1 fn2-pool))
         ((mv & off fn2-fields fn2-pool) (fn2-run-load-values key-layout (append prefix (list 0)) *fn2-rga-lo* qslot qgen 0 10 0 1 fn2-fields fn2-pool))
         ((mv & & fn2-fields fn2-pool) (fn2-run-load-values key-layout (append prefix (list 0)) *fn2-rga-hi* qslot qgen off 10 0 1 fn2-fields fn2-pool))
         ((mv code fn2-ranges fn2-range-sources)
          (fn2-range-start 0 sid *fn2-rga-lo* *fn2-rga-hi* 0 *fn2-rga-smax* 0 *fn2-rga-heads* *fn2-range-no-position* 0 10 0 1
                           fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed))
         ((unless (eq code :ok)) (mv (list :start code) fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         ((mv code fn2-seeks) (fn2-seek-start 0 0 0 hi p pidx fn2-seeks))
         ((unless (eq code :ok)) (mv (list :seek code) fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         ((mv code fn2-seeks fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths fn2-fields)
          (fn2-rgs-drive 10000 budget fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
     (mv (if (eq code :done) (list (fn2-seeks-lo 0 fn2-seeks) (fn2-seeks-probes 0 fn2-seeks)) (list code))
         fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
   (defun fn2-range-seek-image (sid layout sources prefix p hi pidx budget)
    (declare (xargs :verify-guards nil))
    (fn2-run-with-local (fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (fn2-rgs-run sid layout sources prefix p hi pidx budget fn2-seeks fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
   ;; Keystone (INBOX 4.1, Seek(stream, after = p)).
   (defthm-owed fn2-range-seek-position (sources prefix p hi budget)
    (implies (and (fn2-range-inputp *fn2-overview-entry* '((group (:id group)) (number (:id group-number))) sources budget)
                  (true-listp prefix) (equal (len prefix) 1) (natp p) (posp hi) (unsigned-byte-p 59 hi)
                  (fn2-range-monotonep '((group (:id group)) (number (:id group-number))) sources prefix 3))
             (equal (car (fn2-range-seek-image 3 *fn2-overview-entry* sources prefix p hi 3 budget))
                    (fn2-range-seek-spec '((group (:id group)) (number (:id group-number))) sources prefix p hi 3)))
    :teeth (fn2-range-seek-position-positive fn2-range-seek-position-negative)
    :schema :g1 :claim :representation
    :doc "Within one stream (a group's overview, positions growing with numbers), the positioned seek over the overlay and runs answers the number from which a read delivers exactly the entries after commit position p: one past the last entry at or before p.")
   ))
