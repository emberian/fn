; Layer C1c unit: the sealer's engine half (books/sealer.lisp) on real runs.
; Overlays of one schema are loaded through the real insert, published
; (frozen, SEQ in batch order) and sealed by driving the real fn2-seal-step
; until it is idle; then every query is looked up through the real run
; cursor in the installed runs, newest run first. The keystones
; fn2-sealer-run-equals-overlay and fn2-manifest-replacement-atomic, their
; adapters and teeth.
; Run: sh tools/certify.sh tests/sealer-unit.lisp
(in-package "ACL2")
(include-book "runs-assembly")
(include-book "../books/sealer")

(defconst *fn2-su-stobjs*
 '(fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
   fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources))
;; A b* binding (fn2-su-bind (v ...) call) binds V ... and every stobj.
(defun fn2-su-expand (x)
 (declare (xargs :verify-guards nil))
 (cond ((atom x) x)
       ((and (eq (car x) 'fn2-su-bind) (consp (cdr x)) (consp (cddr x)))
        (list (cons 'mv (append (cadr x) *fn2-su-stobjs*)) (fn2-su-expand (caddr x))))
       (t (cons (fn2-su-expand (car x)) (fn2-su-expand (cdr x))))))
(defmacro fn2-su-defun (name args &rest r)
 (let* ((measure (and (eq (car r) :measure) (cadr r))) (body (if measure (caddr r) (car r))))
  `(defun ,name ,(append args *fn2-su-stobjs*)
    (declare (xargs :stobjs ,*fn2-su-stobjs* :verify-guards nil ,@(and measure `(:measure ,measure))))
    ,(fn2-su-expand body))))
(defmacro fn2-su-mv (&rest values) `(mv ,@values ,@*fn2-su-stobjs*))
(defmacro fn2-su-call (name &rest args) `(,name ,@args ,@*fn2-su-stobjs*))

; Field plan: the sealer's rows from 1500 (its merge's query at 2780 and
; sources' readers from 2860, C5); an entry being loaded at 3700, the
; overlay's decode scratch at 3800; the run adapter's reader at 1200 and
; query at 1310. Writer rows 0-6 the sealer's; checker row 0, digest rows
; 0-135. Owner (9 0 1); the query's (10 0 1).
(defconst *fn2-su-fbase* 1500)
(defconst *fn2-su-e* 3700)
(defconst *fn2-su-eb* 3800)
(defconst *fn2-su-icap* 64)
(fn2-su-defun fn2-su-setup (rows pfill)
 (b* ((fn2-seals (fn2-seals-init 1 fn2-seals))
      (fn2-overlays (fn2-overlays-init rows fn2-overlays))
      (fn2-overlay-index (fn2-overlay-index-init (* rows *fn2-su-icap*) fn2-overlay-index))
      (fn2-run-installed (fn2-run-installed-init 16 fn2-run-installed))
      (fn2-run-builds (fn2-run-builds-init 1 fn2-run-builds))
      (fn2-run-writers (fn2-run-writers-init *fn2-seal-writer-rows* fn2-run-writers))
      (fn2-run-restarts (fn2-run-restarts-init (* *fn2-seal-writer-rows* *fn2-run-restart-capacity*) fn2-run-restarts))
      (fn2-run-cache (fn2-run-cache-init 1024 fn2-run-cache))
      (fn2-ribbon-builds (fn2-ribbon-builds-init 1 fn2-ribbon-builds))
      (fn2-ribbon-band (fn2-ribbon-band-init (fn2-ribbon-slots *fn2-su-icap*) fn2-ribbon-band))
      (fn2-fields (fn2-fields-init 3900 fn2-fields))
      (fn2-pool (fn2-pool-init '((300 . 65536)) 1 100 fn2-pool))
      (fn2-fc (fn2-fc-init 1 fn2-fc))
      (fn2-fc-context (fn2-fc-context-init 1 fn2-fc-context))
      (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
      (fn2-digests (fn2-digests-init 150 fn2-digests))
      (fn2-run-cursors (fn2-run-cursors-init 9 fn2-run-cursors))
      (fn2-run-paths (fn2-run-paths-init (* 9 *fn2-run-max-levels*) fn2-run-paths))
      (fn2-ranges (fn2-ranges-init 1 fn2-ranges))
      (fn2-range-sources (fn2-range-sources-init 8 fn2-range-sources))
      ((mv code fn2-seals) (fn2-seal-init 0 *fn2-su-fbase* 0 pfill 9 0 1 fn2-seals))
      ((unless (eq code :ok)) (fn2-su-mv code))
      ;; the merge (C5): range row 0, sources 0-7 through cursors 1-8
      ((mv code fn2-seals) (fn2-seal-merge-rows 0 0 1 (+ *fn2-su-fbase* *fn2-seal-field-rows*)
                                                (+ *fn2-su-fbase* *fn2-seal-field-rows* *fn2-run-entry-rows*) fn2-seals)))
  (fn2-su-mv code)))
; Load overlay O of SID with ENTRIES (inserted in order), SEQ, then publish
; it (frozen) unless PRIVATE.
(fn2-su-defun fn2-su-load-entries (layout entries o src sgen off)
 (if (atom entries) (fn2-su-mv :ok)
  (b* (((mv code off fn2-fields fn2-pool) (fn2-run-load-values layout (car entries) *fn2-su-e* src sgen off 9 0 1 fn2-fields fn2-pool))
       ((unless (eq code :ok)) (fn2-su-mv (list :load code)))
       ((mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
        (fn2-ov-insert o *fn2-su-e* *fn2-su-eb* fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
       ((unless (eq code :ok)) (fn2-su-mv (list :insert code))))
   (fn2-su-call fn2-su-load-entries layout (cdr entries) o src sgen off))))
(fn2-su-defun fn2-su-load (sid layout batches o seqs private)
 (if (atom batches) (fn2-su-mv :ok)
  (b* (((mv & aslot agen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
       ((mv & src sgen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
       ((mv code fn2-overlays fn2-pool)
        (fn2-ov-start o sid aslot agen (* o *fn2-su-icap*) *fn2-su-icap* 9 0 1 0 fn2-overlays fn2-overlay-index fn2-pool))
       ((unless (eq code :ok)) (fn2-su-mv (list :start code)))
       (fn2-su-bind (code) (fn2-su-call fn2-su-load-entries layout (car batches) o src sgen 0))
       ((unless (eq code :ok)) (fn2-su-mv code))
       ((mv & fn2-pool) (fn2-pool-release src sgen 9 0 1 fn2-pool))
       (fn2-overlays (fn2-overlays-set-seq o (car seqs) fn2-overlays))
       ((mv code fn2-overlays)
        (if (and (atom (cdr batches)) private)
            (fn2-ov-advance o *fn2-overlay-phase-active* *fn2-overlay-phase-private* fn2-overlays)
          (fn2-ov-freeze o fn2-overlays)))
       ((unless (eq code :ok)) (fn2-su-mv (list :freeze code))))
   (fn2-su-call fn2-su-load sid layout (cdr batches) (+ 1 o) (cdr seqs) private))))
; Drive the sealer until it is idle or has installed LIMIT runs; (code
; done-count).
(fn2-su-defun fn2-su-drive (fuel limit done) :measure (nfix fuel)
 (if (or (zp fuel) (and (natp limit) (<= limit done))) (fn2-su-mv (if (zp fuel) :fuel :limit) done)
  (b* (((mv code fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts
            fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests
            fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)
        (fn2-seal-step 4096 fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
                       fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                       fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)))
   (case code
    (:idle (fn2-su-mv :idle done))
    ((:more :retired) (fn2-su-call fn2-su-drive (- fuel 1) limit done))
    (:done (fn2-su-call fn2-su-drive (- fuel 1) limit (+ 1 done)))
    (otherwise (fn2-su-mv code done))))))
; Look Q up in SID's live runs, newest first, below BOUND: (:found entry)
; from the first run holding its key, else (:absent).
(fn2-su-defun fn2-su-lookup (fuel sid layout bound) :measure (nfix fuel)
 (b* ((rows (fn2-run-installed-rows fn2-run-installed))
      (r (fn2-succ-newest-run rows 0 sid bound rows fn2-run-installed))
      ((when (or (zp fuel) (not (< r rows)))) (fn2-su-mv (list :absent)))
      ((mv & fn2-run-cursors)
       (fn2-run-cursor-start 0 sid (fn2-run-installed-top r fn2-run-installed) (fn2-run-installed-slot r fn2-run-installed)
                             (fn2-run-installed-gen r fn2-run-installed) (fn2-run-installed-unit r fn2-run-installed)
                             (fn2-run-installed-counter r fn2-run-installed) *fn2-run-run-reader* 9 0 1 fn2-run-cursors))
      ((mv code fn2-run-cursors fn2-run-paths fn2-fields) (fn2-run-run-steps 100000 fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
  (if (eq code :found)
      (fn2-su-mv (list :found (fn2-run-unload-values layout (+ *fn2-run-run-reader* *fn2-run-reader-entry*) fn2-fields fn2-pool)))
    (if (eq code :absent)
        (fn2-su-call fn2-su-lookup (- fuel 1) sid layout (fn2-run-installed-run r fn2-run-installed))
      (fn2-su-mv (list code))))))
(fn2-su-defun fn2-su-queries (sid layout queries)
 (if (atom queries) (fn2-su-mv nil)
  (b* (((mv & qslot qgen fn2-pool) (fn2-pool-reserve 0 10 0 1 fn2-pool))
       ((mv & & fn2-fields fn2-pool) (fn2-run-load-values layout (car queries) *fn2-run-run-query* qslot qgen 0 10 0 1 fn2-fields fn2-pool))
       (fn2-su-bind (answer) (fn2-su-call fn2-su-lookup 20 sid layout *fn2-u60-max*))
       ((mv & fn2-pool) (fn2-pool-release qslot qgen 10 0 1 fn2-pool))
       (fn2-su-bind (rest) (fn2-su-call fn2-su-queries sid layout (cdr queries))))
   (fn2-su-mv (cons answer rest)))))
; The live runs' (schema run entries filter) and the overlay phases.
(fn2-su-defun fn2-su-installed (r k) :measure (nfix k)
 (if (or (zp k) (not (natp r)) (<= (fn2-run-installed-rows fn2-run-installed) r)) (fn2-su-mv nil)
  (b* ((live (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*))
       (row (list (fn2-run-installed-schema r fn2-run-installed) (fn2-run-installed-run r fn2-run-installed)
                  (fn2-run-installed-entries r fn2-run-installed) (fn2-run-installed-filter r fn2-run-installed)))
       (fn2-su-bind (rest) (fn2-su-call fn2-su-installed (+ 1 r) (- k 1))))
   (fn2-su-mv (if live (cons row rest) rest)))))
(fn2-su-defun fn2-su-phases (o k) :measure (nfix k)
 (if (or (zp k) (not (natp o)) (<= (fn2-overlays-rows fn2-overlays) o)) (fn2-su-mv nil)
  (b* ((p (fn2-overlays-phase o fn2-overlays)) (fn2-su-bind (rest) (fn2-su-call fn2-su-phases (+ 1 o) (- k 1))))
   (fn2-su-mv (cons p rest)))))
; The image: setup, load, seal (at most LIMIT runs), then (drive-code done
; answers installed phases).
(fn2-su-defun fn2-su-run (sid layout batches seqs private limit pfill queries)
 (b* ((fn2-su-bind (code) (fn2-su-call fn2-su-setup (+ 1 (len batches)) pfill))
      ((unless (eq code :ok)) (fn2-su-mv (list :setup code)))
      (fn2-su-bind (code) (fn2-su-call fn2-su-load sid layout batches 0 seqs private))
      ((unless (eq code :ok)) (fn2-su-mv (list :load code)))
      (fn2-su-bind (code done) (fn2-su-call fn2-su-drive 1000000 limit 0))
      (fn2-su-bind (answers) (fn2-su-call fn2-su-queries sid layout queries))
      (fn2-su-bind (installed) (fn2-su-call fn2-su-installed 0 16))
      (fn2-su-bind (phases) (fn2-su-call fn2-su-phases 0 (+ 1 (len batches)))))
  (fn2-su-mv (list code done answers installed phases))))
(defun fn2-sealer-image (sid layout batches seqs private limit pfill queries)
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                      fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
  (mv-let (r fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
             fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
    (fn2-su-run sid layout batches seqs private limit pfill queries fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed
                fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
   (mv r fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
       fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources))))

; ---------------------------------------------------------------------------
; Specification: the newest batch (the last in SEQ order) holding Q's key.
(defun fn2-su-find (key entries q)
 (declare (xargs :verify-guards nil))
 (cond ((atom entries) nil)
       ((eq (fn2-run-key-order-spec key (car entries) q) :eq) (list (car entries)))
       (t (fn2-su-find key (cdr entries) q))))
(defun fn2-sealer-lookup-spec (key batches q)
 (declare (xargs :verify-guards nil))
 (if (atom batches) (list :absent)
  (let ((later (fn2-sealer-lookup-spec key (cdr batches) q)) (here (fn2-su-find key (car batches) q)))
   (if (eq (car later) :found) later (if here (list :found (car here)) later)))))
(defun fn2-sealer-spec (key batches queries)
 (declare (xargs :verify-guards nil))
 (if (atom queries) nil (cons (fn2-sealer-lookup-spec key batches (car queries)) (fn2-sealer-spec key batches (cdr queries)))))
(defun fn2-su-seqs (n i) (declare (xargs :verify-guards nil :measure (nfix n))) (if (zp n) nil (cons i (fn2-su-seqs (- n 1) (+ 1 i)))))
; The identity summary (C §4a, schema 13): the schema whose runs carry a filter.
(defconst *fn2-su-summary* '((namespace (:id namespace)) (name (:octets 250)) (selected (:id candidate)) (resolution (:id event))
                             (candidates :u60) (evidence :u60) (history :u60) (gaps :u60)))
(defconst *fn2-su-summary-key* '((namespace (:id namespace)) (name (:octets 250))))
; Inputs: at most four batches, each at most 48 distinct well-formed keys.
(defun fn2-sealer-inputp (layout key batches)
 (declare (xargs :verify-guards nil))
 (or (atom batches)
     (and (consp (car batches)) (fn2-ov-inputp layout key (car batches)) (<= (len (car batches)) 48)
          (fn2-sealer-inputp layout key (cdr batches)))))

(defconst *fn2-su-groups* '((name (:octets 250)) (group (:id group))))
(defconst *fn2-su-groups-key* '((name (:octets 250))))
(defun fn2-su-name (j) (declare (xargs :verify-guards nil)) (list 97 46 (+ 97 (floor j 26)) (+ 97 (mod j 26))))
(defun fn2-su-batch (from n v)
 (declare (xargs :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons (list (fn2-su-name from) (+ v from)) (fn2-su-batch (+ 1 from) (- n 1) v))))
; Three batches over names 0-29: names 0-19 (group = 100 + j), 10-29 (200 +
; j), 5-14 (300 + j); the newest row of each name is the answer.
(defconst *fn2-su-batches* (list (fn2-su-batch 0 20 100) (fn2-su-batch 10 20 200) (fn2-su-batch 5 10 300)))
(defconst *fn2-su-queries*
 (list (list (fn2-su-name 0) 0) (list (fn2-su-name 7) 0) (list (fn2-su-name 12) 0) (list (fn2-su-name 17) 0)
       (list (fn2-su-name 25) 0) (list (fn2-su-name 29) 0) (list (fn2-su-name 30) 0) (list nil 0)))

(defthm-owed fn2-sealer-run-equals-overlay (batches queries pfill)
 (implies (and (fn2-sealer-inputp *fn2-su-groups* *fn2-su-groups-key* batches) (<= (len batches) 4)
               (natp pfill) (<= 400 pfill) (<= pfill *fn2-run-page-size*))
          (equal (caddr (fn2-sealer-image 8 *fn2-su-groups* batches (fn2-su-seqs (len batches) 1) nil nil pfill queries))
                 (fn2-sealer-spec *fn2-su-groups-key* batches queries)))
 :teeth (fn2-sealer-run-equals-overlay-positive fn2-sealer-run-equals-overlay-negative)
 :schema :invariant
 :doc "The sealer seals published overlays into runs in SEQ order through the real build; every lookup through the runs, newest first, answers as the overlays did (the newest batch holding the key), at any page pfill that holds two entries.")
(defun fn2-sealer-run-equals-overlay-positive ()
 (declare (xargs :verify-guards nil))
 (let ((spec (fn2-sealer-spec *fn2-su-groups-key* *fn2-su-batches* *fn2-su-queries*)))
  (and (fn2-sealer-inputp *fn2-su-groups* *fn2-su-groups-key* *fn2-su-batches*)
       (equal (caddr (fn2-sealer-image 8 *fn2-su-groups* *fn2-su-batches* '(1 2 3) nil nil 400 *fn2-su-queries*)) spec)
       (equal (caddr (fn2-sealer-image 8 *fn2-su-groups* *fn2-su-batches* '(1 2 3) nil nil *fn2-run-page-size* *fn2-su-queries*)) spec)
       ; non-vacuous: answers from each batch and an absent one
       (equal (strip-cars spec) '(:found :found :found :found :found :found :absent :absent)))))
; Teeth: (1) a sealer that stops before the last overlay answers name 7 from
; batch 1 where batch 3 is newest; (2) run order must follow SEQ: batches
; published with SEQs against their order read back the older rows.
(defun fn2-sealer-run-equals-overlay-negative ()
 (declare (xargs :verify-guards nil))
 (let ((spec (fn2-sealer-spec *fn2-su-groups-key* *fn2-su-batches* *fn2-su-queries*)))
  (and (not (equal (caddr (fn2-sealer-image 8 *fn2-su-groups* *fn2-su-batches* '(1 2 3) nil 2 400 *fn2-su-queries*)) spec))
       (not (equal (caddr (fn2-sealer-image 8 *fn2-su-groups* *fn2-su-batches* '(3 2 1) nil nil 400 *fn2-su-queries*)) spec)))))
(fn2-assert-owed-teeth fn2-sealer-run-equals-overlay)

;; The engine half of the run replacement: at every cut of the sealer's
;; steps, the resident view holds the runs before the seal or the runs after
;; it, never a third set; the overlay is published until the cut that
;; installs its run and free from that cut on, so a reader sees each fact in
;; exactly one place. (The device half adds B5's recovery over the
;; run-replacement member: the recovered manifest is the old or the new.)
(fn2-su-defun fn2-su-cuts (fuel prev acc) :measure (nfix fuel)
 (if (zp fuel) (fn2-su-mv (reverse acc))
  (b* (((mv code fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts
            fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests
            fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)
        (fn2-seal-step 4096 fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
                       fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                       fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths))
       (fn2-su-bind (installed) (fn2-su-call fn2-su-installed 0 16))
       (fn2-su-bind (phases) (fn2-su-call fn2-su-phases 0 1))
       (view (list installed phases))
       (acc (if (equal view prev) acc (cons view acc))))
   (if (member-eq code '(:more :retired :done)) (fn2-su-call fn2-su-cuts (- fuel 1) view acc) (fn2-su-mv (reverse acc))))))
(fn2-su-defun fn2-su-cut-run (sid layout batch pfill)
 (b* ((fn2-su-bind (code) (fn2-su-call fn2-su-setup 2 pfill))
      ((unless (eq code :ok)) (fn2-su-mv (list :setup code)))
      (fn2-su-bind (code) (fn2-su-call fn2-su-load sid layout (list batch) 0 '(1) nil))
      ((unless (eq code :ok)) (fn2-su-mv (list :load code)))
      (fn2-su-bind (installed) (fn2-su-call fn2-su-installed 0 16))
      (fn2-su-bind (phases) (fn2-su-call fn2-su-phases 0 1))
      (fn2-su-bind (views) (fn2-su-call fn2-su-cuts 100000 (list installed phases) (list (list installed phases)))))
  (fn2-su-mv views)))
(defun fn2-sealer-cut-views (sid layout batch pfill)
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                      fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
  (mv-let (r fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
             fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
    (fn2-su-cut-run sid layout batch pfill fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed
                    fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                    fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
   (mv r fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
       fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources))))
; The views of one seal of a nonempty batch: before (no run, the overlay
; frozen) and after (one run of its entries, the overlay free), nothing else.
(defun fn2-sealer-cuts-ok (sid batch views)
 (declare (xargs :verify-guards nil))
 (let ((filter (if (equal sid *fn2-seal-identity*) 1 0)))
  (equal views (list (list nil (list *fn2-overlay-phase-frozen*))
                     (list (list (list sid 1 (len batch) filter)) (list *fn2-overlay-phase-free*))))))
(defthm-owed fn2-manifest-replacement-atomic (sid batch pfill)
 (implies (and (member sid '(13 8)) (consp batch) (<= (len batch) 48) (natp pfill) (<= 400 pfill) (<= pfill *fn2-run-page-size*)
               (fn2-ov-inputp (if (equal sid 13) *fn2-su-summary* *fn2-su-groups*)
                              (if (equal sid 13) *fn2-su-summary-key* *fn2-su-groups-key*) batch))
          (fn2-sealer-cuts-ok sid batch (fn2-sealer-cut-views sid (if (equal sid 13) *fn2-su-summary* *fn2-su-groups*) batch pfill)))
 :teeth (fn2-manifest-replacement-atomic-positive fn2-manifest-replacement-atomic-negative)
 :schema :invariant
 :doc "Engine half of the run replacement: at every cut of one seal the resident view holds the old runs with the overlay published or the new run with the overlay retired, never both or neither; the device half (B5 recovery over the run-replacement member) owes the same of the recovered manifest.")
(defun fn2-su-fact (j b) (declare (xargs :verify-guards nil)) (list 1 (fn2-su-name j) 0 0 b (+ 1 j) (+ 1 j) 0))
(defun fn2-su-facts (from n) (declare (xargs :verify-guards nil :measure (nfix n))) (if (zp n) nil (cons (fn2-su-fact from 7) (fn2-su-facts (+ 1 from) (- n 1)))))
(defun fn2-manifest-replacement-atomic-positive ()
 (declare (xargs :verify-guards nil))
 (let ((g (fn2-su-batch 0 30 100)) (i (fn2-su-facts 0 20)))
  (and (fn2-sealer-cuts-ok 8 g (fn2-sealer-cut-views 8 *fn2-su-groups* g 400))
       (fn2-sealer-cuts-ok 13 i (fn2-sealer-cut-views 13 *fn2-su-summary* i 400)))))
; Teeth: a seal that installed the run and retired the overlay in two steps
; shows the run beside its published overlay (a fact in two places), or
; neither (a fact nowhere): both views are refused.
(defun fn2-manifest-replacement-atomic-negative ()
 (declare (xargs :verify-guards nil))
 (let ((g (fn2-su-batch 0 3 100)) (fr *fn2-overlay-phase-frozen*) (fe *fn2-overlay-phase-free*))
  (and (not (fn2-sealer-cuts-ok 8 g (list (list nil (list fr)) (list (list (list 8 1 3 0)) (list fr)) (list (list (list 8 1 3 0)) (list fe)))))
       (not (fn2-sealer-cuts-ok 8 g (list (list nil (list fr)) (list nil (list fe)) (list (list (list 8 1 3 0)) (list fe))))))))
(fn2-assert-owed-teeth fn2-manifest-replacement-atomic)

;; The first-overlay rule (C-SEAL-ORDER): with an older batch still private,
;; the newer published one waits (nothing is sealed); summary runs get a
;; filter; an empty published overlay is retired with no run.
(assert-event
 (let ((r (fn2-sealer-image 8 *fn2-su-groups* (list (fn2-su-batch 0 3 100) (fn2-su-batch 3 3 100)) '(2 1) t nil 400 nil)))
  (and (equal (car r) :idle) (equal (cadr r) 0) (equal (cadddr r) nil))))
(assert-event
 (let ((r (fn2-sealer-image 13 *fn2-su-summary* (list (fn2-su-facts 0 5)) '(1) nil nil 400
                            (list (fn2-su-fact 2 7) (fn2-su-fact 9 7)))))
  (and (equal (car r) :idle) (equal (cadr r) 1) (equal (cadddr r) '((13 1 5 1)))
       (equal (caddr r) (list (list :found (fn2-su-fact 2 7)) (list :absent))))))

;; Readiness across seal-row phases (Brick H4): when no overlay is sealable
;; (an older batch is private), :idle is not pending, every active non-idle
;; phase (:build, :filter, :install) stays pending so a parked sealer wakes to
;; finish its in-flight run, and :failed is not pending; with a sealable
;; overlay, :idle is pending. Also verify fn2-seal-cache refuses :cache when
;; the writer's direct-mapped cache row already holds a ready page.
(fn2-su-defun fn2-su-pending-check ()
 (b* ((fn2-su-bind (code) (fn2-su-call fn2-su-setup 3 400))
      ((unless (eq code :ok)) (fn2-su-mv (list :setup code)))
      (fn2-su-bind (code)
        (fn2-su-call fn2-su-load 8 *fn2-su-groups*
                     (list (fn2-su-batch 0 3 100) (fn2-su-batch 3 3 100)) 0 '(2 1) t))
      ((unless (eq code :ok)) (fn2-su-mv (list :load code)))
      (p-idle-blocked (fn2-seal-pending-p fn2-seals fn2-overlays))
      (fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-build* fn2-seals))
      (p-build (fn2-seal-pending-p fn2-seals fn2-overlays))
      (fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-filter* fn2-seals))
      (p-filter (fn2-seal-pending-p fn2-seals fn2-overlays))
      (fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-install* fn2-seals))
      (p-install (fn2-seal-pending-p fn2-seals fn2-overlays))
      (fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-release* fn2-seals))
      (p-release (fn2-seal-pending-p fn2-seals fn2-overlays))
      (fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-failed* fn2-seals))
      (p-failed (fn2-seal-pending-p fn2-seals fn2-overlays))
      (fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-idle* fn2-seals))
      (fn2-overlays (fn2-overlays-set-phase 1 *fn2-overlay-phase-frozen* fn2-overlays))
      (p-idle-sealable (fn2-seal-pending-p fn2-seals fn2-overlays))
      (fn2-run-writers (fn2-run-writers-put 0 (unit 5) (counter 1) (slot 2) (gen 1)))
      ((mv c1 fn2-run-cache) (fn2-seal-cache 0 fn2-run-writers fn2-run-cache))
      (fn2-run-writers (fn2-run-writers-put 0 (unit (+ 5 (fn2-run-cache-rows fn2-run-cache))) (counter 2) (slot 3) (gen 1)))
      ((mv c2 fn2-run-cache) (fn2-seal-cache 0 fn2-run-writers fn2-run-cache))
      (kept-unit (fn2-run-cache-unit (fn2-run-cache-row 5 fn2-run-cache) fn2-run-cache)))
  (fn2-su-mv (list p-idle-blocked p-build p-filter p-install p-release p-failed p-idle-sealable c1 c2 kept-unit))))
(defun fn2-su-pending-result ()
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                      fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
  (mv-let (r fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
             fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
    (fn2-su-pending-check fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                          fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
   (mv r fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
       fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources))))
(assert-event (equal (fn2-su-pending-result) '(nil t t t t nil t :ok :cache 5)))

;; Minimal C5: bounded multi-run merge, row & arena reclamation, run-only
;; cross-schema compaction, and atomic multi-run replacement under :full.
(fn2-su-defun fn2-su-setup-cap (orows irows pages pfill)
 (b* ((fn2-seals (fn2-seals-init 1 fn2-seals))
      (fn2-overlays (fn2-overlays-init orows fn2-overlays))
      (fn2-overlay-index (fn2-overlay-index-init (* orows *fn2-su-icap*) fn2-overlay-index))
      (fn2-run-installed (fn2-run-installed-init irows fn2-run-installed))
      (fn2-run-builds (fn2-run-builds-init 1 fn2-run-builds))
      (fn2-run-writers (fn2-run-writers-init *fn2-seal-writer-rows* fn2-run-writers))
      (fn2-run-restarts (fn2-run-restarts-init (* *fn2-seal-writer-rows* *fn2-run-restart-capacity*) fn2-run-restarts))
      (fn2-run-cache (fn2-run-cache-init 1024 fn2-run-cache))
      (fn2-ribbon-builds (fn2-ribbon-builds-init 1 fn2-ribbon-builds))
      (fn2-ribbon-band (fn2-ribbon-band-init (fn2-ribbon-slots *fn2-su-icap*) fn2-ribbon-band))
      (fn2-fields (fn2-fields-init 3900 fn2-fields))
      (fn2-pool (fn2-pool-init (list (cons pages 65536)) 1 100 fn2-pool))
      (fn2-fc (fn2-fc-init 1 fn2-fc))
      (fn2-fc-context (fn2-fc-context-init 1 fn2-fc-context))
      (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
      (fn2-digests (fn2-digests-init 150 fn2-digests))
      (fn2-run-cursors (fn2-run-cursors-init 9 fn2-run-cursors))
      (fn2-run-paths (fn2-run-paths-init (* 9 *fn2-run-max-levels*) fn2-run-paths))
      (fn2-ranges (fn2-ranges-init 1 fn2-ranges))
      (fn2-range-sources (fn2-range-sources-init 8 fn2-range-sources))
      ((mv code fn2-seals) (fn2-seal-init 0 *fn2-su-fbase* 0 pfill 9 0 1 fn2-seals))
      ((unless (eq code :ok)) (fn2-su-mv code))
      ((mv code fn2-seals) (fn2-seal-merge-rows 0 0 1 (+ *fn2-su-fbase* *fn2-seal-field-rows*)
                                                (+ *fn2-su-fbase* *fn2-seal-field-rows* *fn2-run-entry-rows*) fn2-seals)))
  (fn2-su-mv code)))

(fn2-su-defun fn2-su-run-cap (sid layout batches irows pages pfill queries)
 (b* ((fn2-su-bind (code) (fn2-su-call fn2-su-setup-cap (+ 1 (len batches)) irows pages pfill))
      ((unless (eq code :ok)) (fn2-su-mv (list :setup code)))
      (fn2-su-bind (code) (fn2-su-call fn2-su-load sid layout batches 0 (fn2-su-seqs (len batches) 1) nil))
      ((unless (eq code :ok)) (fn2-su-mv (list :load code)))
      (fn2-su-bind (code done) (fn2-su-call fn2-su-drive 1000000 nil 0))
      (fn2-su-bind (answers) (fn2-su-call fn2-su-queries sid layout queries))
      (fn2-su-bind (installed) (fn2-su-call fn2-su-installed 0 irows))
      (free-pages (fn2-seal-free-pages fn2-pool)))
  (fn2-su-mv (list code done answers installed free-pages))))

(defun fn2-sealer-cap-image (sid layout batches irows pages pfill queries)
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                      fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
  (mv-let (r fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
             fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
    (fn2-su-run-cap sid layout batches irows pages pfill queries fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed
                    fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                    fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
   (mv r fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
       fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources))))

;; Step until the seal row reaches *fn2-seal-phase-install*, occupy every free
;; installed-run row, and verify fn2-seal-step refuses :full WITHOUT retiring
;; any of the merge's live input runs or its frozen overlay.
(fn2-su-defun fn2-su-step-to-install (fuel) :measure (nfix fuel)
 (if (or (zp fuel) (equal (fn2-seals-phase 0 fn2-seals) *fn2-seal-phase-install*))
     (fn2-su-mv (equal (fn2-seals-phase 0 fn2-seals) *fn2-seal-phase-install*))
  (b* (((mv code fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts
            fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests
            fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)
        (fn2-seal-step 4096 fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
                       fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                       fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)))
   (if (eq code :more) (fn2-su-call fn2-su-step-to-install (- fuel 1)) (fn2-su-mv nil)))))

(defun fn2-su-fill-free-rows (k r fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :verify-guards nil :measure (nfix k)))
 (if (or (zp k) (>= (nfix r) (fn2-run-installed-rows fn2-run-installed))) fn2-run-installed
  (let ((fn2-run-installed
         (if (equal (fn2-run-installed-state (nfix r) fn2-run-installed) *fn2-run-installed-state-free*)
             (fn2-run-installed-put (nfix r) (state *fn2-run-installed-state-live*) (schema 99) (run (+ 900 (nfix r))))
           fn2-run-installed)))
   (fn2-su-fill-free-rows (- k 1) (+ 1 (nfix r)) fn2-run-installed))))

(fn2-su-defun fn2-su-c5-mechanisms ()
 (b* (;; 1. Seal 2 runs of sid 8 (sizes 20, then 4 so size-tier leaves 2 runs on 8 rows),
      ;; then occupy 4 dummy rows of sid 99 so free-rows = 2 <= floor(8/3) = 2:
      ;; run-only compaction becomes pending with NO sealable overlays and merges sid 8 -> 1 run!
      (fn2-su-bind (code) (fn2-su-call fn2-su-setup-cap 4 8 40 *fn2-run-page-size*))
      ((unless (eq code :ok)) (fn2-su-mv (list :setup code)))
      (b1 (fn2-su-batch 0 20 100))
      (b2 (fn2-su-batch 10 4 200))
      (fn2-su-bind (code) (fn2-su-call fn2-su-load 8 *fn2-su-groups* (list b1 b2) 0 '(1 2) nil))
      ((unless (eq code :ok)) (fn2-su-mv (list :load code)))
      (fn2-su-bind (dcode &) (fn2-su-call fn2-su-drive 100000 nil 0))
      (fn2-su-bind (runs-before) (fn2-su-call fn2-su-installed 0 8))
      (p-unpressured (fn2-seal-compact-pending-p fn2-seals fn2-run-installed fn2-pool))
      ;; Occupy rows 2..5 with sid 99 singletons (1 run each), leaving free-rows = 2 <= 2
      (fn2-run-installed (fn2-run-installed-put 2 (state *fn2-run-installed-state-live*) (schema 91) (run 501)))
      (fn2-run-installed (fn2-run-installed-put 3 (state *fn2-run-installed-state-live*) (schema 92) (run 502)))
      (fn2-run-installed (fn2-run-installed-put 4 (state *fn2-run-installed-state-live*) (schema 93) (run 503)))
      (fn2-run-installed (fn2-run-installed-put 5 (state *fn2-run-installed-state-live*) (schema 94) (run 504)))
      (p-pressured (fn2-seal-compact-pending-p fn2-seals fn2-run-installed fn2-pool))
      (pages-before (fn2-seal-free-pages fn2-pool))
      (fn2-su-bind (ccode cdone) (fn2-su-call fn2-su-drive 100000 nil 0))
      (pages-after (fn2-seal-free-pages fn2-pool))
      (sid8-after (fn2-seal-live-runs 8 0 8 fn2-run-installed))
      (fn2-su-bind (ans-after) (fn2-su-call fn2-su-queries 8 *fn2-su-groups* *fn2-su-queries*))
      ;; 2. Atomic multi-run replacement under :full at *fn2-seal-phase-install*:
      (fn2-su-bind (code2) (fn2-su-call fn2-su-setup-cap 4 8 40 *fn2-run-page-size*))
      ((unless (eq code2 :ok)) (fn2-su-mv (list :setup2 code2)))
      (fn2-su-bind (code2) (fn2-su-call fn2-su-load 8 *fn2-su-groups* (list b1 b2) 0 '(1 2) nil))
      ((unless (eq code2 :ok)) (fn2-su-mv (list :load2 code2)))
      (fn2-su-bind (& &) (fn2-su-call fn2-su-drive 100000 nil 0))
      ;; Load batch 3 (size 10 >= 4/2, so it merges with run 2, k >= 1):
      (b3 (fn2-su-batch 5 10 300))
      (fn2-su-bind (code3) (fn2-su-call fn2-su-load 8 *fn2-su-groups* (list b3) 2 '(3) nil))
      ((unless (eq code3 :ok)) (fn2-su-mv (list :load3 code3)))
      (fn2-su-bind (at-install) (fn2-su-call fn2-su-step-to-install 100000))
      (planned-k (fn2-seals-k 0 fn2-seals))
      (fn2-run-installed (fn2-su-fill-free-rows 8 0 fn2-run-installed))
      ((mv full-code fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts
           fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests
           fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)
       (fn2-seal-step 4096 fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
                      fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                      fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths))
      (sid8-still-live (fn2-seal-live-runs 8 0 8 fn2-run-installed))
      (ov2-still-frozen (equal (fn2-overlays-phase 2 fn2-overlays) *fn2-overlay-phase-frozen*)))
  (fn2-su-mv (list dcode (len runs-before) p-unpressured p-pressured ccode cdone
                   (< pages-before pages-after) sid8-after
                   (equal ans-after (fn2-sealer-spec *fn2-su-groups-key* (list b1 b2) *fn2-su-queries*))
                   at-install (< 0 planned-k) full-code sid8-still-live ov2-still-frozen))))

(defun fn2-su-c5-mechanisms-result ()
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                      fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
  (mv-let (r fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
             fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
    (fn2-su-c5-mechanisms fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
                          fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources)
   (mv r fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cache
       fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-run-cursors fn2-run-paths fn2-ranges fn2-range-sources))))

(defconst *fn2-su-c5-batches*
 (list (fn2-su-batch 0 12 100) (fn2-su-batch 6 12 200) (fn2-su-batch 12 12 300) (fn2-su-batch 18 12 400)
       (fn2-su-batch 0 10 500) (fn2-su-batch 8 10 600) (fn2-su-batch 14 10 700) (fn2-su-batch 4 16 800)))

(defthm-owed fn2-sealer-merge-reclaims (batches queries pfill)
 (implies (and (fn2-sealer-inputp *fn2-su-groups* *fn2-su-groups-key* batches)
               (consp batches) (<= (len batches) 8)
               (natp pfill) (<= 400 pfill) (<= pfill *fn2-run-page-size*))
          (let ((img (fn2-sealer-cap-image 8 *fn2-su-groups* batches 4 24 pfill queries)))
           (and (equal (car img) :idle)
                (<= (len batches) (cadr img))
                (equal (caddr img) (fn2-sealer-spec *fn2-su-groups-key* batches queries))
                (<= (len (cadddr img)) 4)
                (< 16 (nth 4 img)))))
 :teeth (fn2-sealer-merge-reclaims-positive fn2-sealer-merge-reclaims-negative)
 :schema :invariant
 :doc "Minimal C5: sealing up to 8 batches across a 4-row installed-run table and 24-page pool merges superseded runs, reclaims their installed-run rows and 64 KiB page slots in :release, and preserves newest-wins lookup semantics.")

(defun fn2-sealer-merge-reclaims-positive ()
 (declare (xargs :verify-guards nil))
 (let* ((spec (fn2-sealer-spec *fn2-su-groups-key* *fn2-su-c5-batches* *fn2-su-queries*))
        (img (fn2-sealer-cap-image 8 *fn2-su-groups* *fn2-su-c5-batches* 4 24 400 *fn2-su-queries*))
        (sbatches (list (fn2-su-facts 0 6) (fn2-su-facts 3 6) (fn2-su-facts 6 6) (fn2-su-facts 9 6)))
        (squeries (list (fn2-su-fact 0 7) (fn2-su-fact 5 7) (fn2-su-fact 14 7) (fn2-su-fact 99 7)))
        (sspec (fn2-sealer-spec *fn2-su-summary-key* sbatches squeries))
        (simg (fn2-sealer-cap-image 13 *fn2-su-summary* sbatches 3 20 400 squeries)))
  (and (fn2-sealer-inputp *fn2-su-groups* *fn2-su-groups-key* *fn2-su-c5-batches*)
       (equal (car img) :idle)
       (<= 8 (cadr img))
       (equal (caddr img) spec)
       (equal (cadddr img) '((8 8 30 0)))
       (equal (nth 4 img) 23)
       ;; Identity summary (schema 13) multi-run merge skips single-overlay Ribbon filter (filter = 0)
       (equal (car simg) :idle)
       (equal (caddr simg) sspec)
       (equal (cadddr simg) '((13 4 15 0)))
       (equal (nth 4 simg) 19)
       (equal (fn2-su-c5-mechanisms-result) '(:idle 2 nil t :idle 2 t 1 t t t :full 2 t)))))

(defun fn2-sealer-merge-reclaims-negative ()
 (declare (xargs :verify-guards nil))
 (let ((spec (fn2-sealer-spec *fn2-su-groups-key* *fn2-su-c5-batches* *fn2-su-queries*))
       ;; Only 1 installed-run row cannot hold a live run plus a replacement row before retiring: :full
       (too-small (fn2-sealer-cap-image 8 *fn2-su-groups* *fn2-su-c5-batches* 1 24 400 *fn2-su-queries*))
       ;; Reversed batch order yields older values on overlapping keys, refuting oldest-wins merge
       (wrong-order (fn2-sealer-spec *fn2-su-groups-key* (reverse *fn2-su-c5-batches*) *fn2-su-queries*)))
  (and (eq (car too-small) :full)
       (not (equal wrong-order spec)))))

(fn2-assert-owed-teeth fn2-sealer-merge-reclaims)
