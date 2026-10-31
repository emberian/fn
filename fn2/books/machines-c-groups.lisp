; Layer C in the served core, seams S-GROUP and the exact lookup it stands on
; (fn2/docs/c-ordered-runs.md §8 item 9): the group directory's genesis from
; the profile's :groups list, and the exact lookup of a key over a schema's
; published overlays and installed runs, newest first. A lookup is
; resumable: one source (one overlay, or one bounded run step) per call, its
; continuation in the transaction's row (LPHASE LBOUND LROW LVER), its query
; in the transaction's decision entry rows (+4), its decoded entries in the
; run reader rows (+84), its run cursor the transaction's. So it is called at
; :prepare while the transaction's identity decision is idle or done and
; resolve is not inside a run descent (:state otherwise). The genesis, the
; lookup's defcost and the core wrappers (fn2-groups-core-events,
; materialized in assembly-callbacks-c.lisp) are this book's.
(in-package "ACL2")
(include-book "machines-c-bind")
(fn2-book-layer :c)
(local (in-theory (disable fn2-run-layout-fields fn2-run-layout-keys fn2-run-layout-merge fn2-run-layout-size
                           fn2-fold-key-arg fn2-fold-arity fn2-fold-assigned-p fn2-run-layout-octets-max
                           fn2-run-layout-value-ok fn2-run-layout-fold-p fn2-run-version)))

(defconst *fn2-groups-sid* 8)
(defconst *fn2-groups-name-max* 250)
(assert-event (and (equal *fn2-groups-entry-field-name* 0) (equal *fn2-groups-entry-field-group* 1)))

; ---------------------------------------------------------------------------
; The exact lookup. The published overlay of SID (frozen) with the greatest
; SEQ below BOUND among rows O.. (K of them); BEST the row count when none.
(defun fn2-xl-newest-frozen (k o sid bound best fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :measure (nfix k) :guard (and (fn2-overlays-wfp fn2-overlays) (natp o))))
 (if (not (and (posp k) (natp o) (< o (fn2-overlays-rows fn2-overlays)))) best
  (fn2-xl-newest-frozen (- k 1) (+ 1 o) sid bound
                        (if (and (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-frozen*)
                                 (equal (fn2-overlays-schema o fn2-overlays) sid)
                                 (< (nfix (fn2-overlays-seq o fn2-overlays)) (nfix bound))
                                 (or (not (and (natp best) (< best (fn2-overlays-rows fn2-overlays))))
                                     (< (nfix (fn2-overlays-seq best fn2-overlays)) (nfix (fn2-overlays-seq o fn2-overlays)))))
                            o best)
                        fn2-overlays)))
(defthm fn2-xl-newest-frozen-natp
 (implies (natp best) (natp (fn2-xl-newest-frozen k o sid bound best fn2-overlays))) :rule-classes :type-prescription)
(in-theory (disable fn2-xl-newest-frozen))

; Restart TX's lookup from the newest overlay, noting SID's run version.
(defun fn2-xl-restart (tx sid fn2-succ-txns fn2-run-installed)
 (declare (xargs :stobjs (fn2-succ-txns fn2-run-installed)
  :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-run-installed-wfp fn2-run-installed))))
 (b* ((version (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (unsigned-byte-p 60 version)))
       (mv :bounds fn2-succ-txns))
      (fn2-succ-txns (fn2-succ-txns-put tx (lphase *fn2-succ-lookup-overlays*) (lbound *fn2-u60-max*) (lrow 0) (lver version))))
  (mv :more fn2-succ-txns)))
(fn2-idc-fn-shape fn2-xl-restart (tx sid fn2-succ-txns fn2-run-installed) (fn2-succ-txns) (fn2-succ-txns fn2-run-installed))

; Done: TX's lookup idles.
(defun fn2-xl-done (tx code fn2-succ-txns)
 (declare (xargs :stobjs fn2-succ-txns :guard (fn2-succ-txns-wfp fn2-succ-txns)))
 (if (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)))
     (let ((fn2-succ-txns (fn2-succ-txns-put tx (lphase *fn2-succ-lookup-idle*) (lbound 0) (lrow 0) (lver 0))))
      (mv code fn2-succ-txns))
   (mv :bounds fn2-succ-txns)))
(fn2-idc-fn-shape fn2-xl-done (tx code fn2-succ-txns) (fn2-succ-txns) (fn2-succ-txns))

; The overlay leg: the newest published overlay below the bound holding the
; query's key answers with its entry decoded at RB; else the bound moves
; below it, and past the last overlay the run leg starts. (mv code found
; txns fields)
(defun fn2-xl-overlay (tx sid qb rb qk qs qg fn2-succ-txns fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
  :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-ov-locate fn2-ov-entry fn2-fields-rows fn2-overlays-rows)))))
 (b* (((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp qb) (natp rb)
                    (<= (+ qb *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))
                    (<= (+ rb *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))))
       (mv :bounds nil fn2-succ-txns fn2-fields))
      (rows (fn2-overlays-rows fn2-overlays))
      (o (fn2-xl-newest-frozen rows 0 sid (fn2-succ-txns-lbound tx fn2-succ-txns) rows fn2-overlays))
      ((unless (< o rows))
       (let ((fn2-succ-txns (fn2-succ-txns-put tx (lphase *fn2-succ-lookup-runs*) (lbound *fn2-u60-max*))))
        (mv :more nil fn2-succ-txns fn2-fields)))
      ((mv code pos order fn2-fields) (fn2-ov-locate o rb qb qk qs qg fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code nil fn2-succ-txns fn2-fields))
      ((when (eq order :eq))
       (b* (((mv code & fn2-fields) (fn2-ov-entry o pos rb fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
        (mv code (eq code :ok) fn2-succ-txns fn2-fields)))
      (seq (fn2-overlays-seq o fn2-overlays))
      ((unless (unsigned-byte-p 60 seq)) (mv :bounds nil fn2-succ-txns fn2-fields))
      (fn2-succ-txns (fn2-succ-txns-set-lbound tx seq fn2-succ-txns)))
  (mv :more nil fn2-succ-txns fn2-fields)))
(fn2-idc-fn-shape fn2-xl-overlay (tx sid qb rb qk qs qg fn2-succ-txns fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 ((fn2-succ-txns 2) (fn2-fields 3)) (fn2-succ-txns fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-xl-newest-frozen fn2-ov-locate fn2-ov-entry fn2-succ-txns-lbound fn2-overlays-seq))

; The run leg, between runs: start the cursor in the newest live run of SID
; below the bound, or answer :absent past the last.
(defun fn2-xl-run-next (tx sid rb fn2-succ-txns fn2-run-installed fn2-run-cursors)
 (declare (xargs :stobjs (fn2-succ-txns fn2-run-installed fn2-run-cursors)
  :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-run-installed-wfp fn2-run-installed) (fn2-run-cursors-wfp fn2-run-cursors))
  :guard-hints (("Goal" :in-theory (disable fn2-run-cursor-start fn2-xl-done)))))
 (b* (((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp rb)))
       (mv :bounds fn2-succ-txns fn2-run-cursors))
      (rows (fn2-run-installed-rows fn2-run-installed))
      (r (fn2-succ-newest-run rows 0 sid (fn2-succ-txns-lbound tx fn2-succ-txns) rows fn2-run-installed))
      ((unless (and (natp r) (< r rows)))
       (mv-let (code fn2-succ-txns) (fn2-xl-done tx :absent fn2-succ-txns) (mv code fn2-succ-txns fn2-run-cursors)))
      ((mv code fn2-run-cursors)
       (fn2-run-cursor-start tx sid (fn2-run-installed-top r fn2-run-installed) (fn2-run-installed-slot r fn2-run-installed)
                             (fn2-run-installed-gen r fn2-run-installed) (fn2-run-installed-unit r fn2-run-installed)
                             (fn2-run-installed-counter r fn2-run-installed) rb
                             (fn2-run-installed-okind r fn2-run-installed) (fn2-run-installed-oslot r fn2-run-installed)
                             (fn2-run-installed-ogen r fn2-run-installed) fn2-run-cursors))
      ((unless (eq code :ok)) (mv code fn2-succ-txns fn2-run-cursors))
      (run (fn2-run-installed-run r fn2-run-installed))
      ((unless (and (unsigned-byte-p 60 run) (unsigned-byte-p 32 r))) (mv :bounds fn2-succ-txns fn2-run-cursors))
      (fn2-succ-txns (fn2-succ-txns-put tx (lphase *fn2-succ-lookup-scan*) (lbound run) (lrow r))))
  (mv :more fn2-succ-txns fn2-run-cursors)))
(fn2-idc-fn-shape fn2-xl-run-next (tx sid rb fn2-succ-txns fn2-run-installed fn2-run-cursors)
 (fn2-succ-txns fn2-run-cursors) (fn2-succ-txns fn2-run-installed fn2-run-cursors) t
 (fn2-succ-newest-run fn2-run-cursor-start fn2-xl-done fn2-succ-txns-lbound fn2-run-installed-run
  fn2-run-installed-top fn2-run-installed-slot fn2-run-installed-gen fn2-run-installed-unit fn2-run-installed-counter
  fn2-run-installed-okind fn2-run-installed-oslot fn2-run-installed-ogen))

; One call of TX's lookup of the key at QB (owner QK QS QG) in SID: :ok with
; the entry decoded at the returned row, :absent, :more (call again), :miss
; (a run page to load), or a refusal. A run version that moved while the
; lookup was in the run leg restarts it from the newest overlay (a fact
; that moved from an overlay already passed into a new run is met again).
; (mv code erow txns cursors paths fields)
(defun fn2-xl-step (tx sid budget qb rb qk qs qg fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed
                    fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths
                          fn2-run-cache fn2-fields fn2-pool)
  :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
              (fn2-run-installed-wfp fn2-run-installed) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths)
              (fn2-run-cache-wfp fn2-run-cache) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp budget))
  :guard-hints (("Goal" :in-theory (disable fn2-xl-restart fn2-xl-done fn2-xl-overlay fn2-xl-run-next fn2-run-lookup-step
                                            fn2-fields-rows fn2-succ-txns-rows)))))
 (b* (((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp rb) (natp qb)))
       (mv :bounds 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      (lphase (fn2-succ-txns-lphase tx fn2-succ-txns)))
  (cond
   ((equal lphase *fn2-succ-lookup-idle*)
    (mv-let (code fn2-succ-txns) (fn2-xl-restart tx sid fn2-succ-txns fn2-run-installed)
     (mv code 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
   ((equal lphase *fn2-succ-lookup-overlays*)
    (b* (((mv code found fn2-succ-txns fn2-fields)
          (fn2-xl-overlay tx sid qb rb qk qs qg fn2-succ-txns fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
         ((when found) (mv-let (c fn2-succ-txns) (fn2-xl-done tx :ok fn2-succ-txns)
                        (mv c rb fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))))
     (mv code 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
   ((not (equal (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed)
                (fn2-succ-txns-lver tx fn2-succ-txns)))
    (mv-let (code fn2-succ-txns) (fn2-xl-restart tx sid fn2-succ-txns fn2-run-installed)
     (mv code 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
   ((equal lphase *fn2-succ-lookup-runs*)
    (mv-let (code fn2-succ-txns fn2-run-cursors) (fn2-xl-run-next tx sid rb fn2-succ-txns fn2-run-installed fn2-run-cursors)
     (mv code 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
   (t
    (b* (((mv code fn2-run-cursors fn2-run-paths fn2-fields)
          (fn2-run-lookup-step tx budget qb qk qs qg fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
     (case code
      (:found (mv-let (c fn2-succ-txns) (fn2-xl-done tx :ok fn2-succ-txns)
               (mv c (+ rb *fn2-run-reader-entry*) fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
      (:absent (let ((fn2-succ-txns (fn2-succ-txns-set-lphase tx *fn2-succ-lookup-runs* fn2-succ-txns)))
                (mv :more 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
      (otherwise (mv code 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))))))))
(fn2-idc-fn-shape fn2-xl-step (tx sid budget qb rb qk qs qg fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed
                               fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-succ-txns 2) (fn2-run-cursors 3) (fn2-run-paths 4) (fn2-fields 5))
 (fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) t
 (fn2-xl-restart fn2-xl-done fn2-xl-overlay fn2-xl-run-next fn2-run-lookup-step fn2-succ-txns-lphase fn2-succ-txns-lver))
(defthm fn2-xl-step-natp
 (natp (mv-nth 1 (fn2-xl-step tx sid budget qb rb qk qs qg fn2-succ-txns fn2-overlays fn2-overlay-index fn2-run-installed
                              fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
 :hints (("Goal" :in-theory (enable fn2-xl-step))) :rule-classes :type-prescription)

; The group lookup (seam S-GROUP) for transaction TX: the newsgroup name is
; the LEN octets at [OFF, OFF+LEN) of SLOT/GEN, readable under OKIND OSLOT
; OGEN; each call passes the same name. (mv code group txns cursors paths
; fields): :ok with the group identifier, :absent (441), :more, :miss.
(defun fn2-grp-lookup (tx slot gen off len okind oslot ogen budget b0
                       fn2-succ-txns fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed
                       fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-xl-step fn2-fields-rows)))))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-id-decides-wfp fn2-id-decides) (fn2-overlays-wfp fn2-overlays)
                    (fn2-overlay-index-wfp fn2-overlay-index) (fn2-run-installed-wfp fn2-run-installed)
                    (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp fn2-run-cache)
                    (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (< tx (fn2-id-decides-rows fn2-id-decides))
                    (natp b0) (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields)) (natp budget) (<= budget 4096)
                    (posp len) (<= len *fn2-groups-name-max*) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                    (unsigned-byte-p 32 off) (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (member (fn2-id-decides-phase tx fn2-id-decides) (list *fn2-id-decide-phase-idle* *fn2-id-decide-phase-done*))
                    (not (equal (fn2-succ-txns-rstate tx fn2-succ-txns) *fn2-succ-resolve-look*))))
       (mv :state 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      (qb (+ b0 *fn2-idc-eb*)) (rb (+ b0 *fn2-idc-rb*))
      (fn2-fields (fn2-fields-put qb (value 0) (ref-slot slot) (ref-gen gen) (ref-off off) (ref-len len)))
      ((mv code erow fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-xl-step tx *fn2-groups-sid* budget qb rb okind oslot ogen fn2-succ-txns fn2-overlays fn2-overlay-index
                    fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields))
      (row (+ erow *fn2-groups-entry-field-group*))
      ((unless (< row (fn2-fields-rows fn2-fields))) (mv :bounds 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
  (mv :ok (fn2-fields-value row fn2-fields) fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
(fn2-idc-fn-shape fn2-grp-lookup (tx slot gen off len okind oslot ogen budget b0
                                  fn2-succ-txns fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed
                                  fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 ((fn2-succ-txns 2) (fn2-run-cursors 3) (fn2-run-paths 4) (fn2-fields 5))
 (fn2-succ-txns fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) t
 (fn2-xl-step fn2-id-decides-phase fn2-succ-txns-rstate))

; ---------------------------------------------------------------------------
; Genesis: the profile's :groups, a list of (NAME . GROUP) with NAME a string
; of 1 to 250 characters and GROUP a positive u60, enter one published
; overlay of the group directory (SEQ the engine's next, coverage 0) in an
; engine arena, before any transaction exists. A malformed list, a repeated
; name or more groups than one overlay holds is refused by name; an empty
; list is :ok with nothing taken.
(defun fn2-grp-groupsp (groups)
 (declare (xargs :guard t))
 (or (null groups)
     (and (consp groups) (consp (car groups)) (stringp (caar groups))
          (< 0 (length (caar groups))) (<= (length (caar groups)) *fn2-groups-name-max*)
          (posp (cdar groups)) (unsigned-byte-p 60 (cdar groups))
          (fn2-grp-groupsp (cdr groups)))))
(in-theory (disable fn2-grp-groupsp))
(defun fn2-grp-write-name (i name slot gen fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix (- (length name) (nfix i)))
  :guard (and (fn2-pool-wfp fn2-pool) (stringp name) (natp i))))
 (if (not (and (stringp name) (natp i) (< i (length name)))) (mv :ok fn2-pool)
  (mv-let (code fn2-pool)
    (fn2-pool-write slot gen i (char-code (char name i)) *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool)
   (if (eq code :ok) (fn2-grp-write-name (+ 1 i) name slot gen fn2-pool) (mv code fn2-pool)))))
(fn2-pool-preserves fn2-grp-write-name (i name slot gen fn2-pool) :position 1)
(in-theory (disable fn2-grp-write-name))

; Insert one group (NAME . GROUP) into overlay O through the scratch (the
; name at 0): the entry at E, the decode scratch at EB; a repeated name is
; :duplicate (a :latest overlay would replace it).
(defun fn2-grp-insert-one (name group o e eb fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
  :guard (and (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp e) (natp eb))
  :guard-hints (("Goal" :in-theory (disable fn2-ov-insert fn2-pool-reset fn2-grp-write-name fn2-fields-rows fn2-overlays-rows)))))
 (b* (((unless (and (stringp name) (< 0 (length name)) (<= (length name) *fn2-groups-name-max*)
                    (posp group) (unsigned-byte-p 60 group) (natp o) (< o (fn2-overlays-rows fn2-overlays))
                    (< 0 (fn2-id-engine-rows fn2-id-engine)) (natp e) (< (+ e 1) (fn2-fields-rows fn2-fields))))
       (mv :groups fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (sslot (fn2-id-engine-slot 0 fn2-id-engine)) (sgen (fn2-id-engine-gen 0 fn2-id-engine))
      ((unless (and (unsigned-byte-p 32 sslot) (unsigned-byte-p 60 sgen))) (mv :state fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-pool-reset sslot sgen *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-grp-write-name 0 name sslot sgen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (fn2-fields (fn2-fields-put (+ e *fn2-groups-entry-field-name*) (value 0) (ref-slot sslot) (ref-gen sgen) (ref-off 0)
                                  (ref-len (length name))))
      (fn2-fields (fn2-fields-put (+ e *fn2-groups-entry-field-group*) (value group) (ref-len 0)))
      (count (fn2-overlays-count o fn2-overlays))
      ((mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (fn2-ov-insert o e eb fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((when (equal (fn2-overlays-count o fn2-overlays) count)) (mv :duplicate fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
  (mv :ok fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-grp-insert-one (name group o e eb fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-id-engine-slot fn2-id-engine-gen fn2-grp-write-name fn2-overlays-count))
(defun fn2-grp-insert-all (groups o e eb fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
  :guard (and (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp e) (natp eb))))
 (b* (((when (atom groups)) (mv :ok fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (consp (car groups))) (mv :groups fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (fn2-grp-insert-one (caar groups) (cdar groups) o e eb fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
  (fn2-grp-insert-all (cdr groups) o e eb fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-grp-insert-all (groups o e eb fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-grp-insert-one))

(defun fn2-grp-genesis (groups b0 fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-idc-scratch fn2-ov-start fn2-ov-advance fn2-grp-insert-all fn2-pool-reserve
                                            fn2-pool-class-for fn2-fields-rows fn2-overlays-rows fn2-overlay-index-rows
                                            fn2-grp-groupsp fn2-idc-find-overlay fn2-id-engine-rows len)))))
 (b* (((unless (and (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
                    (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((when (null groups)) (mv :ok fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (and (fn2-grp-groupsp groups) (natp b0) (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields))
                    (< 0 (fn2-id-engine-rows fn2-id-engine))))
       (mv :groups fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (rows (fn2-overlays-rows fn2-overlays))
      (o (fn2-idc-find-overlay rows 0 *fn2-overlay-phase-free* 0 fn2-overlays))
      ((unless (and (posp rows) (< o rows))) (mv :full fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (icap (floor (fn2-overlay-index-rows fn2-overlay-index) rows))
      ((unless (<= (len groups) icap)) (mv :capacity fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code fn2-id-engine fn2-pool) (fn2-idc-scratch fn2-id-engine fn2-pool))
      ((unless (and (eq code :ok) (< 0 (fn2-id-engine-rows fn2-id-engine))))
       (mv (if (eq code :ok) :state code) fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (arena (fn2-id-engine-arena 0 fn2-id-engine))
      (class (fn2-pool-class-for (nfix arena) fn2-pool))
      ((unless (natp class)) (mv :capacity fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code slot gen fn2-pool) (fn2-pool-reserve class *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code fn2-overlays fn2-pool)
       (fn2-ov-start o *fn2-groups-sid* slot gen (* o icap) icap *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* 0
                     fn2-overlays fn2-overlay-index fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (fn2-grp-insert-all groups o b0 (+ b0 *fn2-idc-eb*) fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (seq (+ 1 (nfix (fn2-id-engine-seq 0 fn2-id-engine))))
      ((unless (unsigned-byte-p 60 seq)) (mv :bounds fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (fn2-id-engine (fn2-id-engine-set-seq 0 seq fn2-id-engine))
      (fn2-overlays (fn2-overlays-set-seq o seq fn2-overlays))
      ((mv code fn2-overlays) (fn2-ov-advance o *fn2-overlay-phase-active* *fn2-overlay-phase-frozen* fn2-overlays)))
  (mv code fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-grp-genesis (groups b0 fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-grp-groupsp fn2-idc-find-overlay fn2-idc-scratch fn2-id-engine-arena fn2-id-engine-seq fn2-grp-insert-all fn2-pool-class-for))

(defcost fn2-group-lookup :answers (:absent :bad-magic :bounds :done :end :entry :format :invariant :length :lost :miss :more
  :noncanonical :ok :owner :part :payload :schema :stale :state :truncated :unknown-tag :wide)
 :bytes 4096
 :tables (fn2-core-succ-txns fn2-core-run-cursors fn2-core-run-paths fn2-core-fields)
 :doc "One source of a group-name lookup: one overlay search (at most 250-octet compares over 9 probes) or one run step of at most 4,096 pool reads.")

(defmacro fn2-groups-core-events ()
 '(progn
   (defun fn2-group-lookup (tx slot gen off len okind oslot ogen budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
                (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-run-cursors (fn2-core-run-cursors fn2-core))
                (fn2-run-paths (fn2-core-run-paths fn2-core)) (fn2-run-cache (fn2-core-run-cache fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code group fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)
     (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
      (if (eq c :ok)
          (fn2-grp-lookup tx slot gen off len okind oslot ogen budget b0 fn2-succ-txns fn2-id-decides fn2-overlays
                          fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
        (mv c 0 fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields)))
     (mv code group fn2-core)))
   (fn2-core-preserves fn2-group-lookup (tx slot gen off len okind oslot ogen budget fn2-core)
    :position 2 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-groups-genesis (profile fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-id-engine (fn2-core-id-engine fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
     (mv-let (c b0) (fn2-idc-stripe 0 (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
      (if (eq c :ok)
          (fn2-grp-genesis (fn2-profile-get :groups profile) b0 fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
        (mv c fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
     (mv code fn2-core)))
   (fn2-core-preserves fn2-groups-genesis (profile fn2-core)
    :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-group-lookup fn2-groups-genesis))
   (assert-event (fn2-assert-compliant-p '(fn2-group-lookup fn2-groups-genesis) (w state)))))
