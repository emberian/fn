; Layer C: multi-page runs. Level 0 holds the entries; each sealed page's
; first key and parent-held reference become one entry of the level above.
; A build owns one writer row per level; its caller supplies pages and
; records each sealed page. Every call is bounded; :more resumes.
(in-package "ACL2")
(include-book "runs-schema")
(fn2-book-layer :c)
; B's and A's shape lemmas are stated over the rows accessors; keep them folded.
(local (in-theory (disable fn2-pool-rows fn2-fields-rows fn2-digests-rows fn2-fc-rows fn2-fc-context-rows fn2-b3-rows)))

; A format parameter, not a ceiling on stored entries: with 64 KiB pages and
; index entries of at most 350 bytes, six levels address over 10^13 pages.
(defconst *fn2-run-max-levels* 6)
; Field rows a build owns: one writer range per level, then one index-entry
; region where a sealed page's first key and reference are assembled.
(defconst *fn2-run-build-index* (* *fn2-run-max-levels* *fn2-run-writer-fields*))
(defconst *fn2-run-build-fields* (+ *fn2-run-build-index* *fn2-run-entry-rows*))

(defcolumns fn2-run-builds
 ((phase (:enum fn2-run-build-phase (:idle :adding :finishing :done :failed)))
  (schema :u60) (run :u60) (height :u8) (wbase :u32) (entries :u60) (pages :u60)
  (crow :u32) (hbase :u32) (hslot :u32) (hgen :u60) (fields :u32) (limit :u32)
  (history :u60) (incarnation :u60) (okind :u8) (oslot :u32) (ogen :u60)))

(defun fn2-run-buildp (b fn2-run-builds fn2-run-writers)
 (declare (xargs :stobjs (fn2-run-builds fn2-run-writers) :guard t))
 (and (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers)
      (natp b) (< b (fn2-run-builds-rows fn2-run-builds))
      (<= (+ (fn2-run-builds-wbase b fn2-run-builds) *fn2-run-max-levels*)
          (fn2-run-writers-rows fn2-run-writers))))
(defmacro fn2-run-level-writer (b level)
 `(+ (fn2-run-builds-wbase ,b fn2-run-builds) ,level))
(defmacro fn2-run-level-phase (b level)
 `(fn2-run-writers-phase (fn2-run-level-writer ,b ,level) fn2-run-writers))

; Idle every level writer of a build, ordinal zero.
(defun fn2-run-reset-writers (n w fn2-run-writers)
 (declare (xargs :stobjs fn2-run-writers :measure (nfix n)
  :guard (and (fn2-run-writers-wfp fn2-run-writers) (natp n) (natp w))))
 (cond ((zp n) (mv :ok fn2-run-writers))
       ((not (and (natp w) (< (+ w (- n 1)) (fn2-run-writers-rows fn2-run-writers)))) (mv :bounds fn2-run-writers))
       (t (let ((fn2-run-writers (fn2-run-writers-put (+ w (- n 1)) (phase *fn2-run-writer-phase-idle*) (ordinal 0))))
           (fn2-run-reset-writers (- n 1) w fn2-run-writers)))))
(fn2-run-writers-preserves fn2-run-reset-writers (n w fn2-run-writers) :position 1 :raw-rows t)

; Start a build. The hash slot is a C-owned workspace whose first
; 32 * levels bytes are zeroed here; level L's sealed hash is copied to
; offset 32 L for its parent entry.
(defun fn2-run-build-start (b schema run wbase crow hbase hslot hgen fields limit history incarnation
                             okind oslot ogen fn2-run-builds fn2-run-writers fn2-pool)
 (declare (xargs :stobjs (fn2-run-builds fn2-run-writers fn2-pool)
  :guard (and (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (natp b) (< b (fn2-run-builds-rows fn2-run-builds))
                    (unsigned-byte-p 60 schema) (unsigned-byte-p 60 run) (unsigned-byte-p 32 wbase)
                    (unsigned-byte-p 32 crow) (unsigned-byte-p 32 hbase) (unsigned-byte-p 32 hslot)
                    (unsigned-byte-p 60 hgen) (unsigned-byte-p 32 fields) (unsigned-byte-p 32 limit)
                    (unsigned-byte-p 60 history) (unsigned-byte-p 60 incarnation)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds fn2-run-builds fn2-run-writers fn2-pool))
      ((unless (member (fn2-run-builds-phase b fn2-run-builds)
                       (list *fn2-run-build-phase-idle* *fn2-run-build-phase-done*)))
       (mv :state fn2-run-builds fn2-run-writers fn2-pool))
      ((mv code fn2-pool) (fn2-pool-reset hslot hgen okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-run-builds fn2-run-writers fn2-pool))
      ((mv code fn2-pool) (fn2-run-zero (* 32 *fn2-run-max-levels*) hslot hgen 0 okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-run-builds fn2-run-writers fn2-pool))
      ((mv code fn2-run-writers) (fn2-run-reset-writers *fn2-run-max-levels* wbase fn2-run-writers))
      ((unless (eq code :ok)) (mv code fn2-run-builds fn2-run-writers fn2-pool))
      (fn2-run-builds (fn2-run-builds-put b (phase *fn2-run-build-phase-adding*) (schema schema) (run run)
                        (height 0) (wbase wbase) (entries 0) (pages 0) (crow crow) (hbase hbase)
                        (hslot hslot) (hgen hgen) (fields fields) (limit limit)
                        (history history) (incarnation incarnation) (okind okind) (oslot oslot) (ogen ogen))))
  (mv :ok fn2-run-builds fn2-run-writers fn2-pool)))
(fn2-run-builds-preserves fn2-run-build-start (b schema run wbase crow hbase hslot hgen fields limit history incarnation okind oslot ogen fn2-run-builds fn2-run-writers fn2-pool)
 :position 1 :disable nil
 :hyps ((fn2-run-buildsp fn2-run-builds) (fn2-run-builds-wfp fn2-run-builds)))
(fn2-run-writers-preserves fn2-run-build-start (b schema run wbase crow hbase hslot hgen fields limit history incarnation okind oslot ogen fn2-run-builds fn2-run-writers fn2-pool)
 :position 2 :prefix "-WRITERS-PRESERVES" :disable nil)
(fn2-pool-preserves fn2-run-build-start (b schema run wbase crow hbase hslot hgen fields limit history incarnation okind oslot ogen fn2-run-builds fn2-run-writers fn2-pool)
 :position 3 :prefix "-POOL-PRESERVES")

; Give level LEVEL a fresh page: a C-owned 64 KiB workspace and its physical
; identity, from the caller's allocator reservation. The page's ordinal is
; the build's page count at that level, kept in the writer row across pages.
(defun fn2-run-build-page (b level slot gen unit epoch counter fn2-run-builds fn2-run-writers fn2-pool)
 (declare (xargs :stobjs (fn2-run-builds fn2-run-writers fn2-pool)
  :guard (and (fn2-run-buildp b fn2-run-builds fn2-run-writers) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (natp level) (< level *fn2-run-max-levels*)
                    (< level (fn2-run-builds-height b fn2-run-builds))))
       (mv :bounds fn2-run-builds fn2-run-writers fn2-pool))
      (w (fn2-run-level-writer b level))
      ((unless (equal (fn2-run-writers-phase w fn2-run-writers) *fn2-run-writer-phase-idle*))
       (mv :state fn2-run-builds fn2-run-writers fn2-pool))
      (ordinal (fn2-run-writers-ordinal w fn2-run-writers))
      ((mv code fn2-run-writers fn2-pool)
       (fn2-run-open w slot gen (fn2-run-builds-schema b fn2-run-builds) 1 level
                     (fn2-run-builds-run b fn2-run-builds) ordinal
                     (if (zp level) *page-kind-run-data* *page-kind-run-index*)
                     unit epoch counter (fn2-run-builds-history b fn2-run-builds)
                     (fn2-run-builds-incarnation b fn2-run-builds)
                     (fn2-run-builds-okind b fn2-run-builds) (fn2-run-builds-oslot b fn2-run-builds)
                     (fn2-run-builds-ogen b fn2-run-builds)
                     (+ (fn2-run-builds-fields b fn2-run-builds) (* level *fn2-run-writer-fields*))
                     (fn2-run-builds-limit b fn2-run-builds) fn2-run-writers fn2-pool)))
  (mv code fn2-run-builds fn2-run-writers fn2-pool)))
(fn2-run-builds-preserves fn2-run-build-page (b level slot gen unit epoch counter fn2-run-builds fn2-run-writers fn2-pool)
 :position 1 :disable nil)
(fn2-run-writers-preserves fn2-run-build-page (b level slot gen unit epoch counter fn2-run-builds fn2-run-writers fn2-pool)
 :position 2 :prefix "-WRITERS-PRESERVES" :disable nil :raw-rows t
 :hyps ((fn2-run-writersp fn2-run-writers) (fn2-run-buildsp fn2-run-builds) (fn2-run-buildp b fn2-run-builds fn2-run-writers)))
(fn2-pool-preserves fn2-run-build-page (b level slot gen unit epoch counter fn2-run-builds fn2-run-writers fn2-pool)
 :position 3 :prefix "-POOL-PRESERVES")

; All levels below L idle.
(defun fn2-run-below-idle (l wbase fn2-run-writers)
 (declare (xargs :stobjs fn2-run-writers :measure (nfix l)
  :guard (and (fn2-run-writers-wfp fn2-run-writers) (natp l) (natp wbase)
              (<= (+ wbase l) (fn2-run-writers-rows fn2-run-writers)))))
 (or (zp l)
     (and (equal (fn2-run-writers-phase (+ wbase (- l 1)) fn2-run-writers) *fn2-run-writer-phase-idle*)
          (fn2-run-below-idle (- l 1) wbase fn2-run-writers))))
; The highest level that needs action, top down: (mv action level).
(defun fn2-run-scan (l b finishing fn2-run-builds fn2-run-writers)
 (declare (xargs :stobjs (fn2-run-builds fn2-run-writers) :measure (nfix (+ 1 l))
  :guard (and (fn2-run-buildp b fn2-run-builds fn2-run-writers) (integerp l) (< l *fn2-run-max-levels*))))
 (if (or (not (integerp l)) (< l 0)) (mv :idle 0)
  (let* ((wbase (fn2-run-builds-wbase b fn2-run-builds)) (w (+ wbase l))
         (phase (fn2-run-writers-phase w fn2-run-writers)))
   (cond ((equal phase *fn2-run-writer-phase-closing*) (mv :close-step l))
         ((equal phase *fn2-run-writer-phase-heading*) (mv :head l))
         ((equal phase *fn2-run-writer-phase-sealing*) (mv :seal-step l))
         ((equal phase *fn2-run-writer-phase-failed*) (mv :failed l))
         ((equal phase *fn2-run-writer-phase-sealed*)
          (if (and finishing (equal (+ 1 l) (fn2-run-builds-height b fn2-run-builds))
                   (equal (fn2-run-writers-ordinal w fn2-run-writers) 0)
                   (fn2-run-below-idle l wbase fn2-run-writers))
              (mv :root l) (mv :promote l)))
         ((equal phase *fn2-run-writer-phase-idle*)
          (if (and (< 0 l) (equal (fn2-run-writers-phase (+ wbase (- l 1)) fn2-run-writers) *fn2-run-writer-phase-sealed*))
              (mv :need-page l)
            (fn2-run-scan (- l 1) b finishing fn2-run-builds fn2-run-writers)))
         ((and finishing (fn2-run-below-idle l wbase fn2-run-writers)) (mv :finish-close l))
         (t (fn2-run-scan (- l 1) b finishing fn2-run-builds fn2-run-writers))))))

(defthm fn2-run-scan-level-natp
 (natp (mv-nth 1 (fn2-run-scan l b finishing fn2-run-builds fn2-run-writers)))
 :rule-classes ((:type-prescription :typed-term (mv-nth 1 (fn2-run-scan l b finishing fn2-run-builds fn2-run-writers)))))

; One bounded unit of pending page work. Returns (mv code level ...): :more
; after work, (:sealed L) once when a page has sealed (its writer row then
; names the page; the caller records it), and without work (:promote L),
; (:need-page L), (:root L) or :idle for the caller to act on.
(defun fn2-run-build-work (b budget fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                             fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (declare (xargs :stobjs (fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
  :guard (and (fn2-run-buildp b fn2-run-builds fn2-run-writers) (fn2-run-restarts-wfp fn2-run-restarts)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-fc-wfp fn2-fc)
              (fn2-fc-context-wfp fn2-fc-context) (fn2-digests-wfp fn2-digests) (natp budget))
  :guard-hints (("Goal" :in-theory (disable fn2-run-scan fn2-run-close-step fn2-run-head fn2-run-seal-step fn2-run-seal-context fn2-run-close
                                            fn2-run-writers-rows fn2-fields-rows fn2-fc-rows fn2-fc-context-rows)))))
 (b* ((finishing (equal (fn2-run-builds-phase b fn2-run-builds) *fn2-run-build-phase-finishing*))
      (height (fn2-run-builds-height b fn2-run-builds))
      ((unless (<= height *fn2-run-max-levels*))
       (mv :bounds 0 fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv action l) (fn2-run-scan (- height 1) b finishing fn2-run-builds fn2-run-writers))
      (w (+ (fn2-run-builds-wbase b fn2-run-builds) l))
      (crow (fn2-run-builds-crow b fn2-run-builds))
      (hrow (+ (fn2-run-builds-hbase b fn2-run-builds) l))
      ((unless (and (natp l) (< w (fn2-run-writers-rows fn2-run-writers))
                    (fn2-run-writerp w fn2-run-writers fn2-run-restarts fn2-fields)
                    (< crow (fn2-fc-rows fn2-fc)) (< crow (fn2-fc-context-rows fn2-fc-context))
                    (unsigned-byte-p 32 hrow)))
       (mv :bounds l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
  (case action
   (:close-step
    (b* (((mv code fn2-run-writers fn2-fields fn2-pool)
          (fn2-run-close-step w budget fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
     (mv (if (member-eq code '(:ok :more)) :more code) l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
   (:head
    (b* (((mv code fn2-run-writers fn2-fields fn2-pool) (fn2-run-head w fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
         ((unless (and (eq code :ok) (< (fn2-digest-slot crow *fn2-fc-previous-seal*) 4294967296)))
          (mv (if (eq code :ok) :bounds code) l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
         (fn2-fc-context (fn2-run-seal-context w crow hrow fn2-run-writers fn2-fc-context)))
     (mv :more l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
   (:seal-step
    (b* (((mv code fn2-run-writers fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
          (fn2-run-seal-step w crow hrow budget fn2-run-writers fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
         (pages (+ 1 (fn2-run-builds-pages b fn2-run-builds)))
         (fn2-run-builds (if (and (eq code :ok) (unsigned-byte-p 60 pages))
                             (fn2-run-builds-set-pages b pages fn2-run-builds) fn2-run-builds)))
     (mv (case code (:ok :sealed) (:more :more) (otherwise code))
         l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
   (:finish-close
    (b* (((mv code fn2-run-writers) (fn2-run-close w fn2-run-writers)))
     (mv (if (eq code :ok) :more code) l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
   (:root
    (let ((fn2-run-builds (fn2-run-builds-set-phase b *fn2-run-build-phase-done* fn2-run-builds)))
     (mv :root l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
   (otherwise
    (mv action l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))))

; Finishing: the remaining open levels close bottom up; an empty run has no
; root and is :empty.
(defun fn2-run-build-finish (b fn2-run-builds)
 (declare (xargs :stobjs fn2-run-builds
  :guard (and (fn2-run-builds-wfp fn2-run-builds) (natp b) (< b (fn2-run-builds-rows fn2-run-builds)))))
 (cond ((not (equal (fn2-run-builds-phase b fn2-run-builds) *fn2-run-build-phase-adding*)) (mv :state fn2-run-builds))
       ((zp (fn2-run-builds-entries b fn2-run-builds))
        (let ((fn2-run-builds (fn2-run-builds-set-phase b *fn2-run-build-phase-done* fn2-run-builds))) (mv :empty fn2-run-builds)))
       (t (let ((fn2-run-builds (fn2-run-builds-set-phase b *fn2-run-build-phase-finishing* fn2-run-builds))) (mv :ok fn2-run-builds)))))

; Promotion, the generic parts. Check: the sealed level L can promote now
; (:go), or the level above needs a page first, growing the height when L is
; the top. Child reference: the parent-held hash goes to the hash slot at
; 32 L and the reference fields are set by the ref layout's field names
; relative to CB, the index layout's CHILD- base. Commit: :full closes the
; parent (the promotion stays pending); :ok idles L for its next page.
(defun fn2-run-promote-check (b l fn2-run-builds fn2-run-writers)
 (declare (xargs :stobjs (fn2-run-builds fn2-run-writers)
  :guard (and (fn2-run-buildp b fn2-run-builds fn2-run-writers) (natp l))))
 (b* ((wbase (fn2-run-builds-wbase b fn2-run-builds))
      ((unless (and (natp l) (< (+ 1 l) *fn2-run-max-levels*) (< l (fn2-run-builds-height b fn2-run-builds))))
       (mv :levels fn2-run-builds))
      ((unless (equal (fn2-run-writers-phase (+ wbase l) fn2-run-writers) *fn2-run-writer-phase-sealed*))
       (mv :state fn2-run-builds))
      ((when (equal (+ 1 l) (fn2-run-builds-height b fn2-run-builds)))
       (let ((fn2-run-builds (fn2-run-builds-set-height b (+ 2 l) fn2-run-builds))) (mv :need-page fn2-run-builds)))
      ((when (equal (fn2-run-writers-phase (+ wbase l 1) fn2-run-writers) *fn2-run-writer-phase-idle*))
       (mv :need-page fn2-run-builds)))
  (mv :go fn2-run-builds)))
(fn2-fc-shape fn2-run-promote-check-shape (fn2-run-promote-check b l fn2-run-builds fn2-run-writers)
 (and (fn2-run-buildsp fn2-run-builds) (fn2-run-writersp fn2-run-writers) (fn2-run-buildp b fn2-run-builds fn2-run-writers))
 ((fn2-run-builds 1)))
(in-theory (disable fn2-run-promote-check))

(defun fn2-run-child-ref (w l cb eb hrow hslot hgen okind oslot ogen fn2-run-writers fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-run-writers fn2-fields fn2-pool fn2-digests)
  :guard (and (fn2-run-writers-wfp fn2-run-writers) (fn2-fields-wfp fn2-fields)
              (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (and (natp w) (natp l) (natp cb) (natp eb) (< l *fn2-run-max-levels*)
                    (< w (fn2-run-writers-rows fn2-run-writers))
                    (<= (+ cb *fn2-format-ref-num-fields*) (fn2-fields-rows fn2-fields))
                    (< eb (fn2-fields-rows fn2-fields))
                    (unsigned-byte-p 32 hslot) (unsigned-byte-p 60 hgen) (fn2-digest-rowp hrow fn2-digests)))
       (mv :bounds fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-digest-store 32 hrow hslot hgen (* 32 l) okind oslot ogen fn2-digests fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields fn2-pool))
      (unit (fn2-run-writers-unit w fn2-run-writers)) (epoch (fn2-run-writers-epoch w fn2-run-writers))
      (counter (fn2-run-writers-counter w fn2-run-writers)) (kind (fn2-run-writers-page-kind w fn2-run-writers))
      (entries (fn2-run-writers-entries w fn2-run-writers)))
  (if (not (and (unsigned-byte-p 60 unit) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 counter)
                (unsigned-byte-p 60 kind) (unsigned-byte-p 60 entries)))
      (mv :bounds fn2-fields fn2-pool)
   (let* ((h (+ cb *fn2-format-ref-field-expected-hash*))
          (fn2-fields (fn2-fields-set-value (+ cb *fn2-format-ref-field-storage-domain*) 0 fn2-fields))
          (fn2-fields (fn2-fields-set-value (+ cb *fn2-format-ref-field-physical-unit*) unit fn2-fields))
          (fn2-fields (fn2-fields-set-value (+ cb *fn2-format-ref-field-writer-epoch*) epoch fn2-fields))
          (fn2-fields (fn2-fields-set-value (+ cb *fn2-format-ref-field-allocation*) counter fn2-fields))
          (fn2-fields (fn2-fields-set-value (+ cb *fn2-format-ref-field-page-kind*) kind fn2-fields))
          (fn2-fields (fn2-fields-set-value (+ cb *fn2-format-ref-field-encoded-length*) *fn2-run-page-size* fn2-fields))
          (fn2-fields (fn2-fields-set-value h 1 fn2-fields))
          (fn2-fields (fn2-fields-set-ref-slot h hslot fn2-fields))
          (fn2-fields (fn2-fields-set-ref-gen h hgen fn2-fields))
          (fn2-fields (fn2-fields-set-ref-off h (* 32 l) fn2-fields))
          (fn2-fields (fn2-fields-set-ref-len h 32 fn2-fields))
          (fn2-fields (fn2-fields-set-value eb entries fn2-fields)))
    (mv :ok fn2-fields fn2-pool)))))
(fn2-fc-shape fn2-run-child-ref-shape
 (fn2-run-child-ref w l cb eb hrow hslot hgen okind oslot ogen fn2-run-writers fn2-fields fn2-pool fn2-digests)
 (and (fn2-run-writersp fn2-run-writers) (fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool) (fn2-digestsp fn2-digests)
      (fn2-run-writers-wfp fn2-run-writers) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))
 ((fn2-fields 1) (fn2-pool 2)))
(in-theory (disable fn2-run-child-ref))

; Commit a promotion of writer W into W+1.
(defun fn2-run-promote-commit (w code fn2-run-writers)
 (declare (xargs :stobjs fn2-run-writers :guard (fn2-run-writers-wfp fn2-run-writers)))
 (b* (((unless (and (natp w) (< (+ 1 w) (fn2-run-writers-rows fn2-run-writers)))) (mv :bounds fn2-run-writers))
      ((when (eq code :full))
       (mv-let (code fn2-run-writers) (fn2-run-close (+ 1 w) fn2-run-writers) (mv (if (eq code :ok) :more code) fn2-run-writers)))
      ((unless (eq code :ok)) (mv code fn2-run-writers))
      (ordinal (+ 1 (fn2-run-writers-ordinal w fn2-run-writers)))
      ((unless (unsigned-byte-p 60 ordinal)) (mv :bounds fn2-run-writers))
      (fn2-run-writers (fn2-run-writers-put w (phase *fn2-run-writer-phase-idle*) (ordinal ordinal))))
  (mv :ok fn2-run-writers)))
(fn2-fc-shape fn2-run-promote-commit-shape (fn2-run-promote-commit w code fn2-run-writers)
 (and (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers))
 ((fn2-run-writers 1)))
(in-theory (disable fn2-run-promote-commit))

;; Inputs one adapter run accepts: at most 64 sorted well-formed entries, and
;; a fill limit at which every page holds at least two entries or index
;; entries, so six levels and the adapter's 160 pages suffice.
(defun fn2-run-run-inputp (layout key entries limit)
 (declare (xargs :verify-guards nil))
 (and (fn2-layoutp layout) (consp entries) (<= (len entries) 64)
      (fn2-run-entries-layoutp layout entries) (fn2-run-sorted-spec key entries)
      (natp limit) (<= limit *fn2-run-page-size*)
      (<= (+ *fn2-run-entries-base*
             (* 2 (+ *fn2-run-restart-bytes*
                     (max (fn2-layout-max-size layout) (fn2-layout-max-size (fn2-rs-index-layout key))))))
          limit)))
;; A scan from the lower bound of Q: the next N entries in key order, then
;; :count, or the entries left, then :end.
(defun fn2-run-from-spec (key entries q)
 (declare (xargs :verify-guards nil))
 (cond ((atom entries) nil)
       ((eq (fn2-run-key-order-spec key (car entries) q) :lt) (fn2-run-from-spec key (cdr entries) q))
       (t entries)))
(defun fn2-run-take-spec (rest n)
 (declare (xargs :verify-guards nil))
 (cond ((zp n) (list :count)) ((atom rest) (list :end))
       (t (cons (car rest) (fn2-run-take-spec (cdr rest) (- n 1))))))
(defun fn2-run-scan-spec (key entries q n)
 (declare (xargs :verify-guards nil))
 (fn2-run-take-spec (fn2-run-from-spec key entries q) n))
(defconst *fn2-run-run-adapter-stobjs*
 '(fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
   fn2-fc fn2-fc-context fn2-b3 fn2-digests))
(defconst *fn2-run-run-entry* 1100)
(defconst *fn2-run-run-reader* 1200)
(defconst *fn2-run-run-query* 1310)
; ---------------------------------------------------------------------------
; Verified-page cache: direct mapped by physical unit, keyed by the exact
; (unit, allocation counter) pair, so a reused unit never answers for an old
; allocation. A page enters only after B's checker accepted it under its
; parent-held hash (or its own seal); a miss names the reference to load.
(defcolumns fn2-run-cache
 ((state (:enum fn2-run-cache-state (:empty :ready)))
  (unit :u60) (counter :u60) (slot :u32) (gen :u60)))
(defun fn2-run-cache-row (unit fn2-run-cache)
 (declare (xargs :stobjs fn2-run-cache :guard (and (fn2-run-cache-wfp fn2-run-cache) (natp unit))))
 (if (zp (fn2-run-cache-rows fn2-run-cache)) 0 (mod unit (fn2-run-cache-rows fn2-run-cache))))
(defun fn2-run-cache-lookup (unit counter fn2-run-cache)
 (declare (xargs :stobjs fn2-run-cache :guard (fn2-run-cache-wfp fn2-run-cache)))
 (b* (((unless (and (natp unit) (< 0 (fn2-run-cache-rows fn2-run-cache)))) (mv :miss 0 0))
      (i (nfix (fn2-run-cache-row unit fn2-run-cache)))
      ((unless (< i (fn2-run-cache-rows fn2-run-cache))) (mv :miss 0 0)))
  (if (and (equal (fn2-run-cache-state i fn2-run-cache) *fn2-run-cache-state-ready*)
           (equal (fn2-run-cache-unit i fn2-run-cache) unit)
           (equal (fn2-run-cache-counter i fn2-run-cache) counter))
      (mv :ok (fn2-run-cache-slot i fn2-run-cache) (fn2-run-cache-gen i fn2-run-cache))
    (mv :miss 0 0))))
(defun fn2-run-cache-install (unit counter slot gen fn2-run-cache)
 (declare (xargs :stobjs fn2-run-cache :guard (fn2-run-cache-wfp fn2-run-cache)))
 (b* (((unless (and (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter) (unsigned-byte-p 32 slot)
                    (unsigned-byte-p 60 gen) (< 0 (fn2-run-cache-rows fn2-run-cache))))
       (mv :bounds fn2-run-cache))
      (i (nfix (fn2-run-cache-row unit fn2-run-cache)))
      ((unless (< i (fn2-run-cache-rows fn2-run-cache))) (mv :bounds fn2-run-cache)))
  (let ((fn2-run-cache (fn2-run-cache-put i (state *fn2-run-cache-state-ready*) (unit unit) (counter counter) (slot slot) (gen gen))))
   (mv :ok fn2-run-cache))))
(fn2-run-cache-preserves fn2-run-cache-install (unit counter slot gen fn2-run-cache) :position 1 :raw-rows t)

; A cursor: one resumable descent from a run's root to level 0, then (for a
; scan) a walk forward over level 0. Each step does at most BUDGET entry
; decodes; the continuation is the row. TOP is the root's level; LEFT means
; the descent takes the leftmost child (a scan moving to the next leaf); UNIT
; and COUNTER name the page the cursor is on.
(defconst *fn2-run-cursor-fields* *fn2-run-reader-fields*)
(defcolumns fn2-run-cursors
 ((phase (:enum fn2-run-cursor-phase (:idle :header :seek :child :miss :found :absent :failed :at :up :end :lost)))
  (schema :u60) (level :u8) (top :u8) (left :bool) (slot :u32) (gen :u60) (lo :u32) (hi :u32) (idx :u32) (off :u32)
  (unit :u60) (counter :u60) (rb :u32) (okind :u8) (oslot :u32) (ogen :u60)))
(defun fn2-run-cursor-start (c schema level slot gen unit counter rb okind oslot ogen fn2-run-cursors)
 (declare (xargs :stobjs fn2-run-cursors :guard (fn2-run-cursors-wfp fn2-run-cursors)))
 (if (not (and (natp c) (< c (fn2-run-cursors-rows fn2-run-cursors)) (unsigned-byte-p 60 schema) (unsigned-byte-p 8 level)
               (< level *fn2-run-max-levels*)
               (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
               (unsigned-byte-p 32 rb) (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
     (mv :bounds fn2-run-cursors)
  (let ((fn2-run-cursors (fn2-run-cursors-put c (phase *fn2-run-cursor-phase-header*) (schema schema) (level level) (top level)
                               (left 0) (slot slot) (gen gen)
                               (lo 0) (hi 0) (idx 0) (off 0) (unit unit) (counter counter) (rb rb)
                               (okind okind) (oslot oslot) (ogen ogen))))
   (mv :ok fn2-run-cursors))))
(fn2-run-cursors-preserves fn2-run-cursor-start (c schema level slot gen unit counter rb okind oslot ogen fn2-run-cursors) :position 1 :raw-rows t)
(defun fn2-run-cursor-set-left (c fn2-run-cursors)
 (declare (xargs :stobjs fn2-run-cursors :guard (fn2-run-cursors-wfp fn2-run-cursors)))
 (if (and (natp c) (< c (fn2-run-cursors-rows fn2-run-cursors)))
     (let ((fn2-run-cursors (fn2-run-cursors-set-left c 1 fn2-run-cursors))) (mv :ok fn2-run-cursors))
   (mv :bounds fn2-run-cursors)))
(fn2-run-cursors-preserves fn2-run-cursor-set-left (c fn2-run-cursors) :position 1 :raw-rows t)

; A cursor's path: row C * levels + L names the page the descent visited at
; level L (its slot, generation and physical identity), its entry count, and
; the index entry the descent took. A scan moves to the next leaf through it.
(defcolumns fn2-run-paths
 ((slot :u32) (gen :u60) (unit :u60) (counter :u60) (idx :u32) (entries :u32)))
(defun fn2-run-path-row (c level)
 (declare (xargs :guard (and (natp c) (natp level))))
 (+ (* c *fn2-run-max-levels*) level))
(defun fn2-run-path-note (c level slot gen unit counter entries fn2-run-paths)
 (declare (xargs :stobjs fn2-run-paths :guard (fn2-run-paths-wfp fn2-run-paths)))
 (if (not (and (natp c) (natp level) (< level *fn2-run-max-levels*)
               (< (fn2-run-path-row c level) (fn2-run-paths-rows fn2-run-paths))
               (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 60 unit)
               (unsigned-byte-p 60 counter) (unsigned-byte-p 32 entries)))
     (mv :bounds fn2-run-paths)
  (let ((fn2-run-paths (fn2-run-paths-put (fn2-run-path-row c level) (slot slot) (gen gen) (unit unit)
                                          (counter counter) (idx 0) (entries entries))))
   (mv :ok fn2-run-paths))))
(fn2-run-paths-preserves fn2-run-path-note (c level slot gen unit counter entries fn2-run-paths) :position 1 :raw-rows t)
(defun fn2-run-path-take (c level idx fn2-run-paths)
 (declare (xargs :stobjs fn2-run-paths :guard (fn2-run-paths-wfp fn2-run-paths)))
 (if (not (and (natp c) (natp level) (< level *fn2-run-max-levels*)
               (< (fn2-run-path-row c level) (fn2-run-paths-rows fn2-run-paths)) (unsigned-byte-p 32 idx)))
     (mv :bounds fn2-run-paths)
  (let ((fn2-run-paths (fn2-run-paths-set-idx (fn2-run-path-row c level) idx fn2-run-paths)))
   (mv :ok fn2-run-paths))))
(fn2-run-paths-preserves fn2-run-path-take (c level idx fn2-run-paths) :position 1 :raw-rows t)
(defthm fn2-run-path-row-natp
 (implies (and (natp c) (natp level)) (natp (fn2-run-path-row c level)))
 :rule-classes :type-prescription)
(in-theory (disable fn2-run-path-row))
; Save a cursor's continuation after a step; a value out of width is a
; refusal by name, never a silent no-op.
(defun fn2-run-cursor-save (c phase level slot gen lo hi idx off unit counter fn2-run-cursors)
 (declare (xargs :stobjs fn2-run-cursors :guard (fn2-run-cursors-wfp fn2-run-cursors)))
 (if (not (and (natp c) (< c (fn2-run-cursors-rows fn2-run-cursors))
               (natp phase) (< phase *fn2-run-cursor-phase-count*) (unsigned-byte-p 8 level) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
               (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi) (unsigned-byte-p 32 idx) (unsigned-byte-p 32 off)
               (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)))
     (mv :bounds fn2-run-cursors)
  (let ((fn2-run-cursors (fn2-run-cursors-put c (phase phase) (level level) (slot slot) (gen gen) (lo lo) (hi hi)
                               (idx idx) (off off) (unit unit) (counter counter))))
   (mv :ok fn2-run-cursors))))
(fn2-run-cursors-preserves fn2-run-cursor-save (c phase level slot gen lo hi idx off unit counter fn2-run-cursors) :position 1 :raw-rows t)

; Fixture plan of the run-level logic adapter (the assembly's fn2-run-run-run).
(defun fn2-run-run-setup (fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (declare (xargs :stobjs (fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                          fn2-fc fn2-fc-context fn2-b3 fn2-digests) :verify-guards nil))
 (b* ((fn2-run-builds (fn2-run-builds-init 1 fn2-run-builds))
      (fn2-run-cursors (fn2-run-cursors-init 1 fn2-run-cursors))
      (fn2-run-paths (fn2-run-paths-init *fn2-run-max-levels* fn2-run-paths))
      (fn2-run-cache (fn2-run-cache-init 256 fn2-run-cache))
      (fn2-run-writers (fn2-run-writers-init *fn2-run-max-levels* fn2-run-writers))
      (fn2-run-restarts (fn2-run-restarts-init (* *fn2-run-max-levels* *fn2-run-restart-capacity*) fn2-run-restarts))
      (fn2-fields (fn2-fields-init 1400 fn2-fields))
      (fn2-pool (fn2-pool-init '((160 . 65536) (3 . 65536)) 1 100 fn2-pool))
      (fn2-fc (fn2-fc-init 1 fn2-fc))
      (fn2-fc-context (fn2-fc-context-init 1 fn2-fc-context))
      (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
      (fn2-digests (fn2-digests-init 150 fn2-digests)))
  (mv fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
      fn2-fc fn2-fc-context fn2-b3 fn2-digests)))

; ---------------------------------------------------------------------------
; Installed runs: the engine's resident view of each schema's sealed runs (the
; manifest, C1c, makes it durable). A row names a run's root page (its level,
; cache slot and physical identity, the owner its pages are read under) and
; its entry count.
(defcolumns fn2-run-installed
 ((state (:enum fn2-run-installed-state (:free :live)))
  (schema :u60) (run :u60) (top :u8) (slot :u32) (gen :u60) (unit :u60) (counter :u60) (entries :u60)
  (okind :u8) (oslot :u32) (ogen :u60)))
(defun fn2-run-install (r schema run top slot gen unit counter entries okind oslot ogen fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :guard (fn2-run-installed-wfp fn2-run-installed)))
 (b* (((unless (and (natp r) (< r (fn2-run-installed-rows fn2-run-installed))
                    (unsigned-byte-p 60 schema) (unsigned-byte-p 60 run) (unsigned-byte-p 8 top)
                    (< top *fn2-run-max-levels*) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                    (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter) (unsigned-byte-p 60 entries)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds fn2-run-installed))
      ((unless (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*))
       (mv :state fn2-run-installed))
      (fn2-run-installed (fn2-run-installed-put r (state *fn2-run-installed-state-live*) (schema schema) (run run)
                           (top top) (slot slot) (gen gen) (unit unit) (counter counter) (entries entries)
                           (okind okind) (oslot oslot) (ogen ogen))))
  (mv :ok fn2-run-installed)))
(fn2-run-installed-preserves fn2-run-install (r schema run top slot gen unit counter entries okind oslot ogen fn2-run-installed) :position 1 :raw-rows t)
