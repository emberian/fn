; Layer C in the served core, seam C-S3 (fn2/docs/c-ordered-runs.md §8 item 8),
; stage (every write slot against the tip, then room) and out. The tables
; and the :prepare half are machines-c-successor.lisp's; bind, release,
; publication, the defcosts and the core wrappers machines-c-bind.lisp's
; (C-SUCCESSOR-BOOK).
(in-package "ACL2")
(include-book "machines-c-successor")
(fn2-book-layer :c)
(local (in-theory (disable fn2-run-layout-fields fn2-run-layout-keys fn2-run-layout-merge fn2-run-layout-size
                           fn2-fold-key-arg fn2-fold-arity fn2-fold-assigned-p fn2-run-layout-octets-max
                           fn2-run-layout-value-ok fn2-run-layout-fold-p fn2-run-version fn2-succ-bit fn2-succ-has)))

; ---------------------------------------------------------------------------
; Stage (in the :ready arm): every slot in order against the tip, then room.
; The tip of a key is its newest row: in the overlays of its schema (a
; batch's private ones, published ones, active ones), the one taken last
; (greatest SEQ) holding it; else the row resolve read from the installed
; runs if their version has not moved (else :stale); else none (zeros).

; Args 0..N-1 of a slot from SRC into DST: an :out arg reads its slot's
; staged row (field F of slot K, at B0 + 48K + F), an :event arg is 0 until
; bind, any other is copied (value and octet reference).
(defun fn2-succ-eval-arg (j src dst b0 outs events fn2-fields)
 (declare (xargs :stobjs fn2-fields :guard (and (fn2-fields-wfp fn2-fields) (natp j) (natp src) (natp dst) (natp b0))))
 (b* (((unless (and (natp j) (natp src) (natp dst) (natp b0) (< (+ src j) (fn2-fields-rows fn2-fields))
                    (< (+ dst j) (fn2-fields-rows fn2-fields))))
       fn2-fields)
      ((unless (fn2-succ-has outs j))
       (if (fn2-succ-has events j) (fn2-fields-put (+ dst j) (value 0) (ref-len 0))
         (fn2-succ-copy-row (+ src j) (+ dst j) fn2-fields)))
      (h (fn2-fields-value (+ src j) fn2-fields))
      (row (+ b0 (* *fn2-succ-block* (floor h 256)) (mod h 256)))
      ((unless (and (natp row) (< row (fn2-fields-rows fn2-fields)))) fn2-fields))
  (fn2-fields-put (+ dst j) (value (fn2-fields-value row fn2-fields)) (ref-len 0))))
(fn2-fields-preserves fn2-succ-eval-arg (j src dst b0 outs events fn2-fields) :position nil :raw-rows t)
(defun fn2-succ-eval-args (k j src dst b0 outs events fn2-fields)
 (declare (xargs :stobjs fn2-fields :measure (nfix k)
  :guard (and (fn2-fields-wfp fn2-fields) (natp k) (natp j) (natp src) (natp dst) (natp b0))))
 (if (or (zp k) (not (and (natp j) (natp src) (natp dst) (natp b0)))) fn2-fields
  (let ((fn2-fields (fn2-succ-eval-arg j src dst b0 outs events fn2-fields)))
   (fn2-succ-eval-args (- k 1) (+ 1 j) src dst b0 outs events fn2-fields))))
(fn2-fields-preserves fn2-succ-eval-args (k j src dst b0 outs events fn2-fields) :position nil :raw-rows t)

; Whether integer fields J..N-1 of the row at ENTRY fit schema SID.
(defun fn2-succ-fits (k j sid entry fn2-fields)
 (declare (xargs :stobjs fn2-fields :measure (nfix k) :guard (and (fn2-fields-wfp fn2-fields) (natp j) (natp entry))))
 (or (not (posp k))
     (and (natp j) (natp entry) (< (+ entry j) (fn2-fields-rows fn2-fields))
          (or (fn2-run-layout-octets-max sid j) (fn2-run-layout-value-ok sid j (fn2-fields-value (+ entry j) fn2-fields)))
          (fn2-succ-fits (- k 1) (+ 1 j) sid entry fn2-fields))))
; The mask of a fold event's args that are not assigned, J..N-1.
(defun fn2-succ-required (k j sid kw)
 (declare (xargs :guard (natp j) :measure (nfix k)))
 (if (or (not (posp k)) (not (natp j)) (<= 32 j)) 0
  (logior (if (fn2-fold-assigned-p sid kw j) 0 (fn2-succ-bit j)) (nfix (fn2-succ-required (- k 1) (+ 1 j) sid kw)))))

; The overlay holding the key at QBASE newest (greatest SEQ) among the
; readable or private overlays of SID, rows O.. (K of them): (mv code best
; pos fields), BEST the row count when none does. EB is decode scratch.
(defun fn2-succ-tip-scan (k o sid qbase eb qk qs qg best bpos fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-overlays fn2-overlay-index fn2-fields fn2-pool) :measure (nfix k)
  :guard (and (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fields-wfp fn2-fields)
              (fn2-pool-wfp fn2-pool) (natp o))
  :guard-hints (("Goal" :in-theory (disable fn2-ov-locate fn2-fields-rows fn2-overlays-rows)))))
 (b* (((unless (and (posp k) (natp o) (< o (fn2-overlays-rows fn2-overlays)))) (mv :ok best bpos fn2-fields))
      ((unless (and (equal (fn2-overlays-schema o fn2-overlays) sid)
                    (member (fn2-overlays-phase o fn2-overlays)
                            (list *fn2-overlay-phase-active* *fn2-overlay-phase-frozen* *fn2-overlay-phase-private*))))
       (fn2-succ-tip-scan (- k 1) (+ 1 o) sid qbase eb qk qs qg best bpos fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code pos order fn2-fields) (fn2-ov-locate o eb qbase qk qs qg fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code best bpos fn2-fields))
      (newer (and (eq order :eq)
                  (or (not (and (natp best) (< best (fn2-overlays-rows fn2-overlays))))
                      (< (nfix (fn2-overlays-seq best fn2-overlays)) (nfix (fn2-overlays-seq o fn2-overlays)))))))
  (fn2-succ-tip-scan (- k 1) (+ 1 o) sid qbase eb qk qs qg (if newer o best) (if newer pos bpos)
                     fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
(fn2-idc-op-shape fn2-succ-tip-scan (k o sid qbase eb qk qs qg best bpos fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 ((fn2-fields 3)) ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)) :min
 (fn2-ov-locate fn2-overlays-schema fn2-overlays-phase fn2-overlays-seq))
(in-theory (disable fn2-succ-tip-scan))

; Stage record slot S (slot I) of TX: decision TX's verdict against the
; published state (as C-S1/C-S2: :stale, :duplicate, :evidence,
; :identity-conflict-bound), its article and principal evaluated, its size.
(defun fn2-succ-stage-record (tx i s b0 fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-fields)
 (declare (xargs :stobjs (fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-fields)
  :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (fn2-id-decides-wfp fn2-id-decides) (fn2-id-stamps-wfp fn2-id-stamps)
              (fn2-run-installed-wfp fn2-run-installed) (fn2-id-engine-wfp fn2-id-engine) (fn2-fields-wfp fn2-fields)
              (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp i) (natp b0))
  :guard-hints (("Goal" :in-theory (disable fn2-succ-eval-args fn2-fields-rows)))))
 (b* (((unless (and (natp tx) (< tx (fn2-id-decides-rows fn2-id-decides)) (< 0 (fn2-id-engine-rows fn2-id-engine))
                    (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp i) (< i *fn2-succ-slots*) (natp b0)
                    (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-succ-slots fn2-fields))
      ((unless (equal (fn2-id-decides-phase tx fn2-id-decides) *fn2-id-decide-phase-done*)) (mv :state fn2-succ-slots fn2-fields))
      ((unless (equal (logand (nfix (fn2-succ-slots-set s fn2-succ-slots)) 3) 3)) (mv :state fn2-succ-slots fn2-fields))
      (bucket (fn2-id-decides-bucket tx fn2-id-decides))
      ((unless (< bucket (fn2-id-stamps-rows fn2-id-stamps))) (mv :bounds fn2-succ-slots fn2-fields))
      ((unless (and (equal (fn2-id-stamps-gen bucket fn2-id-stamps) (fn2-id-decides-stamp tx fn2-id-decides))
                    (equal (fn2-run-version 1 (fn2-run-installed-rows fn2-run-installed) fn2-run-installed)
                           (fn2-id-decides-vrun tx fn2-id-decides))))
       (mv :stale fn2-succ-slots fn2-fields))
      ((when (equal (fn2-id-decides-exact tx fn2-id-decides) 1)) (mv :duplicate fn2-succ-slots fn2-fields))
      ((when (equal (fn2-id-decides-exact tx fn2-id-decides) 2)) (mv :evidence fn2-succ-slots fn2-fields))
      ((unless (< (fn2-id-decides-others tx fn2-id-decides) *fn2-identity-contents-max*))
       (mv :identity-conflict-bound fn2-succ-slots fn2-fields))
      (entry (+ b0 (* *fn2-succ-block* i)))
      (fn2-fields (fn2-succ-eval-args 2 0 (+ entry *fn2-succ-raw*) (+ entry *fn2-succ-eval*) b0
                                      (fn2-succ-slots-outs s fn2-succ-slots) 0 fn2-fields))
      (mrow (+ b0 *fn2-idc-q* *fn2-id-mid*))
      ((unless (< mrow (fn2-fields-rows fn2-fields))) (mv :bounds fn2-succ-slots fn2-fields))
      (mlen (fn2-fields-ref-len mrow fn2-fields))
      (size (+ (nfix mlen) 32 *fn2-idc-entry-overhead*))
      ((unless (and (<= size (nfix (fn2-id-engine-arena 0 fn2-id-engine))) (unsigned-byte-p 32 size)))
       (mv :capacity fn2-succ-slots fn2-fields))
      (fn2-succ-slots (fn2-succ-slots-set-size s size fn2-succ-slots)))
  (mv :ok fn2-succ-slots fn2-fields)))
(fn2-idc-fn-shape fn2-succ-stage-record (tx i s b0 fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-fields)
 (fn2-succ-slots fn2-fields) (fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-fields) t
 (fn2-id-decides-phase fn2-id-decides-bucket fn2-id-decides-stamp fn2-id-decides-vrun fn2-id-decides-exact fn2-id-decides-others
  fn2-id-stamps-gen fn2-run-version fn2-succ-slots-set fn2-succ-slots-outs fn2-fields-ref-len fn2-id-engine-arena fn2-succ-eval-args))

; Stage insert slot S (slot I) of TX: its entry from its args, its integer
; fields within their widths (:range), and, for a key resolve read, not held
; at the tip (:duplicate; a key with an :out or :event arg is fresh by
; construction and bind's insert refuses a duplicate); its size, a late
; octet arg counted at its bound (C-S3a); its late args unfilled.
(defun fn2-succ-stage-insert (i s b0 fn2-succ-slots fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-slots fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
  :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (fn2-run-installed-wfp fn2-run-installed) (fn2-overlays-wfp fn2-overlays)
              (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp i) (natp b0))
  :guard-hints (("Goal" :in-theory (disable fn2-succ-eval-args fn2-succ-tip-scan fn2-succ-fits fn2-run-layout-size fn2-fields-rows)))))
 (b* (((unless (and (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp i) (< i *fn2-succ-slots*) (natp b0)
                    (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-succ-slots fn2-fields))
      (sid (fn2-succ-slots-sid s fn2-succ-slots)) (nf (nfix (fn2-run-layout-fields sid 0)))
      ((unless (equal (logand (nfix (fn2-succ-slots-set s fn2-succ-slots)) (- (ash 1 nf) 1)) (- (ash 1 nf) 1)))
       (mv :state fn2-succ-slots fn2-fields))
      (entry (+ b0 (* *fn2-succ-block* i)))
      (fn2-fields (fn2-succ-eval-args nf 0 (+ entry *fn2-succ-raw*) entry b0 (fn2-succ-slots-outs s fn2-succ-slots)
                                      (fn2-succ-slots-events s fn2-succ-slots) fn2-fields))
      ((unless (fn2-succ-fits nf 0 sid entry fn2-fields)) (mv :range fn2-succ-slots fn2-fields))
      ((mv code fn2-fields)
       (if (fn2-succ-reads-key s fn2-succ-slots)
           (b* ((rows (fn2-overlays-rows fn2-overlays))
                ((mv code best & fn2-fields)
                 (if (equal (fn2-succ-slots-oset s fn2-succ-slots) 1)
                     (fn2-succ-tip-scan rows 0 sid entry (+ b0 *fn2-idc-eb*) (fn2-succ-slots-sk s fn2-succ-slots)
                                        (fn2-succ-slots-ss s fn2-succ-slots) (fn2-succ-slots-sg s fn2-succ-slots) rows 0
                                        fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
                   (fn2-succ-tip-scan rows 0 sid entry (+ b0 *fn2-idc-eb*) *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen*
                                      rows 0 fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
                ((unless (eq code :ok)) (mv code fn2-fields))
                ((when (and (natp best) (< best rows))) (mv :duplicate fn2-fields))
                ((unless (equal (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed)
                                (fn2-succ-slots-vrun s fn2-succ-slots)))
                 (mv :stale fn2-fields))
                ((when (equal (fn2-succ-slots-found s fn2-succ-slots) 1)) (mv :duplicate fn2-fields)))
            (mv :ok fn2-fields))
         (mv :ok fn2-fields)))
      ((unless (eq code :ok)) (mv code fn2-succ-slots fn2-fields))
      ((unless (<= (+ entry *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))) (mv :bounds fn2-succ-slots fn2-fields))
      (size (fn2-run-layout-size sid 0 entry fn2-fields))
      ((unless (unsigned-byte-p 32 size)) (mv :capacity fn2-succ-slots fn2-fields))
      ; A late arg is filled again after every stage (its entry row was just
      ; recopied from the raw row, which holds only its bound).
      (fn2-succ-slots (fn2-succ-slots-put s (size size) (filled 0))))
  (mv :ok fn2-succ-slots fn2-fields)))
(fn2-idc-fn-shape fn2-succ-stage-insert (i s b0 fn2-succ-slots fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-succ-slots fn2-fields) (fn2-succ-slots fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-succ-slots-sid fn2-succ-slots-set fn2-succ-slots-outs fn2-succ-slots-events fn2-succ-slots-oset fn2-succ-slots-sk
  fn2-succ-slots-ss fn2-succ-slots-sg fn2-succ-slots-vrun fn2-succ-slots-found fn2-run-layout-fields fn2-succ-eval-args
  fn2-succ-fits fn2-succ-reads-key fn2-succ-tip-scan fn2-run-version fn2-run-layout-size))

; Stage fold slot S (slot I) of TX: its event's args evaluated, the key's
; row at the tip into the slot's row, the assigned args computed from it, the
; fold's served step applied (:refused, :range), the key within its widths;
; its size.
(defun fn2-succ-stage-fold (i s b0 fn2-succ-slots fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-slots fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
  :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (fn2-run-installed-wfp fn2-run-installed) (fn2-overlays-wfp fn2-overlays)
              (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp i) (natp b0))
  :guard-hints (("Goal" :in-theory (disable fn2-succ-eval-args fn2-succ-tip-scan fn2-succ-fits fn2-run-layout-size fn2-fields-rows
                                            fn2-succ-key-rows fn2-ov-entry fn2-succ-copy-rows fn2-succ-zero-rows fn2-fold-assign
                                            fn2-fold-apply)))))
 (b* (((unless (and (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp i) (< i *fn2-succ-slots*) (natp b0)
                    (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-succ-slots fn2-fields))
      (sid (fn2-succ-slots-sid s fn2-succ-slots)) (kw (fn2-succ-kindkw (fn2-succ-slots-kind s fn2-succ-slots)))
      (n (nfix (fn2-fold-arity sid kw))) (req (fn2-succ-required n 0 sid kw))
      ((unless (equal (logand (nfix (fn2-succ-slots-set s fn2-succ-slots)) req) req)) (mv :state fn2-succ-slots fn2-fields))
      (entry (+ b0 (* *fn2-succ-block* i))) (args (+ entry *fn2-succ-eval*))
      (nk (nfix (fn2-run-layout-keys sid))) (nv (nfix (- (fn2-run-layout-fields sid 0) nk)))
      (fn2-fields (fn2-succ-eval-args n 0 (+ entry *fn2-succ-raw*) args b0 (fn2-succ-slots-outs s fn2-succ-slots) 0 fn2-fields))
      (fn2-fields (fn2-succ-key-rows nk 0 nk sid kw nil args entry fn2-fields))
      (rows (fn2-overlays-rows fn2-overlays))
      ((mv code best pos fn2-fields)
       (fn2-succ-tip-scan rows 0 sid entry (+ b0 *fn2-idc-eb*) *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen*
                          rows 0 fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-succ-slots fn2-fields))
      ((mv code fn2-fields)
       (cond ((and (natp best) (< best rows) (natp pos))
              (mv-let (code end fn2-fields) (fn2-ov-entry best pos entry fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
               (declare (ignore end))
               (mv code fn2-fields)))
             ((not (equal (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed)
                          (fn2-succ-slots-vrun s fn2-succ-slots)))
              (mv :stale fn2-fields))
             ((equal (fn2-succ-slots-found s fn2-succ-slots) 1)
              (let ((fn2-fields (fn2-succ-copy-rows nv (+ entry *fn2-succ-res*) (+ entry nk) fn2-fields))) (mv :ok fn2-fields)))
             (t (let ((fn2-fields (fn2-succ-zero-rows nv (+ entry nk) fn2-fields))) (mv :ok fn2-fields)))))
      ((unless (eq code :ok)) (mv code fn2-succ-slots fn2-fields))
      ((mv code fn2-fields) (fn2-fold-assign sid kw entry args fn2-fields))
      ((unless (eq code :ok)) (mv code fn2-succ-slots fn2-fields))
      ((mv code fn2-fields) (fn2-fold-apply sid kw entry args fn2-fields))
      ((unless (eq code :ok)) (mv code fn2-succ-slots fn2-fields))
      ((unless (fn2-succ-fits nk 0 sid entry fn2-fields)) (mv :range fn2-succ-slots fn2-fields))
      ((unless (<= (+ entry *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))) (mv :bounds fn2-succ-slots fn2-fields))
      (size (fn2-run-layout-size sid 0 entry fn2-fields))
      ((unless (unsigned-byte-p 32 size)) (mv :capacity fn2-succ-slots fn2-fields))
      (fn2-succ-slots (fn2-succ-slots-set-size s size fn2-succ-slots)))
  (mv :ok fn2-succ-slots fn2-fields)))
(fn2-idc-fn-shape fn2-succ-stage-fold (i s b0 fn2-succ-slots fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-succ-slots fn2-fields) (fn2-succ-slots fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-succ-slots-sid fn2-succ-slots-kind fn2-succ-slots-set fn2-succ-slots-outs fn2-succ-slots-vrun fn2-succ-slots-found
  fn2-succ-kindkw fn2-fold-arity fn2-succ-required fn2-run-layout-keys fn2-run-layout-fields fn2-succ-eval-args fn2-succ-key-rows
  fn2-succ-tip-scan fn2-ov-entry fn2-run-version fn2-succ-copy-rows fn2-succ-zero-rows fn2-fold-assign fn2-fold-apply
  fn2-succ-fits fn2-run-layout-size))

;; Every slot of TX from I (K of them), in order: (mv code i slots fields).
(defun fn2-succ-stage-slots (k i tx b0 fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine
                             fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-overlays
                          fn2-overlay-index fn2-fields fn2-pool) :measure (nfix k)
  :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (fn2-id-decides-wfp fn2-id-decides) (fn2-id-stamps-wfp fn2-id-stamps)
              (fn2-run-installed-wfp fn2-run-installed) (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays)
              (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (natp i) (natp tx) (natp b0))
  :guard-hints (("Goal" :in-theory (disable fn2-succ-stage-record fn2-succ-stage-insert fn2-succ-stage-fold fn2-succ-slots-rows)))))
 (b* (((unless (and (posp k) (natp i) (< i *fn2-succ-slots*))) (mv :ok 0 fn2-succ-slots fn2-fields))
      (s (+ (* (nfix tx) *fn2-succ-slots*) i))
      ((unless (< s (fn2-succ-slots-rows fn2-succ-slots))) (mv :bounds i fn2-succ-slots fn2-fields))
      (code (fn2-succ-slots-kind s fn2-succ-slots))
      ((mv c fn2-succ-slots fn2-fields)
       (cond ((equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*) (mv :ok fn2-succ-slots fn2-fields))
             ((equal code *fn2-succ-kind-record*)
              (fn2-succ-stage-record tx i s b0 fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-fields))
             ((equal code *fn2-succ-kind-insert*)
              (fn2-succ-stage-insert i s b0 fn2-succ-slots fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
             (t (fn2-succ-stage-fold i s b0 fn2-succ-slots fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool))))
      ((unless (eq c :ok)) (mv c i fn2-succ-slots fn2-fields)))
  (fn2-succ-stage-slots (- k 1) (+ 1 i) tx b0 fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine
                        fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-succ-stage-slots (k i tx b0 fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine
                                        fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 ((fn2-succ-slots 2) (fn2-fields 3))
 (fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-succ-slots-kind fn2-succ-slots-phase fn2-succ-stage-record fn2-succ-stage-insert fn2-succ-stage-fold))
(defthm fn2-succ-stage-slots-natp
 (natp (mv-nth 1 (fn2-succ-stage-slots k i tx b0 fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine
                                       fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
 :hints (("Goal" :in-theory (enable fn2-succ-stage-slots))) :rule-classes :type-prescription)

; Room. A transaction's rows of one schema fit one empty overlay together
; (bytes within the arena, entries within an overlay's index: else
; :capacity), so bind needs at most one fresh overlay per schema it writes:
; stage holds that many spares.
(defun fn2-succ-schema-sum (k j tx sid fn2-succ-slots)
 (declare (xargs :stobjs fn2-succ-slots :measure (nfix k) :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (natp j) (natp tx))))
 (b* (((unless (and (posp k) (natp j) (< j *fn2-succ-slots*))) (mv 0 0))
      (s (+ (* (nfix tx) *fn2-succ-slots*) j))
      ((mv bytes count) (fn2-succ-schema-sum (- k 1) (+ 1 j) tx sid fn2-succ-slots))
      (bytes (nfix bytes)) (count (nfix count))
      ((unless (and (< s (fn2-succ-slots-rows fn2-succ-slots))
                    (not (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*))
                    (equal (fn2-succ-slots-sid s fn2-succ-slots) sid)))
       (mv bytes count)))
  (mv (+ bytes (nfix (fn2-succ-slots-size s fn2-succ-slots))) (+ 1 count))))
(defthm fn2-succ-schema-sum-natp
 (and (natp (mv-nth 0 (fn2-succ-schema-sum k j tx sid fn2-succ-slots))) (natp (mv-nth 1 (fn2-succ-schema-sum k j tx sid fn2-succ-slots))))
 :rule-classes ((:type-prescription :corollary (natp (mv-nth 0 (fn2-succ-schema-sum k j tx sid fn2-succ-slots))))
                (:type-prescription :corollary (natp (mv-nth 1 (fn2-succ-schema-sum k j tx sid fn2-succ-slots))))))
(defun fn2-succ-seen (k j i tx sid fn2-succ-slots)
 (declare (xargs :stobjs fn2-succ-slots :measure (nfix k) :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (natp j) (natp tx))))
 (and (posp k) (natp j) (< j (nfix i))
      (let ((s (+ (* (nfix tx) *fn2-succ-slots*) j)))
       (or (and (< s (fn2-succ-slots-rows fn2-succ-slots))
                (not (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*))
                (equal (fn2-succ-slots-sid s fn2-succ-slots) sid))
           (fn2-succ-seen (- k 1) (+ 1 j) i tx sid fn2-succ-slots)))))
(defun fn2-succ-room (k i tx arena icap need fn2-succ-slots)
 (declare (xargs :stobjs fn2-succ-slots :measure (nfix k) :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (natp i) (natp tx) (natp need))))
 (b* (((unless (and (posp k) (natp i) (< i *fn2-succ-slots*))) (mv :ok (nfix need)))
      (s (+ (* (nfix tx) *fn2-succ-slots*) i))
      ((unless (and (< s (fn2-succ-slots-rows fn2-succ-slots))
                    (not (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*))))
       (fn2-succ-room (- k 1) (+ 1 i) tx arena icap need fn2-succ-slots))
      (sid (fn2-succ-slots-sid s fn2-succ-slots))
      ((when (fn2-succ-seen i 0 i tx sid fn2-succ-slots)) (fn2-succ-room (- k 1) (+ 1 i) tx arena icap need fn2-succ-slots))
      ((mv bytes count) (fn2-succ-schema-sum (- *fn2-succ-slots* i) i tx sid fn2-succ-slots))
      ((unless (and (<= (nfix bytes) (nfix arena)) (<= (nfix count) (nfix icap)))) (mv :capacity (nfix need))))
  (fn2-succ-room (- k 1) (+ 1 i) tx arena icap (+ 1 (nfix need)) fn2-succ-slots)))
(defthm fn2-succ-room-natp
 (natp (mv-nth 1 (fn2-succ-room k i tx arena icap need fn2-succ-slots))) :rule-classes :type-prescription)
(in-theory (disable fn2-succ-schema-sum fn2-succ-seen fn2-succ-room))

; Hold the bind scratch (once): :ok, or :full when the pool has none.
(defun fn2-idc-scratch (fn2-id-engine fn2-pool)
 (declare (xargs :stobjs (fn2-id-engine fn2-pool) :guard (and (fn2-id-engine-wfp fn2-id-engine) (fn2-pool-wfp fn2-pool)) :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert fn2-ov-insert
                                             fn2-ov-locate fn2-ov-entry fn2-run-copy-row fn2-fold-apply fn2-fold-assign
                                             fn2-run-layout-size fn2-run-lookup-step fn2-run-cursor-start
                                             fn2-fields-rows fn2-succ-slots-rows fn2-succ-txns-rows fn2-overlays-rows)))))
 (b* (((unless (< 0 (fn2-id-engine-rows fn2-id-engine))) (mv :state fn2-id-engine fn2-pool))
      ((when (equal (fn2-id-engine-scratch 0 fn2-id-engine) 1)) (mv :ok fn2-id-engine fn2-pool))
      (class (fn2-pool-class-for *fn2-idc-scratch-bytes* fn2-pool))
      ((unless (natp class)) (mv :capacity fn2-id-engine fn2-pool))
      ((mv code slot gen fn2-pool) (fn2-pool-reserve class *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
      ((unless (eq code :ok)) (mv (if (eq code :exhausted) :full code) fn2-id-engine fn2-pool))
      ((unless (and (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))) (mv :bounds fn2-id-engine fn2-pool))
      (fn2-id-engine (fn2-id-engine-put 0 (scratch 1) (slot slot) (gen gen))))
  (mv :ok fn2-id-engine fn2-pool)))
(fn2-idc-fn-shape fn2-idc-scratch (fn2-id-engine fn2-pool) (fn2-id-engine fn2-pool) (fn2-id-engine fn2-pool))

; One more spare overlay (an engine arena, not yet any batch's): :ok, :full
; when no overlay row or arena is free, :capacity when no pool class holds
; the arena.
(defun fn2-idc-add-spare (fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool)
 (declare (xargs :stobjs (fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool)
  :guard (and (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert fn2-ov-insert
                                             fn2-ov-locate fn2-ov-entry fn2-run-copy-row fn2-fold-apply fn2-fold-assign
                                             fn2-run-layout-size fn2-run-lookup-step fn2-run-cursor-start
                                             fn2-fields-rows fn2-succ-slots-rows fn2-succ-txns-rows fn2-overlays-rows)))))
 (b* ((rows (fn2-overlays-rows fn2-overlays))
      (o (fn2-idc-find-overlay rows 0 *fn2-overlay-phase-free* 0 fn2-overlays))
      ((unless (and (< o rows) (< 0 (fn2-id-engine-rows fn2-id-engine)) (posp rows))) (mv :full fn2-overlays fn2-pool))
      (arena (fn2-id-engine-arena 0 fn2-id-engine))
      ((unless (natp arena)) (mv :state fn2-overlays fn2-pool))
      (class (fn2-pool-class-for arena fn2-pool))
      ((unless (natp class)) (mv :capacity fn2-overlays fn2-pool))
      ((mv code slot gen fn2-pool) (fn2-pool-reserve class *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
      ((unless (eq code :ok)) (mv (if (eq code :exhausted) :full code) fn2-overlays fn2-pool))
      (icap (floor (fn2-overlay-index-rows fn2-overlay-index) rows))
      ((mv code fn2-overlays fn2-pool)
       (fn2-ov-start o 0 slot gen (* o icap) icap *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* 0
                     fn2-overlays fn2-overlay-index fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-overlays fn2-pool)))
  (mv-let (code fn2-overlays) (fn2-ov-advance o *fn2-overlay-phase-active* *fn2-overlay-phase-spare* fn2-overlays)
   (mv code fn2-overlays fn2-pool))))
(fn2-idc-fn-shape fn2-idc-add-spare (fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool) (fn2-overlays fn2-pool)
 (fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool))
; At least NEED spares (K tries).
(defun fn2-idc-hold-spares (k need fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool)
 (declare (xargs :stobjs (fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool) :measure (nfix k)
  :guard (and (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
              (fn2-pool-wfp fn2-pool) (natp k))
  :guard-hints (("Goal" :in-theory (disable fn2-idc-add-spare fn2-overlays-rows)))))
 (cond ((<= (nfix need) (fn2-idc-count-overlays (fn2-overlays-rows fn2-overlays) 0 *fn2-overlay-phase-spare* fn2-overlays))
        (mv :ok fn2-overlays fn2-pool))
       ((zp k) (mv :full fn2-overlays fn2-pool))
       (t (b* (((mv code fn2-overlays fn2-pool) (fn2-idc-add-spare fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool))
               ((unless (eq code :ok)) (mv code fn2-overlays fn2-pool)))
           (fn2-idc-hold-spares (- k 1) need fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool)))))
(fn2-idc-fn-shape fn2-idc-hold-spares (k need fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool) (fn2-overlays fn2-pool)
 (fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool) t (fn2-idc-add-spare fn2-idc-count-overlays))

; Stage TX: every slot in order against the tip, then room. (mv code i ...):
; :ok (TX :staged: bind may follow in this transition); :stale (resolve
; again; for its :record slot also decide again); :refused (slot I's fold
; test failed); :range; :duplicate, :evidence, :identity-conflict-bound;
; :full (no room now: backpressure); :capacity; :state (TX not resolved, or
; a slot's args incomplete). I names the slot.
(defun fn2-succ-stage (tx b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine
                       fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine
                          fn2-overlays fn2-overlay-index fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-succ-stage-slots fn2-succ-room fn2-idc-scratch fn2-idc-hold-spares
                                            fn2-overlays-rows fn2-overlay-index-rows)))))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-id-decides-wfp fn2-id-decides)
                    (fn2-id-stamps-wfp fn2-id-stamps) (fn2-run-installed-wfp fn2-run-installed) (fn2-id-engine-wfp fn2-id-engine)
                    (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fields-wfp fn2-fields)
                    (fn2-pool-wfp fn2-pool) (< 0 (fn2-id-engine-rows fn2-id-engine))))
       (mv :state 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp b0))) 
       (mv :bounds 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      ((unless (and (member (fn2-succ-txns-phase tx fn2-succ-txns) (list *fn2-succ-phase-open* *fn2-succ-phase-staged*))
                    (<= *fn2-succ-slots* (nfix (fn2-succ-txns-ri tx fn2-succ-txns)))))
       (mv :state 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      (fn2-succ-txns (fn2-succ-txns-set-phase tx *fn2-succ-phase-open* fn2-succ-txns))
      ((mv code i fn2-succ-slots fn2-fields)
       (fn2-succ-stage-slots *fn2-succ-slots* 0 tx b0 fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine
                             fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code i fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      (orows (fn2-overlays-rows fn2-overlays))
      ((unless (posp orows)) (mv :state 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      ((mv code need) (fn2-succ-room *fn2-succ-slots* 0 tx (fn2-id-engine-arena 0 fn2-id-engine)
                                     (floor (fn2-overlay-index-rows fn2-overlay-index) orows) 0 fn2-succ-slots))
      ((unless (eq code :ok)) (mv code 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      ((mv code fn2-id-engine fn2-pool) (fn2-idc-scratch fn2-id-engine fn2-pool))
      ((unless (eq code :ok)) (mv code 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      ((mv code fn2-overlays fn2-pool) (fn2-idc-hold-spares need need fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool))
      ((unless (eq code :ok)) (mv code 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      (fn2-succ-txns (fn2-succ-txns-set-phase tx *fn2-succ-phase-staged* fn2-succ-txns)))
  (mv :ok 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-succ-stage (tx b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine
                                  fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 ((fn2-succ-txns 2) (fn2-succ-slots 3) (fn2-id-engine 4) (fn2-overlays 5) (fn2-fields 6) (fn2-pool 7))
 (fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-succ-txns-phase fn2-succ-txns-ri fn2-id-engine-arena fn2-succ-stage-slots fn2-succ-room fn2-idc-scratch fn2-idc-hold-spares))

; Field F of slot I's staged row (D reads the assigned group number here
; before admission): (mv code value); a record slot's and an octet field are
; :kind.
(defun fn2-succ-out (tx i f b0 fn2-succ-txns fn2-succ-slots fn2-fields)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-fields) :guard t))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-fields-wfp fn2-fields))) (mv :state 0))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp i) (< i *fn2-succ-slots*) (natp f) (natp b0)
                    (< (+ (* tx *fn2-succ-slots*) i) (fn2-succ-slots-rows fn2-succ-slots))
                    (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields))))
       (mv :bounds 0))
      ((unless (member (fn2-succ-txns-phase tx fn2-succ-txns)
                       (list *fn2-succ-phase-staged* *fn2-succ-phase-bound* *fn2-succ-phase-published*)))
       (mv :state 0))
      (s (+ (* tx *fn2-succ-slots*) i)) (sid (fn2-succ-slots-sid s fn2-succ-slots))
      ((when (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*)) (mv :state 0))
      ((unless (< f (min *fn2-succ-fields-max* (fn2-run-layout-fields sid 0)))) (mv :bounds 0))
      ((when (or (equal (fn2-succ-slots-kind s fn2-succ-slots) *fn2-succ-kind-record*) (fn2-run-layout-octets-max sid f))) (mv :kind 0)))
  (if (< (+ b0 (* *fn2-succ-block* i) f) (fn2-fields-rows fn2-fields))
      (mv :ok (fn2-fields-value (+ b0 (* *fn2-succ-block* i) f) fn2-fields))
    (mv :bounds 0))))

; Fill late octet arg J of insert slot I of TX (C-S3a): LEN octets at [OFF,
; OFF+LEN) of SLOT/GEN, readable under OKIND OSLOT OGEN until bind (every
; octet arg of a slot under one owner: :owner). TX must be :staged (else
; :state: a later stage needs the fill again); J a late arg of the slot
; (else :kind); LEN at most the declared bound (else :bounds). The staged
; entry row takes the reference; TX stays :staged and its room is unchanged
; (stage counted the bound).
(defun fn2-succ-fill-octets (tx i j slot gen off len okind oslot ogen b0 fn2-succ-txns fn2-succ-slots fn2-fields)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-fields) :guard t))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-fields-wfp fn2-fields)))
       (mv :state fn2-succ-slots fn2-fields))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp i) (< i *fn2-succ-slots*)
                    (natp j) (< j *fn2-succ-fields-max*) (natp b0)
                    (< (+ (* tx *fn2-succ-slots*) i) (fn2-succ-slots-rows fn2-succ-slots))
                    (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields))
                    (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds fn2-succ-slots fn2-fields))
      ((unless (equal (fn2-succ-txns-phase tx fn2-succ-txns) *fn2-succ-phase-staged*)) (mv :state fn2-succ-slots fn2-fields))
      (s (+ (* tx *fn2-succ-slots*) i))
      (bit (fn2-succ-bit j))
      ((unless (and (not (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*))
                    (equal (fn2-succ-slots-kind s fn2-succ-slots) *fn2-succ-kind-insert*)
                    (fn2-succ-has (fn2-succ-slots-late s fn2-succ-slots) j)))
       (mv :kind fn2-succ-slots fn2-fields))
      (raw (+ b0 (* *fn2-succ-block* i) *fn2-succ-raw* j)) (row (+ b0 (* *fn2-succ-block* i) j))
      ((unless (and (< raw (fn2-fields-rows fn2-fields)) (< row (fn2-fields-rows fn2-fields)))) (mv :bounds fn2-succ-slots fn2-fields))
      ((unless (<= len (nfix (fn2-fields-ref-len raw fn2-fields)))) (mv :bounds fn2-succ-slots fn2-fields))
      ((when (and (equal (fn2-succ-slots-oset s fn2-succ-slots) 1)
                  (not (and (equal (fn2-succ-slots-sk s fn2-succ-slots) okind) (equal (fn2-succ-slots-ss s fn2-succ-slots) oslot)
                            (equal (fn2-succ-slots-sg s fn2-succ-slots) ogen)))))
       (mv :owner fn2-succ-slots fn2-fields))
      (filled (logior (nfix (fn2-succ-slots-filled s fn2-succ-slots)) bit))
      ((unless (unsigned-byte-p 32 filled)) (mv :bounds fn2-succ-slots fn2-fields))
      (fn2-fields (fn2-fields-put row (value 0) (ref-slot slot) (ref-gen gen) (ref-off off) (ref-len len)))
      (fn2-succ-slots (fn2-succ-slots-put s (oset 1) (sk okind) (ss oslot) (sg ogen) (filled filled))))
  (mv :ok fn2-succ-slots fn2-fields)))
(fn2-idc-fn-shape fn2-succ-fill-octets (tx i j slot gen off len okind oslot ogen b0 fn2-succ-txns fn2-succ-slots fn2-fields)
 (fn2-succ-slots fn2-fields) (fn2-succ-txns fn2-succ-slots fn2-fields) t
 (fn2-succ-txns-phase fn2-succ-slots-phase fn2-succ-slots-kind fn2-succ-slots-late fn2-succ-slots-filled fn2-succ-slots-oset
  fn2-succ-slots-sk fn2-succ-slots-ss fn2-succ-slots-sg fn2-fields-ref-len))
