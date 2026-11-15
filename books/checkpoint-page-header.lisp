; Shared physical page header for real checkpoint construction reservations.
; The C producer owns held-cut admission and body provenance. This B leaf
; authenticates the reservation tuple and encodes only the header at offset0.
(in-package "ACL2")
(include-book "checkpoint-page-state")
(include-book "format")
(fn2-book-layer :b)
(defconst *fn2-checkpoint-page-header-area*
 (* 32 (ceiling *fn2-format-page-header-max-size* 32)))

; Metadata's role1 may use any declared physical page kind. Root3's archive
; contains its manifest envelope and internal member run/index pages. The C
; constructor establishes the exact schema/level kind from its owned writer;
; this class predicate conveys no source coverage or completion evidence.
(defun fn2-checkpoint-page-role-kind-p (role kind)
 (declare (xargs :guard t))
 (and (natp kind) (< kind (len (caddr *fn2-format-page-kind*)))
      (case role
       (0 (equal kind *page-kind-checkpoint-descriptor*))
       (1 t)
       (2 (equal kind *page-kind-allocation-map*))
       (3 (or (equal kind *page-kind-manifest*)
              (equal kind *page-kind-run-data*) (equal kind *page-kind-run-index*)))
       (4 (equal kind *page-kind-merkle-node*))
       (5 (equal kind *page-kind-recovery-arena*))
       (otherwise nil))))

(defun fn2-checkpoint-page-pack-header (token okind oslot ogen role ordinal extent epoch allocation
                                       kind history incarnation encoded-length payload base slot gen
                                       fn2-checkpoint-construction fn2-extents fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoint-construction fn2-extents fn2-fields fn2-pool)
  :guard (and (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (posp token) (unsigned-byte-p 60 history) (unsigned-byte-p 60 incarnation)
                     (fn2-checkpoint-page-role-kind-p role kind)
                     (posp encoded-length) (<= encoded-length *fn2-storage-extent-bytes*)
                     (equal (mod encoded-length *fn2-format-sector-size*) 0)
                     (or (not (equal role 0)) (equal encoded-length *fn2-format-sector-size*))
                     (natp payload) (<= (+ *fn2-checkpoint-page-header-area* payload) encoded-length)
                     (natp base) (<= (+ base *fn2-format-page-header-num-fields*) (fn2-fields-rows fn2-fields))
                     (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                     (eq (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool) :ok)
                     (<= encoded-length (fn2-pool-cap slot fn2-pool))
                     (fn2-checkpoint-page-ledger-p token okind oslot ogen role ordinal extent epoch allocation
                       encoded-length 0 fn2-checkpoint-construction fn2-extents)))
       (mv :identity fn2-fields fn2-pool))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-page-header-field-magic*) *fn2-format-page-magic* fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-page-header-field-version*) *fn2-format-version* fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-page-header-field-page-kind*) kind fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-page-header-field-history*) history fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-page-header-field-incarnation*) incarnation fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-page-header-field-physical-unit*) (* extent *fn2-storage-extent-units*) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-page-header-field-writer-epoch*) epoch fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-page-header-field-allocation*) allocation fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-page-header-field-header-length*) *fn2-checkpoint-page-header-area* fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-page-header-field-payload-length*) payload fn2-fields))
      ((mv code next fn2-pool) (fn2-format-page-header-encode base slot gen 0 okind oslot ogen fn2-fields fn2-pool)))
  (mv (if (and (eq code :ok) (> next *fn2-checkpoint-page-header-area*)) :format code) fn2-fields fn2-pool)))
(fn2-fields-preserves fn2-checkpoint-page-pack-header
 (token okind oslot ogen role ordinal extent epoch allocation kind history incarnation encoded-length payload base slot gen
  fn2-checkpoint-construction fn2-extents fn2-fields fn2-pool)
 :carriers ((fn2-fields 1 :prefix "-FIELDS") (fn2-pool 2 :prefix "-POOL")))
