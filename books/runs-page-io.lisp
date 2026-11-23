; Layer C verified nonresident run-page eviction, zero-copy BLAKE3/format page
; reload, cache installation, and cursor miss resolution over child stobjs.
(in-package "ACL2")
(include-book "runs-cache-evict")
(include-book "runs-served")
(include-book "pool-digest")
(include-book "columns-call-guards")
(include-book "std/util/bstar" :dir :system)
(fn2-book-layer :c)

(local (defthm fn2-pio-u-from-range
 (implies (and (natp bits) (integerp v) (<= 0 v) (< v (expt 2 bits)))
          (unsigned-byte-p bits v))
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-pio-u-forward
 (implies (unsigned-byte-p bits v)
          (and (integerp v) (<= 0 v)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-pio-u8-bound
 (implies (unsigned-byte-p 8 v) (< v 256))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-pio-u32-bound
 (implies (unsigned-byte-p 32 v) (< v 4294967296))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-pio-u60-bound
 (implies (unsigned-byte-p 60 v) (< v 1152921504606846976))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

; Keep child-table structures, readers, and heavy callees closed by default so
; guard and preservation proofs operate strictly over public column contracts.
(local (in-theory (disable
 unsigned-byte-p integer-range-p
 fn2-run-cachep fn2-run-cache-wfp fn2-run-cache-rows
 fn2-run-cache-state fn2-run-cache-unit fn2-run-cache-counter fn2-run-cache-slot fn2-run-cache-gen
 fn2-poolp fn2-pool-wfp fn2-pool-rows fn2-pool-cap fn2-pool-base fn2-pool-fill fn2-pool-data-length
 fn2-pool-state fn2-pool-gen fn2-pool-query-ref-count fn2-pool-out-count fn2-pool-credit-group
 fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-fields-value
 fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
 fn2-fcp fn2-fc-wfp fn2-fc-rows
 fn2-fc-contextp fn2-fc-context-wfp fn2-fc-context-rows
 fn2-fc-context-hash fn2-fc-context-geometry fn2-fc-context-previous-seal
 fn2-b3p fn2-b3-wfp fn2-b3-rows fn2-b3-words-length
 fn2-digestsp fn2-digests-wfp fn2-digests-rows
 fn2-run-cursorsp fn2-run-cursors-wfp fn2-run-cursors-rows
 fn2-run-cursors-phase fn2-run-cursors-schema fn2-run-cursors-level
 fn2-run-cursors-slot fn2-run-cursors-gen fn2-run-cursors-idx fn2-run-cursors-rb
 fn2-run-cursors-unit fn2-run-cursors-counter
 fn2-run-cursors-okind fn2-run-cursors-oslot fn2-run-cursors-ogen
 fn2-run-pathsp fn2-run-paths-wfp fn2-run-paths-rows
 fn2-run-layout-keys fn2-run-layout-page-kind
 fn2-run-cache-row fn2-run-cache-lookup fn2-run-cache-install fn2-run-cache-drop
 fn2-pool-reserve fn2-pool-release fn2-pool-release-countp fn2-pool-workspace-code
 fn2-pool-readable-code fn2-pool-read fn2-pool-write fn2-pool-copy-range fn2-pool-class-for
 fn2-format-drive fn2-run-read-header fn2-run-nth fn2-run-cursor-start
 fn2-rec-fetch fn2-digest-copy fn2-digest-equal
 fn2-run-readerp fn2-b3-ready fn2-digest-workspacep fn2-digest-rowp fn2-digest-slot)))

; ---------------------------------------------------------------------------
; 1. Zero-Copy BLAKE3 + Format Page Verification & Cache Reload

(local (defthm fn2-pio-fc-slots-rowp
 (implies (fn2-digest-workspacep row fn2-digests)
          (and (fn2-digest-rowp (fn2-digest-slot row *fn2-fc-hash*) fn2-digests)
               (fn2-digest-rowp (fn2-digest-slot row *fn2-fc-geometry*) fn2-digests)
               (fn2-digest-rowp (fn2-digest-slot row *fn2-fc-previous-seal*) fn2-digests)
               (fn2-digest-rowp (fn2-digest-slot row *fn2-fc-result*) fn2-digests)))
 :hints (("Goal" :in-theory (enable fn2-digest-workspacep fn2-digest-rowp fn2-digest-slot)))))

(local (defthm fn2-pio-fc-slots-u32
 (implies (and (natp row) (< (fn2-digest-slot row *fn2-fc-previous-seal*) 4294967296))
          (and (unsigned-byte-p 32 (fn2-digest-slot row *fn2-fc-hash*))
               (unsigned-byte-p 32 (fn2-digest-slot row *fn2-fc-geometry*))
               (unsigned-byte-p 32 (fn2-digest-slot row *fn2-fc-previous-seal*))))
 :hints (("Goal" :in-theory (enable fn2-digest-slot unsigned-byte-p integer-range-p)))))

(local (defthm fn2-pio-b3-ready-workspace
 (implies (fn2-b3-ready row fn2-b3 fn2-digests)
          (fn2-digest-workspacep row fn2-digests))
 :hints (("Goal" :in-theory (enable fn2-b3-ready)))))

(local (defthm fn2-pio-digest-slot-natp
 (implies (and (natp row) (natp region))
          (natp (fn2-digest-slot row region)))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn2-digest-slot)))))

(defun fn2-run-pio-set-context (crow unit epoch allocation history incarnation page-kind fn2-fc-context)
 (declare (xargs :stobjs fn2-fc-context
  :guard (and (fn2-fc-context-wfp fn2-fc-context) (natp crow) (< crow (fn2-fc-context-rows fn2-fc-context))
              (< (fn2-digest-slot crow *fn2-fc-previous-seal*) 4294967296)
              (unsigned-byte-p 60 unit) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
              (unsigned-byte-p 60 history) (unsigned-byte-p 60 incarnation) (unsigned-byte-p 60 page-kind))))
 (b* ((fn2-fc-context (fn2-fc-context-set-location crow unit fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-allocation crow allocation fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-history crow history fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-incarnation crow incarnation fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-writer-epoch crow epoch fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-page-kind crow page-kind fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-encoded-length crow *fn2-run-page-size* fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-hash crow (fn2-digest-slot crow *fn2-fc-hash*) fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-geometry crow (fn2-digest-slot crow *fn2-fc-geometry*) fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-previous-seal crow (fn2-digest-slot crow *fn2-fc-previous-seal*) fn2-fc-context)))
  fn2-fc-context))

(fn2-fc-shape fn2-run-pio-set-context-shape
 (fn2-run-pio-set-context crow unit epoch allocation history incarnation page-kind fn2-fc-context)
 (and (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context)
      (natp crow) (< crow (fn2-fc-context-rows fn2-fc-context))
      (< (fn2-digest-slot crow *fn2-fc-previous-seal*) 4294967296)
      (unsigned-byte-p 60 unit) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
      (unsigned-byte-p 60 history) (unsigned-byte-p 60 incarnation) (unsigned-byte-p 60 page-kind))
 ((fn2-fc-context nil)))

(local (defthm fn2-run-pio-set-context-digest-slots
 (let ((ctx (fn2-run-pio-set-context crow unit epoch allocation history incarnation page-kind fn2-fc-context)))
  (implies (and (natp crow) (< crow (fn2-fc-context-rows fn2-fc-context))
                (< (fn2-digest-slot crow *fn2-fc-previous-seal*) 4294967296))
           (and (equal (fn2-fc-context-hash crow ctx) (fn2-digest-slot crow *fn2-fc-hash*))
                (equal (fn2-fc-context-geometry crow ctx) (fn2-digest-slot crow *fn2-fc-geometry*))
                (equal (fn2-fc-context-previous-seal crow ctx) (fn2-digest-slot crow *fn2-fc-previous-seal*)))))
 :hints (("Goal" :in-theory (enable fn2-run-pio-set-context
                                    fn2-fc-context-hash fn2-fc-context-geometry fn2-fc-context-previous-seal)))))

(in-theory (disable fn2-run-pio-set-context))

(local (defthm fn2-pio-digest-copy-preserves-rowp-and-b3-ready
 (implies (and (fn2-digestsp fn2-digests)
               (fn2-digest-rowp dst fn2-digests)
               (fn2-digest-rowp src fn2-digests))
          (and (equal (fn2-digest-rowp r (fn2-digest-copy dst src fn2-digests))
                      (fn2-digest-rowp r fn2-digests))
               (equal (fn2-b3-ready row fn2-b3 (fn2-digest-copy dst src fn2-digests))
                      (fn2-b3-ready row fn2-b3 fn2-digests))))
 :hints (("Goal" :in-theory (enable fn2-digest-rowp fn2-b3-ready fn2-digest-workspacep)))))

(local (defthm fn2-pio-format-drive-preserves-rowp-and-readerp
 (let ((res (fn2-format-drive fuel row kind sealp slot gen off len base okind oslot ogen budget
                              fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
  (implies (and (fn2-fc-guard) (natp fuel)
                (fn2-fcp fn2-fc) (fn2-fc-contextp fn2-fc-context)
                (fn2-b3p fn2-b3) (fn2-fieldsp fn2-fields)
                (fn2-poolp fn2-pool) (fn2-digestsp fn2-digests))
           (and (equal (fn2-digest-rowp r (mv-nth 5 res))
                       (fn2-digest-rowp r fn2-digests))
                (equal (fn2-digest-workspacep w (mv-nth 5 res))
                       (fn2-digest-workspacep w fn2-digests))
                (equal (fn2-run-readerp rb (mv-nth 3 res))
                       (fn2-run-readerp rb fn2-fields)))))
 :hints (("Goal" :in-theory (enable fn2-digest-rowp fn2-digest-workspacep fn2-run-readerp)))))

(local (defthm fn2-pio-readerp-bounds
 (implies (fn2-run-readerp rb fn2-fields)
          (and (natp rb)
               (<= (+ rb *fn2-format-page-header-num-fields*) (fn2-fields-rows fn2-fields))))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable fn2-run-readerp)))))

(defun fn2-run-pio-check-header (expected-page-kind rb slot gen okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (unsigned-byte-p 60 expected-page-kind) (fn2-run-readerp rb fn2-fields)
              (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
              (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))))
 (if (equal expected-page-kind *page-kind-partitioned-filter*)
     (b* (((mv dcode & fn2-fields)
           (fn2-format-page-header-decode rb slot gen 0 *fn2-run-header-area* okind oslot ogen fn2-fields fn2-pool))
          ((unless (eq dcode :ok))
           (mv :corrupt dcode fn2-fields))
          (payload (nfix (fn2-fields-value (+ rb *fn2-format-page-header-field-payload-length*) fn2-fields)))
          ((unless (and (equal (fn2-fields-value (+ rb *fn2-format-page-header-field-magic*) fn2-fields)
                               *fn2-format-page-magic*)
                        (equal (fn2-fields-value (+ rb *fn2-format-page-header-field-page-kind*) fn2-fields)
                               expected-page-kind)
                        (equal (fn2-fields-value (+ rb *fn2-format-page-header-field-header-length*) fn2-fields)
                               *fn2-run-header-area*)
                        (<= (+ *fn2-run-header-area* payload) *fn2-run-page-size*)))
           (mv :corrupt :format fn2-fields)))
      (mv :ok :ok fn2-fields))
   (b* (((mv hcode fn2-fields)
         (fn2-run-read-header slot gen rb okind oslot ogen fn2-fields fn2-pool))
        ((unless (eq hcode :ok))
         (mv :corrupt hcode fn2-fields))
        ((unless (equal (fn2-fields-value (+ rb *fn2-format-page-header-field-page-kind*) fn2-fields)
                        expected-page-kind))
         (mv :corrupt :wrong-kind fn2-fields)))
    (mv :ok :ok fn2-fields))))

(fn2-fc-shape fn2-run-pio-check-header-shape
 (fn2-run-pio-check-header expected-page-kind rb slot gen okind oslot ogen fn2-fields fn2-pool)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (unsigned-byte-p 60 expected-page-kind) (fn2-run-readerp rb fn2-fields)
      (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
      (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))
 ((fn2-fields 2)))

(in-theory (disable fn2-run-pio-check-header))

; Verify a loaded 64 KiB page in pool workspace (SLOT, GEN) in place:
; 1) Validates workspace handle, ownership, and exact 64 KiB fill.
; 2) Runs fn2-format-drive (:page, sealp=nil) to decode B's page header,
;    compute real BLAKE3 over domain "fn2/physical-page/v1" + 65,536 octets,
;    verify zero-padding, and check digest bytes against expected-hash HSRC.
; 3) Explicitly verifies full 256-bit BLAKE3 equality (fn2-digest-equal) between
;    the computed digest in *fn2-fc-result* and HSRC.
; 4) Validates run-page header framing (fn2-run-read-header, or filter B-header)
;    and page-kind match.
(defun fn2-run-page-verify (unit epoch allocation history incarnation expected-page-kind
                            crow fc-base rb slot gen hsrc okind oslot ogen
                            fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
  :guard (and (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context)
              (fn2-b3-wfp fn2-b3) (fn2-digests-wfp fn2-digests)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (unsigned-byte-p 60 unit) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
                    (unsigned-byte-p 60 history) (unsigned-byte-p 60 incarnation)
                    (unsigned-byte-p 60 expected-page-kind)
                    (natp crow) (< crow (fn2-fc-rows fn2-fc)) (< crow (fn2-fc-context-rows fn2-fc-context))
                    (fn2-b3-ready crow fn2-b3 fn2-digests)
                    (fn2-digest-rowp hsrc fn2-digests)
                    (< (fn2-digest-slot crow *fn2-fc-previous-seal*) 4294967296)
                    (natp fc-base) (<= (+ fc-base *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows fn2-fields))
                    (fn2-run-readerp rb fn2-fields)
                    (unsigned-byte-p 32 slot) (< slot (fn2-pool-rows fn2-pool)) (unsigned-byte-p 60 gen)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds :bounds fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      (wcode (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool))
      ((unless (eq wcode :ok))
       (mv :workspace wcode fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ((unless (and (equal (fn2-pool-fill slot fn2-pool) *fn2-run-page-size*)
                    (<= *fn2-run-page-size* (fn2-pool-cap slot fn2-pool))))
       (mv :corrupt :wrong-length fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      (fn2-digests (fn2-digest-copy (fn2-digest-slot crow *fn2-fc-hash*) hsrc fn2-digests))
      (fn2-fc-context
       (fn2-run-pio-set-context crow unit epoch allocation history incarnation expected-page-kind fn2-fc-context))
      (fn2-fc (fn2-fc-set-phase crow *fn2-fc-phase-idle* fn2-fc))
      ((mv fcode fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-format-drive (fn2-format-fuel *fn2-run-page-size*) crow :page nil
                         slot gen 0 *fn2-run-page-size* fc-base okind oslot ogen 4096
                         fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      (digest-ok (fn2-digest-equal (fn2-digest-slot crow *fn2-fc-result*) hsrc fn2-digests))
      ((unless (and (eq fcode :ok) digest-ok))
       (mv :corrupt (if (eq fcode :ok) :bad-hash fcode)
           fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ((mv hcode detail fn2-fields)
       (fn2-run-pio-check-header expected-page-kind rb slot gen okind oslot ogen fn2-fields fn2-pool)))
  (mv hcode detail fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))

(fn2-fc-shape fn2-run-page-verify-shape
 (fn2-run-page-verify unit epoch allocation history incarnation expected-page-kind
                      crow fc-base rb slot gen hsrc okind oslot ogen
                      fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
 (and (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc)
      (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context)
      (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-fc 2) (fn2-fc-context 3) (fn2-b3 4) (fn2-digests 5) (fn2-fields 6) (fn2-pool 7)))

; Explicit BLAKE3 mismatch rejection: if the finalized BLAKE3 digest in
; *fn2-fc-result* differs from expected-hash HSRC, fn2-run-page-verify never
; returns :ok (and specifically returns :corrupt when prechecks pass).
(defthm fn2-run-page-verify-digest-mismatch-refuses
 (let ((res (fn2-run-page-verify unit epoch allocation history incarnation expected-page-kind
                                 crow fc-base rb slot gen hsrc okind oslot ogen
                                 fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))
  (implies (not (fn2-digest-equal (fn2-digest-slot crow *fn2-fc-result*) hsrc (mv-nth 5 res)))
           (not (equal (mv-nth 0 res) :ok))))
 :hints (("Goal" :in-theory (enable fn2-run-page-verify))))

(in-theory (disable fn2-run-page-verify))

; Zero-copy nonresident page reload & cache installation:
; Verifies loaded 64 KiB page octets in (SLOT, GEN) against (unit, epoch,
; allocation, history, incarnation, expected-page-kind, expected-hash=hsrc).
; - On :corrupt (or any verification refusal), releases (SLOT, GEN) back to
;   fn2-pool and returns with fn2-run-cache COMPLETELY UNCHANGED.
; - On :ok, evicts any unpinned collision on (mod unit cache-rows) and installs
;   (unit, allocation, slot, gen) into fn2-run-cache.
(defun fn2-run-page-reload-work (unit epoch allocation history incarnation expected-page-kind
                                 crow fc-base rb slot gen hsrc okind oslot ogen
                                 fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
  :guard (and (fn2-run-cache-wfp fn2-run-cache) (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context)
              (fn2-b3-wfp fn2-b3) (fn2-digests-wfp fn2-digests) (fn2-fields-wfp fn2-fields)
              (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (unsigned-byte-p 60 unit) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
                    (< 0 (fn2-run-cache-rows fn2-run-cache))
                    (unsigned-byte-p 32 slot) (< slot (fn2-pool-rows fn2-pool)) (unsigned-byte-p 60 gen)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds :bounds fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      (crow-idx (fn2-run-cache-row unit fn2-run-cache))
      ((unless (and (natp crow-idx) (< crow-idx (fn2-run-cache-rows fn2-run-cache))))
       (mv :bounds :cache fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ;; Never verify/install a buffer whose slot aliases a currently cached row.
      ((when (and (equal (fn2-run-cache-state crow-idx fn2-run-cache) *fn2-run-cache-state-ready*)
                  (equal (fn2-run-cache-slot crow-idx fn2-run-cache) slot)))
       (mv :alias :alias fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ((mv vcode detail fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
       (fn2-run-page-verify unit epoch allocation history incarnation expected-page-kind
                            crow fc-base rb slot gen hsrc okind oslot ogen
                            fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ((unless (eq vcode :ok))
       (let ((fn2-pool (fn2-run-pio-release-quiet slot gen okind oslot ogen fn2-pool)))
        (mv vcode detail fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))
      ((mv ecode fn2-run-cache fn2-pool)
       (fn2-run-cache-evict-for-unit unit okind oslot ogen fn2-run-cache fn2-pool))
      ((unless (eq ecode :ok))
       (let ((fn2-pool (fn2-run-pio-release-quiet slot gen okind oslot ogen fn2-pool)))
        (mv ecode :evict fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))
      ((mv icode fn2-run-cache) (fn2-run-cache-install unit allocation slot gen fn2-run-cache)))
  (mv icode (if (eq icode :ok) :ok :install)
      fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))

(fn2-fc-shape fn2-run-page-reload-work-shape
 (fn2-run-page-reload-work unit epoch allocation history incarnation expected-page-kind
                           crow fc-base rb slot gen hsrc okind oslot ogen
                           fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
 (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc)
      (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context)
      (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-run-cache 2) (fn2-fc 3) (fn2-fc-context 4) (fn2-b3 5) (fn2-digests 6) (fn2-fields 7) (fn2-pool 8)))

(in-theory (disable fn2-run-page-reload-work))

(defun fn2-run-page-reload (unit epoch allocation history incarnation expected-page-kind
                            crow fc-base rb slot gen hsrc okind oslot ogen
                            fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
  :guard t))
 (if (and (fn2-run-cache-wfp fn2-run-cache) (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context)
          (fn2-b3-wfp fn2-b3) (fn2-digests-wfp fn2-digests) (fn2-fields-wfp fn2-fields)
          (fn2-pool-wfp fn2-pool))
     (fn2-run-page-reload-work unit epoch allocation history incarnation expected-page-kind
                               crow fc-base rb slot gen hsrc okind oslot ogen
                               fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
   (mv :state :state fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))

(fn2-fc-shape fn2-run-page-reload-shape
 (fn2-run-page-reload unit epoch allocation history incarnation expected-page-kind
                      crow fc-base rb slot gen hsrc okind oslot ogen
                      fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
 (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc)
      (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context)
      (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-run-cache 2) (fn2-fc 3) (fn2-fc-context 4) (fn2-b3 5) (fn2-digests 6) (fn2-fields 7) (fn2-pool 8)))

; ---------------------------------------------------------------------------
; 3. Cursor :miss Decode, Resolution & Cache-Checked Cursor Start

; Extract child reference [unit, epoch, allocation, page-kind, encoded-length,
; expected-hash -> HSRC] from cursor C in :miss phase by decoding entry IDX on
; its parent page.
(defun fn2-run-miss-decode (c hsrc fn2-run-cursors fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-run-cursors fn2-fields fn2-pool fn2-digests) :guard t
  :guard-hints ((fn2-columns-guard-hint '(fn2-run-cursors fn2-fields fn2-pool fn2-digests)
                  '(fn2-run-nth fn2-rec-fetch fn2-run-layout-keys)
                  nil world))))
 (b* (((unless (and (fn2-run-cursors-wfp fn2-run-cursors) (fn2-fields-wfp fn2-fields)
                    (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests)))
       (mv :state 0 0 0 0 0 fn2-fields fn2-digests))
      ((unless (and (natp c) (< c (fn2-run-cursors-rows fn2-run-cursors))
                    (fn2-digest-rowp hsrc fn2-digests)))
       (mv :bounds 0 0 0 0 0 fn2-fields fn2-digests))
      ((unless (equal (fn2-run-cursors-phase c fn2-run-cursors) *fn2-run-cursor-phase-miss*))
       (mv :state 0 0 0 0 0 fn2-fields fn2-digests))
      (sid (fn2-run-cursors-schema c fn2-run-cursors))
      (lv (fn2-run-cursors-level c fn2-run-cursors))
      (slot (fn2-run-cursors-slot c fn2-run-cursors))
      (gen (fn2-run-cursors-gen c fn2-run-cursors))
      (idx (fn2-run-cursors-idx c fn2-run-cursors))
      (rb (fn2-run-cursors-rb c fn2-run-cursors))
      (ok (fn2-run-cursors-okind c fn2-run-cursors))
      (os (fn2-run-cursors-oslot c fn2-run-cursors))
      (og (fn2-run-cursors-ogen c fn2-run-cursors))
      (nkeys (fn2-run-layout-keys sid))
      ((unless (and (natp rb) (fn2-run-readerp rb fn2-fields) (< 0 lv) (natp nkeys)))
       (mv :bounds 0 0 0 0 0 fn2-fields fn2-digests))
      ((mv code & fn2-fields) (fn2-run-nth sid lv idx slot gen rb ok os og fn2-fields fn2-pool))
      ((unless (eq code :ok))
       (mv code 0 0 0 0 0 fn2-fields fn2-digests))
      (cb (+ rb *fn2-run-reader-entry* nkeys))
      ((unless (and (fn2-fields-wfp fn2-fields)
                    (<= (+ cb *fn2-format-ref-num-fields*) (fn2-fields-rows fn2-fields))))
       (mv :bounds 0 0 0 0 0 fn2-fields fn2-digests))
      (cunit (fn2-fields-value (+ cb *fn2-format-ref-field-physical-unit*) fn2-fields))
      (cepoch (fn2-fields-value (+ cb *fn2-format-ref-field-writer-epoch*) fn2-fields))
      (calloc (fn2-fields-value (+ cb *fn2-format-ref-field-allocation*) fn2-fields))
      (ckind (fn2-fields-value (+ cb *fn2-format-ref-field-page-kind*) fn2-fields))
      (clen (fn2-fields-value (+ cb *fn2-format-ref-field-encoded-length*) fn2-fields))
      ((unless (and (equal cunit (fn2-run-cursors-unit c fn2-run-cursors))
                    (equal calloc (fn2-run-cursors-counter c fn2-run-cursors))))
       (mv :mismatch 0 0 0 0 0 fn2-fields fn2-digests))
      (hf (+ cb *fn2-format-ref-field-expected-hash*))
      (hslot (fn2-fields-ref-slot hf fn2-fields))
      (hgen (fn2-fields-ref-gen hf fn2-fields))
      (hoff (nfix (fn2-fields-ref-off hf fn2-fields)))
      (hlen (fn2-fields-ref-len hf fn2-fields))
      ((unless (equal hlen 32))
       (mv :format 0 0 0 0 0 fn2-fields fn2-digests))
      ((mv fcode fn2-digests) (fn2-rec-fetch 0 hsrc hslot hgen hoff ok os og fn2-pool fn2-digests)))
  (mv fcode cunit cepoch calloc ckind clen fn2-fields fn2-digests)))

(fn2-fc-shape fn2-run-miss-decode-shape
 (fn2-run-miss-decode c hsrc fn2-run-cursors fn2-fields fn2-pool fn2-digests)
 (and (fn2-run-cursorsp fn2-run-cursors) (fn2-run-cursors-wfp fn2-run-cursors)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 ((fn2-fields 6) (fn2-digests 7)))

(in-theory (disable fn2-run-miss-decode))

; Resolve a cursor :miss by extracting the parent-held reference + expected
; BLAKE3 hash and verifying/installing the loaded page workspace (SLOT, GEN).
(defun fn2-run-miss-resolve (c history incarnation crow fc-base rb slot gen hsrc okind oslot ogen
                             fn2-run-cursors fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-run-cursors fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
  :guard t))
 (b* (((unless (and (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-cache-wfp fn2-run-cache)
                    (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context)
                    (fn2-b3-wfp fn2-b3) (fn2-digests-wfp fn2-digests)
                    (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state :state fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ((mv dcode unit epoch alloc pkind plen fn2-fields fn2-digests)
       (fn2-run-miss-decode c hsrc fn2-run-cursors fn2-fields fn2-pool fn2-digests))
      ((unless (eq dcode :ok))
       (mv dcode :decode fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ((unless (equal plen *fn2-run-page-size*))
       (mv :corrupt :wrong-length fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))
  (fn2-run-page-reload unit epoch alloc history incarnation pkind crow fc-base rb slot gen hsrc okind oslot ogen
                       fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))

(fn2-fc-shape fn2-run-miss-resolve-shape
 (fn2-run-miss-resolve c history incarnation crow fc-base rb slot gen hsrc okind oslot ogen
                       fn2-run-cursors fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
 (and (fn2-run-cursorsp fn2-run-cursors) (fn2-run-cursors-wfp fn2-run-cursors)
      (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc)
      (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context)
      (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-run-cache 2) (fn2-fc 3) (fn2-fc-context 4) (fn2-b3 5) (fn2-digests 6) (fn2-fields 7) (fn2-pool 8)))

(in-theory (disable fn2-run-miss-resolve))

; Start cursor C by looking up (ROOT-UNIT, ROOT-COUNTER) in fn2-run-cache,
; returning :miss cleanly when the root page is nonresident.
(defun fn2-run-cursor-start-cached (c schema level root-unit root-counter rb okind oslot ogen
                                    fn2-run-cursors fn2-run-cache)
 (declare (xargs :stobjs (fn2-run-cursors fn2-run-cache) :guard t))
 (b* (((unless (and (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-cache-wfp fn2-run-cache)
                    (natp root-unit) (natp root-counter)))
       (mv :state fn2-run-cursors))
      ((mv hit cslot cgen) (fn2-run-cache-lookup root-unit root-counter fn2-run-cache))
      ((unless (eq hit :ok))
       (mv :miss fn2-run-cursors)))
  (fn2-run-cursor-start c schema level cslot cgen root-unit root-counter rb okind oslot ogen fn2-run-cursors)))

(fn2-run-cursors-preserves fn2-run-cursor-start-cached
 (c schema level root-unit root-counter rb okind oslot ogen fn2-run-cursors fn2-run-cache)
 :position 1 :disable t)

; ---------------------------------------------------------------------------
; 4. Keystone Integrity, Corruption Rejection & Resident-Equivalence Theorems

; (A) Byte-level BLAKE3 digest mismatch refusal inside B's page checker.
(defthm fn2-fc-byte-digest-mismatch-refuses
 (implies (and (not sealp) (eq kind :page)
               (equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-digest*)
               (natp pos) (< pos 32)
               (equal (fn2-fc-pos row fn2-fc) pos)
               (not (equal (fn2-fc-digest-byte row pos fn2-fc fn2-digests)
                           (fn2-fc-word-byte
                            (fn2-fc-context-hash-word row (floor pos 4) fn2-fc-context fn2-digests)
                            (mod pos 4)))))
          (equal (mv-nth 0 (fn2-fc-byte row kind sealp slot gen off len base okind oslot ogen
                                        fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
                 :bad-hash))
 :hints (("Goal" :in-theory (enable fn2-fc-byte))))

(local (defthm fn2-pio-evict-for-unit-preserves-cache
 (implies (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache))
          (let ((c2 (mv-nth 1 (fn2-run-cache-evict-for-unit unit okind oslot ogen fn2-run-cache fn2-pool))))
           (and (fn2-run-cachep c2)
                (fn2-run-cache-wfp c2)
                (equal (fn2-run-cache-rows c2) (fn2-run-cache-rows fn2-run-cache)))))
 :hints (("Goal" :in-theory (enable fn2-run-cache-evict-for-unit fn2-run-cache-evict-row)))))

(local (defthm fn2-pio-install-ok-when-ready
 (implies (and (fn2-run-cache-wfp fn2-run-cache)
               (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
               (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
               (< 0 (fn2-run-cache-rows fn2-run-cache)))
          (equal (car (fn2-run-cache-install unit counter slot gen fn2-run-cache)) :ok))
 :hints (("Goal" :in-theory (enable fn2-run-cache-install fn2-run-cache-row)))))

; (B) Corruption & refusal protection: any non-:ok result from
;     fn2-run-page-reload leaves fn2-run-cache and every lookup unchanged.
(defthm fn2-run-page-reload-work-fail-unchanged
 (implies (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache))
          (let ((res (fn2-run-page-reload-work
                      unit epoch allocation history incarnation expected-page-kind
                      crow fc-base rb slot gen hsrc okind oslot ogen
                      fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))
           (implies (not (equal (car res) :ok))
                    (equal (mv-nth 2 res) fn2-run-cache))))
 :hints (("Goal" :in-theory (enable fn2-run-page-reload-work))))

(defthm fn2-run-page-reload-fail-preserves-cache
 (implies (fn2-run-cachep fn2-run-cache)
          (let ((res (fn2-run-page-reload
                      unit epoch allocation history incarnation expected-page-kind
                      crow fc-base rb slot gen hsrc okind oslot ogen
                      fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))
           (implies (not (equal (car res) :ok))
                    (and (equal (mv-nth 2 res) fn2-run-cache)
                         (equal (fn2-run-cache-lookup u c (mv-nth 2 res))
                                (fn2-run-cache-lookup u c fn2-run-cache))))))
 :hints (("Goal" :in-theory (enable fn2-run-page-reload))))

; Direct digest-inequality corollary: computed BLAKE3 != expected-hash HSRC
; guarantees fn2-run-page-reload refuses (:corrupt when invoked on valid workspace)
; and leaves fn2-run-cache untouched!
(defthm fn2-run-page-reload-digest-mismatch-leaves-cache-unchanged
 (let* ((vres (fn2-run-page-verify unit epoch allocation history incarnation expected-page-kind
                                   crow fc-base rb slot gen hsrc okind oslot ogen
                                   fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
        (rres (fn2-run-page-reload unit epoch allocation history incarnation expected-page-kind
                                   crow fc-base rb slot gen hsrc okind oslot ogen
                                   fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))
  (implies (not (fn2-digest-equal (fn2-digest-slot crow *fn2-fc-result*) hsrc (mv-nth 5 vres)))
           (and (not (equal (car rres) :ok))
                (equal (mv-nth 2 rres) fn2-run-cache))))
 :hints (("Goal" :in-theory (enable fn2-run-page-reload fn2-run-page-reload-work)
                 :use ((:instance fn2-run-page-verify-digest-mismatch-refuses)))))

; (C) Verified reload installation establishes exact cache hit:
(local (defthm fn2-pio-cache-install-lookup-hit
 (implies (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
               (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
               (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
               (< 0 (fn2-run-cache-rows fn2-run-cache)))
          (let ((c2 (mv-nth 1 (fn2-run-cache-install unit counter slot gen fn2-run-cache))))
           (and (equal (car (fn2-run-cache-lookup unit counter c2)) :ok)
                (equal (mv-nth 1 (fn2-run-cache-lookup unit counter c2)) slot)
                (equal (mv-nth 2 (fn2-run-cache-lookup unit counter c2)) gen))))
 :hints (("Goal" :in-theory (enable fn2-run-cache-install fn2-run-cache-lookup fn2-run-cache-row
                                    fn2-run-cache-state fn2-run-cache-unit fn2-run-cache-counter
                                    fn2-run-cache-slot fn2-run-cache-gen fn2-run-cache-rows)))))

(defthm fn2-run-page-reload-lookup-hit
 (implies (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache))
          (let ((res (fn2-run-page-reload
                      unit epoch allocation history incarnation expected-page-kind
                      crow fc-base rb slot gen hsrc okind oslot ogen
                      fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))
           (implies (equal (car res) :ok)
                    (and (equal (car (fn2-run-cache-lookup unit allocation (mv-nth 2 res))) :ok)
                         (equal (mv-nth 1 (fn2-run-cache-lookup unit allocation (mv-nth 2 res))) slot)
                         (equal (mv-nth 2 (fn2-run-cache-lookup unit allocation (mv-nth 2 res))) gen)))))
 :hints (("Goal" :in-theory (enable fn2-run-page-reload fn2-run-page-reload-work)
                 :use ((:instance fn2-pio-cache-install-lookup-hit
                                  (counter allocation)
                                  (fn2-run-cache (mv-nth 1 (fn2-run-cache-evict-for-unit
                                                            unit okind oslot ogen fn2-run-cache
                                                            (mv-nth 7 (fn2-run-page-verify
                                                                       unit epoch allocation history incarnation expected-page-kind
                                                                       crow fc-base rb slot gen hsrc okind oslot ogen
                                                                       fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))))))))))

; (D) Resident-equivalence on reload:
;     When fn2-run-step-child encounters a nonresident child (:miss), and
;     fn2-run-page-reload verifies & installs that child at (CSLOT, CGEN),
;     resuming fn2-run-step-child (childp = nil) produces the EXACT SAME
;     (code, fn2-run-cursors, fn2-run-paths) state as when the child page was
;     already resident at (CSLOT, CGEN) in fn2-run-cache!
(local (defthm fn2-pio-update-nth-same
 (equal (update-nth i v2 (update-nth i v1 xs))
        (update-nth i v2 xs))
 :hints (("Goal" :in-theory (enable update-nth)))))

(local (defthm fn2-pio-nth-update-nth
 (implies (and (natp i) (natp j))
          (equal (nth i (update-nth j v xs))
                 (if (equal i j) v (nth i xs))))
 :hints (("Goal" :in-theory (enable nth update-nth)))))

(local (defthm fn2-pio-update-nth-commute
 (implies (and (natp i) (natp j) (< i j))
          (equal (update-nth j v2 (update-nth i v1 xs))
                 (update-nth i v1 (update-nth j v2 xs))))
 :hints (("Goal" :in-theory (enable update-nth)))))

(local (defthm fn2-pio-cursor-save-overwrite
 (implies (and (equal (car (fn2-run-cursor-save c p1 l1 s1 g1 lo1 hi1 idx1 off1 u cnt fn2-run-cursors)) :ok)
               (natp p2) (< p2 *fn2-run-cursor-phase-count*)
               (unsigned-byte-p 8 l2) (unsigned-byte-p 32 s2) (unsigned-byte-p 60 g2)
               (unsigned-byte-p 32 lo2) (unsigned-byte-p 32 hi2) (unsigned-byte-p 32 idx2) (unsigned-byte-p 32 off2))
          (equal (fn2-run-cursor-save c p2 l2 s2 g2 lo2 hi2 idx2 off2 u cnt
                  (mv-nth 1 (fn2-run-cursor-save c p1 l1 s1 g1 lo1 hi1 idx1 off1 u cnt fn2-run-cursors)))
                 (fn2-run-cursor-save c p2 l2 s2 g2 lo2 hi2 idx2 off2 u cnt fn2-run-cursors)))
 :hints (("Goal" :in-theory (e/d (fn2-run-cursor-save fn2-run-cursors-rows
                                  fn2-run-cursors-set-phase fn2-run-cursors-set-level
                                  fn2-run-cursors-set-slot fn2-run-cursors-set-gen
                                  fn2-run-cursors-set-lo fn2-run-cursors-set-hi
                                  fn2-run-cursors-set-idx fn2-run-cursors-set-off
                                  fn2-run-cursors-set-unit fn2-run-cursors-set-counter
                                  update-fn2-run-cursors-phase$ai update-fn2-run-cursors-level$ai
                                  update-fn2-run-cursors-slot$ai update-fn2-run-cursors-gen$ai
                                  update-fn2-run-cursors-lo$ai update-fn2-run-cursors-hi$ai
                                  update-fn2-run-cursors-idx$ai update-fn2-run-cursors-off$ai
                                  update-fn2-run-cursors-unit$ai update-fn2-run-cursors-counter$ai)
                                 (nth update-nth))))))

(local (defthm fn2-pio-cursor-save-props
 (let ((res (fn2-run-cursor-save c ph l s g lo hi idx off u cnt fn2-run-cursors)))
  (and (not (equal (car res) :miss))
       (not (equal (car (fn2-run-path-take c l idx fn2-run-paths)) :miss))
       (equal (fn2-run-cursors-phase c (mv-nth 1 res))
              (if (equal (car res) :ok)
                  ph
                (fn2-run-cursors-phase c fn2-run-cursors)))))
 :hints (("Goal" :in-theory (e/d (fn2-run-cursor-save fn2-run-path-take
                                  fn2-run-cursors-rows fn2-run-cursors-phase
                                  fn2-run-cursors-phase$ai
                                  fn2-run-cursors-set-phase fn2-run-cursors-set-level
                                  fn2-run-cursors-set-slot fn2-run-cursors-set-gen
                                  fn2-run-cursors-set-lo fn2-run-cursors-set-hi
                                  fn2-run-cursors-set-idx fn2-run-cursors-set-off
                                  fn2-run-cursors-set-unit fn2-run-cursors-set-counter
                                  update-fn2-run-cursors-phase$ai update-fn2-run-cursors-level$ai
                                  update-fn2-run-cursors-slot$ai update-fn2-run-cursors-gen$ai
                                  update-fn2-run-cursors-lo$ai update-fn2-run-cursors-hi$ai
                                  update-fn2-run-cursors-idx$ai update-fn2-run-cursors-off$ai
                                  update-fn2-run-cursors-unit$ai update-fn2-run-cursors-counter$ai)
                                 (nth update-nth))))))

(in-theory (disable fn2-run-page-reload))

(defthm fn2-run-step-child-reload-resident-equiv
 (b* (((mv mcode cur-miss paths-miss fields-miss)
       (fn2-run-step-child c sid t level nkeys pslot pgen lo hi idx off punit pcounter rb ok os og
                           fn2-run-cursors fn2-run-paths cache-cold fn2-fields fn2-pool))
      (cunit (fn2-fields-value (+ rb *fn2-run-reader-entry* nkeys *fn2-format-ref-field-physical-unit*) fields-miss))
      (ccounter (fn2-fields-value (+ rb *fn2-run-reader-entry* nkeys *fn2-format-ref-field-allocation*) fields-miss))
      ((mv rcode & cache-reloaded & & & & & &)
       (fn2-run-page-reload cunit cepoch ccounter history incarnation expected-page-kind
                            crow fc-base rrb cslot cgen hsrc cok cos cog
                            cache-cold fn2-fc fn2-fc-context fn2-b3 fn2-digests rfields rpool))
      ((mv res-code cur-resumed paths-resumed &)
       (fn2-run-step-child c sid nil level nkeys pslot pgen lo hi idx off cunit ccounter rb ok os og
                           cur-miss paths-miss cache-reloaded fields-miss fn2-pool))
      ((mv hit-code cur-resident paths-resident fields-resident)
       (fn2-run-step-child c sid t level nkeys pslot pgen lo hi idx off punit pcounter rb ok os og
                           fn2-run-cursors fn2-run-paths cache-resident fn2-fields fn2-pool)))
  (implies (and (fn2-run-cachep cache-cold) (fn2-run-cache-wfp cache-cold)
                (not (equal (fn2-run-cursors-phase c fn2-run-cursors) *fn2-run-cursor-phase-miss*))
                (equal mcode :miss)
                (equal (fn2-run-cursors-phase c cur-miss) *fn2-run-cursor-phase-miss*)
                (equal rcode :ok)
                (equal (mv-nth 0 (fn2-run-cache-lookup cunit ccounter cache-resident)) :ok)
                (equal (mv-nth 1 (fn2-run-cache-lookup cunit ccounter cache-resident)) cslot)
                (equal (mv-nth 2 (fn2-run-cache-lookup cunit ccounter cache-resident)) cgen)
                (unsigned-byte-p 8 (- level 1))
                (unsigned-byte-p 32 cslot) (unsigned-byte-p 60 cgen))
           (and (equal res-code hit-code)
                (equal cur-resumed cur-resident)
                (equal paths-resumed paths-resident)
                (equal fields-miss fields-resident))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-run-step-child) (fn2-run-cursor-save)))))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-run-cache-pinned-p
    fn2-run-cache-evict-row
    fn2-run-cache-evict-for-unit
    fn2-run-cache-evict-unit
    fn2-run-cache-evict-one
    fn2-run-cache-evict-unpinned
    fn2-run-page-verify
    fn2-run-page-reload
    fn2-run-miss-decode
    fn2-run-miss-resolve
    fn2-run-cursor-start-cached)
  (w state)))
