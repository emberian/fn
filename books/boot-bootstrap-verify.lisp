; The actual BOOT completion wrapper owns persisted-read and genesis provenance.
; This lower leaf rebuilds and compares every bootstrap octet before minting.
(in-package "ACL2")
(include-book "boot-bootstrap-pack")
(include-book "origin")
(local (include-book "columns-call-guards"))
(fn2-book-layer :b)

; This is the exact two-extent separation relation in POOL-EXTENTS-APART.
; Check the two concrete windows before construction, without rescanning the
; pool semantic invariant or relying on distinct slot numbers alone.
(defun fn2-boot-bootstrap-windows-apart-p (page rx fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
 (and (natp page) (natp rx) (< page (fn2-pool-rows fn2-pool)) (< rx (fn2-pool-rows fn2-pool))
      (or (<= (+ (fn2-pool-base page fn2-pool) (fn2-pool-cap page fn2-pool))
              (fn2-pool-base rx fn2-pool))
          (<= (+ (fn2-pool-base rx fn2-pool) (fn2-pool-cap rx fn2-pool))
              (fn2-pool-base page fn2-pool)))))

; PAGE is the existing 64KiB BOOT window. Its second sector begins with the
; generated geometry digest; its first sector is the canonical bootstrap.
; No retained receipt or geometry is written by this construction function.
(defun fn2-boot-bootstrap-pack-pool (size page pgen kind id ogen fn2-boot-config
                                    fn2-fields fn2-digests fn2-b3 fn2-pool)
 (declare (xargs :stobjs (fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool)
  :verify-guards nil
  :guard (and (fn2-boot-config-wfp fn2-boot-config) (fn2-fields-wfp fn2-fields)
              (fn2-digests-wfp fn2-digests) (fn2-b3-wfp fn2-b3) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (unsigned-byte-p 8 kind) (unsigned-byte-p 32 id)
                     (posp ogen) (unsigned-byte-p 60 ogen)
                     (natp page) (< page (fn2-pool-rows fn2-pool))
                     (<= (+ *fn2-format-sector-size* 32) (fn2-pool-cap page fn2-pool))))
       (mv :bounds fn2-fields fn2-digests fn2-b3 fn2-pool))
      ((mv code end fn2-fields fn2-digests fn2-b3 fn2-pool)
       (fn2-boot-pack-geometry size (fn2-boot-config-extents fn2-boot-config)
        (fn2-boot-config-count fn2-boot-config) page pgen kind id ogen
        fn2-fields fn2-digests fn2-b3 fn2-pool))
      ((unless (and (eq code :ok) (natp end) (<= (+ end 32) *fn2-format-sector-size*)))
       (mv (if (eq code :ok) :bounds code) fn2-fields fn2-digests fn2-b3 fn2-pool))
      ((mv code fn2-pool)
       (fn2-boot-pad (- *fn2-format-sector-size* (+ end 32)) (+ end 32) page pgen kind id ogen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields fn2-digests fn2-b3 fn2-pool))
      ((mv code fn2-pool)
       (fn2-digest-store 32 (fn2-digest-slot 2 *fn2-b3-result*) page pgen
        *fn2-format-sector-size* kind id ogen fn2-digests fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields fn2-digests fn2-b3 fn2-pool))
      ((mv code fn2-fields fn2-pool)
       (fn2-boot-bootstrap-encode-pool size (fn2-boot-config-extents fn2-boot-config)
        (fn2-boot-config-count fn2-boot-config) page pgen page pgen
        *fn2-format-sector-size* kind id ogen fn2-fields fn2-pool)))
  (mv code fn2-fields fn2-digests fn2-b3 fn2-pool)))

; The CORE caller must establish actual bootstrap-read completion at its saved
; address, no pending operation, and the already verified genesis namespace.
; This function accepts no READY/equal argument and performs the real compare.
(defun fn2-boot-bootstrap-verify-pool (size page pgen rx rgen kind id ogen
                                      fn2-boot-config fn2-origin fn2-fields fn2-digests fn2-b3 fn2-pool)
 (declare (xargs :stobjs (fn2-boot-config fn2-origin fn2-fields fn2-digests fn2-b3 fn2-pool)
  :verify-guards nil
  :guard (and (fn2-boot-config-wfp fn2-boot-config) (fn2-origin-wfp fn2-origin)
              (fn2-fields-wfp fn2-fields) (fn2-digests-wfp fn2-digests)
              (fn2-b3-wfp fn2-b3) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (equal (fn2-boot-config-bootstrap-owner-gen fn2-boot-config) 0)
                     (not (equal page rx))
                     (fn2-origin-tuplep (fn2-origin-lineage fn2-origin)
                       (fn2-origin-domain fn2-origin) (fn2-origin-incarnation fn2-origin))
                     (fn2-origin-physicalp (fn2-origin-history fn2-origin)
                       (fn2-origin-history-incarnation fn2-origin))))
       (mv :state fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool))
      (readable (fn2-layout-range-code rx rgen 0 *fn2-format-sector-size* nil kind id ogen fn2-pool))
      ((unless (eq readable :ok))
       (mv readable fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool))
      ((unless (fn2-boot-bootstrap-windows-apart-p page rx fn2-pool))
       (mv :alias fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool))
      ((mv code fn2-fields fn2-digests fn2-b3 fn2-pool)
       (fn2-boot-bootstrap-pack-pool size page pgen kind id ogen fn2-boot-config
        fn2-fields fn2-digests fn2-b3 fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool))
      ((mv code result at)
       (fn2-pool-compare page pgen 0 kind id ogen rx rgen 0 kind id ogen
        *fn2-format-sector-size* fn2-pool))
      ((unless (and (eq code :ok) (eq result :equal) (equal at *fn2-format-sector-size*)))
       (mv (if (eq code :ok) :different code) fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool))
      ((mv code fn2-boot-config)
       (fn2-boot-save-geometry 0 page pgen *fn2-format-sector-size* kind id ogen fn2-pool fn2-boot-config))
      ((unless (eq code :ok)) (mv code fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool))
      (fn2-boot-config (update-fn2-boot-config-image-size size fn2-boot-config))
      (fn2-boot-config (update-fn2-boot-config-bootstrap-owner-kind kind fn2-boot-config))
      (fn2-boot-config (update-fn2-boot-config-bootstrap-owner-slot id fn2-boot-config))
      (fn2-boot-config (update-fn2-boot-config-bootstrap-domain (fn2-origin-domain fn2-origin) fn2-boot-config))
      (fn2-boot-config (update-fn2-boot-config-bootstrap-lineage (fn2-origin-lineage fn2-origin) fn2-boot-config))
      (fn2-boot-config (update-fn2-boot-config-bootstrap-incarnation (fn2-origin-incarnation fn2-origin) fn2-boot-config))
      (fn2-boot-config (update-fn2-boot-config-bootstrap-history (fn2-origin-history fn2-origin) fn2-boot-config))
      (fn2-boot-config (update-fn2-boot-config-bootstrap-history-incarnation (fn2-origin-history-incarnation fn2-origin) fn2-boot-config))
      ; The receipt generation is published last, after all matched evidence.
      (fn2-boot-config (update-fn2-boot-config-bootstrap-owner-gen ogen fn2-boot-config)))
  (mv :ok fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool)))

; These final obligations are part of this component author pilot. No nil-
; guard-verification runtime body can qualify merely by loading its DEFUN.
(verify-guards fn2-boot-bootstrap-pack-pool
 :hints ((fn2-columns-call-guard-hint 'fn2-boot-bootstrap-pack-pool
  '(fn2-boot-pack-geometry fn2-boot-bootstrap-encode-pool fn2-boot-pad fn2-digest-store) nil world)))
(verify-guards fn2-boot-bootstrap-verify-pool
 :hints ((fn2-columns-call-guard-hint 'fn2-boot-bootstrap-verify-pool
  '(fn2-boot-bootstrap-pack-pool fn2-pool-compare fn2-boot-save-geometry) nil world)))
