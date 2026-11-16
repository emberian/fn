; Producer interfaces over the admitted canonical constructor bodies.
; This proof-only book leaves the accepted constructor source/key unchanged.
(in-package "ACL2")
(include-book "boot-bootstrap-pack")
(include-book "columns-carrier-contracts")
(local (include-book "pool-read-contracts"))
(local (include-book "blake3-row-frames"))
(fn2-book-layer :b)

; The public shape theorem is typed; the ROWS facets below are unconditional.
; Derive their actual wrapper boundary with the canonical ABI-driven form.
(fn2-hash-row-frames fn2-pool-block-hash-loop fn2-digests fn2-b3)
(fn2-hash-row-frames fn2-pool-block-hash fn2-digests fn2-b3)

(defcolumns-guarded-contracts fn2-boot-pack-geometry
 :carriers ((fn2-fields 2 :prefix "-FIELDS") (fn2-digests 3 :prefix "-DIGESTS")
            (fn2-b3 4 :prefix "-HASHER") (fn2-pool 5 :prefix "-POOL")) :rows t
 :hints ((fn2-columns-guard-hint
  '(fn2-fields fn2-digests fn2-b3 fn2-pool)
  '(fn2-pool-reset fn2-pool-append-text fn2-checkpoint-geometry-record-encode
    fn2-pool-block-hash fn2-digest-store)
  '(fn2-boot-pack-geometry fn2-boot-geometry-fields) world)))

(defcolumns-guarded-contracts fn2-boot-bootstrap-encode-pool
 :carriers ((fn2-fields 1 :prefix "-FIELDS") (fn2-pool 2 :prefix "-POOL")) :rows t
 :hints ((fn2-columns-guard-hint
  '(fn2-fields fn2-pool)
  '(fn2-format-bootstrap-encode fn2-boot-pad)
  '(fn2-boot-bootstrap-encode-pool) world)))

(defcolumns-guarded-contracts fn2-boot-save-geometry
 :carriers ((fn2-boot-config 1 :prefix "-CONFIG")) :rows t
 :hints ((append (fn2-columns-guard-hint
  '(fn2-pool fn2-boot-config) '(fn2-pool-read) '(fn2-boot-save-geometry) world)
  '(:use ((:instance fn2-pool-read-byte-type
   (slot source) (gen sgen) (idx (+ source-off i)) (okind kind) (oslot id)))))))

(defcolumns-guarded-contracts fn2-boot-save-anchor-digest
 :carriers ((fn2-boot-config 1 :prefix "-CONFIG")) :rows t
 :hints ((append (fn2-columns-guard-hint
  '(fn2-pool fn2-boot-config) '(fn2-pool-read) '(fn2-boot-save-anchor-digest) world)
  '(:use ((:instance fn2-pool-read-byte-type (idx src) (okind kind) (oslot id)))))))

; These are the exact successful branch checks in PACK-GEOMETRY, not caller
; claims or a larger input guard. STORE writes POOL only, retaining DIGESTS.
(defthm fn2-boot-pack-geometry-ok-result-row-by-definition
 (implies
  (equal (car (fn2-boot-pack-geometry size extents groups slot gen kind id ogen
               fn2-fields fn2-digests fn2-b3 fn2-pool)) :ok)
  (fn2-digest-rowp (fn2-digest-slot 2 *fn2-b3-result*)
   (mv-nth 3 (fn2-boot-pack-geometry size extents groups slot gen kind id ogen
               fn2-fields fn2-digests fn2-b3 fn2-pool))))
 :hints (("Goal" :in-theory
  (e/d (fn2-boot-pack-geometry)
       (fn2-checkpoint-geometry-record-encode fn2-pool-block-hash fn2-digest-store
        fn2-boot-geometry-fields fn2-pool-reset fn2-pool-append-text fn2-digest-rowp)))))

(defthm fn2-boot-pack-geometry-ok-image-by-definition
 (implies
  (equal (car (fn2-boot-pack-geometry size extents groups slot gen kind id ogen
               fn2-fields fn2-digests fn2-b3 fn2-pool)) :ok)
  (fn2-checkpoint-image-sizep size extents groups))
 :hints (("Goal" :in-theory
  (e/d (fn2-boot-pack-geometry)
       (fn2-checkpoint-image-sizep fn2-checkpoint-geometry-record-encode fn2-pool-block-hash
        fn2-digest-store fn2-boot-geometry-fields fn2-pool-reset fn2-pool-append-text)))))

(in-theory (disable fn2-boot-pack-geometry fn2-boot-bootstrap-encode-pool
                    fn2-boot-save-geometry fn2-boot-save-anchor-digest))
